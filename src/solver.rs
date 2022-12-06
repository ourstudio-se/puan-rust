//! # Simplex solver
//! 
//! Beta version of simplex solver for linear and integer linear programs.
//! 

use itertools::Itertools;
use linalg::Matrix;
use crate::polyopt::{Polyhedron, VariableFloat};

use crate::linalg;

/// Data structure for a solution to a linear program.
#[derive(Default)]
pub struct Solution {
    /// Value of the variables at the solution.
    pub x: Vec<f64>,
    /// Value of the objective function given `x`.
    pub z: f64,
    /// Status of the solution.
    /// 
    ///| Code | Description                 |
    ///|------|-----------------------------|
    ///| 1    | solution is undefined       |
    ///| 2    | solution is feasible        |
    ///| 3    | solution is infeasible      |
    ///| 4    | no feasible solution exists |
    ///| 5    | solution is optimal         |
    ///| 6    | solution is unbounded       |
    pub status_code: usize
}

impl Clone for Solution {
    fn clone(&self) -> Self {
        return Solution { x: self.x.clone(), z: self.z, status_code: self.status_code}
    }
}

/// Data structure for integer solutions to an integer linear program. (See Solution).
pub struct IntegerSolution {
    pub x: Vec<i64>,
    pub z: i64,
    pub status_code: usize
}

impl Clone for IntegerSolution {
    fn clone(&self) -> Self {
        return IntegerSolution { x: self.x.clone(), z: self.z, status_code: self.status_code}
    }
}

/// Data structure for a basic feasible solution.
#[derive(Default)]
struct BFS {
    /// values of the basis variables.
    x: Vec<f64>,
    /// Indices of the basis variables.
    b_vars: Vec<usize>,
    /// Indices of non-basis variables.
    n_vars: Vec<usize>,
    /// Indices of substituted variables.
    /// Substitutions as x' = upper_bound(x) - x.
    sub_vars: Vec<usize>
}

impl Clone for BFS {
    fn clone(&self) -> Self {
        return BFS { x: self.x.clone(), b_vars: self.b_vars.clone(), n_vars: self.n_vars.clone(), sub_vars: self.sub_vars.clone()}
    }
}
/// Data structure for a linear program (LP).
#[derive(Default)]
pub struct LinearProgram {
    /// Polyhedron with constraints on the form $ A \ge b $.
    pub ge_ph: Polyhedron,
    /// Polyhedron with constraints on the form $ A = b $.
    pub eq_ph: Polyhedron,
    /// Objective function.
    pub of: Vec<f64>
}

impl Clone for LinearProgram {
    fn clone(&self) -> Self {
        return LinearProgram { ge_ph: self.ge_ph.clone(), eq_ph: self.eq_ph.clone(), of: self.of.clone()}
    }
}

/// Data structure for an integer linear program (ILP).
#[derive(Default)]
pub struct IntegerLinearProgram {
    /// Polyhedron with constraints on the form $ A \ge b $.
    pub ge_ph: Polyhedron,
    /// Polyhedron with constraints on the form $ A = b $.
    pub eq_ph: Polyhedron,
    /// Objective function.
    pub of: Vec<f64>
}

impl Clone for IntegerLinearProgram {
    fn clone(&self) -> Self {
        return IntegerLinearProgram { ge_ph: self.ge_ph.clone(), eq_ph: self.eq_ph.clone(), of: self.of.clone()}
    }
}

/// Data structute for a linear program on standard form.
struct StandardFormLP{
    eq_ph: Polyhedron,
    of: Vec<f64>
}

impl Clone for StandardFormLP {
    fn clone(&self) -> Self {
        return StandardFormLP { eq_ph: self.eq_ph.clone(), of: self.of.clone() }
    }
    
}
/// Function which converts an LP to an LP on standard form, i.e. introducing slack variables,
/// adding constraints for lower bounds above zero, substituting variables below zero etc.
fn convert_lp_to_standard_form(lp: &LinearProgram) -> StandardFormLP {
    // Handle lower bounds above and below zero
    let mut new_a = lp.ge_ph.a.clone();
    let mut new_b = lp.ge_ph.b.to_vec();
    let mut new_bounds = lp.ge_ph.bounds();
    let mut new_of = lp.of.to_vec();
    for i in 0..new_a.ncols {
        // Add new constraint to force variable i to be above its lower bound
        if new_bounds[i].0 > 0.0 {
            let mut tmp = vec![0.0; new_a.ncols];
            tmp[i] = 1.0;
            new_a.val.extend(tmp);
            new_a.nrows = new_a.nrows+1;
            new_b.push(new_bounds[i].0);
            new_bounds[i].0 = 0.0;
        }
        if new_bounds[i].0 < 0.0 {
            let tmp_a = new_a.val.to_vec();
            new_a = new_a.insert_column(new_a.ncols, tmp_a.iter().skip(i).step_by(new_a.ncols).map(|e| -e).collect());
            new_of.push(-new_of[i]);
            new_bounds.push((f64::max(0.0, -new_bounds[i].1), -new_bounds[i].0));
        }
    }
    // Introduce slack-variables
    for i in 0..new_a.nrows {
        let mut tmp = vec![0.0; new_a.nrows];
        if new_b[i] <= 0.0 {
            tmp[i] = 1.0;
            for j in 0..new_a.ncols{
                new_a.val[i*new_a.ncols+j] = -new_a.val[i*new_a.ncols+j];
            }
            new_b[i] = -new_b[i];
        } else {
            tmp[i] = -1.0;
        }
        new_a = new_a.insert_column( new_a.ncols, tmp);
        new_bounds.push((0.0, f64::MAX));
        new_of.push(0.);
    }
    
    let n_rows = new_a.nrows;
    return StandardFormLP {
        eq_ph: Polyhedron{
            a: new_a,
            b: new_b.to_vec(),
            variables: new_bounds.iter().map(|b| VariableFloat { id: 0, bounds: *b}).collect(),
            index: (0..n_rows).map(|x| Some(x as u32)).collect(),
        },
        of: new_of.to_vec()
    }
}

fn convert_ilp_to_standard_form(lp: &IntegerLinearProgram) -> StandardFormLP {
    convert_lp_to_standard_form(&LinearProgram{ge_ph: lp.ge_ph.clone(), eq_ph: lp.eq_ph.clone(), of: lp.of.clone()})
}
/// Phase one of the simplex algorithm, finds a basic feasible solution
fn _simplex_phase_one(lp: &StandardFormLP) -> (StandardFormLP, BFS) {
    let mut origo_is_bfs = true;
    let mut new_a: Matrix = lp.eq_ph.a.clone();
    let mut art_var_cnt = 0;
    let mut new_bounds = lp.eq_ph.bounds();
    let mut new_of = vec![0.0; lp.eq_ph.a.ncols];
    let updated_lp: StandardFormLP;
    let new_bfs: BFS;
    let mut b_vars: Vec<usize> = Vec::with_capacity(lp.eq_ph.a.nrows);
    let mut n_vars: Vec<usize> = (0..lp.eq_ph.a.ncols - lp.eq_ph.a.nrows).collect();
    
    let lp_eq_ph_bounds = lp.eq_ph.bounds();
    for i in 0..lp.eq_ph.a.nrows {
        if lp.eq_ph.a.val[i*lp.eq_ph.a.ncols + lp.eq_ph.a.ncols - lp.eq_ph.a.nrows+i] < 0.0 && lp.eq_ph.b[i] > 0.0 || lp.eq_ph.b[i] < lp_eq_ph_bounds[lp.eq_ph.a.ncols - lp.eq_ph.a.nrows+i].0 || lp.eq_ph.b[i] > lp_eq_ph_bounds[lp.eq_ph.a.ncols - lp.eq_ph.a.nrows+i].1   {
            origo_is_bfs = false;
            let mut tmp = vec![0.0; lp.eq_ph.a.nrows];
            tmp[i] = 1.0;
            new_a = new_a.insert_column(new_a.ncols, tmp);
            b_vars.push(lp.eq_ph.a.ncols + art_var_cnt);
            art_var_cnt = art_var_cnt + 1;
            new_bounds.push((0.0, f64::MAX));
            new_of.push(-1.0);
            n_vars.push(lp.eq_ph.a.ncols - lp.eq_ph.a.nrows + i);
        } else {
            b_vars.push(lp.eq_ph.a.ncols - lp.eq_ph.a.nrows + i);
        }
    }
    if origo_is_bfs {
        return (lp.clone(), BFS {x: lp.eq_ph.b.clone(), b_vars: (new_a.ncols-new_a.nrows..new_a.ncols).collect(), n_vars: (0..new_a.ncols-new_a.nrows).collect(), sub_vars: Default::default()});
    } else {
        (updated_lp, new_bfs) = revised_simplex(
            &StandardFormLP{ eq_ph: Polyhedron { a: new_a.clone(), b: lp.eq_ph.b.clone(), variables: new_bounds.iter().map(|b| VariableFloat {id: 0, bounds: *b}).collect(), index: lp.eq_ph.index.clone() },
                                of: new_of.clone()}, 
                                &BFS{
                                    x: lp.eq_ph.b.clone(),
                                    b_vars, n_vars, sub_vars: Default::default()
                                });
    }
    let res = Matrix {val: new_bfs.x.clone(), nrows: 1, ncols: new_bfs.x.len()}.dot(&Matrix{val: new_of.clone(), ncols: new_of.len(), nrows: 1}.get_columns(&new_bfs.b_vars).transpose());
    if res.val[0] < 0.0 {
        // No feasible solution exists
        return (lp.clone(), Default::default());
    } else {
        let mut b_vars = new_bfs.b_vars.clone();
        let mut n_vars = new_bfs.n_vars.clone();
        let mut b_inv = linalg::identity_matrix(b_vars.len());
        let mut a = updated_lp.eq_ph.a.clone();
        for index in 0..b_vars.len(){
            if b_vars[index] >= lp.eq_ph.a.ncols {
                let incoming_variable = n_vars.iter().find_or_first(|x| **x < lp.eq_ph.a.ncols).unwrap();
                let b_inv_n_j = b_inv.dot(&Matrix { val : a.val.iter().skip(*incoming_variable).step_by(a.ncols).copied().collect(), ncols: 1, nrows: a.nrows});
                let mut e = linalg::identity_matrix(b_vars.len());
                e.val = e.update_column(index, &Matrix{val: (b_inv_n_j.val).iter().map(|x| -x).collect(), nrows: b_inv_n_j.nrows, ncols: b_inv_n_j.ncols}.divide(&Matrix{val: vec![(b_inv_n_j.val)[index]], ncols: 1, nrows:1}).val).val;
                e.val[index*e.ncols + index] = if b_inv_n_j.val[index] != 0. {1./b_inv_n_j.val[index]} else {f64::MAX};
                b_inv = e.dot(&b_inv);
                b_vars[index] = *incoming_variable;
                n_vars = n_vars.iter().filter(|x| **x != *incoming_variable).map(|x| *x).collect();
            }
        }
        a = b_inv.dot(&a);
        let b = b_inv.dot(&Matrix{val: updated_lp.eq_ph.b.to_vec(), ncols: 1, nrows: updated_lp.eq_ph.b.len()});

        return (StandardFormLP{ eq_ph: Polyhedron{ a: a.get_columns(&(0..lp.eq_ph.a.ncols).collect()), b: b.val.to_vec(), variables: updated_lp.eq_ph.bounds()[0..lp.eq_ph.a.ncols].iter().map(|b| VariableFloat {id: 0, bounds: *b}).collect(), index: updated_lp.eq_ph.index.clone()}, of: lp.of.clone()},
        BFS { x: b.val.to_vec(), b_vars: b_vars, n_vars: n_vars.into_iter().filter(|x| *x < lp.eq_ph.a.ncols).collect::<Vec<usize>>(), sub_vars: new_bfs.sub_vars})
    }
}

/// Phase two of the simplex algorithm. Finds an optimal solution to the LP if possible.
fn _simplex_phase_two(lp: &StandardFormLP, bfs: &BFS) -> (StandardFormLP, BFS) {
    revised_simplex(lp, bfs)
}

/// Solves a maximization LP on standard form using the simplex algorithm. 
fn solve_standard_form_lp(lp: &StandardFormLP, bfs: Option<&BFS>) -> Solution {
    let mut _bfs: BFS;
    let mut _lp = lp.clone();
    let sol: Solution;
    if bfs.is_none() {
        (_lp, _bfs) = _simplex_phase_one(&lp);
    } else {
        _bfs = bfs.unwrap().clone();
    }
    if _bfs.x.len() > 0 {
        (_lp, _bfs) = _simplex_phase_two(&_lp, &_bfs);
        // Re substitute variables
        let mut x = vec![0.0; _lp.eq_ph.a.ncols];
        for i in 0.._bfs.b_vars.len(){
            x[_bfs.b_vars[i]] = _bfs.x[i];
        }
        let lp_eq_ph_bounds = lp.eq_ph.bounds();
        for i in 0.._bfs.sub_vars.len(){
            x[_bfs.sub_vars[i]] = lp_eq_ph_bounds[_bfs.sub_vars[i]].1 - x[_bfs.sub_vars[i]];
        }
        let z = lp.of.iter().zip(x.iter()).map(|(x, y)| x*y).sum();
        let status_code: usize;
        if _bfs.x.len() < 1 {
            status_code = 1;
        } else if x.iter().any(|x| *x >= f64::MAX){
            status_code = 6;
        } else {
            status_code = 5;
        }
        sol = Solution { x, z, status_code };
    } else {
        sol = Solution{
            x: Default::default(),
            z: Default::default(),
            status_code: 4
        };
    }
    sol
}

/// Solves a maximization LP using the simplex algorithm
pub fn solve_lp(lp: &LinearProgram) -> Solution {
    let mut sol = solve_standard_form_lp(&lp.convert_to_standard_form(), None);
    if sol.x.len() > lp.ge_ph.a.ncols {
        sol.x = sol.x[..lp.ge_ph.a.ncols].to_vec()
    }
    Solution { x: sol.x, z: sol.z, status_code: sol.status_code}
}

/// Solves a maximization ILP using the Land-Doig-Dakins algorithm together with the simplex algorithm. 
pub fn solve_ilp(lp: &IntegerLinearProgram) -> IntegerSolution {
    let mut z_lb: f64 = f64::MIN;
    let mut current_best_sol: Solution = Default::default();
    let mut nodes_to_explore = vec![LinearProgram{ge_ph: lp.ge_ph.clone(), eq_ph: lp.eq_ph.clone(), of: lp.of.to_vec()}]; 
    let mut explored_nodes: Vec<Vec<(f64, f64)>> = vec![];
    let mut current_lp: LinearProgram;
    let mut current_sol: Solution;
    while nodes_to_explore.len() > 0 {
        current_lp = nodes_to_explore.pop().expect("No LinearProgram in vector");
        current_sol = LinearProgram::solve(&current_lp);
        if current_sol.status_code==4 || current_sol.status_code==3 {
            // No feasible solution in this area
           continue
        } else if current_sol.z < z_lb {
            // Not possible to find better solution in this area
           continue
        } else if current_sol.x.iter().position(|x| (x%1.0) > 0.0000001).is_none() || current_sol.x.iter().position(|x| (x%1.0) > 0.0000001).unwrap() >= current_lp.ge_ph.a.ncols {
            // We've found a best solution in this area
            z_lb = current_sol.z;
            current_best_sol = current_sol;
        } else {
            let first_non_int = current_sol.x.iter().position(|x| (x%1.0) > 0.0000001).unwrap();
            
            let mut bounds1 = current_lp.ge_ph.bounds().to_vec();
            bounds1[first_non_int].1 = f64::floor(current_sol.x[first_non_int]);
            let mut node_explored = false;
            for i in 0..explored_nodes.len(){
                node_explored = true;
                for j in 0..explored_nodes[i].len(){
                    if j < bounds1.len() && !(explored_nodes[i][j].0 == bounds1[j].0 && explored_nodes[i][j].1 == bounds1[j].1) {
                        node_explored = false;
                        continue;
                    }
                }
                if node_explored {
                    break;
                }
            }
            if !node_explored{
                explored_nodes.push(bounds1.to_vec());
                nodes_to_explore.push(LinearProgram{ge_ph: Polyhedron{ a: current_lp.ge_ph.a.clone(), b: current_lp.ge_ph.b.to_vec(), variables: bounds1.iter().map(|b| VariableFloat {id: 0, bounds: *b}).collect(), index: current_lp.ge_ph.index.clone()},
                                                    eq_ph: Polyhedron{ a: current_lp.eq_ph.a.clone(), b: current_lp.eq_ph.b.to_vec(), variables: bounds1.iter().map(|b| VariableFloat {id: 0, bounds: *b}).collect(), index: current_lp.eq_ph.index.clone()},
                                                    of: current_lp.of.to_vec()});
            }
            let mut node_explored = false;
            let mut bounds2 = current_lp.ge_ph.bounds();
            bounds2[first_non_int].0 = f64::ceil(current_sol.x[first_non_int]);
            for i in 0..explored_nodes.len(){
                node_explored = true;
                for j in 0..explored_nodes[i].len(){
                    if j < bounds2.len() && !(explored_nodes[i][j].0 == bounds2[j].0 && explored_nodes[i][j].1 == bounds2[j].1) {
                        node_explored = false;
                        continue;
                    }
                }
                if node_explored {
                    break;
                }
            }
            if !node_explored{
                explored_nodes.push(bounds2.to_vec());
                nodes_to_explore.push(LinearProgram{ge_ph: Polyhedron{ a: current_lp.ge_ph.a.clone(), b: current_lp.ge_ph.b.to_vec(), variables: bounds2.iter().map(|b| VariableFloat {id: 0, bounds: *b}).collect(), index: current_lp.ge_ph.index.clone()},
                                                    eq_ph: Polyhedron{ a: current_lp.eq_ph.a.clone(), b: current_lp.eq_ph.b.to_vec(), variables: bounds2.iter().map(|b| VariableFloat {id: 0, bounds: *b}).collect(), index: current_lp.eq_ph.index.clone()},
                                                    of: current_lp.of.to_vec()});
            }
        }
    }
    let mut res: Vec<i64> = current_best_sol.x.iter().map(|x| *x as i64).collect();
    if res.len() > lp.ge_ph.a.ncols {
        res = res[..lp.ge_ph.a.ncols].to_vec()
    }
    return IntegerSolution { z: z_lb as i64, x: res, status_code: current_best_sol.status_code};
}
impl LinearProgram {
    fn convert_to_standard_form(&self) -> StandardFormLP {
        convert_lp_to_standard_form(self)
    }
    /// Solves a linear program with the revised simplex algorithm. 
    /// # Example:
    /// 
    /// Solve the linear program
    /// $$ \max \quad -4x_1+-5x_2 $$
    /// $$ s.t. \quad x_1+4x_2 \geq 4 $$
    /// $$ \qquad \ 3x_1+2x_2 \geq 6 $$
    /// $$ \qquad \  x_1, x_2 \geq 0$$
    /// ```
    /// use puanrs::polyopt::{Polyhedron, VariableFloat};
    /// use puanrs::solver::LinearProgram;
    /// use puanrs::linalg::Matrix;
    /// let sol = LinearProgram {
    ///                 ge_ph: Polyhedron {
    ///                         a: Matrix{val: vec![1.0, 4.0, 3.0, 2.0],
    ///                             nrows: 2,
    ///                             ncols: 2
    ///                         },
    ///                         b: vec![4.0, 6.0],
    ///                         variables: vec![ VariableFloat { id: 0, bounds: (0.0,f64::MAX) }, VariableFloat { id: 1, bounds: (0.0,f64::MAX) }],
    ///                         index: vec![Some(0),Some(1)],
    ///                 },
    ///                 eq_ph: Default::default(),
    ///                 of: vec![-4.0, -5.0],
    ///             }.solve();
    /// assert_eq!(sol.z, -9.4);
    /// assert_eq!(sol.x, vec![1.6000000000000003, 0.5999999999999999]);
    /// assert_eq!(sol.status_code, 5);
    /// ```
    pub fn solve(&self) -> Solution {
        solve_lp(self)
    }
}

impl IntegerLinearProgram {
    fn convert_to_standard_form(&self) -> StandardFormLP {
        convert_ilp_to_standard_form(self)
    }
    /// Solves a linear program with the revised simplex algorithm and produces an integer solution using the Land-Doig-Dakins algorithm. 
    /// # Example:
    /// 
    /// Solve the linear program
    /// $$ \max \quad -4x_1+-5x_2 $$
    /// $$ s.t. \quad x_1+4x_2 \geq 4 $$
    /// $$ \qquad \ 3x_1+2x_2 \geq 6 $$
    /// $$ \qquad \  x_1, x_2 \geq 0$$
    /// ```
    /// use puanrs::solver::IntegerLinearProgram;
    /// use puanrs::polyopt::{Polyhedron, VariableFloat};
    /// use puanrs::linalg::Matrix;
    /// let sol = IntegerLinearProgram {
    ///                 ge_ph: Polyhedron {
    ///                         a: Matrix{
    ///                             val: vec![1.0, 4.0, 3.0, 2.0],
    ///                             nrows: 2,
    ///                             ncols: 2
    ///                         },
    ///                         b: vec![4.0, 6.0],
    ///                         variables: vec![ VariableFloat { id:0, bounds: (0.0,f64::MAX) }, VariableFloat { id: 1, bounds: (0.0,f64::MAX) }],
    ///                         index: vec![Some(0),Some(1)],
    ///                 },
    ///                 eq_ph: Default::default(),
    ///                 of: vec![-4.0, -5.0],
    ///             }.solve();
    /// assert_eq!(sol.z, -13);
    /// assert_eq!(sol.x, vec![2, 1]);
    /// assert_eq!(sol.status_code, 5);
    /// ```
    pub fn solve(&self) -> IntegerSolution {
        solve_ilp(self)
    }
    
}

/// The revised simplex algorithm
fn revised_simplex(lp: &StandardFormLP, bfs: &BFS) -> (StandardFormLP, BFS) {
    fn _update_constraint_column(b_inv_n_j: &Matrix, index: usize, b_inv: &Matrix, b_vars: &Vec<usize>) -> Matrix {
        let mut e = linalg::identity_matrix(b_vars.len());
        e.val = e.update_column(index, &Matrix{val: (b_inv_n_j.val).iter().map(|x| -x).collect(), nrows: b_inv_n_j.nrows, ncols: b_inv_n_j.ncols}.divide(&Matrix{val: vec![(b_inv_n_j.val)[index]], ncols: 1, nrows:1}).val).val;
        e.val[index*e.ncols + index] = if b_inv_n_j.val[index] != 0. {1./b_inv_n_j.val[index]} else {f64::MAX};
        e.dot(&b_inv)
    }
    fn _update_basis(b_vars: &Vec<usize>, n_vars: &Vec<usize>, incoming: usize, outgoing: usize) -> (Vec<usize>, Vec<usize>) {
        let _tmp = b_vars[outgoing];
        let mut b_vars_new = b_vars.to_vec();
        let mut n_vars_new = n_vars.to_vec();
        b_vars_new[outgoing] = n_vars[incoming];
        n_vars_new[incoming] = _tmp;
        (b_vars_new, n_vars_new)
    }
    fn _perform_ub_substitution(a_eq: &Matrix, b_eq: &Vec<f64>, c: &Vec<f64>, variable: &usize, limit: &f64, substituted_vars: &Vec<usize>) -> (Matrix, Vec<f64>, Vec<f64>, Vec<usize>){
        let mut b = Vec::with_capacity(b_eq.len());
        for i in 0..b_eq.len() {
            b.push(b_eq[i] - limit*a_eq.val[i*a_eq.ncols+variable]);
        } 
        let a = a_eq.val.iter().enumerate().map(|x| if x.0%a_eq.ncols == *variable {-*x.1} else {*x.1}).collect();
        let mut c_new = c.to_vec();
        c_new[*variable] = -c[*variable];
        let mut sub_vars = substituted_vars.to_vec();
        sub_vars.push(*variable);
        return (Matrix{val: a, ncols: a_eq.ncols, nrows: a_eq.nrows}, b, c_new, sub_vars)
    }
    
    //Initialization
    let mut b_vars = bfs.b_vars.clone();
    let mut n_vars = bfs.n_vars.clone();
    let mut c_new = lp.of.clone();
    let mut sub_vars = bfs.sub_vars.clone();
    for i in 0..sub_vars.len(){
        c_new[sub_vars[i]] = -c_new[sub_vars[i]];
    }
    let mut x_b = Matrix{val: bfs.x.clone(), ncols: 1, nrows: b_vars.len()};
    let mut b_inv = linalg::identity_matrix(b_vars.len());
    let mut c_tilde_n: Vec<f64> = Vec::with_capacity(n_vars.len());
    let mut a = lp.eq_ph.a.clone();
    let mut b = lp.eq_ph.b.clone();
    for i in 0..n_vars.len(){
        c_tilde_n.push(lp.of[n_vars[i]] - Matrix{val:  b_vars.iter().map(|i| lp.of[*i]).collect(),
            ncols: b_vars.len(),
            nrows: 1}.dot(&b_inv).dot(&linalg::get_columns(&a, &n_vars)).val[i]);
    }
    let mut b_inv_tilde: Matrix;
    //Iteration start
    let lp_eq_ph_bounds = lp.eq_ph.bounds();
    while c_tilde_n.iter().any(|x| *x > 0.0) {
        let c_tilde_n_max = c_tilde_n.iter().cloned().fold(0./0., f64::max);
        let incoming_variable_index = c_tilde_n.iter().position(|&x| x == c_tilde_n_max).unwrap();
        let incoming_variable = n_vars[incoming_variable_index];
        let b_inv_n_j = b_inv.dot(&Matrix { val : a.val.iter().skip(incoming_variable).step_by(a.ncols).copied().collect(), ncols: 1, nrows: a.nrows});
        let mut _t1 = x_b.ge_divide(&b_inv_n_j);
        let t1 = _t1.val.iter().cloned().fold(0.0/0.0, f64::min);
        let t2 = lp_eq_ph_bounds[incoming_variable].1;
        let _t3 = linalg::get_columns(&Matrix{val: lp_eq_ph_bounds.iter().map(|x| x.1).collect(), nrows:1, ncols: lp_eq_ph_bounds.len()}, &b_vars).subtract(&x_b.transpose()).ge_divide(&Matrix{ val: b_inv_n_j.val.iter().map(|x| -x).collect(), ncols: b_inv_n_j.ncols, nrows: b_inv_n_j.nrows}.transpose());
        let t3 = _t3.val.iter().cloned().fold(0.0/0.0, f64::min);
        if f64::min(f64::min(t1, t2), t3) == f64::MAX {
            // Problem is unbounded
            (b_vars, n_vars) = _update_basis(&b_vars, &n_vars, incoming_variable_index, 0);
            x_b.val[0] = f64::MAX;
            break;
        } else if t3 < t1 && t3 < t2 {
            let mut outgoing_variable = 0;
            for i in 0.._t3.val.len(){
                if _t3.val[i] == t3 && b_vars[i] > outgoing_variable {
                    outgoing_variable = b_vars[i];
                }
            }
            let outgoing_variable_index = b_vars.iter().position(|&x| x==outgoing_variable).unwrap();
            (a, b, c_new, sub_vars) = _perform_ub_substitution(&a.clone(), &b.to_vec(), &c_new.to_vec(), &outgoing_variable, &lp_eq_ph_bounds[outgoing_variable].1, &sub_vars);
            b_inv_tilde = _update_constraint_column(&b_inv_n_j, outgoing_variable_index, &b_inv, &b_vars);
            (b_vars, n_vars) = _update_basis(&b_vars, &n_vars, incoming_variable_index, outgoing_variable_index);
        } else if t2 < t1 {
            (a, b, c_new, sub_vars) = _perform_ub_substitution(&a.clone(), &b.to_vec(), &c_new.to_vec(), &incoming_variable, &lp_eq_ph_bounds[incoming_variable].1, &sub_vars);
            b_inv_tilde = b_inv.clone();
        } else {
            let outgoing_variable: Option<usize> = _t1.val.iter().enumerate().filter(|(_, &r)| r == t1).map(|(index, _)| *b_vars.get(index).expect("did not find index")).max();
            let outgoing_variable_index = b_vars.iter().position(|&x| x==outgoing_variable.unwrap()).unwrap();
            b_inv_tilde = _update_constraint_column(&b_inv_n_j, outgoing_variable_index, &b_inv, &b_vars);
            (b_vars, n_vars) = _update_basis(&b_vars, &n_vars, incoming_variable_index, outgoing_variable_index);
        }
        b_inv = b_inv_tilde.clone();
        for i in 0..n_vars.len(){
            c_tilde_n[i] = c_new[n_vars[i]] - Matrix{val: b_vars.iter().map(|j| c_new[*j]).collect(),
                                                             ncols: b_vars.len(),
                                                             nrows: 1}.dot(&b_inv_tilde).dot(&linalg::get_columns(&a, &n_vars)).val[i];
        }
        x_b = b_inv.dot(&Matrix{val: b.to_vec(), ncols: 1, nrows: b.len()});
    }
    
    let a_new = b_inv.dot(&a);
    
    return (StandardFormLP{ eq_ph: Polyhedron {a: a_new, b: x_b.val.to_vec(), variables: lp.eq_ph.variables.clone(), index: lp.eq_ph.index.clone()}, of: lp.of.clone()},
            BFS { x: x_b.val, b_vars, n_vars, sub_vars})
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_solver_1(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![1.0, 1.0, 0.0, 0.0, 1.0, 1.0],
                          nrows: 2,
                          ncols: 3},
                b: vec![1.0, 1.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)},
                    VariableFloat { id: 0, bounds: (0.0,1.0)}
                ],
                index: (0..2).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![1.0,1.0,1.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 3);
        assert_eq!(sol.x, vec![1, 1, 1]);
    }
    #[test]
    fn test_solver_2(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-2.0, -1.0, -1.0, -1.0, -1.0, 0.0],
                          nrows: 3,
                          ncols: 2},
                b: vec![-100.0, -80.0, -40.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX) }, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX) },
                ],
                index: (0..3).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![30.0,20.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 1800);
        assert_eq!(sol.x, vec![20, 60]);
    }
    #[test]
    fn test_solver_3(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-2.0, -1.0, -1.0, -1.0],
                          nrows: 2,
                          ncols: 2},
                b: vec![-100.0, -80.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,40.0) }, 
                    VariableFloat { id: 0, bounds: (0.0,30.0) }
                ],
                index: (0..2).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![30.0,20.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 1650);
        assert_eq!(sol.x, vec![35, 30]);
    }
    #[test]
    fn test_solver_4(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![2.0, -1.0, -1.0, -2.0, -1.0, 0.0, 0.0, -1.0, 1.0, 0.0, 1.0, -1.0],
                          nrows: 4,
                          ncols: 3},
                b: vec![1.0, -5.0, 1.0, -1.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX) }, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX) }, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX) }
                ],
                index: (0..4).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![-2.0,-1.0, -1.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, -3);
        assert_eq!(sol.x, vec![1, 0, 1]);
    }
    #[test]
    fn test_solver_5(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-1.0, 1.0, -2.0, 1.0, 0.0, -1.0],
                          nrows: 3,
                          ncols: 2},
                b: vec![-2.0, -4.0, -2.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}
                ],
                index: (0..3).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![1.0, 1.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 5);
        assert_eq!(sol.x, vec![3, 2]);
    }

    #[test]
    fn test_solver_6(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-5.0, -4.0],
                          nrows: 1,
                          ncols: 2},
                b: vec![-21.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}
                ],
                index: (0..1).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![5.0, 2.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 20);
        assert_eq!(sol.x, vec![4, 0]);
    }

    #[test]
    fn test_solver_7(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-4.0, -2.0, -2.0, -3.0],
                          nrows: 1,
                          ncols: 4},
                b: vec![-7.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)}
                ],
                index: (0..1).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![7.0, 3.0, 2.0, 2.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 10);
        assert_eq!(sol.x, vec![1,1,0,0]);
    }

    #[test]
    fn test_solver_8(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![1.0, 4.0, 3.0, 2.0],
                            nrows: 2,
                            ncols: 2},
                b: vec![4.0, 6.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}
                ],
                index: (0..2).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![-4.0, -5.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, -13);
        assert_eq!(sol.x, vec![2,1]);
    }
    #[test]
    fn test_solver_9(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![4.0, -3.0, -3.0, -2.0],
                            nrows: 2,
                            ncols: 2},
                b: vec![-6.0, -18.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}
                ],
                index: (0..2).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![1.0, 5.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 23);
        assert_eq!(sol.x, vec![3,4]);
    }
    #[test]
    fn test_solver_10(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-5.0, -7.0, -1.0, 0.0, 0.0, -1.0],
                            nrows: 3,
                            ncols: 2},
                b: vec![-35.0, -3.0, -4.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}
                ],
                index: (0..3).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![5.0, 6.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 29);
        assert_eq!(sol.x, vec![1,4]);
    }
    #[test]
    fn test_solver_11(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-4.0, -2.0, -3.0, -1.0],
                            nrows: 1,
                            ncols: 4},
                b: vec![-7.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}
                ],
                index: (0..1).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![18.0, 8.0, 4.0, 2.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 28);
        assert_eq!(sol.x, vec![1, 1, 0, 1]);
    }
    #[test]
    fn test_solver_12(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-6.0, -10.0, -15.0, -10.0],
                            nrows: 1,
                            ncols: 4},
                b: vec![-36.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0,f64::MAX)}
                ],
                index: (0..1).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![5.0, 10.0, 10.0, 16.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 53);
        assert_eq!(sol.x, vec![1, 0, 0, 3]);
    }
    #[test]
    fn test_solver_13(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-2.0, -3.0, -3.0],
                            nrows: 1,
                            ncols: 3},
                b: vec![-9.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,2.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,2.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,2.0)}
                ],
                index: (0..1).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![5.0, 6.0, 7.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 20);
        assert_eq!(sol.x, vec![0, 1, 2]);
    }
    #[test]
    fn test_solver_14(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-1.0, -2.0, -1.0, 0.0, 0.0, -2.0, -4.0, -3.0, -7.0, -3.0],
                            nrows: 2,
                            ncols: 5},
                b: vec![-2.0, -13.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)} 
                ],
                index: (0..2).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![5.0, 7.0, 6.0, 4.0, 5.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 16);
        assert_eq!(sol.x, vec![1, 0, 1, 0, 1]);
    }
    #[test]
    fn test_solver_15(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-2.0, -1.0, -2.0, -1.0],
                            nrows: 1,
                            ncols: 4},
                b: vec![-4.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)} 
                ],
                index: (0..1).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![5.0, 8.0, 4.0, 6.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 19);
        assert_eq!(sol.x, vec![1, 1, 0, 1]);
    }
    // Unbounded
    #[test]
    fn test_solver_16(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![0.0, -1.0],
                            nrows: 1,
                            ncols: 2},
                b: vec![-3.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0, f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0, f64::MAX)}
                ],
                index: (0..1).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![1.0, 1.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, i64::MAX);
        assert_eq!(sol.x, vec![i64::MAX, 0]);
    }
    // Unsolvable
    #[test]
    fn test_solver_17(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-1.0, -1.0, 1.0, -1.0, 0.0, 1.0],
                            nrows: 3,
                            ncols: 2},
                b: vec![-1.0, 0.0, 2.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0, f64::MAX)}, 
                    VariableFloat { id: 0, bounds: (0.0, f64::MAX)}
                ],
                index: (0..3).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![1.0, 1.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, -f64::MAX as i64);
        assert_eq!(sol.x, vec![]);
    }
    // Not feasible bfs
    #[test]
    fn test_solver_18(){
        let lp: IntegerLinearProgram = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![1.0, 1.0, 0.0, 0.0, 1.0, 1.0],
                          nrows: 2,
                          ncols: 3},
                b: vec![1.0, 1.0],
                variables: vec![
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)}, 
                    VariableFloat { id: 0, bounds: (0.0,1.0)}
                ],
                index: (0..2).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: vec![1.0,1.0,1.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 3);
        assert_eq!(sol.x, vec![1, 1, 1]);
    }
    #[test]
    fn test_solver_19(){
        let lp: IntegerLinearProgram = IntegerLinearProgram{
            ge_ph: Polyhedron { a: Matrix { val: vec![ 1.,  1.,  0.,  0.,  0.,  0., 0., -2.,  0.,  0.,  1.,  1., -1.,  0., -1., -1.,  0.,  0.],
                                nrows: 3, ncols: 6},
                                b: vec![1.0, 0.0, -2.0],
                                variables: vec![
                                    VariableFloat{id: 0, bounds:(0.0, 1.0)},
                                    VariableFloat{id: 0, bounds:(0.0, 1.0)},
                                    VariableFloat{id: 0, bounds:(0.0, 1.0)},
                                    VariableFloat{id: 0, bounds:(0.0, 1.0)},
                                    VariableFloat{id: 0, bounds:(0.0, 1.0)},
                                    VariableFloat{id: 0, bounds:(0.0, 1.0)}],
                                index: (0..5).map(|x| Some(x as u32)).collect(),
                },
                eq_ph: Default::default(),
                of: vec![0.0, 1.0, 1.0, 1.0, 0.0, 0.0]
        };
        let sol = lp.solve();
        assert_eq!(sol.z, 3);
        assert_eq!(sol.x, vec![0, 1, 1, 1, 1, 1]);
    }
    #[test]
    fn test_solver_20(){
        let solution: IntegerSolution = IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: Matrix { 
                    val: vec![1.0, 1.0], 
                    ncols: 2, 
                    nrows: 1 
                },
                b: vec![2.0],
                index: vec![Some(0)],
                variables: vec![
                    VariableFloat { id: 1, bounds: (0.0, 1.0) },
                    VariableFloat { id: 2, bounds: (0.0, 1.0) },
                ]
            },
            eq_ph: Default::default(),
            of: vec![1.0, 0.0]
        }.solve();
        assert_eq!(solution.x, vec![1,1]);
        assert_eq!(solution.z, 1);
        assert_eq!(solution.status_code, 5);
    }
}
