//! # Simplex solver
//! 
//! Simplex solver producing integer solutions for linear programs.
//! 

use itertools::Itertools;
use linalg::Matrix;

use crate::linalg;

/// Data structure for polyhedron with `a` as `Matrix` and `b` as `Vec` and `bounds` as a `Vec` of `Tuples`.
/// Note that the number of rows of `a` must be the same as the length of `b` and the number of columns of `a`
/// must be the same as the length of `bounds`.
#[derive(Default)]
pub struct Polyhedron {
    /// The left-hand side of linear constraints on the form $ a + b + c \ge x $.
    pub a: Matrix,
    /// The right-hand side of linear constraints as described above.
    pub b: Vec<f64>,
    /// Upper and lower bounds (`lower_bound`, `upper_bound`) of the variables given by `a`.
    pub bounds: Vec<(f64, f64)>
}
impl Clone for Polyhedron {
    fn clone(&self) -> Self {
        return Polyhedron { a: self.a.clone(), b: self.b.clone(), bounds: self.bounds.clone() }
    }
}

/// Data structure for solutions to a linear program.
#[derive(Default)]
pub struct Solution {
    x: Vec<f64>,
    z: f64,
    status_code: usize
}

impl Clone for Solution {
    fn clone(&self) -> Self {
        return Solution { x: self.x.clone(), z: self.z, status_code: self.status_code}
    }
}

pub struct IntegerSolution {
    x: Vec<i64>,
    z: i64,
    status_code: usize
}

impl Clone for IntegerSolution {
    fn clone(&self) -> Self {
        return IntegerSolution { x: self.x.clone(), z: self.z, status_code: self.status_code}
    }
}

/// Data structure for a linear program
#[derive(Default)]
pub struct LinearProgram { // (ge_ph, eq_ph, of, )
    /// Polyhedron
    pub ge_ph: Polyhedron,
    pub eq_ph: Polyhedron,
    /// Objective function
    pub of: Vec<f64>
}

impl Clone for LinearProgram {
    fn clone(&self) -> Self {
        return LinearProgram { ge_ph: self.ge_ph.clone(), eq_ph: self.eq_ph.clone(), of: self.of.clone()}
    }
    
}
pub struct StandardFormLP{
    pub eq_ph: Polyhedron,
    pub of: Vec<f64>
}

impl Clone for StandardFormLP {
    fn clone(&self) -> Self {
        return StandardFormLP { eq_ph: self.eq_ph.clone(), of: self.of.clone() }
    }
    
}
fn convert_lp_to_standard_form(lp: &LinearProgram) -> StandardFormLP {
    // Handle lower bounds above and below zero
    let mut new_a = lp.ge_ph.a.clone();
    let mut new_b = lp.ge_ph.b.to_vec();
    let mut new_bounds = lp.ge_ph.bounds.to_vec();
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
        if new_b[i] < 0.0 {
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
    
    return StandardFormLP {
        eq_ph: Polyhedron{
            a: new_a,
            b: new_b.to_vec(),
            bounds: new_bounds.to_vec()
        },
        of: new_of.to_vec()
    }
}

fn _simplex_phase_one(lp: &StandardFormLP) -> (Solution, StandardFormLP) {
    let mut origo_is_bfs = true;
    let mut new_a: Matrix = lp.eq_ph.a.clone();
    let mut art_var_cnt = 0;
    let mut new_bounds = lp.eq_ph.bounds.to_vec();
    let mut new_of = vec![0.0; lp.eq_ph.a.ncols];
    let solved_lp: Solution;
    let updated_lp: StandardFormLP;
    let mut sol = vec![0.0; lp.eq_ph.a.ncols];
    for i in 0..lp.eq_ph.a.nrows {
        if lp.eq_ph.a.val[i*lp.eq_ph.a.ncols + lp.eq_ph.a.ncols - lp.eq_ph.a.nrows+i] < 0.0 && lp.eq_ph.b[i] > 0.0 || lp.eq_ph.b[i] < lp.eq_ph.bounds[lp.eq_ph.a.ncols - lp.eq_ph.a.nrows+i].0 || lp.eq_ph.b[i] > lp.eq_ph.bounds[lp.eq_ph.a.ncols - lp.eq_ph.a.nrows+i].1   {
            origo_is_bfs = false;
            let mut tmp = vec![0.0; lp.eq_ph.a.nrows];
            tmp[i] = 1.0;
            new_a = new_a.insert_column(new_a.ncols, tmp);
            art_var_cnt = art_var_cnt + 1;
            new_bounds.push((0.0, f64::MAX));
            new_of.push(-1.0);
            sol.push(lp.eq_ph.b[i]);
        } else {
            sol[lp.eq_ph.a.ncols - lp.eq_ph.a.nrows+i] = lp.eq_ph.b[i];
        }
    }
    if origo_is_bfs {
        return (Solution{
            x: sol,
            z: 0.0,
            status_code: 2
        }, lp.clone());
    } else {
        (solved_lp, updated_lp) = revised_simplex(
            &StandardFormLP{ eq_ph: Polyhedron { a: new_a, b: lp.eq_ph.b.clone(), bounds: new_bounds },
                                of: new_of}, &Solution{
                                    x: sol,
                                    z: -lp.eq_ph.b.iter().sum::<f64>(),
                                    status_code: 2
                                });
    }
    if solved_lp.z < 0.0 {
        // No feasible solution exists
        return (Solution{ x: vec![], z: -1.0, status_code: 4}, lp.clone());
    } else {
        return (Solution{
            x: solved_lp.x[0..lp.eq_ph.a.ncols].to_vec(),
            z: solved_lp.z,
            status_code: 2
        }, StandardFormLP{ eq_ph: Polyhedron{ a: updated_lp.eq_ph.a.get_columns(&(0..lp.eq_ph.a.ncols).collect()), b: updated_lp.eq_ph.b, bounds: updated_lp.eq_ph.bounds[0..lp.eq_ph.a.ncols].to_vec()}, of: lp.of.clone()})
    }
}
fn _simplex_phase_two(lp: &StandardFormLP, sol: &Solution) -> (Solution, StandardFormLP) {
    revised_simplex(lp, sol)
}

pub fn solve_lp(lp: &LinearProgram, sol: Option<&Solution>) -> Solution {
    let mut lp_standard = lp.convert_to_standard_form();
    let _sol: Solution;
    if sol.is_none(){
        (_sol, lp_standard) = _simplex_phase_one(&lp_standard);
    } else {
        _sol = sol.unwrap().clone();
    }
    if _sol.status_code != 4 {
        _simplex_phase_two(&lp_standard, &_sol).0
    } else {
        _sol
    }
}
pub fn solve_ilp(lp: &LinearProgram, sol: Option<&Solution>) -> IntegerSolution {
    let mut z_lb: f64 = f64::MIN;
    let mut current_best_sol: Solution = Default::default();
    let mut nodes_to_explore = vec![LinearProgram{ge_ph: lp.ge_ph.clone(), eq_ph: lp.eq_ph.clone(), of: lp.of.to_vec()}]; 
    let mut explored_nodes: Vec<Vec<(f64, f64)>> = vec![];
    let mut current_lp: LinearProgram;
    let mut current_sol: Solution;
    while nodes_to_explore.len() > 0 {
        current_lp = nodes_to_explore.pop().expect("No LinearProgram in vector");
        current_sol = LinearProgram::solve(&current_lp, sol);
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
            
            let mut bounds1 = current_lp.ge_ph.bounds.to_vec();
            bounds1[first_non_int].1 = f64::floor(current_sol.x[first_non_int]);
            let mut node_explored = false;
            for i in 0..explored_nodes.len(){
                node_explored = true;
                for j in 0..explored_nodes[i].len(){
                    if j < bounds1.len() {
                        if !(explored_nodes[i][j].0 == bounds1[j].0 && explored_nodes[i][j].1 == bounds1[j].1) {
                            node_explored = false;
                            continue;
                        }
                    }
                }
                if node_explored {
                    break;
                }
            }
            if !node_explored{
                explored_nodes.push(bounds1.to_vec());
                nodes_to_explore.push(LinearProgram{ge_ph: Polyhedron{ a: current_lp.ge_ph.a.clone(), b: current_lp.ge_ph.b.to_vec(), bounds: bounds1.to_vec()},
                                                    eq_ph: Polyhedron{ a: current_lp.eq_ph.a.clone(), b: current_lp.eq_ph.b.to_vec(), bounds: bounds1.to_vec()},
                                                    of: current_lp.of.to_vec()});
            }
            let mut node_explored = false;
            let mut bounds2 = current_lp.ge_ph.bounds.to_vec();
            bounds2[first_non_int].0 = f64::ceil(current_sol.x[first_non_int]);
            for i in 0..explored_nodes.len(){
                node_explored = true;
                for j in 0..explored_nodes[i].len(){
                    if j < bounds2.len() {
                        if !(explored_nodes[i][j].0 == bounds2[j].0 && explored_nodes[i][j].1 == bounds2[j].1) {
                            node_explored = false;
                            continue;
                        }
                    }
                }
                if node_explored {
                    break;
                }
            }
            if !node_explored{
                explored_nodes.push(bounds2.to_vec());
                nodes_to_explore.push(LinearProgram{ge_ph: Polyhedron{ a: current_lp.ge_ph.a.clone(), b: current_lp.ge_ph.b.to_vec(), bounds: bounds2.to_vec()},
                                                    eq_ph: Polyhedron{ a: current_lp.eq_ph.a.clone(), b: current_lp.eq_ph.b.to_vec(), bounds: bounds2.to_vec()},
                                                    of: current_lp.of.to_vec()});
            }
        }
    }
    let res: Vec<i64> = current_best_sol.x.iter().map(|x| *x as i64).collect();
    return IntegerSolution { z: z_lb as i64, x: res[..lp.ge_ph.a.ncols].to_vec(), status_code: current_best_sol.status_code};
}
impl LinearProgram {
    fn convert_to_standard_form(&self) -> StandardFormLP {
        convert_lp_to_standard_form(self)
    }
    pub fn solve(&self, sol: Option<&Solution>) -> Solution {
        solve_lp(self, sol)
    }
    /// Solves a linear program with the revised simplex algorithm and produces an integer solution using the Land-Doig-Dakins algorithm. 
    /// # Example:
    /// 
    /// Solve the linear program
    /// $$ \max \quad 30x_1+20x_2 $$
    /// $$ s.t. \quad 2x_1+x_2 \leq 100 $$
    /// $$ \qquad \ x_1+x_2 \leq 80 $$
    /// $$ \qquad \qquad \ x_1 \leq 40 $$
    /// $$ \qquad \  x_1, x_2 \geq 0$$
    /// ```
    /// use puanrs::solver::LinearProgram;
    /// use puanrs::solver::Polyhedron;
    /// use puanrs::linalg::Matrix;
    /// let sol = LinearProgram::solve(&LinearProgram {
    ///                 ge_ph: Polyhedron {
    ///                         a: Matrix{val: vec![-2.0, -1.0, -1.0, -1.0, -1.0, 0.0],
    ///                         nrows: 3,
    ///                         ncols: 2},
    ///                         b: vec![-100.0, -80.0, -40.0],
    ///                         bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX)]
    ///                 },
    ///                 eq_ph: Default::default(),
    ///                 of: vec![30.0, 20.0],
    ///             }, None);
    /// ```
    pub fn solve_ilp(&self, sol: Option<&Solution>) -> IntegerSolution {
        solve_ilp(self, sol)
    }
}

fn revised_simplex(lp: &StandardFormLP, bfs: &Solution) -> (Solution, StandardFormLP) {
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
    fn _setup(lp: &StandardFormLP, bfs: &Solution) -> (Matrix, Vec<usize>, Vec<usize>, Vec<f64>, Vec<usize>){
        // Adjust lp Polyhedron to given bfs
        let mut b_vars: Vec<usize> = vec![lp.eq_ph.a.ncols; lp.eq_ph.a.nrows];
        let mut n_vars: Vec<usize> = Vec::with_capacity(lp.eq_ph.a.ncols-lp.eq_ph.a.nrows);
        let mut ph = lp.eq_ph.a.insert_column(0, lp.eq_ph.b.clone());
        let mut curr_bvar: usize;
        let mut a: Matrix;
        let mut b: Vec<f64>;
        let mut c = lp.of.to_vec();
        let mut sub_vars: Vec<usize> = vec![];
        let mut bfs_x: Vec<usize> = (0..bfs.x.len()).collect();
        let mut removed_items = 0;
        // Identify basis which doesn't require changes to the matrix
        for i in 0..bfs.x.len(){
            if bfs.x[i] != 0.0 {
                if bfs.x[i] != lp.eq_ph.bounds[i].1 && lp.eq_ph.a.val.iter().skip(i).step_by(lp.eq_ph.a.ncols).filter(|b| **b != 0.0).count() == 1 {
                    curr_bvar = lp.eq_ph.a.val.iter().skip(i).step_by(lp.eq_ph.a.ncols).enumerate().find_or_first(|b| *b.1 != 0.0).map(|x| x.0).expect("No row found");
                    b_vars[curr_bvar] = i;
                    let corr = ph.val[curr_bvar*ph.ncols+i+1];
                    if corr != 1.0 {
                        let mut tmp = Vec::with_capacity(ph.val.len());
                        for k in 0..ph.val.len(){
                            if k >= curr_bvar*ph.ncols && k < curr_bvar*ph.ncols+ph.ncols {
                                tmp.push(ph.val[k]/corr);
                            } else {
                                tmp.push(ph.val[k]);
                            }
                        }
                    }
                    bfs_x.remove(i-removed_items);
                    removed_items += 1;
                }
            } else {
                n_vars.push(i);
                bfs_x.remove(i- removed_items);
                removed_items += 1;
            }

        }
        // Adjust matrix to accomodate for basis which won't result in substitutions
        let mut remains: Vec<usize> = b_vars.iter().enumerate().filter(|b| *b.1 >= lp.eq_ph.a.ncols).map(|x| x.0).collect();
        removed_items = 0;
        for i in 0..remains.len(){
            for j in 0..bfs_x.len(){
                if bfs.x[bfs_x[j]] != lp.eq_ph.bounds[remains[i-removed_items]].1 {
                    b_vars[remains[i-removed_items]] = bfs_x[j];
                    if ph.val[remains[i-removed_items]*ph.ncols + bfs_x[j] + 1] == 0.0 {
                        let mut tmp: Option<usize> = None;
                        for k in 0..remains.len() {
                            if ph.val[remains[k]*ph.ncols + bfs_x[j] + 1] != 0.0 {
                                tmp = Some(remains[k]);
                                break;
                            }
                        }
                        if tmp.is_none() {
                            panic!{"Could not setup problem with given bfs"};
                        } else {
                            ph = linalg::row_addition(&ph, remains[i-removed_items], tmp.expect("No valid row"), None);
                        }
                    }
                    for k in 0..lp.eq_ph.a.nrows{
                        if remains[i-removed_items] != k {
                            ph = linalg::gauss_elimination(&ph, k, remains[i-removed_items], bfs_x[j]+1);
                        } else {
                            let corr = ph.val[remains[i-removed_items]*ph.ncols+bfs_x[j]+1];
                            if corr != 1.0 {
                                let mut tmp = Vec::with_capacity(ph.val.len());
                                for l in 0..ph.val.len(){
                                    if l >= remains[i-removed_items]*ph.ncols && l < remains[i-removed_items]*ph.ncols+ph.ncols {
                                        tmp.push(ph.val[l]/corr);
                                    } else {
                                        tmp.push(ph.val[l]);
                                    }
                                }
                                ph.val = tmp;
                            }
                        }
                    }
                    bfs_x.remove(j);
                    remains.remove(i-removed_items);
                    removed_items += 1;
                    break;
                }
            }
        }
        // Add remaining bfs variables to complete the basis
        removed_items = 0;
        for i in 0..remains.len(){
            for j in 0..bfs_x.len(){
                if ph.val[remains[i-removed_items]*ph.ncols + bfs_x[j] + 1] == 0.0 {
                    let mut tmp: Option<usize> = None;
                    for k in 0..remains.len() {
                        if ph.val[remains[k]*ph.ncols + bfs_x[j] + 1] != 0.0 {
                            tmp = Some(remains[k]);
                            break;
                        }
                    }
                    if tmp.is_none() {
                        if j == bfs_x.len()-1 {
                            panic!("Could not setup problem with given bfs");
                        } else {
                            continue;
                        }
                    } else {
                        ph = linalg::row_addition(&ph, remains[i-removed_items], tmp.expect("No valid row"), None);
                    }
                }
                b_vars[remains[i-removed_items]] = bfs_x[j];
                for k in 0..lp.eq_ph.a.nrows{
                    if remains[i-removed_items] != k {
                        ph = linalg::gauss_elimination(&ph, k, remains[i-removed_items], bfs_x[j]+1);
                    } else {
                        let corr = ph.val[remains[i-removed_items]*ph.ncols+bfs_x[j]+1];
                        if corr != 1.0 {
                            let mut tmp = Vec::with_capacity(ph.val.len());
                            for l in 0..ph.val.len(){
                                if l >= remains[i-removed_items]*ph.ncols && l < remains[i-removed_items]*ph.ncols+ph.ncols {
                                    tmp.push(ph.val[l]/corr);
                                } else {
                                    tmp.push(ph.val[l]);
                                }
                            }
                            ph.val = tmp;
                        }
                    }
                }
                bfs_x.remove(j);
                remains.remove(i-removed_items);
                removed_items += 1;
                break;
            }
        }
        // Perform substitutions for the remaining non-zero variables in the bfs
        for i in 0..bfs_x.len() {
            if bfs.x[bfs_x[i]] == lp.eq_ph.bounds[bfs_x[i]].1 {
                (a, b, c, sub_vars) = _perform_ub_substitution(&linalg::get_columns(&ph, &(1..(ph.ncols)).collect()), &linalg::get_columns(&ph, &vec![0]).val, &c, &bfs_x[i], &lp.eq_ph.bounds[bfs_x[i]].1, &sub_vars);
                ph = a.insert_column(0, b);
                n_vars.push(bfs_x[i]);
                
            } else {
                panic!("Could not setup problem with given bfs");
            }
        }
        if remains.len() > 0 && bfs_x.len() > 0 {
            panic!("Could not setup problem with given bfs");
        }
        // If missing variables in basis, add from n_vars
        removed_items = 0;
        for i in 0..remains.len(){
            for j in 0..lp.eq_ph.a.ncols{
                if ph.val[remains[i]*ph.ncols + j + 1] != 0.0 && !b_vars.contains(&j){
                    for k in 0..lp.eq_ph.a.nrows{
                        if remains[i-removed_items] != k {
                            ph = linalg::gauss_elimination(&ph, k, remains[i-removed_items], j+1);
                        } else {
                            let corr = ph.val[remains[i-removed_items]*ph.ncols+j+1];
                            if corr != 1.0 {
                                let mut tmp = Vec::with_capacity(ph.val.len());
                                for l in 0..ph.val.len(){
                                    if l >= remains[i-removed_items]*ph.ncols && l < remains[i-removed_items]*ph.ncols+ph.ncols {
                                        tmp.push(ph.val[l]/corr);
                                    } else {
                                        tmp.push(ph.val[l]);
                                    }
                                }
                                ph.val = tmp;
                            }
                        }
                    }
                    b_vars[remains[i]] = j;
                    let to_remove = n_vars.iter().position(|x| *x==j).unwrap() ;
                    n_vars.remove(to_remove);
                    break;
                }
            }
            remains.remove(i - removed_items);
            removed_items += 1;
        }
        if remains.len() > 0 {
            panic!("Could not setup problem with given bfs");
        }
        return (ph, b_vars, n_vars, c, sub_vars)
    }
    
    //Initialization
    let (ph, mut b_vars, mut n_vars, mut c_new, mut sub_vars) = _setup(lp, bfs);
    let mut x_b = Matrix{val: b_vars.iter().map(|x| bfs.x[*x]).collect(), ncols: 1, nrows: b_vars.len()};
    let mut b_inv = linalg::identity_matrix(b_vars.len());
    let mut c_tilde_n: Vec<f64> = Vec::with_capacity(n_vars.len());
    let mut a = linalg::get_columns(&ph, &(1..ph.ncols).collect());
    let mut b = linalg::get_columns(&ph, &vec![0]).val;
    for i in 0..n_vars.len(){
        c_tilde_n.push(lp.of[n_vars[i]] - Matrix{val:  b_vars.iter().map(|i| lp.of[*i]).collect(),
            ncols: b_vars.len(),
            nrows: 1}.dot(&b_inv).dot(&linalg::get_columns(&a, &n_vars)).val[i]);
    }
    let mut b_inv_tilde: Matrix;
    let mut status_code: usize = 1;
    //Iteration start
    while c_tilde_n.iter().any(|x| *x > 0.0) {
        let c_tilde_n_max = c_tilde_n.iter().cloned().fold(0./0., f64::max);
        let incoming_variable_index = c_tilde_n.iter().position(|&x| x == c_tilde_n_max).unwrap();
        let incoming_variable = n_vars[incoming_variable_index];
        let b_inv_n_j = b_inv.dot(&Matrix { val : a.val.iter().skip(incoming_variable).step_by(a.ncols).copied().collect(), ncols: 1, nrows: a.nrows});
        let mut _t1 = x_b.ge_divide(&b_inv_n_j);
        let t1 = _t1.val.iter().cloned().fold(0.0/0.0, f64::min);
        let t2 = lp.eq_ph.bounds[incoming_variable].1;
        let _t3 = linalg::get_columns(&Matrix{val: lp.eq_ph.bounds.iter().map(|x| x.1).collect(), nrows:1, ncols: lp.eq_ph.bounds.len()}, &b_vars).subtract(&x_b.transpose()).ge_divide(&Matrix{ val: b_inv_n_j.val.iter().map(|x| -x).collect(), ncols: b_inv_n_j.ncols, nrows: b_inv_n_j.nrows}.transpose());
        let t3 = _t3.val.iter().cloned().fold(0.0/0.0, f64::min);
        if f64::min(f64::min(t1, t2), t3) == f64::MAX {
            // Problem is unbounded
            (b_vars, n_vars) = _update_basis(&b_vars, &n_vars, incoming_variable_index, 0);
            status_code = 6;
            break;
        } else if t3 < t1 && t3 < t2 {
            let mut outgoing_variable = 0;
            for i in 0.._t3.val.len(){
                if _t3.val[i] == t3 && b_vars[i] > outgoing_variable {
                    outgoing_variable = b_vars[i];
                }
            }
            let outgoing_variable_index = b_vars.iter().position(|&x| x==outgoing_variable).unwrap();
            (a, b, c_new, sub_vars) = _perform_ub_substitution(&a.clone(), &b.to_vec(), &c_new.to_vec(), &outgoing_variable, &lp.eq_ph.bounds[outgoing_variable].1, &sub_vars);
            b_inv_tilde = _update_constraint_column(&b_inv_n_j, outgoing_variable_index, &b_inv, &b_vars);
            (b_vars, n_vars) = _update_basis(&b_vars, &n_vars, incoming_variable_index, outgoing_variable_index);
        } else if t2 < t1 {
            (a, b, c_new, sub_vars) = _perform_ub_substitution(&a.clone(), &b.to_vec(), &c_new.to_vec(), &incoming_variable, &lp.eq_ph.bounds[incoming_variable].1, &sub_vars);
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
    // Re substitute variables
    let mut x = vec![0.0; lp.eq_ph.a.ncols];
    for i in 0..b_vars.len(){
        x[b_vars[i]] = x_b.val[i];
    }
    for i in 0..sub_vars.len(){
        x[sub_vars[i]] = lp.eq_ph.bounds[sub_vars[i]].1 - x[sub_vars[i]];
    }
    let z = lp.of.iter().zip(x.iter()).map(|(x, y)| x*y).sum();
    return (Solution {x, z, status_code },
        StandardFormLP{ eq_ph: Polyhedron {a: Matrix { val: b_inv.dot(&lp.eq_ph.a).val, ncols: lp.eq_ph.a.ncols, nrows: lp.eq_ph.a.nrows }, b: b_inv.dot(&Matrix {val: lp.eq_ph.b.clone(), ncols: 1, nrows: lp.eq_ph.b.len()}).val, bounds: lp.eq_ph.bounds.clone()}, of: lp.of.clone()})
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_solver_1(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![1.0, 1.0, 0.0, 0.0, 1.0, 1.0],
                          nrows: 2,
                          ncols: 3},
                b: vec![1.0, 1.0],
                bounds: vec![(0.0,1.0), (0.0,1.0), (0.0,1.0)]
            },
            eq_ph: Default::default(),
            of: vec![1.0,1.0,1.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 3);
        assert_eq!(sol.x, vec![1, 1, 1]);
    }
    #[test]
    fn test_solver_2(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-2.0, -1.0, -1.0, -1.0, -1.0, 0.0],
                          nrows: 3,
                          ncols: 2},
                b: vec![-100.0, -80.0, -40.0],
                bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX)]
            },
            eq_ph: Default::default(),
            of: vec![30.0,20.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 1800);
        assert_eq!(sol.x, vec![20, 60]);
    }
    #[test]
    fn test_solver_3(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-2.0, -1.0, -1.0, -1.0],
                          nrows: 2,
                          ncols: 2},
                b: vec![-100.0, -80.0],
                bounds: vec![(0.0,40.0), (0.0,30.0)]
            },
            eq_ph: Default::default(),
            of: vec![30.0,20.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 1650);
        assert_eq!(sol.x, vec![35, 30]);
    }
    #[test]
    fn test_solver_4(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![2.0, -1.0, -1.0, -2.0, -1.0, 0.0, 0.0, -1.0, 1.0, 0.0, 1.0, -1.0],
                          nrows: 4,
                          ncols: 3},
                b: vec![1.0, -5.0, 1.0, -1.0],
                bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX), (0.0,f64::MAX)]
            },
            eq_ph: Default::default(),
            of: vec![-2.0,-1.0, -1.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, -3);
        assert_eq!(sol.x, vec![1, 0, 1]);
    }
    #[test]
    fn test_solver_5(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-1.0, 1.0, -2.0, 1.0, 0.0, -1.0],
                          nrows: 3,
                          ncols: 2},
                b: vec![-2.0, -4.0, -2.0],
                bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX)]
            },
            eq_ph: Default::default(),
            of: vec![1.0, 1.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 5);
        assert_eq!(sol.x, vec![3, 2]);
    }

    #[test]
    fn test_solver_6(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-5.0, -4.0],
                          nrows: 1,
                          ncols: 2},
                b: vec![-21.0],
                bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX)]
            },
            eq_ph: Default::default(),
            of: vec![5.0, 2.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 20);
        assert_eq!(sol.x, vec![4, 0]);
    }

    #[test]
    fn test_solver_7(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-4.0, -2.0, -2.0, -3.0],
                          nrows: 1,
                          ncols: 4},
                b: vec![-7.0],
                bounds: vec![(0.0,1.0), (0.0,1.0), (0.0,1.0), (0.0,1.0)]
            },
            eq_ph: Default::default(),
            of: vec![7.0, 3.0, 2.0, 2.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 10);
        assert_eq!(sol.x, vec![1,1,0,0]);
    }

    #[test]
    fn test_solver_8(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![1.0, 4.0, 3.0, 2.0],
                            nrows: 2,
                            ncols: 2},
                b: vec![4.0, 6.0],
                bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX)]
            },
            eq_ph: Default::default(),
            of: vec![-4.0, -5.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, -13);
        assert_eq!(sol.x, vec![2,1]);
    }
    #[test]
    fn test_solver_9(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![4.0, -3.0, -3.0, -2.0],
                            nrows: 2,
                            ncols: 2},
                b: vec![-6.0, -18.0],
                bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX)]
            },
            eq_ph: Default::default(),
            of: vec![1.0, 5.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 23);
        assert_eq!(sol.x, vec![3,4]);
    }
    #[test]
    fn test_solver_10(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-5.0, -7.0, -1.0, 0.0, 0.0, -1.0],
                            nrows: 3,
                            ncols: 2},
                b: vec![-35.0, -3.0, -4.0],
                bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX)]
            },
            eq_ph: Default::default(),
            of: vec![5.0, 6.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 29);
        assert_eq!(sol.x, vec![1,4]);
    }
    #[test]
    fn test_solver_11(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-4.0, -2.0, -3.0, -1.0],
                            nrows: 1,
                            ncols: 4},
                b: vec![-7.0],
                bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX), (0.0,f64::MAX), (0.0,f64::MAX)]
            },
            eq_ph: Default::default(),
            of: vec![18.0, 8.0, 4.0, 2.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 28);
        assert_eq!(sol.x, vec![1, 1, 0, 1]);
    }
    #[test]
    fn test_solver_12(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-6.0, -10.0, -15.0, -10.0],
                            nrows: 1,
                            ncols: 4},
                b: vec![-36.0],
                bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX), (0.0,f64::MAX), (0.0,f64::MAX)]
            },
            eq_ph: Default::default(),
            of: vec![5.0, 10.0, 10.0, 16.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 53);
        assert_eq!(sol.x, vec![1, 0, 0, 3]);
    }
    #[test]
    fn test_solver_13(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-2.0, -3.0, -3.0],
                            nrows: 1,
                            ncols: 3},
                b: vec![-9.0],
                bounds: vec![(0.0,2.0), (0.0,2.0), (0.0,2.0)]
            },
            eq_ph: Default::default(),
            of: vec![5.0, 6.0, 7.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 20);
        assert_eq!(sol.x, vec![0, 1, 2]);
    }
    #[test]
    fn test_solver_14(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-1.0, -2.0, -1.0, 0.0, 0.0, -2.0, -4.0, -3.0, -7.0, -3.0],
                            nrows: 2,
                            ncols: 5},
                b: vec![-2.0, -13.0],
                bounds: vec![(0.0,1.0), (0.0,1.0), (0.0,1.0), (0.0,1.0), (0.0,1.0) ]
            },
            eq_ph: Default::default(),
            of: vec![5.0, 7.0, 6.0, 4.0, 5.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 16);
        assert_eq!(sol.x, vec![1, 0, 1, 0, 1]);
    }
    #[test]
    fn test_solver_15(){
        let lp: LinearProgram = LinearProgram {
            ge_ph: Polyhedron {
                a: Matrix{val: vec![-2.0, -1.0, -2.0, -1.0],
                            nrows: 1,
                            ncols: 4},
                b: vec![-4.0],
                bounds: vec![(0.0,1.0), (0.0,1.0), (0.0,1.0), (0.0,1.0) ]
            },
            eq_ph: Default::default(),
            of: vec![5.0, 8.0, 4.0, 6.0]
        };
        let sol = LinearProgram::solve_ilp(&lp, None);
        assert_eq!(sol.z, 19);
        assert_eq!(sol.x, vec![1, 1, 0, 1]);
    }
    

    
}
