//! # Simplex solver
//! 
//! Simplex solver producing integer solutions for linear programs.
//! 
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
    /// Bool indicating if solution is a basic feasible solution, bfs. 
    pub bfs : bool,
    /// Indices of the variables defined by `ph.a` which are basis variables
    pub b_vars : Vec<usize>,
    /// Indices of the variables defined by `ph.a` which are non basis variables
    pub n_vars : Vec<usize>,
    /// The B inverse matrix from which the solution could be calculated. Given the linear program $B x_B + N x_N = b $ the solution $x_B$ is given by $ x_B = B^{-1} b - B^{-1} N x_N$ where the second term in the RHS is zero.
    /// $B$ is given by `ph.a[b_vars]`, $N$ is given by `ph.a[n_vars]`, $B^{-1}$ is given by `b_inv` and $b$ is given by `ph.b`.
    pub b_inv : Matrix,
    /// A system of linear equations $Ax=b$.
    pub eq_ph: Polyhedron,
    /// Objective function
    pub of: Vec<f64>,
    /// Indices of substituted variables
    pub sub_vars: Vec<usize>
}

impl Clone for Solution {
    fn clone(&self) -> Self {
        return Solution { bfs: self.bfs, b_vars: self.b_vars.clone(), n_vars: self.n_vars.clone(), b_inv: self.b_inv.clone(), eq_ph: self.eq_ph.clone(), of: self.of.clone(), sub_vars: self.sub_vars.clone() }
    }
}

/// Data structure for a linear program
#[derive(Default)]
pub struct LinearProgram {
    /// Polyhedron
    pub ge_ph: Polyhedron,
    /// Objective function
    pub of: Vec<f64>,
    /// Solution
    pub sol: Solution,
}

impl Clone for LinearProgram {
    fn clone(&self) -> Self {
        return LinearProgram { ge_ph: self.ge_ph.clone(), of: self.of.clone(), sol: self.sol.clone() }
    }
    
}


impl LinearProgram {
    /// Get the value of the objective function at the current solution of the linear program
    fn get_sol_val(lp: &LinearProgram) -> f64 {
        let mut of: Vec<f64> = lp.sol.of.to_vec();
        for i in 0..lp.sol.sub_vars.len(){
            of[lp.sol.sub_vars[i]] = -of[lp.sol.sub_vars[i]];
        }
        Matrix{val: of, ncols: lp.sol.of.len(), nrows: 1 }.dot(&LinearProgram::get_sol(lp)).val[0]
    }
    /// Get the variable values at the current solution on the linear program
    fn get_sol(lp: &LinearProgram) -> Matrix {
        let xb = lp.sol.b_inv.dot(&Matrix{val: lp.sol.eq_ph.b.to_vec(), ncols: 1, nrows: lp.sol.eq_ph.b.len()});
        let mut res = vec![0.; lp.sol.eq_ph.a.ncols];
        for i in 0..lp.sol.b_vars.len(){
            res[lp.sol.b_vars[i]] = xb.val[i];
        }
        for i in 0..lp.sol.sub_vars.len(){
            res[lp.sol.sub_vars[i]] = lp.sol.eq_ph.bounds[lp.sol.sub_vars[i]].1 - res[lp.sol.sub_vars[i]];
        }
        return Matrix { val: res.to_vec(), ncols: 1, nrows: res.len() }
    }
    fn _preprocess(lp: &LinearProgram) -> LinearProgram {
        // Handle lower bounds above and below zero
        let mut new_a_val = lp.ge_ph.a.val.to_vec();
        let mut new_b = lp.ge_ph.b.to_vec();
        let mut new_nrows = lp.ge_ph.a.nrows;
        let mut new_ncols = lp.ge_ph.a.ncols;
        let mut new_bounds = lp.ge_ph.bounds.to_vec();
        let mut new_of = lp.of.to_vec();
        for i in 0..new_ncols {
            // Add new constraint to force variable i to be above its lower bound
            if new_bounds[i].0 > 0.0 {
                let mut tmp = vec![0.0; new_ncols];
                tmp[i] = 1.0;
                new_a_val.extend(tmp);
                new_b.push(new_bounds[i].0);
                new_bounds[i].0 = 0.0;
                new_nrows = new_nrows + 1;
            }
            if new_bounds[i].0 < 0.0 {
                let tmp_a = new_a_val.to_vec();
                new_a_val = insert_after_every(&new_a_val.to_vec(), new_nrows, tmp_a.iter().skip(i).step_by(new_ncols).map(|e| -e).collect());
                new_of.push(-new_of[i]);
                new_ncols = new_ncols + 1;
                new_bounds.push((f64::max(0.0, -new_bounds[i].1), -new_bounds[i].0));
            }
        }
        // Introduce slack-variables
        for i in 0..new_nrows {
            let mut tmp = vec![0.0; new_nrows];
            if new_b[i] < 0.0 {
                tmp[i] = 1.0;
                for j in 0..new_ncols{
                    new_a_val[i*new_ncols+j] = -new_a_val[i*new_ncols+j];
                }
                new_b[i] = -new_b[i];
            } else {
                tmp[i] = -1.0;
            }
            new_a_val = insert_after_every(&new_a_val.to_vec(), new_ncols, tmp);
            new_ncols = new_ncols + 1;
            new_bounds.push((0.0, f64::MAX));
            new_of.push(0.);
        }
        
        return LinearProgram {
            ge_ph: lp.ge_ph.clone(),
            of: lp.of.clone(),
            sol: Solution{ bfs: false, b_vars: vec![], n_vars: vec![], b_inv: Matrix { val: vec![], ncols: 0, nrows: 0 }, eq_ph: Polyhedron{
                a: Matrix{val: new_a_val.to_vec(), ncols: new_ncols, nrows: new_nrows},
                b: new_b.to_vec(),
                bounds: new_bounds.to_vec()
            }, of: new_of.to_vec(), sub_vars: lp.sol.sub_vars.to_vec()}}
    }
    fn _phase_one(lp: &LinearProgram) -> LinearProgram {
        let mut new_bvars: Vec<usize> = ((lp.sol.eq_ph.a.ncols - lp.sol.eq_ph.a.nrows)..lp.sol.eq_ph.a.ncols).collect();
        let mut new_binv: Vec<f64> = lp.sol.eq_ph.a.val.iter().enumerate().filter(|x| x.0 % lp.sol.eq_ph.a.ncols >= (lp.sol.eq_ph.a.ncols-lp.sol.eq_ph.a.nrows)).map(|x| *x.1).collect(); //Vec::with_capacity(lp.sol.ph.a.nrows*lp.sol.ph.a.nrows);// = lp.sol.ph.a.val.iter().enumerate().filter(|x| i%);//step_by(lp.sol.ph.a.ncols).take(lp.sol.ph.a.nrows).copied().collect();//lp.sol.ph.a.val.iter().skip(lp.sol.ph.a.ncols - lp.sol.ph.a.nrows).step_by(lp.sol.ph.a.ncols).take(lp.sol.ph.a.nrows).copied().collect(); //lp.sol.ph.a.iter().map(|e| e.iter().cloned().rev().take(new_bvars.len()).collect_vec()).collect();//linalg::identity_matrix(new_bvars.len()).iter().map(|e| e.iter().map(|&f| f as f64).collect()).collect();
        let mut origo_is_bfs = true;
        let mut new_nvars: Vec<usize> = (0..(lp.sol.eq_ph.a.ncols - lp.sol.eq_ph.a.nrows)).collect();
        let mut new_a: Vec<f64> = lp.sol.eq_ph.a.val.to_vec();
        let mut art_var_cnt = 0;
        let mut new_bounds = lp.sol.eq_ph.bounds.to_vec();
        let mut new_of = vec![0.0; lp.sol.eq_ph.a.ncols];
        let mut new_cols = lp.sol.eq_ph.a.ncols;
        let solved_lp: LinearProgram; 
        for i in 0..new_bvars.len() {
            if new_binv[i*lp.sol.eq_ph.a.nrows+i] < 0.0 {
                origo_is_bfs = false;
                let mut tmp = vec![0.0; lp.sol.eq_ph.a.nrows];
                tmp[i] = 1.0;
                new_a = insert_after_every(&new_a, new_cols, tmp);
                new_cols = new_cols + 1;
                new_nvars.push(new_bvars[i]);
                new_bvars[i] = lp.sol.eq_ph.a.ncols + art_var_cnt;
                art_var_cnt = art_var_cnt + 1;
                new_bounds.push((0.0, f64::MAX));
                new_of.push(-1.0);
                new_binv[i*lp.sol.eq_ph.a.nrows+i] = 1.0;
            }
        }
        if origo_is_bfs {
            return LinearProgram{
                ge_ph: lp.ge_ph.clone(),
                of: lp.of.to_vec(),
                sol: Solution{ 
                    bfs: true,
                    b_vars: new_bvars.to_vec(),
                    n_vars: new_nvars.to_vec(),
                    b_inv: Matrix{
                        val: new_binv,
                        ncols: new_bvars.len(),
                        nrows: new_bvars.len()
                    },
                    eq_ph: lp.sol.eq_ph.clone(),
                    of: lp.sol.of.to_vec(),
                    sub_vars: lp.sol.sub_vars.to_vec()}};
        } else {
            solved_lp = revised_simplex(
                LinearProgram{ ge_ph: lp.ge_ph.clone(),
                                   of: lp.of.to_vec(),
                                   sol: Solution { bfs: true,
                                                   b_vars: new_bvars. to_vec(),
                                                   n_vars: new_nvars.to_vec(),
                                                   b_inv: Matrix{ val: new_binv, ncols: lp.sol.eq_ph.a.nrows, nrows: lp.sol.eq_ph.a.nrows},
                                                   eq_ph: Polyhedron{a: Matrix{val: new_a, ncols: new_cols, nrows: lp.sol.eq_ph.a.nrows},
                                                   bounds: new_bounds,
                                                   b: lp.sol.eq_ph.b.to_vec()},
                                                   of: new_of.to_vec(),
                                                   sub_vars: lp.sol.sub_vars.to_vec()},
                                   });
        }
        if get_columns(&Matrix{val: new_of.to_vec(), ncols: new_of.len(), nrows:1}, &solved_lp.sol.b_vars).dot(&solved_lp.sol.b_inv.dot(&Matrix{val: lp.sol.eq_ph.b.to_vec(), ncols: 1, nrows: lp.sol.eq_ph.b.len()})).val[0] < 0.0 {
            // No feasible solution exists
            return LinearProgram{
                ge_ph: lp.ge_ph.clone(),
                of: lp.of.to_vec(),
                sol: Solution{ bfs: false, b_vars: vec![], n_vars: vec![], b_inv: Matrix{val: vec![], ncols: 0, nrows: 0}, eq_ph: Default::default(), of: lp.of.to_vec(), sub_vars: vec![]}};
        } else {
            if solved_lp.sol.b_vars.to_vec().into_iter().filter(|x| *x >= (lp.sol.eq_ph.a.ncols + art_var_cnt)).collect::<Vec<usize>>().len() > 0 {
                panic!("Failed to find bfs");
            }
            new_nvars = solved_lp.sol.n_vars.into_iter().filter(|x| *x < lp.sol.eq_ph.a.ncols).collect();
            new_bounds = solved_lp.sol.eq_ph.bounds.split_at(lp.sol.eq_ph.a.ncols).0.to_vec();
            return LinearProgram{
                ge_ph: lp.ge_ph.clone(),
                of: lp.of.clone(),
                sol: Solution { bfs: solved_lp.sol.bfs, b_vars: solved_lp.sol.b_vars.to_vec(), n_vars: new_nvars.to_vec(), b_inv: solved_lp.sol.b_inv, eq_ph: Polyhedron { a: get_columns(&solved_lp.sol.eq_ph.a, &(0..lp.sol.eq_ph.a.ncols).collect()), b: solved_lp.sol.eq_ph.b.to_vec(), bounds: new_bounds }, of: solved_lp.of.to_vec(), sub_vars: solved_lp.sol.sub_vars.to_vec()}};
        }
    }
    fn _phase_two(lp: &LinearProgram) -> LinearProgram{
        return revised_simplex(lp.clone());
    }
    fn _solve(lp: &LinearProgram) -> LinearProgram {
        if !lp.sol.bfs {
            let mut sol = LinearProgram::_phase_one(lp);
            if sol.sol.bfs {
                sol.sol.of = lp.sol.of.to_vec();
                for i in 0..sol.sol.sub_vars.len(){
                    sol.sol.of[sol.sol.sub_vars[i]] = -sol.sol.of[sol.sol.sub_vars[i]];
                }
                return LinearProgram::_phase_two(&sol)
            }
            else {
                return LinearProgram{ge_ph: lp.ge_ph.clone(), of: lp.of.to_vec(), sol:Default::default()}
            }
        } else {
            LinearProgram::_phase_two(lp)
        }
    }
    /// Solves a linear program with the revisec simplex algorithm and produces an integer solution using the Land-Doig-Dakins algorithm. 
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
    /// let (z, x, info) = LinearProgram::solve(&LinearProgram {
    ///                 ge_ph: Polyhedron {
    ///                         a: Matrix{val: vec![-2.0, -1.0, -1.0, -1.0, -1.0, 0.0],
    ///                         nrows: 3,
    ///                         ncols: 2},
    ///                         b: vec![-100.0, -80.0, -40.0],
    ///                         bounds: vec![(0.0,f64::MAX), (0.0,f64::MAX)]
    ///                 },
    ///                 of: vec![30.0, 20.0],
    ///                 sol: Default::default()
    ///             });
    /// ```
    pub fn solve(lp: &LinearProgram) -> (i64, Vec<i64>, &str){
        let mut z_lb: f64 = f64::MIN;
        let mut current_best_sol: LinearProgram = Default::default();
        let mut nodes_to_explore = vec![LinearProgram{ge_ph: lp.ge_ph.clone(), of: lp.of.to_vec(), sol:lp.sol.clone()}]; 
        let mut explored_nodes: Vec<Vec<(f64, f64)>> = vec![];
        let mut current_lp: LinearProgram;
        let mut sol: LinearProgram;
        let mut sol_info:&str = "No feasible solution exists";
        while nodes_to_explore.len() > 0 {
            current_lp = LinearProgram::_preprocess(nodes_to_explore.pop().as_ref().expect("No LinearProgram in vector"));
            sol = LinearProgram::_solve(&current_lp);
            if !sol.sol.bfs {
                // No feasible solution in this area
               continue
            }
            if LinearProgram::get_sol_val(&sol) < z_lb {
                // Not possible to find better solution in this area
               continue
            } else if LinearProgram::get_sol(&sol).val.iter().position(|x| (x%1.0) > 0.0000001).is_none() || LinearProgram::get_sol(&sol).val.iter().position(|x| (x%1.0) > 0.0000001).unwrap() >= current_lp.ge_ph.a.ncols {
                // We've found a best solution in this area
                if LinearProgram::get_sol_val(&sol) == z_lb {
                    sol_info = "Solution is not unique";
                } else {
                    z_lb = LinearProgram::get_sol_val(&sol);
                    current_best_sol = sol;
                    sol_info = "Solution exists";
                }
                continue
            } else {
                let first_non_int = LinearProgram::get_sol(&sol).val.iter().position(|x| (x%1.0) > 0.0000001).unwrap();
                
                let mut bounds1 = sol.ge_ph.bounds.to_vec();
                bounds1[first_non_int].1 = f64::floor(LinearProgram::get_sol(&sol).val[first_non_int]);
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
                    nodes_to_explore.push(LinearProgram{ge_ph: Polyhedron{ a: sol.ge_ph.a.clone(), b: sol.ge_ph.b.to_vec(), bounds: bounds1.to_vec()}, of: sol.of.to_vec(), sol: Default::default()});
                }
                let mut node_explored = false;
                let mut bounds2 = sol.ge_ph.bounds.to_vec();
                bounds2[first_non_int].0 = f64::ceil(LinearProgram::get_sol(&sol).val[first_non_int]);
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
                    nodes_to_explore.push(LinearProgram{ge_ph: Polyhedron{ a: sol.ge_ph.a.clone(), b: sol.ge_ph.b.to_vec(), bounds: bounds2.to_vec()}, of: sol.of.to_vec(), sol: Default::default()});
                }
            }
        }
        let res: Vec<i64> = LinearProgram::get_sol(&current_best_sol).val.iter().map(|x| *x as i64).collect();
        return (z_lb as i64, res[..lp.ge_ph.a.ncols].to_vec(), sol_info);
    }
}
fn insert_after_every<T>(ts: &Vec<T>, after: usize, elem: Vec<T>) -> Vec<T>
where
    T: Clone
{
    let mut result = Vec::new();
    let mut j = 0;
    for (i, e) in ts.into_iter().enumerate() {
        result.push(e.clone());
        if (i + 1) % after == 0 {
            result.push(elem[j].clone());
            j = j + 1;
        }
    }
    return result
}

pub fn revised_simplex(lp: LinearProgram) -> LinearProgram {
//pub fn revised_simplex(a_eq: Matrix, bounds: Vec<(f64, f64)>, b_eq: Vec<f64>, c: Vec<f64>, bfs: Solution) -> Solution {
    fn _update_constraint_column(b_inv_n_j: &Matrix, index: usize, b_inv: &Matrix, b_vars: &Vec<usize>) -> Matrix {
        let mut e = linalg::identity_matrix(b_vars.len());//E = numpy.eye(self.B_vars.shape[0])
        e.val = update_column(&e.clone(), index, &Matrix{val: (b_inv_n_j.val).iter().map(|x| -x).collect(), nrows: b_inv_n_j.nrows, ncols: b_inv_n_j.ncols}.divide(&Matrix{val: vec![(b_inv_n_j.val)[index]], ncols: 1, nrows:1}).val).val;
        e.val[index*e.ncols + index] = if b_inv_n_j.val[index] != 0. {1./b_inv_n_j.val[index]} else {f64::MAX}; //numpy.divide(1, B_inv_N_j[index], out=numpy.repeat(numpy.inf, 1), where=B_inv_N_j[index]!=0)
        e.dot(&b_inv) //return numpy.dot(E, B_inv)
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
            b.push(b_eq[i] - limit*a_eq.val[i*a_eq.ncols+variable]); //b_eq - limit*A[:, variable]
        } 
        let a = a_eq.val.iter().enumerate().map(|x| if x.0%a_eq.ncols == *variable {-*x.1} else {*x.1}).collect(); //A[:, variable] = -A[:, variable]
        let mut c_new = c.to_vec();
        c_new[*variable] = -c[*variable]; //C[variable] = -C[variable]
        let mut sub_vars = substituted_vars.to_vec();
        sub_vars.push(*variable);
        return (Matrix{val: a, ncols: a_eq.ncols, nrows: a_eq.nrows}, b, c_new, sub_vars)
    }
    if !lp.sol.bfs {
        panic!("There must be a basic feasible solution in order to use this function");
    }
    let mut c_tilde_n: Vec<f64> = Vec::with_capacity(lp.sol.n_vars.len()); //C_tilde_N = C_N - numpy.dot(numpy.dot(C_B, self.B_inv), N)
    for i in 0..lp.sol.n_vars.len(){
        c_tilde_n.push(lp.sol.of[lp.sol.n_vars[i]] - Matrix{val:  lp.sol.b_vars.iter().map(|i| lp.sol.of[*i]).collect(),
            ncols: lp.sol.b_vars.len(),
            nrows: 1}.dot(&lp.sol.b_inv).dot(&get_columns(&lp.sol.eq_ph.a, &lp.sol.n_vars)).val[i]);
    }
    let mut x_b = lp.sol.b_inv.dot(&Matrix{val: lp.sol.eq_ph.b.to_vec(), ncols: 1, nrows: lp.sol.eq_ph.b.len()}); // X_B = numpy.dot(self.B_inv, self.b) # X values a current solution
    let mut n_vars = lp.sol.n_vars.to_vec();
    let mut b_vars = lp.sol.b_vars.to_vec();
    let mut b_inv = lp.sol.b_inv.clone();
    let mut a = lp.sol.eq_ph.a.clone();
    let mut b = lp.sol.eq_ph.b.to_vec();
    let mut c_new = lp.sol.of.to_vec();
    let mut sub_vars: Vec<usize> = lp.sol.sub_vars;
    let mut b_inv_tilde: Matrix;
    while c_tilde_n.iter().any(|x| *x > 0.0) {
        // incoming_candidates = self.N_vars[C_tilde_N == C_tilde_N.max()]
        let c_tilde_n_max = c_tilde_n.iter().cloned().fold(0./0., f64::max);
        let incoming_variable_index = c_tilde_n.iter().position(|&x| x == c_tilde_n_max).unwrap();
        let incoming_variable = n_vars[incoming_variable_index];
        let b_inv_n_j = b_inv.dot(&Matrix { val : a.val.iter().skip(incoming_variable).step_by(a.ncols).copied().collect(), ncols: 1, nrows: a.nrows}); //B_inv_N_j = numpy.dot(self.B_inv, self.A[:, incoming_variable])
        let mut _t1 = x_b.ge_divide(&b_inv_n_j); // _t1 = numpy.divide(X_B, B_inv_N_j, out=numpy.repeat(numpy.inf, X_B.shape[0]), where=B_inv_N_j>0)
        let t1 = _t1.val.iter().cloned().fold(0.0/0.0, f64::min);// t1 = _t1.min()
        let t2 = lp.sol.eq_ph.bounds[incoming_variable].1; // t2 = self.bounds_upper[incoming_variable]
        let _t3 = get_columns(&Matrix{val: lp.sol.eq_ph.bounds.iter().map(|x| x.1).collect(), nrows:1, ncols: lp.sol.eq_ph.bounds.len()}, &b_vars).subtract(&x_b.transpose()).ge_divide(&Matrix{ val: b_inv_n_j.val.iter().map(|x| -x).collect(), ncols: b_inv_n_j.ncols, nrows: b_inv_n_j.nrows}.transpose());// _t3 = numpy.divide(self.bounds_upper[self.B_vars]-X_B, -B_inv_N_j, out=numpy.repeat(numpy.inf, X_B.shape[0]), where=B_inv_N_j<0)
        let t3 = _t3.val.iter().cloned().fold(0.0/0.0, f64::min);// t3 = _t3.min()
        if f64::min(f64::min(t1, t2), t3) == f64::MAX {
            // Problem is unbounded
            b_inv = _update_constraint_column(&b_inv_n_j, 0, &b_inv, &b_vars);
            (b_vars, n_vars) = _update_basis(&b_vars, &n_vars, incoming_variable_index, 0);
            return LinearProgram{ge_ph: lp.ge_ph, of: lp.of, sol: Solution { bfs: true, b_vars: b_vars, n_vars: n_vars, b_inv: b_inv, eq_ph: lp.sol.eq_ph, of: c_new, sub_vars: sub_vars}}
        } else if t3 < t1 && t3 < t2 {
            let mut outgoing_variable = 0;
            for i in 0.._t3.val.len(){
                if _t3.val[i] == t3 && b_vars[i] > outgoing_variable {
                    outgoing_variable = b_vars[i];
                }
            }
            //let outgoing_variable = b_vars[_t3.val.into_iter().filter(|&x| x==t3).collect::<Vec<f64>>().max()]; //numpy.min(self.B_vars[_t3==t3])
            let outgoing_variable_index = b_vars.iter().position(|&x| x==outgoing_variable).unwrap(); //numpy.argwhere(self.B_vars==outgoing_variable)[0][0]
            (a, b, c_new, sub_vars) = _perform_ub_substitution(&a.clone(), &b.to_vec(), &c_new.to_vec(), &outgoing_variable, &lp.sol.eq_ph.bounds[outgoing_variable].1, &sub_vars); //self.A, self.b, C, self.substituted_vars = _perform_ub_substitution(self.A, self.b, C, outgoing_variable, self.bounds_upper[outgoing_variable], self.substituted_vars)
            b_inv_tilde = _update_constraint_column(&b_inv_n_j, outgoing_variable_index, &b_inv, &b_vars);//B_inv_tilde = _update_constraint_column(B_inv_N_j, outgoing_variable_index, self.B_inv)
            (b_vars, n_vars) = _update_basis(&b_vars, &n_vars, incoming_variable_index, outgoing_variable_index);//self.B_vars, self.N_vars = _update_basis(self.B_vars, self.N_vars, incoming_variable_index, outgoing_variable_index)
        } else if t2 < t1 {
            (a, b, c_new, sub_vars) = _perform_ub_substitution(&a.clone(), &b.to_vec(), &c_new.to_vec(), &incoming_variable, &lp.sol.eq_ph.bounds[incoming_variable].1, &sub_vars);// self.A, self.b, C, self.substituted_vars = _perform_ub_substitution(self.A, self.b, C, incoming_variable, self.bounds_upper[incoming_variable], self.substituted_vars)
            b_inv_tilde = b_inv.clone(); // B_inv_tilde = self.B_inv
        } else {
            let outgoing_variable: Option<usize> = _t1.val.iter().enumerate().filter(|(_, &r)| r == t1).map(|(index, _)| *b_vars.get(index).expect("did not find index")).max();
            //let outgoing_variable = b_vars[_t1.val.iter().filter(|&x| x==t1).unwrap().max()]; // outgoing_variable = numpy.min(self.B_vars[_t1==t1])
            let outgoing_variable_index = b_vars.iter().position(|&x| x==outgoing_variable.unwrap()).unwrap(); // outgoing_variable_index = numpy.argwhere(self.B_vars==outgoing_variable)[0][0]
            b_inv_tilde = _update_constraint_column(&b_inv_n_j, outgoing_variable_index, &b_inv, &b_vars); // B_inv_tilde = _update_constraint_column(B_inv_N_j, outgoing_variable_index, self.B_inv)
            (b_vars, n_vars) = _update_basis(&b_vars, &n_vars, incoming_variable_index, outgoing_variable_index); // self.B_vars, self.N_vars = _update_basis(self.B_vars, self.N_vars, incoming_variable_index, outgoing_variable_index)
        }
        b_inv = b_inv_tilde.clone(); //self.B_inv = B_inv_tilde
        //C_N = C[self.N_vars]
        //C_B = C[self.B_vars]
        for i in 0..n_vars.len(){
            c_tilde_n[i] = c_new[n_vars[i]] - Matrix{val: b_vars.iter().map(|j| c_new[*j]).collect(),
                                                             ncols: b_vars.len(),
                                                             nrows: 1}.dot(&b_inv_tilde).dot(&get_columns(&a, &n_vars)).val[i];
        } //C_tilde_N = C_N - numpy.dot(numpy.dot(C_B, B_inv_tilde), self.A[:, self.N_vars])
        x_b = b_inv.dot(&Matrix{val: b.to_vec(), ncols: 1, nrows: b.len()}); //X_B = numpy.dot(self.B_inv, self.b) # X values a current solution
    }
    return LinearProgram{ge_ph: lp.ge_ph.clone(), of: lp.of, sol: Solution { bfs: true, b_vars, n_vars, b_inv, eq_ph: Polyhedron { a: a, b: b.to_vec(), bounds: lp.sol.eq_ph.bounds }, of: c_new, sub_vars: sub_vars }}
}

pub fn get_columns(v: &Matrix, ind: &Vec<usize>) -> Matrix {
    let mut result: Vec<f64> = Vec::with_capacity(ind.len());
    for i in 0..v.nrows {
        result.extend(ind.iter().map(|j| v.val[i*v.ncols+j]).collect::<Vec<f64>>());
    }
    return Matrix { val: result, ncols: ind.len(), nrows: v.nrows }   
}

pub fn update_column(m: &Matrix, ind: usize, v: &Vec<f64>) -> Matrix{
    if m.nrows != v.len() {
        panic!("Dimension does not match");
    }
    let mut result = m.val.to_vec();
    for i in 0..v.len() {
        result[i*m.ncols+ind] = v[i];
    }
    Matrix { val: result, ncols: m.ncols, nrows: m.nrows}
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
            of: vec![1.0,1.0,1.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 3);
        assert_eq!(sol, vec![1, 1, 1]);
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
            of: vec![30.0,20.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 1800);
        assert_eq!(sol, vec![20, 60]);
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
            of: vec![30.0,20.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 1650);
        assert_eq!(sol, vec![35, 30]);
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
            of: vec![-2.0,-1.0, -1.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, -3);
        assert_eq!(sol, vec![1, 0, 1]);
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
            of: vec![1.0, 1.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 5);
        assert_eq!(sol, vec![3, 2]);
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
            of: vec![5.0, 2.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 20);
        assert_eq!(sol, vec![4, 0]);
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
            of: vec![7.0, 3.0, 2.0, 2.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 10);
        assert_eq!(sol, vec![1,1,0,0]);
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
            of: vec![-4.0, -5.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, -13);
        assert_eq!(sol, vec![2,1]);
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
            of: vec![1.0, 5.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 23);
        assert_eq!(sol, vec![3,4]);
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
            of: vec![5.0, 6.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 29);
        assert_eq!(sol, vec![1,4]);
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
            of: vec![18.0, 8.0, 4.0, 2.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 28);
        assert_eq!(sol, vec![1, 1, 0, 1]);
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
            of: vec![5.0, 10.0, 10.0, 16.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 53);
        assert_eq!(sol, vec![1, 0, 0, 3]);
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
            of: vec![5.0, 6.0, 7.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 20);
        assert_eq!(sol, vec![0, 1, 2]);
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
            of: vec![5.0, 7.0, 6.0, 4.0, 5.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 16);
        assert_eq!(sol, vec![1, 0, 1, 0, 1]);
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
            of: vec![5.0, 8.0, 4.0, 6.0],
            sol: Default::default()
        };
        let (z, sol, _) = LinearProgram::solve(&lp);
        assert_eq!(z, 19);
        assert_eq!(sol, vec![1, 1, 0, 1]);
    }

    
}
