//! # Polyhedron data structures and functions
//! 
//! Ease work for preparing solving (integer) linear programs.

use std::cmp;

use linalg::Matrix;

use crate::linalg::{self, CsrMatrix};

/// Data structure for linear inequalities on the following form
/// $$ c_0 * v_0 + c_1 * v_1 + ... + c_n * v_n + bias \ge 0 $$ for $ c \in $ `coeffs` and $ v $ are variables which can take on the values
/// given by `bounds`. `Indices` represents the global indices of the variables. Note that the length of `coeffs`, `bounds` and `indices` must be the same.
#[derive(Hash)]
pub struct GeLineq {
    /// `id` may be used as a reference for later purposes
    pub id      : Option<u32>,
    /// Coefficients of the linear inequality
    pub coeffs  : Vec<i64>,
    /// Bounds for every variable
    pub bounds  : Vec<(i64, i64)>,
    /// `d` in a linear inequality $ ax+by+cz+d >= 0 $
    pub bias    : i64,
    /// Id of each index
    pub indices : Vec<u32>
}

impl Clone for GeLineq {
    fn clone(&self) -> Self {
        return GeLineq {
            id: self.id,
            coeffs: self.coeffs.to_vec(),
            bounds: self.bounds.to_vec(),
            bias: self.bias,
            indices: self.indices.to_vec(),
        }
    }
}

impl GeLineq {
    
    fn _eqmax(&self) -> i64 {
        let mut res : i64 = 0;
        for i in 0..self.coeffs.len() {
            if self.coeffs[i] < 0 {
                res = res + self.coeffs[i] * self.bounds[i].0;
            } else {
                res = res + self.coeffs[i] * self.bounds[i].1;
            }
        }
        return res;
    }
    
    fn _eqmin(&self) -> i64 {
        let mut res : i64 = 0;
        for i in 0..self.coeffs.len() {
            if self.coeffs[i] > 0 {
                res = res + self.coeffs[i] * self.bounds[i].0;
            } else {
                res = res + self.coeffs[i] * self.bounds[i].1;
            }
        }
        return res;
    }
    
    /// Takes two GeLineqs and merge those into one GeLineq under the condition that one of the GeLineqs must be satisfied.
    /// If it's not possible to merge the inequalities, i.e. it's impossible to preserve the logic, `none` is returned.
    /// 
    /// # Example:
    /// 
    /// If atleast one of the two linear inequalities $ x + y - 1 \ge 0 $ where $ x, y \in \\{0, 1 \\}$ and $ a + b - 1 \ge 0 $ where $ a, b \in \\{0, 1\\}$ must hold,
    /// then they can be merged into one linear inequality as $ x + y + a + b - 1 \ge 0$ where $ x, y, a, b \in \\{0, 1\\}$. Note that the logic is preserved,
    /// i.e the merged inequality will be valid if at least one of the two original inequalities are valid. Likewise, the merged constraint will not be valid if none of the original inequalites are.
    /// ```
    /// use puanrs::polyopt::GeLineq;
    /// let ge_lineq1:GeLineq = GeLineq {
    ///    id      : None,
    ///    coeffs  : vec![1, 1],
    ///    bounds  : vec![(0, 1), (0, 1)],
    ///    bias    : -1,
    ///    indices : vec![1, 2]
    ///    };
    /// let ge_lineq2: GeLineq = GeLineq {
    ///    id      : None,
    ///    coeffs  : vec![1, 1],
    ///    bounds  : vec![(0, 1), (0, 1)],
    ///    bias    : -1,
    ///    indices : vec![3, 4]
    ///  };
    /// let expected: GeLineq = GeLineq {
    ///    id      : None,
    ///    coeffs  : vec![1, 1, 1, 1],
    ///    bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
    ///    bias    : -1,
    ///    indices : vec![1, 2, 3, 4]
    ///  };
    /// let actual = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
    /// assert_eq!(actual.as_ref().expect("Not possible to merge lineqs").coeffs, expected.coeffs);
    /// assert_eq!(actual.as_ref().expect("Not possible to merge lineqs").bounds, expected.bounds);
    /// assert_eq!(actual.as_ref().expect("Not possible to merge lineqs").bias, expected.bias);
    /// assert_eq!(actual.as_ref().expect("Not possible to merge lineqs").indices, expected.indices);
    /// ```
    pub fn merge_disj(ge_lineq1: &GeLineq, ge_lineq2: &GeLineq) -> Option<GeLineq> {
        if ge_lineq1._eqmin() + ge_lineq1.bias == -1 {
            let mut equal_indices : Vec<(usize, usize)> = Vec::new();
            for i in 0..ge_lineq1.indices.len(){
                for j in 0..ge_lineq2.indices.len(){
                    if ge_lineq1.indices[i]==ge_lineq2.indices[j] {
                        equal_indices.push((i, j));
                    }
                }
            }
            let n: usize = ge_lineq1.coeffs.len() + ge_lineq2.coeffs.len() - equal_indices.len();
            let mut new_coeffs : Vec<i64> = Vec::with_capacity(n);
            let mut equal_index_pointer: usize = 0;
            let mut corrector: i64 = 0;
            let mut new_bounds : Vec<(i64, i64)> = Vec::with_capacity(n);
            let mut new_indices : Vec<u32> = Vec::with_capacity(n);
            
            for i in 0..ge_lineq1.coeffs.len() {
                if equal_index_pointer < equal_indices.len() && equal_indices[equal_index_pointer].0 == i {
                    corrector = ge_lineq2.coeffs[equal_indices[equal_index_pointer].1];
                    equal_index_pointer = equal_index_pointer + 1;
                }
                new_coeffs.push(-ge_lineq1.coeffs[i]*(ge_lineq2._eqmin() + ge_lineq2.bias) + corrector);
                new_indices.push(ge_lineq1.indices[i]);
                new_bounds.push(ge_lineq1.bounds[i]);
                corrector = 0;
            }
            let mut skip_equal_index = false;
            for i in 0..ge_lineq2.coeffs.len(){
                for j in 0..equal_indices.len(){
                    if equal_indices[j].1 == i {
                        equal_indices.remove(j);
                        skip_equal_index = true;
                        break;
                    }
                }
                if !skip_equal_index {
                    new_coeffs.push(ge_lineq2.coeffs[i]);
                    new_indices.push(ge_lineq2.indices[i]);
                    new_bounds.push(ge_lineq2.bounds[i]);
                }
                skip_equal_index = false;
            }
            return Some(
                GeLineq {
                    id: None,
                    coeffs: new_coeffs,
                    bounds: new_bounds,
                    bias: ge_lineq1._eqmin()*(ge_lineq2._eqmin() + ge_lineq2.bias)+ge_lineq2.bias,
                    indices: new_indices
                }
            );  
        } else if ge_lineq2._eqmin() + ge_lineq2.bias == -1 {
            return GeLineq::merge_disj(ge_lineq2, ge_lineq1);
        }
    
        None
        
    }

    /// Takes two GeLineqs and merge those into one GeLineq under the condition that both of the GeLineqs must be valid.
    /// If it's not possible to merge the inequalities, i.e. it's impossible to preserve the logic, `none` is returned.
    pub fn merge_conj(ge_lineq1: &GeLineq, ge_lineq2: &GeLineq) -> Option<GeLineq> {
    
        if ge_lineq1._eqmax() + ge_lineq1.bias == 0 {
            let mut equal_indices : Vec<(usize, usize)> = Vec::new();
            for i in 0..ge_lineq1.indices.len(){
                for j in 0..ge_lineq2.indices.len(){
                    if ge_lineq1.indices[i]==ge_lineq2.indices[j] {
                        equal_indices.push((i, j));
                    }
                }
            }
            let n: usize = ge_lineq1.coeffs.len() + ge_lineq2.coeffs.len() - equal_indices.len();
            let mut new_coeffs : Vec<i64> = Vec::with_capacity(n);
            let mut equal_index_pointer: usize = 0;
            let mut corrector: i64 = 0;
            let mut new_bounds : Vec<(i64, i64)> = Vec::with_capacity(n);
            let mut new_indices : Vec<u32> = Vec::with_capacity(n);
            
            for i in 0..ge_lineq1.coeffs.len() {
                if equal_index_pointer < equal_indices.len() && equal_indices[equal_index_pointer].0 == i {
                    corrector = ge_lineq2.coeffs[equal_indices[equal_index_pointer].1];
                    equal_index_pointer = equal_index_pointer + 1;
                }
                new_coeffs.push(ge_lineq1.coeffs[i]*(cmp::max(ge_lineq2._eqmax().abs(), ge_lineq2._eqmin().abs())+1) + corrector);
                new_indices.push(ge_lineq1.indices[i]);
                new_bounds.push(ge_lineq1.bounds[i]);
                corrector = 0;
            }
            let mut skip_equal_index = false;
            for i in 0..ge_lineq2.coeffs.len(){
                for j in 0..equal_indices.len(){
                    if equal_indices[j].1 == i {
                        equal_indices.remove(j);
                        skip_equal_index = true;
                        break;
                    }
                }
                if !skip_equal_index {
                    new_coeffs.push(ge_lineq2.coeffs[i]);
                    new_indices.push(ge_lineq2.indices[i]);
                    new_bounds.push(ge_lineq2.bounds[i]);
                }
                skip_equal_index = false;
            }
            return Some(
                GeLineq {
                    id: None,
                    coeffs: new_coeffs,
                    bounds: new_bounds,
                    bias: ge_lineq1.bias*(cmp::max(ge_lineq2._eqmax().abs(), ge_lineq2._eqmin().abs())+1) + ge_lineq2.bias - cmp::max(ge_lineq2._eqmin() + ge_lineq2.bias, 0),
                    indices: new_indices
                }
            );  
        } else if ge_lineq2._eqmax() + ge_lineq2.bias == 0 {
            return GeLineq::merge_conj(&ge_lineq2, &ge_lineq1);
        }
    
        None
        
    }
    
    /// Takes a GeLineq, referred to as main GeLineq which has a variable (given by variable index) which in turn is a GeLineq, referred to as the sub GeLineq.
    /// The function substitutes the variable with the sub GeLineq into the main GeLineq if possible. 
    /// 
    /// # Example
    /// Given the lineq x + Y - 2 >= 0 where Y: a + b - 1 >= 0
    /// a substitution would give 2x + a + b - 3 >= 0. Lets see it in code:
    /// ```
    /// use puanrs::polyopt::GeLineq;
    /// let main_gelineq:GeLineq = GeLineq {
    ///    id      : None,
    ///    coeffs  : vec![1, 1],
    ///    bounds  : vec![(0, 1), (0, 1)],
    ///    bias    : -2,
    ///    indices : vec![1, 2]
    /// };
    /// let sub_gelineq: GeLineq = GeLineq {
    ///    id      : None,
    ///    coeffs  : vec![1, 1],
    ///    bounds  : vec![(0, 1), (0, 1)],
    ///    bias    : -1,
    ///    indices : vec![3, 4]
    /// };
    /// let result = GeLineq::substitution(&main_gelineq, 2, &sub_gelineq);
    /// assert_eq!(vec![2, 1, 1], result.as_ref().expect("No result generated").coeffs);
    /// assert_eq!(vec![(0,1), (0,1), (0,1)], result.as_ref().expect("No result generated").bounds);
    /// assert_eq!(-3, result.as_ref().expect("No result generated").bias);
    /// assert_eq!(vec![1, 3, 4], result.as_ref().expect("No result generated").indices);
    /// ```

    pub fn substitution(main_gelineq: &GeLineq, variable_index: u32, sub_gelineq: &GeLineq) -> Option<GeLineq> {
        let var_to_substitute = main_gelineq.indices.iter().position(|&x| x == variable_index).expect(&format!("Variable '{variable_index}' to substitute not found"));
        if main_gelineq.coeffs[var_to_substitute] < 0 {
            let new_sub_coeffs: Vec<i64> = sub_gelineq.coeffs.iter().map(|x| -1*x).collect();
            let new_sub_bias = -sub_gelineq.bias - 1;
            let new_sub_gelineq = GeLineq {
                id: None,
                coeffs: new_sub_coeffs,
                bounds: sub_gelineq.bounds.to_vec(),
                bias: new_sub_bias,
                indices: sub_gelineq.indices.to_vec()
            };
            return GeLineq::_substitution(main_gelineq, var_to_substitute, &new_sub_gelineq);
        }
        return GeLineq::_substitution(main_gelineq, var_to_substitute, sub_gelineq);
    }
    
    fn _substitution(main_gelineq: &GeLineq, variable_index: usize, sub_gelineq: &GeLineq) -> Option<GeLineq> {
        if !GeLineq::is_homogenous(main_gelineq) && sub_gelineq.coeffs.len() > 1 {
            // Not possible to perform substitution
            return None;
        }
        if sub_gelineq.bias < 0 {
            if sub_gelineq._eqmax() > 0 && (main_gelineq.coeffs[variable_index]*(2*sub_gelineq._eqmax() + sub_gelineq.bias)/sub_gelineq._eqmax()) >= 2 {
                // Not possible to perform substitution
                return None;
            }
        } else {
            if (main_gelineq.coeffs[variable_index]*(sub_gelineq._eqmax() + sub_gelineq._eqmin().abs() + sub_gelineq.bias) / sub_gelineq._eqmin().abs()) >= 2 {
                // Not possible to perform substitution
                return None;
            }
        }
        let mut equal_indices : Vec<(usize, usize)> = Vec::new();
        for i in 0..main_gelineq.indices.len(){
            for j in 0..sub_gelineq.indices.len(){
                if main_gelineq.indices[i]==sub_gelineq.indices[j] {
                    equal_indices.push((i, j));
                }
            }
        }
        let n: usize = main_gelineq.coeffs.len() + sub_gelineq.coeffs.len() - equal_indices.len() - 1;
        let mut new_coeffs : Vec<i64> = Vec::with_capacity(n);
        let mut equal_index_pointer: usize = 0;
        let mut corrector: i64 = 0;
        let mut new_bounds : Vec<(i64, i64)> = Vec::with_capacity(n);
        let mut new_indices : Vec<u32> = Vec::with_capacity(n);
        
        for i in 0..main_gelineq.coeffs.len() {
            if i == variable_index {
                continue;
            }
            if equal_index_pointer < equal_indices.len() && equal_indices[equal_index_pointer].0 == i {
                corrector = sub_gelineq.coeffs[equal_indices[equal_index_pointer].1];
                equal_index_pointer = equal_index_pointer + 1;
            }
            if sub_gelineq.bias < 0 {
                new_coeffs.push(main_gelineq.coeffs[i]*sub_gelineq._eqmax() + corrector);
            } else {
                new_coeffs.push(main_gelineq.coeffs[i]*sub_gelineq._eqmin().abs() + corrector);
            }
            new_indices.push(main_gelineq.indices[i]);
            new_bounds.push(main_gelineq.bounds[i]);
            corrector = 0;
        }
        let mut skip_equal_index = 0;
        for i in 0..sub_gelineq.coeffs.len(){
            for j in 0..equal_indices.len(){
                if equal_indices[j].1 == i {
                    equal_indices.remove(j);
                    skip_equal_index = 1;
                    break;
                }
            }
            if skip_equal_index < 1 {
                new_coeffs.push(sub_gelineq.coeffs[i]);
                new_indices.push(sub_gelineq.indices[i]);
                new_bounds.push(sub_gelineq.bounds[i]);
            }
            skip_equal_index = 0;
        }
        let adjuster = if main_gelineq.bias != 0 {1} else {0};
        let new_bias = if sub_gelineq.bias < 0 {(main_gelineq.bias + adjuster)*sub_gelineq._eqmax() + sub_gelineq.bias} else {(main_gelineq.bias+adjuster)*sub_gelineq._eqmin().abs() + sub_gelineq.bias};
        return Some(
            GeLineq {
                id: main_gelineq.id,
                coeffs: new_coeffs,
                bounds: new_bounds,
                bias: new_bias,
                indices: new_indices
            }
        );  
    }

    fn is_homogenous(ge_lineq: &GeLineq) -> bool {
        let first = ge_lineq.coeffs[0];
        ge_lineq.coeffs.iter().all(|x| *x==first)
    }
    
    fn is_mixed(gelineq: &GeLineq) -> bool {
        let mut is_mixed = false;
        let mut positive = false;
        let mut negative = false;
        let mut i: usize = 0;
        while !is_mixed && i < gelineq.coeffs.len() {
            if gelineq.coeffs[i]*gelineq.bounds[i].0 > 0 || gelineq.coeffs[i]*gelineq.bounds[i].1 > 0 {
                positive = true;
            }
            if gelineq.coeffs[i]*gelineq.bounds[i].0 < 0 || gelineq.coeffs[i]*gelineq.bounds[i].1 < 0 {
                negative = true
            }
            if positive && negative {
                is_mixed = true;
            }
            i = i + 1;
        }
        return is_mixed;
    }
    
    /// Takes a GeLineq and minimizes/maximizes the coefficients while preserving the logic
    /// 
    /// # Example
    /// 
    /// Consider the GeLineq 2x + y + z >= 1 where x, y, z takes values between 0 and 1.
    /// This inequlity can be written as x + y + z >= 1 while preserving the logic. 
    /// ```
    /// use puanrs::polyopt::GeLineq;
    /// let gelineq: GeLineq = GeLineq {
    ///     id      : None,
    ///     coeffs  : vec![2, 1, 1],
    ///     bounds  : vec![(0,1), (0,1), (0,1)],
    ///     bias    : -1,
    ///     indices : vec![0, 1, 2]
    ///   };
    /// let result = GeLineq::min_max_coefficients(&gelineq);
    /// assert_eq!(vec![1, 1, 1], result.as_ref().expect("").coeffs);
    pub fn min_max_coefficients(gelineq: &GeLineq) -> Option<GeLineq> {
        if GeLineq::is_mixed(gelineq){
            return None;
        }
        let mut new_coeffs: Vec<i64> = Vec::with_capacity(gelineq.coeffs.len());
        for i in 0..gelineq.coeffs.len(){
            if gelineq.coeffs[i]*gelineq.bounds[i].0 > 0 || gelineq.coeffs[i]*gelineq.bounds[i].1 > 0 {
                new_coeffs.push(cmp::min(gelineq.coeffs[i], cmp::max(-gelineq.bias, 0)));
            } else if gelineq.coeffs[i]*gelineq.bounds[i].0 < 0 || gelineq.coeffs[i]*gelineq.bounds[i].1 < 0 {
                new_coeffs.push(cmp::max(gelineq.coeffs[i], cmp::min(-gelineq.bias, 0)-1));
            } else {
                new_coeffs.push(0);
            }
        }
        return Some(
                GeLineq {
                    id: gelineq.id,
                    coeffs: new_coeffs,
                    bounds: gelineq.bounds.to_vec(),
                    bias: gelineq.bias, 
                    indices: gelineq.indices.to_vec() 
                }
            )
        }
        
        
    }


#[derive(Debug)]
pub struct VariableFloat {
    pub id      : u32,
    pub bounds  : (f64, f64)
}

impl Clone for VariableFloat {
    fn clone(&self) -> Self {
        return VariableFloat { 
            id: self.id, 
            bounds: self.bounds 
        }
    }
}

impl PartialEq for VariableFloat {
    fn eq(&self, other: &Self) -> bool {
        return self.id == other.id;
    }
}


/// Variable data structure has two properties, "id" and "bounds". An instance of Variable
/// is used to reference to Statement or an input into a Theory. 
#[derive(Copy, Eq, Debug)]
pub struct Variable {
    pub id      : u32,
    pub bounds  : (i64, i64)
}

impl Clone for Variable {
    fn clone(&self) -> Self {
        return Variable {
            id : self.id,
            bounds: self.bounds
        }
    }
}

impl PartialEq for Variable {
    fn eq(&self, other: &Self) -> bool {
        return self.id == other.id;
    }
}

impl Variable {

    /// A negated linear inequality representation of a Variable.
    /// 
    /// # Example:
    /// 
    /// ```
    /// use puanrs::polyopt::Variable;
    /// use puanrs::polyopt::GeLineq;
    /// let variable: Variable = Variable {
    ///     id      : 0,
    ///     bounds  : (0,1)
    /// };
    /// let actual: GeLineq = variable.to_lineq_neg();
    /// assert_eq!(actual.bias, 0);
    /// assert_eq!(actual.bounds, vec![(0,1)]);
    /// assert_eq!(actual.coeffs, vec![-1]);
    /// assert_eq!(actual.indices, vec![0]);
    /// ```
    pub fn to_lineq_neg(&self) -> GeLineq {
        return GeLineq {
            id: Some(self.id),
            coeffs: vec![-1],
            bias: 0,
            bounds: vec![(0,1)],
            indices: vec![self.id]
        }
    }

    pub fn to_variable_float(&self) -> VariableFloat {
        return VariableFloat { id: self.id, bounds: (self.bounds.0 as f64, self.bounds.1 as f64) }
    }
}

/// Data structure for polyhedron with `a` as `Matrix` and `b` as `Vec` and `bounds` as a `Vec` of `Tuples`.
/// Note that the number of rows of `a` must be the same as the length of `b` and the number of columns of `a`
/// must be the same as the length of `bounds`.
#[derive(Default, Debug)]
pub struct Polyhedron {
    /// The left-hand side of linear constraints on the form $ a + b + c \ge x $.
    pub a: Matrix,
    /// The right-hand side of linear constraints as described above.
    pub b: Vec<f64>,
    /// Upper and lower bounds (`lower_bound`, `upper_bound`) of the variables given by `a`.
    pub variables: Vec<VariableFloat>,
    // Index of rows in `a`.
    pub index: Vec<Option<u32>>
}
impl Clone for Polyhedron {
    fn clone(&self) -> Self {
        return Polyhedron { a: self.a.clone(), b: self.b.clone(), variables: self.variables.clone(), index: self.index.clone() }
    }
}
impl PartialEq for Polyhedron {
    fn eq(&self, other: &Self) -> bool {
        return (self.a == other.a) & (self.b == other.b) & (self.variables == other.variables) & (self.index == other.index);
    }
}
impl Polyhedron {
    /// Returns a Vec of all variable bounds generated from variables vector.
    pub fn bounds(&self) -> Vec<(f64, f64)> {
        return self.variables.iter().map(|x| x.bounds).collect();
    }

    /// Returns a Vec of all variable ID's generated from variables vector.
    pub fn ids(&self) -> Vec<u32> {
        return self.variables.iter().map(|x| x.id).collect();
    }
}

pub struct CsrPolyhedron {
    /// The left-hand side of linear constraints on the form $ a + b + c \ge x $ as a compressed sparse matrix.
    pub a: CsrMatrix,
    /// The right-hand side of linear constraints as described above.
    pub b: Vec<f64>,
    /// Upper and lower bounds (`lower_bound`, `upper_bound`) of the variables given by `a`.
    pub variables: Vec<VariableFloat>,
    // Index of rows in `a`.
    pub index: Vec<Option<u32>>
} 

impl Clone for CsrPolyhedron {
    fn clone(&self) -> Self {
        return CsrPolyhedron { a: self.a.clone(), b: self.b.clone(), variables: self.variables.clone(), index: self.index.clone() }
    }
}
impl PartialEq for CsrPolyhedron {
    fn eq(&self, other: &Self) -> bool {
        return (self.a == other.a) & (self.b == other.b) & (self.variables == other.variables) & (self.index == other.index);
    }
}
impl CsrPolyhedron {
    /// Returns a Vec of all variable bounds generated from variables vector.
    pub fn bounds(&self) -> Vec<(f64, f64)> {
        return self.variables.iter().map(|x| x.bounds).collect();
    }

    /// Returns a Vec of all variable ID's generated from variables vector.
    pub fn ids(&self) -> Vec<u32> {
        return self.variables.iter().map(|x| x.id).collect();
    }

    pub fn to_dense_polyhedron(&self) -> Polyhedron {
        return Polyhedron {
            a: self.a.to_matrix(),
            b: self.b.clone(),
            index: self.index.clone(),
            variables: self.variables.clone()
        }
    }
}