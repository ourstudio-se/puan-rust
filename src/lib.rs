//! # Puan rust
//! 
//! Puan algorithms implemented in Rust. 

use std::hash::Hash;
use std::{collections::HashMap};
use std::fmt::Display;
use itertools::iproduct;
use std::cmp;

pub mod solver;
pub mod linalg;

/// Data structure for linear inequalities on the following form
/// $$ c_0 * v_0 + c_1 * v_1 + ... + c_n * v_n + bias \ge 0 $$ for $ c \in $ `coeffs` and $ v $ are variables which can take on the values
/// given by `bounds`. `Indices` represents the global indices of the variables. Note that the length of `coeffs`, `bounds` and `indices` must be the same.
#[derive(Hash)]
pub struct GeLineq {
    pub coeffs  : Vec<i64>,
    pub bounds  : Vec<(i64, i64)>,
    pub bias    : i64,
    pub indices : Vec<u32>
}

impl Clone for GeLineq {
    fn clone(&self) -> Self {
        return GeLineq {
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
    
    fn eqbounds(&self) -> (i64, i64) {
        return (self._eqmin(), self._eqmax());
    }
    
    fn satisfied(&self, variables: Vec<(u32, i64)>) -> bool{
        let mut res = 0;
        for i in 0..variables.len() {
            for j in 0..self.coeffs.len() {
                if self.indices[j] == variables[i].0 {
                    res = res + self.coeffs[j]*variables[i].1;
                }
            }
        }
        return res + self.bias >= 0;
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
    /// use puanrs::GeLineq;
    /// let ge_lineq1:GeLineq = GeLineq {
    ///    coeffs  : vec![1, 1],
    ///    bounds  : vec![(0, 1), (0, 1)],
    ///    bias    : -1,
    ///    indices : vec![1, 2]
    ///    };
    /// let ge_lineq2: GeLineq = GeLineq {
    ///    coeffs  : vec![1, 1],
    ///    bounds  : vec![(0, 1), (0, 1)],
    ///    bias    : -1,
    ///    indices : vec![3, 4]
    ///  };
    /// let expected: GeLineq = GeLineq {
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
    /// use puanrs::GeLineq;
    /// let main_gelineq:GeLineq = GeLineq {
    ///    coeffs  : vec![1, 1],
    ///    bounds  : vec![(0, 1), (0, 1)],
    ///    bias    : -2,
    ///    indices : vec![1, 2]
    /// };
    /// let sub_gelineq: GeLineq = GeLineq {
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
    /// use puanrs::GeLineq;
    /// let gelineq: GeLineq = GeLineq {
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
        return Some(GeLineq {
            coeffs: new_coeffs,
            bounds: gelineq.bounds.to_vec(),
            bias: gelineq.bias, 
            indices: gelineq.indices.to_vec() })
        }
        
        
    }
fn select_check(pairs: Vec<[u32;2]>) -> Vec<[u32;2]> {
    let mut candidates: Vec<[u32;2]> = pairs.to_vec();
    let mut solution: Vec<[u32;2]> = Vec::new();

    while candidates.len() > 0 {
        let selected: [u32;2] = candidates.pop().expect("empty candidates in select_check function");
        candidates = candidates.iter().filter(
            |candidate| {
                iproduct!(selected.iter(), candidate.iter()).map(
                    |comb| {
                        *comb.0!=*comb.1
                    }
                ).all(|x: bool| x)
            }
        ).map(|x| *x).collect();
        solution.push(selected);
    }

    return solution;
}

/// Variable data structure has two properties, "id" and "bounds". An instance of Variable
/// is used to reference to Statement or an input into a Theory. 
#[derive(Copy, Hash, Eq)]
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
    /// use puanrs::Variable;
    /// use puanrs::GeLineq;
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
            coeffs: vec![-1],
            bias: 0,
            bounds: vec![(0,1)],
            indices: vec![self.id]
        }
    }
}

/// Data structure for representing an `at least` constraint on form 
/// $$ c * v_0 + c * v_1 + ... + c * v_n + bias \ge 0 $$
/// where $c \in [-1,1]$ depending on positive or negative bias.
/// `ids` vector property holds what variables are connected to this constraint.
pub struct AtLeast {
    pub ids     : Vec<u32>,
    pub bias   : i64,
}

impl Clone for AtLeast {
    fn clone(&self) -> Self {
        return AtLeast {
            bias: self.bias,
            ids: self.ids.to_vec(),
        }
    }
}

impl AtLeast {

    fn size(&self) -> usize {
        return self.ids.len();
    }

    /// Transform into a linear inequality constraint.
    /// `variable_bounds` are the lower and upper bound for each variable
    /// in `ids`.
    /// 
    /// # Example:
    /// 
    /// ```
    /// use puanrs::AtLeast;
    /// use puanrs::GeLineq;
    /// use puanrs::Variable;
    /// use std::{collections::HashMap};
    /// let at_least: AtLeast = AtLeast {
    ///     ids     : vec![0,1,2],
    ///     bias   : -1,
    /// };
    /// let mut variable_hm: HashMap<u32, Variable> = HashMap::default();
    /// variable_hm.insert(0, Variable {id: 0, bounds: (0,1)});
    /// variable_hm.insert(1, Variable {id: 1, bounds: (0,1)});
    /// variable_hm.insert(2, Variable {id: 2, bounds: (0,1)});
    /// let actual: GeLineq = at_least.to_lineq(&variable_hm);
    /// assert_eq!(actual.coeffs, vec![1,1,1]);
    /// assert_eq!(actual.bias, -1);
    /// assert_eq!(actual.bounds, vec![(0,1),(0,1),(0,1)]);
    /// assert_eq!(actual.indices, vec![0,1,2]);
    /// ```
    pub fn to_lineq(&self, variable_hm: &HashMap<u32, Variable>) -> GeLineq {
        return GeLineq {
            coeffs: vec![match self.bias >= 0 {true => -1, false => 1}; self.size()],
            bias: self.bias,
            bounds: self.ids.iter().map(
                |id| {
                    variable_hm.get(id).expect(
                        &format!(
                            "got id `{id}` in expression {self} that was not in theory"
                        )
                    ).bounds
                }
            ).collect(),
            indices: self.ids.to_vec()
        }
    }

    fn to_lineq_expressed(&self, extended: bool, variable: Variable, variable_hm: &HashMap<u32, Variable>) -> GeLineq {
        if extended {
            return GeLineq::merge_disj(
                &variable.to_lineq_neg(),
                &self.to_lineq(variable_hm)
            ).expect("could not merge disjunctions") // <- should always be able to merge here
        } else {
            return self.to_lineq(variable_hm);
        }
    }

    fn to_lineq_reduced(&self, extended: bool, variable: Variable, variable_hm: &HashMap<u32, Variable>, statement_hm: &HashMap<u32, &Statement>) -> GeLineq {
        return match (self.bias, self.ids.len()) {
            (-1, 2) => {
                let sub_lineqs: Vec<GeLineq> = self.ids.iter().filter_map(|id| {
                    if let Some(statement) = statement_hm.get(id) {
                        if let Some(expression) = statement.expression.clone() {
                            return Some(expression.to_lineq(variable_hm));
                        }
                    }
                    return None;
                }).collect();
                if sub_lineqs.len() == 2 {
                    if let Some(lineq) = GeLineq::merge_disj(&sub_lineqs[0], &sub_lineqs[1]) {
                        return lineq;
                    } else {
                        return self.to_lineq_expressed(extended, variable, variable_hm);
                    }
                } else {
                    return self.to_lineq_expressed(extended, variable, variable_hm);
                }
            },
            (-2, 2) => {
                let sub_lineqs: Vec<GeLineq> = self.ids.iter().filter_map(|id| {
                    if let Some(statement) = statement_hm.get(id) {
                        if let Some(expression) = statement.expression.clone() {
                            return Some(expression.to_lineq(variable_hm));
                        }
                    }
                    return None;
                }).collect();
                if sub_lineqs.len() == 2 {
                    if let Some(lineq) = GeLineq::merge_conj(&sub_lineqs[0], &sub_lineqs[1]) {
                        return lineq;
                    } else {
                        return self.to_lineq_expressed(extended, variable, variable_hm)
                    }
                } else {
                    return self.to_lineq_expressed(extended, variable, variable_hm);
                }
            },
            _ => self.to_lineq_expressed(extended, variable, variable_hm)
        }
    }
}

impl Display for AtLeast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})({}>={})", match self.bias < 0 {true => "+", false => "-"}, self.ids.iter().map(|v| v.to_string()).collect::<Vec<String>>().join(","), self.bias)
    }
}

/// A `Statement` is a declaration of a expression (or proposition) connected to a `Variable`.
/// For instance, "A is true iff x > 3, else false" is a statement. Currently only `AtLeast` is
/// considered to be an `Expression`.
pub struct Statement {
    pub variable    : Variable,
    pub expression  : Option<AtLeast>
}

/// A `Theory` is a list of statements with a common name (id).
pub struct Theory {
    pub id : String,
    pub statements : Vec<Statement>
}

impl Theory {

    // top node/id, i.e the id which no one has as a child
    fn _top(&self) -> &u32 {
        let mut is_child : bool = true;
        let mut id_curr : &u32 = &self.statements.first().expect("theory is empty").variable.id;
        let mut counter = 0;
        while is_child {
            if counter >= self.statements.len() {
                panic!("theory has circular statement references! (a -> b -> c -> a)")
            }
            for statement in self.statements.iter() {
                is_child = match &statement.expression {
                    Some(a) => a.ids.contains(id_curr),
                    None => false
                };
                if is_child {
                    id_curr = &statement.variable.id;
                    break;
                }
            }
            counter += 1;
        }
        return id_curr;
    }

    // All bottom / atomic variable ids. E.i. statements that don't have any children.
    fn _bottoms(&self) -> Vec<&u32> {
        return self.statements.iter().filter_map(
            |statement| {
                match &statement.expression {
                    Some(_) => None,
                    None => Some(&statement.variable.id)
                }
            }
        ).collect()
    }

    // Variable hash map from variable id to variable
    fn _variable_hm(&self) -> HashMap<u32, Variable> {
        return self.statements.iter().map(|statement: &Statement| {
            (statement.variable.id, statement.variable)
        }).collect();
    }

    // Statement hash map from variable id to statement
    fn _statement_hm(&self) -> HashMap<u32, &Statement> {
        return self.statements.iter().map(|statement: &Statement| {
            (statement.variable.id, statement)
        }).collect();
    }

    /// Transforms all Statements in Theory into GeLineq's such that 
    /// if all GeLineq's are true <-> Theory is true.
    ///
    /// # Example:
    /// 
    /// ```
    /// use puanrs::Theory;
    /// use puanrs::Statement;
    /// use puanrs::AtLeast;
    /// use puanrs::Variable;
    /// use puanrs::GeLineq;
    /// let theory: Theory = Theory {
    ///     id          : String::from("A"),
    ///     statements  : vec![
    ///         Statement {
    ///             variable    : Variable {
    ///                 id      : 0,
    ///                 bounds  : (0,1),
    ///             },
    ///             expression  : Some(
    ///                 AtLeast {
    ///                     ids     : vec![1,2],
    ///                     bias   : -1,
    ///                 }
    ///             )
    ///         },
    ///         Statement {
    ///             variable    : Variable {
    ///                 id      : 1,
    ///                 bounds  : (0,1),
    ///             },
    ///             expression  : None
    ///         },
    ///         Statement {
    ///             variable    : Variable {
    ///                 id      : 2,
    ///                 bounds  : (0,1),
    ///             },
    ///             expression  : None
    ///         },
    ///     ]
    /// };
    /// let actual: Vec<GeLineq> = theory.to_lineqs(false, false);
    /// assert_eq!(actual.len(), 1);
    /// assert_eq!(actual[0].bias, 0);
    /// assert_eq!(actual[0].coeffs, vec![-1,1,1]);
    /// assert_eq!(actual[0].indices, vec![0,1,2]);
    /// ```
    pub fn to_lineqs(&self, active: bool, reduced: bool) -> Vec<GeLineq> {
        let top_node_id = *self._top();
        let var_hm: HashMap<u32, Variable> = self._variable_hm();
        let state_hm: HashMap<u32, &Statement> = self._statement_hm();
        let mut lineqs: Vec<GeLineq> = Vec::default();
        let mut queue: Vec<u32> = vec![top_node_id];

        while let Some(id) = queue.pop() {
            if let Some(statement) = state_hm.get(&id) {
                let pot_lineq = match &statement.expression {
                    Some(a) => match reduced {
                        true => Some(
                            a.to_lineq_reduced(
                                !((top_node_id == statement.variable.id) & active), 
                                statement.variable,
                                &var_hm,
                                &state_hm,
                            )
                        ),
                        false => Some(a.to_lineq_expressed(!((top_node_id == statement.variable.id) & active), statement.variable, &var_hm))
                    },
                    None => None
                };

                if let Some(act_lineq) = pot_lineq {
                    queue.append(&mut act_lineq.indices.clone().into_iter().filter(|i| (*i) != statement.variable.id).collect());
                    lineqs.push(act_lineq);
                }
            }
        }
        return lineqs;
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use super::*;

    #[test]
    fn test_theory_to_lineqs_reduced() {

        fn lineqs_eq(actual: Vec<GeLineq>, expected: Vec<GeLineq>) -> bool {
            return actual.iter().zip(expected.iter()).all(|ae| {
                let bias_ok = ae.0.bias == ae.1.bias;
                let bounds_ok = ae.0.bounds == ae.1.bounds;
                let indices_ok = ae.0.indices == ae.1.indices;
                let coeffs_ok = ae.0.coeffs == ae.1.coeffs;
                return bias_ok && bounds_ok && indices_ok && coeffs_ok;
            });
        }

        // Depth 3
        // 0: 1 & 2
        // 1: 3 + 4 >= 6 (3 has bounds (-5,5), 4 is bool) 
        // 2: 5 + 6 >= 5 (5 has bounds (-3,3), 6 is bool) 

        // Expected constraints:
        // 4( x) +( y) -41
        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -2
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: -6
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6],
                            bias: -4
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 3, bounds: (-5,5) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 4, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 5, bounds: (-3,3) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 6, bounds: (0,1) },
                    expression: None
                },
            ]
        };
        let actual: Vec<GeLineq> = t.to_lineqs(true, true);
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                bias: -34,
                bounds: vec![(-5,5),(0,1),(-3,3),(0,1)],
                coeffs: vec![5,5,1,1],
                indices: vec![3,4,5,6]
            },
        ];
        assert!(lineqs_eq(actual, expected));

        // Depth 4
        // 0: 1 & 2 & 3
        // 1: 4 | 5
        // 2: 5 | 6
        // 3: 7 & 8
        // 4: 9 & 10
        // 5: -11
        // 6: 12 | 13

        // We test two things:
        // 1) sharing variable works (both 1 and 2 has 5 as child and is reducable)
        // 2) direct reducement works (0 and 3 has same constraint, therefore 0 should have 7 and 8 directly as children)  <- NOT IMPLEMENTED

        // Expected constraints:
        //   ( 1) +( 2) +( 3) -3
        // -2( 3) +( 7) +( 8) +0
        // -1(11) +(12) +(13) +0 (instead of 5 & 6)
        //   ( 9) +(10)-2(11) +0 (instead of 4 & 5)

        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2,3],
                            bias: -3
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![4,5],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 3, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![7,8],
                            bias: -2
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 4, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![9,10],
                            bias: -2
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 5, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![11],
                            bias: 0
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 6, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![12,13],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 7, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 8, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 9, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 10, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 11, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 12, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 13, bounds: (0,1) },
                    expression: None
                },
            ]
        };
        let actual: Vec<GeLineq> = t.to_lineqs(true, true);
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                bias: -3,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![1,1,1],
                indices: vec![1,2,3]
            },
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-2,1,1],
                indices: vec![3,7,8]
            },
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,1,1],
                indices: vec![11,12,13]
            },
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-2,1,1],
                indices: vec![11,9,10]
            },
        ];
        assert!(lineqs_eq(actual, expected));

        // Depth 3
        // 0: 1 -> 2
        // 1: 3 & 4
        // 2: 5 & 6 & 7
        // Expects to be reduced into 1 constraint
        // -3(3)-3(4)+(5)+(6)+(7)-3 >= 0 

        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 3, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 4, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 5, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 6, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 7, bounds: (0,1) },
                    expression: None
                },
            ]
        };
        let actual: Vec<GeLineq> = t.to_lineqs(true, true);
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                bias: 3,
                bounds: vec![(0,1),(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![-3,-3,1,1,1],
                indices: vec![3,4,5,6,7]
            },
        ];
        assert!(lineqs_eq(actual, expected));
        
        // Depth 3
        // 0: 1 & 2
        // 1: -3 | -4
        // 2: 5 & 6 & 7
        // Expects to be reduced into 1 constraint
        // -4(3)-4(4)+(5)+(6)+(7) -3 >= 0

        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -2
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 0
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 3, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 4, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 5, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 6, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 7, bounds: (0,1) },
                    expression: None
                },
            ]
        };
        let actual: Vec<GeLineq> = t.to_lineqs(true, true);
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                bias: -3,
                bounds: vec![(0,1),(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![-4,-4,1,1,1],
                indices: vec![3,4,5,6,7]
            },
        ];
        assert!(lineqs_eq(actual, expected));
        
        // Depth 4
        // 0: 1 & 2
        // 1: 3 & 4
        // 2: 5 | 6
        // 3: 7 | 8
        // 4: 9 | 10
        // 5: -11
        // 6: 12 & 13

        // Expects to be reduced into 5 constraints
        // Notice since 0 constraint has 2 subs, it gets
        // reduced before 1 and 2 could be reduced. Because
        // of that, we don't get a minimum number of constraints.
        //  3( 3) +3( 4) +( 5) +( 6) +( 7) -7
        // -2( 6) +3(12) +(13) +0
        // -1( 5) -1(11) +1
        // -1( 4) +1( 9) +(10) +0
        // -1( 3) +1( 7) +( 8) +0
        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -2
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: -2
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 3, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![7,8],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 4, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![9,10],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 5, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![11],
                            bias: 0
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 6, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![12,13],
                            bias: -2
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 7, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 8, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 9, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 10, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 11, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 12, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 13, bounds: (0,1) },
                    expression: None
                },
            ]
        };
        let actual: Vec<GeLineq> = t.to_lineqs(true, true);
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                bias: -7,
                bounds: vec![(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![3,3,1,1],
                indices: vec![3,4,5,6]
            },
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-2,1,1],
                indices: vec![6,12,13]
            },
            GeLineq {
                bias: 1,
                bounds: vec![(0,1),(0,1)],
                coeffs: vec![-1,-1],
                indices: vec![5,11]
            },
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,1,1],
                indices: vec![4,9,10]
            },
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,1,1],
                indices: vec![3,7,8]
            },
        ];
        assert!(lineqs_eq(actual, expected));
    }

    #[test]
    fn test_logic(){
        // Disjunction merge between 1-1
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 6]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l) in iproduct!(0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(6,l)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(6,l)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(6,l)]));

        }
        // Disjunction merge between 2-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![1, 2, 3, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l) in iproduct!(0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(8,l)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(8,l)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(8,l)]));

        }
        // Disjunction merge between 1-1
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m)]));

        }
        // Disjunction merge between 1-2
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 3,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 1-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 1-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 1-5
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 1-6
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 2-2
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 3,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 2-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 2-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 2-5
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 2-6
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Conjunction merge between 4-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 0, 4]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(4,l), (0,m)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(4,l), (0,m)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(4,l), (0,m)]));
            
        }
        // Conjunction merge between 4-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
            
        }
        // Conjunction merge between 1-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
            
        }
        // Conjunction merge between 2-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 2-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 3-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 3-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 3-5
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));

        }
        // Conjunction merge between 3-6
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 4-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 4-5
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 4-6
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 4-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Disjunction merge, special case
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(-2, -1), (2, 3), (2, 3)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(-2..0, 2..4, 2..4, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) || ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge, special case
        let ge_lineq1:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(-2, -1), (2, 3), (2, 3)],
            bias    : -5,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2);
        for (i,j,k,l,m, n, o) in iproduct!(-2..0, 2..4, 2..4, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && ge_lineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
    }
    #[test]
    fn test_substitution() {
        // Negative bias on sub lineq
        let main_gelineq:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq: GeLineq = GeLineq {
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -2,
            indices : vec![4,5]
        };
        let result = GeLineq::substitution(&main_gelineq, 3, &sub_gelineq);
        for (i,j,k,l) in iproduct!(0..2, 0..2, 0..2, 0..2){
            let z:i64 = sub_gelineq.satisfied(vec![(1, i), (2, j),(4,k),(5,l)]) as i64;
            assert_eq!(main_gelineq.satisfied(vec![(1, i), (2, j), (3, z), (4,k),(5,l)]), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(4,k),(5,l)]));
        }

        let main_gelineq:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq: GeLineq = GeLineq {
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -1,
            indices : vec![4,5]
        };
        let result = GeLineq::substitution(&main_gelineq, 3, &sub_gelineq);
        for (i,j,k,l) in iproduct!(0..2, 0..2, 0..2, 0..2){
            let z:i64 = sub_gelineq.satisfied(vec![(1, i), (2, j),(4,k),(5,l)]) as i64;
            assert_eq!(main_gelineq.satisfied(vec![(1, i), (2, j), (3, z), (4,k),(5,l)]), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(4,k),(5,l)]));
        }
        // Positive bias on sub lineq
        let main_gelineq:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq: GeLineq = GeLineq {
            coeffs  : vec![-1, -1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : 1,
            indices : vec![4,5]
        };
        let result = GeLineq::substitution(&main_gelineq, 3, &sub_gelineq);
        for (i,j,k,l) in iproduct!(0..2, 0..2, 0..2, 0..2){
            let z:i64 = sub_gelineq.satisfied(vec![(1, i), (2, j),(4,k),(5,l)]) as i64;
            assert_eq!(main_gelineq.satisfied(vec![(1, i), (2, j), (3, z), (4,k),(5,l)]), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(4,k),(5,l)]));
        }
        // Not possible to substitute
        let main_gelineq:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq: GeLineq = GeLineq {
            coeffs  : vec![-1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![4,5, 6]
        };
        let result = GeLineq::substitution(&main_gelineq, 3, &sub_gelineq);
        assert!(result.is_none());

        let main_gelineq:GeLineq = GeLineq {
            coeffs  : vec![-1],
            bounds  : vec![(0, 1)],
            bias    : 0,
            indices : vec![1]
        };
        let sub_gelineq: GeLineq = GeLineq {
            coeffs  : vec![1],
            bounds  : vec![(0, 10)],
            bias    : -3,
            indices : vec![2]
        };
        let result = GeLineq::substitution(&main_gelineq, 1, &sub_gelineq);
        assert_eq!(vec![-1], result.as_ref().expect("").coeffs);
        assert_eq!(vec![(0, 10)], result.as_ref().expect("").bounds);
        assert_eq!(2, result.as_ref().expect("").bias);
        for i in iproduct!(0..11){
            let x:i64 = sub_gelineq.satisfied(vec![(2, i)]) as i64;
            assert_eq!(main_gelineq.satisfied(vec![(2, i), (1, x)]), result.as_ref().expect("No result generated").satisfied(vec![(2, i), (1, x)]));
        }
        
        // Mixed signs of coeffs in sub lineq, possible to merge
        let main_gelineq:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq: GeLineq = GeLineq {
            coeffs  : vec![-1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![4,5, 6]
        };
        let result = GeLineq::substitution(&main_gelineq, 3, &sub_gelineq);
        for (i,j,k,l, m) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2){
            let z:i64 = sub_gelineq.satisfied(vec![(1, i), (2, j),(4,k),(5,l), (6,m)]) as i64;
            assert_eq!(main_gelineq.satisfied(vec![(1, i), (2, j), (3, z), (4,k),(5,l),(6,m)]), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(4,k),(5,l),(6,m)]));
        }

        let main_gelineq:GeLineq = GeLineq {
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2]
        };
        let sub_gelineq: GeLineq = GeLineq {
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -1,
            indices : vec![3, 4]
        };
        let result = GeLineq::substitution(&main_gelineq, 2, &sub_gelineq);
        for (i,j,k) in iproduct!(0..2, 0..2, 0..2){
            let z:i64 = sub_gelineq.satisfied(vec![(1, i), (3, j), (4,k)]) as i64;
            assert_eq!(main_gelineq.satisfied(vec![(1, i), (2, z), (3, j), (4,k)]), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (3, j),(4,k)]));
        }
        let main_gelineq:GeLineq = GeLineq {
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2]
        };
        let sub_gelineq: GeLineq = GeLineq {
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -1,
            indices : vec![3, 4]
        };
        let result = GeLineq::substitution(&main_gelineq, 2, &sub_gelineq);
        for (i,j,k) in iproduct!(0..2, 0..2, 0..2){
            let z:i64 = sub_gelineq.satisfied(vec![(1, i), (3, j), (4,k)]) as i64;
            assert_eq!(main_gelineq.satisfied(vec![(1, i), (2, z), (3, j), (4,k)]), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (3, j),(4,k)]));
        }
        let main_gelineq:GeLineq = GeLineq {
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq1: GeLineq = GeLineq {
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -2,
            indices : vec![4, 5]
        };
        let sub_gelineq2: GeLineq = GeLineq {
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -2,
            indices : vec![6, 7]
        };
        let result1 = GeLineq::substitution(&main_gelineq, 2, &sub_gelineq1);
        let result2 = GeLineq::substitution(&result1.as_ref().expect("No gelineq created"), 3, &sub_gelineq2);
        assert!(result2.is_none());
    }

    #[test]
    fn test_min_max_coefficients() {
        let gelineq : GeLineq = GeLineq { 
            coeffs: vec![2, 1, 1],
            bounds: vec![(0,1),(0,1),(0,1)],
            bias: -1,
            indices: vec![0, 1, 2]
        };
        let result = GeLineq::min_max_coefficients(&gelineq);
        assert_eq!(vec![1, 1, 1], result.as_ref().expect("").coeffs);
        for (i,j,k) in iproduct!(0..2, 0..2, 0..2){
            assert_eq!(gelineq.satisfied(vec![(0, i), (1, j), (2, k)]), result.as_ref().expect("No result generated").satisfied(vec![(0, i), (1, j), (2, k)]));
        }

        let gelineq : GeLineq = GeLineq { 
            coeffs: vec![2, 1, 1],
            bounds: vec![(-2,-1),(0,1),(0,1)],
            bias: 0,
            indices: vec![0, 1, 2]
        };
        let result = GeLineq::min_max_coefficients(&gelineq);
        assert!(result.is_none());

        let gelineq : GeLineq = GeLineq { 
            coeffs: vec![5, 6, 3],
            bounds: vec![(0,1),(0,1),(0,1)],
            bias: -1,
            indices: vec![0, 1, 2]
        };
        let result = GeLineq::min_max_coefficients(&gelineq);
        assert_eq!(vec![1, 1, 1], result.as_ref().expect("").coeffs);
        for (i,j,k) in iproduct!(0..2, 0..2, 0..2){
            assert_eq!(gelineq.satisfied(vec![(0, i), (1, j), (2, k)]), result.as_ref().expect("No result generated").satisfied(vec![(0, i), (1, j), (2, k)]));
        }

        let gelineq : GeLineq = GeLineq { 
            coeffs: vec![-2, -1, -1],
            bounds: vec![(0,1),(0,1),(0,1)],
            bias: 0,
            indices: vec![0, 1, 2]
        };
        let result = GeLineq::min_max_coefficients(&gelineq);
        assert_eq!(vec![-1, -1, -1], result.as_ref().expect("").coeffs);
        for (i,j,k) in iproduct!(0..2, 0..2, 0..2){
            assert_eq!(gelineq.satisfied(vec![(0, i), (1, j), (2, k)]), result.as_ref().expect("No result generated").satisfied(vec![(0, i), (1, j), (2, k)]));
        }

        let gelineq : GeLineq = GeLineq { 
            coeffs: vec![-2, -1, -1],
            bounds: vec![(0,1),(0,1),(0,1)],
            bias: 1,
            indices: vec![0, 1, 2]
        };
        let result = GeLineq::min_max_coefficients(&gelineq);
        assert_eq!(vec![-2, -1, -1], result.as_ref().expect("").coeffs);
        for (i,j,k) in iproduct!(0..2, 0..2, 0..2){
            assert_eq!(gelineq.satisfied(vec![(0, i), (1, j), (2, k)]), result.as_ref().expect("No result generated").satisfied(vec![(0, i), (1, j), (2, k)]));
        }

        let gelineq : GeLineq = GeLineq { 
            coeffs: vec![-2, 1, 1],
            bounds: vec![(0,1),(0,1),(0,1)],
            bias: 0,
            indices: vec![0, 1, 2]
        };
        let result = GeLineq::min_max_coefficients(&gelineq);
        assert!(result.is_none());
    }

    #[test]
    fn test_select_check_fn() {
        assert_eq!(
            select_check(vec![[0,1],[1,2],[3,4],[5,6]]),
            vec![[5,6],[3,4],[1,2]]
        );
        
        let empty : Vec<[u32;2]> = Vec::new();
        assert_eq!(
            select_check(vec![]),
            empty
        );

        assert_eq!(
            select_check(vec![[0,0],[1,1]]),
            vec![[1,1],[0,0]]
        );

        assert_eq!(
            select_check(vec![[1,2],[3,4],[2,5],[3,6]]),
            vec![[3,6],[2,5]]
        );

        assert_eq!(
            select_check(vec![[3,1],[2,0],[0,1]]),
            vec![[0,1]]
        );
    }

    #[test]
    fn test_theory_top_ok() {
        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3
                        }
                    )
                },
            ]
        };
        assert_eq!(*t._top(), 0);
    }

    #[test]
    #[should_panic]
    fn test_theory_top_has_circular_references() {
        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![2],
                            bias: 1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![0],
                            bias: -3
                        }
                    )
                },
            ]
        };
        t._top();
    }

    #[test]
    fn test_theory_top_should_not_panic() {
        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![2],
                            bias: 1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1],
                            bias: -3
                        }
                    )
                },
            ]
        };
        t._top();
    }

    #[test]
    fn test_theory_variable_hm_should_be_correct() {
        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 3, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 4, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 5, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 6, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 7, bounds: (0,1) },
                    expression: None
                },
            ]
        };
        let vm = t._variable_hm();
        let expected_keys : Vec<u32> = vec![0,1,2,3,4,5,6,7];
        let test_result = expected_keys.iter().map(|k| vm.contains_key(k)).all(|k| k);
        assert!(test_result);
    }
    
    #[test]
    fn test_theory_variable_hm_have_id_duplicates() {
        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: None
                },
            ]
        };
        let vm = t._variable_hm();
        let expected_keys : Vec<u32> = vec![0,1,2];
        let test_result = expected_keys.iter().map(|k| vm.contains_key(k)).all(|k| k);
        assert!(test_result);
    }
    
    #[test]
    fn test_theory_to_lineqs() {
        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 1
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 3, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 4, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 5, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 6, bounds: (0,1) },
                    expression: None
                },
                Statement {
                    variable: Variable { id: 7, bounds: (0,1) },
                    expression: None
                },
            ]
        };
        let actual: Vec<GeLineq> = t.to_lineqs(false, false);
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,1,1],
                indices: vec![0,1,2]
            },
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-3,1,1,1],
                indices: vec![2,5,6,7]
            },
            GeLineq {
                bias: 2,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,-1,-1],
                indices: vec![1,3,4]
            },
        ];
        assert!(actual.iter().zip(expected.iter()).all(|ae| ae.0.bias == ae.1.bias));
        let actual: Vec<GeLineq> = t.to_lineqs(true, false);
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                bias: -1,
                bounds: vec![(0,1),(0,1)],
                coeffs: vec![1,1],
                indices: vec![1,2]
            },
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![-3,1,1,1],
                indices: vec![2,5,6,7]
            },
            GeLineq {
                bias: 2,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,-1,-1],
                indices: vec![1,3,4]
            },
        ];
        assert!(actual.iter().zip(expected.iter()).all(|ae| ae.0.bias == ae.1.bias));
        let actual: Vec<GeLineq> = t.to_lineqs(false, true); // reduce overrides active
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                bias: 3,
                bounds: vec![(0,1),(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![-3,-3,1,1,1],
                indices: vec![3,4,5,6,7]
            },
        ];
        assert!(actual.iter().zip(expected.iter()).all(|ae| ae.0.bias == ae.1.bias));
        let actual: Vec<GeLineq> = t.to_lineqs(true, true); // same as previous
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                bias: 3,
                bounds: vec![(0,1),(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![-3,-3,1,1,1],
                indices: vec![3,4,5,6,7]
            },
        ];
        assert!(actual.iter().zip(expected.iter()).all(|ae| ae.0.bias == ae.1.bias));
    }
}
