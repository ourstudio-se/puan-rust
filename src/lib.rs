//! # Puan rust
//! 
//! Puan algorithms implemented in Rust. 

use std::hash::Hash;
use std::{collections::HashMap};
use std::fmt::Display;
use itertools::iproduct;
use std::cmp;

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

    pub fn substitution(main_gelineq: &GeLineq, variable_index: u32, sub_gelineq: &GeLineq) -> Option<GeLineq> {
        let var_to_substitute = main_gelineq.indices.iter().position(|x| x == variable_index).expect(&format!("Variable '{variable_index}' to substitute not found"))
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
#[derive(Copy)]
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
    /// let at_least: AtLeast = AtLeast {
    ///     ids     : vec![0,1,2],
    ///     bias   : -1,
    /// };
    /// let variable_bounds: Vec<(i64,i64)> = vec![(0,1),(0,1),(0,1)];
    /// let actual: GeLineq = at_least.to_lineq(variable_bounds);
    /// assert_eq!(actual.coeffs, vec![1,1,1]);
    /// assert_eq!(actual.bias, -1);
    /// assert_eq!(actual.bounds, vec![(0,1),(0,1),(0,1)]);
    /// assert_eq!(actual.indices, vec![0,1,2]);
    /// ```
    pub fn to_lineq(&self, variable_bounds: Vec<(i64,i64)>) -> GeLineq {
        return GeLineq {
            coeffs: vec![match self.bias >= 0 {true => -1, false => 1}; self.size()],
            bias: self.bias,
            bounds: variable_bounds,
            indices: self.ids.to_vec()
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
    /// let actual: Vec<GeLineq> = theory.to_lineqs();
    /// assert_eq!(actual.len(), 1);
    /// assert_eq!(actual[0].bias, 0);
    /// assert_eq!(actual[0].coeffs, vec![-1,1,1]);
    /// assert_eq!(actual[0].indices, vec![0,1,2]);
    /// ```
    pub fn to_lineqs(&self) -> Vec<GeLineq> {
        let var_hm: HashMap<u32, Variable> = self._variable_hm();
        return self.statements.iter().filter_map(
            |statement: &Statement| match &statement.expression {
                Some(a) => GeLineq::merge_disj(
                    &statement.variable.to_lineq_neg(),
                    &a.to_lineq(
                        a.ids.iter().map(
                            |id| {
                                var_hm.get(id).expect(
                                    &format!(
                                        "got id `{id}` in expression {a} that was not in theory"
                                    )
                                ).bounds
                            }
                        ).collect()
                    )
                ),
                None => None
            }
        ).collect();
    }

    // fn to_lineqs_red(&self) -> Vec<GeLineq> {
    //     let state_hm: HashMap<u32, &Statement> = self.statement_hm();
    //     let queue: Vec<u32> = vec![*self.top()];
    //     while queue.len() > 0 {
    //         current_statement : &Statement = queue
    //     }
    // }
}

#[cfg(test)]
mod tests {
    use super::*;

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
        // Should fail
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
        for (i) in iproduct!(0..11){
            let x:i64 = sub_gelineq.satisfied(vec![(2, i)]) as i64;
            assert_eq!(main_gelineq.satisfied(vec![(2, i), (1, x)]), result.as_ref().expect("No result generated").satisfied(vec![(2, i), (1, x)]));
        }
        
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
        let actual: Vec<GeLineq> = t.to_lineqs();
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,1,1],
                indices: vec![0,1,2]
            },
            GeLineq {
                bias: 2,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,-1,-1],
                indices: vec![1,3,4]
            },
            GeLineq {
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![-3,1,1,1],
                indices: vec![2,5,6,7]
            },
        ];
        let test_ok = actual.iter().zip(expected.iter()).all(|ae| ae.0.bias == ae.1.bias);
        assert!(test_ok);
    }

}
