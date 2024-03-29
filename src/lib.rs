//! # Puan rust
//! 
//! Puan algorithms implemented in Rust. 

use std::{collections::HashMap};
use std::fmt::Display;
use itertools::Itertools;
use polyopt::{GeLineq, Variable, Polyhedron, CsrPolyhedron};

pub mod solver;
pub mod linalg;
pub mod polyopt;

#[derive(Clone, Copy)]
pub enum Sign {
    Positive,
    Negative
}

impl Sign {

    /// Value representation of the various Sign choices.
    /// `Sign::Positive` is represented by `1`. 
    /// `Sign::Negative` is represented by `-1`. 
    pub fn val(&self) -> i8 {
        return match *self {
            Sign::Positive => 1,
            Sign::Negative => -1,
        }
    }
}


/// Data structure for representing an `at least` constraint on form 
/// $$ c * v_0 + c * v_1 + ... + c * v_n + bias \ge 0 $$
/// where $c=1$ if `sign == Sign::Positive`, or, $c=-1$ if `sign == Sign::Negative`.
/// `ids` vector property holds what variables are connected to this constraint.
pub struct AtLeast {
    pub ids     : Vec<u32>,
    pub bias    : i64,
    pub sign    : Sign,
}

impl Clone for AtLeast {
    fn clone(&self) -> Self {
        return AtLeast {
            bias: self.bias,
            ids: self.ids.to_vec(),
            sign: self.sign,
        }
    }
}

impl AtLeast {

    fn size(&self) -> usize {
        return self.ids.len();
    }

    /// Transform into a linear inequality constraint.
    /// `variable_hm` is a hash map of id's and variables.
    /// 
    /// # Example:
    /// 
    /// ```
    /// use puanrs::AtLeast;
    /// use puanrs::Sign;
    /// use puanrs::polyopt::GeLineq;
    /// use puanrs::polyopt::Variable;
    /// use std::{collections::HashMap};
    /// let at_least: AtLeast = AtLeast {
    ///     ids     : vec![0,1,2],
    ///     bias    : -1,
    ///     sign    : Sign::Positive,
    /// };
    /// let mut variable_hm: HashMap<u32, Variable> = HashMap::default();
    /// variable_hm.insert(0, Variable {id: 0, bounds: (0,1)});
    /// variable_hm.insert(1, Variable {id: 1, bounds: (0,1)});
    /// variable_hm.insert(2, Variable {id: 2, bounds: (0,1)});
    /// let actual: GeLineq = at_least.to_lineq(None, &variable_hm);
    /// assert_eq!(actual.coeffs, vec![1,1,1]);
    /// assert_eq!(actual.bias, -1);
    /// assert_eq!(actual.bounds, vec![(0,1),(0,1),(0,1)]);
    /// assert_eq!(actual.indices, vec![0,1,2]);
    /// ```
    pub fn to_lineq(&self, id: Option<u32>, variable_hm: &HashMap<u32, Variable>) -> GeLineq {
        return GeLineq {
            id: id,
            coeffs: vec![self.sign.val() as i64; self.size()],
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

    /// Transforms into a linear inequality constraint. Unlike `to_lineq` this is extended to include the given variable
    /// such that it holds logic as "if `given_id` is true then `self` must be true".
    fn to_lineq_extended(&self, given_id: u32, variable_hm: &HashMap<u32, Variable>) -> GeLineq {
        return GeLineq::merge_disj(
            &(variable_hm.get(&given_id).expect(&format!("variable id `{given_id}` does not exist in variable hash map"))).to_lineq_neg(),
            &self.to_lineq(Some(given_id), variable_hm)
        ).expect("could not merge disjunctions") // <- should always be able to merge here
    }

    /// Transforms into a linear inequality constraint. If sub constraints fulfills certain requirements, then the sub constraints
    /// will be merged into this constraint. If the requirements are not met, then `to_lineq_extended` is called. 
    fn to_lineq_reduced(&self, extend_default: bool, given_id: u32, variable_hm: &HashMap<u32, Variable>, statement_hm: &HashMap<u32, &Statement>) -> GeLineq {
        return match (self.bias, self.ids.len()) {
            (-1, 2) => {
                let sub_lineqs: Vec<GeLineq> = self.ids.iter().filter_map(|id| {
                    if let Some(statement) = statement_hm.get(id) {
                        if let Some(expression) = statement.expression.clone() {
                            return Some(expression.to_lineq(Some(given_id), variable_hm));
                        }
                    }
                    return None;
                }).collect();
                if sub_lineqs.len() == 2 {
                    if let Some(lineq) = GeLineq::merge_disj(&sub_lineqs[0], &sub_lineqs[1]) {
                        return lineq;
                    } else {
                        return match extend_default {
                            false => self.to_lineq(Some(given_id), variable_hm),
                            true => self.to_lineq_extended(given_id, variable_hm),
                        }
                    }
                } else {
                    return match extend_default {
                        false => self.to_lineq(Some(given_id), variable_hm),
                        true => self.to_lineq_extended(given_id, variable_hm),
                    }
                }
            },
            (-2, 2) => {
                let sub_lineqs: Vec<GeLineq> = self.ids.iter().filter_map(|id| {
                    if let Some(statement) = statement_hm.get(id) {
                        if let Some(expression) = statement.expression.clone() {
                            return Some(expression.to_lineq(Some(given_id), variable_hm));
                        }
                    }
                    return None;
                }).collect();
                if sub_lineqs.len() == 2 {
                    if let Some(lineq) = GeLineq::merge_conj(&sub_lineqs[0], &sub_lineqs[1]) {
                        return lineq;
                    } else {
                        return match extend_default {
                            false => self.to_lineq(Some(given_id), variable_hm),
                            true => self.to_lineq_extended(given_id, variable_hm),
                        }
                    }
                } else {
                    return match extend_default {
                        false => self.to_lineq(Some(given_id), variable_hm),
                        true => self.to_lineq_extended(given_id, variable_hm),
                    }
                }
            },
            _ => match extend_default {
                false => self.to_lineq(Some(given_id), variable_hm),
                true => self.to_lineq_extended(given_id, variable_hm),
            }
        }
    }
}

impl Display for AtLeast {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({})({}>={})", match self.bias < 0 {true => "+", false => "-"}, self.ids.iter().map(|v| v.to_string()).collect::<Vec<String>>().join(","), self.bias)
    }
}

/// A `Statement` is a declaration of an expression (or proposition) connected to a `Variable`.
/// For instance, "A is true iff x > 3, else false" is a statement. Currently only `AtLeast` is
/// considered to be an `Expression`.
pub struct Statement {
    pub variable    : Variable,
    pub expression  : Option<AtLeast>
}

impl Clone for Statement {
    fn clone(&self) -> Self {
        return Statement {
            variable: self.variable.clone(),
            expression: match &self.expression {
                Some(exp) => Some(exp.clone()),
                None => None
            }
        }
    }
}

/// A `Theory` is a list of statements with a common name (id).
pub struct Theory {
    pub id : String,
    pub statements : Vec<Statement>
}

impl Clone for Theory {
    fn clone(&self) -> Self {
        return Theory {
            id: self.id.clone(),
            statements: self.statements.to_vec()
        }
    }
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

    // All bottom / atomic variable ids, e.i. statements that don't have any children.
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

    /// Propagates all information bottoms-up in the Theory and compiles
    /// into a HashMap from variable id to bounds.
    ///
    /// # Example:
    /// 
    /// ```
    /// use puanrs::Theory;
    /// use puanrs::Statement;
    /// use puanrs::Sign;
    /// use puanrs::AtLeast;
    /// use puanrs::polyopt::Variable;
    /// use std::collections::HashMap;
    /// let theory: Theory = Theory {
    ///    id          : String::from("A"),
    ///    statements  : vec![
    ///        Statement {
    ///            variable    : Variable {
    ///              id      : 0,
    ///              bounds  : (0,1),
    ///            },
    ///            expression  : Some(
    ///                AtLeast {
    ///                    ids     : vec![1,2],
    ///                    bias    : -1,
    ///                    sign    : Sign::Positive
    ///                }
    ///            )
    ///       },
    ///       Statement {
    ///           variable    : Variable {
    ///               id      : 1,
    ///               bounds  : (0,1),
    ///           },
    ///           expression  : None
    ///       },
    ///       Statement {
    ///           variable    : Variable {
    ///               id      : 2,
    ///               bounds  : (1,1),
    ///           },
    ///           expression  : None
    ///       },
    ///    ]
    /// };
    /// let actual: HashMap<u32, (i64, i64)> = theory.propagate();
    /// let expected: HashMap<u32, (i64, i64)> = vec![
    ///     (0, (1,1)),
    ///     (1, (0,1)),
    ///     (2, (1,1)),
    /// ].into_iter().collect();
    /// assert_eq!(actual, expected);
    /// ```
    /// 
    pub fn propagate(&self) -> HashMap<u32, (i64, i64)> {

        // We add the primitive variables directly to the
        // result since they are already propagated.
        let mut variable_bounds: HashMap<u32, (i64, i64)> = self.statements
            .iter()
            .filter(|statement| statement.expression.is_none())
            .map(|statement| (statement.variable.id, statement.variable.bounds))
            .collect();
        let statements_hm: HashMap<u32, &Statement> = self._statement_hm();

        // We don't need to iterate over all primitive variables since
        // they are already propagated.
        let mut queue: Vec<u32> = self.statements
            .iter()
            .filter(|statement| statement.expression.is_some())
            .map(|statement| statement.variable.id)
            .collect();

        // Popping from of queue until it is empty
        while let Some(id) = queue.pop() {

            if let Some(statement) = statements_hm.get(&id) {

                if let Some(expression) = &statement.expression {

                    // Check if all ids in expression is set in variable_bounds (has been propagated)
                    if let Some(bounds) = expression.ids.iter().map(|id| variable_bounds.get(id)).collect::<Option<Vec<&(i64, i64)>>>() {
    
                        // Get bounds for expression
                        let bounds_expression: (i64, i64) = bounds.iter().fold((0,0), |acc, bound| {
                            match expression.sign {
                                
                                // This is simply adding all children bounds together if
                                // the sign is positive, e.g. x + y + z -1 >= 0 should resolve into
                                // [0,1]+[0,1]+[0,1] -1 >= 0 == [-1,2] >= 0 == [0,1]
                                Sign::Positive => (acc.0 +bound.0, acc.1 + bound.1),

                                // NOTE HERE that if the sign is negative we do not only
                                // subtract the bound but we also flip the bounds, e.g.
                                // -x -y -z +1 >= 0 should resolve into [-1,0]+[-1,0]+[-1,0]+1 >= 0 == [-2,1] >= 0 == [0,1]
                                Sign::Negative => (acc.0 - bound.1, acc.1 - bound.0),
                            }
                        });

                        // Update variable bounds
                        variable_bounds.insert(
                            statement.variable.id,
                            (
                                (bounds_expression.0 + expression.bias >= 0) as i64,
                                (bounds_expression.1 + expression.bias >= 0) as i64, 
                            )
                        );
    
                    } else {

                        // If we don't check that it actually exists in statements map
                        // we know that we will never be able to propagate fully and we
                        // will end up in an infinite loop.
                        if !statements_hm.contains_key(&id) {
                            panic!("statement id `{id}` does not exist in statements hash map");
                        }

                        // But if it does exists, we will eventually be able to propagate
                        // it so we put it back in the queue.
                        queue.push(id);
                    }

                } else {
                    variable_bounds.insert(statement.variable.id, statement.variable.bounds);
                }

            }

        }

        return variable_bounds;
    }

    /// Transforms all Statements in Theory into GeLineq's such that 
    /// if all GeLineq's are true <-> Theory is true.
    ///
    /// # Example:
    /// 
    /// ```
    /// use puanrs::Theory;
    /// use puanrs::Statement;
    /// use puanrs::Sign;
    /// use puanrs::AtLeast;
    /// use puanrs::polyopt::Variable;
    /// use puanrs::polyopt::GeLineq;
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
    ///                     bias    : -1,
    ///                     sign    : Sign::Positive
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
                                !((statement.variable.id == top_node_id) & active), 
                                statement.variable.id,
                                &var_hm,
                                &state_hm,
                            )
                        ),
                        false => match (statement.variable.id == top_node_id) & active {
                            true => Some(a.to_lineq(Some(statement.variable.id), &var_hm)),
                            false => Some(a.to_lineq_extended(statement.variable.id, &var_hm))
                        }
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

    /// Converts Theory into a polyhedron. Set `active` param to true
    /// to activate polyhedron, meaning assuming the top node to be true. 
    /// Set `reduced` to true to potentially retrieve a reduced polyhedron.
    pub fn to_ge_polyhedron(&self, active: bool, reduced: bool) -> CsrPolyhedron {
        let lineqs = self.to_lineqs(active, reduced);
        let mut index_bound_vec: Vec<(u32, (i64,i64))> = Vec::default();
        for lineq in lineqs.iter() {
            for (index, bound) in lineq.indices.iter().zip(lineq.bounds.iter()) {
                let element = (*index, *bound);
                if !index_bound_vec.contains(&element) {
                    index_bound_vec.push(element);
                }
            }
        }

        let size = lineqs.iter().map(|l| l.indices.len()).sum(); 

        let mut row: Vec<i64> = vec![0; size];
        let mut col: Vec<i64> = vec![0; size];
        let mut val: Vec<f64> = vec![0.0; size];
        let mut i: usize = 0;
        for (il, lineq) in lineqs.iter().enumerate() {
            for (index, cf) in lineq.indices.iter().zip(lineq.coeffs.iter()) {
                row[i] = il as i64;
                col[i] = (*index) as i64;
                val[i] = (*cf) as f64;
                i += 1;
            }
        }
        
        let actual_indices: Vec<u32> = index_bound_vec.iter().map(|x| x.0).sorted().collect();
        let index_bound_hm : HashMap<u32, (i64, i64)> = index_bound_vec.clone().into_iter().collect();
        let variables: Vec<Variable> = actual_indices.iter().filter_map(|i| {
            if let Some(bounds) = index_bound_hm.get(i) {
                return Some(
                    Variable {
                        id: *i,
                        bounds: bounds.clone()
                    }
                )
            }
            return None;
        }).collect();
        return CsrPolyhedron {
            a: linalg::CsrMatrix { 
                val: val, 
                row: row,
                col: col
            },
            b: lineqs.iter().map(|x| (-1*x.bias) as f64).collect(),
            variables: variables.iter().map(|x| x.to_variable_float()).collect(),
            index: lineqs.iter().map(|x| x.id).collect(),
        };
    }

    /// Find solutions to this Theory. `objectives` is a vector of HashMap's pointing from
    /// an id to a value. The solver will try to find a valid configuration that maximizes those values,
    /// for each objective in objectives.
    /// # Note
    /// * Ids given in objectives which are not in Theory will be ignored.
    /// * Ids which have not been given a value will be given 0 as default.
    /// 
    /// # Returns
    /// A tuple of (solution: HashMap<u32, i64>, objective value: i64, status code: usize)
    /// 
    /// # Example:
    /// 
    /// ```
    /// use puanrs::Theory;
    /// use puanrs::Statement;
    /// use puanrs::Sign;
    /// use puanrs::AtLeast;
    /// use puanrs::polyopt::Variable;
    /// let t = Theory {
    ///    id: String::from("A"),
    ///     statements: vec![
    ///         Statement {
    ///            variable: Variable { id: 0, bounds: (0,1) },
    ///            expression: Some(
    ///                AtLeast {
    ///                    ids: vec![1,2],
    ///                    bias: -1,
    ///                    sign: Sign::Positive
    ///                }
    ///            )
    ///        },
    ///        Statement {
    ///            variable: Variable { id: 1, bounds: (0,1) },
    ///            expression: Some(
    ///                AtLeast {
    ///                    ids: vec![3,4],
    ///                    bias: 1,
    ///                    sign: Sign::Negative
    ///                }
    ///            )
    ///        },
    ///        Statement {
    ///            variable: Variable { id: 2, bounds: (0,1) },
    ///            expression: Some(
    ///                AtLeast {
    ///                    ids: vec![5,6,7],
    ///                    bias: -3,
    ///                    sign: Sign::Positive,
    ///                }
    ///            )
    ///        },
    ///        Statement {
    ///            variable: Variable { id: 3, bounds: (0,1) },
    ///            expression: None
    ///        },
    ///        Statement {
    ///            variable: Variable { id: 4, bounds: (0,1) },
    ///            expression: None
    ///        },
    ///        Statement {
    ///            variable: Variable { id: 5, bounds: (0,1) },
    ///            expression: None
    ///        },
    ///        Statement {
    ///            variable: Variable { id: 6, bounds: (0,1) },
    ///            expression: None
    ///        },
    ///        Statement {
    ///            variable: Variable { id: 7, bounds: (0,1) },
    ///            expression: None
    ///        },
    ///     ]
    /// };
    /// let actual_solutions = t.solve(
    ///     vec![
    ///         vec![(3, 1.0), (4, 1.0)].iter().cloned().collect(),
    ///     ],
    ///     true
    /// );
    /// let expected_solutions = vec![
    ///    vec![(3,1),(4,1),(5,1),(6,1),(7,1)].iter().cloned().collect(), // <- notice that these are from reduced columns (3,4,5,6,7)
    /// ];
    /// assert_eq!(actual_solutions[0].0, expected_solutions[0]);
    pub fn solve(&self, objectives: Vec<HashMap<u32, f64>>, reduce_polyhedron: bool) -> Vec<(HashMap<u32, i64>, i64, usize)> {
        let polyhedron: Polyhedron = self.to_ge_polyhedron(true,reduce_polyhedron).to_dense_polyhedron();
        let _objectives: Vec<Vec<f64>> = objectives.iter().map(|x| {
            let mut vector = vec![0.0; polyhedron.variables.len()];
            for (k, v) in x.iter() {
                let pot_index = polyhedron.variables.iter().position(|y| y.id == (*k));
                if let Some(index) = pot_index {
                    vector[index] = *v;
                }
            }
            return vector;
        }).collect();
        return _objectives.iter().map(|objective| {
            let ilp = solver::IntegerLinearProgram {
                ge_ph: polyhedron.to_owned(),
                eq_ph: Default::default(),
                of: objective.to_vec(),
            };
            return ilp.solve();
        }).map(|sol| {
            (
                polyhedron.variables.clone().iter().map(|x| x.id).zip(sol.x).collect(),
                sol.z,
                sol.status_code,
            )
        }).collect();
    }

    /// Given two positive integers `n` (width) and `m` (depth), this function creates a n-ary Theory/tree, with variable 
    /// size $ n^0 + n^1 + ... + n^m $. Each Statement with Some expression has bias -1 and `n` number of children.
    /// For eaxmple, `Theory::instance(2, 3, String::from("my-id"))` would create a binary tree/Theory of variable size $ 2^3 = 8 $.
    /// # Note
    /// This function was mainly created to support benchmarking tests for different Theory sizes.
    pub fn instance(width: u32, depth: u32, id: String) -> Theory {
        
        let n: u32 = (0..depth).into_iter().map(|i| width.pow(i as u32)).sum();
        let n_before_leafs: u32 = n - width.pow(depth-1);
        return Theory {
            id,
            statements: (0..n).into_iter().map(|i| {
                let start_index = i*width+1;
                match i < n_before_leafs {
                    true => Statement {
                        variable: Variable {
                            id: i,
                            bounds: (0,1)
                        },
                        expression: Some(
                            AtLeast {
                                bias: -1,
                                ids: (start_index..start_index+width).collect_vec(),
                                sign: Sign::Positive,
                            }
                        )
                    },
                    false => Statement {
                        variable: Variable {
                            id: i,
                            bounds: (0,1)
                        },
                        expression: None
                    }
                }
            }).collect(), 
        };
    }

}

#[cfg(test)]
mod tests {
    use std::vec;

    use crate::{linalg::Matrix, polyopt::VariableFloat};

    use super::*;

    use std::ops::Range;
    use itertools::Itertools;

    impl GeLineq {
        
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
    }

    #[test]
    fn test_theory_propagate() {
        let theory: Theory = Theory {
            id          : String::from("A"),
            statements  : vec![
                Statement {
                    variable    : Variable {
                        id      : 0,
                        bounds  : (0,1),
                    },
                    expression  : Some(
                        AtLeast {
                            ids     : vec![1,2],
                            bias    : -1,
                            sign    : Sign::Positive
                        }
                    )
                },
                Statement {
                    variable    : Variable {
                        id      : 1,
                        bounds  : (0,1),
                    },
                    expression  : None
                },
                Statement {
                    variable    : Variable {
                        id      : 2,
                        bounds  : (1,1),
                    },
                    expression  : None
                },
            ]
        };
        let actual: HashMap<u32, (i64, i64)> = theory.propagate();
        let expected: HashMap<u32, (i64, i64)> = vec![
            (0, (1,1)),
            (1, (0,1)),
            (2, (1,1)),
        ].into_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_generate_instance_to_polyhedron() {
        for (w,d) in [(2,2),(2,3),(2,4),(3,3),(3,4),(4,4)] {
            let theory: Theory = Theory::instance(w, d, String::from("my-id"));
            let polyhedron: Polyhedron = theory.to_ge_polyhedron(true, false).to_dense_polyhedron();
            assert_eq!(polyhedron.variables.len(), theory.statements.len()-1);
        }
    }

    // Validates that all combinations, generated from `variable_bounds`, in two vectors of GeLineqs gives the same result, i.e. they hold the same truth table```
    // The `all_relation` states how the GeLineq within each vector relates. If `all_relation` is true then all GeLineqs of the vector must hold to produce `True` as output. If `all_relation` is false then it is treated as an any, and only one GeLineq of the vector must hold to produce `True` as output. 
    fn validate_all_combinations(variable_bounds: Vec<(u32, (i64, i64))>, lineqs0: Vec<GeLineq>, lineqs1: Vec<GeLineq>, all_relation: bool) -> bool {

        let base : i64 = 2;
        let max_combinations: i64 = base.pow(15);
        let bound_ranges: Vec<std::ops::Range<i64>> = variable_bounds.iter().map(|x| Range {start: x.1.0, end: x.1.1+1}).collect_vec();
        let n_combinations : i64 = variable_bounds.iter().map(|x| (x.1.1+1)-x.1.0).product();
        if n_combinations > max_combinations {
            panic!("number of combinations ({n_combinations}) to test are more than allowed ({max_combinations})");
        }

        return bound_ranges.into_iter().multi_cartesian_product().all(|combination| {
            let variable_ids : Vec<u32> = variable_bounds.iter().map(|x| x.0).collect_vec();
            let variable_combination: Vec<(u32, i64)> = variable_ids.into_iter().zip(combination).collect();

            let res0: bool;
            let res1: bool;
            if all_relation {
                res0 = lineqs0.iter().all(|x| x.satisfied(variable_combination.clone()));
                res1 = lineqs1.iter().all(|x| x.satisfied(variable_combination.clone()));
            } else {
                res0 = lineqs0.iter().any(|x| x.satisfied(variable_combination.clone()));
                res1 = lineqs1.iter().any(|x| x.satisfied(variable_combination.clone()));
            }
            return (res0 & res1) | !(res0 & res1);
        })
    }
    
    #[test]
    fn test_theory_to_lineqs_reduced() {

        fn validate(t: Theory) -> bool {
            let non_reduced: Vec<GeLineq> = t.to_lineqs(true, false);
            let reduced: Vec<GeLineq> = t.to_lineqs(true, true);
            let variable_bounds: Vec<(u32, (i64, i64))> = t.statements.into_iter().map(|x| (x.variable.id, x.variable.bounds)).collect();
            return validate_all_combinations(variable_bounds, non_reduced, reduced, true)
        }

        // Depth 3
        // 0: 1 & 2
        // 1: 3 + 4 >= 6 (3 has bounds (-5,5), 4 is bool) 
        // 2: 5 + 6 >= 4 (5 has bounds (-3,3), 6 is bool) 

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
                            bias: -2,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: -6,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6],
                            bias: -4,
                            sign: Sign::Positive,
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
        assert!(validate(t));

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
                            bias: -3,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![4,5],
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6],
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 3, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![7,8],
                            bias: -2,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 4, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![9,10],
                            bias: -2,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 5, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![11],
                            bias: 0,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 6, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![12,13],
                            bias: -1,
                            sign: Sign::Positive,
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
        assert!(validate(t));

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
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 1,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3,
                            sign: Sign::Positive,
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
        assert!(validate(t));
        
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
                            bias: -2,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 0,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3,
                            sign: Sign::Positive,
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
        assert!(validate(t));
        
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
                            bias: -2,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: -2,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6],
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 3, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![7,8],
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 4, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![9,10],
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 5, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![11],
                            bias: 0,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 6, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![12,13],
                            bias: -2,
                            sign: Sign::Positive,
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
        assert!(validate(t));
    }

    #[test]
    fn test_merge_conj_disj(){

        fn validate_all_combinations_single(ge_lineq1: GeLineq, ge_lineq2: GeLineq, conj: bool) -> bool {
            let mut variable_bounds_hm: HashMap<u32, (i64,i64)> = HashMap::default();
            for lineq in vec![ge_lineq1.clone(), ge_lineq2.clone()] {
                for (id, bound) in lineq.indices.iter().zip(lineq.bounds) {
                    variable_bounds_hm.insert(*id, bound);
                }
            }
            let variable_bounds = variable_bounds_hm.into_iter().collect();
            if conj {
                if let Some(merged) = GeLineq::merge_conj(&ge_lineq1, &ge_lineq2) {
                    return validate_all_combinations(
                        variable_bounds, 
                        vec![ge_lineq1, ge_lineq2], 
                        vec![merged], 
                        true
                    );
                }
                return false;
            } else {
                if let Some(merged) = GeLineq::merge_disj(&ge_lineq1, &ge_lineq2) {
                    return validate_all_combinations(
                        variable_bounds, 
                        vec![ge_lineq1, ge_lineq2], 
                        vec![merged], 
                        false
                    );
                }
                return false;
            }
        }

        // Disjunction merge between 1-1
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 6]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));
        
        // }
        // Disjunction merge between 2-3
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![1, 2, 3, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 1-1
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 1-2
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 3,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 1-3
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 1-4
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 1-5
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 1-6
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 2-2
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 3,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 2-3
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 2-4
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 2-5
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Disjunction merge between 2-6
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Conjunction merge between 4-4
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 0, 4]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 4-3
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 1-4
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 2-3
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 2-4
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 3-3
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 3-4
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 3-5
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 3-6
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 4-4
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 4-5
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 4-6
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1, -1, -1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : 2,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Conjunction merge between 4-4
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -4,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));

        // Disjunction merge, special case
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(-2, -1), (2, 3), (2, 3)],
            bias    : -3,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, false));

        // Conjunction merge, special case
        let ge_lineq1:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(-2, -1), (2, 3), (2, 3)],
            bias    : -5,
            indices : vec![1, 2, 3]
        };
        let ge_lineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![5, 6, 7, 8]
        };
        assert!(validate_all_combinations_single(ge_lineq1, ge_lineq2, true));
    }
    
    #[test]
    fn test_substitution() {

        fn validate_substitution(main_lineq: GeLineq, sub_lineq: GeLineq, variable_index: u32) -> bool {
            if let Some(result) = GeLineq::substitution(&main_lineq, variable_index, &sub_lineq) {
                let mut variable_bounds_hm: HashMap<u32, (i64,i64)> = HashMap::default();
                for lineq in vec![main_lineq.clone(), sub_lineq.clone()] {
                    for (id, bound) in lineq.indices.iter().zip(lineq.bounds) {
                        if (*id) != variable_index {
                            variable_bounds_hm.insert(*id, bound);
                        }
                    }
                }
                let variable_bounds: Vec<(u32, (i64, i64))> = variable_bounds_hm.into_iter().collect();
                let variable_ids : Vec<u32> = variable_bounds.iter().map(|x| x.0).collect_vec();
                let bound_ranges: Vec<std::ops::Range<i64>> = variable_bounds.iter().map(|x| Range {start: x.1.0, end: x.1.1+1}).collect_vec();
                return bound_ranges.into_iter().multi_cartesian_product().all(|combination| {
                    let mut main_variable_combination: Vec<(u32, i64)> = variable_ids.clone().into_iter().zip(combination.clone()).filter(|(id, _)| {
                        main_lineq.indices.contains(id)
                    }).collect();
                    let sub_variable_combination: Vec<(u32, i64)> = variable_ids.clone().into_iter().zip(combination.clone()).filter(|(id, _)| {
                        sub_lineq.indices.contains(id)
                    }).collect();
                    let sub_value: i64 = sub_lineq.satisfied(sub_variable_combination) as i64;
                    main_variable_combination.push((variable_index, sub_value));

                    let main_result = main_lineq.satisfied(main_variable_combination);
                    let substitution_result = result.satisfied(variable_ids.clone().into_iter().zip(combination.clone()).collect());

                    return (!main_result & !substitution_result) | (main_result & substitution_result);
                });
            }

            return false;
        }

        // Negative bias on sub lineq
        let main_gelineq:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -2,
            indices : vec![4,5]
        };
        assert!(validate_substitution(main_gelineq, sub_gelineq, 3));

        let main_gelineq:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -1,
            indices : vec![4,5]
        };
        assert!(validate_substitution(main_gelineq, sub_gelineq, 3));

        // Positive bias on sub lineq
        let main_gelineq:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, -1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : 1,
            indices : vec![4,5]
        };
        assert!(validate_substitution(main_gelineq, sub_gelineq, 3));

        // Not possible to substitute
        let main_gelineq:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : 0,
            indices : vec![4,5, 6]
        };
        assert!(!validate_substitution(main_gelineq, sub_gelineq, 3));

        let main_gelineq:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1],
            bounds  : vec![(0, 1)],
            bias    : 0,
            indices : vec![1]
        };
        let sub_gelineq: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1],
            bounds  : vec![(0, 10)],
            bias    : -3,
            indices : vec![2]
        };
        assert!(validate_substitution(main_gelineq.clone(), sub_gelineq.clone(), 1));
        let result = GeLineq::substitution(&main_gelineq, 1, &sub_gelineq);
        assert_eq!(vec![-1], result.as_ref().expect("").coeffs);
        assert_eq!(vec![(0, 10)], result.as_ref().expect("").bounds);
        assert_eq!(2, result.as_ref().expect("").bias);

        // Mixed signs of coeffs in sub lineq, possible to merge
        let main_gelineq:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![-1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -1,
            indices : vec![4,5, 6]
        };
        assert!(validate_substitution(main_gelineq, sub_gelineq, 3));

        let main_gelineq:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2]
        };
        let sub_gelineq: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -1,
            indices : vec![3, 4]
        };
        assert!(validate_substitution(main_gelineq, sub_gelineq, 2));

        let main_gelineq:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -1,
            indices : vec![1, 2]
        };
        let sub_gelineq: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -1,
            indices : vec![3, 4]
        };
        assert!(validate_substitution(main_gelineq, sub_gelineq, 2));

        let main_gelineq:GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1, 1],
            bounds  : vec![(0, 1), (0, 1), (0, 1)],
            bias    : -2,
            indices : vec![1, 2, 3]
        };
        let sub_gelineq1: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -2,
            indices : vec![4, 5]
        };
        let sub_gelineq2: GeLineq = GeLineq {
            id: None,
            coeffs  : vec![1, 1],
            bounds  : vec![(0, 1), (0, 1)],
            bias    : -2,
            indices : vec![6, 7]
        };
        let result1 = GeLineq::substitution(&main_gelineq, 2, &sub_gelineq1);
        assert!(validate_substitution(main_gelineq, sub_gelineq1, 2));
        let result2 = GeLineq::substitution(&result1.as_ref().expect("No gelineq created"), 3, &sub_gelineq2);
        assert!(result2.is_none());
    }

    #[test]
    fn test_min_max_coefficients() {

        fn validate_all_combinations_single_min_max(gelineq: GeLineq, expected_vec: Option<Vec<i64>>) -> bool {
            let mut variable_bounds_hm: HashMap<u32, (i64,i64)> = HashMap::default();
            for (id, bound) in gelineq.indices.iter().zip(gelineq.bounds.clone()) {
                variable_bounds_hm.insert(*id, bound);
            }
            let variable_bounds = variable_bounds_hm.into_iter().collect();
            if let Some(result) = GeLineq::min_max_coefficients(&gelineq) {
                let validation = validate_all_combinations(
                    variable_bounds, 
                    vec![gelineq], 
                    vec![result.clone()], 
                    true
                );
                if let Some(vec) = expected_vec {
                    return validation & (vec == result.coeffs)
                } 
                return validation;
            }
            return false;
        }

        assert!(
            validate_all_combinations_single_min_max(
                GeLineq {
                    id: None, 
                    coeffs: vec![2, 1, 1],
                    bounds: vec![(0,1),(0,1),(0,1)],
                    bias: -1,
                    indices: vec![0, 1, 2]
                }, 
                Some(vec![1, 1, 1])
            )
        );
        assert!(
            !validate_all_combinations_single_min_max(
                GeLineq {
                    id: None, 
                    coeffs: vec![2, 1, 1],
                    bounds: vec![(-2,-1),(0,1),(0,1)],
                    bias: 0,
                    indices: vec![0, 1, 2]
                }, 
                None
            )
        );
        assert!(
            validate_all_combinations_single_min_max(
                GeLineq {
                    id: None, 
                    coeffs: vec![5, 6, 3],
                    bounds: vec![(0,1),(0,1),(0,1)],
                    bias: -1,
                    indices: vec![0, 1, 2]
                }, 
                Some(vec![1, 1, 1])
            )
        );
        assert!(
            validate_all_combinations_single_min_max(
                GeLineq {
                    id: None, 
                    coeffs: vec![-2, -1, -1],
                    bounds: vec![(0,1),(0,1),(0,1)],
                    bias: 0,
                    indices: vec![0, 1, 2]
                }, 
                Some(vec![-1, -1, -1]),
            )
        );
        assert!(
            validate_all_combinations_single_min_max(
                GeLineq {
                    id: None, 
                    coeffs: vec![-2, -1, -1],
                    bounds: vec![(0,1),(0,1),(0,1)],
                    bias: 1,
                    indices: vec![0, 1, 2]
                }, 
                Some(vec![-2,-1,-1]),
            )
        );
        assert!(
            !validate_all_combinations_single_min_max(
                GeLineq {
                    id: None, 
                    coeffs: vec![-2, 1, 1],
                    bounds: vec![(0,1),(0,1),(0,1)],
                    bias: 0,
                    indices: vec![0, 1, 2]
                }, 
                None
            )
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
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 1,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3,
                            sign: Sign::Positive,
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
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![2],
                            bias: 1,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![0],
                            bias: -3,
                            sign: Sign::Positive,
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
                            bias: 1,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1],
                            bias: -3,
                            sign: Sign::Positive,
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
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 1,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3,
                            sign: Sign::Positive,
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
                            bias: -1,
                            sign: Sign::Positive,
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

        fn validate_theory_lineqs(t: Theory, actual: Vec<GeLineq>, expected: Vec<GeLineq>) -> bool {
            assert!(actual.iter().zip(expected.clone()).all(|(a,b)| {
                let bias_eq = a.bias == b.bias;
                let indices_eq = a.indices == b.indices;
                let coeffs_eq = a.coeffs == b.coeffs;
                let bounds_eq = a.bounds == b.bounds;
                bias_eq & indices_eq & coeffs_eq & bounds_eq
            }));
            return validate_all_combinations(
                t.statements.into_iter().map(|x| (x.variable.id, x.variable.bounds)).collect(), 
                actual, 
                expected, 
                true
            )
        }

        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 1,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3,
                            sign: Sign::Positive,
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
                id: None,
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,1,1],
                indices: vec![0,1,2]
            },
            GeLineq {
                id: None,
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![-3,1,1,1],
                indices: vec![2,5,6,7]
            },
            GeLineq {
                id: None,
                bias: 2,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,-1,-1],
                indices: vec![1,3,4]
            },
        ];
        assert!(validate_theory_lineqs(t.clone(), actual, expected));
        let actual: Vec<GeLineq> = t.to_lineqs(true, false);
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                id: None,
                bias: -1,
                bounds: vec![(0,1),(0,1)],
                coeffs: vec![1,1],
                indices: vec![1,2]
            },
            GeLineq {
                id: None,
                bias: 0,
                bounds: vec![(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![-3,1,1,1],
                indices: vec![2,5,6,7]
            },
            GeLineq {
                id: None,
                bias: 2,
                bounds: vec![(0,1),(0,1),(0,1)],
                coeffs: vec![-1,-1,-1],
                indices: vec![1,3,4]
            },
        ];
        assert!(validate_theory_lineqs(t.clone(), actual, expected));
        let actual: Vec<GeLineq> = t.to_lineqs(false, true); // reduce overrides active
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                id: None,
                bias: 3,
                bounds: vec![(0,1),(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![-3,-3,1,1,1],
                indices: vec![3,4,5,6,7]
            },
        ];
        assert!(validate_theory_lineqs(t.clone(), actual, expected));
        let actual: Vec<GeLineq> = t.to_lineqs(true, true); // same as previous
        let expected: Vec<GeLineq> = vec![
            GeLineq {
                id: None,
                bias: 3,
                bounds: vec![(0,1),(0,1),(0,1),(0,1),(0,1)],
                coeffs: vec![-3,-3,1,1,1],
                indices: vec![3,4,5,6,7]
            },
        ];
        assert!(validate_theory_lineqs(t.clone(), actual, expected));
    }
    #[test]
    fn test_solver(){
        let obj = vec![3.0, 1.0, -1.0, -1.0, 1.0];
        let ilp = solver::IntegerLinearProgram {
            ge_ph: Polyhedron {
                a: linalg::Matrix { 
                    val: vec![-3.0, -3.0, 1.0, 1.0, 1.0], 
                    ncols: 5, 
                    nrows: 1 
                },
                b: vec![-3.0],
                variables: vec![
                    VariableFloat {id: 3, bounds: (0.0, 1.0) },
                    VariableFloat {id: 4, bounds: (0.0, 1.0) },
                    VariableFloat {id: 5, bounds: (0.0, 1.0) },
                    VariableFloat {id: 6, bounds: (0.0, 1.0) },
                    VariableFloat {id: 7, bounds: (0.0, 1.0) }
                ],
                index: (0..1).map(|x| Some(x as u32)).collect(),
            },
            eq_ph: Default::default(),
            of: obj.to_vec(),
        };
        let actual_solution = ilp.solve();
        let expected_solution_x = vec![1,0,0,0,1];
        assert_eq!(actual_solution.x, expected_solution_x);
        assert_eq!(actual_solution.z, 4);
    }

    #[test]
    fn test_theory_to_ge_polyhedron() {

        fn validate(actual: Polyhedron, expected: Polyhedron) -> bool {
            if actual.variables != expected.variables {
                return false;
            }

            let variable_bounds: Vec<(f64, f64)> = actual.bounds();
            let base : i64 = 2;
            let max_combinations: i64 = base.pow(15);
            let bound_ranges: Vec<std::ops::Range<i64>> = variable_bounds.iter().map(|x| Range {start: (x.0 as i64), end: (x.1 as i64)+1}).collect_vec();
            let n_combinations : i64 = variable_bounds.iter().map(|x| ((x.1 as i64)+1)-(x.0 as i64)).product();
            if n_combinations > max_combinations {
                panic!("number of combinations ({n_combinations}) to test are more than allowed ({max_combinations})");
            }

            let combinations: Vec<Vec<i64>> = bound_ranges.clone().into_iter().multi_cartesian_product().collect();
            let combination_matrix: Matrix = Matrix {
                val: combinations.clone().into_iter().concat().iter().map(|x| (*x) as f64).collect(),
                ncols: bound_ranges.len(),
                nrows: combinations.len(),
            };

            let actual_dot: Matrix = actual.a.dot(&combination_matrix.transpose());
            let actual_dot_cmp: Vec<bool> = actual_dot.val.chunks(actual_dot.nrows).map(|x| {
                x.iter().zip(actual.b.clone()).map(|(v0,v1)| (*v0) >= v1).collect()
            }).concat();
            let expected_dot: Matrix = expected.a.dot(&combination_matrix.transpose());
            let expected_dot_cmp: Vec<bool> = expected_dot.val.chunks(expected_dot.nrows).map(|x| {
                x.iter().zip(expected.b.clone()).map(|(v0,v1)| (*v0) >= v1).collect()
            }).concat();

            return actual_dot_cmp == expected_dot_cmp;
        }

        // Depth 3
        // 0: 1 & 2
        // 1: 3 + 4 >= 6 (3 has bounds (-5,5), 4 is bool) 
        // 2: 5 + 6 >= 4 (5 has bounds (-3,3), 6 is bool) 

        // Since each variable must be set to their max we can
        // reduce into one single constraint (3)+(4)+(5)+(6) >= 10

        // Expected constraints:
        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -2,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: -6,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6],
                            bias: -4,
                            sign: Sign::Positive,
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
        
        let expected: Polyhedron = Polyhedron { 
            a: linalg::Matrix { 
                val: vec![1.0, 1.0, 1.0, 1.0], 
                ncols: 4, 
                nrows: 1 
            },
            b: vec![10.0],
            variables: vec![
                VariableFloat {
                    id: 3,
                    bounds: (-5.0, 5.0),
                },
                VariableFloat {
                    id: 4,
                    bounds: (0.0, 1.0),
                },
                VariableFloat {
                    id: 5,
                    bounds: (-3.0, 3.0),
                },
                VariableFloat {
                    id: 6,
                    bounds: (0.0, 1.0),
                },
            ],
            index: (0..1).map(|x| Some(x as u32)).collect(),
        };
        assert!(validate(t.to_ge_polyhedron(true, true).to_dense_polyhedron(), expected));

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
                            bias: -3,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![4,5],
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6],
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 3, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![7,8],
                            bias: -2,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 4, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![9,10],
                            bias: -2,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 5, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![11],
                            bias: 0,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 6, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![12,13],
                            bias: -1,
                            sign: Sign::Positive,
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

        let expected: Polyhedron = Polyhedron { 
            a: linalg::Matrix { 
                val: vec![1.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -2.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0, -1.0, 1.0, 1.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0, 1.0, -2.0, 0.0, 0.0], 
                ncols: 10, 
                nrows: 4
            },
            b: vec![3.0, 0.0, 0.0, 0.0],
            variables: vec![
                VariableFloat {id: 1, bounds: (0.0, 1.0)},
                VariableFloat {id: 2, bounds: (0.0, 1.0)},
                VariableFloat {id: 3, bounds: (0.0, 1.0)},
                VariableFloat {id: 7, bounds: (0.0, 1.0)},
                VariableFloat {id: 8, bounds: (0.0, 1.0)},
                VariableFloat {id: 9, bounds: (0.0, 1.0)},
                VariableFloat {id: 10, bounds: (0.0, 1.0)},
                VariableFloat {id: 11, bounds: (0.0, 1.0)},
                VariableFloat {id: 12, bounds: (0.0, 1.0)},
                VariableFloat {id: 13, bounds: (0.0, 1.0)},
            ],
            index: (0..4).map(|x| Some(x as u32)).collect(),
            // variable_ids: vec![1, 2, 3, 7, 8, 9, 10, 11, 12, 13] 
        };
        assert!(validate(t.to_ge_polyhedron(true, true).to_dense_polyhedron(), expected));

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
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 1,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3,
                            sign: Sign::Positive,
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

        let expected: Polyhedron = Polyhedron { 
            a: linalg::Matrix { 
                val: vec![-3.0, -3.0, 1.0, 1.0, 1.0], 
                ncols: 5, 
                nrows: 1
            },
            b: vec![-3.0],
            variables: vec![
                VariableFloat {id: 3, bounds: (0.0, 1.0)},
                VariableFloat {id: 4, bounds: (0.0, 1.0)},
                VariableFloat {id: 5, bounds: (0.0, 1.0)},
                VariableFloat {id: 6, bounds: (0.0, 1.0)},
                VariableFloat {id: 7, bounds: (0.0, 1.0)},
            ],
            index: (0..1).map(|x| Some(x as u32)).collect(),
        };
        assert!(validate(t.to_ge_polyhedron(true, true).to_dense_polyhedron(), expected));
    }

    #[test]
    fn test_theory_solve() {
        let t = Theory {
            id: String::from("A"),
            statements: vec![
                Statement {
                    variable: Variable { id: 0, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![1,2],
                            bias: -1,
                            sign: Sign::Positive,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 1, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![3,4],
                            bias: 1,
                            sign: Sign::Negative,
                        }
                    )
                },
                Statement {
                    variable: Variable { id: 2, bounds: (0,1) },
                    expression: Some(
                        AtLeast {
                            ids: vec![5,6,7],
                            bias: -3,
                            sign: Sign::Positive,
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
        let actual_solutions = t.solve(
            vec![
                vec![(3, 1.0), (4, 1.0)].iter().cloned().collect(),
                vec![(3, 2.0), (4, 1.0), (5, -1.0), (6, -1.0), (7, -1.0)].iter().cloned().collect(),
                // vec![3.0, 1.0,-1.0,-1.0, 1.0],
            ], true);
        let expected_solutions = vec![
            vec![(3,1),(4,1),(5,1),(6,1),(7,1)].iter().cloned().collect(),
            vec![(3,1),(4,0),(5,0),(6,0),(7,0)].iter().cloned().collect(),
        ];
        assert!(actual_solutions.iter().zip(expected_solutions).all(|(x,y)| x.0 == y));
    }
}