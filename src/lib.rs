//! Puan algorithms implemented in Rust. 
//! 

use theory::Theory;
use std::{collections::HashMap};

pub mod solver;
pub mod linalg;
pub mod polyopt;
pub mod theory;


pub trait PropositionTrait {
    fn to_statement(&self) -> theory::Statement;
    fn variable(&self) -> polyopt::Variable;
}

#[derive(Debug)]
pub enum Proposition {
    VAR(polyopt::Variable),
    AND(And),
    OR(Or)
}
impl Clone for Proposition {
    fn clone(&self) -> Self {
        return match self {
            Proposition::VAR(x) => Proposition::VAR(x.clone()),
            Proposition::AND(x) => Proposition::AND(x.clone()),
            Proposition::OR(x) => Proposition::OR(x.clone()),
        }
    }
}
impl PropositionTrait for Proposition {
    fn variable(&self) -> polyopt::Variable {
        match self {
            Proposition::VAR(x) => *x,
            Proposition::AND(x) => x.variable,
            Proposition::OR(x) => x.variable,
        }
    }
    fn to_statement(&self) -> theory::Statement {
        match self {
            Proposition::VAR(x) => theory::Statement { variable: *x, expression: None },
            Proposition::AND(x) => theory::Statement {
                variable: x.variable,
                expression: Some(
                    theory::AtLeast {
                        bias: -1 * (x.propositions.len() as i64),
                        ids: x.propositions.iter().map(|prop| prop.variable().id ).collect()
                    }
                )
            },
            Proposition::OR(x) => theory::Statement {
                variable: x.variable,
                expression: Some(
                    theory::AtLeast {
                        bias: -1,
                        ids: x.propositions.iter().map(|prop| prop.variable().id ).collect()
                    }
                )
            },
        }
    }
}

pub trait LogicConnector {
    fn to_theory(&self, theory_id: String) -> theory::Theory;
}

#[derive(Debug)]
pub struct And {
    pub variable: polyopt::Variable,
    pub propositions: Vec<Proposition>
}
impl Clone for And {
    fn clone(&self) -> Self {
        return And {
            variable: self.variable,
            propositions: self.propositions.clone(),
        }
    }
}
impl LogicConnector for And {
    fn to_theory(&self, theory_id: String) -> theory::Theory {
        let mut props: HashMap<u32, Proposition> = HashMap::new();
        let mut queue: Vec<Proposition> = self.propositions.clone();
        props.insert(self.variable.id, Proposition::AND( self.clone() ));
        while let Some(prop) = queue.pop() {
            if !props.contains_key(&prop.variable().id) {
                match prop {
                    Proposition::AND(x) => {
                        queue.append(&mut x.propositions.clone());
                        props.insert(x.variable.id, Proposition::AND(x.clone()));
                    },
                    Proposition::OR(x) => {
                        queue.append(&mut x.propositions.clone());
                        props.insert(x.variable.id, Proposition::OR(x.clone()));
                    },
                    Proposition::VAR(x) => {
                        props.insert(x.id, Proposition::VAR(x.clone()));
                    },
                }
            }
        }
        return Theory {
            id: theory_id,
            statements: props.iter().map(|x| x.1.to_statement()).collect(),
        }
    }
}

#[derive(Debug)]
pub struct Or {
    pub variable: polyopt::Variable,
    pub propositions: Vec<Proposition>
}
impl Clone for Or {
    fn clone(&self) -> Self {
        return Or {
            variable: self.variable,
            propositions: self.propositions.clone(),
        }
    }
}
impl LogicConnector for Or {
    fn to_theory(&self, theory_id: String) -> theory::Theory {
        let mut props: HashMap<u32, Proposition> = HashMap::new();
        let mut queue: Vec<Proposition> = self.propositions.clone();
        props.insert(self.variable.id, Proposition::OR( self.clone() ));
        while let Some(prop) = queue.pop() {
            if !props.contains_key(&prop.variable().id) {
                match prop {
                    Proposition::AND(x) => {
                        queue.append(&mut x.propositions.clone());
                        props.insert(x.variable.id, Proposition::AND(x.clone()));
                    },
                    Proposition::OR(x) => {
                        queue.append(&mut x.propositions.clone());
                        props.insert(x.variable.id, Proposition::OR(x.clone()));
                    },
                    Proposition::VAR(x) => {
                        props.insert(x.id, Proposition::VAR(x.clone()));
                    },
                }
            }
        }
        return Theory {
            id: theory_id,
            statements: props.iter().map(|x| x.1.to_statement()).collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_construct_and_or_propositions() {
        let proposition = And {
            variable: polyopt::Variable { id: 0, bounds: (0,1) },
            propositions: vec![
                Proposition::OR(
                    Or { 
                        variable: polyopt::Variable { id: 1, bounds: (0,1) }, 
                        propositions: vec![
                            Proposition::VAR(
                                polyopt::Variable { id: 3, bounds: (0,1) },
                            ),
                            Proposition::VAR(
                                polyopt::Variable { id: 4, bounds: (0,1) },
                            )
                        ] 
                    },
                ),
                Proposition::OR(
                    Or { 
                        variable: polyopt::Variable { id: 2, bounds: (0,1) }, 
                        propositions: vec![
                            Proposition::VAR(
                                polyopt::Variable { id: 5, bounds: (0,1) },
                            ),
                            Proposition::VAR(
                                polyopt::Variable { id: 6, bounds: (0,1) },
                            )
                        ] 
                    },
                ),
            ]
        };
        let theory = proposition.to_theory(String::from("myID"));
        let x = 1;

        
    }
}