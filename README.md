# Puan
Defining logic relationships among linear inequalities and has effective reduction algorithms.

# Example

Here defining a relation between id 0, 1 and 2 saying that value of id 0 is dependent on value on id 1 and 2.

```rust
use puanrs::Theory;
use puanrs::Statement;
use puanrs::AtLeast;
use puanrs::Variable;
use puanrs::GeLineq;

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
                    bias   : -1,
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
                bounds  : (0,1),
            },
            expression  : None
        },
    ]
};

let actual: Vec<GeLineq> = theory.to_lineqs();
assert_eq!(actual.len(), 1);
assert_eq!(actual[0].bias, 0);
assert_eq!(actual[0].coeffs, vec![-1,1,1]);
assert_eq!(actual[0].indices, vec![0,1,2]);
```
If `A=0, x=1, y=2` (with 0, 1, 2 here being variable id's), we could express above as `A=x+y>=1`.