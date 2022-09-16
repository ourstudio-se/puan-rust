use core::num;
use itertools::iproduct;
use std::cmp;

struct GeLineq {
    coeffs : Vec<i64>,
    bounds : Vec<(i64, i64)>,
    bias   : i64,
    index  : Vec<u32>
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
                if self.index[j] == variables[i].0 {
                    res = res + self.coeffs[j]*variables[i].1;
                }
            }
        }
        return res + self.bias >= 0;
    }

    pub fn merge_disj(GeLineq1: &GeLineq, GeLineq2: &GeLineq) -> Option<GeLineq> {
        
        if GeLineq1._eqmin() + GeLineq1.bias == -1 {
            let mut equal_indices : Vec<(usize, usize)> = Vec::new();
            for i in 0..GeLineq1.index.len(){
                for j in 0..GeLineq2.index.len(){
                    if GeLineq1.index[i]==GeLineq2.index[j] {
                        equal_indices.push((i, j));
                    }
                }
            }
            let n: usize = GeLineq1.coeffs.len() + GeLineq2.coeffs.len() - equal_indices.len();
            let mut new_coeffs : Vec<i64> = Vec::with_capacity(n);
            let mut equal_index_pointer: usize = 0;
            let mut corrector: i64 = 0;
            let mut new_bounds : Vec<(i64, i64)> = Vec::with_capacity(n);
            let mut new_index : Vec<u32> = Vec::with_capacity(n);
            
            for i in 0..GeLineq1.coeffs.len() {
                if equal_index_pointer < equal_indices.len() && equal_indices[equal_index_pointer].0 == i {
                    corrector = GeLineq2.coeffs[equal_indices[equal_index_pointer].1];
                    equal_index_pointer = equal_index_pointer + 1;
                }
                new_coeffs.push(-GeLineq1.coeffs[i]*(GeLineq2._eqmin() + GeLineq2.bias) + corrector);
                new_index.push(GeLineq1.index[i]);
                new_bounds.push(GeLineq1.bounds[i]);
                corrector = 0;
            }
            let mut skip_equal_index = 0;
            for i in 0..GeLineq2.coeffs.len(){
                for j in 0..equal_indices.len(){
                    if equal_indices[j].1 == i {
                        equal_indices.remove(j);
                        skip_equal_index = 1;
                        break;
                    }
                }
                if skip_equal_index < 1 {
                    new_coeffs.push(GeLineq2.coeffs[i]);
                    new_index.push(GeLineq2.index[i]);
                    new_bounds.push(GeLineq2.bounds[i]);
                }
                skip_equal_index = 0;
            }
            return Some(
                GeLineq {
                    coeffs: new_coeffs,
                    bounds: new_bounds,
                    bias: GeLineq1._eqmin()*(GeLineq2._eqmin() + GeLineq2.bias)+GeLineq2.bias,
                    index: new_index
                }
            );  
        } else if GeLineq2._eqmin() + GeLineq2.bias == -1 {
            return GeLineq::merge_disj(GeLineq2, GeLineq1);
        }
    
        None
        
    }

    pub fn merge_conj(GeLineq1: &GeLineq, GeLineq2: &GeLineq) -> Option<GeLineq> {
    
        if GeLineq1._eqmax() + GeLineq1.bias == 0 {
            let mut equal_indices : Vec<(usize, usize)> = Vec::new();
            for i in 0..GeLineq1.index.len(){
                for j in 0..GeLineq2.index.len(){
                    if GeLineq1.index[i]==GeLineq2.index[j] {
                        equal_indices.push((i, j));
                    }
                }
            }
            let n: usize = GeLineq1.coeffs.len() + GeLineq2.coeffs.len() - equal_indices.len();
            let mut new_coeffs : Vec<i64> = Vec::with_capacity(n);
            let mut equal_index_pointer: usize = 0;
            let mut corrector: i64 = 0;
            let mut new_bounds : Vec<(i64, i64)> = Vec::with_capacity(n);
            let mut new_index : Vec<u32> = Vec::with_capacity(n);
            
            for i in 0..GeLineq1.coeffs.len() {
                if equal_index_pointer < equal_indices.len() && equal_indices[equal_index_pointer].0 == i {
                    corrector = GeLineq2.coeffs[equal_indices[equal_index_pointer].1];
                    equal_index_pointer = equal_index_pointer + 1;
                }
                new_coeffs.push(GeLineq1.coeffs[i]*(cmp::max(GeLineq2._eqmax().abs(), GeLineq2._eqmin().abs())+1) + corrector);
                new_index.push(GeLineq1.index[i]);
                new_bounds.push(GeLineq1.bounds[i]);
                corrector = 0;
            }
            let mut skip_equal_index = 0;
            for i in 0..GeLineq2.coeffs.len(){
                for j in 0..equal_indices.len(){
                    if equal_indices[j].1 == i {
                        equal_indices.remove(j);
                        skip_equal_index = 1;
                        break;
                    }
                }
                if skip_equal_index < 1 {
                    new_coeffs.push(GeLineq2.coeffs[i]);
                    new_index.push(GeLineq2.index[i]);
                    new_bounds.push(GeLineq2.bounds[i]);
                }
                skip_equal_index = 0;
            }
            return Some(
                GeLineq {
                    coeffs: new_coeffs,
                    bounds: new_bounds,
                    bias: GeLineq1.bias*(cmp::max(GeLineq2._eqmax().abs(), GeLineq2._eqmin().abs())+1) + GeLineq2.bias - cmp::max(GeLineq2._eqmin() + GeLineq2.bias, 0),
                    index: new_index
                }
            );  
        } else if GeLineq2._eqmax() + GeLineq2.bias == 0 {
            return GeLineq::merge_conj(&GeLineq2, &GeLineq1);
        }
    
        None
        
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_logic(){
        // Disjunction merge between 1-1
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -1,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1],
            bounds : vec![(0, 1), (0, 1)],
            bias   : -1,
            index  : vec![1, 6]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l) in iproduct!(0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(6,l)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(6,l)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(6,l)]));

        }
        // Disjunction merge between 2-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 0,
            index  : vec![1, 2, 3, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l) in iproduct!(0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(8,l)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(8,l)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(8,l)]));

        }
        // Disjunction merge between 1-1
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -1,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1],
            bounds : vec![(0, 1), (0, 1)],
            bias   : 0,
            index  : vec![5, 6]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m)]));

        }
        // Disjunction merge between 1-2
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -1,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 3,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 1-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -1,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 0,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 1-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -1,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -4,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 1-5
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -1,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -2,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 1-6
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -1,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 2-2
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 3,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 2-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 0,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 2-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -4,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 2-5
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -2,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Disjunction merge between 2-6
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k, l, m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7, n), (8, o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l),(6,m), (7, n), (8, o)]));

        }
        // Conjunction merge between 4-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -3,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -3,
            index  : vec![1, 0, 4]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(4,l), (0,m)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(4,l), (0,m)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(4,l), (0,m)]));
            
        }
        // Conjunction merge between 4-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -3,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 0,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
            
        }
        // Conjunction merge between 1-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -1,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -4,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
            
        }
        // Conjunction merge between 2-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 0,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 2-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -4,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 3-3
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 0,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 0,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 3-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 0,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -4,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 3-5
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 0,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -2,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));

        }
        // Conjunction merge between 3-6
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 0,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 4-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -3,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -4,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 4-5
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -3,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -2,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 4-6
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : -3,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![-1, -1, -1, -1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : 2,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge between 4-4
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1)],
            bias   : 3,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -4,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(0..2, 0..2, 0..2, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Disjunction merge, special case
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(-2, -1), (2, 3), (2, 3)],
            bias   : -3,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -1,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_disj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(-2..0, 2..4, 2..4, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) || gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
        // Conjunction merge, special case
        let ge_lineq1:GeLineq = GeLineq {
            coeffs : vec![1, 1, 1],
            bounds : vec![(-2, -1), (2, 3), (2, 3)],
            bias   : -5,
            index  : vec![1, 2, 3]
        };
        let gelineq2: GeLineq = GeLineq {
            coeffs : vec![1, 1, 1, 1],
            bounds : vec![(0, 1), (0, 1), (0, 1), (0, 1)],
            bias   : -1,
            index  : vec![5, 6, 7, 8]
        };
        let result = GeLineq::merge_conj(&ge_lineq1, &gelineq2);
        for (i,j,k,l,m, n, o) in iproduct!(-2..0, 2..4, 2..4, 0..2, 0..2, 0..2, 0..2){
            assert_eq!((ge_lineq1.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]) && gelineq2.satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)])), result.as_ref().expect("No result generated").satisfied(vec![(1, i), (2, j),(3,k),(5,l), (6,m), (7,n), (8,o)]));
        }
    }

    // #[test]
    // fn it_works_0() {
    //     let constr1: GeLineq = GeLineq {
    //         coeffs : vec![1,1,1,1,1],
    //         bounds : vec![(0,1),(0,1),(0,1),(0,1),(0,1)],
    //         bias : -1,
    //         index: vec![1,2,3,4,5]
    //     };
    //     let constr2: GeLineq = GeLineq {
    //         coeffs : vec![1,1,1,1,1],
    //         bounds : vec![(0,1),(0,1),(0,1),(0,1),(0,1)],
    //         bias : -5,
    //         index: vec![1,2,3,4,5]
    //     };
    //     let result = GeLineq::merge_disj(&constr1, &constr2);
    //     //assert_eq!(constr1._eqmin(), -1);
    //     assert_eq!(result.expect("None returned from merge disj").bias, 2);
    // }
}
