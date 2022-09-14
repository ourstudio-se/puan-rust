struct GeLineq {
    coeffs : Vec<i64>,
    bounds : Vec<(i64,i64)>,
    bias   : i64,
    index  : Vec<i64>
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

    fn merge_disj(&self, other: GeLineq) -> Option<GeLineq> {

        let mut new_coeffs : Vec<i64> = Vec::new();
        for i in 0..self.coeffs.len() {
            new_coeffs.push(self.coeffs[i] * other._eqmin() + other.bias);
        }
        
        if self._eqmin() == -1 {
            return Some(
                GeLineq {
                    coeffs: new_coeffs,
                    bounds: vec![(0,1)],
                    bias: 1,
                    index: vec![0,1,2]
                }
            );
        } else if other._eqmin() == -1 {

        }

        None
    }

}

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // fn it_works_0() {
    //     let result = add(2, 2);
    //     assert_eq!(result, 4);
    // }
}
