//! # Linalg functions
//! 
//! Handy tools from linear algebra
//! 

/// Data structure for matrix
#[derive(Debug)]
#[derive(Default)]
pub struct Matrix {
    /// `Vec` holding the values of the matrix. Note that `val.len()` must be equal to the product of `ncols` and `nrows`.
    pub val: Vec<f64>,
    /// Number of columns of the matrix
    pub ncols: usize,
    /// Number of rows of the matrix
    pub nrows: usize
}

impl Clone for Matrix {
    fn clone(&self) -> Self {
        return Matrix {
            val : self.val.to_vec(),
            ncols: self.ncols,
            nrows: self.nrows
        }
    }
}

impl PartialEq for Matrix {
    fn eq(&self, other: &Self) -> bool {
        (self.val == other.val) & (self.ncols == other.ncols) & (self.nrows == other.nrows)
    }
}

/// Creates an identity matrix based on the input size `n`
pub fn identity_matrix(n: usize) -> Matrix {
    let mut t: Vec<f64> = Vec::with_capacity(n*n);
    for r in 0..n {
        for i in 0..n {
            if r == i {
                t.push(1.);
            } else {
                t.push(0.);
            }
        }
    }
    Matrix { val: t, ncols: n, nrows: n}
}

/// Calculates the dot product between two matrices
pub fn dot(mat1: &Matrix, mat2: &Matrix) -> Matrix{
    if !(mat1.ncols == mat2.nrows){
        panic!("Dimensions does not match, cannot calculate the dot product between matrices of shapes ({},{}) and ({},{})", mat1.nrows, mat1.ncols, mat2.nrows, mat2.ncols);
    }
    let mut result: Vec<f64> = Vec::with_capacity(mat1.nrows*mat2.ncols);
    for i in 0..mat1.nrows {
        for j in 0..mat2.ncols {
            result.push(mat1.val[i*mat1.ncols..(i+1)*mat1.ncols].to_vec().iter().zip(mat2.val.iter().skip(j).step_by(mat2.ncols)).map(|(x, y)| x * y).sum());
        }
    }
    return Matrix {
        val: result,
        ncols: mat2.ncols,
        nrows: mat1.nrows
    }
}

/// Divides one matrix by another.
/// 
/// If the matrices have the same shape each element $a_{ij}$ in the numerator matrix is divided by the corresponding element $b_{ij}$ in the denominator matrix.
/// It is also possible to divide a matrix with another matrix with only one row, if they share the same number of columns. In this case, each row in the nominator matrix is
/// divided by the denominator matrix. 
/// 
/// # Example:
/// 
/// $$ \[ a \ b \] / \[ c \ d \] = \[a/c \ b/d \]$$
/// 
/// ```
/// use puanrs::linalg::Matrix;
/// use puanrs::linalg::divide;
/// // Divide 2x3 matrix with 2x3 matrix
/// let res = divide(
///     &Matrix{
///         val: vec![1., 1., 1., 1., 1., 1.],
///         ncols: 3,
///         nrows: 2},
///     &Matrix{
///         val: vec![1., 2., 3., -1., 1., 0.],
///         ncols: 3,
///         nrows: 2});
/// assert_eq!(format!("{res:#?}"),
/// "Matrix {
///     val: [
///         1.0,
///         0.5,
///         0.3333333333333333,
///         -1.0,
///         1.0,
///         1.7976931348623157e308,
///     ],
///     ncols: 3,
///     nrows: 2,
/// }")
/// ```
/// ```
/// use puanrs::linalg::Matrix;
/// use puanrs::linalg::divide;
/// // Divide 2x3 matrix with 1x3 matrix
/// let res = divide(
///     &Matrix{
///         val: vec![1., 1., 1., 6., 6., 6.],
///         ncols: 3,
///         nrows: 2},
///     &Matrix{
///         val: vec![1., 2., 3.],
///         ncols: 3,
///         nrows: 1});
/// assert_eq!(format!("{res:#?}"),
/// "Matrix {
///     val: [
///         1.0,
///         0.5,
///         0.3333333333333333,
///         6.0,
///         3.0,
///         2.0,
///     ],
///     ncols: 3,
///     nrows: 2,
/// }")
/// ```

pub fn divide(mat1: &Matrix, mat2: &Matrix) -> Matrix {
    if !(mat1.ncols == mat2.ncols && (mat1.nrows == mat2.nrows || mat2.nrows == 1)) {
        panic!("Dimensions does not match, cannot divide a matrix of shape ({},{}) with a matrix of shape ({},{})", mat1.nrows, mat1.ncols, mat2.nrows, mat2.ncols);
    }
    let mut result: Vec<f64> = Vec::with_capacity(mat1.ncols*mat1.nrows);
    for i in 0..mat1.nrows{
        for j in 0..mat1.ncols {
            if mat2.nrows > 1 && mat2.val[i*mat1.ncols+j] != 0.0 {
                result.push(mat1.val[i*mat1.ncols+j]/mat2.val[i*mat1.ncols+j]);
            } else if mat2.nrows == 1 && mat2.val[j] != 0.0 {
                result.push(mat1.val[i*mat1.ncols+j]/mat2.val[j]);
            } else {
                result.push(f64::MAX);
            }
        }
    }
    return Matrix { val: result, ncols: mat1.ncols, nrows: mat1.nrows }
}

/// Divides one matrix by another if the divisor is greater than zero, otherwise the value is set to `f64::MAX`. (See [divide])
/// 
/// 
/// # Example:
/// 
/// ```
/// use puanrs::linalg::Matrix;
/// use puanrs::linalg::ge_divide;
/// // Divide 2x3 matrix with 2x3 matrix
/// let res = ge_divide(
///     &Matrix{
///         val: vec![1., 1., 1., 1., 1., 1.],
///         ncols: 3,
///         nrows: 2},
///     &Matrix{
///         val: vec![1., 2., 3., -1., 1., 0.],
///         ncols: 3,
///         nrows: 2});
/// assert_eq!(format!("{res:#?}"),
/// "Matrix {
///     val: [
///         1.0,
///         0.5,
///         0.3333333333333333,
///         1.7976931348623157e308,
///         1.0,
///         1.7976931348623157e308,
///     ],
///     ncols: 3,
///     nrows: 2,
/// }")
/// ```
pub fn ge_divide(mat1: &Matrix, mat2: &Matrix) -> Matrix {
    if !(mat1.ncols == mat2.ncols && (mat1.nrows == mat2.nrows || mat2.nrows == 1)) {
        panic!("Dimensions does not match, cannot divide a matrix of shape ({},{}) with a matrix of shape ({},{})", mat1.nrows, mat1.ncols, mat2.nrows, mat2.ncols);
    }
    let mut result: Vec<f64> = Vec::with_capacity(mat1.ncols*mat1.nrows);
    for i in 0..mat1.nrows{
        for j in 0..mat1.ncols {
            if mat2.nrows > 1 && mat2.val[i*mat1.ncols+j] > 0.0 {
                result.push(mat1.val[i*mat1.ncols+j]/mat2.val[i*mat1.ncols+j]);
            } else if mat2.nrows == 1 && mat2.val[j] > 0.0 {
                result.push(mat1.val[i*mat1.ncols+j]/mat2.val[j]);
            } else {
                result.push(f64::MAX);
            }
        }
    }
    return Matrix { val: result, ncols: mat1.ncols, nrows: mat1.nrows }
}

/// Divides one matrix by another if the divisor is less than zero, otherwise the value is set to `f64::MAX`. (See [divide])
/// 
/// # Example:
/// 
/// ```
/// use puanrs::linalg::Matrix;
/// use puanrs::linalg::le_divide;
/// // Divide 2x3 matrix with 2x3 matrix
/// let res = le_divide(
///     &Matrix{
///         val: vec![1., 1., 1., -1., -1., -1.],
///         ncols: 3,
///         nrows: 2},
///     &Matrix{
///         val: vec![-1., -2., -3., 1., -1., 0.],
///         ncols: 3,
///         nrows: 2});
/// assert_eq!(format!("{res:#?}"),
/// "Matrix {
///     val: [
///         -1.0,
///         -0.5,
///         -0.3333333333333333,
///         1.7976931348623157e308,
///         1.0,
///         1.7976931348623157e308,
///     ],
///     ncols: 3,
///     nrows: 2,
/// }")
/// ```
pub fn le_divide(mat1: &Matrix, mat2: &Matrix) -> Matrix {
    if !(mat1.ncols == mat2.ncols && (mat1.nrows == mat2.nrows || mat2.nrows == 1)) {
        panic!("Dimensions does not match, cannot divide a matrix of shape ({},{}) with a matrix of shape ({},{})", mat1.nrows, mat1.ncols, mat2.nrows, mat2.ncols);
    }
    let mut result: Vec<f64> = Vec::with_capacity(mat1.ncols*mat1.nrows);
    for i in 0..mat1.nrows{
        for j in 0..mat1.ncols {
            if mat2.nrows > 1 && mat2.val[i*mat1.ncols+j] < 0.0 {
                result.push(mat1.val[i*mat1.ncols+j]/mat2.val[i*mat1.ncols+j]);
            } else if mat2.nrows == 1 && mat2.val[j] < 0.0 {
                result.push(mat1.val[i*mat1.ncols+j]/mat2.val[j]);
            } else {
                result.push(f64::MAX);
            }
        }
    }
    return Matrix { val: result, ncols: mat1.ncols, nrows: mat1.nrows }
}

/// Adds one matrix by another.
/// 
/// If the matrices have the same shape each element $a_{ij}$ in matrix 1 is added by the corresponding element $b_{ij}$ in matrix 2.
/// It is also possible to add a matrix with a singled rowed matrix, if they share the same number of columns. In this case, each row in matrix 1 is
/// added by matrix 2. 
/// 
/// # Example:
/// 
/// $$ \[ a \ b \] + \[ c \ d \] = \[a+c \ b+d \]$$
/// 
/// ```
/// use puanrs::linalg::Matrix;
/// use puanrs::linalg::add;
/// // Add a 2x3 matrix with a 2x3 matrix
/// let res = add(
///     &Matrix{
///         val: vec![1., 1., 1., 1., 1., 1.],
///         ncols: 3,
///         nrows: 2},
///     &Matrix{
///         val: vec![1., 2., 3., -1., 1., 0.],
///         ncols: 3,
///         nrows: 2});
/// assert_eq!(format!("{res:#?}"),
/// "Matrix {
///     val: [
///         2.0,
///         3.0,
///         4.0,
///         0.0,
///         2.0,
///         1.0,
///     ],
///     ncols: 3,
///     nrows: 2,
/// }")
/// ```
/// ```
/// use puanrs::linalg::Matrix;
/// use puanrs::linalg::add;
/// // Add a 2x3 matrix with a 1x3 matrix
/// let res = add(
///     &Matrix{
///         val: vec![1., 1., 1., 6., 6., 6.],
///         ncols: 3,
///         nrows: 2},
///     &Matrix{
///         val: vec![1., 2., 3.],
///         ncols: 3,
///         nrows: 1});
/// assert_eq!(format!("{res:#?}"),
/// "Matrix {
///     val: [
///         2.0,
///         3.0,
///         4.0,
///         7.0,
///         8.0,
///         9.0,
///     ],
///     ncols: 3,
///     nrows: 2,
/// }")
/// ```
pub fn add(mat1: &Matrix, mat2: &Matrix) -> Matrix {
    if !(mat1.ncols == mat2.ncols && (mat1.nrows == mat2.nrows || mat2.nrows == 1)) {
        panic!("Dimensions does not match, cannot add a matrix of shape ({},{}) with a matrix of shape ({},{})", mat1.nrows, mat1.ncols, mat2.nrows, mat2.ncols);
    }
    let mut result: Vec<f64> = Vec::with_capacity(mat1.ncols*mat1.nrows);
    for i in 0..mat1.nrows{
        for j in 0..mat1.ncols {
            if mat2.nrows > 1 {
                result.push(mat1.val[i*mat1.ncols+j]+mat2.val[i*mat1.ncols+j]);
            } else {
                result.push(mat1.val[i*mat1.ncols+j]+mat2.val[j]);
            } 
        }
    }
    return Matrix { val: result, ncols: mat1.ncols, nrows: mat1.nrows }
}

/// Subtracts one matrix by another.
/// 
/// If the matrices have the same shape each element $a_{ij}$ in matrix 1 is subtracted by the corresponding element $b_{ij}$ in matrix 2.
/// It is also possible to subtract a matrix with another matrix with only one row, if they share the same number of columns. In this case, each row in matrix 1 is
/// subtracted by matrix 2. 
/// 
/// # Example:
/// 
/// $$ \[ a \ b \] - \[ c \ d \] = \[a-c \ b-d \]$$
/// 
/// ```
/// use puanrs::linalg::Matrix;
/// use puanrs::linalg::subtract;
/// // Subtract a 2x3 matrix with a 2x3 matrix
/// let res = subtract(
///     &Matrix{
///         val: vec![1., 1., 1., 1., 1., 1.],
///         ncols: 3,
///         nrows: 2},
///     &Matrix{
///         val: vec![1., 2., 3., -1., 1., 0.],
///         ncols: 3,
///         nrows: 2});
/// assert_eq!(format!("{res:#?}"),
/// "Matrix {
///     val: [
///         0.0,
///         -1.0,
///         -2.0,
///         2.0,
///         0.0,
///         1.0,
///     ],
///     ncols: 3,
///     nrows: 2,
/// }")
/// ```
/// ```
/// use puanrs::linalg::Matrix;
/// use puanrs::linalg::subtract;
/// // Subtract a 2x3 matrix with a 1x3 matrix
/// let res = subtract(
///     &Matrix{
///         val: vec![1., 1., 1., 6., 6., 6.],
///         ncols: 3,
///         nrows: 2},
///     &Matrix{
///         val: vec![1., 2., 3.],
///         ncols: 3,
///         nrows: 1});
/// assert_eq!(format!("{res:#?}"),
/// "Matrix {
///     val: [
///         0.0,
///         -1.0,
///         -2.0,
///         5.0,
///         4.0,
///         3.0,
///     ],
///     ncols: 3,
///     nrows: 2,
/// }")
/// ```
pub fn subtract(mat1: &Matrix, mat2: &Matrix) -> Matrix {
    if !(mat1.ncols == mat2.ncols && (mat1.nrows == mat2.nrows || mat2.nrows == 1)) {
        panic!("Dimensions does not match, cannot subtract a matrix of shape ({},{}) with a matrix of shape ({},{})", mat1.nrows, mat1.ncols, mat2.nrows, mat2.ncols);
    }
    let mut result: Vec<f64> = Vec::with_capacity(mat1.ncols*mat1.nrows);
    for i in 0..mat1.nrows{
        for j in 0..mat1.ncols {
            if mat2.nrows > 1 {
                result.push(mat1.val[i*mat1.ncols+j]-mat2.val[i*mat1.ncols+j]);
            } else {
                result.push(mat1.val[i*mat1.ncols+j]-mat2.val[j]);
            } 
        }
    }
    return Matrix { val: result, ncols: mat1.ncols, nrows: mat1.nrows }
}

/// Transpose the input Matrix and returns the result as a new Matrix
/// 
/// # Example:
/// 
/// ```
/// use puanrs::linalg::Matrix;
/// use puanrs::linalg::transpose;
/// let res = transpose(&Matrix{val: vec![1., 2., 3., 4., 5., 6.], ncols: 3, nrows: 2});
/// assert_eq!(format!("{res:#?}"),
/// "Matrix {
///     val: [
///         1.0,
///         4.0,
///         2.0,
///         5.0,
///         3.0,
///         6.0,
///     ],
///     ncols: 2,
///     nrows: 3,
/// }")
/// ```

pub fn transpose(mat: &Matrix) -> Matrix{
    let mut result = Vec::with_capacity(mat.val.len());
    for i in 0..mat.ncols{
        for j in 0..mat.nrows{
            result.push(mat.val[j*mat.ncols + i])
        }
    }
    return Matrix{val: result, nrows: mat.ncols, ncols: mat.nrows}
}

/// Eliminates column coefficient `col` of row `dst_row` by Gauss elemination with row `src_row`.
pub fn gauss_elimination(mat: &Matrix, dst_row: usize, src_row: usize, col: usize) -> Matrix{
    if mat.val[src_row*mat.ncols+col] == 0.0 {
        panic!("Cannot perform Gauss elimination when 'col' coefficient in the 'src_row' is zero");
    }
    let corr = mat.val[dst_row*mat.ncols + col]/mat.val[src_row*mat.ncols+col];
    row_subtraction(mat, dst_row, src_row, Some(corr))
}

/// Adds `src_row` to `dst_row`. If multiplier is given the `src_row` is multiplied by this number before the addition.
pub fn row_addition(mat: &Matrix, dst_row: usize, src_row: usize, multiplier: Option<f64>) -> Matrix{
    let mul: f64;
    if multiplier.is_none() {
        mul = 1.0;
    } else {
        mul = multiplier.unwrap();
    }
    let mut tmp = Vec::with_capacity(mat.val.len());
    for i in 0..mat.val.len(){
        if i >= dst_row*mat.ncols && i < dst_row*mat.ncols+mat.ncols{
            tmp.push(mat.val[i]+mat.val[src_row*mat.ncols+i%mat.ncols]*mul);
        } else {
            tmp.push(mat.val[i]);
        }
    }
    return Matrix{val: tmp, ncols: mat.ncols, nrows: mat.nrows}
}

/// Subtracts `dst_row` with `src_row`. If multiplier is given the `src_row` is multiplied by this number before the subtraction.
pub fn row_subtraction(mat: &Matrix, dst_row: usize, src_row: usize, multiplier: Option<f64>) -> Matrix{
    let mul: f64;
    if multiplier.is_none() {
        mul = 1.0;
    } else {
        mul = multiplier.unwrap();
    }
    let mut tmp = Vec::with_capacity(mat.val.len());
    for i in 0..mat.val.len(){
        if i >= dst_row*mat.ncols && i < dst_row*mat.ncols+mat.ncols{
            tmp.push(mat.val[i]-mat.val[src_row*mat.ncols+i%mat.ncols]*mul);
        } else {
            tmp.push(mat.val[i]);
        }
    }
    return Matrix{val: tmp, ncols: mat.ncols, nrows: mat.nrows}
}

/// Returns a new Matrix with the coluns specified by `ind`. 
pub fn get_columns(mat: &Matrix, ind: &Vec<usize>) -> Matrix {
    let mut result: Vec<f64> = Vec::with_capacity(ind.len());
    for i in 0..mat.nrows {
        result.extend(ind.iter().map(|j| mat.val[i*mat.ncols+j]).collect::<Vec<f64>>());
    }
    return Matrix { val: result, ncols: ind.len(), nrows: mat.nrows }   
}

/// Returns a new Matrix with column `ind` replaced with `v`. 
pub fn update_column(mat: &Matrix, ind: usize, v: &Vec<f64>) -> Matrix{
    if mat.nrows != v.len() {
        panic!("Dimension does not match");
    }
    let mut result = mat.val.to_vec();
    for i in 0..v.len() {
        result[i*mat.ncols+ind] = v[i];
    }
    Matrix { val: result, ncols: mat.ncols, nrows: mat.nrows}
}

impl Matrix {
    /// See [dot]
    pub fn dot(&self, mat2: &Matrix) -> Matrix{
        dot(self, mat2)
    }
    /// See [ge_divide]
    pub fn ge_divide(&self, mat2: &Matrix) -> Matrix {
        ge_divide(self, mat2)
    }
    /// See [le_divide]
    pub fn le_divide(&self, mat2: &Matrix) -> Matrix {
        le_divide(self, mat2)
    }
    /// See [divide]
    pub fn divide(&self, mat2: &Matrix) -> Matrix {
        divide(self, mat2)
    }
    /// See [subtract]
    pub fn subtract(&self, mat2: &Matrix) -> Matrix {
        subtract(self, mat2)
    }
    /// See [transpose]
    pub fn transpose(&self) -> Matrix{
        transpose(self)
    }
    pub fn insert_column(&self, column: usize, elem: Vec<f64>) -> Matrix {
    if column > self.ncols {
        panic!("Cannot insert column at {} to matrix with dimensions {}, {}", column, self.nrows, self.ncols);
    }
    let mut result = Vec::new();
    let mut j = 0;
    for (i, e) in self.val.iter().enumerate() {
        if (i + self.ncols - column) > 0 && (i + self.ncols - column) % self.ncols == 0 {
            result.push(elem[j].clone());
            j = j + 1;
        }
        result.push(e.clone());
    }
    if (j + 1) == elem.len() {
        result.push(elem[j])
    }
    return Matrix { val: result, ncols: self.ncols+1, nrows: self.nrows }
    }
    pub fn gauss_elimination(&self, row: usize, by: usize, col: usize) -> Matrix{
        gauss_elimination(self, row, by, col)
    }

    pub fn row_addition(&self, dst_row: usize, src_row: usize, multiplier: Option<f64>) -> Matrix{
        row_addition(self, dst_row, src_row, multiplier)
    }

    pub fn get_columns(&self, ind: &Vec<usize>) -> Matrix {
        get_columns(self, ind)
    }

    pub fn update_column(&self, ind: usize, v: &Vec<f64>) -> Matrix{
        update_column(self, ind, v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_dot_product() {
        let m1 = Matrix {
            val: vec![1.0,2.0,3.0,4.0,5.0,6.0],
            ncols: 2,
            nrows: 3,
        };
        let m2 = Matrix {
            val: vec![7.0,8.0,9.0,10.0],
            ncols: 2,
            nrows: 2,
        };
        assert_eq!(m1.dot(&m2).val, Matrix{val: vec![25.0, 28.0, 57.0, 64.0, 89.0, 100.0], ncols: 2, nrows: 3}.val);

    }

}