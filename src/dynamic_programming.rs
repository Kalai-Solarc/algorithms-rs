/// LONGEST INCREASING PATH IN A MATRIX
///
/// ```
/// use algorithms::dynamic_programming::longest_increasing_path;
///
/// assert_eq!(4,
///     longest_increasing_path(
///         vec![
///             vec![9, 9, 4],
///             vec![6, 6, 8],
///             vec![2, 1, 1],
///         ]
///     )
/// );
/// assert_eq!(4,
///     longest_increasing_path(
///         vec![
///             vec![3, 4, 5],
///             vec![3, 2, 6],
///             vec![2, 2, 1],
///         ]
///     )
/// );
/// ```
pub fn longest_increasing_path(matrix: Vec<Vec<i32>>) -> i32 {
    fn dfs(
        matrix: &Vec<Vec<i32>>,
        cache: &mut Vec<Vec<Option<i32>>>,
        m: usize,
        n: usize,
        r: usize,
        c: usize,
    ) -> i32 {
        if let Some(cached) = cache[r][c] {
            return cached;
        }

        let current = matrix[r][c];

        let mut result = 0;

        if r > 0 && matrix[r - 1][c] > current {
            result = result.max(dfs(matrix, cache, m, n, r - 1, c));
        }

        if r < m && matrix[r + 1][c] > current {
            result = result.max(dfs(matrix, cache, m, n, r + 1, c));
        }

        if c > 0 && matrix[r][c - 1] > current {
            result = result.max(dfs(matrix, cache, m, n, r, c - 1));
        }

        if c < n && matrix[r][c + 1] > current {
            result = result.max(dfs(matrix, cache, m, n, r, c + 1));
        }

        result += 1;

        cache[r][c] = Some(result);

        result
    }

    let mut result = 0;

    if matrix.is_empty() {
        return result;
    }

    let row_len = matrix.len();
    let col_len = matrix[0].len();
    let mut cache = vec![vec![None; col_len]; row_len];
    let m = row_len - 1;
    let n = col_len - 1;

    for r in 0..row_len {
        for c in 0..col_len {
            result = result.max(dfs(&matrix, &mut cache, m, n, r, c));
        }
    }

    result
}
