use std::iter::FromIterator;

/// (1) N QUEENS
///
/// ```
/// use algorithms::backtrack::solve_n_queens;
///
/// assert_eq!(
///     vec![
///         vec!["..Q.", "Q...", "...Q", ".Q.."],
///         vec![".Q..", "...Q", "Q...", "..Q."]
///     ],
///     solve_n_queens(4)
/// )
/// ```
pub fn solve_n_queens(n: usize) -> Vec<Vec<String>> {
    let mut board = vec![vec!['.'; n]; n];
    let mut result = vec![];

    fn dfs(board: &mut Vec<Vec<char>>, column: usize, result: &mut Vec<Vec<String>>) {
        if column == board.len() {
            result.push(build(board));
            return;
        }

        for row in 0..board.len() {
            if validate(board, row, column) {
                board[row][column] = 'Q';
                dfs(board, column + 1, result);
                board[row][column] = '.';
            }
        }
    }

    fn validate(board: &mut Vec<Vec<char>>, row: usize, column: usize) -> bool {
        for i in 0..board.len() {
            for j in 0..column {
                if board[i][j] == 'Q'
                    && (row + j == column + i || row + column == i + j || row == i)
                {
                    return false;
                }
            }
        }

        true
    }

    #[inline]
    fn build(board: &mut Vec<Vec<char>>) -> Vec<String> {
        board
            .iter()
            .map(|row| String::from_iter(row.iter()))
            .collect()
    }

    dfs(&mut board, 0, &mut result);

    result
}
