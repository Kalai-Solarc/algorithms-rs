use std::iter::FromIterator;
use std::ops::Deref;


/// LETTER COMBINATIONS
///
/// Given a string containing digits from 2-9 inclusive, return all possible letter combinations
/// that the number could represent. Return the answer in any order.
///
/// A mapping of digit to letters (just like on the telephone buttons). Note that 1 does not map to any letters.
///
/// Examples:
/// ```
/// use algorithms::backtrack::letter_combinations;
///
/// assert_eq!(Vec::<String>::new(), letter_combinations(""));
/// assert_eq!(vec!["a", "b", "c"], letter_combinations("2"));
/// assert_eq!(vec!["ad", "ae", "af", "bd", "be", "bf", "cd", "ce", "cf"], letter_combinations("23"));
/// ```
///
pub fn letter_combinations(digits: &str) -> Vec<String> {
    let mut results = vec![];

    if digits.is_empty() {
        return results;
    }

    let pad = [
        "", "", "abc", "def", "ghi", "jkl", "mno", "pqrs", "tuv", "wxyz",
    ];

    let digits = digits.as_bytes();

    fn dfs(digits: &[u8], buf: &mut String, index: usize, pad: &[&str], results: &mut Vec<String>) {
        if digits.len() == index {
            results.push(buf.to_owned());
            return;
        }

        let lookup = (digits[index] - b'0') as usize;

        for letter in pad[lookup].chars() {
            buf.push(letter);
            dfs(digits, buf, index + 1, pad, results);
            buf.pop();
        }
    }

    dfs(digits.as_ref(), &mut "".to_string(), 0, &pad, results.as_mut());

    results
}


/// N QUEENS
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

/// PALINDROME PARTITIONING
/// ```
/// use algorithms::backtrack::partition;
///
/// assert_eq!(vec![vec!["a","a","b"],vec!["aa","b"]], partition("aab".to_string()));
/// assert_eq!(vec![vec!["a"]], partition("a".to_string()));
/// ```
pub fn partition(st: String) -> Vec<Vec<String>> {
    fn dfs(index: usize, st: &str, path: &mut Vec<String>, result: &mut Vec<Vec<String>>) {
        if index == st.len() {
            result.push(path.clone());
            return;
        }

        let chars: Vec<char> = st.chars().collect();

        for i in index..st.len() {
            if is_palindrome(chars.deref(), index, i) {
                path.push(st[index..(i + 1)].to_string());
                dfs(i + 1, st, path, result);
                path.pop();
            }
        }
    }

    fn is_palindrome(chars: &[char], mut start: usize, mut end: usize) -> bool {
        while start < end {
            if chars[start] != chars[end] {
                return false;
            }
            start += 1;
            end -= 1;
        }
        true
    }

    let mut result = vec![];
    dfs(0, &st, &mut vec![], &mut result);
    result
}

/// (3) GENERATE PARENTHESIS
/// ```
/// use algorithms::backtrack::generate_parenthesis;
///
/// assert_eq!(vec!["((()))", "(()())", "(())()", "()(())", "()()()"], generate_parenthesis(3));
/// assert_eq!(vec!["()"], generate_parenthesis(1));
/// ```
pub fn generate_parenthesis(n: i32) -> Vec<String> {
    fn dfs(open: i32, close: i32, str: &mut String, n: i32, result: &mut Vec<String>) {
        if close > open || open > n {
            return;
        }

        if open == close && open == n {
            result.push(str.to_owned());
        }

        str.push_str("(");
        dfs(open + 1, close, str, n, result);
        str.pop();

        str.push_str(")");
        dfs(open, close + 1, str, n, result);
        str.pop();
    }

    let mut result = vec![];
    dfs(0, 0, &mut "".to_string(), n, &mut result);
    result
}
