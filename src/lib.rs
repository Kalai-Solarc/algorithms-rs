use std::rc::Rc;
use std::cell::RefCell;

///
/// (1) LETTER COMBINATIONS
///
/// Given a string containing digits from 2-9 inclusive, return all possible letter combinations
/// that the number could represent. Return the answer in any order.
///
/// A mapping of digit to letters (just like on the telephone buttons). Note that 1 does not map to any letters.
///
/// Examples:
/// ```
/// use dfs::letter_combinations;
///
/// assert_eq!(Vec::<String>::new(), letter_combinations(""));
/// assert_eq!(vec!["a", "b", "c"], letter_combinations("2"));
/// assert_eq!(vec!["ad", "ae", "af", "bd", "be", "bf", "cd", "ce", "cf"], letter_combinations("23"));
/// ```
///
pub fn letter_combinations(digits: &str) -> Vec<String> {
    let mut results = vec![];

    if digits.is_empty() {
        return results
    }

    let pad= ["", "", "abc", "def", "ghi", "jkl", "mno", "pqrs", "tuv", "wxyz"];

    let digits = digits.as_bytes();

    fn dfs(digits: &[u8], temp: String, index: usize, pad: &[&str], results: &mut Vec<String>) {
        if digits.len() == index {
            results.push(temp);
            return;
        }

        let lookup = (digits[index] - b'0') as usize;

        for letter in pad[lookup].chars() {
            let mut buf = String::with_capacity(temp.len() + 1);
            buf.push_str(&temp);
            buf.push(letter);
            dfs(digits, buf, index + 1, pad, results)
        }
    }

    dfs(digits.as_ref(), "".to_string(), 0, &pad, results.as_mut());

    results
}


#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
  pub val: i32,
  pub left: Node,
  pub right: Node,
}

type Node = Option<Rc<RefCell<TreeNode>>>;

impl TreeNode {
  #[inline]
  pub fn new(val: i32) -> Self {
    TreeNode {
      val,
      left: None,
      right: None
    }
  }
}

///
/// (2) BALANCED BINARY TREE
/// Given the root of a binary tree, determine if it is a valid binary search tree (BST).
///
/// A valid BST is defined as follows:
///
/// The left subtree of a node contains only nodes with keys less than the node's key.
/// The right subtree of a node contains only nodes with keys greater than the node's key.
/// Both the left and right subtrees must also be binary search trees.
/// ```
/// use std::rc::Rc;
/// use std::cell::RefCell;
/// use dfs::{TreeNode, is_valid_bst};
///
/// let node1 = Some(Rc::new(RefCell::new(TreeNode{ val: 1, left: None, right: None })));
/// let node3 = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: None, right: None })));
/// let node2 = Some(Rc::new(RefCell::new(TreeNode{ val: 2, left: node1, right: node3 })));
///
/// assert_eq!(true, is_valid_bst(node2));
///
/// let node1 = Some(Rc::new(RefCell::new(TreeNode{ val: 1, left: None, right: None })));
/// let node3 = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: None, right: None })));
/// let node6 = Some(Rc::new(RefCell::new(TreeNode{ val: 6, left: None, right: None })));
/// let node4 = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: node3, right: node6 })));
/// let node5 = Some(Rc::new(RefCell::new(TreeNode{ val: 5, left: node1, right: node4 })));
///
/// assert_eq!(false, is_valid_bst(node5));
/// ```
///
pub fn is_valid_bst(root: Node) -> bool {
    fn dfs(node: Node, lower: Node, upper: Node) -> bool {
        match node.clone() {
            Some(n) => {
                if let Some(lower) = lower.clone() {
                    if !(lower.borrow().val < n.borrow().val) {
                        return false
                    }
                }

                if let Some(upper) = upper.clone() {
                    if !(upper.borrow().val > n.borrow().val) {
                        return false
                    }
                }

                dfs(n.borrow().left.clone(), lower, node.clone())
                    && dfs(n.borrow().right.clone(), node.clone(), upper)
            }

            None => true
        }
    }

    dfs(root.clone(), None, None)
}
///
/// ```
/// use dfs::{TreeNode, is_symmetric};
/// use std::rc::Rc;
/// use std::cell::RefCell;
///
/// let node3 = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: None, right: None })));
/// let node4 = Some(Rc::new(RefCell::new(TreeNode{ val: 4, left: None, right: None })));
/// let node2_l = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: node3, right: node4 })));
/// let node3 = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: None, right: None })));
/// let node4 = Some(Rc::new(RefCell::new(TreeNode{ val: 4, left: None, right: None })));
/// let node2_r = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: node3, right: node4 })));
/// let node1 = Some(Rc::new(RefCell::new(TreeNode{ val: 1, left: node2_l, right: node2_r })));
///
/// assert_eq!(false, is_symmetric(node1));
///
/// let node3 = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: None, right: None })));
/// let node4 = Some(Rc::new(RefCell::new(TreeNode{ val: 4, left: None, right: None })));
/// let node2_l = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: node3, right: node4 })));
/// let node3 = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: None, right: None })));
/// let node4 = Some(Rc::new(RefCell::new(TreeNode{ val: 4, left: None, right: None })));
/// let node2_r = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: node4, right: node3 })));
/// let node1 = Some(Rc::new(RefCell::new(TreeNode{ val: 1, left: node2_l, right: node2_r })));
///
/// assert_eq!(true, is_symmetric(node1));
/// ```
/// 
pub fn is_symmetric(root: Option<Rc<RefCell<TreeNode>>>) -> bool {
    fn dfs(node1: Node, node2: Node) -> bool {
        match (node1, node2) {
            (None, None) => true,
            (Some(_), None) | (None, Some(_)) => false,
            (Some(node1), Some(node2)) => {
                node1.borrow().val == node2.borrow().val
                    && dfs(node1.borrow().left.clone(), node2.borrow().right.clone())
                    && dfs(node1.borrow().right.clone(), node2.borrow().left.clone())
            }
        }
    }

    dfs(root.clone(), root.clone())
}

///
/// ```
/// use std::rc::Rc;
/// use std::cell::RefCell;
///
/// use dfs::{max_depth_bst, TreeNode};
///
/// let node9 = Some(Rc::new(RefCell::new(TreeNode{ val: 9, left: None, right: None })));
/// let node15 = Some(Rc::new(RefCell::new(TreeNode{ val: 15, left: None, right: None })));
/// let node7 = Some(Rc::new(RefCell::new(TreeNode{ val: 7, left: None, right: None })));
/// let node20 = Some(Rc::new(RefCell::new(TreeNode{ val: 20, left: node15, right: node7 })));
/// let node3 = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: node9, right: node20 })));
///
/// assert_eq!(3, max_depth_bst(node3));
///
/// let node2 = Some(Rc::new(RefCell::new(TreeNode{ val: 20, left: None, right: None })));
/// let node1 = Some(Rc::new(RefCell::new(TreeNode{ val: 3, left: None, right: node2 })));
///
/// assert_eq!(2, max_depth_bst(node1));
///
/// assert_eq!(0, max_depth_bst(None));
/// ```
/// 
pub fn max_depth_bst(root: Option<Rc<RefCell<TreeNode>>>) -> i32 {
    match root {
        None => 0,
        Some(node) => {
            1 + i32::max(max_depth_bst(node.borrow().left.clone()),
                         max_depth_bst(node.borrow().right.clone()))
        },
    }
}

/// (5) NUMBER OF ISLANDS
/// 
/// ```
/// use std::ops::DerefMut;
///
/// use dfs::{num_islands};
///
/// let mut grid = vec![
///     vec!['1', '1', '1', '1', '0'],
///     vec!['1', '1', '0', '1', '0'],
///     vec!['1', '1', '0', '0', '0'],
///     vec!['0', '0', '0', '0', '0']
/// ];
///
/// let mut grid =
///     grid
///         .iter_mut()
///         .map(|v| v.deref_mut())
///         .collect::<Vec<&mut [char]>>();
///
/// assert_eq!(1, num_islands(grid.deref_mut()));
/// 
/// let mut  grid = vec![
///     vec!['1','1','0','0','0'],
///     vec!['1','1','0','0','0'],
///     vec!['0','0','1','0','0'],
///     vec!['0','0','0','1','1']
/// ];
///
/// let mut grid =
///     grid
///         .iter_mut()
///         .map(|v| v.deref_mut())
///         .collect::<Vec<&mut [char]>>();
///
/// assert_eq!(3, num_islands(grid.deref_mut()));
/// ```
/// 
pub fn num_islands(grid: &mut [&mut [char]]) -> i32 {
    let mut count = 0;

    for row in 0..grid.len() {
        for column in 0..grid[row].len() {
            if grid[row][column] == '1' {
                count += 1;
                dfs(row, column, grid);
            }
        }
    }

    fn dfs(row: usize, column: usize, grid: &mut [&mut [char]]) {
        if grid[row][column] != '1' {
            return;
        }

        grid[row][column] = '0';

        if column < grid[row].len() - 1 {
            dfs(row, column + 1, grid);
        }

        if column > 0 {
            dfs(row, column - 1, grid);
        }

        if row < grid.len() - 1 {
            dfs(row + 1, column, grid);
        }

        if row > 0 {
            dfs(row - 1, column, grid);
        }
    }

    count as i32
}


#[cfg(test)]
mod test {

    #[test]
    fn it_works() {
    }
}