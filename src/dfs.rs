use std::rc::Rc;
use std::cell::RefCell;
use std::ops::Deref;
use std::collections::HashMap;


/// (1) LETTER COMBINATIONS
///
/// Given a string containing digits from 2-9 inclusive, return all possible letter combinations
/// that the number could represent. Return the answer in any order.
///
/// A mapping of digit to letters (just like on the telephone buttons). Note that 1 does not map to any letters.
///
/// Examples:
/// ```
/// use algorithms::dfs::letter_combinations;
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
  pub fn new(val: i32, left: Node, right: Node) -> Node {
    Some(Rc::new(RefCell::new(TreeNode { val, left, right })))
  }
}


/// (2) VALID BINARY TREE
///
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
///
/// use algorithms::dfs::{TreeNode, is_valid_bst};
///
/// let node1 = TreeNode::new(1, None, None);
/// let node3 = TreeNode::new(3, None, None);
/// let node2 = TreeNode::new(2, node1, node3);
///
/// assert_eq!(true, is_valid_bst(node2));
///
/// let node1 = TreeNode::new(1, None, None);
/// let node3 = TreeNode::new(3, None, None);
/// let node6 = TreeNode::new(6, None, None);
/// let node4 = TreeNode::new(3, node3, node6);
/// let node5 = TreeNode::new(5, node1, node4);
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
/// (3) SYMETRIC TREE
///
/// Given the root of a binary tree, check whether it is a mirror of itself (i.e., symmetric around its center).
///
/// ```
/// use algorithms:: dfs::{TreeNode, is_symmetric};
///
/// use std::rc::Rc;
/// use std::cell::RefCell;
///
/// let node3 = TreeNode::new(3, None, None);
/// let node4 = TreeNode::new(4, None, None);
/// let node2_l = TreeNode::new(3, node3, node4);
/// let node3 = TreeNode::new(3, None, None);
/// let node4 = TreeNode::new(4, None, None);
/// let node2_r = TreeNode::new(3, node3, node4);
/// let node1 = TreeNode::new(1, node2_l, node2_r);
///
/// assert_eq!(false, is_symmetric(node1));
///
/// let node3 = TreeNode::new(3, None, None);
/// let node4 = TreeNode::new(4, None, None);
/// let node2_l = TreeNode::new(3, node3, node4);
/// let node3 = TreeNode::new(3, None, None);
/// let node4 = TreeNode::new(4, None, None);
/// let node2_r = TreeNode::new(3, node4, node3);
/// let node1 = TreeNode::new(1, node2_l, node2_r);
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

/// (4) MAX DEPTH OF BINARY SEARCH TREE
///
/// Given the root of a binary tree, return its maximum depth.
///
/// A binary tree's maximum depth is the number of nodes along the longest path from the root node down to the farthest leaf node.
///
/// ```
/// use std::rc::Rc;
/// use std::cell::RefCell;
///
/// use algorithms::dfs::{max_depth_bst, TreeNode};
///
/// let node9 = TreeNode::new(9, None, None);
/// let node15 = TreeNode::new(15, None, None);
/// let node7 = TreeNode::new(7, None, None);
/// let node20 = TreeNode::new(20, node15, node7);
/// let node3 = TreeNode::new(3, node9, node20);
///
/// assert_eq!(3, max_depth_bst(node3));
///
/// let node2 = TreeNode::new(20, None, None);
/// let node1 = TreeNode::new(3, None, node2);
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
/// Given an m x n 2D binary grid grid which represents a map of '1's (land) and '0's (water), return the number of islands.
///
/// An island is surrounded by water and is formed by connecting adjacent lands horizontally or vertically.
/// You may assume all four edges of the grid are all surrounded by water.
///
/// ```
/// use std::ops::DerefMut;
///
/// use algorithms::dfs::{num_islands};
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

/// (6) FLATTEN BINARY TREE
/// 
/// ```
/// use std::rc::Rc;
/// use std::cell::RefCell;
/// 
/// use algorithms::dfs::{flatten_binary_tree, TreeNode};
/// 
/// let node3 = TreeNode::new(3, None, None);
/// let node4 = TreeNode::new(4, None, None);
/// let node6 = TreeNode::new(6, None, None);
/// let node2 = TreeNode::new(2, node3, node4);
/// let node5 = TreeNode::new(5, None, node6);
/// let mut node1 = TreeNode::new(1, node2, node5);
///
/// flatten_binary_tree(&mut node1);
///
/// let mut  current = node1.clone();
/// let mut nodes: Vec<i32> = vec![];
///
/// while let Some(n) = current {
///     nodes.push(n.borrow().val);
///     current = n.borrow().right.clone();
/// }
///
/// assert_eq!(vec![1, 2, 3, 4, 5, 6], nodes);
/// ```
/// 
pub fn flatten_binary_tree(root: &mut Node) {
    fn dfs(node: Node, rest: Node) -> Node {
        match node {
            None => rest,
            Some(node) => {
                let mut node_mut = node.borrow_mut();
                node_mut.right = dfs(node_mut.right.take(), rest);
                node_mut.right = dfs(node_mut.left.take(), node_mut.right.take());
                Some(node.clone())
            }
        }
    }

    dfs(root.clone(), None);
}

/// (7) BUILD TREE FROM PREORDER & INORDER
///
/// ```
/// use algorithms::dfs::{TreeNode, build_tree};
///
/// let tree = build_tree(vec![3,9,20,15,7], vec![9,3,15,20,7]);
///
/// let node9 = TreeNode::new(9, None, None);
/// let node15 = TreeNode::new(15, None, None);
/// let node7 = TreeNode::new(7, None, None);
/// let node20 = TreeNode::new(20, node15, node7);
/// let root = TreeNode::new(3, node9, node20);
///
/// assert_eq!(root, tree);
///
/// ```
pub fn build_tree(preorder: Vec<i32>, inorder: Vec<i32>) -> Node {

    fn dfs(start: i32, end: i32, preorder: &[i32], map: &HashMap<i32, usize>, current: &mut usize) -> Node {
        if start > end {
            return None;
        }

        let val = preorder[*current];

        *current += 1;

        let i = map[&val] as i32;

        let node = TreeNode{
            val,
            left: dfs(start, i - 1, preorder, map, current),
            right: dfs(i + 1, end, preorder, map, current),
        };

        Some(Rc::new(RefCell::new(node)))
    }

    let mut map = HashMap::with_capacity(inorder.len());

    for i in 0..inorder.len() {
        map.insert(inorder[i],i);
    }

    dfs(0, preorder.len() as i32 - 1, preorder.deref(), &map, &mut 0)
}
