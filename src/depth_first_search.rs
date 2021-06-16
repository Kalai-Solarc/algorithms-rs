use std::rc::Rc;
use std::cell::RefCell;
use std::ops::{Deref};
use std::collections::HashMap;


use crate::model::{TreeNode, TreeNodeRef};

/// (1) LETTER COMBINATIONS
///
/// Given a string containing digits from 2-9 inclusive, return all possible letter combinations
/// that the number could represent. Return the answer in any order.
///
/// A mapping of digit to letters (just like on the telephone buttons). Note that 1 does not map to any letters.
///
/// Examples:
/// ```
/// use algorithms::depth_first_search::letter_combinations;
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
/// use algorithms::depth_first_search::is_valid_bst;
/// use algorithms::model::TreeNode;
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
pub fn is_valid_bst(root: TreeNodeRef) -> bool {
    fn dfs(node: TreeNodeRef, lower: TreeNodeRef, upper: TreeNodeRef) -> bool {
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
/// use algorithms::depth_first_search::is_symmetric;
/// use algorithms::model::TreeNode;
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
    fn dfs(node1: TreeNodeRef, node2: TreeNodeRef) -> bool {
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
/// use algorithms::depth_first_search::max_depth_bst;
/// use algorithms::model::TreeNode;
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
/// use algorithms::depth_first_search::num_islands;
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
/// use algorithms::depth_first_search::flatten_binary_tree;
/// use algorithms::model::TreeNode;
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
pub fn flatten_binary_tree(root: &mut TreeNodeRef) {
    fn dfs(node: TreeNodeRef, rest: TreeNodeRef) -> TreeNodeRef {
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
/// use algorithms::depth_first_search::build_tree;
/// use algorithms::model::TreeNode;
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
pub fn build_tree(preorder: Vec<i32>, inorder: Vec<i32>) -> TreeNodeRef {

    fn dfs(start: i32, end: i32, preorder: &[i32], map: &HashMap<i32, usize>, current: &mut usize) -> TreeNodeRef {
        if start > end {
            return None;
        }

        let val = preorder[*current];
        let mid = map[&val] as i32;
        *current += 1;

        let node = TreeNode{
            val,
            left: dfs(start, mid - 1, preorder, map, current),
            right: dfs(mid + 1, end, preorder, map, current),
        };

        Some(Rc::new(RefCell::new(node)))
    }

    let mut map = HashMap::with_capacity(inorder.len());

    for i in 0..inorder.len() {
        map.insert(inorder[i],i);
    }

    dfs(0, preorder.len() as i32 - 1, preorder.deref(), &map, &mut 0)
}

/// (7) TARGET SUM WAYS
///
/// ```
/// use algorithms::depth_first_search::find_target_sum_ways;
///
/// assert_eq!(5, find_target_sum_ways(vec![1, 1, 1, 1, 1], 3));
///
/// assert_eq!(1, find_target_sum_ways(vec![1], 1));
/// ```
pub fn find_target_sum_ways(nums: Vec<i32>, target: i32) -> i32 {
    fn dfs(nums: &[i32], index: usize, temp: i32, target: i32, count: &mut i32) {
        if nums.len() == index {
            if temp == target {
                *count += 1;
            }

            return;
        }

        dfs(nums, index + 1, temp + nums[index], target, count);
        dfs(nums, index + 1, temp - nums[index], target, count);
    }

    let mut count = 0;
    dfs(nums.deref(), 0, 0, target, &mut count);
    count
}

/// (8) BINARY TREE MAXIMUM PATH SUM
///
/// ```
/// use algorithms::model::TreeNode;
/// use algorithms::depth_first_search::max_path_sum;
///
/// let node2 = TreeNode::new(2, None, None);
/// let node3 = TreeNode::new(3, None, None);
/// let node1 = TreeNode::new(1, node2, node3);
///
/// assert_eq!(6, max_path_sum(node1));
///
/// let node9 = TreeNode::new(9, None, None);
/// let node15 = TreeNode::new(15, None, None);
/// let node7 = TreeNode::new(7, None, None);
/// let node20 = TreeNode::new(20, node15, node7);
/// let node10 = TreeNode::new(-10, node9, node20);
///
/// assert_eq!(42, max_path_sum(node10))
/// ```
pub fn max_path_sum(root: TreeNodeRef) -> i32 {
    fn dfs(node: TreeNodeRef, max: &mut i32) -> i32 {
        match node {
            None => return 0,
            Some(node) => {
                let node = node.borrow();
                let left = dfs(node.left.clone(), max);
                let right = dfs(node.right.clone(), max);
                let current = i32::max(left + node.val, right + node.val);
                let current = i32::max(current, node.val);
                *max = i32::max(*max, current);
                *max = i32::max(*max, left + right + node.val);
                current
            }
        }
    }
    let mut max = i32::MIN;
    dfs(root, &mut max);
    max
}

/// (9) COURSE SCHEDULE
///
/// ````
/// use algorithms::depth_first_search::can_finish;
///
/// assert_eq!(true, can_finish(2, vec![vec![1, 0]]));
///
/// assert_eq!(false, can_finish(2, vec![vec![1, 0], vec![0, 1]]));
/// ````
pub fn can_finish(num_courses: i32, prerequisites: Vec<Vec<i32>>) -> bool {
    if num_courses == 0 || prerequisites.is_empty() {
        return true;
    }

    let mut graph: HashMap<i32, Vec<i32>> = (0..num_courses).map(|i| (i, vec![])).collect();

    for p in prerequisites {
        graph.get_mut(&p[0]).unwrap().push(p[1]);
    }

    let mut visited = vec![0; num_courses as usize];

    fn dfs(graph: &HashMap<i32, Vec<i32>>, visited: &mut [i32], i: i32) -> bool {
        let index = i as usize;

        if visited[index] == -1 {
            return false;
        }

        if visited[index] == 1 {
            return true;
        }

        visited[index] = -1;

        if graph.contains_key(&i) {
            for j in graph.get(&i).unwrap() {
                if !dfs(graph, visited, *j) {
                    return false;
                }
            }
        }

        visited[index] = 1;

        true
    }

    for i in 0..num_courses {
        if !dfs(&graph, &mut visited, i) {
            return false;
        }
    }

    true
}
