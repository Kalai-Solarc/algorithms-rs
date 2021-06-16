use std::collections::VecDeque;

use crate::model::TreeNodeRef;

/// (1) BINARY TREE RIGHT SIDE VIEW
///
/// ```
/// use algorithms::model::TreeNode;
/// use algorithms::breadth_first_search::right_side_view;
///
/// let node5 = TreeNode::new(5, None, None);
/// let node2 = TreeNode::new(2, None, node5);
/// let node4 = TreeNode::new(4, None, None);
/// let node3 = TreeNode::new(3, None, node4);
/// let node1 = TreeNode::new(1, node2, node3);
///
/// assert_eq!(vec![1, 3, 4], right_side_view(node1));
/// ```
///
pub fn right_side_view(root: TreeNodeRef) -> Vec<i32> {
    let mut result = vec![];
    let mut queue = VecDeque::new();

    match root {
        None => return result,
        Some(root) => queue.push_back(root),
    }

    while !queue.is_empty() {
        for i in 0..queue.len() {
            if let Some(current) = queue.pop_front() {
                let node = current.borrow();

                if i == 0 {
                    result.push(node.val);
                }

                if let Some(right) = node.right.clone() {
                    queue.push_back(right)
                }

                if let Some(left) = node.left.clone() {
                    queue.push_back(left)
                }
            }
        }
    }

    result
}

/// (2) BINARY TREE LEVEL ORDER TRAVERSAL
///
/// ```
/// use algorithms::model::TreeNode;
/// use algorithms::breadth_first_search::level_order;
/// let node15 = TreeNode::new(15, None, None);
/// let node7 = TreeNode::new(7, None, None);
/// let node20 = TreeNode::new(20, node15, node7);
/// let node9 = TreeNode::new(9, None, None);
/// let node3 = TreeNode::new(3, node9, node20);
///
/// assert_eq!(vec![vec![3], vec![9, 20], vec![15, 7]], level_order(node3));
/// ```
pub fn level_order(root: TreeNodeRef) -> Vec<Vec<i32>> {
    let mut result = vec![];
    let mut queue = VecDeque::new();

    if root.is_none() {
        return result;
    }

    queue.push_back(vec![root]);

    while !queue.is_empty() {
        let mut values = vec![];
        let mut nodes = vec![];

        for node in queue.pop_front().unwrap() {
            if let Some(node) = node {
                let node = node.borrow();
                values.push(node.val);
                nodes.push(node.left.clone());
                nodes.push(node.right.clone());
            }
        }

        if !values.is_empty() {
            result.push(values);
        }

        if !nodes.is_empty() {
            queue.push_back(nodes);
        }
    }

    result
}
