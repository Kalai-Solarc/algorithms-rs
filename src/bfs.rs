use std::collections::VecDeque;

use crate::model::TreeNodeRef;

/// (1) BINARY TREE RIGHT SIDE VIEW
///
/// ```
/// use algorithms::model::TreeNode;
/// use algorithms::bfs::right_side_view;
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
