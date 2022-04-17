use std::borrow::Borrow;
use std::rc::Rc;
use std::cell::RefCell;
use std::ops::Deref;

#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}

impl TreeNode {
    #[inline]
    pub fn new(val: i32) -> Self {
        TreeNode {
            val,
            left: None,
            right: None,
        }
    }

    pub fn new_ref(val: i32, left: MaybeTreeNodeRef, right: MaybeTreeNodeRef) -> MaybeTreeNodeRef {
        Some(Rc::new(RefCell::new(TreeNode { val, left, right, })))
    }
}

type MaybeTreeNodeRef = Option<Rc<RefCell<TreeNode>>>;

/// Search in a Binary Search Tree
/// You are given the root of a binary search tree (BST) and an integer val.
/// Find the node in the BST that the node's value equals val and return the subtree rooted with that node.
/// If such a node does not exist, return None.
/// ```
/// use std::cell::RefCell;
/// use std::rc::Rc;
/// use algorithms::depth_first::search_bst;
/// use algorithms::depth_first::TreeNode;
///
/// let node1 = TreeNode::new_ref(1, None, None);
/// let node3 = TreeNode::new_ref(3, None, None);
/// let node2 = TreeNode::new_ref(2, node1.clone(), node3.clone());
/// let node7 = TreeNode::new_ref(1, None, None);
/// let node4 = TreeNode::new_ref(4, node2.clone(), node7.clone());
///
/// assert_eq!(node2.clone(), search_bst(node4, 2))
/// ```
pub fn search_bst(root: MaybeTreeNodeRef, val: i32) -> MaybeTreeNodeRef {
    let mut current = root;

    while let Some(node_rc) = current.clone() {
        let node_ref = node_rc.borrow();

        if node_ref.val > val {
            current = node_ref.left.clone();
        } else if node_ref.val < val {
            current = node_ref.right.clone();
        } else {
            return Some(node_rc.clone());
        }
    }

    None
}


pub fn inorder_traversal(root: MaybeTreeNodeRef) -> Vec<i32> {
    let mut result = vec![];
    let mut stack = vec![(root, false)];

    while !stack.is_empty() {
        let (maybe_node_ref, visited) = stack.pop().unwrap();

        if let Some(node_ref) = maybe_node_ref.as_deref() {
            let node_ref = node_ref.borrow();

            if visited {
                result.push(node_ref.val)
            } else {
                stack.push((node_ref.right.clone(), false));
                stack.push((maybe_node_ref.clone(), true));
                stack.push((node_ref.left.clone(), false));
            }
        }
    }

    result
}