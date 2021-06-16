use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: TreeNodeRef,
    pub right: TreeNodeRef,
}

pub type TreeNodeRef = Option<Rc<RefCell<TreeNode>>>;

impl TreeNode {
    #[inline]
    pub fn new(val: i32, left: TreeNodeRef, right: TreeNodeRef) -> TreeNodeRef {
        Some(Rc::new(RefCell::new(TreeNode { val, left, right })))
    }
}
