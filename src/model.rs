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

pub type TreeNodeWithNextRef = Option<Rc<RefCell<TreeNodeWithNext>>>;

#[derive(Debug, PartialEq, Eq)]
pub struct TreeNodeWithNext {
    pub val: i32,
    pub left: TreeNodeWithNextRef,
    pub right: TreeNodeWithNextRef,
    pub next: TreeNodeWithNextRef,
}

impl TreeNodeWithNext {
    #[inline]
    pub fn new(
        val: i32,
        left: TreeNodeWithNextRef,
        right: TreeNodeWithNextRef,
        next: TreeNodeWithNextRef,
    ) -> TreeNodeWithNextRef {
        Some(Rc::new(RefCell::new(TreeNodeWithNext {
            val,
            left,
            right,
            next,
        })))
    }
}
