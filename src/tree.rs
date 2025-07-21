use std::sync::Arc;

use crate::disassembler::*;
use hashbrown::HashMap;
use parking_lot::{Mutex, RwLock, RwLockReadGuard, RwLockWriteGuard};

pub struct Node<T: Default> {
    pub children: Vec<usize>,
    pub value: T,
    pub parent: Option<usize>,
}

impl<T: Default> Default for Node<T> {
    fn default() -> Self {
        Node {
            value: T::default(),
            children: Vec::new(),
            parent: None,
        }
    }
}

pub struct Tree<T: Default> {
    root: Option<usize>,
    nodes: Vec<RwLock<Node<T>>>,
}

impl<T: Default> Tree<T> {
    fn new() -> Self {
        Tree {
            root: None,
            nodes: Vec::<RwLock<Node<T>>>::new(),
        }
    }

    pub fn with_root(root: usize) -> Self {
        Tree {
            root: Some(root),
            nodes: Vec::<RwLock<Node<T>>>::new(),
        }
    }

    pub fn insert(&mut self, value: T) -> usize {
        let index = self.nodes.len();
        self.nodes.push(RwLock::new(Node {
            value,
            children: Vec::new(),
            parent: None,
        }));
        index
    }

    pub fn insert_child(&mut self, parent_idx: usize, value: T) -> usize {
        let new_child = self.insert(value);
        self.aquire_node_mut(parent_idx).children.push(new_child);
        new_child
    }

    fn aquire_node_mut(&self, index: usize) -> RwLockWriteGuard<Node<T>> {
        self.nodes[index].write()
    }

    fn aquire_node(&self, index: usize) -> RwLockReadGuard<Node<T>> {
        self.nodes[index].read()
    }

    fn reserve_leaf(&mut self, parent_idx: usize) -> usize {
        let new_leaf = self.nodes.len();
        let mut new_node = Node::<T>::default();
        new_node.parent = Some(parent_idx);
        self.nodes.push(RwLock::new(new_node));
        self.aquire_node_mut(parent_idx).children.push(new_leaf);
        new_leaf
    }

    pub fn reserve_leaf_ref(&mut self, parent_idx: usize) -> RwLockWriteGuard<Node<T>> {
        let new_leaf = self.reserve_leaf(parent_idx);
        self.aquire_node_mut(new_leaf)
    }
}

pub struct DisassemblyTree {
    pub tree: Tree<DisassemblySection>,
    pub subroutines: HashMap<usize, usize>,
}

impl DisassemblyTree {
    pub fn new() -> Self {
        DisassemblyTree {
            tree: Tree::with_root(0),
            subroutines: HashMap::new(),
        }
    }

    pub fn add_subroutine(&mut self, start: usize, subroutine: usize) {
        self.subroutines.insert(start, subroutine);
    }
}
