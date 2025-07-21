use std::sync::Arc;

use crate::disassembler::*;
use hashbrown::HashMap;
use parking_lot::RwLock;

struct Node<T> {
    value: T,
    children: Vec<usize>,
    parent: Option<usize>,
}

pub struct Tree<T> {
    root: Option<usize>,
    nodes: Vec<RwLock<Node<T>>>,
}

impl<T> Tree<T> {
    fn new() -> Self {
        Tree {
            root: None,
            nodes: Vec::<RwLock<Node<T>>>::new(),
        }
    }

    fn insert(&mut self, value: T) -> usize {
        let index = self.nodes.len();
        self.nodes.push(RwLock::new(Node {
            value,
            children: Vec::new(),
            parent: None,
        }));
        index
    }
}

pub struct DisassemblyTree {
    pub tree: Arc<Tree<DisassemblySection>>,
    pub subroutines: HashMap<u32, usize>,
    disassembly_function: Arc<dyn Fn(Arc<Vec<u8>>, usize) -> DisassemblySection>,
}

impl DisassemblyTree {}
