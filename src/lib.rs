use std::{fmt::Display, rc::Rc, cell::RefCell, collections::{HashSet, HashMap}};

/// Contains implementations for the graph to work.
mod graph;
/// Contains all algorithms that are implemented in this crate.
pub mod algorithms;

/// A node inside the graph
#[derive(Debug, Clone, Eq)]
struct Node<T: Display> {
    /// Identifier of this node
    id: T,
    /// Edges of this node
    edges: Vec<Edge<T>>,
    /// The calculated minimum distance to this node from the start node
    distance: i32,
    /// The way to go to get to this node
    shortest_path: Vec<Rc<RefCell<Node<T>>>>,
}

// An edge between two nodes inside a graph
#[derive(Debug, Clone, Eq)]
struct Edge<T: Display> {
    /// The "cost" of moving along this edge
    weight: i32,
    /// The parent of this edge
    parent: Rc<RefCell<Node<T>>>,
    /// Where this edge lands
    target: Rc<RefCell<Node<T>>>,
}

/// Graph data structure to organize nodes that are connected to each other with edges.
/// 
/// # Minimal Example
/// //TODO Add minimal example
#[derive(Debug)]
pub struct Graph<T: Display> {
    /// All nodes contained in this graph
    //nodes: Vec<Rc<RefCell<Node<T>>>>,

    /// Stores all nodes contained in this graph mapped to the node's id.
    nodes: HashMap<T, Rc<RefCell<Node<T>>>>,
}

impl<T: Display> Graph<T> {

    /// Resets the distance of each node in the graph back to `i32::MAX` and resets the shortest path string.
    /// 
    /// Is called each time before a pathfinding algorithm is run.
    fn reset_nodes(&mut self) {
        for (_, node) in self.nodes.iter_mut() {
            node.borrow_mut().distance = i32::MAX;
            node.borrow_mut().shortest_path = Vec::new();
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
/// Errors that can occur when edges are added to a graph.
pub enum AddEdgeError {
    /// Indicates that the source node is missing from the graph,
    SourceMissing,
    /// Indicates that the target node is missing form the graph.
    TargetMissing,
    /// Indicates that either node is missing from the graph.
    EitherMissing,
}

impl ToString for AddEdgeError {
    fn to_string(&self) -> String {
        match self {
            AddEdgeError::SourceMissing => String::from("SourceMissing"),
            AddEdgeError::TargetMissing => String::from("TargetMissing"),
            AddEdgeError::EitherMissing => String::from("EitherMissing"),
        }
    }
}