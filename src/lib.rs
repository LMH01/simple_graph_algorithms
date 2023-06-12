use std::{fmt::Display, rc::Rc, cell::RefCell, collections::{HashSet, HashMap}};

/// Contains implementations for the graph to work
mod graph;

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