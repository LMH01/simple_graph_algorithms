//! # Overview
//! 
//! All algorithms in this crate are run using the [Graph](struct.Graph.html) struct.
//! It is used to organize nodes that are connected to each other using weighted edges
//! and to provide a simple to use interface.
//!
//! Click [here](algorithms/index.html#algorithms-implemented) to see a list of implemented algorithms.
//!  
//! # Minimal working example
//! ```
//! use simple_graph_algorithms::{Graph, algorithms::dijkstra};
//! 
//! fn main() {
//!     // Create empty graph
//!     let mut graph = Graph::new();
//! 
//!     // Add new nodes to the graph
//!     graph.add_node("a");
//!     graph.add_node("b");
//!     graph.add_node("c");
//!     graph.add_node("d");
//!     graph.add_node("e");
//! 
//!     // Add edges to the graph
//!     graph.add_edge(1, &"a", &"b"); // Adds an edge that leads from a to b with weight 1
//!     graph.add_edge(2, &"a", &"c");
//!     graph.add_edge(5, &"b", &"d");
//!     graph.add_edge(3, &"c", &"a");
//!     graph.add_edge(4, &"d", &"a");
//!     graph.add_edge(2, &"d", &"c");
//!     graph.add_edge(3, &"c", &"e");
//!     
//!     // Calculate the shortest distance from node "a" to node "d" using dijkstra's algorithm
//!     let distance = dijkstra(&mut graph, &"a", &"d");
//!     assert_eq!(distance, Ok(Some(6)));
//! 
//!     // Get more distances
//!     assert_eq!(graph.node_shortest_distance(&"c"), Some(2));
//!     assert_eq!(graph.node_shortest_distance(&"e"), Some(5));
//! }
//! ```

use std::{fmt::{Display, Debug}, rc::Rc, cell::RefCell, collections::HashMap, hash::Hash};

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

/// Structure to store the shortest path and distance from one node 
/// to other nodes after a pathfinding algorithm has been run on a graph.
#[derive(Debug)]
pub struct ShortestPathTree<T: Display + Clone> {
    source: T,
    results: HashMap<T, Option<(i32, ShortestPath<T>)>>,
}

impl<T: Display + Clone + Eq + Hash> ShortestPathTree<T> {
    
    /// Create a new shortest path tree originating at `source`.
    fn new(source: T) -> Self {
        Self {
            source,
            results: HashMap::new(),
        }
    }

    /// Adds a new result to the shortest path tree
    /// 
    /// The `node_id` is the id of the node for which a result should be added.
    /// The `distance` is the minimal distance to this node and `shortest_path` is the path taken to get to this node.
    /// 
    /// If either `distance` or `shortest_path` is None, no path will be added.
    fn add_result(&mut self, node_id: T, distance: Option<i32>, shortest_path: Option<ShortestPath<T>>) {// add test
        if shortest_path.is_none() | distance.is_none() {
            self.results.insert(node_id, None);
        } else {
            self.results.insert(node_id, Some((distance.unwrap(), shortest_path.unwrap())));
        }
    }

    pub fn shortest_path(&self, node_id: &T) -> Option<&ShortestPath<T>> {//TODO Add doc, example and test
        match self.results.get(node_id)? {
            Some(res) => Some(&res.1),
            None => None
        }
    }

    /// Returns the shortest distance to the target node.
    /// 
    /// Requires that a pathfinding algorithm has run to set the shortest distance.
    /// 
    /// If the `target_node_id` is not contained within the graph, `None` is returned instead of the distance.
    /// 
    /// # Examples
    /// 
    /// ## Use pathfinding algorithm that does not return a distance
    /// ```
    /// use simple_graph_algorithms::{Graph, algorithms::dijkstra_graph};
    /// 
    /// let mut graph = Graph::new();
    /// graph.add_node('a');
    /// graph.add_node('b');
    /// graph.add_node('c');
    /// graph.add_edge(1, &'a', &'b');
    /// graph.add_edge(2, &'b', &'c');
    /// 
    /// dijkstra_graph(&mut graph, &'a')?;
    /// 
    /// assert_eq!(graph.node_shortest_distance(&'b'), Some(1));
    /// assert_eq!(graph.node_shortest_distance(&'c'), Some(3));
    /// assert_eq!(graph.node_shortest_distance(&'d'), None);
    /// # Ok::<(), ()>(())
    /// ```
    /// ## Use pathfinding algorithm that returns a distance to a target node
    /// ```
    /// use simple_graph_algorithms::{Graph, algorithms::dijkstra};
    /// 
    /// let mut graph = Graph::new();
    /// graph.add_node('a');
    /// graph.add_node('b');
    /// graph.add_node('c');
    /// graph.add_edge(1, &'a', &'b');
    /// graph.add_edge(2, &'b', &'c');
    /// 
    /// assert_eq!(dijkstra(&mut graph, &'a', &'b'), Ok(Some(1)));
    /// 
    /// assert_eq!(graph.node_shortest_distance(&'c'), Some(3));
    /// assert_eq!(graph.node_shortest_distance(&'d'), None);
    /// ```
    pub fn shortest_distance(&self, target_node_id: &T) -> Option<i32> {//TODO Update example and add test
        match self.results.get(&target_node_id)? {
            Some(res) => Some(res.0),
            None => None,
        }
    }

    /// Creates a shortest path tree from a graph and a source node. A pathfinding algorithm
    /// should have run on the graph before the shortest path tree is constructed.
    fn from_graph(graph: &Graph<T>, source: &T) -> Self {//TODO add test
        let mut spt = ShortestPathTree::new(source.clone());
        for (id, node) in &graph.nodes {
            if let Ok(path) = ShortestPath::try_from(node) {
                spt.add_result(id.clone(), Some(node.borrow().distance), Some(path));
            } else {
                spt.add_result(id.clone(), None, None);
            }
        }
        spt
    }

}

/// The shortest path from one node to another.
#[derive(Debug)]
pub struct ShortestPath<T: Display + Clone> {//TODO check if it is possible to use references instead of T, add documentation
    /// Contains a list of node ids, first entry is the start node, last entry is the target node.
    path: Vec<T>, //TODO maybe add later that the distance between each node is stored as well
}

impl<T: Display + Clone> ShortestPath<T> {

    /// Creates a new shortest path from a source node to a target node
    fn new(path: Vec<T>) -> Self {
        Self {
            path,
        }
    }

    /// The source node where this shortest path starts
    pub fn source(&self) -> Option<&T> {//TODO Add example and test
        self.path.first().clone()
    }

    /// The target node where this shortest path ends
    pub fn target(&self) -> Option<&T> {//TODO Add example and test
        self.path.last().clone()
    }

    /// Path fragments of the shortest path.
    /// 
    /// First element is the start node.
    /// Last element is the target node.
    /// 
    /// # Example
    /// //TODO Add example
    pub fn path(&self) -> &Vec<T> {//TODO Add test
        &self.path
    }

}

impl<T: Display + Clone + Debug> Display for ShortestPath<T> {
    
    /// Returns a string illustrating the shortest path to the target node.
    /// 
    /// Requires that a pathfinding algorithm has run to fill the shortest paths.
    /// 
    /// If the `target_node_id` is not contained within the graph, `None` is returned instead of the path.
    /// //TODO add in example, once pathfinding algorithm has been implemented
    /// 
//    /// # Example
//    /// ```
//    /// use simple_graph_algorithms::{Graph, Node}, algorithms::dijkstra};
//    /// 
//    /// // Prepare graph
//    /// let mut graph: Graph<char> = Graph::new();
//    /// let node_a_idx = graph.add_node(Node::new('a'));
//    /// let node_b_idx = graph.add_node(Node::new('b'));
//    /// let node_c_idx = graph.add_node(Node::new('c'));
//    /// let node_d_idx = graph.add_node(Node::new('d'));
//    /// graph.add_edge(3, node_a_idx, node_b_idx);
//    /// graph.add_edge(4, node_a_idx, node_c_idx);
//    /// graph.add_edge(3, node_b_idx, node_a_idx);
//    /// graph.add_edge(2, node_b_idx, node_d_idx);
//    /// graph.add_edge(9, node_c_idx, node_a_idx);
//    /// graph.add_edge(1, node_c_idx, node_d_idx);
//    /// graph.add_edge(3, node_d_idx, node_b_idx);
//    /// graph.add_edge(7, node_d_idx, node_c_idx);
//    /// dijkstra(&mut graph, &'a', &'d').unwrap_or(-1);
//    /// 
//    /// // Get shortest path
//    /// let string = graph.node_by_id(&'d').unwrap().borrow_mut().shortest_path();
//    /// assert_eq!("a -> b -> d", string)
//    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, node_id) in self.path.iter().enumerate() {
            if i == self.path.len()-1 {
                // Last node
                write!(f, "{}", node_id)?;
            } else {
                write!(f, "{} -> ", node_id)?;
            }
        }
        Ok(())
    }

}

#[doc(hidden)]
impl<T: Display + Clone> TryFrom<&Rc<RefCell<Node<T>>>> for ShortestPath<T> {
    type Error = &'static str;

    /// Tries to read the shortest path from the node.
    /// 
    /// Will fail when the node does not contain a shortest path or when the distance is `i32::MAX`.
    fn try_from(value: &Rc<RefCell<Node<T>>>) -> Result<ShortestPath<T>, &'static str> {
        if value.borrow().distance == i32::MAX || value.borrow().shortest_path.is_empty() {
            return Err("Unable to create shortest path from vector, vector is empty!");
        }
        let mut path = Vec::new();
        for node in &value.borrow().shortest_path {
            path.push(node.borrow().id.clone());
        }
        path.push(value.borrow().id.clone());
        Ok(ShortestPath::new(path))
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

/// Graph variation used for testing
#[cfg(test)]
fn graph_1() -> Graph<&'static str> {
    let mut graph = Graph::new();
    graph.add_node("Berlin");
    graph.add_node("New York");
    graph.add_node("Brussels");
    graph.add_node("Copenhagen");
    graph.add_node("Oslo");
    graph.add_node("London");
    graph.add_edge(5, &"Berlin", &"New York");
    graph.add_edge(6, &"Berlin", &"Brussels");
    graph.add_edge(2, &"New York", &"Berlin");
    graph.add_edge(9, &"New York", &"Copenhagen");
    graph.add_edge(7, &"Brussels", &"Berlin");
    graph.add_edge(2, &"Brussels", &"Copenhagen");
    graph.add_edge(5, &"Copenhagen", &"Brussels");
    graph.add_edge(1, &"Copenhagen", &"New York");
    graph.add_double_edge(10, &"Copenhagen", &"Oslo");
    graph
}

/// Graph variation used for testing
#[cfg(test)]
fn graph_2() -> Graph<char> {
    let mut graph: Graph<char> = Graph::new();
    graph.add_node('a');
    graph.add_node('b');
    graph.add_node('c');
    graph.add_node('d');
    graph.add_node('e');
    graph.add_edge(3, &'a', &'b');
    graph.add_edge(4, &'a', &'c');
    graph.add_edge(5, &'b', &'a');
    graph.add_edge(2, &'b', &'d');
    graph.add_edge(9, &'c', &'a');
    graph.add_edge(1, &'c', &'d');
    graph.add_edge(3, &'d', &'b');
    graph.add_edge(7, &'d', &'c');
    graph
}

#[cfg(test)]
mod tests {

    //#[test]
    //fn node_shortest_distance_test() {
    //    let mut graph = graph_2();
    //    dijkstra_graph(&mut graph, &'a').unwrap();
    //    assert_eq!(graph.node_shortest_distance(&'b'), Some(3));
    //    assert_eq!(graph.node_shortest_distance(&'d'), Some(5));
    //    assert_eq!(graph.node_shortest_distance(&'g'), None);
    //}
}