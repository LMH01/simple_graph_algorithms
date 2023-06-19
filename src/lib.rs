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
//! use simple_graph_algorithms::{Graph, algorithms::{dijkstra, RunAlgorithmError}};
//! 
//! fn main() -> Result<(), RunAlgorithmError> {
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
//!     // Calculate the shortest path tree starting at node "a" using Dijkstra's algorithm
//!     let spt = dijkstra(&mut graph, &"a")?;
//! 
//!     // Get the shortest distance from "a" to other nodes
//!     assert_eq!(spt.shortest_distance(&"d"), Some(6));
//!     assert_eq!(spt.shortest_distance(&"c"), Some(2));
//!     assert_eq!(spt.shortest_distance(&"e"), Some(5));
//! 
//!     Ok(())
//! }
//! ```
//! # Features
//! 
//! | Feature | Description |
//! | - | - |
//! | from_instruction | Enables functionality that allows graphs to be parsed from a list of instructions. |

use std::{fmt::{Display, Debug}, rc::Rc, cell::RefCell, collections::HashMap, hash::Hash};
/// Contains implementations for the graph to work.
mod graph;
/// Contains all algorithms that are implemented in this crate.
pub mod algorithms;
/// Graph parsing from a list of instructions.
#[cfg(feature = "from_instruction")]
pub mod instruction;

/// A node inside the graph
#[derive(Clone, Eq, Debug)]
struct Node<T: Display + Eq> {
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
#[derive(Clone, Eq, Ord, PartialOrd, Debug)]
struct Edge<T: Display + Eq> {
    /// The "cost" of moving along this edge
    weight: i32,
    /// The parent of this edge
    parent: Rc<RefCell<Node<T>>>,
    /// Where this edge lands
    target: Rc<RefCell<Node<T>>>,
}

/// Graph data structure to organize nodes that are connected to each other with edges.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Graph<T: Display + Eq + Hash> {
    /// All nodes contained in this graph
    //nodes: Vec<Rc<RefCell<Node<T>>>>,

    /// Stores all nodes contained in this graph mapped to the node's id.
    nodes: HashMap<T, Rc<RefCell<Node<T>>>>,
}

impl<T: Display + Eq + Hash + Clone> PartialOrd for Graph<T> {
    /// Compares the size of this graph with the size of another graph.
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.size().partial_cmp(&other.size())
    }
}

impl<T: Display + Eq + Hash + Clone> Ord for Graph<T> {
    /// Compares the size of this graph with the size of another graph.
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.size().cmp(&other.size())
    }
}

impl<T: Display + Eq + Hash> Graph<T> {

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
#[derive(Eq, PartialEq, Debug)]
pub struct ShortestPathTree<T: Display + Clone + Hash + Eq> {
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
    #[allow(clippy::unnecessary_unwrap)]
    fn add_result(&mut self, node_id: T, distance: Option<i32>, shortest_path: Option<ShortestPath<T>>) {
        if shortest_path.is_none() | distance.is_none() {
            self.results.insert(node_id, None);
        } else {
            self.results.insert(node_id, Some((distance.unwrap(), shortest_path.unwrap())));
        }
    }

    /// Returns the shortest path to the node with id `target_id`.
    /// 
    /// If the `target_id` is not contained within the shortest path tree,
    /// `None` is returned instead of the shortest path.
    /// 
    /// For further information and for what can be done with the shortest
    /// path see [ShortestPath](struct.ShortestPath.html).
    pub fn shortest_path(&self, target_id: &T) -> Option<&ShortestPath<T>> {
        match self.results.get(target_id)? {
            Some(res) => Some(&res.1),
            None => None
        }
    }

    /// Returns the shortest distance to the node with id `target_id`.
    /// 
    /// If the `target_id` is not contained within the shortest path tree, 
    /// `None` is returned instead of the distance.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::{Graph, algorithms::dijkstra};
    /// # use simple_graph_algorithms::algorithms::RunAlgorithmError;
    /// # fn main() -> Result<(), RunAlgorithmError> {
    /// 
    /// let mut graph = Graph::new();
    /// graph.add_node('a');
    /// graph.add_node('b');
    /// graph.add_node('c');
    /// graph.add_edge(1, &'a', &'b');
    /// graph.add_edge(2, &'b', &'c');
    /// 
    /// let spt = dijkstra(&mut graph, &'a')?;
    /// 
    /// assert_eq!(spt.shortest_distance(&'b'), Some(1));
    /// assert_eq!(spt.shortest_distance(&'c'), Some(3));
    /// assert_eq!(spt.shortest_distance(&'d'), None);
    /// # Ok(())
    /// # }
    /// ```
    pub fn shortest_distance(&self, target_id: &T) -> Option<i32> {
        self.results.get(target_id)?.as_ref().map(|res| res.0)
    }

    /// Creates a shortest path tree from a graph and the id of a source node. A pathfinding algorithm
    /// should have run on the graph before the shortest path tree is constructed, to make sure that the
    /// resulting shortest path tree is not empty.
    fn from_graph(graph: &Graph<T>, source_id: &T) -> Self {
        let mut spt = ShortestPathTree::new(source_id.clone());
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
#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub struct ShortestPath<T: Display + Clone> {// Add documentation
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

    /// Id of source node where this shortest path starts.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::{Graph, algorithms::dijkstra};
    /// # use simple_graph_algorithms::algorithms::RunAlgorithmError;
    /// # fn main() -> Result<(), RunAlgorithmError> {
    /// 
    /// let mut graph = Graph::new();
    /// graph.add_node('a');
    /// graph.add_node('b');
    /// graph.add_edge(4, &'a', &'b');
    /// let spt = dijkstra(&mut graph, &'a')?;
    /// 
    /// // Calculate shortest path from a to b using dijkstra's algorithm.
    /// // It is ok to use .unwrap() here, because we know that the graph contains node b.
    /// let shortest_path = spt.shortest_path(&'b').unwrap();
    /// 
    /// assert_eq!(shortest_path.source(), Some(&'a'));
    /// # Ok(())}
    /// ```
    pub fn source(&self) -> Option<&T> {
        self.path.first()
    }

    /// Id of target node where this shortest path ends.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::{Graph, algorithms::dijkstra};
    /// # use simple_graph_algorithms::algorithms::RunAlgorithmError;
    /// # fn main() -> Result<(), RunAlgorithmError> {
    /// 
    /// let mut graph = Graph::new();
    /// graph.add_node('a');
    /// graph.add_node('b');
    /// graph.add_edge(4, &'a', &'b');
    /// let spt = dijkstra(&mut graph, &'a')?;
    /// 
    /// // Calculate shortest path from a to b using dijkstra's algorithm.
    /// // It is ok to use .unwrap() here, because we know that the graph contains node b.
    /// let shortest_path = spt.shortest_path(&'b').unwrap();
    /// 
    /// assert_eq!(shortest_path.target(), Some(&'b'));
    /// # Ok(())}
    /// ```
    pub fn target(&self) -> Option<&T> {
        self.path.last()
    }

    /// Id's of nodes that form the shortest path.
    /// 
    /// First element is the id of the start node.
    /// Last element is the id of the target node.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::{Graph, algorithms::dijkstra};
    /// # use simple_graph_algorithms::algorithms::RunAlgorithmError;
    /// # fn main() -> Result<(), RunAlgorithmError> {
    /// 
    /// let mut graph = Graph::new();
    /// graph.add_node('a');
    /// graph.add_node('b');
    /// graph.add_node('c');
    /// graph.add_edge(4, &'a', &'b');
    /// graph.add_edge(2, &'b', &'c');
    /// let spt = dijkstra(&mut graph, &'a')?;
    /// 
    /// // Calculate shortest path from a to c using dijkstra's algorithm.
    /// // It is ok to use .unwrap() here, because we know that the graph contains node c.
    /// let shortest_path = spt.shortest_path(&'c').unwrap();
    /// 
    /// assert_eq!(shortest_path.path(), &vec!['a', 'b', 'c']);
    /// # Ok(())}
    /// ```
    pub fn path(&self) -> &Vec<T> {
        &self.path
    }

}

impl<T: Display + Clone + Debug> Display for ShortestPath<T> {
    
    /// Formats the shortest path in a way that can be printed easily.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::{Graph, algorithms::dijkstra};
    /// # use simple_graph_algorithms::algorithms::RunAlgorithmError;
    /// # fn main() -> Result<(), RunAlgorithmError> {
    /// 
    /// let mut graph = Graph::new();
    /// graph.add_node('a');
    /// graph.add_node('b');
    /// graph.add_node('c');
    /// graph.add_edge(4, &'a', &'b');
    /// graph.add_edge(2, &'b', &'c');
    /// let spt = dijkstra(&mut graph, &'a')?;
    /// 
    /// // Calculate shortest path from a to c using dijkstra's algorithm.
    /// // It is ok to use .unwrap() here, because we know that the graph contains node c.
    /// let shortest_path = spt.shortest_path(&'c').unwrap();
    /// 
    /// assert_eq!(shortest_path.to_string(), "a -> b -> c");
    /// # Ok(())}
    /// ```
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
impl<T: Display + Clone + Eq> TryFrom<&Rc<RefCell<Node<T>>>> for ShortestPath<T> {
    type Error = &'static str;

    /// Tries to read the shortest path from the node.
    /// 
    /// Will fail on the following occasions:
    /// 
    /// - When the node does not contain a shortest path and the distance is not 0
    /// - when the distance is `i32::MAX`.
    fn try_from(value: &Rc<RefCell<Node<T>>>) -> Result<ShortestPath<T>, &'static str> {
        if value.borrow().distance == 0 {
            // It is tried to parse the shortest path to the source node
            return Ok(ShortestPath::new(vec![value.borrow().id.clone()]));
        } else if value.borrow().distance == i32::MAX || value.borrow().shortest_path.is_empty() {
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

#[derive(Clone, Eq, PartialEq, PartialOrd, Ord, Hash, Debug)]
/// Errors that can occur when edges are added to the graph.
/// 
/// Variants specify what exact node is missing.
pub enum AddEdgeError {
    /// Indicates that the source node is missing from the graph,
    SourceMissing,
    /// Indicates that the target node is missing form the graph.
    TargetMissing,
    /// Indicates that either node is missing from the graph.
    BothMissing,
}

impl ToString for AddEdgeError {
    fn to_string(&self) -> String {
        match self {
            AddEdgeError::SourceMissing => String::from("SourceMissing"),
            AddEdgeError::TargetMissing => String::from("TargetMissing"),
            AddEdgeError::BothMissing => String::from("BothMissing"),
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

    mod shortest_path_tree {
        use crate::{graph_2, algorithms::dijkstra, ShortestPath, graph, ShortestPathTree};

        #[test]
        fn add_result_test() {
            let mut spt = ShortestPathTree::new('a');
            let test_path = ShortestPath::new(vec!['a', 'd', 'c']);
            spt.add_result('b', Some(5), Some(test_path.clone()));
            let path = spt.shortest_path(&'b');
            let distance = spt.shortest_distance(&'b');
            assert!(path.is_some());
            assert_eq!(path.unwrap(), &test_path);
            assert_eq!(distance, Some(5));
        }

        #[test]
        fn shortest_path_test() {
            let mut graph = graph_2();
            let spt = dijkstra(&mut graph, &'a');
            assert!(spt.is_ok());
            let should_path = vec!['a', 'b', 'd'];
            let sp = ShortestPath::new(should_path);
            assert_eq!(spt.as_ref().unwrap().shortest_path(&'d'), Some(&sp));
            let should_path = vec!['a'];
            let sp = ShortestPath::new(should_path);
            assert_eq!(spt.unwrap().shortest_path(&'a'), Some(&sp));
            let spt = dijkstra(&mut graph, &'d');
            let should_path = vec!['d', 'b', 'a'];
            let sp = ShortestPath::new(should_path);
            assert_eq!(spt.unwrap().shortest_path(&'a'), Some(&sp));
        }

        #[test]
        fn shortest_distance_test() {
            let mut graph = graph_2();
            let spt = dijkstra(&mut graph, &'c');
            assert!(spt.is_ok());
            let spt = spt.unwrap();
            assert_eq!(spt.shortest_distance(&'b'), Some(4));
            assert_eq!(spt.shortest_distance(&'a'), Some(9));
        }

        #[test]
        fn from_graph_test() {
            let mut graph = graph_2();
            assert!(dijkstra(&mut graph, &'a').is_ok());
            let spt = ShortestPathTree::from_graph(&graph, &'a');
            assert_eq!(spt.source, 'a');
            assert_eq!(spt.results[&'a'], Some((0, ShortestPath::new(vec!['a']))));
        }
    }

    mod shortest_path {
        use crate::{graph_2, algorithms::dijkstra, ShortestPath};


        #[test]
        fn source_test() {
            let mut graph = graph_2();
            let spt = dijkstra(&mut graph, &'a').unwrap();
            assert_eq!(spt.shortest_path(&'a').unwrap().source(), Some(&'a'));
            assert_eq!(spt.shortest_path(&'d').unwrap().source(), Some(&'a'));
            let spt = dijkstra(&mut graph, &'d').unwrap();
            assert_eq!(spt.shortest_path(&'a').unwrap().source(), Some(&'d'));
            assert_eq!(spt.shortest_path(&'d').unwrap().source(), Some(&'d'));
        }

        #[test]
        fn target_test() {
            let mut graph = graph_2();
            let spt = dijkstra(&mut graph, &'a').unwrap();
            assert_eq!(spt.shortest_path(&'a').unwrap().target(), Some(&'a'));
            assert_eq!(spt.shortest_path(&'b').unwrap().target(), Some(&'b'));
            assert_eq!(spt.shortest_path(&'c').unwrap().target(), Some(&'c'));
            assert_eq!(spt.shortest_path(&'d').unwrap().target(), Some(&'d'));
        }

        #[test]
        fn path() {
            let mut graph = graph_2();
            let spt = dijkstra(&mut graph, &'a').unwrap();
            assert_eq!(spt.shortest_path(&'a').unwrap().path(), &vec!['a']);
            assert_eq!(spt.shortest_path(&'b').unwrap().path(), &vec!['a', 'b']);
            assert_eq!(spt.shortest_path(&'c').unwrap().path(), &vec!['a', 'c']);
            assert_eq!(spt.shortest_path(&'d').unwrap().path(), &vec!['a', 'b', 'd']);
        }

        #[test]
        fn display() {
            let mut graph = graph_2();
            let spt = dijkstra(&mut graph, &'a').unwrap();
            assert_eq!(spt.shortest_path(&'a').unwrap().to_string(), "a");
            assert_eq!(spt.shortest_path(&'b').unwrap().to_string(), "a -> b");
            assert_eq!(spt.shortest_path(&'c').unwrap().to_string(), "a -> c");
            assert_eq!(spt.shortest_path(&'d').unwrap().to_string(), "a -> b -> d");
        }

        #[test]
        fn try_from_rc_ref_cell_node() {
            let mut graph = graph_2();
            dijkstra(&mut graph, &'a').unwrap();
            let node = graph.nodes[&'d'].clone();
            let shortest_path = ShortestPath::try_from(&node);
            assert!(shortest_path.is_ok());
            let shortest_path = shortest_path.unwrap();
            assert_eq!(shortest_path.source(), Some(&'a'));
            assert_eq!(shortest_path.target(), Some(&'d'));
            assert_eq!(shortest_path.path(), &vec!['a', 'b', 'd']);
            assert_eq!(shortest_path.to_string(), "a -> b -> d");
        }

    }

}