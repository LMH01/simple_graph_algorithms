//! # Algorithms implemented
//! 
//! ## Pathfinding algorithms
//! 
//! - [Bellman-Ford algorithm](fn.bellman_ford.html)
//! - [Dijkstra's algorithm](fn.dijkstra.html)
//! 
//! # Note on algorithm variants
//! 
//! All pathfinding algorithms have two variants: `ALGORITHM_NAME` and `ALGORITHM_NAME_graph`.
//! The only difference is that the `ALGORITHM_NAME` implementation takes a third argument that
//! provides a target node and that the function returns the distance from the source node
//! to that target node, when a path exists.
//! 
//! ## What variant should I choose?
//! 
//! You should use `ALGORITHM_NAME` when you need the distance from one node to a single other node 
//! and `ALGORITHM_NAME_graph` when you need the distance from one node to several other nodes.
//! 
//! Note that you can use [Graph::node_shortest_distance](../struct.Graph.html#method.node_shortest_distance) to receive further shortest paths to other nodes once
//! `ALGORITHM_NAME` has run.
//! 
//! ## Example
//! 
//! These two code snippets are equal in what they achieve, the shortest distance from `a` to `c`
//! is stored in the variable `distance` at the end of each snippet.
//! 
//! The functions [dijkstra](fn.dijkstra.html) and [dijkstra_graph](fn.dijkstra_graph.html) are used in this example.
//! 
//! ### Version using `ALGORITHM_NAME`
//! ```
//! use simple_graph_algorithms::{Graph, algorithms::dijkstra};
//! 
//! let mut graph = Graph::new();
//! 
//! graph.add_node("a");
//! graph.add_node("b");
//! graph.add_node("c");
//! graph.add_edge(1, &"a", &"b");
//! graph.add_edge(2, &"b", &"c");
//! 
//! let distance = dijkstra(&mut graph, &"a", &"c")
//!     .expect("Either node not contained in graph")
//!     .expect("No path found");
//! 
//! // distance now stores the shortest distance from a to c.
//! ```
//! 
//! ### Version using `ALGORITHM_NAME_graph`
//! ```
//! use simple_graph_algorithms::{Graph, algorithms::dijkstra_graph};
//! 
//! let mut graph = Graph::new();
//! 
//! graph.add_node("a");
//! graph.add_node("b");
//! graph.add_node("c");
//! graph.add_edge(1, &"a", &"b");
//! graph.add_edge(2, &"b", &"c");
//! 
//! dijkstra_graph(&mut graph, &"a")
//!     .expect("Node a is missing from the graph!");
//! 
//! let distance = graph.node_shortest_distance(&"c")
//!     .expect("Node is missing from the graph!");
//! 
//! // distance now stores the shortest distance from a to c.
//! ```

use std::{fmt::Display, hash::Hash, collections::{BinaryHeap, HashSet}, rc::Rc, cell::RefCell};

use crate::{Graph, Node};

/// Calculates the shortest distance between one source node and all other nodes on the graph using
/// [Dijkstra's algorithm](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm).
/// Returns the distance to one specified target node.
/// 
/// Dijkstra's algorithm does not work properly on graphs with negative edge weights.
/// Use [bellman_ford](fn.bellman_ford.html) instead if your graph contains those edges with negative weights.
/// 
/// This function takes a `graph` on which the algorithm should be run, the id of the start node
/// and the id of the target node.
/// 
/// Returns `Ok(Some(length))` when the shortest path was found, `Ok(None)` when the path
/// was not found or `Err(())` when either node was not found in the graph.
/// 
/// Use [dijkstra_graph](fn.dijkstra_graph.html) instead if you wan't to run Dijkstra's algorithm
/// on the graph without providing a target node.
/// 
/// # Examples
/// ```rust
/// use simple_graph_algorithms::{Graph, algorithms::dijkstra};
/// 
/// // Create new graph
/// let mut graph: Graph<char> = Graph::new();
/// 
/// // Add nodes to graph
/// graph.add_node('a');
/// graph.add_node('b');
/// graph.add_node('c');
/// graph.add_node('d');
/// graph.add_node('e');
/// 
/// // Add edges between nodes
/// graph.add_edge(3, &'a', &'b');
/// graph.add_edge(4, &'a', &'c');
/// graph.add_edge(5, &'b', &'a');
/// graph.add_edge(2, &'b', &'d');
/// graph.add_edge(9, &'c', &'a');
/// graph.add_edge(1, &'c', &'d');
/// graph.add_edge(3, &'d', &'b');
/// graph.add_edge(7, &'d', &'c');
/// 
/// // Result contains the shortest distance.
/// assert_eq!(dijkstra(&mut graph, &'b', &'c'), Ok(Some(9)));
/// 
/// // Returns None because no node exists that connects e to the rest of the graph.
/// assert_eq!(dijkstra(&mut graph, &'a', &'e'), Ok(None));
/// 
/// // Returns Err because node f is missing from the graph
/// assert_eq!(dijkstra(&mut graph, &'f', &'e'), Err(()));
/// ```
/// It is also possible to create a graph from a vector. For more information take a look [here](struct.Graph.html#method.from_i32_vec).
pub fn dijkstra<T: Display + Clone + Eq + Hash>(graph: &mut Graph<T>, source_node_id: &T, target_node_id: &T) -> Result<Option<i32>, ()> {
    inner_dijkstra(graph, source_node_id, Some(target_node_id))
}

/// Calculates the shortest distance between one source node and all other nodes on the graph using 
/// [Dijkstra's algorithm](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm).
/// 
/// Dijkstra's algorithm does not work properly on graphs with negative edge weights.
/// Use [bellman_ford](fn.bellman_ford.html) instead if your graph contains those edges with negative weights.
/// 
/// This function takes a `graph` on which the algorithm should be run and the id of the start node.
/// 
/// Returns `Ok(())` when the algorithm was run on the graph or `Err(())` when the start node is missing from the graph.
/// 
/// Use [dijkstra](fn.dijkstra.html) instead if you wan't to calculate the distance between a start and a target node and
/// get the distance as return value.
/// 
/// # Examples
/// ```rust
/// use simple_graph_algorithms::{Graph, algorithms::dijkstra_graph};
/// 
/// // Create new graph
/// let mut graph: Graph<char> = Graph::new();
/// 
/// // Add nodes to graph
/// graph.add_node('a');
/// graph.add_node('b');
/// graph.add_node('c');
/// graph.add_node('d');
/// 
/// // Add edges between nodes
/// graph.add_edge(3, &'a', &'b');
/// graph.add_edge(4, &'a', &'c');
/// graph.add_edge(5, &'b', &'a');
/// graph.add_edge(9, &'c', &'a');
/// graph.add_edge(4, &'c', &'d');
/// 
/// // Run Dijkstra's algorithm to determine the shortest path, to each node starting at node `a`.
/// assert_eq!(dijkstra_graph(&mut graph, &'a'), Ok(()));
/// 
/// // Access shortest ways
/// assert_eq!(graph.node_shortest_distance(&'c'), Some(4));
/// assert_eq!(graph.node_shortest_distance(&'d'), Some(8));
/// 
/// // Run algorithm again, returns Err because e does not exist in the graph.
/// assert_eq!(dijkstra_graph(&mut graph, &'e'), Err(()));
/// ```
pub fn dijkstra_graph<T: Display + Clone + Eq + Hash>(graph: &mut Graph<T>, source_node_id: &T) -> Result<(), ()> {
    match inner_dijkstra(graph, source_node_id, None) {
        Ok(_) => Ok(()),
        Err(_) => Err(()),
    }
}

/// Calculates Dijkstra's algorithm on the graph.
/// 
/// Returns Ok(Option<i32>) when the algorithm was run, Err when source or target node id was not found in the graph.
/// The option contained determines if a shortest path to the target node was found, if it was found it contains the distance.
fn inner_dijkstra<T: Display + Clone + Eq + Hash>(graph: &mut Graph<T>, source_node_id: &T, target_node_id: Option<&T>) -> Result<Option<i32>, ()> {
    graph.reset_nodes();
    let source_node = match graph.nodes.get(source_node_id) {
        Some(node) => node,
        None => return Err(()),
    };
    source_node.borrow_mut().distance = 0;
    let mut open_nodes: BinaryHeap<Rc<RefCell<Node<T>>>> = BinaryHeap::new();
    let mut open_node_ids: HashSet<T> = HashSet::new();
    let mut closed_node_ids: HashSet<T> = HashSet::new();
    //let mut closed_nodes: Vec<Rc<RefCell<Node<T>>>> = Vec::new();
    open_nodes.push(source_node.clone());

    while !open_nodes.is_empty() {
        let node = open_nodes.pop().unwrap();

        for edge in &node.borrow().edges {
            let target = &edge.target;
            let edge_weight = edge.weight;
            if !closed_node_ids.contains(&target.borrow().id) {
                let new_distance = node.borrow().distance + edge_weight;
                calc_min_distance(target, edge_weight, &node);
                if new_distance < target.borrow().distance {
                    target.borrow_mut().distance = new_distance;
                }
                if !open_node_ids.contains(&target.borrow().id) {
                    open_nodes.push(target.clone());
                    open_node_ids.insert(target.borrow().clone().id);
                }
            }
        }
        closed_node_ids.insert(node.borrow().clone().id);
    }

    sp_end(graph, target_node_id)
}

fn calc_min_distance<T: Display + Eq + Clone>(node: &Rc<RefCell<Node<T>>>, weight: i32, source: &Rc<RefCell<Node<T>>>) {
    let source_distance = source.borrow().distance;
    if source_distance + weight < node.borrow().distance {
        node.borrow_mut().distance = source_distance + weight;
        let mut shortest_path = source.borrow().shortest_path.clone();
        shortest_path.push(source.clone());
        node.borrow_mut().shortest_path = shortest_path;
    }
}

/// Calculates the shortest distance between one source node and all other nodes on the graph using 
/// [Bellman-Ford algorithm](https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm).
/// Returns the distance to one specified target node.
/// 
/// This algorithm works on graphs with negative edge weights but is slower than [Dijkstra's algorithm](fn.dijkstra.html).
/// 
/// This function takes a `graph` on which the algorithm should be run, the id of the start node
/// and the id of the target node.
/// 
/// Returns `Ok(Some(length))` when the shortest path was found, `Ok(None)` when the path
/// was not found or `Err(())` when either node was not found in the graph.
/// 
/// Use [bellman_ford_graph](fn.bellman_ford_graph.html) instead if you wan't to run the Bellman-Ford algorithm
/// on the graph without providing a target node.
/// 
/// # Examples
/// ```rust
/// use simple_graph_algorithms::{Graph, algorithms::bellman_ford};
/// 
/// // Create new graph
/// let mut graph: Graph<char> = Graph::new();
/// 
/// // Add nodes to graph
/// graph.add_node('a');
/// graph.add_node('b');
/// graph.add_node('c');
/// graph.add_node('d');
/// graph.add_node('e');
/// 
/// // Add edges between nodes
/// graph.add_edge(3, &'a', &'b');
/// graph.add_edge(4, &'a', &'c');
/// graph.add_edge(5, &'b', &'a');
/// graph.add_edge(2, &'b', &'d');
/// graph.add_edge(9, &'c', &'a');
/// graph.add_edge(1, &'c', &'d');
/// graph.add_edge(3, &'d', &'b');
/// graph.add_edge(7, &'d', &'c');
/// 
/// // Result contains the shortest distance.
/// assert_eq!(bellman_ford(&mut graph, &'b', &'c'), Ok(Some(9)));
/// 
/// // Returns None because no node exists that connects e to the rest of the graph.
/// assert_eq!(bellman_ford(&mut graph, &'a', &'e'), Ok(None));
/// 
/// // Returns Err because node f is missing from the graph
/// assert_eq!(bellman_ford(&mut graph, &'f', &'e'), Err(()));
/// ```
/// It is also possible to create a graph from a vector. For more information take a look [here](struct.Graph.html#method.from_i32_vec).
pub fn bellman_ford<T: Display + Eq + Clone + Hash>(graph: &mut Graph<T>, source_node_id: &T, target_node_id: &T) -> Result<Option<i32>, ()> {
    inner_bellman_ford(graph, source_node_id, Some(target_node_id))
}

/// Calculates the shortest distance between one source node and all other nodes on the graph using 
/// [Bellman-Ford algorithm](https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm).
/// 
/// This algorithm works on graphs with negative edge weights but is slower than [Dijkstra's algorithm](fn.dijkstra.html).
/// 
/// This function takes a `graph` on which the algorithm should be run and the id of the start node.
/// 
/// Returns `Ok(())` when the algorithm was run on the graph or `Err(())` when the start node is missing from the graph.
/// 
/// Use [bellman_ford](fn.bellman_ford.html) instead if you wan't to calculate the distance between a start and a target node and
/// get the distance as return value.
/// 
/// # Examples
/// ```rust
/// use simple_graph_algorithms::{Graph, algorithms::bellman_ford_graph};
/// 
/// // Create new graph
/// let mut graph: Graph<char> = Graph::new();
/// 
/// // Add nodes to graph
/// graph.add_node('a');
/// graph.add_node('b');
/// graph.add_node('c');
/// graph.add_node('d');
/// 
/// // Add edges between nodes
/// graph.add_edge(3, &'a', &'b');
/// graph.add_edge(4, &'a', &'c');
/// graph.add_edge(5, &'b', &'a');
/// graph.add_edge(9, &'c', &'a');
/// graph.add_edge(4, &'c', &'d');
/// 
/// // Run Bellman-Ford algorithm to determine the shortest path, to each node starting at node `a`.
/// assert_eq!(bellman_ford_graph(&mut graph, &'a'), Ok(()));
/// 
/// // Access shortest ways
/// assert_eq!(graph.node_shortest_distance(&'c'), Some(4));
/// assert_eq!(graph.node_shortest_distance(&'d'), Some(8));
/// 
/// // Run algorithm again, returns Err because e does not exist in the graph.
/// assert_eq!(bellman_ford_graph(&mut graph, &'e'), Err(()));
/// ```
pub fn bellman_ford_graph<T: Display + Eq + Clone + Hash>(graph: &mut Graph<T>, source_node_id: &T) -> Result<(), ()> {
    match inner_bellman_ford(graph, source_node_id, None) {
        Ok(_) => Ok(()),
        Err(_) => Err(()),
    }
}

/// Calculates Bellman-Ford algorithm on the graph.
/// 
/// Returns Ok(Option<i32>) when the algorithm was run, Err when source or target node id was not found in the graph.
/// The option contained determines if a shortest path to the target node was found, if it was found it contains the distance.
fn inner_bellman_ford<T: Display + Eq + Clone + Hash>(graph: &mut Graph<T>, source_node_id: &T, target_node_id: Option<&T>) -> Result<Option<i32>, ()> {
    graph.reset_nodes();

    let source_node = match graph.nodes.get(source_node_id) {
        Some(node) => node,
        None => return Err(()),
    };
    source_node.borrow_mut().distance = 0;

    let nodes_count = graph.size();

    for _ in 0..nodes_count - 1 {
        for (_, node) in &graph.nodes {
            let node_ref = node.borrow();

            if node_ref.distance == std::i32::MAX {
                continue;
            }

            for edge in &node_ref.edges {
                let target_node = edge.target.clone();
                let new_distance = node_ref.distance + edge.weight;

                if new_distance < target_node.borrow().distance {
                    target_node.borrow_mut().distance = new_distance;
                    let mut shortest_path = node_ref.shortest_path.clone();
                    shortest_path.push(node.clone());
                    target_node.borrow_mut().shortest_path = shortest_path;
                }
            }
        }
    }

    sp_end(graph, target_node_id)
}

/// Checks if graph contains target node and returns result depending on some factors.
/// 
/// Returns Ok(Some(length)) when the target node exists and has a distance set, Ok(None) when the target node
/// exists but has an infinite distance or Err(()) when the graph does not contain the target node.
fn sp_end<T: Display + Eq + Clone + Hash>(graph: &mut Graph<T>, target_node_id: Option<&T>) -> Result<Option<i32>, ()> {
    if target_node_id.is_some() {
        let target_distance = match graph.nodes.get(target_node_id.unwrap()) {
            Some(node) => node.borrow().distance,
            None => return Err(()),
        };

        if target_distance == i32::MAX {
            Ok(None)
        } else {
            Ok(Some(target_distance))
        }
    } else {
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use crate::{Graph, algorithms::{dijkstra, dijkstra_graph, bellman_ford, bellman_ford_graph}, graph_1, graph_2};

    #[test]
    fn dijkstra_test_1() {
        let mut graph = graph_1();
        assert_eq!(dijkstra(&mut graph, &"New York", &"Oslo"), Ok(Some(19)));
        assert_eq!(dijkstra(&mut graph, &"New York", &"London"), Ok(None));
        assert_eq!(dijkstra(&mut graph, &"New York", &"Munic"), Err(()));
    }

    #[test]
    fn dijkstra_test_2() {
        let mut graph = graph_2();
        assert_eq!(dijkstra(&mut graph, &'b', &'c'), Ok(Some(9)));
        assert_eq!(dijkstra(&mut graph, &'a', &'e'), Ok(None)); 
        assert_eq!(dijkstra(&mut graph, &'a', &'d'), Ok(Some(5)));
    }

    #[test]
    fn dijkstra_graph_test() {
        let mut graph = graph_1();
        assert_eq!(dijkstra_graph(& mut graph, &"London"), Ok(()));
        assert_eq!(dijkstra_graph(& mut graph, &"Los Angeles"), Err(()));
    }

    #[test]
    fn bellman_ford_test_1() {
        let mut graph = graph_1();
        assert_eq!(bellman_ford(&mut graph, &"New York", &"Oslo"), Ok(Some(19)));
        assert_eq!(bellman_ford(&mut graph, &"New York", &"London"), Ok(None));
        assert_eq!(bellman_ford(&mut graph, &"New York", &"Munic"), Err(()));
    }

    #[test]
    fn bellman_ford_test_2() {
        let mut graph = graph_2();
        assert_eq!(bellman_ford(&mut graph, &'b', &'c'), Ok(Some(9)));
        assert_eq!(bellman_ford(&mut graph, &'a', &'e'), Ok(None)); 
        assert_eq!(bellman_ford(&mut graph, &'a', &'d'), Ok(Some(5)));
    }

    #[test]
    fn bellman_ford_graph_test() {
        let mut graph = graph_1();
        assert_eq!(bellman_ford_graph(& mut graph, &"London"), Ok(()));
        assert_eq!(bellman_ford_graph(& mut graph, &"Los Angeles"), Err(()));
    }

    /// Returns a graph that contains negative edges
    fn graph_with_negative_edges() -> Graph<char> {
        let mut graph: Graph<char> = Graph::new();
        graph.add_node('a');
        graph.add_node('b');
        graph.add_node('c');
        graph.add_node('d');
        graph.add_double_edge(4, &'a', &'b');
        graph.add_edge(2, &'a', &'c');
        graph.add_edge(-1, &'c', &'a');
        graph.add_edge(5, &'a', &'d');
        graph.add_edge(-3, &'d', &'b');
        graph.add_double_edge(2, &'b', &'c');
        graph.add_edge(7, &'d', &'c');
        graph
    }

    #[test]
    fn bellman_ford_negative_edges_test() {
        let mut graph = graph_with_negative_edges();
        println!("{graph}");
        assert_eq!(bellman_ford(&mut graph, &'c', &'b'), Ok(Some(1)));
        assert_eq!(bellman_ford(&mut graph, &'d', &'b'), Ok(Some(-3)));
        assert_eq!(bellman_ford(&mut graph, &'d', &'a'), Ok(Some(-2)));
    }

    #[test]
    fn bellman_ford_node_shortest_path_test() {
        let mut graph = graph_with_negative_edges();
        assert!(bellman_ford(&mut graph, &'d', &'a').is_ok());
        assert_eq!(graph.node_shortest_path(&'a').unwrap(), "d -> b -> c -> a");
    }
}