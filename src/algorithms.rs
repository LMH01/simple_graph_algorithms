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
//! Note that you can get further shortest paths after `ALGORITHM_NAME` has run by using [Graph::node_shortest_distance](../struct.Graph.html#method.node_shortest_distance).
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

use crate::{Graph, Node, ShortestPathTree};

/// Calculates the shortest distance between one source node and all other nodes on the graph using 
/// [Dijkstra's algorithm](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm).
/// 
/// Dijkstra's algorithm does not work properly on graphs with negative edge weights.
/// Use [bellman_ford](fn.bellman_ford.html) instead if your graph contains those edges with negative weights.
/// 
/// This function takes a `graph` on which the algorithm should be run and the id of the start node.
/// 
/// Returns `Ok(ShortestPathTree)` when the algorithm was run on the graph or `Err(())` when the start node is missing from the graph.
/// The [ShortestPathTree](../struct.ShortestPathTree.html) can then be used to receive the shortest distance and path to a node.
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
pub fn dijkstra<T: Display + Clone + Eq + Hash>(graph: &mut Graph<T>, source_node_id: &T) -> Result<ShortestPathTree<T>, ()> {
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

    Ok(ShortestPathTree::from_graph(&graph, &source_node_id))
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
/// 
/// This algorithm works on graphs with negative edge weights but is slower than [Dijkstra's algorithm](fn.dijkstra.html).
/// graph
/// This function takes a `graph` on which the algorithm should be run and the id of the start node.
/// 
/// Returns `Ok(ShortestPathTree)` when the algorithm was run on the graph or `Err(())` when the start node is missing from the graph.
/// The [ShortestPathTree](../struct.ShortestPathTree.html) can then be used to receive the shortest distance and path to a node.
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
pub fn bellman_ford<T: Display + Eq + Clone + Hash>(graph: &mut Graph<T>, source_node_id: &T) -> Result<ShortestPathTree<T>, ()> {
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

    Ok(ShortestPathTree::from_graph(&graph, &source_node_id))
}

#[cfg(test)]
mod tests {
    use crate::{Graph, algorithms::{dijkstra, bellman_ford}, graph_1, graph_2};

    #[test]
    fn dijkstra_test_1() {
        let mut graph = graph_1();
        let spt = dijkstra(&mut graph, &"New York");
        assert!(spt.is_ok());
        assert_eq!(spt.as_ref().unwrap().shortest_distance(&"Oslo"), Some(19));
        assert_eq!(spt.as_ref().unwrap().shortest_distance(&"London"), None);
        assert_eq!(spt.as_ref().unwrap().shortest_distance(&"Munich"), None);
    }

    #[test]
    fn dijkstra_test_2() {
        let mut graph = graph_2();
        let spt = dijkstra(&mut graph, &'b');
        assert_eq!(dijkstra(&mut graph, &'b').unwrap().shortest_distance(&'c'), Some(9));
        assert_eq!(dijkstra(&mut graph, &'a').unwrap().shortest_distance(&'e'), None); 
        assert_eq!(dijkstra(&mut graph, &'a').unwrap().shortest_distance(&'d'), Some(5));
    }

    #[test]
    fn bellman_ford_test_1() {
        let mut graph = graph_1();
        let spt = bellman_ford(&mut graph, &"New York");
        assert!(spt.is_ok());
        assert_eq!(spt.as_ref().unwrap().shortest_distance(&"Oslo"), Some(19));
        assert_eq!(spt.as_ref().unwrap().shortest_distance(&"London"), None);
        assert_eq!(spt.as_ref().unwrap().shortest_distance(&"Munich"), None);
    }

    #[test]
    fn bellman_ford_test_2() {
        let mut graph = graph_2();
        let spt = bellman_ford(&mut graph, &'b');
        assert_eq!(dijkstra(&mut graph, &'b').unwrap().shortest_distance(&'c'), Some(9));
        assert_eq!(dijkstra(&mut graph, &'a').unwrap().shortest_distance(&'e'), None); 
        assert_eq!(dijkstra(&mut graph, &'a').unwrap().shortest_distance(&'d'), Some(5));
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
        assert_eq!(bellman_ford(&mut graph, &'c').unwrap().shortest_distance(&'b'), Some(1));
        assert_eq!(bellman_ford(&mut graph, &'d').unwrap().shortest_distance(&'b'), Some(-3)); 
        assert_eq!(bellman_ford(&mut graph, &'d').unwrap().shortest_distance(&'a'), Some(-2));
    }

    #[test]
    fn bellman_ford_node_shortest_path_test() {
        let mut graph = graph_with_negative_edges();
        let spt = bellman_ford(&mut graph, &'d');
        assert!(spt.is_ok());
        assert_eq!(spt.unwrap().shortest_path(&'a').unwrap().to_string(), "d -> b -> c -> a");
    }
}