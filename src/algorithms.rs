//! # Algorithms implemented
//! 
//! ## Pathfinding algorithms
//! 
//! - [Bellman-Ford algorithm](fn.bellman_ford.html)
//! - [Dijkstra's algorithm](fn.dijkstra.html)
//! 
//! # Performance
//! 
//! All algorithms where measured using [criterion](https://github.com/bheisler/criterion.rs)
//! on a graph with 10,000 nodes and 39,600 edges. The algorithms where run 100 times on the test graph,
//! the mean time is listed in the table below. The tests where performed on a `Ryzen 5 7600x` processor.
//! 
//! | Algorithm | Mean time per run |
//! | - | - |
//! | Bellman-Ford | 1.8786 s |
//! | Dijkstra | 52.874 ms |
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
/// The [ShortestPathTree](../struct.ShortestPathTree.html) can then be used to retrieve the shortest distance and path to a node.
/// 
/// # Examples
/// ```rust
/// use simple_graph_algorithms::{Graph, ShortestPathTree, algorithms::dijkstra};
/// 
/// # fn main() -> Result<(), ()> {
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
/// /// Run Dijkstra's algorithm to calculate the shortest path tree, starting at node a.
/// let spt = dijkstra(&mut graph, &'a')?;
/// 
/// // Retrieve shortest distances
/// assert_eq!(spt.shortest_distance(&'c'), Some(4));
/// assert_eq!(spt.shortest_distance(&'d'), Some(8));
/// 
/// /// When run on a graph, that is missing the start node an Err is returned:
/// assert_eq!(dijkstra(&mut graph, &'e'), Err(()));
/// # Ok(())
/// # }
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
/// use simple_graph_algorithms::{Graph, ShortestPathTree, algorithms::bellman_ford};
/// 
/// # fn main() -> Result<(), ()> {
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
/// /// Run Bellman-Ford algorithm to calculate the shortest path tree, starting at node a.
/// let spt = bellman_ford(&mut graph, &'a')?;
/// 
/// // Retrieve shortest distances
/// assert_eq!(spt.shortest_distance(&'c'), Some(4));
/// assert_eq!(spt.shortest_distance(&'d'), Some(8));
/// 
/// /// When run on a graph, that is missing the start node an Err is returned:
/// assert_eq!(bellman_ford(&mut graph, &'e'), Err(()));
/// # Ok(())
/// # }
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
                let target_node = Rc::clone(&edge.target);
                let mut target_node_ref = target_node.borrow_mut();
                let new_distance = node_ref.distance + edge.weight;

                if new_distance < target_node_ref.distance {
                    target_node_ref.distance = new_distance;
                    let mut shortest_path = node_ref.shortest_path.clone();
                    shortest_path.push(Rc::clone(&node));
                    target_node_ref.shortest_path = shortest_path;
                }
            }
        }
    }
    //TODO Add in check that detects negative circles and return Err() when found, update docs accordingly and add in a test that checks that

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