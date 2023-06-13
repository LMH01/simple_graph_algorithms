use std::{fmt::Display, hash::Hash, collections::{BinaryHeap, HashSet}, rc::Rc, cell::RefCell};

use crate::{Graph, Node};


/// Calculates the shortest distance between one source node and one target node using
/// [dijkstra's algorithm](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm).
/// 
/// Dijkstra's algorithm does not work properly on graphs with negative edge weights.
/// Use [bellman_ford](fn.bellman_ford.html) instead if your graph contains those edges with negative weights.
/// 
/// This function takes a `graph` on wich the algorithm should be run, the id of the start node
/// and the id of the target node.
/// 
/// Returns `Ok(Some(length))` when the shortest path was found, `Ok(None)` when the path
/// was not found or `Err(())` when either node was not found in the graph.
/// 
/// Use [dijkstra_graph](fn.dijkstra_graph.html) instead if you wan't to run dijkstra's algorithm
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
/// // Run dijkstra's algorithm to determine the shortest path, result contains the shortest distance.
/// assert_eq!(dijkstra(&mut graph, &'b', &'c'), Ok(Some(9)));
/// 
/// // Run algorithm again, returns None because no node exists that connects e to the rest of the graph.
/// assert_eq!(dijkstra(&mut graph, &'a', &'e'), Ok(None));
/// 
/// // Run algorithm again, ruturns Err because node f is missing from the graph
/// assert_eq!(dijkstra(&mut graph, &'f', &'e'), Err(()));
/// ```
/// It is also possible to create a graph from a vector. For more information take a look [here](struct.Graph.html#method.from_i32_vec).
pub fn dijkstra<T: Display + Clone + Eq + Hash>(graph: &mut Graph<T>, source_node_id: &T, target_node_id: &T) -> Result<Option<i32>, ()> {
    inner_dijkstra(graph, source_node_id, Some(target_node_id))
}

/// Calculates the shortest distance between one source node and all other nodes on the graph using 
/// [dijkstra's algorithm](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm).
/// 
/// Dijkstra's algorithm does not work properly on graphs with negative edge weights.
/// Use [bellman_ford](fn.bellman_ford.html) instead if your graph contains those edges with negative weights.
/// 
/// This function takes a `graph` on wich the algorithm should be run and the id of the start node.
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
/// 
/// // Add edges between nodes
/// graph.add_edge(3, &'a', &'b');
/// graph.add_edge(4, &'a', &'c');
/// graph.add_edge(5, &'b', &'a');
/// graph.add_edge(9, &'c', &'a');
/// 
/// // Run dijkstra's algorithm to determine the shortest path, to each node starting at node `b`.
/// assert_eq!(dijkstra_graph(&mut graph, &'a'), Ok(()));
/// 
/// // Run algorithm again, returns Err because f does not exist in the graph.
/// assert_eq!(dijkstra_graph(&mut graph, &'d'), Err(()));
/// ```
pub fn dijkstra_graph<T: Display + Clone + Eq + Hash>(graph: &mut Graph<T>, source_node_id: &T) -> Result<(), ()> {
    match inner_dijkstra(graph, source_node_id, None) {
        Ok(_) => Ok(()),
        Err(_) => Err(()),
    }
}

/// Calculates dijkstras algorithm on the graph.
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

fn calc_min_distance<T: Display + Eq + Clone>(node: &Rc<RefCell<Node<T>>>, weight: i32, source: &Rc<RefCell<Node<T>>>) {
    let source_distance = source.borrow().distance;
    if source_distance + weight < node.borrow().distance {
        node.borrow_mut().distance = source_distance + weight;
        let mut shortest_path = source.borrow().shortest_path.clone();
        shortest_path.push(source.clone());
        node.borrow_mut().shortest_path = shortest_path;
    }
}

#[cfg(test)]
mod tests {
    use crate::{Graph, algorithms::{dijkstra, dijkstra_graph}, graph_1, graph_2};

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
        println!("Length: {:?}", dijkstra(&mut graph, &'a', &'d').unwrap_or(None));
        println!("{}", graph);
    }

    #[test]
    fn dijkstra_graph_test() {
        let mut graph = graph_1();
        assert_eq!(dijkstra_graph(& mut graph, &"London"), Ok(()));
        assert_eq!(dijkstra_graph(& mut graph, &"Los Angeles"), Err(()));
    }
}