use std::{fmt::Display, hash::Hash, collections::{BinaryHeap, HashSet}, rc::Rc, cell::RefCell};

use crate::{Graph, Node};


/// Calculates the shortest distance between two nodes.
/// This will utilize the algorithm by [djikstra](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm).
///
/// This algorithm does not work properly on graphs with negative edge weights. Use [bellman_ford](fn.bellman_ford.html) instead if your graph has negative weights.
///  
/// The distance field in each node should be set to `i32:MAX` before this function is called.
/// When the nodes are organized using the [Graph](struct.Graph.html) struct the function [reset_nodes](struct.Graph.html#method.reset_nodes) may be used to reset the distance field.
/// # Params
/// `graph` - the graph on which the algorithm should be run
/// 
/// `source` - id of the source node
/// 
/// `target` - id of the target node
/// # Returns
/// `Some(length)` when the shortest path was found.
/// 
/// `None` when no path between the two nodes exists.
/// 
/// # Examples
/// ```rust
/// use simple_graph_algorithms::{Graph, AddEdgeError, algorithms::dijkstra};
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
/// graph.add_edge(3, &'a', &'b')?;
/// graph.add_edge(4, &'a', &'c')?;
/// graph.add_edge(5, &'b', &'a')?;
/// graph.add_edge(2, &'b', &'d')?;
/// graph.add_edge(9, &'c', &'a')?;
/// graph.add_edge(1, &'c', &'d')?;
/// graph.add_edge(3, &'d', &'b')?;
/// graph.add_edge(7, &'d', &'c')?;
/// 
/// // Run dijkstra's algorithm to determine the shortest path, result contains the shortest distance.
/// let result = dijkstra(&mut graph, &'b', &'c').unwrap_or(-1);
/// assert_eq!(9, result);
/// 
/// // Run algorithm again, returns -1 because no node exists that connects e to the rest of the graph.
/// let result = dijkstra(&mut graph, &'a', &'e').unwrap_or(-1);
/// assert_eq!(-1, result);
/// 
/// # Ok::<(), AddEdgeError>(())
/// ```
/// It is also possible to create a graph from a vector. For more information take a look [here](struct.Graph.html#method.from_i32_vec).
pub fn dijkstra<T: Display + Clone + Eq + Hash>(graph: &mut Graph<T>, source_node_id: &T, target_node_id: &T) -> Option<i32> {
    graph.reset_nodes();
    let source_node = graph.nodes.get(source_node_id)?;
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

    let target_distance = graph.nodes.get(target_node_id)?.borrow().distance;
    if target_distance == i32::MAX {
        None
    } else {
        Some(target_distance)
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
    use crate::{Graph, algorithms::dijkstra};

    
    #[test]
    fn dijkstra_test_1() {
        let mut graph = Graph::new();
        graph.add_node("Berlin");
        graph.add_node("New York");
        graph.add_node("Brussels");
        graph.add_node("Copenhagen");
        graph.add_node("Oslo");
        graph.add_edge(5, &"Berlin", &"New York").unwrap();
        graph.add_edge(6, &"Berlin", &"Brussels").unwrap();
        graph.add_edge(2, &"New York", &"Berlin").unwrap();
        graph.add_edge(9, &"New York", &"Copenhagen").unwrap();
        graph.add_edge(7, &"Brussels", &"Berlin").unwrap();
        graph.add_edge(2, &"Brussels", &"Copenhagen").unwrap();
        graph.add_edge(5, &"Copenhagen", &"Brussels").unwrap();
        graph.add_edge(1, &"Copenhagen", &"New York").unwrap();
        graph.add_double_edge(10, &"Copenhagen", &"Oslo").unwrap();
        println!("Length: {}", dijkstra(&mut graph, &"Berlin", &"Oslo").unwrap_or(-1));
        println!("{}", graph);
    }

    #[test]
    fn dijkstra_test_2() {
         // Create new graph
         let mut graph: Graph<char> = Graph::new();

         // Add nodes to graph
         graph.add_node('a');
         graph.add_node('b');
         graph.add_node('c');
         graph.add_node('d');
         graph.add_node('e');

         // Add edges between nodes
         graph.add_edge(3, &'a', &'b').unwrap();
         graph.add_edge(4, &'a', &'c').unwrap();
         graph.add_edge(5, &'b', &'a').unwrap();
         graph.add_edge(2, &'b', &'d').unwrap();
         graph.add_edge(9, &'c', &'a').unwrap();
         graph.add_edge(1, &'c', &'d').unwrap();
         graph.add_edge(3, &'d', &'b').unwrap();
         graph.add_edge(7, &'d', &'c').unwrap();

         // Run dijkstra's algorithm to determine the shortest path, result contains the shortest distance.
         let result = dijkstra(&mut graph, &'b', &'c').unwrap_or(-1);
         assert_eq!(9, result);

         // Run algorithm again, returns -1 because no node exists that connects e to the rest of the graph.
         let result = dijkstra(&mut graph, &'a', &'e').unwrap_or(-1);
         assert_eq!(-1, result);
        assert_eq!(5, dijkstra(&mut graph, &'a', &'d').unwrap_or(-1));
        println!("Length: {}", dijkstra(&mut graph, &'a', &'d').unwrap_or(-1));
        println!("{}", graph);
    }
}