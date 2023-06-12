use std::{fmt::Display, rc::Rc, cell::RefCell, hash::Hash, collections::HashMap};

use crate::{Node, Edge, Graph, AddEdgeError};

// Node implementations

impl<T: Display + Eq + Clone> Node<T> {
    
    /// Creates a new node with `id`.
    /// 
    /// The id is used to compare this node with other nodes and to address this node when searching for a shortest way.
    fn new(id: T) -> Self {
        Self {
            id,
            edges: Vec::new(),
            distance: i32::MAX,
            shortest_path: Vec::new(),
        }
    }

    /// Returns the shortest path to this node.
    /// 
    /// For a node to receive its shortest path a path finding algorithm has to have run beforehand.
    /// 
    /// See //TODO move example to function in graph that exposes this functionality to the user
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
    fn shortest_path(&self) -> String {
        let mut path: Vec<T> = Vec::new();
        for previous in &self.shortest_path {
            path.push(previous.borrow().id.clone());
        }
        let mut path_string = String::new();
        for previous in path {
            path_string.push_str(&format!("{} -> ", previous));
        }
        path_string.push_str(&format!("{}", self.id));
        path_string
    }

}

impl<T: Display + Eq> PartialEq for Node<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T: Display + Eq> Display for Node<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.id)
    }
}

impl<T: Display + Eq> PartialOrd for Node<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.distance.cmp(&other.distance).reverse())
    }
}

impl<T: Display + Eq> Ord for Node<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.distance.cmp(&other.distance).reverse()
    }
}

// Edge implementations

impl<T: Display + Eq> Edge<T> {
    /// Creates a new edge
    /// # Params
    /// - `weight` the weight of this edge
    /// - `parent` the node from which the edge originates
    /// - `target` the node to which the edge lands
    fn new(weight: i32, parent: Rc<RefCell<Node<T>>>, target: Rc<RefCell<Node<T>>>) -> Self {
        Self {
            weight,
            parent,
            target,
        }
    }
}

impl<T: Display + Eq> PartialEq for Edge<T> {
    fn eq(&self, other: &Self) -> bool {
        self.parent.borrow().id.eq(&other.parent.borrow().id) 
            && self.target.borrow().id.eq(&other.target.borrow().id)
            && self.weight.eq(&other.weight)
    }
}

// Graph implementations

impl<'a, T: Display + Clone + Eq + Hash> Graph<T> {
    
    /// Creates a new and empty graph.
    pub fn new() -> Self {
        Self {
            nodes: HashMap::new(),
        }
    }

    /// Adds a new node to the graph.
    /// 
    /// The `id` is the unique identifier of this node, it is also used to specify the start node when a path finding algorithm is run.
    /// 
    /// Return value indicates if the node was added to the graph.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::Graph;
    /// 
    /// let mut graph = Graph::new();
    /// 
    /// assert_eq!(graph.add_node("a"), true);
    /// assert_eq!(graph.add_node("b"), true);
    /// 
    /// // Returns false because node with id `b` was already added to the graph.
    /// assert_eq!(graph.add_node("b"), false);
    /// ```
    pub fn add_node(&mut self, id: T) -> bool {
        if self.nodes.contains_key(&id) {
            false
        } else {
            self.nodes.insert(id.clone(), Rc::new(RefCell::new(Node::new(id))));
            true
        }
    }

    /// Adds new nodes to the graph.
    /// 
    /// For each entry in the `ids` vector a new node is added, the entry being the unique identifier of the new node.
    /// 
    /// Return value indicates how many nodes where not added because a node with the id already exists.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::Graph;
    /// 
    /// let mut graph = Graph::new();
    /// let ids = vec!["a", "b", "c"];
    /// 
    /// assert_eq!(graph.add_nodes(ids.clone()), 0);
    /// 
    /// assert_eq!(graph.contains_node(&"a"), true);
    /// assert_eq!(graph.contains_node(&"b"), true);
    /// assert_eq!(graph.contains_node(&"c"), true);
    /// 
    /// // Add nodes again, returns 3 because all nodes already exist in the graph.
    /// assert_eq!(graph.add_nodes(ids), 3);
    /// ```
    pub fn add_nodes(&mut self, ids: Vec<T>) -> i32 {
        let mut duplicates = 0;
        for id in ids {
            if !self.add_node(id) {
                duplicates += 1;
            }
        }
        duplicates
    }

    /// Checks if node with `id` is contained inside this graph.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::Graph;
    /// 
    /// let mut graph = Graph::new();
    /// 
    /// graph.add_node("a");
    /// 
    /// assert_eq!(graph.contains_node(&"a"), true);
    /// assert_eq!(graph.contains_node(&"b"), false);
    /// ```
    pub fn contains_node(&self, id: &T) -> bool {
        self.nodes.contains_key(id)
    }

    /// Adds a new edge to the graph that connects two nodes in a single direction from source to target.
    /// For that succeed both nodes are required to be contained within the graph.
    /// 
    /// The `weight` defines "the distance" between the `source` and `target` nodes.
    /// 
    /// Returns an [AddEdgeError](enum.AddEdgeError.html) when the edge was not added. The error indicates 
    /// the reason why the edge could not be added to the graph.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::Graph;
    /// use simple_graph_algorithms::AddEdgeError;
    /// 
    /// let mut graph = Graph::new();
    /// 
    /// graph.add_node("a");
    /// graph.add_node("b");
    /// 
    /// assert_eq!(graph.add_edge(1, &"a", &"b"), Ok(()));
    /// 
    /// // Errors because node "c" is missing from the graph
    /// assert_eq!(graph.add_edge(1, &"c", &"b"), Err(AddEdgeError::SourceMissing));
    /// 
    /// // Errors because node "d" is missing from the graph
    /// assert_eq!(graph.add_edge(1, &"a", &"d"), Err(AddEdgeError::TargetMissing));
    /// 
    /// // Errors because nodes "c" and  "d" are missing from the graph
    /// assert_eq!(graph.add_edge(1, &"c", &"d"), Err(AddEdgeError::EitherMissing));
    /// ```
    pub fn add_edge(&mut self, weight: i32, source: &T, target: &T) -> Result<(), AddEdgeError> {
        if !self.nodes.contains_key(source) && !self.nodes.contains_key(target) {
            return Err(AddEdgeError::EitherMissing);
        } else if !self.nodes.contains_key(source) {
            return Err(AddEdgeError::SourceMissing);
        } else if !self.nodes.contains_key(target) {
            return Err(AddEdgeError::TargetMissing);
        }
        let parent = Rc::clone(&self.nodes.get(source).unwrap());
        let target = Rc::clone(&self.nodes.get(target).unwrap());
        self.nodes.get(source).unwrap().borrow_mut().edges.push(Edge::new(weight, parent, target));
        Ok(())
    }

    /// Adds a new edge to the graph that connects two nodes in both directions.
    /// For that to succeed both nodes are required to be contained within the graph.
    /// 
    /// The `weight` defines "the distance" between the `source` and `target` nodes.
    /// 
    /// Returns an [AddEdgeError](enum.AddEdgeError.html) when the edge was not added. The error indicates 
    /// the reason why the edge could not be added to the graph.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::Graph;
    /// use simple_graph_algorithms::AddEdgeError;
    /// 
    /// let mut graph = Graph::new();
    /// 
    /// graph.add_node("a");
    /// graph.add_node("b");
    /// 
    /// assert_eq!(graph.add_double_edge(1, &"a", &"b"), Ok(()));
    /// 
    /// // Errorsid because node "c" is missing from the graph
    /// assert_eq!(graph.add_double_edge(1, &"c", &"b"), Err(AddEdgeError::SourceMissing));
    /// 
    /// // Errors because node "d" is missing from the graph
    /// assert_eq!(graph.add_double_edge(1, &"a", &"d"), Err(AddEdgeError::TargetMissing));
    /// 
    /// // Errors because nodes "c" and  "d" are missing from the graph
    /// assert_eq!(graph.add_double_edge(1, &"c", &"d"), Err(AddEdgeError::EitherMissing));
    /// ```
    pub fn add_double_edge(&mut self, weight: i32, source: &T, target: &T) -> Result<(), AddEdgeError> {
        if !self.nodes.contains_key(source) && !self.nodes.contains_key(target) {
            return Err(AddEdgeError::EitherMissing);
        } else if !self.nodes.contains_key(source) {
            return Err(AddEdgeError::SourceMissing);
        } else if !self.nodes.contains_key(target) {
            return Err(AddEdgeError::TargetMissing);
        }
        let parent = Rc::clone(&self.nodes.get(source).unwrap());
        let destination = Rc::clone(&self.nodes.get(target).unwrap());
        self.nodes.get(source).unwrap().borrow_mut().edges.push(Edge::new(weight, parent.clone(), destination.clone()));
        self.nodes.get(target).unwrap().borrow_mut().edges.push(Edge::new(weight, destination, parent));
        Ok(())
    }


    /// Checks if the graph contains an edge from node with `source_id` to node with `target_id`.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::Graph;
    /// 
    /// let mut graph = Graph::new();
    /// 
    /// graph.add_node("a");
    /// graph.add_node("b");
    /// graph.add_edge(1, &"a", &"b");
    /// 
    /// assert_eq!(graph.contains_edge(&"a", &"b"), true);
    /// assert_eq!(graph.contains_edge(&"c", &"d"), false);
    /// ```
    pub fn contains_edge(&self, source_id: &T, target_id: &T) -> bool {
        if !self.nodes.contains_key(source_id) {
            return false;
        }
        for edge in &self.nodes.get(source_id).unwrap().borrow().edges {
            if &edge.target.borrow().id == target_id {
                return true;
            }
        }
        false
    }    

    /// Resets the distance of each node in the graph back to `i32::MAX` and resets the shortest path string.
    /// 
    /// Is called each time before a pathfinding algorithm is run.
    fn reset_nodes(&mut self) {
        for (_, node) in self.nodes.iter_mut() {
            node.borrow_mut().distance = i32::MAX;
            node.borrow_mut().shortest_path = Vec::new();
        }
    }

    /// Returns the size of this graph, determined by the amount of nodes contained.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::Graph;
    /// 
    /// let mut graph = Graph::new();
    /// 
    /// graph.add_node("a");
    /// graph.add_node("b");
    /// 
    /// assert_eq!(graph.size(), 2);
    /// ```
    pub fn size(&self) -> usize {
        self.nodes.len()
    }

    /// Clears the graph, removing all nodes. Keeps the allocated memory for reuse.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::Graph;
    /// 
    /// let mut graph = Graph::new();
    /// 
    /// graph.add_node("a");
    /// graph.add_node("b");
    /// 
    /// assert_eq!(graph.size(), 2);
    /// 
    /// graph.clear();
    /// 
    /// assert_eq!(graph.size(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.nodes.clear();
    }

}

impl<T: Display> Display for Graph<T> {
    /// Formats the graph to show all edges between nodes
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut graph = String::new();
        graph.push_str(&format!("{:13} | {:08} | edges\n", "id", "distance"));
        graph.push_str("--------------------------------------------------------------------\n");
        for (_, node) in &self.nodes {
            let id = &node.borrow().id;
            let distance = node.borrow().distance;
            if distance != i32::MAX {
                graph.push_str(&format!("{:13} | {:8} | ", id, distance));
            } else {
                graph.push_str(&format!("{:13} | {:8} | ", id, ""));
            }
            for edge in &node.borrow().edges {
                graph.push_str(&format!("(--{}-> {})", edge.weight, edge.target.borrow().id));
            }
            graph.push('\n');
        }
        write!(f, "{}", graph)
    }
}

#[cfg(test)]
mod tests {
    use crate::Graph;

    #[test]
    fn test_node() {
        let graph = simple_graph();
        assert!(graph.contains_node(&"a"));
        assert!(graph.contains_node(&"b"));
    }

    #[test]
    fn test_add_nodes() {
        let mut graph = Graph::new();
        let vec = vec!["a", "b", "c"];
        assert_eq!(graph.add_nodes(vec.clone()), 0);
        assert_eq!(graph.add_nodes(vec), 3);

        let vec = vec!["c", "d", "e"];
        assert_eq!(graph.add_nodes(vec), 1);
    }

    #[test]
    fn test_add_edge() {
        let mut graph = simple_graph();
        assert_eq!(graph.add_edge(1, &"a", &"b"), Ok(()));
        assert!(graph.contains_edge(&"a", &"b"));
        assert!(!graph.contains_edge(&"b", &"a"));
    }

    #[test]
    fn test_add_double_edge() {
        let mut graph = simple_graph();
        assert_eq!(graph.add_double_edge(1, &"a", &"b"), Ok(()));
        assert!(graph.contains_edge(&"a", &"b"));
        assert!(graph.contains_edge(&"b", &"a"));
    }

    #[test]
    fn test_add_edge_errors() {
        let mut graph = simple_graph();
        assert_eq!(graph.add_edge(1, &"c", &"b"), Err(crate::AddEdgeError::SourceMissing));
        assert_eq!(graph.add_edge(1, &"b", &"d"), Err(crate::AddEdgeError::TargetMissing));
        assert_eq!(graph.add_edge(1, &"c", &"d"), Err(crate::AddEdgeError::EitherMissing));
    }

    #[test]
    fn test_add_double_edge_errors() {
        let mut graph = simple_graph();
        assert_eq!(graph.add_double_edge(1, &"c", &"b"), Err(crate::AddEdgeError::SourceMissing));
        assert_eq!(graph.add_double_edge(1, &"b", &"d"), Err(crate::AddEdgeError::TargetMissing));
        assert_eq!(graph.add_double_edge(1, &"c", &"d"), Err(crate::AddEdgeError::EitherMissing));
    }

    fn simple_graph() -> Graph<&'static str> {
        let mut graph = Graph::new();
        graph.add_node("a");
        graph.add_node("b");
        graph
    }
}
