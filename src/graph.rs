use std::{fmt::{Display, Debug}, rc::Rc, cell::RefCell, hash::Hash, collections::HashMap};

use crate::{Node, Edge, Graph, AddEdgeError, ShortestPath};

// Node implementations

impl<T: Display + Eq + Clone> Node<T> {
    
    /// Creates a new node with id `id`.
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

    /// Adds a new node with id `id` to the graph.
    /// 
    /// The `id` is the unique identifier of this node,
    /// it is used to adddress this node in all other functions.
    /// 
    /// Return value indicates if the node was added to
    /// the graph or if a node with this id already exists.
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

    /// Checks if node with id `id` is contained inside this graph.
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
    /// For that to succeed both nodes are required to be contained within the graph.
    /// 
    /// The `weight` defines "the distance" between the nodes with ids `source_id` and `target_id`.
    /// 
    /// Returns `true` if the edge was added, if `false` is returned either node is missing in the graph.
    /// 
    /// Use [Graph::try_add_edge(&mut self, i32, &T, &T)](struct.Graph.html#method.try_add_edge) instead if you need to know why the edge could not be added.
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
    /// assert_eq!(graph.add_edge(1, &"a", &"b"), true);
    /// assert_eq!(graph.add_edge(1, &"c", &"d"), false);
    /// ```
    pub fn add_edge(&mut self, weight: i32, source_id: &T, target_id: &T) -> bool {
        if !self.nodes.contains_key(source_id) && !self.nodes.contains_key(target_id) {
            return false;
        }
        let parent = Rc::clone(&self.nodes.get(source_id).unwrap());
        let target = Rc::clone(&self.nodes.get(target_id).unwrap());
        self.nodes.get(source_id).unwrap().borrow_mut().edges.push(Edge::new(weight, parent, target));
        return true;
    }

    /// Tries to add a new edge to the graph that connects two nodes in a single direction from source to target.
    /// 
    /// The `weight` defines "the distance" between the nodes with ids `source_id` and `target_id`.
    /// 
    /// Returns `Ok(())` when the edge was added or an [AddEdgeError](enum.AddEdgeError.html)
    /// containing the reason why the edge was not added.
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
    /// assert_eq!(graph.try_add_edge(1, &"a", &"b"), Ok(()));
    /// 
    /// // Errors because node "c" is missing from the graph
    /// assert_eq!(graph.try_add_edge(1, &"c", &"b"), Err(AddEdgeError::SourceMissing));
    /// 
    /// // Errors because node "d" is missing from the graph
    /// assert_eq!(graph.try_add_edge(1, &"a", &"d"), Err(AddEdgeError::TargetMissing));
    /// 
    /// // Errors because nodes "c" and  "d" are missing from the graph
    /// assert_eq!(graph.try_add_edge(1, &"c", &"d"), Err(AddEdgeError::EitherMissing));
    /// ```
    pub fn try_add_edge(&mut self, weight: i32, source_id: &T, target_id: &T) -> Result<(), AddEdgeError> {//TODO rename variant EitherMissing into BothMissing
        if !self.nodes.contains_key(source_id) && !self.nodes.contains_key(target_id) {
            return Err(AddEdgeError::EitherMissing);
        } else if !self.nodes.contains_key(source_id) {
            return Err(AddEdgeError::SourceMissing);
        } else if !self.nodes.contains_key(target_id) {
            return Err(AddEdgeError::TargetMissing);
        }
        let parent = Rc::clone(&self.nodes.get(source_id).unwrap());
        let target = Rc::clone(&self.nodes.get(target_id).unwrap());
        self.nodes.get(source_id).unwrap().borrow_mut().edges.push(Edge::new(weight, parent, target));
        Ok(())
    }

    /// Adds a new edge to the graph that connects two nodes in a both directions.
    /// For that to succeed both nodes are required to be contained within the graph.
    /// 
    /// The `weight` defines "the distance" between the nodes with ids `source_id` and `target_id`.
    /// 
    /// Returns `true` if the edge was added, if `false` is returned either node is missing in the graph.
    /// 
    /// Use [Graph::try_add_double_edge(&mut self, i32, &T, &T)](struct.Graph.html#method.try_add_double_edge) instead if you need to know why the edge could not be added.
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
    /// assert_eq!(graph.add_double_edge(1, &"a", &"b"), true);
    /// assert_eq!(graph.add_double_edge(1, &"c", &"d"), false);
    /// ```
    pub fn add_double_edge(&mut self, weight: i32, source_id: &T, target: &T) -> bool {
        if !self.nodes.contains_key(source_id) && !self.nodes.contains_key(target) {
            return false;
        }
        let parent = Rc::clone(&self.nodes.get(source_id).unwrap());
        let destination = Rc::clone(&self.nodes.get(target).unwrap());
        self.nodes.get(source_id).unwrap().borrow_mut().edges.push(Edge::new(weight, parent.clone(), destination.clone()));
        self.nodes.get(target).unwrap().borrow_mut().edges.push(Edge::new(weight, destination, parent));
        true
    }

    /// Tries to add a new edge to the graph that connects two nodes in a single direction from source to target.
    /// 
    /// The `weight` defines "the distance" between the nodes with ids `source_id` and `target_id`.
    /// 
    /// Returns `Ok(())` when the edge was added or an [AddEdgeError](enum.AddEdgeError.html)
    /// containing the reason why the edge was not added.
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
    /// assert_eq!(graph.try_add_double_edge(1, &"a", &"b"), Ok(()));
    /// 
    /// // Errors because node "c" is missing from the graph
    /// assert_eq!(graph.try_add_double_edge(1, &"c", &"b"), Err(AddEdgeError::SourceMissing));
    /// 
    /// // Errors because node "d" is missing from the graph
    /// assert_eq!(graph.try_add_double_edge(1, &"a", &"d"), Err(AddEdgeError::TargetMissing));
    /// 
    /// // Errors because nodes "c" and  "d" are missing from the graph
    /// assert_eq!(graph.try_add_double_edge(1, &"c", &"d"), Err(AddEdgeError::EitherMissing));
    /// ```
    pub fn try_add_double_edge(&mut self, weight: i32, source_id: &T, target_id: &T) -> Result<(), AddEdgeError> {
        if !self.nodes.contains_key(source_id) && !self.nodes.contains_key(target_id) {
            return Err(AddEdgeError::EitherMissing);
        } else if !self.nodes.contains_key(source_id) {
            return Err(AddEdgeError::SourceMissing);
        } else if !self.nodes.contains_key(target_id) {
            return Err(AddEdgeError::TargetMissing);
        }
        let parent = Rc::clone(&self.nodes.get(source_id).unwrap());
        let destination = Rc::clone(&self.nodes.get(target_id).unwrap());
        self.nodes.get(source_id).unwrap().borrow_mut().edges.push(Edge::new(weight, parent.clone(), destination.clone()));
        self.nodes.get(target_id).unwrap().borrow_mut().edges.push(Edge::new(weight, destination, parent));
        Ok(())
    }

    /// Checks if the graph contains an edge from node with id `source_id` to node with id `target_id`.
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

    /// Constructs a graph from a list of instructions. This is meant to be used by reading the instructions form a file.
    /// 
    /// The order in which the instructions are stored in the vector does not matter.
    /// 
    /// # Instructions
    /// 
    /// ## Nodes
    /// 
    /// ```txt
    /// node: LABEL1
    /// ```
    /// This declares a new node labeled `LABEL1`
    /// 
    /// ## Edge
    /// 
    /// ```txt
    /// edge: LABEL1 WEIGHT LABEL2
    /// ```
    /// This adds an edge from `LABEL1` to `LABEL2` with `WEIGHT`
    /// 
    /// ```txt
    /// double_edge: LABEL1 WEIGHT LABEL2
    /// ```
    /// This adds a double edge between `LABEL1` and `LABEL2` with `WEIGHT`
    /// 
    /// # Example
    /// 
    /// ```rust
    /// //use lmh01_pathfinding::algorithms::dijkstra;
    /// use simple_graph_algorithms::Graph;
    /// 
    /// // This lines vector should ideally constructed by parsing a file, below insertions are just for demonstration.
    /// let mut lines = Vec::new();
    /// lines.push(String::from("node: a"));
    /// lines.push(String::from("node: b"));
    /// lines.push(String::from("node: c"));
    /// lines.push(String::from("node: d"));
    /// lines.push(String::from("edge: a 7 b"));
    /// lines.push(String::from("edge: a 4 c"));
    /// lines.push(String::from("edge: b 2 d"));
    /// lines.push(String::from("edge: c 9 d"));
    /// lines.push(String::from("edge: c 2 b"));
    /// lines.push(String::from("double_edge: a 1 d"));
    /// let mut graph = Graph::<String>::from_instructions(&lines);
    /// //assert_eq!(1, dijkstra(&mut graph, &String::from("a"), &String::from("d")).unwrap_or(-1));
    /// ```
    pub fn from_instructions(instructions: &Vec<String>) -> Graph<String> {
        // Stores all node labels of nodes that should be added to the graph
        let mut node_labels = Vec::new();
        // Stores all edges that should be added to the graph, (WEIGHT, LABEL1, LABEL2, double)
        let mut edges: Vec<(i32, String, String, bool)> = Vec::new();

        // Parse lines
        for line in instructions {
            let split: Vec<&str> = line.split(' ').collect();
            match split[0].to_lowercase().as_str() {
                "node:" => {
                    node_labels.push(String::from(split[1]));
                },
                "edge:" => {
                    edges.push((split[2].parse::<i32>().expect("Unable to parse edge weight!"), String::from(split[1]), String::from(split[3]), false));
                },
                "double_edge:" => {
                    edges.push((split[2].parse::<i32>().expect("Unable to parse edge weight!"), String::from(split[1]), String::from(split[3]), true));
                },
                _ => (),
            }
        }

        let mut graph = Graph::new();

        // Add nodes to graph
        for label in node_labels {
            graph.add_node(label.clone());
        }
        // Add edges to graph
        for edge in edges {
            if edge.3 {
                graph.add_double_edge(edge.0, &edge.1, &edge.2);
            } else {
                graph.add_edge(edge.0, &edge.1, &edge.2);
            }
        }

        graph
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

impl<T: Display + Clone + Eq + Hash + From<String>> From<&Vec<Vec<i32>>> for Graph<T> {

    /// Create a graph from a 2D vector containing i32.
    /// 
    /// The i32 value is the edge weight of each edge leading into that node.
    /// # Example
    /// ```
    /// use simple_graph_algorithms::Graph;
    /// 
    /// // Prepare example vector
    /// let mut vec: Vec<Vec<i32>> = Vec::new();
    /// let vec_inner_1 = vec![3, 4, 5];
    /// let vec_inner_2 = vec![1, 2, 3];
    /// let vec_inner_3 = vec![1, 8, 2];
    /// vec.push(vec_inner_1);
    /// vec.push(vec_inner_2);
    /// vec.push(vec_inner_3);
    /// 
    /// // Create graph from example vector
    /// let mut graph = Graph::<String>::from(&vec);
    /// 
    /// // Run dijkstra's algorithm
    /// //assert_eq!(8, dijkstra(&mut graph, &String::from("[0|0]"), &String::from("[2|2]")).unwrap_or(-1));
    /// ```
    fn from(value: &Vec<Vec<i32>>) -> Self {
        let mut graph: Graph<T> = Graph::new();
        for (i_y, y) in value.iter().enumerate() {
            for (i_x, _x) in y.iter().enumerate() {
graph.add_node(String::from(format!("[{}|{}]", i_x, i_y)).into());
            }
        }
        for (i_y, y) in value.iter().enumerate() {
            let max_x_size = y.len();
            for (i_x, x) in y.iter().enumerate() {
                for neighbor in neighbor_positions((i_x, i_y), max_x_size, value.len()) {
                    graph.add_edge(*x, &format!("[{}|{}]", neighbor.0, neighbor.1).into(), &format!("[{}|{}]", i_x, i_y).into());
                }
            }
        }
        graph
    }
}

/// Returns the neighboring positions for a position in a 2D graph.
/// 
/// # Example
/// ```ignore
/// let neighbors = neighbor_positions((2,2), 10, 10);
/// assert_eq!((1, 2), neighbors[0]);
/// assert_eq!((2, 1), neighbors[1]);
/// assert_eq!((3, 2), neighbors[2]);
/// assert_eq!((2, 3), neighbors[3]);
/// ```
fn neighbor_positions(pos: (usize, usize), max_x_size: usize, max_y_size: usize) -> Vec<(usize, usize)> {
    let mut positions = Vec::new();
    if pos.0 != 0 {
        positions.push((pos.0-1, pos.1));
    }
    if pos.1 != 0 {
        positions.push((pos.0, pos.1-1));
    }
    if pos.0 != max_x_size-1 {
        positions.push((pos.0+1, pos.1));
    }
    if pos.1 != max_y_size-1 {
        positions.push((pos.0, pos.1+1));
    }
    positions
}

#[cfg(test)]
mod tests {
    use crate::{Graph, algorithms::dijkstra, graph_1, graph_2};

    fn simple_graph() -> Graph<&'static str> {
        let mut graph = Graph::new();
        graph.add_node("a");
        graph.add_node("b");
        graph
    }

    #[test]
    fn node_test() {
        let graph = simple_graph();
        assert!(graph.contains_node(&"a"));
        assert!(graph.contains_node(&"b"));
    }

    #[test]
    fn add_nodes_test() {
        let mut graph = Graph::new();
        let vec = vec!["a", "b", "c"];
        assert_eq!(graph.add_nodes(vec.clone()), 0);
        assert_eq!(graph.add_nodes(vec), 3);

        let vec = vec!["c", "d", "e"];
        assert_eq!(graph.add_nodes(vec), 1);
    }

    #[test]
    fn add_edge_test() {
        let mut graph = simple_graph();
        assert_eq!(graph.add_edge(1, &"a", &"b"), true);
        assert_eq!(graph.add_edge(1, &"c", &"d"), false);
        assert!(graph.contains_edge(&"a", &"b"));
        assert!(!graph.contains_edge(&"b", &"a"));
    }

    #[test]
    fn add_double_edge_test() {
        let mut graph = simple_graph();
        assert_eq!(graph.add_double_edge(1, &"a", &"b"), true);
        assert!(graph.contains_edge(&"a", &"b"));
        assert!(graph.contains_edge(&"b", &"a"));
    }

    #[test]
    fn try_add_edge_errors_test() {
        let mut graph = simple_graph();
        assert_eq!(graph.try_add_edge(1, &"c", &"b"), Err(crate::AddEdgeError::SourceMissing));
        assert_eq!(graph.try_add_edge(1, &"b", &"d"), Err(crate::AddEdgeError::TargetMissing));
        assert_eq!(graph.try_add_edge(1, &"c", &"d"), Err(crate::AddEdgeError::EitherMissing));
    }

    #[test]
    fn try_add_double_edge_errors_test() {
        let mut graph = simple_graph();
        assert_eq!(graph.try_add_double_edge(1, &"c", &"b"), Err(crate::AddEdgeError::SourceMissing));
        assert_eq!(graph.try_add_double_edge(1, &"b", &"d"), Err(crate::AddEdgeError::TargetMissing));
        assert_eq!(graph.try_add_double_edge(1, &"c", &"d"), Err(crate::AddEdgeError::EitherMissing));
    }

    #[test]
    fn graph_from_vec_vec_i32_test() {
        let mut vec: Vec<Vec<i32>> = Vec::new();
        let vec_inner_1 = vec![3, 4, 5];
        let vec_inner_2 = vec![1, 2, 3];
        let vec_inner_3 = vec![1, 8, 2];
        vec.push(vec_inner_1);
        vec.push(vec_inner_2);
        vec.push(vec_inner_3);
     
        let mut graph = Graph::<String>::from(&vec);
        assert_eq!(graph.size(), 9);
        assert_eq!(graph.contains_node(&String::from("[0|0]")), true);
        assert_eq!(graph.contains_node(&String::from("[3|3]")), false);
        assert_eq!(graph.contains_edge(&String::from("[1|1]"), &String::from("[0|1]")), true);
        assert_eq!(graph.contains_edge(&String::from("[1|1]"), &String::from("[0|0]")), false);
    }

    #[test]
    fn from_instructions_test() {
        let mut lines = Vec::new();
        lines.push(String::from("node: a"));
        lines.push(String::from("node: b"));
        lines.push(String::from("node: c"));
        lines.push(String::from("node: d"));
        lines.push(String::from("edge: a 7 b"));
        lines.push(String::from("edge: a 4 c"));
        lines.push(String::from("edge: b 2 d"));
        lines.push(String::from("edge: c 9 d"));
        lines.push(String::from("edge: c 2 b"));
        let mut graph = Graph::<String>::from_instructions(&lines);
        assert_eq!(graph.size(), 4);
        assert_eq!(graph.contains_edge(&String::from("a"), &String::from("c")), true);
        let spt = dijkstra(&mut graph, &String::from("a")).unwrap();
        assert_eq!(spt.shortest_distance(&String::from("d")), Some(8));
    }
}
