use std::fmt::Display;

enum Instruction<T: Display + Clone> {
    AddNode(T),
    AddEdge(i32, T, T),
    AddDoubleEdge(i32, T, T),
}

struct Instructions<T: Display + Clone> {
    instructions: Vec<Instruction<T>>,
}

impl<T: Display + Clone> From<&Vec<String>> for Instructions<T> {
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
    pub fn from(value: &Vec<String>) -> Instructions<T> {//TODO Remove function from here when from_instructions feature works
        // Stores all node labels of nodes that should be added to the graph
        let mut node_labels = Vec::new();
        // Stores all edges that should be added to the graph, (WEIGHT, LABEL1, LABEL2, double)
        let mut edges: Vec<(i32, String, String, bool)> = Vec::new();

        let mut Instructions = Vec::new();

        // Parse lines
        for line in value {
            let split: Vec<&str> = line.split(' ').collect();
            match split[0].to_lowercase().as_str() {
                "node:" => {
                    Instructions.push(Instruction::AddNode(String::from(split[1])));
                },
                "edge:" => {
                    Instructions.push(Instruction::AddEdge(split[2].parse()::<i32>, String::from(split[1]), String::From(split[3])));
                    //TODO decide if I want to change impl to TryFrom and return with err or if i want to cach it and just not parse ddefective lines
                    // I should do an implementation for TryFrom
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

impl<T: Display + Clone> TryFrom<String> for Instructions<T> {
    type Error = InstructionParseError;

    /// Tries to parse each line of the string as instruction
    fn try_from(value: String) -> Result<Self, Self::Error> {
        todo!()
    }
}