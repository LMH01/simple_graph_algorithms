//! # Recognized instructions
//! 
//! | Instruction | Description |
//! | - | - |
//! | node: NODE_LABEL | Used to add a node to the graph that is labeled `NODE_LABEL`|
//! | edge: SOURCE_NODE_LABEL WEIGHT TARGET_NODE_LABEL| Used to create an edge that leads from node labeled `SOURCE_NODE_LABEL` to node labeled `TARGET_NODE_LABEL` with a weight of `WEIGHT` |
//! | double_edge: SOURCE_NODE_LABEL WEIGHT TARGET_NODE_LABEL| Used to create a double edge between node labeled `SOURCE_NODE_LABEL` and node labeled `TARGET_NODE_LABEL` with a weight of `WEIGHT` |
//! 
//! # Example
//! ```
//! use simple_graph_algorithms::{Graph, instruction::Instructions};
//! # fn main() -> Result<(), String> {
//! 
//! // Create a vector that contains instructions.
//! // The idea is that these instructions are read from a file).
//! let mut instruction_strings = Vec::new();
//! instruction_strings.push("node: a");
//! instruction_strings.push("node: b");
//! instruction_strings.push("node: c");
//! instruction_strings.push("node: d");
//! instruction_strings.push("edge: a 3 b");
//! instruction_strings.push("edge: a 4 c");
//! instruction_strings.push("double_edge: b 2 d");
//! instruction_strings.push("edge: c 2 a");
//! instruction_strings.push("edge: c 5 d");
//! instruction_strings.push("edge: b -1 a");
//! 
//! // Create parsed instructions from the instruction strings.
//! let instructions: Instructions<String> = Instructions::try_from(&instruction_strings)?;
//! 
//! // Construct graph from instructions.
//! let mut graph = Graph::from(instructions);
//! 
//! // Do something with the graph...
//! # Ok(())
//! # }
//! ```
use std::{fmt::Display, hash::Hash};

use crate::Graph;

#[cfg(feature = "from_instruction")]
#[derive(Debug, PartialEq)]
enum Instruction<T: Display + Clone> {
    AddNode(T),
    AddEdge(i32, T, T),
    AddDoubleEdge(i32, T, T),
}

/// A list of instructions used to construct a graph.
#[cfg(feature = "from_instruction")]
#[derive(Debug, PartialEq)]
pub struct Instructions<T: Display + Clone> {
    instructions: Vec<Instruction<T>>,
}

#[cfg(feature = "from_instruction")]
impl<T: Display + Clone + From<String>> TryFrom<&Vec<&str>> for Instructions<T> {
    type Error = String;

    /// Tries to parse each line of the string as an instruction and
    /// returns a list of instructions when the parsing was successful.
    /// 
    /// When an instruction could not be parsed,
    /// the returning error contains the offending instruction.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::{Graph, instruction::Instructions};
    /// # fn main() -> Result<(), String> {
    /// 
    /// // Create a vector that contains instructions (this should normally be read from a file).
    /// let mut instruction_strings = Vec::new();
    /// instruction_strings.push("node: a");
    /// instruction_strings.push("node: b");
    /// instruction_strings.push("node: c");
    /// instruction_strings.push("node: d");
    /// instruction_strings.push("edge: a 3 b");
    /// instruction_strings.push("edge: a 4 c");
    /// instruction_strings.push("double_edge: b 2 d");
    /// instruction_strings.push("edge: c 2 a");
    /// instruction_strings.push("edge: c 5 d");
    /// instruction_strings.push("edge: b -1 a");
    /// 
    /// // Create parsed instructions from the instruction strings.
    /// let instructions: Instructions<String> = Instructions::try_from(&instruction_strings)?;
    /// 
    /// // Construct graph from instructions.
    /// let mut graph = Graph::from(instructions);
    /// 
    /// // Do something with the graph...
    /// # Ok(())
    /// # }
    /// ```
    fn try_from(value: &Vec<&str>) -> Result<Self, Self::Error> {
        let mut instructions = Vec::new();

        // Parse lines
        for line in value {
            try_from_vec_string(line, &mut instructions)?;
        }
        Ok(Instructions { instructions, })
    }
}

#[cfg(feature = "from_instruction")]
impl<T: Display + Clone + From<String>> TryFrom<&Vec<String>> for Instructions<T> {
    type Error = String;

    /// Tries to parse each line of the string as an instruction and
    /// returns a list of instructions when the parsing was successful.
    /// 
    /// When an instruction could not be parsed,
    /// the returning error contains the offending instruction.
    /// 
    /// # Example
    /// ```
    /// use simple_graph_algorithms::{Graph, instruction::Instructions};
    /// # fn main() -> Result<(), String> {
    /// 
    /// // Create a vector that contains instructions (this should normally be read from a file).
    /// let mut instruction_strings = Vec::new();
    /// instruction_strings.push(String::from("node: a"));
    /// instruction_strings.push(String::from("node: b"));
    /// instruction_strings.push(String::from("node: c"));
    /// instruction_strings.push(String::from("node: d"));
    /// instruction_strings.push(String::from("edge: a 3 b"));
    /// instruction_strings.push(String::from("edge: a 4 c"));
    /// instruction_strings.push(String::from("double_edge: b 2 d"));
    /// instruction_strings.push(String::from("edge: c 2 a"));
    /// instruction_strings.push(String::from("edge: c 5 d"));
    /// instruction_strings.push(String::from("edge: b -1 a"));
    /// 
    /// // Create parsed instructions from the instruction strings.
    /// let instructions: Instructions<String> = Instructions::try_from(&instruction_strings)?;
    /// 
    /// // Construct graph from instructions.
    /// let mut graph = Graph::from(instructions);
    /// 
    /// // Do something with the graph...
    /// # Ok(())
    /// # }
    /// ```
    fn try_from(value: &Vec<String>) -> Result<Self, Self::Error> {
        let mut instructions = Vec::new();

        // Parse lines
        for line in value {
            try_from_vec_string(line, &mut instructions)?;
        }
        Ok(Instructions { instructions, })
    }
}

/// Tries to parse the `line` into an instruction. If successful the instruction is added to the
/// `instructions` vector, if it can not be parsed an error is returned containing the offending string.
fn try_from_vec_string<T: Display + Clone + From<String>>(line: &str, instructions: &mut Vec<Instruction<T>>) -> Result<(), String> {
    let split: Vec<&str> = line.split(' ').collect();
    match split[0].to_lowercase().as_str() {
        "node:" => {
            instructions.push(Instruction::AddNode(T::from(split[1].to_string())));
        },
        "edge:" => {
            match split[2].parse::<i32>() {
                Ok(weight) => {
                    instructions.push(Instruction::AddEdge(weight, T::from(split[1].to_string()), T::from(split[3].to_string())));
                },
                Err(_) => return Err(String::from(line)),
            };
        },
        "double_edge:" => {
            if let Ok(weight) = split[2].parse::<i32>() {
                instructions.push(Instruction::AddDoubleEdge(weight, T::from(split[1].to_string()), T::from(split[3].to_string())));
            }
        },
        "" => (),
        _ => return Err(String::from(line)),
    }
    Ok(())
}

#[cfg(feature = "from_instruction")]
impl<T: Display + Clone + Eq + Hash> From<Instructions<T>> for Graph<T> {
    /// Constructs a graph from a list of instructions.
    /// 
    /// See [here](instruction/index.html) for further information.
    fn from(value: Instructions<T>) -> Self {
        let mut graph = Graph::new();
        for instruction in value.instructions {
            match instruction {
                Instruction::AddNode(id) => graph.add_node(id),
                Instruction::AddEdge(weight, source, target) => graph.add_edge(weight, &source, &target),
                Instruction::AddDoubleEdge(weight, source, target) => graph.add_double_edge(weight, &source, &target),
            };
        }
        graph
    }
}

#[cfg(test)]
mod tests {
    use crate::{Graph, algorithms::{bellman_ford, dijkstra}};

    use super::Instructions;


    #[test]
    fn graph_from_instructions_string_test() {
        let mut instructions = Vec::new();
        instructions.push(String::from("node: a"));
        instructions.push(String::from("node: b"));
        instructions.push(String::from("node: c"));
        instructions.push(String::from("node: d"));
        instructions.push(String::from("edge: a 3 b"));
        instructions.push(String::from("edge: a 4 c"));
        instructions.push(String::from("double_edge: b 2 d"));
        instructions.push(String::from("edge: c 2 a"));
        instructions.push(String::from("edge: c 5 d"));
        instructions.push(String::from("edge: b -1 a"));
        let instructions: Result<Instructions<String>, String> = Instructions::try_from(&instructions);
        assert!(instructions.is_ok());
        let mut graph = Graph::from(instructions.unwrap());
        println!("{graph}");
        let spt = bellman_ford(&mut graph, &String::from("a"));
        assert!(spt.is_ok());
        println!("{}", spt.as_ref().unwrap().shortest_path(&String::from("d")).unwrap());
        assert_eq!(spt.unwrap().shortest_distance(&String::from("d")), Some(5));    
    }

    #[test]
    fn graph_from_instructions_string_test_2() {
        let mut instructions = Vec::new();
        instructions.push(String::from("node: a"));
        instructions.push(String::from("node: b"));
        instructions.push(String::from("node: c"));
        instructions.push(String::from("node: d"));
        instructions.push(String::from("edge: a 7 b"));
        instructions.push(String::from("edge: a 4 c"));
        instructions.push(String::from("edge: b 2 d"));
        instructions.push(String::from("edge: c 9 d"));
        instructions.push(String::from("edge: c 2 b"));
        let instructions: Result<Instructions<String>, String> = Instructions::try_from(&instructions);
        assert!(instructions.is_ok());
        let mut graph = Graph::from(instructions.unwrap());
        assert_eq!(graph.size(), 4);
        assert_eq!(graph.contains_edge(&String::from("a"), &String::from("c")), true);
        let spt = dijkstra(&mut graph, &String::from("a")).unwrap();
        assert_eq!(spt.shortest_distance(&String::from("d")), Some(8));
    }

    #[test]
    fn graph_from_instructions_str_test() {
        let mut instructions = Vec::new();
        instructions.push("node: a");
        instructions.push("node: b");
        instructions.push("node: c");
        instructions.push("node: d");
        instructions.push("edge: a 3 b");
        instructions.push("edge: a 4 c");
        instructions.push("double_edge: b 2 d");
        instructions.push("edge: c 2 a");
        instructions.push("edge: c 5 d");
        instructions.push("edge: b -1 a");
        let instructions: Result<Instructions<String>, String> = Instructions::try_from(&instructions);
        assert!(instructions.is_ok());
        let mut graph = Graph::from(instructions.unwrap());
        println!("{graph}");
        let spt = bellman_ford(&mut graph, &String::from("a"));
        assert!(spt.is_ok());
        println!("{}", spt.as_ref().unwrap().shortest_path(&String::from("d")).unwrap());
        assert_eq!(spt.unwrap().shortest_distance(&String::from("d")), Some(5));
    }

    #[test]
    fn graph_from_instructions_err_test() {
        let mut instructions = Vec::new();
        instructions.push("nodea: a");
        let instructions: Result<Instructions<String>, String> = Instructions::try_from(&instructions);
        assert!(instructions.is_err());
        assert_eq!(instructions, Err(String::from("nodea: a")))
    }

    #[test]
    fn graph_from_instructions_err_test_2() {
        let mut instructions = Vec::new();
        instructions.push("edge: a x b");
        let instructions: Result<Instructions<String>, String> = Instructions::try_from(&instructions);
        assert!(instructions.is_err());
        assert_eq!(instructions, Err(String::from("edge: a x b")))
    }

}