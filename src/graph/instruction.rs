use std::{fmt::Display, hash::Hash};

use crate::Graph;

#[cfg(feature = "from_instruction")]
enum Instruction<T: Display + Clone> {
    AddNode(T),
    AddEdge(i32, T, T),
    AddDoubleEdge(i32, T, T),
}

#[cfg(feature = "from_instruction")]
struct Instructions<T: Display + Clone> {
    instructions: Vec<Instruction<T>>,
}

#[cfg(feature = "from_instruction")]
impl<T: Display + Clone + From<String>> TryFrom<&Vec<String>> for Instructions<T> {
    type Error = String;

    /// Tries to parse each line of the string as instruction
    fn try_from(value: &Vec<String>) -> Result<Self, Self::Error> {//TODO add doc, example + test
        let mut instructions = Vec::new();

        // Parse lines
        for line in value {
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
                        Err(_) => return Err(String::from(split[2])),
                    };
                },
                "double_edge:" => {
                    if let Ok(weight) = split[2].parse::<i32>() {
                        instructions.push(Instruction::AddDoubleEdge(weight, T::from(split[1].to_string()), T::from(split[3].to_string())));
                    }
                },
                _ => (),
            }
        }
        Ok(Instructions { instructions, })
    }
}

#[cfg(feature = "from_instruction")]
impl<T: Display + Clone + Eq + Hash> From<Instructions<T>> for Graph<T> {
    /// Constructs a graph from the list of instructions
    fn from(value: Instructions<T>) -> Self {//TODO Add doc, example + test
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
    use crate::{Graph, algorithms::bellman_ford};

    use super::Instructions;


    #[test]
    fn graph_from_instructions_test() {
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

}