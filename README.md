[![Current Crates.io Version](https://img.shields.io/crates/v/simple_graph_algorithms.svg)](https://crates.io/crates/simple_graph_algorithms)
[![Current documentation](https://img.shields.io/docsrs/simple_graph_algorithms/latest)](https://docs.rs/simple_graph_algorithms/)


# simple_graph_algorithms

This library aims to provide simple to use implementations for various algorithms run on graphs.

## Algorithms

The following algorithms are currently implemented in this library:

- **[Dijkstra's algorithm](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm)**
- **[Bellman-Ford algorithm](https://en.wikipedia.org/wiki/Bellman%E2%80%93Ford_algorithm)**

## Documentation

The documentation is hosted [here on docs.rs](https://docs.rs/simple_graph_algorithms/).

## Changelog

The changelog can be found [here](changelog.md)

## Performance

| Algorithm | Mean time over 100 runs on a graph with 10,000 nodes and 39,600 edges|
| - | - |
| Bellman-Ford | 2.1883 s |
| Dijkstra | 52.3155 ms |

These tests where performed on a `Ryzen 5 7600x`. Performance might be slower on older hardware.

To run these tests yourself type `cargo bench`, a full run will take a few minutes.