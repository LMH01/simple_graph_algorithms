use criterion::{black_box, criterion_group, criterion_main, Criterion};
use simple_graph_algorithms::{Graph, algorithms::{dijkstra, bellman_ford}};

fn criterion_benchmark(c: &mut Criterion) {
    let mut graph = graph();
    c.bench_function("dijkstra 100x100", |b| b.iter(|| {
        dijkstra(&mut graph, &String::from("[0|0]")).unwrap();
    }));
    c.bench_function("bellman-ford 100x100", |b| b.iter(|| {
        bellman_ford(&mut graph, &String::from("[0|0]")).unwrap();
    }));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);

fn graph() -> Graph<String> {
    let mut vec = Vec::new();
    let node_weights = vec![7, 2, 4, 10, 5, 9, 3, 1, 6, 8];
    for i in 1..=100 {
        let mut inner_vec = Vec::new();
        for j in 1..=100 {
            inner_vec.push(node_weights[i*j%10]);
        }
        vec.push(inner_vec);
    }
    Graph::from(&vec)
}