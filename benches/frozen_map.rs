use std::collections::HashMap;

use criterion::{black_box, Criterion, criterion_group, criterion_main};

use frozen_collections::FrozenMap;

fn integer_keys(c: &mut Criterion) {
    let mut group = c.benchmark_group("Integer Keys");

    group.bench_function("FrozenMap<u32, _> (hash integer map)", |b| {
        let map = FrozenMap::<u32, u32>::from([(0, 1), (2, 3), (4, 5), (6, 7), (8, 9)]);
        b.iter(|| {
            for i in 0..10 {
                _ = black_box(map.get(&i));
            }
        });
    });

    group.bench_function("FrozenMap<u32, _> (integer range map)", |b| {
        let map = FrozenMap::<u32, u32>::from([(0, 0), (1, 1), (2, 2), (3, 3), (4, 4)]);
        b.iter(|| {
            for i in 0..10 {
                _ = black_box(map.get(&i));
            }
        });
    });

    group.bench_function("FrozenMap<i32, _> (hash map)", |b| {
        let map = FrozenMap::<i32, i32>::from([(0, 1), (2, 3), (4, 5), (6, 7), (8, 9)]);
        b.iter(|| {
            for i in 0..10 {
                _ = black_box(map.get(&i));
            }
        });
    });

    let map = HashMap::from([(0, 1), (2, 3), (4, 5), (6, 7), (8, 9)]);
    group.bench_function("HashMap", |b| {
        b.iter(|| {
            for i in 0..10 {
                _ = black_box(map.get(&i));
            }
        });
    });

    group.finish();
}
criterion_group!(benches, integer_keys,);
criterion_main!(benches);
