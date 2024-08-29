use std::collections::BTreeMap;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use ds_ext::OrdHashMap;
use rand::Rng;

fn ord_read(map: &mut OrdHashMap<usize, usize>, num_reads: usize) {
    let mut rng = rand::thread_rng();
    let size = map.len();

    for _ in 0..num_reads {
        let n = rng.gen_range(0..size);
        assert!(map.get(&n).is_some()); // make sure the read isn't optimized away
    }
}

fn btree_read(map: &mut BTreeMap<usize, usize>, num_reads: usize) {
    let mut rng = rand::thread_rng();
    let size = map.len();

    for _ in 0..num_reads {
        let n = rng.gen_range(0..size);
        assert!(map.get(&n).is_some()); // make sure the read isn't optimized away
    }
}

fn benchmark_list_vs_vec(c: &mut Criterion) {
    let mut group = c.benchmark_group("RandomRead");

    for size in [10, 100, 1_000, 10_000].iter() {
        let mut map = OrdHashMap::from_iter((0..*size).into_iter().map(|i| (i, i)));
        group.bench_with_input(BenchmarkId::new("OrdHashMap", size), size, |b, i| {
            b.iter(|| ord_read(&mut map, 10_000))
        });

        let mut map = BTreeMap::from_iter((0..*size).into_iter().map(|i| (i, i)));
        group.bench_with_input(BenchmarkId::new("BTreeMap", size), size, |b, i| {
            b.iter(|| btree_read(&mut map, 10_000))
        });
    }

    group.finish();
}

criterion_group!(benches, benchmark_list_vs_vec);
criterion_main!(benches);
