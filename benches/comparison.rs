use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};

use ds_ext::List;

fn list_from_iter(size: u64) -> List<u64> {
    List::from_iter(0..size)
}

fn vec_from_iter(size: u64) -> Vec<u64> {
    Vec::from_iter(0..size)
}

fn criterion_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("FromIter");

    for size in [10, 100, 1_000].iter() {
        group.bench_with_input(BenchmarkId::new("List", size), size, |b, i| {
            b.iter(|| list_from_iter(*i))
        });

        group.bench_with_input(BenchmarkId::new("Vec", size), size, |b, i| {
            b.iter(|| vec_from_iter(*i))
        });
    }

    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
