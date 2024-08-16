use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use ds_ext::List;
use rand::Rng;

fn list_random_mut(list: &mut List<usize>, num_mutations: usize) {
    let mut rng = rand::thread_rng();
    let size = list.len();

    for _ in 0..num_mutations {
        let (n, remove) = if list.len() <= 1 {
            (0, false)
        } else if list.len() > size {
            (rng.gen_range(0..size), true)
        } else {
            (
                rng.gen_range(0..list.len()),
                rng.gen_bool(list.len() as f64 / size as f64),
            )
        };

        if remove {
            list.remove(n);
        } else {
            list.insert(n, n);
        }
    }
}

fn vec_random_mut(list: &mut Vec<usize>, num_mutations: usize) {
    let mut rng = rand::thread_rng();
    let size = list.len();

    for _ in 0..num_mutations {
        let (n, remove) = if list.len() <= 1 {
            (0, false)
        } else if list.len() > size {
            (rng.gen_range(0..size), true)
        } else {
            (
                rng.gen_range(0..list.len()),
                rng.gen_bool(list.len() as f64 / size as f64),
            )
        };

        if remove {
            list.remove(n);
        } else {
            list.insert(n, n);
        }
    }
}

fn benchmark_list_vs_vec(c: &mut Criterion) {
    let mut group = c.benchmark_group("RandomMutation");

    for size in [10, 100, 1_000, 10_000].iter() {
        let mut list = List::from_iter(0..*size);
        group.bench_with_input(BenchmarkId::new("List", size), size, |b, i| {
            b.iter(|| list_random_mut(&mut list, 10_000))
        });

        let mut list = Vec::from_iter(0..*size);
        group.bench_with_input(BenchmarkId::new("Vec", size), size, |b, i| {
            b.iter(|| vec_random_mut(&mut list, 10_000))
        });
    }

    group.finish();
}

criterion_group!(benches, benchmark_list_vs_vec);
criterion_main!(benches);
