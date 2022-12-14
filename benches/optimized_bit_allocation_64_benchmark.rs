use criterion::{black_box, criterion_group, criterion_main, Criterion};
use puanrs::linalg::{optimized_bit_allocation_64};

pub fn criterion_benchmark(c: &mut Criterion) {
    let vec: Vec<i64> = (0..63).collect();
    c.bench_function("opt_bit_63", |b| b.iter(|| optimized_bit_allocation_64(black_box(&vec))));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);