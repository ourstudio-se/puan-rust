use criterion::{criterion_group, criterion_main, Criterion, BenchmarkId, Throughput};
use puanrs::{Theory};

fn criterion_benchmark(c: &mut Criterion) {
    
    let mut group = c.benchmark_group("to_polyhedron_w2");
    let static_width = 2;
    for depth in 1..16 {
        let theory = Theory::instance(static_width, depth, String::from("some-id"));
        group.throughput(Throughput::Bytes(depth as u64));
        group.bench_with_input(BenchmarkId::from_parameter(depth), &depth, |b, &depth| {
            b.iter(|| theory.to_ge_polyhedron(true, false));
        });
    }
    group.finish();
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);