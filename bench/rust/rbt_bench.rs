use criterion::{black_box, criterion_group, criterion_main, Criterion};
use dafny_runtime::DafnyInt;
use src::RedBlackTree::{Tree, _default};
use std::rc::Rc;

const N: i32 = 1000;

fn leaf() -> Rc<Tree> {
    Rc::new(Tree::Leaf {})
}

fn build_tree() -> Rc<Tree> {
    let mut t = leaf();
    for i in 0..N {
        t = _default::Insert(&t, &DafnyInt::from_i32(i));
    }
    t
}

fn bench_insert(c: &mut Criterion) {
    c.bench_function("insert", |b| {
        b.iter(|| {
            let mut t = leaf();
            for i in 0..N {
                t = _default::Insert(&t, black_box(&DafnyInt::from_i32(i)));
            }
            t
        })
    });
}

fn bench_contains_hit(c: &mut Criterion) {
    let t = build_tree();
    c.bench_function("contains_hit", |b| {
        b.iter(|| {
            for i in 0..N {
                black_box(_default::Contains(&t, black_box(&DafnyInt::from_i32(i))));
            }
        })
    });
}

fn bench_contains_miss(c: &mut Criterion) {
    let mut t = leaf();
    for i in 0..N {
        t = _default::Insert(&t, &DafnyInt::from_i32(i * 2)); // even keys only
    }
    c.bench_function("contains_miss", |b| {
        b.iter(|| {
            for i in 0..N {
                black_box(_default::Contains(&t, black_box(&DafnyInt::from_i32(i * 2 + 1)))); // odd: always miss
            }
        })
    });
}

criterion_group!(benches, bench_insert, bench_contains_hit, bench_contains_miss);
criterion_main!(benches);
