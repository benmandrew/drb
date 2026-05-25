package bench

import (
	"testing"

	rbt "RedBlackTree"
	_dafny "dafny"
)

const N = 1000

// build a tree with 0..N-1 inserted in order
func buildTree() rbt.Tree {
	t := rbt.Companion_Tree_.Create_Leaf_()
	for i := 0; i < N; i++ {
		t = rbt.Companion_Default___.Insert(t, _dafny.IntOf(i))
	}
	return t
}

func BenchmarkInsert(b *testing.B) {
	for i := 0; i < b.N; i++ {
		t := rbt.Companion_Tree_.Create_Leaf_()
		for j := 0; j < N; j++ {
			t = rbt.Companion_Default___.Insert(t, _dafny.IntOf(j))
		}
		_ = t
	}
}

func BenchmarkContainsHit(b *testing.B) {
	t := buildTree()
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := 0; j < N; j++ {
			_ = rbt.Companion_Default___.Contains(t, _dafny.IntOf(j))
		}
	}
}

func BenchmarkContainsMiss(b *testing.B) {
	t := rbt.Companion_Tree_.Create_Leaf_()
	for j := 0; j < N; j++ {
		t = rbt.Companion_Default___.Insert(t, _dafny.IntOf(j*2)) // even keys only
	}
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		for j := 0; j < N; j++ {
			_ = rbt.Companion_Default___.Contains(t, _dafny.IntOf(j*2+1)) // odd: always miss
		}
	}
}
