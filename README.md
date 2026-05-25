# Verified Red-Black Tree in Dafny

A functional red-black tree whose invariants are machine-checked by the Dafny verifier. Every public operation carries a `requires`/`ensures` contract, and Dafny proves those contracts hold for all possible inputs before the code can compile.

## Building

```
make         # verify proofs + generate Go and Rust library sources
make go      # generate Go library source only
make rust    # generate Rust library source only
make verify  # proof-check only (no code generation)
make clean
```

Requires Dafny 4.x, Go, `goimports` (`go install golang.org/x/tools/cmd/goimports@latest`), and Rust/Cargo.

## Benchmarks

```
make bench-go       # Go benchmark (go test -bench)
make bench-rust     # Rust benchmark (criterion)
make bench          # both, with verbose output
make bench-compare  # both, then print a comparison table
```

Benchmarks measure `Insert` and `Contains` over 1000 keys using each compiled target.
`bench-compare` requires Python 3.9+.

---

## The data structure

Trees are **immutable algebraic datatypes**. This is the natural fit for Dafny: immutable values avoid heap reasoning and `modifies` clauses, and pattern matching lines up directly with structural induction.

```dafny
datatype Color = Red | Black
datatype Tree  = Leaf | Node(color: Color, left: Tree, key: int, right: Tree)
```

---

## The invariants

Four properties jointly define a valid red-black tree.

| Name | Definition |
|------|-----------|
| **BST** | Every key in a left subtree is strictly less than the node key; every key in a right subtree is strictly greater. |
| **NoRedRed** | No red node has a red child. |
| **BlackHeight** | Every path from a node to a leaf passes through the same number of black nodes. |
| **Black root** | The root node is black. |

### Ghost helpers

`BlackHeight` is expressed as a function that returns the uniform black-height, or `-1` if the two subtrees disagree. This avoids an existential quantifier and makes it easy to state that an operation *preserves* the height.

`Keys` is a ghost function returning the set of all keys in a subtree. BST ordering is stated in terms of `Keys` rather than immediate neighbours, which makes it precise across arbitrary depth.

### Predicate hierarchy

```
Valid(t)  =  RBInv(t)  ∧  (t is Leaf or t.color == Black)
RBInv(t)  =  BST(t)  ∧  NoRedRed(t)  ∧  BlackHeight(t) ≥ 0
```

`RBInv` omits the black-root rule deliberately. A valid tree's children satisfy `RBInv` but not `Valid` (they may be red), so every lemma that recurses into subtrees requires `RBInv`, not `Valid`.

---

## Insertion

### The challenge

Naive insertion breaks `NoRedRed`: inserting a red leaf under a red node creates a red-red violation. The fix is Okasaki's *balance* function, which detects and rotates the four symmetric red-red patterns on the way back up. The trouble for verification is that the tree is *temporarily invalid* mid-recursion. The proof structure must account for this intermediate state.

### The intermediate invariant: `InsPost`

```dafny
ghost predicate InsPost(t: Tree) {
  BST(t) && BlackHeight(t) >= 0 &&
  (t.Leaf? || (NoRedRed(t.left) && NoRedRed(t.right)))
}
```

`InsPost` relaxes only one thing: the root may be a red node with a red child. Everything else — BST ordering, uniform black-height, and `NoRedRed` for both immediate children — must hold. This is what `Ins` (the internal recursive function) guarantees, and it is enough for `Balance` to restore full validity.

### The stronger inductive postcondition

`InsCorrect` carries four postconditions:

```
1. InsPost(InsImpl(t, x))
2. BlackHeight(InsImpl(t, x)) == BlackHeight(t)
3. Keys(InsImpl(t, x)) == Keys(t) + {x}
4. (t.Leaf? || t.color == Black)  ==>  NoRedRed(InsImpl(t, x))
```

Postcondition 4 is the key to the induction. When a **red** parent recurses into one of its children:

- `NoRedRed` on the parent forces the child to be Leaf or Black.
- The stronger post (4) then fires on that child, giving `NoRedRed` on the
  result `l'`.
- `Balance(Red, l', k, r)` returns `Node(Red, l', k, r)` unchanged (no rotation
  for a red parent), and `NoRedRed(l')` is exactly what `InsPost` needs.

When a **black** parent recurses, `Balance` may fire a rotation. The `BalanceBlackLeft` / `BalanceBlackRight` lemmas prove that regardless of which of the four rotation cases applies, the result is fully `NoRedRed` with correct black-height and BST ordering.

### `Insert` closes the loop

```dafny
function Insert(t: Tree, x: int): Tree
  requires Valid(t)
  ensures  Valid(Insert(t, x))
  ensures  Keys(Insert(t, x)) == Keys(t) + {x}
{
  InsCorrect(t, x);
  match InsImpl(t, x)
  case Node(_, l, k, r) => Node(Black, l, k, r)
}
```

`t` is `Valid`, so its root is black. Postcondition 4 of `InsCorrect` applies, giving `NoRedRed` on the result. Recolouring the root black (which cannot increase any violation) then satisfies every clause of `Valid`.

### The Balance rotations

All four rotation patterns produce the same shape:

```
Node(Red, Node(Black, a, x, b), y, Node(Black, c, z, d))
```

The middle key `y` becomes the new root; the two flanking subtrees become black children. This eliminates exactly one red-red violation and preserves black-height because the new root is red where the old root was black.

```
    B               R
   / \            /   \
  R   d   →    B       B
 / \          / \     / \
R   c        a   b   c   d
```

---

## Lookup

```dafny
function Contains(t: Tree, x: int): bool
  requires BST(t)
  ensures  Contains(t, x) <==> x in Keys(t)
```

`Contains` requires only `BST`, not `Valid`. The recursive calls go into subtrees whose roots may be red; those roots satisfy `BST` but not `Valid`'s black-root requirement. Using the weakest sufficient precondition keeps the proof clean and makes `Contains` callable on any BST, not just fully valid trees.

---

## Proof obligations summary

| Lemma | What it proves |
|-------|---------------|
| `ChildrenRBInv` | `RBInv(t)` implies `RBInv` for both children |
| `RedParentBlackChildren` | Red node's children are Leaf or Black |
| `InsPostNoRedPattern` | `InsPost` + no root red-red pattern → `NoRedRed` |
| `BSTTop` | Unfolds `BST` quantifiers; used as a trigger hint |
| `BalanceKeys` | `Balance` preserves the key set |
| `BalanceBlackLeft` | For a black parent with left child from `Ins`: result is `NoRedRed`, correct black-height, BST |
| `BalanceBlackRight` | Symmetric for right child from `Ins` |
| `InsCorrect` | `InsImpl` preserves `RBInv` (modulo root) and the key set |
