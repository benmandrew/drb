/**
  * A verified functional red-black tree.
  *
  * Trees are immutable algebraic values. Every public operation carries
  * `requires`/`ensures` contracts that the Dafny verifier proves hold for all
  * possible inputs before the code can compile.
  *
  * The four invariants that jointly define a valid tree:
  * - **BST**: every left-subtree key is strictly less than the node key;
  *   every right-subtree key is strictly greater.
  * - **NoRedRed**: no red node has a red child.
  * - **BlackHeight**: every root-to-leaf path passes through the same number
  *   of black nodes.
  * - **Black root**: the root node is black.
  */
module RedBlackTree {

  /** Node colour for the red-black colouring invariant. */
  datatype Color = Red | Black

  /**
    * An immutable binary search tree node.
    *
    * `Leaf` is the empty tree. `Node` carries a colour, left subtree, integer
    * key, and right subtree. Trees are values: every operation returns a new
    * tree rather than mutating an existing one.
    */
  datatype Tree =
    | Leaf
    | Node(color: Color, left: Tree, key: int, right: Tree)

  /**
    * The set of all keys stored in a subtree.
    *
    * Used to state BST ordering precisely at arbitrary depth. Rather than
    * comparing immediate neighbours, every invariant is expressed in terms of
    * `Keys` to avoid quantifier-alternation issues and to make ordering claims
    * exact across subtrees of any shape.
    */
  ghost function Keys(t: Tree): set<int> {
    match t
    case Leaf             => {}
    case Node(_, l, k, r) => Keys(l) + {k} + Keys(r)
  }

  /**
    * The uniform black-height of a subtree, or `-1` if the invariant is broken.
    *
    * Returns the number of black nodes on any root-to-leaf path when the
    * black-height invariant holds. Returns `-1` when the two subtrees have
    * different black-heights, encoding invalidity without introducing an
    * existential quantifier. This makes it straightforward to state that an
    * operation *preserves* the height: `BlackHeight(result) == BlackHeight(t)`.
    */
  ghost function BlackHeight(t: Tree): int {
    match t
    case Leaf             => 0
    case Node(c, l, _, r) =>
      var lh := BlackHeight(l);
      var rh := BlackHeight(r);
      if lh < 0 || rh < 0 || lh != rh then -1
      else if c == Black then lh + 1 else lh
  }

  /**
    * No red node has a red child.
    *
    * Checked structurally by pattern-matching on the two immediate children of
    * every red node, then recursing into both subtrees. Together with
    * `BlackHeight >= 0`, this bounds the height of any valid tree to at most
    * `2 * log2(n + 1)`.
    */
  ghost predicate NoRedRed(t: Tree) {
    match t
    case Leaf                                => true
    case Node(Red, Node(Red, _, _, _), _, _) => false
    case Node(Red, _, _, Node(Red, _, _, _)) => false
    case Node(_, l, _, r)                   => NoRedRed(l) && NoRedRed(r)
  }

  /**
    * The binary-search-tree ordering invariant.
    *
    * Every key in the left subtree is strictly less than the node key, and every
    * key in the right subtree is strictly greater. Stated in terms of `Keys`
    * rather than immediate neighbours so that the ordering holds at arbitrary
    * depth and is precise for the full subtree, not just the next level.
    */
  ghost predicate BST(t: Tree) {
    match t
    case Leaf             => true
    case Node(_, l, k, r) =>
      (forall x :: x in Keys(l) ==> x < k) &&
      (forall x :: x in Keys(r) ==> x > k) &&
      BST(l) && BST(r)
  }

  /**
    * All red-black invariants except the black-root rule.
    *
    * Holds for every subtree of a `Valid` tree, including subtrees whose roots
    * may be red. Omits the black-root requirement deliberately so that recursive
    * lemmas can use `RBInv` on children without first proving them black.
    * Every lemma that recurses into subtrees requires `RBInv`, not `Valid`.
    */
  ghost predicate RBInv(t: Tree) {
    BST(t) && NoRedRed(t) && BlackHeight(t) >= 0
  }

  /**
    * Full red-black tree validity: `RBInv` plus a black root.
    *
    * This is the invariant maintained by the public API. `Insert` requires and
    * ensures `Valid`; `Contains` requires only `BST`, the weaker condition
    * sufficient for lookup.
    */
  ghost predicate Valid(t: Tree) {
    RBInv(t) && (t.Leaf? || t.color == Black)
  }

  /**
    * Intermediate postcondition produced by `InsImpl`.
    *
    * Relaxes exactly one rule relative to `RBInv`: the root may be a red node
    * whose immediate child is also red (one red-red violation at the top).
    * Everything else — BST ordering, uniform black-height, and `NoRedRed` on
    * both immediate children of the root — must hold.
    *
    * This is what `InsImpl` guarantees after recursion, and it is enough for
    * `Balance` to restore full `NoRedRed` on the way back up the call stack.
    */
  ghost predicate InsPost(t: Tree) {
    BST(t) &&
    BlackHeight(t) >= 0 &&
    (t.Leaf? || (NoRedRed(t.left) && NoRedRed(t.right)))
  }

  /**
    * `RBInv` is closed under taking children.
    *
    * If a node satisfies all red-black invariants (modulo the black-root rule),
    * both of its children satisfy `RBInv` as well. Used to establish the
    * inductive hypothesis when recursing into subtrees during insertion.
    */
  lemma ChildrenRBInv(t: Tree)
    requires RBInv(t) && t.Node?
    ensures  RBInv(t.left) && RBInv(t.right)
  {}

  /**
    * A red node's children must be `Leaf` or `Black`.
    *
    * Follows directly from `NoRedRed`: if either child were a red `Node`, the
    * pattern `Node(Red, Node(Red,...), ...)` would immediately falsify
    * `NoRedRed(t)`. Used in `InsCorrect` to activate the stronger inductive
    * postcondition when recursing through a red parent.
    */
  lemma RedParentBlackChildren(t: Tree)
    requires RBInv(t) && t.Node? && t.color == Red
    ensures  t.left.Leaf?  || t.left.color  == Black
    ensures  t.right.Leaf? || t.right.color == Black
  {
    // If left were a Red Node, NoRedRed(t) would be false by definition.
    assert !(t.left.Node? && t.left.color == Red);
    assert !(t.right.Node? && t.right.color == Red);
  }

  /**
    * `InsPost` without a root red-red pattern implies full `NoRedRed`.
    *
    * When `InsPost` holds and neither child of a potential red root is itself a
    * red node, the single relaxation permitted by `InsPost` does not apply and
    * the tree satisfies the strict `NoRedRed` predicate. Used in the no-rotation
    * fallthrough cases of `BalanceBlackLeft` and `BalanceBlackRight`.
    */
  lemma InsPostNoRedPattern(t: Tree)
    requires InsPost(t)
    requires !(t.Node? && t.color == Red && t.left.Node?  && t.left.color  == Red)
    requires !(t.Node? && t.color == Red && t.right.Node? && t.right.color == Red)
    ensures  NoRedRed(t)
  {}

  /**
    * Okasaki's rebalancing function for red-black insertion.
    *
    * Detects and rotates the four symmetric patterns in which a black node has a
    * red child with a red grandchild, producing
    * `Node(Red, Node(Black,a,x,b), y, Node(Black,c,z,d))` in each case. The
    * middle key `y` becomes the new (red) root; the two flanking subtrees become
    * black children. This eliminates exactly one red-red violation and preserves
    * the black-height because the new root is red where the old root was black.
    *
    * When no pattern matches the tree is returned as `Node(c, l, k, r)`.
    *
    * Left-child patterns are checked before right-child patterns. This ordering
    * has consequences for the proofs in `BalanceBlackLeft` and
    * `BalanceBlackRight`: `BalanceBlackRight` must explicitly rule out left-child
    * patterns before reasoning about the right-child cases.
    */
  function Balance(c: Color, l: Tree, k: int, r: Tree): Tree {
    match (c, l) {
      case (Black, Node(Red, Node(Red, a, x, b), y, c2)) =>
        Node(Red, Node(Black, a, x, b), y, Node(Black, c2, k, r))
      case (Black, Node(Red, a, x, Node(Red, b, y, c2))) =>
        Node(Red, Node(Black, a, x, b), y, Node(Black, c2, k, r))
      case _ =>
        match (c, r) {
          case (Black, Node(Red, Node(Red, b, y, c2), z, d)) =>
            Node(Red, Node(Black, l, k, b), y, Node(Black, c2, z, d))
          case (Black, Node(Red, b, y, Node(Red, c2, z, d))) =>
            Node(Red, Node(Black, l, k, b), y, Node(Black, c2, z, d))
          case _ =>
            Node(c, l, k, r)
        }
    }
  }

  /**
    * `Balance` preserves the key set.
    *
    * Regardless of which rotation case fires (or whether none fires),
    * `Keys(Balance(c, l, k, r)) == Keys(l) + {k} + Keys(r)`. Used as a hint
    * in `InsCorrect` and the `BalanceBlack*` lemmas to connect the key sets
    * before and after a potential rotation.
    */
  lemma BalanceKeys(c: Color, l: Tree, k: int, r: Tree)
    ensures Keys(Balance(c, l, k, r)) == Keys(l) + {k} + Keys(r)
  {}

  /**
    * Unfolds the top-level BST quantifiers of a node into separate facts.
    *
    * Extracts `forall z :: z in Keys(t.left) ==> z < t.key` and the symmetric
    * right-side bound as standalone `ensures` so that Dafny's trigger-based
    * quantifier instantiation can use them directly. Called inside rotation
    * proofs where the verifier cannot find the quantifier trigger on its own.
    */
  lemma BSTTop(t: Tree)
    requires t.Node? && BST(t)
    ensures forall z :: z in Keys(t.left)  ==> z < t.key
    ensures forall z :: z in Keys(t.right) ==> z > t.key
    ensures BST(t.left) && BST(t.right)
  {}

  /**
    * Constructs a `BST` fact for a node from its children and key bounds.
    *
    * If both subtrees satisfy `BST`, all left keys are strictly below `k`, and
    * all right keys are strictly above `k`, then `Node(c, l, k, r)` satisfies
    * `BST`. Isolates the BST proof obligation for each rotation result into a
    * single, trivial verification condition.
    */
  lemma BSTNode(c: Color, l: Tree, k: int, r: Tree)
    requires BST(l) && BST(r)
    requires forall q :: q in Keys(l) ==> q < k
    requires forall q :: q in Keys(r) ==> q > k
    ensures  BST(Node(c, l, k, r))
  {}

  /**
    * After inserting into the **left** subtree of a black node, `Balance`
    * restores full `NoRedRed`, preserves the black-height, and maintains BST.
    *
    * The left child `l` comes from `InsImpl` and satisfies `InsPost` (it may
    * have one red-red violation at its root). The right child `r` is unchanged
    * and satisfies `NoRedRed`.
    *
    * Because `Balance` checks left-child patterns first, one of the LL or LR
    * rotation cases fires to eliminate the violation, or — when `l` carries no
    * red-red pattern — `InsPostNoRedPattern` closes the no-rotation case
    * directly.
    *
    * `{:vcs_split_on_every_assert}` splits each `assert` into its own
    * verification condition, keeping individual VC complexity manageable.
    */
  lemma {:vcs_split_on_every_assert} BalanceBlackLeft(l: Tree, k: int, r: Tree)
    requires InsPost(l) && NoRedRed(r)
    requires BlackHeight(l) == BlackHeight(r) && BlackHeight(l) >= 0
    requires BST(l) && BST(r)
    requires forall x :: x in Keys(l) ==> x < k
    requires forall x :: x in Keys(r) ==> x > k
    ensures  NoRedRed(Balance(Black, l, k, r))
    ensures  BlackHeight(Balance(Black, l, k, r)) == BlackHeight(l) + 1
    ensures  BST(Balance(Black, l, k, r))
    ensures  Keys(Balance(Black, l, k, r)) == Keys(l) + {k} + Keys(r)
  {
    BalanceKeys(Black, l, k, r);
    match l {
      case Node(Red, Node(Red, a, x, b), y, c2) =>
        // LL rotation: result = Node(Red, Node(Black,a,x,b), y, Node(Black,c2,k,r))
        BSTTop(l); BSTTop(l.left);
        // Keys(l.left) < l.key = y, so Keys(Node(Black,a,x,b)) < y.
        assert forall q :: q in Keys(Node(Black, a, x, b)) ==> q < y by {
          assert Keys(Node(Black, a, x, b)) == Keys(l.left);
        }
        // Keys(c2) > y and y < k (y ∈ Keys(l)), so Keys(Node(Black,c2,k,r)) > y.
        assert y in Keys(l);
        assert y < k;
        assert forall q :: q in Keys(Node(Black, c2, k, r)) ==> q > y by {
          assert Keys(Node(Black, c2, k, r)) == Keys(c2) + {k} + Keys(r);
          assert forall q :: q in Keys(c2) ==> q > y;
        }
        BSTNode(Black, a, x, b);
        BSTNode(Black, c2, k, r);
        BSTNode(Red, Node(Black, a, x, b), y, Node(Black, c2, k, r));

      case Node(Red, a, x, Node(Red, b, y, c2)) =>
        // LR rotation: result = Node(Red, Node(Black,a,x,b), y, Node(Black,c2,k,r))
        BSTTop(l); BSTTop(l.right);
        assert Keys(l.right) == Keys(b) + {y} + Keys(c2);
        // Keys(b) ⊆ Keys(l.right), all > l.key = x.
        assert forall q :: q in Keys(b) ==> q > x;
        // x < y (y ∈ Keys(l.right) > x) and Keys(b) < y, so Keys(Node(Black,a,x,b)) < y.
        assert y in Keys(l.right);
        assert x < y;
        assert forall q :: q in Keys(Node(Black, a, x, b)) ==> q < y by {
          assert Keys(Node(Black, a, x, b)) == Keys(a) + {x} + Keys(b);
          assert forall q :: q in Keys(b) ==> q < y;
        }
        // Keys(c2) > y and y < k (y ∈ Keys(l)), so Keys(Node(Black,c2,k,r)) > y.
        assert y in Keys(l);
        assert y < k;
        assert forall q :: q in Keys(Node(Black, c2, k, r)) ==> q > y by {
          assert Keys(Node(Black, c2, k, r)) == Keys(c2) + {k} + Keys(r);
          assert forall q :: q in Keys(c2) ==> q > y;
        }
        BSTNode(Black, a, x, b);
        BSTNode(Black, c2, k, r);
        BSTNode(Red, Node(Black, a, x, b), y, Node(Black, c2, k, r));

      case _ =>
        // NoRedRed(r) makes RL/RR inner cases impossible; no rotation fires.
        match r {
          case Node(Red, Node(Red, _, _, _), _, _) => {}
          case Node(Red, _, _, Node(Red, _, _, _)) => {}
          case _ => InsPostNoRedPattern(l);
        }
    }
  }

  /**
    * After inserting into the **right** subtree of a black node, `Balance`
    * restores full `NoRedRed`, preserves the black-height, and maintains BST.
    *
    * Symmetric to `BalanceBlackLeft`, but with `r` as the potentially-violated
    * child from `InsImpl`. The top-level match is on `r` rather than `l` to
    * avoid paying the cost of re-deriving that the LL/LR left-child patterns
    * cannot apply. Two explicit assertions at the top of the body establish that
    * `l` has no left-side red-red pattern (since `NoRedRed(l)` holds), making
    * this fact available to the verifier before it enters each `r`-case.
    *
    * `{:vcs_split_on_every_assert}` splits each `assert` into its own
    * verification condition, keeping individual VC complexity manageable.
    */
  lemma {:vcs_split_on_every_assert} BalanceBlackRight(l: Tree, k: int, r: Tree)
    requires NoRedRed(l) && InsPost(r)
    requires BlackHeight(l) == BlackHeight(r) && BlackHeight(l) >= 0
    requires BST(l) && BST(r)
    requires forall x :: x in Keys(l) ==> x < k
    requires forall x :: x in Keys(r) ==> x > k
    ensures  NoRedRed(Balance(Black, l, k, r))
    ensures  BlackHeight(Balance(Black, l, k, r)) == BlackHeight(l) + 1
    ensures  BST(Balance(Black, l, k, r))
    ensures  Keys(Balance(Black, l, k, r)) == Keys(l) + {k} + Keys(r)
  {
    BalanceKeys(Black, l, k, r);
    // NoRedRed(l) rules out both left-side patterns that Balance checks first.
    // Making this explicit avoids re-deriving it inside each rotation case.
    assert !(l.Node? && l.color == Red && l.left.Node?  && l.left.color  == Red);
    assert !(l.Node? && l.color == Red && l.right.Node? && l.right.color == Red);
    match r {
      case Node(Red, Node(Red, b, y, c2), z, d) =>
        // RL rotation: result = Node(Red, Node(Black,l,k,b), y, Node(Black,c2,z,d))
        BSTTop(r); BSTTop(r.left);
        assert Keys(r.left) == Keys(b) + {y} + Keys(c2);
        // Keys(b) ⊆ Keys(r.left) ⊆ Keys(r), all > k.
        assert forall q :: q in Keys(b) ==> q > k;
        // k < y (y ∈ Keys(r) > k) and Keys(b) < y, so Keys(Node(Black,l,k,b)) < y.
        assert y in Keys(r);
        assert k < y;
        assert forall q :: q in Keys(Node(Black, l, k, b)) ==> q < y by {
          assert Keys(Node(Black, l, k, b)) == Keys(l) + {k} + Keys(b);
          assert forall q :: q in Keys(b) ==> q < y;
        }
        // Keys(c2) > y and y < z (y ∈ Keys(r.left) < r.key = z), so Keys(Node(Black,c2,z,d)) > y.
        assert y < z;
        assert forall q :: q in Keys(Node(Black, c2, z, d)) ==> q > y by {
          assert Keys(Node(Black, c2, z, d)) == Keys(c2) + {z} + Keys(d);
          assert forall q :: q in Keys(c2) ==> q > y;
          assert forall q :: q in Keys(d)  ==> q > z;
        }
        BSTNode(Black, l, k, b);
        BSTNode(Black, c2, z, d);
        BSTNode(Red, Node(Black, l, k, b), y, Node(Black, c2, z, d));

      case Node(Red, b, y, Node(Red, c2, z, d)) =>
        // RR rotation: result = Node(Red, Node(Black,l,k,b), y, Node(Black,c2,z,d))
        BSTTop(r); BSTTop(r.right);
        // Keys(b) ⊆ Keys(r), all > k.
        assert forall q :: q in Keys(b) ==> q > k by {
          assert Keys(r) == Keys(b) + {y} + Keys(c2) + {z} + Keys(d);
        }
        // k < y (y = r.key ∈ Keys(r) > k) and Keys(b) < y, so Keys(Node(Black,l,k,b)) < y.
        assert y in Keys(r);
        assert k < y;
        assert forall q :: q in Keys(Node(Black, l, k, b)) ==> q < y by {
          assert Keys(Node(Black, l, k, b)) == Keys(l) + {k} + Keys(b);
          assert forall q :: q in Keys(b) ==> q < y;
        }
        // Keys(c2) > y (⊆ Keys(r.right) > r.key = y) and Keys(d) > z > y.
        assert forall q :: q in Keys(Node(Black, c2, z, d)) ==> q > y by {
          assert Keys(Node(Black, c2, z, d)) == Keys(c2) + {z} + Keys(d);
          assert forall q :: q in Keys(c2) ==> q > y by {
            assert forall q :: q in Keys(r.right) ==> q > y;
          }
          assert z > y by { assert z in Keys(r.right); }
          assert forall q :: q in Keys(d) ==> q > z;
        }
        BSTNode(Black, l, k, b);
        BSTNode(Black, c2, z, d);
        BSTNode(Red, Node(Black, l, k, b), y, Node(Black, c2, z, d));

      case _ =>
        // NoRedRed(l) makes LL/LR patterns for l impossible, so no rotation fires.
        InsPostNoRedPattern(r);
        BSTNode(Black, l, k, r);
    }
  }

  /**
    * Internal recursive insertion, without the black-root fix.
    *
    * Inserts `x` as a red leaf, then calls `Balance` on the way back up the
    * call stack to repair any red-red violations introduced by the new node.
    * The result satisfies `InsPost` rather than full `RBInv`: the root may be
    * red with a red child when insertion recurses through a red parent.
    *
    * Not part of the public API; use `Insert` instead.
    */
  function InsImpl(t: Tree, x: int): Tree {
    match t
    case Leaf             => Node(Red, Leaf, x, Leaf)
    case Node(c, l, k, r) =>
      if      x < k then Balance(c, InsImpl(l, x), k, r)
      else if x > k then Balance(c, l, k, InsImpl(r, x))
      else t
  }

  /**
    * Correctness proof for `InsImpl`.
    *
    * Establishes four postconditions by structural induction on `t`:
    * 1. `InsPost(InsImpl(t, x))` — the result satisfies the relaxed invariant.
    * 2. `BlackHeight(InsImpl(t, x)) == BlackHeight(t)` — black-height is unchanged.
    * 3. `Keys(InsImpl(t, x)) == Keys(t) + {x}` — exactly one key is added.
    * 4. `(t.Leaf? || t.color == Black) ==> NoRedRed(InsImpl(t, x))` — when
    *    the input root is black (or a leaf), the result is fully `NoRedRed`.
    *
    * Postcondition 4 is the key to the induction. A red parent forces its
    * children to be black (`RedParentBlackChildren`), so postcondition 4 fires
    * on each recursive call, giving `NoRedRed` on the modified child. `Balance`
    * on a red parent returns the node unchanged, and `NoRedRed` on the child is
    * exactly what `InsPost` requires at the red level.
    */
  lemma {:timeLimitMultiplier 4} InsCorrect(t: Tree, x: int)
    requires RBInv(t)
    ensures  InsPost(InsImpl(t, x))
    ensures  BlackHeight(InsImpl(t, x)) == BlackHeight(t)
    ensures  Keys(InsImpl(t, x)) == Keys(t) + {x}
    ensures  (t.Leaf? || t.color == Black) ==> NoRedRed(InsImpl(t, x))
    decreases t
  {
    match t {
      case Leaf => {}

      case Node(c, l, k, r) =>
        ChildrenRBInv(t);

        if x < k {
          InsCorrect(l, x);
          var l' := InsImpl(l, x);
          BalanceKeys(c, l', k, r);

          if c == Black {
            // Black parent: rotations may fire; result is fully NoRedRed.
            BalanceBlackLeft(l', k, r);
          } else {
            // Red parent: no rotation fires (Balance(Red,...) = Node(Red, l', k, r)).
            // l must be Leaf or Black (NoRedRed of the red parent).
            RedParentBlackChildren(t);
            assert l.Leaf? || l.color == Black;
            // InsCorrect's stronger post gives NoRedRed(l').
            assert NoRedRed(l');
            // Result is Node(Red, l', k, r); check InsPost.
            assert InsPost(InsImpl(t, x)) by {
              assert InsImpl(t, x) == Node(Red, l', k, r);
              assert NoRedRed(l'.left)  || l'.Leaf?;
              assert NoRedRed(l'.right) || l'.Leaf?;
              // BST of Node(Red, l', k, r)
              assert BST(Node(Red, l', k, r)) by {
                assert Keys(l') == Keys(l) + {x};
                assert forall z :: z in Keys(l') ==> z < k;
                assert forall z :: z in Keys(r)  ==> z > k;
              }
            }
          }

        } else if x > k {
          InsCorrect(r, x);
          var r' := InsImpl(r, x);
          BalanceKeys(c, l, k, r');

          if c == Black {
            BalanceBlackRight(l, k, r');
          } else {
            RedParentBlackChildren(t);
            assert r.Leaf? || r.color == Black;
            assert NoRedRed(r');
            assert InsPost(InsImpl(t, x)) by {
              assert InsImpl(t, x) == Node(Red, l, k, r');
              assert BST(Node(Red, l, k, r')) by {
                assert Keys(r') == Keys(r) + {x};
                assert forall z :: z in Keys(l)  ==> z < k;
                assert forall z :: z in Keys(r') ==> z > k;
              }
            }
          }
        }
    }
  }

  /**
    * Insert a key into a valid red-black tree, returning a new valid tree.
    *
    * Calls `InsImpl` to perform the recursive insertion and rebalancing, then
    * recolours the root black to satisfy `Valid`'s black-root requirement.
    * Because `t` is `Valid`, its root is already black (or it is `Leaf`), so
    * postcondition 4 of `InsCorrect` applies and the result of `InsImpl` is
    * fully `NoRedRed`. Recolouring the root black cannot introduce a new
    * red-red violation, so `Valid` is restored.
    *
    * If `x` is already present in `t`, the tree is returned unchanged.
    */
  function Insert(t: Tree, x: int): Tree
    requires Valid(t)
    ensures  Valid(Insert(t, x))
    ensures  Keys(Insert(t, x)) == Keys(t) + {x}
  {
    assert RBInv(t);
    // t is Leaf or Black-rooted (Valid), so InsCorrect's stronger post applies:
    // InsImpl returns a fully NoRedRed tree with the right black-height.
    InsCorrect(t, x);
    match InsImpl(t, x)
    case Leaf             => Leaf  // unreachable
    case Node(_, l, k, r) => Node(Black, l, k, r)
  }

  /**
    * Test whether a key is present in the tree.
    *
    * Performs a standard BST search, recursing left when `x < k` and right when
    * `x > k`. Returns `true` if and only if `x in Keys(t)`.
    *
    * Requires only `BST`, not `Valid`: recursive calls descend into subtrees
    * whose roots may be red, which would violate `Valid`'s black-root
    * requirement. Using the weakest sufficient precondition keeps the proof
    * clean and makes `Contains` callable on any BST, not just fully valid trees.
    */
  function Contains(t: Tree, x: int): bool
    requires BST(t)
    ensures  Contains(t, x) <==> x in Keys(t)
  {
    match t
    case Leaf             => false
    case Node(_, l, k, r) =>
      if      x < k then Contains(l, x)
      else if x > k then Contains(r, x)
      else true
  }

}
