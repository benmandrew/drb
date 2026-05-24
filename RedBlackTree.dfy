module RedBlackTree {

  // ── Types ────────────────────────────────────────────────────────────────

  datatype Color = Red | Black

  datatype Tree =
    | Leaf
    | Node(color: Color, left: Tree, key: int, right: Tree)

  // ── Ghost helpers ─────────────────────────────────────────────────────────

  ghost function Keys(t: Tree): set<int> {
    match t
    case Leaf             => {}
    case Node(_, l, k, r) => Keys(l) + {k} + Keys(r)
  }

  // Returns the uniform black-height, or -1 if left/right heights differ.
  ghost function BlackHeight(t: Tree): int {
    match t
    case Leaf             => 0
    case Node(c, l, _, r) =>
      var lh := BlackHeight(l);
      var rh := BlackHeight(r);
      if lh < 0 || rh < 0 || lh != rh then -1
      else if c == Black then lh + 1 else lh
  }

  // ── Invariant predicates ──────────────────────────────────────────────────

  ghost predicate NoRedRed(t: Tree) {
    match t
    case Leaf                                => true
    case Node(Red, Node(Red, _, _, _), _, _) => false
    case Node(Red, _, _, Node(Red, _, _, _)) => false
    case Node(_, l, _, r)                   => NoRedRed(l) && NoRedRed(r)
  }

  ghost predicate BST(t: Tree) {
    match t
    case Leaf             => true
    case Node(_, l, k, r) =>
      (forall x :: x in Keys(l) ==> x < k) &&
      (forall x :: x in Keys(r) ==> x > k) &&
      BST(l) && BST(r)
  }

  // All red-black invariants except the black-root rule.
  // Holds for every subtree of a Valid tree.
  ghost predicate RBInv(t: Tree) {
    BST(t) && NoRedRed(t) && BlackHeight(t) >= 0
  }

  // Full validity: RBInv + black root.
  ghost predicate Valid(t: Tree) {
    RBInv(t) && (t.Leaf? || t.color == Black)
  }

  // Post-condition for Ins: BST, consistent black-height, and both immediate
  // children satisfy NoRedRed.  The root itself may be Red with a Red child.
  ghost predicate InsPost(t: Tree) {
    BST(t) &&
    BlackHeight(t) >= 0 &&
    (t.Leaf? || (NoRedRed(t.left) && NoRedRed(t.right)))
  }

  // ── Structural lemmas ─────────────────────────────────────────────────────

  lemma ChildrenRBInv(t: Tree)
    requires RBInv(t) && t.Node?
    ensures  RBInv(t.left) && RBInv(t.right)
  {}

  // A red parent's children must be Leaf or Black (from NoRedRed).
  lemma RedParentBlackChildren(t: Tree)
    requires RBInv(t) && t.Node? && t.color == Red
    ensures  t.left.Leaf?  || t.left.color  == Black
    ensures  t.right.Leaf? || t.right.color == Black
  {
    // If left were a Red Node, NoRedRed(t) would be false by definition.
    assert !(t.left.Node? && t.left.color == Red);
    assert !(t.right.Node? && t.right.color == Red);
  }

  // If t has InsPost and neither root-child is a Red node, then t is fully NoRedRed.
  lemma InsPostNoRedPattern(t: Tree)
    requires InsPost(t)
    requires !(t.Node? && t.color == Red && t.left.Node?  && t.left.color  == Red)
    requires !(t.Node? && t.color == Red && t.right.Node? && t.right.color == Red)
    ensures  NoRedRed(t)
  {}

  // ── Balance ───────────────────────────────────────────────────────────────
  //
  // The four symmetric rotations all produce Node(Red, Node(Black,..), y, Node(Black,..)).
  // When no rotation applies, the tree is returned unchanged.

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

  lemma BalanceKeys(c: Color, l: Tree, k: int, r: Tree)
    ensures Keys(Balance(c, l, k, r)) == Keys(l) + {k} + Keys(r)
  {}

  // Unfolds the top-level of BST into explicit quantifier facts.
  // Calling this gives Dafny the trigger it needs to instantiate key-ordering.
  lemma BSTTop(t: Tree)
    requires t.Node? && BST(t)
    ensures forall z :: z in Keys(t.left)  ==> z < t.key
    ensures forall z :: z in Keys(t.right) ==> z > t.key
    ensures BST(t.left) && BST(t.right)
  {}

  // For a Black parent, Balance either fires a rotation (result fully NoRedRed)
  // or does nothing (result is Node(Black, l, k, r), NoRedRed if l and r are).
  // Preconditions include BST and key-ordering so the BST postcondition can be proved.
  lemma {:timeLimitMultiplier 3} {:vcs_split_on_every_assert} BalanceBlackLeft(l: Tree, k: int, r: Tree)
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
        // LL rotation.  Dafny needs BSTTop calls to chain the quantifiers.
        BSTTop(l); BSTTop(l.left);
      case Node(Red, a, x, Node(Red, b, y, c2)) =>
        // LR rotation.
        BSTTop(l); BSTTop(l.right);
        // Keys(b) ⊆ Keys(l.right), all of which are > x.
        assert Keys(l.right) == Keys(b) + {y} + Keys(c2);
        assert forall z :: z in Keys(b) ==> z > x;
        // Keys(c2) ⊆ Keys(l.right) ⊆ Keys(l), all of which are < k.
        assert forall z :: z in Keys(c2) ==> z < k;
        // BST of the two new black children.
        assert BST(Node(Black, a, x, b)) by {
          assert BST(a); assert BST(b);
          assert forall z :: z in Keys(a) ==> z < x;
          assert forall z :: z in Keys(b) ==> z > x;
        }
        assert BST(Node(Black, c2, k, r)) by {
          assert BST(c2); assert BST(r);
          assert forall z :: z in Keys(c2) ==> z < k;
          assert forall z :: z in Keys(r) ==> z > k;
        }
      case _ =>
        match r {
          case Node(Red, Node(Red, _, _, _), _, _) => {}
          case Node(Red, _, _, Node(Red, _, _, _)) => {}
          case _ =>
            InsPostNoRedPattern(l);
        }
    }
  }

  // Symmetric: RIGHT child comes from Ins.
  lemma {:timeLimitMultiplier 3} {:vcs_split_on_every_assert} BalanceBlackRight(l: Tree, k: int, r: Tree)
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
    match l {
      case Node(Red, Node(Red, _, _, _), _, _) => {}
      case Node(Red, _, _, Node(Red, _, _, _)) => {}
      case _ =>
        match r {
          case Node(Red, Node(Red, b, y, c2), z, d) =>
            // RL rotation: result is Node(Red, Node(Black, l, k, b), y, Node(Black, c2, z, d)).
            // Keys(b) ⊆ Keys(r.left) ⊆ Keys(r), all > k.
            BSTTop(r); BSTTop(r.left);
            assert Keys(r.left) == Keys(b) + {y} + Keys(c2);
            assert forall q :: q in Keys(b) ==> q > k;
            // Keys(c2) ⊆ Keys(r.left), all < r.key == z.
            assert forall q :: q in Keys(c2) ==> q < z;
            assert BST(Node(Black, l, k, b)) by {
              assert BST(l); assert BST(b);
              assert forall q :: q in Keys(l) ==> q < k;
              assert forall q :: q in Keys(b) ==> q > k;
            }
            assert BST(Node(Black, c2, z, d)) by {
              assert BST(c2); assert BST(d);
              assert forall q :: q in Keys(c2) ==> q < z;
              assert forall q :: q in Keys(d)  ==> q > z;
            }
          case Node(Red, b, y, Node(Red, c2, z, d)) =>
            // RR rotation: result is Node(Red, Node(Black, l, k, b), y, Node(Black, c2, z, d)).
            // Keys(b) ⊆ Keys(r), all > k.
            BSTTop(r); BSTTop(r.right);
            assert Keys(r) == Keys(b) + {y} + Keys(c2) + {z} + Keys(d);
            assert forall q :: q in Keys(b) ==> q > k;
            assert BST(Node(Black, l, k, b)) by {
              assert BST(l); assert BST(b);
              assert forall q :: q in Keys(l) ==> q < k;
              assert forall q :: q in Keys(b) ==> q > k;
            }
            assert BST(Node(Black, c2, z, d)) by {
              assert BST(c2); assert BST(d);
              assert forall q :: q in Keys(c2) ==> q < z;
              assert forall q :: q in Keys(d)  ==> q > z;
            }
          case _ => InsPostNoRedPattern(r);
        }
    }
  }

  // ── InsImpl ───────────────────────────────────────────────────────────────

  function InsImpl(t: Tree, x: int): Tree {
    match t
    case Leaf             => Node(Red, Leaf, x, Leaf)
    case Node(c, l, k, r) =>
      if      x < k then Balance(c, InsImpl(l, x), k, r)
      else if x > k then Balance(c, l, k, InsImpl(r, x))
      else t
  }

  // Correctness of InsImpl.  The stronger postcondition (line 4) is key to
  // the induction: when a red parent recurses into a black child, the child
  // result is fully NoRedRed, so no rotation fires and InsPost holds at the
  // red level.
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

  // ── Insert ────────────────────────────────────────────────────────────────

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

  // ── Contains ─────────────────────────────────────────────────────────────
  //
  // Requires BST only — not Valid — so recursive calls work even when
  // subtree roots are Red (which would fail Valid's black-root requirement).

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
