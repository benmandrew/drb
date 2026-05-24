include "RedBlackTree.dfy"

import opened RedBlackTree

module Main {
  import opened RedBlackTree

  method {:main} Main() {
    var t: Tree := Leaf;
    t := Insert(t, 5);
    t := Insert(t, 3);
    t := Insert(t, 7);
    t := Insert(t, 1);
    t := Insert(t, 4);

    print Contains(t, 3), "\n";  // true
    print Contains(t, 6), "\n";  // false
  }
}
