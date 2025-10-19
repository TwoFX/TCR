/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

meta import TCR.Data.SegmentTree.Basic

open TCR

meta def testSegmentTree : IO Unit := do
  let mut tree := SegmentTree.ofVector (· + ·) 0 #v[1, 2, 3, 4, 5]
  IO.println s!"{tree.query 0 1 (by decide) (by decide)} {tree.query 1 3 (by decide) (by decide)}"
  tree := tree.modify 1 (by decide) (fun _ => 4)
  IO.println s!"{tree.query 0 1 (by decide) (by decide)} {tree.query 1 3 (by decide) (by decide)}"
  tree := tree.modify 1 (by decide) (· + 1)
  IO.println s!"{tree.query 0 1 (by decide) (by decide)} {tree.query 1 3 (by decide) (by decide)}"
  IO.println s!"{tree.query 0 5 (by decide) (by decide)}"
  IO.println s!"{tree.query 5 5 (by decide) (by decide)}"
  IO.println s!"{tree.query 1 1 (by decide) (by decide)}"

/--
info: 1 5
1 7
1 8
18
0
0
-/
#guard_msgs in
#eval testSegmentTree
