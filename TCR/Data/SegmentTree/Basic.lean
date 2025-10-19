/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import TCR.Data.Vector

/-!
# Segment trees

This file defines *segment trees*, following the approach described in the article
[efficient and easy segment trees](https://codeforces.com/blog/entry/18051).
-/

namespace TCR.SegmentTree

namespace Impl

/-- A vector of size `2 * n` is an `op`-segment tree if, when interpreted as a binary tree,
it satisfies the heap-like property that the parent is always the `op` of the children. -/
public structure IsSegmentTree (op : α → α → α) (neutral : α) (v : Vector α (2 * n)) : Prop where
  /-- The unused zero-th element of `v` is the neutral element, to ensure that segment trees on
  a given underlying array are unique. -/
  zero_eq : ∀ (h : 0 < 2 * n), v[0] = neutral
  /-- Given `0 < i < n`, `v[i] = op v[2 * i + 1] v[2 * i + 2]`. -/
  op_eq : ∀ (i : Nat) (_ : 0 < i) (hi : i < n), v[i] = op v[2 * i] v[2 * i + 1]

/-- Creates a new `op`-segment tree on the vector `v`. -/
@[inline]
def mkSegmentTree (op : α → α → α) (neutral : α) (v : Vector α n) : Vector α (2 * n) :=
  if h : n = 0 then
    Vector.mk #[] (by simp [h])
  else
    let vec := Vector.mk (Array.replicate n neutral ++ v.toArray) (by grind)
    loop vec (n - 1) (by omega)
where
  @[specialize] loop (vec : Vector α (2 * n)) (idx : Nat) (hidx : idx < n) : Vector α (2 * n) :=
    match h : idx with
    | 0 => vec
    | idx' + 1 => loop (vec.set (idx' + 1) (op vec[2 * (idx' + 1)] vec[2 * (idx' + 1) + 1])) idx' (by grind)

/-- Creates an empty segment tree using the neutral element `neutral`. -/
@[inline]
def mkEmpty (neutral : α) (n : Nat) : Vector α (2 * n) :=
  Vector.replicate (2 * n) neutral

/-- Given a segment tree, extracts the underlying data by copying it. -/
@[inline]
def underlying (v : Vector α (2 * n)) : Vector α n :=
  v.extract n (2 * n) |>.cast <| by grind

/-- Modifies the underlying array of the segment tree at position `i` using `f` and restores the segment tree
property. -/
@[inline]
def modify (op : α → α → α) (v : Vector α (2 * n)) (i : Nat) (hi : i < n) (f : α → α) : Vector α (2 * n) :=
  loop (v.modify (n + i) f) ((n + i) / 2) (by omega)
where
  @[specialize] loop (vec : Vector α (2 * n)) (idx : Nat) (hidx : idx < n) : Vector α (2 * n) :=
    if h : idx = 0 then
      vec
    else
      loop (vec.set idx (op vec[2 * idx] vec[2 * idx + 1])) (idx / 2) (by omega)

/-- Folds the operation over `underlying[l...<r]`. -/
@[inline]
def query (op : α → α → α) (neutral : α) (v : Vector α (2 * n)) (l r : Nat) (hlr : l ≤ r) (hr : r ≤ n) : α :=
  loop (l + n) (r + n) neutral neutral (by omega) (by omega)
where
  @[specialize] loop (l r : Nat) (resl resr : α) (hlr : l ≤ r) (hr : r ≤ 2 * n) : α :=
    if h : l < r then
      let resl := if l % 2 = 0 then resl else op resl (v[l]'(by grind))
      let resr := if r % 2 = 0 then resr else op (v[r - 1]'(by grind)) resr
      loop ((l + 1) / 2) (r / 2) resl resr (by grind) (by grind)
    else
      op resl resr

/-- Inductive well-formedness predicate for segment trees. In `TCR.Data.SegmentTree.WF` we show that the first
constructors subsumes all other ones, i.e., that all operations preserve the segment tree property, see
`Impl.WF.out`. -/
public protected inductive WF (op : α → α → α) (neutral : α) : Vector α (2 * n) → Prop where
  | isSegmentTree : IsSegmentTree op neutral v → Impl.WF op neutral v
  | private mkSegmentTree : Impl.WF op neutral (mkSegmentTree op neutral v)
  | private mkEmpty : Impl.WF op neutral (mkEmpty neutral n)
  | private modify : Impl.WF op neutral v → Impl.WF op neutral (modify op v i hi f)

end Impl

/-- A segment tree is a data structure for dynamic range queries. It has an underlying array `underlying`.
It supports modifying the underlying array via `modify`, and folding the operation over a range using
`query`.

This is an efficient implementation representing the segment tree as an implicit data structure in an
array. As with all data structures based on arrays, care should be taken to use it linearly. -/
public structure _root_.TCR.SegmentTree (op : α → α → α) (neutral : α) (n : Nat) where
  /-- The segment tree, stored as an implicit binary tree. -/
  tree : Vector α (2 * n)
  /-- The tree forms a valid segment tree. -/
  wf : Impl.WF op neutral tree

/-- Constructs an `op`-segment tree from the vector `v.` -/
@[inline]
public def ofVector (op : α → α → α) (neutral : α) (v : Vector α n) : SegmentTree op neutral n where
  tree := Impl.mkSegmentTree op neutral v
  wf := .mkSegmentTree

/-- Constructs an empty `op`-segment tree whose underlying array has size `n`. -/
@[inline]
public def empty (op : α → α → α) (neutral : α) (n : Nat) : SegmentTree op neutral n where
  tree := Impl.mkEmpty neutral n
  wf := .mkEmpty

/-- Modifies the underlying array of the segment tree at position `i` using `f`. -/
@[inline]
public def modify {op : α → α → α} {neutral : α} (t : SegmentTree op neutral n) (i : Nat) (hi : i < n) (f : α → α) :
    SegmentTree op neutral n where
  tree := Impl.modify op t.tree i hi f
  wf := .modify t.wf

/-- Folds the operation over `underlying[l...<r]`. -/
@[inline]
public def query {op : α → α → α} {neutral : α} (t : SegmentTree op neutral n) (l r : Nat) (hlr : l ≤ r) (hr : r ≤ n) : α :=
  Impl.query op neutral t.tree l r hlr hr

/-- Obtains the array that the tree represents. Note that this makes a copy of the array, so it is a
linear-time operation. -/
@[inline]
public def underlying {op : α → α → α} {neutral : α} (t : SegmentTree op neutral n) : Vector α n :=
  Impl.underlying t.tree

end TCR.SegmentTree
