/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

import TCR.Data.Vector

/-!
# Verification of the segment tree `query` operation (WIP)

This file will contain the internal part of the verification of the `query` operation on segment trees.
The final user-facing lemma will appear in `TCR.Data.SegmentTree.Lemmas`.
-/

namespace TCR.SegmentTree

namespace Impl

/-- Returns the leftmost node reachable from node `i` in the implicit tree of size `n`. -/
def leftmost (n i : Nat) : Nat :=
  if i = 0 then
    0
  else if n ≤ i then
    i
  else
    leftmost n (2 * i)

@[simp]
theorem leftmost_zero {n : Nat} : leftmost n 0 = 0 := by
  simp [leftmost]

theorem leftmost_eq_self {n i : Nat} (hi : 0 < i) (hni : n ≤ i) : leftmost n i = i := by
  grind [leftmost]

theorem leftmost_eq_leftmost_two_mul {n i : Nat} (hi : 0 < i) (hni : i < n) : leftmost n i = leftmost n (2 * i) := by
  grind [leftmost]

/-- `IsFold op neutral v l r a` is shorthand for the fact that `a` is obtained by folding `op` over `v[l...<r]`. -/
def IsFold (op : α → α → α) (neutral : α) (v : Vector α k) (l r : Nat) (a : α) : Prop :=
  a = (v.extract l r).foldl op neutral

theorem isFold_iff {op : α → α → α} {neutral : α} {v : Vector α k} {l r : Nat} {a : α} :
    IsFold op neutral v l r a ↔ a = (v.extract l r).foldl op neutral := Iff.rfl

theorem IsFold.base {op : α → α → α} {neutral : α} {v : Vector α k} {l} : IsFold op neutral v l l neutral := by
  simp [isFold_iff, Vector.extract_eq_cast_empty (Nat.min_le_left l k)]

theorem IsFold.concat {op : α → α → α} {neutral : α} [Std.Associative op] [Std.LawfulRightIdentity op neutral]
    {v : Vector α k} {l m r} {a b : α} (hlm : l ≤ m) (hmr : m ≤ r) :
    IsFold op neutral v l m a → IsFold op neutral v m r b → IsFold op neutral v l r (op a b) := by
  simp only [isFold_iff, isFold_iff]
  rintro rfl rfl
  rw [← Vector.foldl_assoc (op := op), Std.LawfulRightIdentity.right_id (op := op),
    ← Vector.foldl_append, Vector.extract_append_extract]
  rcases v with ⟨a, ha⟩
  simp [Nat.min_eq_left hlm, Nat.max_eq_right hmr]

end Impl

end TCR.SegmentTree
