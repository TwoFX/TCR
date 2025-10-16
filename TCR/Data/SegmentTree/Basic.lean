/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

import TCR.Data.Vector

namespace TCR

/-- A vector of size `2 * n` is an `op`-segment tree if, when interpreted as a binary tree,
it satisfies the heap-like property that the parent is always the `op` of the children. -/
structure IsSegmentTree (op : α → α → α) (neutral : α) (v : Vector α (2 * n)) : Prop where
  /-- Given `i < n`, `v[i] = op v[2 * i + 1] v[2 * i + 2]`. -/
  op_eq : ∀ (i : Nat) (hi : i < n), v[i] = op v[2 * i + 1] (v[(2 * i + 2)]?.getD neutral)

/-- Creates a new `op`-segment tree on the vector `v`. -/
def mkSegmentTree (op : α → α → α) (neutral : α) (v : Vector α n) : Vector α (2 * n) :=
  let vec := Vector.mk (Array.replicate n neutral ++ v.toArray) (by grind)
  loop vec n (Nat.le_refl _)
where
  loop (vec : Vector α (2 * n)) (idx : Nat) (hidx : idx ≤ n) : Vector α (2 * n) :=
    match h : idx with
    | 0 => vec
    | idx' + 1 => loop (vec.set idx' (op vec[2 * idx' + 1] (vec.getD (2 * idx' + 2) neutral))) idx' (by grind)

theorem isSegmentTree_mkSegmentTree {op : α → α → α} {neutral : α} {v : Vector α n} :
    IsSegmentTree op neutral (mkSegmentTree op neutral v) := by
  rw [mkSegmentTree]
  exact loop _ _ (by grind)
where
  loop {vec : Vector α (2 * n)} (idx : Nat) (hidx : idx ≤ n)
      (h : ∀ idx', idx ≤ idx' → (h : idx' < n) →
        vec[idx'] = op vec[2 * idx' + 1] (vec.getD (2 * idx' + 2) neutral)) :
      IsSegmentTree op neutral (mkSegmentTree.loop op neutral vec idx hidx) := by
    fun_induction mkSegmentTree.loop with
    | case1 => exact ⟨by simpa using h⟩
    | case2 vec idx' hidx ih =>
      refine ih (fun idx'' h₁ h₂ => ?_)
      rw [Vector.getElem_set]
      split
      · rename_i h
        subst h
        rw [Vector.getElem_set_ne _ _ (by omega), Vector.getD_set_ne (by omega)]
      · rw [Vector.getElem_set_ne _ _ (by omega), Vector.getD_set_ne (by omega)]
        apply h <;> omega

/-- Given a segment tree, extracts the underlying data by copying it. -/
def underlying (v : Vector α (2 * n)) : Vector α n :=
  v.extract n (2 * n) |>.cast <| by grind

theorem getElem_eq_getElem_underlying {v : Vector α (2 * n)} {i : Nat} {hi : i < 2 * n} (hi' : n ≤ i) :
    v[i] = (underlying v)[i - n] := by
  simp [underlying]
  grind

theorem getElem?_eq_getElem?_underlying {v : Vector α (2 * n)} {i : Nat} (hi' : n ≤ i) :
    v[i]? = (underlying v)[i - n]? := by
  simp [underlying]
  grind [Vector.getElem?_extract]

@[simp]
theorem underlying_mkSegmentTree {op : α → α → α} {neutral : α} {v : Vector α n} :
    underlying (mkSegmentTree op neutral v) = v := by
  suffices ∀ (vec : Vector α (2 * n)) idx hidx, (mkSegmentTree.loop op neutral vec idx hidx).extract n (2 * n) = vec.extract n (2 * n) by
    simp [underlying, mkSegmentTree, this]
    grind
  intro vec idx hidx
  fun_induction mkSegmentTree.loop <;> grind

theorem IsSegmentTree.underlying_inj (v v' : Vector α (2 * n)) (hv : IsSegmentTree op neutral v) (hv' : IsSegmentTree op neutral v')
    (h : underlying v = underlying v') : v = v' := by
  suffices ∀ i, (h : i < n) → v[n - i - 1] = v'[n - i - 1] by
    ext i hi
    have := this (n - i - 1)
    grind [getElem_eq_getElem_underlying]
  intro i hi
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rw [hv.op_eq _ (by grind), hv'.op_eq _ (by grind)]
    have := ih (2 * i - n)
    have := ih (2 * i - 1 - n)
    grind (splits := 10) [getElem_eq_getElem_underlying]

end TCR
