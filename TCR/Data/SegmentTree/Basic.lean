/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

import TCR.Data.Vector
import TCR.Data.Nat

namespace TCR

/-- A vector of size `2 * n` is an `op`-segment tree if, when interpreted as a binary tree,
it satisfies the heap-like property that the parent is always the `op` of the children. -/
structure IsSegmentTree (op : α → α → α) (neutral : α) (v : Vector α (2 * n)) : Prop where
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

theorem isSegmentTree_mkSegmentTree {op : α → α → α} {neutral : α} {v : Vector α n} :
    IsSegmentTree op neutral (mkSegmentTree op neutral v) := by
  rw [mkSegmentTree]
  split
  · refine ⟨by simp_all, by simp_all⟩
  · refine loop _ _ ?_ (by grind)
    simp_all [Array.getElem_append]
where
  loop {vec : Vector α (2 * n)} (idx : Nat) (hidx : idx < n)
      (h₀ : vec[0] = neutral)
      (h : ∀ idx', 0 < idx' → idx < idx' → (h : idx' < n) →
        vec[idx'] = op vec[2 * idx'] vec[2 * idx' + 1]) :
      IsSegmentTree op neutral (mkSegmentTree.loop op vec idx hidx) := by
    fun_induction mkSegmentTree.loop with
    | case1 => exact ⟨by simp_all, by simpa using h⟩
    | case2 vec idx' hidx ih =>
      refine ih ?_ (fun idx'' h₁ h₂ h₃ => ?_)
      · rw [Vector.getElem_set_ne _ _ (by omega), h₀]
      · rw [Vector.getElem_set]
        split
        · rename_i h
          subst h
          rw [Vector.getElem_set_ne _ _ (by omega), Vector.getElem_set_ne _ _ (by omega)]
        · rw [Vector.getElem_set_ne _ _ (by omega), Vector.getElem_set_ne _ _ (by omega)]
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
  rw [mkSegmentTree]
  split
  · simp_all [underlying]
  suffices ∀ (vec : Vector α (2 * n)) idx hidx,
      (mkSegmentTree.loop op vec idx hidx).extract n (2 * n) = vec.extract n (2 * n) by
    simp [underlying, this]
    grind
  intro vec idx hidx
  fun_induction mkSegmentTree.loop <;> grind

theorem IsSegmentTree.underlying_inj (v v' : Vector α (2 * n))
    (hv : IsSegmentTree op neutral v) (hv' : IsSegmentTree op neutral v')
    (h : underlying v = underlying v') : v = v' := by
  suffices ∀ i, (h : i < n - 1) → v[n - i - 1] = v'[n - i - 1] by
    ext i hi
    have := this (n - i - 1)
    have := hv.zero_eq
    have := hv'.zero_eq
    grind [getElem_eq_getElem_underlying]
  intro i hi
  induction i using Nat.strongRecOn with
  | ind i ih =>
    rw [hv.op_eq _ (by grind) (by grind), hv'.op_eq _ (by grind) (by grind)]
    have := ih (2 * i + 1 - n)
    have := ih (2 * i - n)
    grind (splits := 12) [getElem_eq_getElem_underlying]

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

@[simp]
theorem underlying_modify {op : α → α → α} {v : Vector α (2 * n)} {i : Nat} {hi : i < n} {f : α → α} :
    underlying (modify op v i hi f) = (underlying v).modify i f := by
  suffices ∀ (vec : Vector α (2 * n)) idx hidx, underlying (modify.loop op i hi vec idx hidx) = underlying vec by
    simp only [modify, this]
    simp only [underlying, Vector.modify_cast, Vector.cast_eq_cast, Vector.cast_rfl]
    ext j hj
    simp [Vector.getElem_modify]
  intro vec idx hidx
  fun_induction modify.loop with  grind [underlying]

theorem IsSegmentTree.modify {op : α → α → α} {neutral : α} {v : Vector α (2 * n)} (hv : IsSegmentTree op neutral v)
    {i : Nat} (hi : i < n) (f : α → α) : IsSegmentTree op neutral (modify op v i hi f) := by
  rw [TCR.modify]
  apply loop <;> grind [Vector.getElem_modify_of_ne, IsSegmentTree.zero_eq, IsSegmentTree.op_eq]
where
  loop {vec : Vector α (2 * n)} {idx hidx₀ hidx} (h₀ : vec[0] = neutral)
      (h : ∀ (i : Nat) (_ : 0 < i) (hi : i < n) (_ : i ≠ idx), vec[i] = op vec[2 * i] vec[2 * i + 1]) :
      IsSegmentTree op neutral (modify.loop op i hi vec idx hidx) := by
    fun_induction modify.loop with grind [IsSegmentTree]

end TCR
