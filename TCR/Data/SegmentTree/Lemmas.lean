/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import TCR.Data.SegmentTree.Basic
import all TCR.Data.SegmentTree.Basic
import TCR.Data.SegmentTree.WF

/-!
# Segment tree lemmas

This file characterizes segment tree modification operations in terms of `underlying`, and
proves an extensionality theorem for segment trees.
-/

namespace TCR.SegmentTree

namespace Impl

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

@[simp]
theorem underlying_modify {op : α → α → α} {v : Vector α (2 * n)} {i : Nat} {hi : i < n} {f : α → α} :
    underlying (modify op v i hi f) = (underlying v).modify i f := by
  suffices ∀ (vec : Vector α (2 * n)) idx hidx, underlying (modify.loop op i hi vec idx hidx) = underlying vec by
    simp only [modify, this]
    simp only [underlying, Vector.modify_cast, Vector.cast_eq_cast, Vector.cast_rfl]
    ext j hj
    simp [Vector.getElem_modify]
  intro vec idx hidx
  fun_induction modify.loop with grind [underlying]

@[simp]
theorem underlying_mkEmpty {neutral : α} {n : Nat} : underlying (mkEmpty neutral n) = Vector.replicate n neutral := by
  simp [underlying, mkEmpty]

end Impl

@[simp]
public theorem underlying_ofVector {op : α → α → α} {neutral : α} {v : Vector α n} :
    (SegmentTree.ofVector op neutral v).underlying = v :=
  Impl.underlying_mkSegmentTree

@[simp]
public theorem underlying_modify {op : α → α → α} {neutral : α} {t : SegmentTree op neutral n}
    {i : Nat} {hi : i < n} {f : α → α} : (t.modify i hi f).underlying = t.underlying.modify i f :=
  Impl.underlying_modify

@[simp]
public theorem underlying_empty {op : α → α → α} {neutral : α} {n : Nat} :
    (empty op neutral n).underlying = Vector.replicate n neutral :=
  Impl.underlying_mkEmpty

@[ext]
public protected theorem ext {op : α → α → α} {neutral : α} [Std.LawfulRightIdentity op neutral]
    {t t' : SegmentTree op neutral n} : t.underlying = t'.underlying → t = t' := by
  rcases t with ⟨t, ht⟩
  rcases t' with ⟨t', ht'⟩
  simpa using Impl.IsSegmentTree.underlying_inj _ _ ht.out ht'.out

end TCR.SegmentTree
