/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import TCR.Data.SegmentTree.Basic
import all TCR.Data.SegmentTree.Basic

/-!
# Well-formedness of segment trees

In this file we prove the all segment tree operations preserve well-formedness.
-/

namespace TCR.SegmentTree

namespace Impl

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
        · rename_i hx
          subst hx
          grind [Vector.getElem_set_ne]
        · grind [Vector.getElem_set_ne]

theorem IsSegmentTree.modify {op : α → α → α} {neutral : α} {v : Vector α (2 * n)} (hv : IsSegmentTree op neutral v)
    {i : Nat} (hi : i < n) (f : α → α) : IsSegmentTree op neutral (modify op v i hi f) := by
  rw [Impl.modify]
  apply loop <;> grind [Vector.getElem_modify_of_ne, IsSegmentTree.zero_eq, IsSegmentTree.op_eq]
where
  loop {vec : Vector α (2 * n)} {idx hidx₀ hidx} (h₀ : vec[0] = neutral)
      (h : ∀ (i : Nat) (_ : 0 < i) (hi : i < n) (_ : i ≠ idx), vec[i] = op vec[2 * i] vec[2 * i + 1]) :
      IsSegmentTree op neutral (modify.loop op i hi vec idx hidx) := by
    fun_induction modify.loop with grind [IsSegmentTree]

theorem isSegmentTree_mkEmpty {op : α → α → α} {neutral : α} [Std.LawfulRightIdentity op neutral] {n : Nat} :
    IsSegmentTree op neutral (mkEmpty neutral n) where
  zero_eq h := by simp [mkEmpty]
  op_eq i hi₀ hi := by simp [mkEmpty, Std.LawfulRightIdentity.right_id]

/-- A well-formed segment tree has the segment tree property. -/
public theorem WF.out {op : α → α → α} {neutral : α} [Std.LawfulRightIdentity op neutral] :
    {v : Vector α (2 * n)} → Impl.WF op neutral v → IsSegmentTree op neutral v
  | _, .isSegmentTree h => h
  | _, .mkSegmentTree => isSegmentTree_mkSegmentTree
  | _, .mkEmpty => isSegmentTree_mkEmpty
  | _, .modify h => h.out.modify ..

end Impl

public theorem isSegmentTree_tree {op : α → α → α} {neutral : α} [Std.LawfulRightIdentity op neutral]
    (t : SegmentTree op neutral n) : Impl.IsSegmentTree op neutral t.tree :=
  t.wf.out

end TCR.SegmentTree
