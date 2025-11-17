/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import TCR.Data.SegmentTree.Basic
import all TCR.Data.SegmentTree.Basic
import TCR.Data.Vector

/-!
# Verification of the segment tree `query` operation

This file will contain the internal part of the verification of the `query` operation on segment trees.
The final user-facing lemma appears in `TCR.Data.SegmentTree.Lemmas`.
-/

open Std

namespace TCR.SegmentTree

namespace Impl

/-!
# `IsFold`
-/

/-- `IsFold op neutral v l r x` means that `x = [l, r) = v[l] op v[l + 1] op … op v[r - 1]`. -/
structure IsFold (op : α → α → α) (neutral : α) (v : Vector α k) (l r : Nat) (x : α) : Prop where
  le : l ≤ r
  eq_foldl : x = (v.extract l r).foldl op neutral

attribute [grind →] IsFold.le

theorem isFold_iff {op : α → α → α} {neutral : α} {v : Vector α k} {l r : Nat} {a : α} :
    IsFold op neutral v l r a ↔ l ≤ r ∧ a = (v.extract l r).foldl op neutral := by
  grind [IsFold]

@[simp]
theorem IsFold.base {op : α → α → α} {neutral : α} {v : Vector α k} {l} : IsFold op neutral v l l neutral := by
  simp [isFold_iff, Vector.extract_eq_cast_empty (Nat.min_le_left l k)]

theorem IsFold.singleton {op : α → α → α} {neutral : α} [LawfulLeftIdentity op neutral] {v : Vector α k} {l} (hl : l < k) :
    IsFold op neutral v l (l + 1) v[l] := by
  simp [isFold_iff, Vector.extract_add_one (by omega : l + 1 ≤ k), LawfulLeftIdentity.left_id (op := op)]

theorem IsFold.concat {op : α → α → α} {neutral : α} [Associative op] [LawfulRightIdentity op neutral]
    {v : Vector α k} {l m r} {a b : α} :
    IsFold op neutral v l m a → IsFold op neutral v m r b → IsFold op neutral v l r (op a b) := by
  simp only [isFold_iff]
  rintro ⟨hlm, rfl⟩ ⟨hmr, rfl⟩
  rw [← Vector.foldl_assoc (op := op), LawfulRightIdentity.right_id (op := op),
    ← Vector.foldl_append, Vector.extract_append_extract]
  rcases v with ⟨a, ha⟩
  simp [Nat.min_eq_left hlm, Nat.max_eq_right hmr, Nat.le_trans hlm hmr]

theorem IsFold.concat_of_eq {op : α → α → α} {neutral : α} [Associative op] [LawfulRightIdentity op neutral]
    {v : Vector α k} {l m m' r} {a b : α} :
    IsFold op neutral v l m a → IsFold op neutral v m' r b → m = m' → IsFold op neutral v l r (op a b) := by
  rintro h₁ h₂ rfl
  exact h₁.concat h₂

theorem IsFold.of_congr {op : α → α → α} {neutral : α} {v : Vector α k} {l r l' r' a a'} (hl : l = l') (hr : r = r') (ha : a = a') :
    IsFold op neutral v l r a → IsFold op neutral v l' r' a' := by
  subst hl hr ha
  exact id

/-!
# `below`
-/

/--
`below d i` is just `2 ^ d * i`. Since this expression plays a central role in the
verification of the `query` operation, it makes sense to develop explicit API for it.
-/
def below (d i : Nat) : Nat :=
  2 ^ d * i

@[simp]
theorem below_zero {i : Nat} : below 0 i = i := by
  simp [below]

@[grind =]
theorem below_add_one_div_two_of_mod_two_eq_zero {d i : Nat} (hi : i % 2 = 0) :
    below (d + 1) (i / 2) = below d i := by
  have hi : i = 2 * (i / 2) := by grind
  grind [below]

@[grind =]
theorem below_add_one_div_two_of_mod_two_ne_zero {d i : Nat} (hi : i % 2 ≠ 0) :
    below (d + 1) (i / 2) = below d (i - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = 2 * j  + 1 :=
    ⟨i / 2, Nat.mod_two_ne_zero.1 hi ▸ (Nat.div_add_mod i 2).symm⟩
  have : (2 * j + 1) / 2 = j := by grind
  grind [below]

/-!
# `HasHeight`
-/

/--
`HasHeight op neutral v depth i` says that `v[i]` is the root of a complete binary subtree of depth
`depth` and contains the correct fold over that subtree.
-/
structure HasHeight (op : α → α → α) (neutral : α) (v : Vector α k) (depth i : Nat) : Prop where
  lt : i < k
  isFold : IsFold op neutral v (below depth i) (below depth (i + 1)) v[i]

attribute [grind →] HasHeight.lt

theorem hasHeight_zero {op : α → α → α} {neutral : α} [LawfulLeftIdentity op neutral]
    {v : Vector α k} {i : Nat} (hi : i < k) : HasHeight op neutral v 0 i where
  lt := hi
  isFold := by simpa using IsFold.singleton _

theorem HasHeight.succ {op : α → α → α} {neutral : α}
    [Associative op] [LawfulRightIdentity op neutral]
    {v : Vector α k} {i : Nat} (hleft : HasHeight op neutral v depth (2 * i))
    (hright : HasHeight op neutral v depth (2 * i + 1))
    (heq : v[i] = op (v[2 * i]) (v[2 * i + 1])) :
    HasHeight op neutral v (depth + 1) i where
  lt := by have := hright.lt; omega
  isFold := by refine (hleft.isFold.concat hright.isFold).of_congr ?_ ?_ heq.symm <;> grind [below]

theorem IsSegmentTree.hasHeight_succ {op : α → α → α} {neutral : α}
    [Associative op] [LawfulRightIdentity op neutral]
    {v : Vector α (n + n)} (hv : IsSegmentTree op neutral v) {i : Nat} (hi : 0 < i)
    (hleft : HasHeight op neutral v depth (2 * i))
    (hright : HasHeight op neutral v depth (2 * i + 1)) :
    HasHeight op neutral v (depth + 1) i := by
  apply HasHeight.succ hleft hright (hv.op_eq _ hi _)
  have := hleft.lt
  grind

/-!
# Verification of `query`
-/

theorem isFold_queryLoop {op : α → α → α} {neutral : α} [Associative op] [LawfulRightIdentity op neutral]
    {v : Vector α (n + n)} (hv : IsSegmentTree op neutral v)
    -- (n_is_power_of_two : ∃ d, n = 2 ^ d)
    {l₀ r₀ : Nat} {resl resr : α} (i : Nat) {l r : Nat} {hlr}
    (hheight : ∀ k, l ≤ k → k < r → HasHeight op neutral v i k)
    (hresl : IsFold op neutral v (l₀ + n) (below i l) resl)
    (hresr : IsFold op neutral v (below i r) (r₀ + n) resr) :
    IsFold op neutral v (l₀ + n) (r₀ + n) (query.loop op v l r resl resr hlr) := by
  -- clear n_is_power_of_two
  fun_induction query.loop generalizing i with
  | case1 l r resl resr hlr₀ hlr resl' resr' ih =>
    subst resl' resr'; apply ih (i + 1) <;> clear ih
    · intro k hkl hkr
      apply hv.hasHeight_succ <;> grind [below]
    · split
      · grind
      · exact (hresl.concat (hheight l (by simp) hlr).isFold).of_congr rfl (by grind) rfl
    · split
      · grind
      · exact ((hheight (r - 1) (by omega) (by omega)).isFold.concat_of_eq hresr (by grind)).of_congr (by grind) rfl rfl
  | case2 l r resl resr h₁ h₂ => exact hresl.concat_of_eq hresr (by grind)

theorem isFold_query {op : α → α → α} {neutral : α} [Associative op] [LawfulIdentity op neutral]
    {v : Vector α (n + n)} (hv : IsSegmentTree op neutral v) {l r : Nat} {hlr : l ≤ r} {hr : r ≤ n} :
    IsFold op neutral v (l + n) (r + n) (query op neutral v l r hlr hr) :=
  isFold_queryLoop hv 0 (fun k hkl hkr => hasHeight_zero (by omega)) (by simp) (by simp)

theorem extract_underlying {v : Vector α (n + n)} :
    (underlying v).extract l r = (v.extract (l + n) (r + n)).cast (by omega) := by
  ext1
  simp only [underlying, Vector.getElem_extract, Vector.getElem_cast]
  grind

theorem query_eq_foldl {op : α → α → α} {neutral : α} [Associative op] [LawfulIdentity op neutral]
    {v : Vector α (n + n)} (hv : IsSegmentTree op neutral v) {l r : Nat} {hlr hr} :
    query op neutral v l r hlr hr = ((underlying v).extract l r).foldl op neutral := by
  simpa only [extract_underlying] using (isFold_iff.1 (isFold_query hv)).2

end Impl

end TCR.SegmentTree
