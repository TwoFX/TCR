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
# Verification of the segment tree `query` operation (WIP)

This file will contain the internal part of the verification of the `query` operation on segment trees.
The final user-facing lemma will appear in `TCR.Data.SegmentTree.Lemmas`.
-/

namespace TCR.SegmentTree

namespace Impl

/-- `IsFold op neutral v l r a` is shorthand for the fact that `a` is obtained by folding `op` over `v[l...<r]`. -/
structure IsFold (op : α → α → α) (neutral : α) (v : Vector α k) (l r : Nat) (a : α) : Prop where
  eq_foldl : a = (v.extract l r).foldl op neutral

theorem isFold_iff {op : α → α → α} {neutral : α} {v : Vector α k} {l r : Nat} {a : α} :
    IsFold op neutral v l r a ↔ a = (v.extract l r).foldl op neutral := by
  grind  [IsFold]

@[simp]
theorem IsFold.base {op : α → α → α} {neutral : α} {v : Vector α k} {l} : IsFold op neutral v l l neutral := by
  simp [isFold_iff, Vector.extract_eq_cast_empty (Nat.min_le_left l k)]

theorem IsFold.singleton {op : α → α → α} {neutral : α} [Std.LawfulLeftIdentity op neutral] {v : Vector α k} {l} (hl : l < k) :
    IsFold op neutral v l (l + 1) v[l] := by
  simp [isFold_iff, Vector.extract_add_one (by omega : l + 1 ≤ k), Std.LawfulLeftIdentity.left_id (op := op)]

theorem IsFold.concat {op : α → α → α} {neutral : α} [Std.Associative op] [Std.LawfulRightIdentity op neutral]
    {v : Vector α k} {l m r} {a b : α} (hlm : l ≤ m) (hmr : m ≤ r) :
    IsFold op neutral v l m a → IsFold op neutral v m r b → IsFold op neutral v l r (op a b) := by
  simp only [isFold_iff, isFold_iff]
  rintro rfl rfl
  rw [← Vector.foldl_assoc (op := op), Std.LawfulRightIdentity.right_id (op := op),
    ← Vector.foldl_append, Vector.extract_append_extract]
  rcases v with ⟨a, ha⟩
  simp [Nat.min_eq_left hlm, Nat.max_eq_right hmr]

/-- `IsValidAtDepth op neutral v depth i` says that `v[i]` is the root of a complete binary subtree of depth
`depth` and contains the correct fold over that subtree. -/
structure IsValidAtDepth (op : α → α → α) (neutral : α) (v : Vector α k) (depth i : Nat) : Prop where
  hi : i < k
  isFold : IsFold op neutral v (2 ^ depth * i) (2 ^ depth * (i + 1)) v[i]

theorem isValidAtDepth_zero {op : α → α → α} {neutral : α} [Std.LawfulLeftIdentity op neutral]
    {v : Vector α k} {i : Nat} (hi : i < k) : IsValidAtDepth op neutral v 0 i where
  hi := hi
  isFold := by simpa using IsFold.singleton _

theorem IsValidAtDepth.succ {op : α → α → α} {neutral : α}
    [Std.Associative op] [Std.LawfulRightIdentity op neutral]
    {v : Vector α k} {i : Nat} (hleft : IsValidAtDepth op neutral v depth (2 * i))
    (hright : IsValidAtDepth op neutral v depth (2 * i + 1))
    (heq : v[i]'(by have := hright.hi; omega) = op (v[2 * i]'(hleft.hi)) (v[2 * i + 1]'(hright.hi))) :
    IsValidAtDepth op neutral v (depth + 1) i where
  hi := by have := hright.hi; omega
  isFold := by
    have hfl := hleft.isFold
    have hfr := hright.isFold
    rw [← Nat.mul_assoc, ← Nat.pow_add_one] at hfl
    have : 2 ^ depth * (2 * i + 1 + 1) = 2 ^ (depth + 1) * (i + 1) := by grind
    rw [this] at hfr
    rw [heq]
    exact IsFold.concat (by grind) (by grind) hfl hfr

theorem IsSegmentTree.isValidAtDepth_succ {op : α → α → α} {neutral : α}
    [Std.Associative op] [Std.LawfulRightIdentity op neutral]
    {v : Vector α (2 * n)} (hv : IsSegmentTree op neutral v) {i : Nat} (hi : 0 < i)
    (hleft : IsValidAtDepth op neutral v depth (2 * i))
    (hright : IsValidAtDepth op neutral v depth (2 * i + 1)) :
    IsValidAtDepth op neutral v (depth + 1) i := by
  apply IsValidAtDepth.succ hleft hright (hv.op_eq _ hi _)
  have := hleft.hi
  grind

theorem grind_wishlist_0 {l i : Nat} (hl : l % 2 = 0) :
    2 ^ (i + 1) * ((l + 1) / 2) = 2 ^ i * l := by
  obtain ⟨d, rfl⟩ : ∃ d, l = 2 * d := Nat.dvd_of_mod_eq_zero hl
  have : (2 * d + 1) / 2 = d := by grind
  grind

theorem grind_wishlist_1 {l i : Nat} (hl : l % 2 ≠ 0) :
    2 ^ (i + 1) * ((l + 1) / 2) = 2 ^ i * (l + 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, l = 2 * d + 1 :=
    ⟨l / 2, Nat.mod_two_ne_zero.1 hl ▸ (Nat.div_add_mod l 2).symm⟩
  have : (2 * d + 1 + 1) / 2 = d + 1 := by grind
  grind

theorem grind_wishlist_2 {r i : Nat} (hr : r % 2 = 0) :
    2 ^ (i + 1) * (r / 2) = 2 ^ i * r := by
  obtain ⟨d, rfl⟩ : ∃ d, r = 2 * d := Nat.dvd_of_mod_eq_zero hr
  simp [Nat.pow_succ, Nat.mul_assoc]

theorem grind_wishlist_3 {r i : Nat} (hr : r % 2 ≠ 0) :
    2 ^ (i + 1) * (r / 2) = 2 ^ i * (r - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d, r = 2 * d + 1 :=
    ⟨r / 2, Nat.mod_two_ne_zero.1 hr ▸ (Nat.div_add_mod r 2).symm⟩
  have : (2 * d + 1) / 2 = d := by grind
  grind

theorem grind_wishlist_4 {r i : Nat} (hr : r % 2 ≠ 0) :
    2 ^ i * (r - 1 + 1) = 2 ^ i * r := by
  rw [Nat.sub_add_cancel (by grind)]

theorem query_loop {op : α → α → α} {neutral : α} [Std.Associative op] [Std.LawfulRightIdentity op neutral]
    {v : Vector α (2 * n)} (hv : IsSegmentTree op neutral v)
    {l₀ r₀ : Nat} {resl resr : α} (i : Nat)
    {l r : Nat} (hlx : l₀ + n ≤ 2 ^ i * l) (hrx : 2 ^ i * r ≤ r₀ + n)
    (hresl : IsFold op neutral v (l₀ + n) (2 ^ i * l) resl)
    (hresr : IsFold op neutral v (2 ^ i * r) (r₀ + n) resr)
    (hvalid : ∀ k, l ≤ k → k < r → IsValidAtDepth op neutral v i k)
    {hlr' hr'} :
    IsFold op neutral v (l₀ + n) (r₀ + n) (query.loop op v l r resl resr hlr' hr') := by
  fun_induction query.loop generalizing i with
  | case1 l r resl resr _ hr hlr resl' resr' ih =>
    apply ih (i + 1) <;> clear ih
    · rw [Nat.pow_succ, Nat.mul_assoc]
      exact Nat.le_trans hlx (Nat.mul_le_mul_left _ (by grind))
    · rw [Nat.pow_succ, Nat.mul_assoc]
      exact Nat.le_trans (Nat.mul_le_mul_left _ (by grind)) hrx
    · subst resl'
      split <;> rename_i hl
      · rwa [(grind_wishlist_0 hl : 2 ^ (i + 1) * ((l + 1) / 2) = 2 ^ i * l)]
      · have hisf := (hvalid l (by simp) (by omega)).isFold
        have : 2 ^ (i + 1) * ((l + 1) / 2) = 2 ^ i * (l + 1) := grind_wishlist_1 hl
        exact this ▸ hresl.concat hlx (by grind) hisf
    · subst resr'
      split <;> rename_i hr
      · have : 2 ^ (i + 1) * (r / 2) = 2 ^ i * r := grind_wishlist_2 hr
        rwa [this]
      · have hisf := (hvalid (r - 1) (by omega) (by omega)).isFold
        have hr₁ : 2 ^ (i + 1) * (r / 2) = 2 ^ i * (r - 1) := grind_wishlist_3 hr
        have hr₂ : 2 ^ i * (r - 1 + 1) = 2 ^ i * r := grind_wishlist_4 hr
        exact hr₁ ▸ (hr₂ ▸ hisf).concat (by grind) hrx hresr
    · intro k hkl hkr
      apply hv.isValidAtDepth_succ <;> grind
  | case2 l r resl resr h₁ h₂ h₃ =>
    obtain rfl : l = r := by grind
    exact hresl.concat hlx hrx hresr

theorem isFold_query {op : α → α → α} {neutral : α} [Std.Associative op] [Std.LawfulIdentity op neutral]
    {v : Vector α (2 * n)} (hv : IsSegmentTree op neutral v) {l r : Nat} {hlr : l ≤ r} {hr : r ≤ n} :
    IsFold op neutral v (l + n) (r + n) (query op neutral v l r hlr hr) :=
  query_loop hv 0 (by simp) (by simp) (by simp) (by simp) (fun k hkl hkr => isValidAtDepth_zero (by omega))

theorem extract_underlying {v : Vector α (2 * n)} :
    (underlying v).extract l r = (v.extract (l + n) (r + n)).cast (by omega) := by
  ext1
  simp only [underlying, Vector.getElem_extract, Vector.getElem_cast]
  grind

theorem query_eq_foldl {op : α → α → α} {neutral : α} [Std.Associative op] [Std.LawfulIdentity op neutral]
    {v : Vector α (2 * n)} (hv : IsSegmentTree op neutral v) {l r : Nat} {hlr hr} :
    query op neutral v l r hlr hr = ((underlying v).extract l r).foldl op neutral := by
  simpa [extract_underlying, Vector.foldl_cast, ← isFold_iff] using isFold_query hv

end Impl

end TCR.SegmentTree
