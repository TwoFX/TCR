/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

import TCR.Data.Vector
import all TCR.Data.SegmentTree.Basic

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
structure IsFold (op : α → α → α) (neutral : α) (v : Vector α k) (l r : Nat) (a : α) : Prop where
  eq_foldl : a = (v.extract l r).foldl op neutral

theorem isFold_iff {op : α → α → α} {neutral : α} {v : Vector α k} {l r : Nat} {a : α} :
    IsFold op neutral v l r a ↔ a = (v.extract l r).foldl op neutral := by
  grind  [IsFold]

@[simp]
theorem IsFold.base {op : α → α → α} {neutral : α} {v : Vector α k} {l} : IsFold op neutral v l l neutral := by
  simp [isFold_iff, Vector.extract_eq_cast_empty (Nat.min_le_left l k)]

theorem Vector.extract_add_one {v : Vector α n} {i : Nat} (hi : i + 1 ≤ n) :
    v.extract i (i + 1) = #v[v[i]].cast (by omega) := by
  ext j hj
  simp [(by omega : j = 0)]

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

def Nat.divCeil (a b : Nat) : Nat :=
  (a + b - 1) / b

theorem Nat.divCeil_eq {a b : Nat} (hb : 0 < b) :
    Nat.divCeil a b = if b ∣ a then a / b else a / b + 1 := by
  rw [Nat.divCeil]
  rw (occs := [1]) [← Nat.div_add_mod a b, Nat.add_assoc, Nat.add_sub_assoc (by grind),
    Nat.mul_add_div hb]
  split <;> rename_i hab
  · rw [Nat.mod_eq_zero_of_dvd hab, Nat.zero_add, (Nat.div_eq_zero_iff_lt (x := b - 1) hb).2 (Nat.sub_one_lt (by omega)), Nat.add_zero]
  · congr
    refine (Nat.div_eq_iff hb).2 ⟨?_, ?_⟩
    · suffices 0 < a % b by grind
      rwa [Nat.pos_iff_ne_zero, ne_eq, ← Nat.dvd_iff_mod_eq_zero]
    · have := Nat.mod_lt a hb
      grind

def leftalign (l₀ : Nat) (i : Nat) : Nat :=
  (l₀ + 2 ^ i - 1) / (2 ^ i)

theorem leftalign_eq_divCeil {l₀ i : Nat} : leftalign l₀ i = Nat.divCeil l₀ (2 ^ i) := rfl

@[simp, grind =]
theorem leftalign_zero {l : Nat} : leftalign l 0 = l := by
  grind [leftalign]

theorem leftalign_add_one {l₀ : Nat} {i : Nat} :
    leftalign l₀ (i + 1) = (leftalign l₀ i + 1) / 2 := by
  rw [leftalign_eq_divCeil, leftalign_eq_divCeil,
    Nat.divCeil_eq (Nat.two_pow_pos _), Nat.divCeil_eq (Nat.two_pow_pos _)]
  split <;> rename_i h₁
  · obtain ⟨d, rfl⟩ := h₁
    rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    rw [if_pos (by simp [Nat.pow_succ, Nat.mul_assoc, Nat.dvd_mul_right]),
      Nat.pow_succ, Nat.mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
    grind
  · split <;> rename_i h₂
    · obtain ⟨d, rfl⟩ := h₂
      simp [Nat.pow_succ, Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos _)] at h₁
      have hd₁ : d % 2 = 1 := by grind
      have : 2 ^ i * d / 2 ^ (i + 1) = d / 2 := by
        rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
      rw [this]
      rw [Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
      grind
    · have : (l₀ / 2 ^ i + 1 + 1) / 2 = l₀ / (2 ^ i) / 2 + 1 := by grind
      rw [this, Nat.div_div_eq_div_mul, ← Nat.pow_succ]

theorem le_leftalign {l₀ i : Nat} : l₀ ≤ 2 ^ i * leftalign l₀ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Nat.pow_succ, leftalign_add_one, Nat.mul_assoc]
    exact Nat.le_trans ih (Nat.mul_le_mul_left _ (by grind))

def rightalign (r₀ : Nat) (i : Nat) : Nat :=
  r₀ / (2 ^ i)

@[simp]
theorem rightalign_zero {r : Nat} : rightalign r 0 = r := by
  grind [rightalign]

theorem rightalign_add_one {r₀ : Nat} {i : Nat} :
    rightalign r₀ (i + 1) = rightalign r₀ i / 2 := by
  rw [rightalign, rightalign, Nat.div_div_eq_div_mul, Nat.pow_succ]

theorem rightalign_le {r₀ i : Nat} : 2 ^ i * rightalign r₀ i ≤ r₀ := by
  rw [rightalign, Nat.mul_div_self_eq_mod_sub_self]
  simp

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
    {l r : Nat} (hlx : l = leftalign (l₀ + n) i) (hrx : r = rightalign (r₀ + n) i)
    (hresl : IsFold op neutral v (l₀ + n) (2 ^ i * l) resl) (hresr : IsFold op neutral v (2 ^ i * r) (r₀ + n) resr)
    (hvalid : ∀ k, l ≤ k → k < r → IsValidAtDepth op neutral v i k)
    {hlr' hr'} :
    IsFold op neutral v (l₀ + n) (r₀ + n) (query.loop op v l r resl resr hlr' hr') := by
  fun_induction query.loop generalizing i with
  | case1 l r resl resr _ hr hlr resl' resr' ih =>
    apply ih (i + 1) <;> clear ih
    · rw [hlx, leftalign_add_one]
    · rw [hrx, rightalign_add_one]
    · subst resl'
      split <;> rename_i hl
      · have : 2 ^ (i + 1) * ((l + 1) / 2) = 2 ^ i * l := grind_wishlist_0 hl
        rwa [this]
      · have hisf := (hvalid l (by simp) (by omega)).isFold
        have : 2 ^ (i + 1) * ((l + 1) / 2) = 2 ^ i * (l + 1) := grind_wishlist_1 hl
        rw [this]
        exact hresl.concat (hlx ▸ le_leftalign) (by grind) hisf
    · subst resr'
      split <;> rename_i hr
      · have : 2 ^ (i + 1) * (r / 2) = 2 ^ i * r := grind_wishlist_2 hr
        rwa [this]
      · have hisf := (hvalid (r - 1) (by omega) (by omega)).isFold
        have hr₁ : 2 ^ (i + 1) * (r / 2) = 2 ^ i * (r - 1) := grind_wishlist_3 hr
        have hr₂ : 2 ^ i * (r - 1 + 1) = 2 ^ i * r := grind_wishlist_4 hr
        rw [hr₂] at hisf
        rw [hr₁]
        exact hisf.concat (by grind) (hrx ▸ rightalign_le) hresr
    · intro k hkl hkr
      apply hv.isValidAtDepth_succ
      · have : 0 < n := by omega
        have := le_leftalign (l₀ := l₀ + n) (i := i)
        grind
      · apply hvalid <;> omega
      · apply hvalid <;> omega
  | case2 l r resl resr h₁ h₂ h₃ =>
    obtain rfl : l = r := by grind
    exact hresl.concat (hlx ▸ le_leftalign) (hrx ▸ rightalign_le) hresr

theorem isFold_query {op : α → α → α} {neutral : α} [Std.Associative op] [Std.LawfulIdentity op neutral]
    {v : Vector α (2 * n)} (hv : IsSegmentTree op neutral v) {l r : Nat} {hlr : l ≤ r} {hr : r ≤ n} :
    IsFold op neutral v (l + n) (r + n) (query op neutral v l r hlr hr) :=
  query_loop hv 0 (by simp) (by simp) (by simp) (by simp) (fun k hkl hkr => isValidAtDepth_zero (by omega))

end Impl

end TCR.SegmentTree
