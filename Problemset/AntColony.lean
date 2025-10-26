/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

import TCR.Data.SegmentTree.Lemmas

/-!
# Codeforces 474F: Ant colony

https://codeforces.com/contest/474/problem/F
-/

namespace Problemset.AntColony

open TCR

section Solution

structure Input where
  n : Nat
  s : Vector Nat n
  t : Nat
  q : Vector { lr : Nat × Nat // lr.1 ≤ lr.2 ∧ lr.2 < n } t

@[ext]
structure Entry where
  val : Nat
  count : Nat

def Entry.combine (e₁ e₂ : Entry) : Entry where
  val := Nat.gcd e₁.val e₂.val
  count :=
    let c₁ := if Nat.gcd e₁.val e₂.val = e₁.val then e₁.count else 0
    let c₂ := if Nat.gcd e₁.val e₂.val = e₂.val then e₂.count else 0
    c₁ + c₂

def Entry.singleton (a : Nat) : Entry where
  val := a
  count := 1

def Entry.neutral : Entry where
  val := 0
  count := 0

def solve (inp : Input) : Vector Nat inp.t :=
  let segtree := SegmentTree.ofVector Entry.combine Entry.neutral (inp.s.map Entry.singleton)
  inp.q.map (fun lr => answerQuery segtree lr.1.1 lr.1.2 lr.2.1 lr.2.2)
where
  answerQuery {n : Nat} (segtree : SegmentTree Entry.combine Entry.neutral n)
      (l : Nat) (r : Nat) (hlr : l ≤ r) (hr : r < n) : Nat :=
    r - l + 1 - (segtree.query l (r + 1) (by omega) (by omega)).count

end Solution

section Sample

def sampleInput : Input where
  n := 5
  s := #v[1, 3, 2, 4, 2]
  t := 4
  q := #v[
    ⟨(0, 4), by decide⟩,
    ⟨(1, 4), by decide⟩,
    ⟨(2, 4), by decide⟩,
    ⟨(3, 4), by decide⟩,
  ]

example : solve sampleInput = #v[4, 4, 1, 1] := by native_decide

end Sample

section Specification

def answerForSegment (s : Vector Nat n) : Nat :=
  n - s.countP (fun x => s.all (fun y => x ∣ y))

structure IsCorrectAnswer (inp : Input) (v : Vector Nat inp.t) where
  eq_length_filter : ∀ i, (hi : i < inp.t) → v[i] = answerForSegment (inp.s.extract inp.q[i].1.1 (inp.q[i].1.2 + 1))

end Specification

section Verification

@[simp]
theorem Entry.val_singleton {a : Nat} :
    (Entry.singleton a).val = a := rfl

@[simp]
theorem Entry.count_singleton {a : Nat} :
    (Entry.singleton a).count = 1 := rfl

@[simp]
theorem Entry.val_neutral : Entry.neutral.val = 0 := rfl

@[simp]
theorem Entry.count_neutral : Entry.neutral.count = 0 := rfl

instance : Std.Associative Entry.combine where
  assoc e₁ e₂ e₃ := by grind [Entry.combine]

instance : Std.LawfulIdentity Entry.combine Entry.neutral where
  left_id _ := by ext <;> simp [Entry.combine]
  right_id _ := by ext <;> simp [Entry.combine]

theorem Entry.combine_comm {e₁ e₂ : Entry} : e₁.combine e₂ = e₂.combine e₁ := by
  grind [Entry.combine]

theorem foldl_dvd_of_mem {l : List Nat} {x : Nat} (hx : x ∈ l) : l.foldl Nat.gcd 0 ∣ x := by
  induction l with
  | nil => simp at hx
  | cons hd tl ih =>
    rw [List.foldl_cons, Nat.gcd_comm, List.foldl_assoc]
    obtain (rfl|hx) := List.mem_cons.1 hx
    · exact Nat.gcd_dvd_left ..
    · exact Nat.dvd_trans (Nat.gcd_dvd_right ..) (ih hx)

theorem foldl_map_combine (v : Vector Nat n) :
    (v.map Entry.singleton).foldl Entry.combine Entry.neutral =
      ⟨v.foldl Nat.gcd 0, v.count (v.foldl Nat.gcd 0)⟩ := by
  rcases v with ⟨⟨v⟩, hv⟩
  simp only [Vector.map_mk, List.map_toArray, Vector.foldl_mk, List.size_toArray, List.length_map,
    List.foldl_toArray', Vector.count_mk, List.count_toArray]
  clear n hv
  induction v with
  | nil => simp [Entry.neutral]
  | cons hd tl ih =>
    rw [List.map_cons, List.foldl_cons, Entry.combine_comm,
      List.foldl_assoc, ih]
    ext
    · simp only [Entry.combine, Entry.val_singleton, Entry.count_singleton, List.foldl_cons,
        Nat.gcd_zero_left]
      rw [← List.foldl_assoc (op := Nat.gcd), Nat.gcd_zero_right]
    · simp only [Entry.combine, Entry.val_singleton, Entry.count_singleton, List.foldl_cons,
        Nat.gcd_zero_left, List.count_cons, beq_iff_eq]
      conv => rhs; congr; rw [← Nat.gcd_zero_right hd]
      conv => rhs; enter [2]; congr; rhs; rw [← Nat.gcd_zero_right hd]
      simp only [List.foldl_assoc]
      by_cases h₁ : hd ∣ tl.foldl Nat.gcd 0 <;> by_cases h₂ : tl.foldl Nat.gcd 0 ∣ hd
      · obtain rfl := Nat.dvd_antisymm h₁ h₂
        grind
      · simp only [Nat.gcd_eq_left_iff_dvd, h₁, ↓reduceIte, Nat.gcd_eq_right_iff_dvd, h₂,
          Nat.add_zero, eq_comm (a := hd), Nat.right_eq_add]
        rw [Nat.gcd_eq_left h₁, List.count_eq_zero]
        exact fun h => h₂ (foldl_dvd_of_mem h)
      · simp only [Nat.gcd_eq_left_iff_dvd, h₁, ↓reduceIte, Nat.gcd_eq_right_iff_dvd, h₂,
          Nat.zero_add, eq_comm (a := hd), Nat.add_zero]
        rw [Nat.gcd_eq_right h₂]
      · simp only [Nat.gcd_eq_left_iff_dvd, h₁, ↓reduceIte, Nat.gcd_eq_right_iff_dvd, h₂,
          Nat.add_zero, eq_comm (a := hd)]
        rw [eq_comm (a := 0), List.count_eq_zero]
        exact fun h => h₂ (Nat.dvd_trans (foldl_dvd_of_mem h) (Nat.gcd_dvd_left ..))

theorem answerForSegment_eq {v : Vector Nat n} :
    answerForSegment v = n - v.count (v.foldl Nat.gcd 0) := by
  rw [answerForSegment]
  congr 1
  rw [Vector.count_eq_countP]
  apply Vector.countP_congr
  rcases v with ⟨⟨v⟩, hv⟩
  simp only [Vector.mem_mk, List.mem_toArray, Vector.all_mk, List.size_toArray, List.all_toArray',
    List.all_eq_true, decide_eq_true_eq, Vector.foldl_mk, List.foldl_toArray', beq_iff_eq]
  clear hv n
  refine fun y hy => ⟨?_, by rintro rfl; exact fun _ => foldl_dvd_of_mem⟩
  intro hx
  induction v with
  | nil => simp at hy
  | cons h t ih =>
    rw [List.mem_cons] at hy
    rw [List.foldl_cons, Nat.gcd_comm, List.foldl_assoc]
    obtain (rfl|hy) := hy
    · rw [Nat.gcd_eq_left]
      clear ih
      induction t with
      | nil => simp
      | cons h' t' ih =>
        rw [List.foldl_cons, Nat.gcd_comm, List.foldl_assoc]
        apply Nat.dvd_gcd
        · apply hx _ (by simp)
        · grind
    · rw [← ih hy (fun x hx' => hx _ (by simp [hx'])), Nat.gcd_eq_right]
      exact hx _ (by simp)

theorem answerQuery_eq_answerForSegment {v : Vector Nat n} {segtree : SegmentTree Entry.combine Entry.neutral n}
    (hst : segtree.underlying = v.map Entry.singleton) {l r hlr hr} :
    solve.answerQuery segtree l r hlr hr = answerForSegment (v.extract l (r + 1)) := by
  simp only [solve.answerQuery, SegmentTree.query_eq_foldl, hst, ← Vector.map_extract,
    foldl_map_combine]
  grind [answerForSegment_eq]

theorem isCorrectAnswer_solve {inp : Input} : IsCorrectAnswer inp (solve inp) where
  eq_length_filter i hi := by simp [solve, answerQuery_eq_answerForSegment SegmentTree.underlying_ofVector]

end Verification

end Problemset.AntColony
