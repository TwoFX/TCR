/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

@[simp]
public theorem Vector.getD_mk {a : Array α} {n : Nat} (h : a.size = n) {m : Nat} {b : α} :
    (Vector.mk a h).getD m b = a.getD m b := rfl

@[simp]
public theorem Vector.getD_eq_getD_getElem? {v : Vector α n} {m : Nat} {a : α} :
    v.getD m a = v[m]?.getD a := by
  cases v; simp

public theorem Vector.getD_set_ne {v : Vector α n} {m k : Nat} {hm} {a b : α} (hmk : m ≠ k) :
    (v.set m a hm).getD k b = v.getD k b := by
  simp [Vector.getElem?_set_ne _ hmk]

/-- Applies the function `f` to the `i`-th element of `v`, provided `i < n`. Otherwise, returns
`v` unmodified. -/
public def Vector.modify (v : Vector α n) (i : Nat) (f : α → α) : Vector α n where
  toArray := v.toArray.modify i f
  size_toArray := by simp

@[simp]
public theorem Vector.toArray_modify {v : Vector α n} {i : Nat} {f : α → α} :
    (v.modify i f).toArray = v.toArray.modify i f := (rfl)

@[simp]
public theorem Vector.modify_mk {a : Array α} (hn : a.size = n) {i : Nat} {f : α → α} :
    (Vector.mk a hn).modify i f = Vector.mk (a.modify i f) (by simp [hn]) := (rfl)

@[simp]
public theorem Vector.modify_cast {h : n = m} {v : Vector α n} {i : Nat} {f : α → α} :
    (v.cast h).modify i f = (v.modify i f).cast h := (rfl)

public theorem Vector.getElem_modify {f : α → α} {v : Vector α n} {j i : Nat} {h} :
    (v.modify j f)[i]'h = if j = i then f v[i] else v[i] := by
  cases v
  simp [Array.getElem_modify]

public theorem Vector.getElem_modify_of_ne {j : Nat} {v : Vector α n} {i : Nat} (hi : i ≠ j) (f : α → α) (hj) : (v.modify i f)[j] = v[j] := by
  simp [getElem_modify, hi]
