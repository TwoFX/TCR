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
