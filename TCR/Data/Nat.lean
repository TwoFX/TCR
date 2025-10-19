/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

namespace Nat

public theorem two_mul_add_eq_or_of_lt {b : Nat} (hb : b < 2) (a : Nat) : 2 * a + b = 2 * a ||| b := by
  simpa using Nat.two_pow_add_eq_or_of_lt (i := 1) (by simpa using hb) a

@[simp]
public theorem testBit_two_mul : (2 * a).testBit j = (decide (j ≥ 1) && a.testBit (j - 1)) := by
  simpa using Nat.testBit_two_pow_mul (i := 1)

@[simp]
public theorem testBit_mul_two : (a * 2).testBit j = (decide (j ≥ 1) && a.testBit (j - 1)) := by
  simpa using Nat.testBit_mul_two_pow (i := 1) ..

public theorem xor_one_eq {n : Nat} : n ^^^ 1 = if n % 2 = 0 then n + 1 else n - 1 := by
  split <;> rename_i h
  · rw [← Nat.div_add_mod n 2, h, Nat.add_zero, Nat.two_mul_add_eq_or_of_lt (by omega)]
    apply Nat.eq_of_testBit_eq
    simp; grind
  · rw [← Nat.div_add_mod n 2, Nat.mod_two_not_eq_zero.1 h, Nat.add_one_sub_one]
    apply Nat.eq_of_testBit_eq
    simp; grind

public theorem xor_one_le {n : Nat} : n ^^^ 1 ≤ n + 1 := by
  grind [Nat.xor_one_eq]

end Nat
