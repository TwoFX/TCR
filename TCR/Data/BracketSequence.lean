/-
Copyright (c) 2025 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

/-!
# Bracket sequences
-/

namespace TCR

/-- `IsBracketPrefix IsPair s l` states that `l` is the prefix of a valid bracket sequence according
to the "bracket relation" `IsPair`, with `s` being the stack of remaining closing brackets.

Therefore, `IsBracketPrefix IsPair [] : List α → Prop` is the predicate of balanced backet sequences.

Example:
```lean
example : IsBracketPrefix (fun x y => (x, y) ∈ [('(', ')'), ('{', '}')]) [')', '}'] ['{', '(', ')', '('] :=
  .open (by simp) (.close (.open (by simp) (.open (by simp) .empty)))
```
-/
inductive IsBracketPrefix {α : Type u} (IsPair : α → α → Prop) : List α → List α → Prop where
  /-- The empty sequence is a valid bracket prefix with empty stack. -/
  | empty : IsBracketPrefix IsPair [] []
  /-- Opening a bracket puts the corresponding closing bracket on the stack. -/
  | open : IsPair b e → IsBracketPrefix IsPair s l → IsBracketPrefix IsPair (e :: s) (l ++ [b])
  /-- Closing a bracket consumes it from the stack. -/
  | close : IsBracketPrefix IsPair (e :: s) l → IsBracketPrefix IsPair s (l ++ [e])

-- Sync with docstring above
example : IsBracketPrefix (fun x y => (x, y) ∈ [('(', ')'), ('{', '}')]) [')', '}'] ['{', '(', ')', '('] :=
  .open (by simp) (.close (.open (by simp) (.open (by simp) .empty)))

inductive IsBracketSuffix {α : Type u} (IsPair : α → α → Prop) : List α → List α → Prop where
  | empty : IsBracketSuffix IsPair [] []
  | open : IsPair b e → IsBracketSuffix IsPair s l → IsBracketSuffix IsPair (b :: s) (e :: l)
  | close : IsBracketSuffix IsPair (b :: s) l → IsBracketSuffix IsPair s (b :: l)

end TCR
