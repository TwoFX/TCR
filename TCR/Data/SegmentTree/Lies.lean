module

/-!
Welcome to `Lies.lean`, where we use Lean's syntax extensibility to make
Lean look nice for the video. There are two hacks:

* We override the `if` syntax so that `if P then Q else R` expands to
  `if _ : P then Q else R`, which introduces the hypothesis `P` or `¬P`
  into the context for automation we use. Actually, we define a new
  syntax `𝚒f` which is completely separate from the usual `if`. Yes,
  you saw that right, that is `i` as in `U+1D692 Mathematical Monospace Small I`.
* We define ` ` as in `U+2009 Thin Space` to mean `by grind`, so that
  automation calls become invisible.
-/

macro " ": term => `(term|by grind)

syntax
  ppRealGroup(ppRealFill(ppIndent("𝚒f " term " then") ppSpace term)
    ppDedent(ppSpace) ppRealFill("else " term)) : term

macro_rules
  | `(𝚒f $c then $t else $e) => `(if _ : $c then $t else $e)

macro_rules
  | `(tactic| get_elem_tactic_extensible) => `(tactic| grind)
