import Mathlib

/-!
# Inductive Types

The main way of introducing new types in Lean is through inductive types. An inductive type is a type
which is specified by saying how to construct terms of that type. Concretely, we specify the types of 
a set of `constructors` all of which have _final codomain_ the type being constructed.

When an inductive type is defined, Lean automatically generates a _recursor_ for that type, which allows defining by cases, matching, and induction on terms of that type.
-/

namespace Waffle

/-!
Enumerated types are a special case of inductive types where the constructors have no arguments. We simply list the terms of that type.
-/

/-- 
An enumerated type for the answers to a yes/no question. 
-/
inductive Answer where
  | yes : Answer
  | no : Answer
  | maybe : Answer
deriving Repr, Inhabited

#check Answer -- Type
#check Answer.yes -- Answer
#eval Answer.yes -- Waffle.Answer.yes

#eval (default : Answer)

/-- A function defined by cases which disagrees with the given answer. -/
def disagree: Answer → Answer
  | Answer.yes => Answer.no
  | Answer.no => Answer.yes
  | Answer.maybe => Answer.maybe

#eval disagree Answer.yes -- Waffle.Answer.no

theorem disagree_eq_maybe(ans: Answer) : 
  (disagree ans) = ans → ans = Answer.maybe :=
    by
      cases ans <;> simp [disagree] 

/-!
The definition is rewritten by Lean in terms of the `rec` function, which is automatically generated by Lean for each inductive type. The `rec` function is a _recursor_ for the type, which allows defining by cases, matching, and induction on terms of that type.

```lean
#reduce disagree -- fun x => Answer.rec Answer.no Answer.yes Answer.maybe x
#check @Answer.rec -- {motive : Answer → Sort u_1} → motive Answer.yes → motive Answer.no → motive Answer.maybe → (t : Answer) → motive t

```

-/
#reduce disagree -- fun x => Answer.rec Answer.no Answer.yes Answer.maybe x
#check @Answer.rec -- {motive : Answer → Sort u_1} → motive Answer.yes → motive Answer.no → motive Answer.maybe → (t : Answer) → motive t

end Waffle

namespace Explained

/-!
Another simple kind of inductive type is a `Structure`, whose terms correspond to values of specified fields of given types.
-/

/-- A structure for answers with explanations -/
structure Answer where
  agree : Bool
  explanation: String

/-!
An element of the type can be constructed using special syntax which is similar to a tuple but with left and right angle brackets instead of parentheses. 

```lean
example : Answer := ⟨true, "I agree"⟩
```
-/

example : Answer := ⟨true, "I agree"⟩

/-!
When a structure is defined, a constructor named `mk` is automatically generated. The constructor is a function which takes the arguments of the structure in the order they are declared and returns a term of the structure type. 

Further, projections onto each of the fields are defined as functions named after the field. As with any induction type, a recursor is automatically generated for the structure.

```lean
#check Answer -- Type
#check Answer.agree -- Answer → Bool 
#check Answer.explanation -- Answer → String
#check Answer.mk -- Bool → String → Answer
#check Answer.rec -- {motive : Answer → Sort u} → ((agree : Bool) → (explanation : String) → motive { agree := agree, explanation := explanation }) → (t : Answer) → motive t
```
-/
#check Answer -- Type
#check Answer.agree -- Answer → Bool 
#check Answer.explanation -- Answer → String
#check Answer.mk -- Bool → String → Answer
#check Answer.rec -- {motive : Answer → Sort u} → ((agree : Bool) → (explanation : String) → motive { agree := agree, explanation := explanation }) → (t : Answer) → motive t

end Explained