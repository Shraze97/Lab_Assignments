import Mathlib
import PnP2023.Lec_02_03.InductiveTypes

/-!
Vectors, i.e., lists of a fixed length, can be defined in (at least) two ways. One way is as an indexed inductive type `Vec`, as we saw in lecture and is in the file `InductiveTypes.lean`. 

A different definition is as a subtype `Vector` of lists consisting of those of a fixed length. This is the definition used in `mathlib` and is recalled below.

```lean
/-- `Vector α n` is the type of lists of length `n` with elements of type `α`. -/
def Vector (α : Type u) (n : ℕ) :=
  { l : List α // l.length = n }
```

In this lab, you will relate the two definitions by constructing functions that convert between the two definitions and prove that these functions are inverses of each other.
-/
universe u

/-- Convert a `Vector` to a `Vec` -/
def Vec.ofVector {α : Type u}: (n : ℕ) →  Vector α n → Vec α n 
| n, v => 
  match v with 
  | ⟨l, h⟩ => 
    match l with 
    | [] =>  
      match h with 
      | rfl => Vec.nil
    | x :: xs => 
      have h' : xs.length = n-1 := by 
        rw[←h]
        rw[List.length_cons]
        simp
      match h with 
      | rfl => Vec.cons x (Vec.ofVector ((x :: xs).length -1) ⟨xs, h'⟩) 


/-- Convert a `Vec` to a `Vector` -/
def Vec.toVector {α : Type u}: (n : ℕ) →  Vec α n → Vector α n
| n, v => 
  match v with 
  | Vec.nil => 
    ⟨[], rfl⟩
  | Vec.cons x xs =>
    match Vec.toVector _ xs with 
    | ⟨l, h⟩ => 
      ⟨x :: l, by 
        rw[List.length_cons]
        rw[h]
        ⟩
    


/-- Mapping a `Vec` to a `Vector` and back gives the original `Vec` -/
theorem Vec.ofVector.toVector {α : Type u} (n : ℕ) (v : Vec α n) :
  Vec.ofVector n (Vec.toVector n v) = v := by 
  match v with
  | Vec.nil => 
    rw[Vec.toVector]
    simp
    have h : List.length [] = 0 := by 
      simp
    rw[Vec.ofVector]  
    
    
/-- Mapping a `Vector` to a `Vec` and back gives the original `Vector` -/
theorem Vec.toVector.ofVector {α : Type u} (n : ℕ) (v : Vector α n) :
  Vec.toVector n (Vec.ofVector n v) = v := sorry