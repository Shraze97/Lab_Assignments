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

def supp_ofVector {α : Type u} : (n : ℕ) → (l : List α ) → (h : l.length = n ) →  Vec α n 
| 0 , [], h =>
  Vec.nil
| n + 1, x :: xs, h =>
  have h' : xs.length = (x :: xs).length-1 := by 
      rw[List.length_cons]
      simp
  have h' : xs.length = n := by 
      rw[List.length_cons] at h 
      simp at h
      assumption
  Vec.cons x (supp_ofVector _ xs h')
  

/-- Convert a `Vector` to a `Vec` -/
def Vec.ofVector {α : Type u}: (n : ℕ) →  Vector α n → Vec α n 
| n, v => 
  supp_ofVector n v.val v.property

def supp_toVector {α : Type u} {n : ℕ} : Vec α n → Vector α n
| Vec.nil => ⟨[], rfl⟩
| Vec.cons head tail =>
  ⟨ head :: (supp_toVector tail).val, 
    by 
      rw[List.length_cons]
      rw[(supp_toVector tail).2] ⟩


/-- Convert a `Vec` to a `Vector` -/
def Vec.toVector {α : Type u}: (n : ℕ) →  Vec α n → Vector α n
| _, v => 
  supp_toVector v
    
#check Vector.nil  

/-- Mapping a `Vec` to a `Vector` and back gives the original `Vec` -/
theorem Vec.ofVector.toVector {α : Type u} (n : ℕ) (v : Vec α n) :
  Vec.ofVector n (Vec.toVector n v) = v := by 
  match v with
  | Vec.nil => 
    rw[Vec.toVector]
    simp
    rw[supp_toVector]    
    rw[Vec.ofVector]
    simp
    rw[supp_ofVector]
  | Vec.cons x xs => 
    have lem : Vec.ofVector _ (Vec.toVector _ xs) = xs := by 
      apply Vec.ofVector.toVector
    rw[Vec.toVector]
    simp
    rw[supp_toVector]
    rw[Vec.ofVector]
    simp 
    rw[supp_ofVector]
    simp
    rw[Vec.ofVector] at lem
    simp at lem 
    assumption


    
/-- Mapping a `Vector` to a `Vec` and back gives the original `Vector` -/
theorem Vec.toVector.ofVector {α : Type u} (n : ℕ) (v : Vector α n) :
  Vec.toVector n (Vec.ofVector n v) = v := by
  match v with
  | ⟨l,h⟩ => 
    match l with 
    | [] => 
      rw[Vec.ofVector]
      simp
      simp at h 
      subst h 
      rw[supp_ofVector]
      rw[Vec.toVector]
      simp 
    | head :: tail => 
      have h' : tail.length = (head :: tail).length-1 := by 
        rw[List.length_cons]
        simp
      rw[h] at h'
      have lem : Vec.toVector _ (Vec.ofVector _ ⟨tail, h'⟩) = ⟨tail, h'⟩ := by 
        apply Vec.toVector.ofVector
      rw[Vec.ofVector]
      set b := tail.length with b_def
      have h'' : n = b + 1 := by 
        rw[b_def]
        rw[List.length_cons] at h
        simp at h
        rw[← h]
      simp at *
      subst h'' 
      rw[supp_ofVector]
      simp
      rw[Vec.toVector]
      simp
      rw[supp_toVector]
      rw[Vec.ofVector] at lem
      simp at lem
      rw[Vec.toVector] at lem
      simp at lem
      
      


     
