import PnP2023.Labs.Lab02.SelectionSort

/-!
# Selection Sort (continued)

In this lab you will show that `selectionSort` defined in the previous lab is correct, i.e. the result is sorted and preserves membership.

__Note:__ If the list has duplicates the sorted list will erase these. For example, `[1, 1, 2, 3]` will be sorted to `[1, 2, 3]`. For the purposes of this exercise, this is fine.


We first define recursively when a list is sorted. -/

/-- A direct definition of an element being below all members of a list. -/
def List.le_all (a : ℕ) (l : List ℕ) : Prop := ∀ b: ℕ, b ∈ l → a ≤ b

/-- Whether a given list is sorted. -/
def List.sorted: List ℕ →  Prop 
| [] => True 
| h :: t => (t.le_all h) ∧ (t.sorted)

-- For your convenience, here are some definitions/theorems that may be useful in the two labs. Clicking on them takes you to the source, where you may find other useful results.
#check List.remove -- {α : Type u_1} → [inst : DecidableEq α] → α → List α → List α
#check List.length_cons -- ∀ {α : Type u_1} (a : α) (as : List α), List.length (a :: as) = Nat.succ (List.length as)
#check List.mem_cons -- ∀ {α : Type u_1} {a b : α} {l : List α}, a ∈ b :: l ↔ a = b ∨ a ∈ l
#check List.mem_of_mem_remove -- ∀ {α : Type u_1} [inst : DecidableEq α] {a b : α} {as : List α}, b ∈ List.remove a as → b ∈ as
#check List.remove_eq_of_not_mem -- ∀ {α : Type u_1} [inst : DecidableEq α] {a : α} {as : List α}, ¬a ∈ as → List.remove a as = as
#check List.mem_remove_iff -- ∀ {α : Type u_1} [inst : DecidableEq α] {a b : α} {as : List α}, b ∈ List.remove a as ↔ b ∈ as ∧ b ≠ a

/-!
- Problem 1: show that members of the given list are members of the sorted list(remove sorry). 
-/

/-- Members of a list are members of the given sorted list -/
theorem selectionSort_mem_of_mem {a : ℕ} {l : List ℕ} (hyp : a ∈ l) : a ∈ selectionSort l := by 
  rw[selectionSort]
  have c : ¬ l = []  := by 
    by_contra h1
    rw[h1,List.mem_nil_iff ] at hyp
    assumption
  simp[c] 
  by_cases a = smallest l c 
  · left 
    assumption
  · right
    have lem : a ∈ List.remove (smallest l c) l := by 
      simp[List.mem_remove_iff]
      apply And.intro 
      · assumption
      · assumption
    apply selectionSort_mem_of_mem lem
termination_by _ _ => l.length
decreasing_by  apply remove_mem_length                 
               have lem : smallest l c ∈ l := by 
                   simp[c, smallest_in_list l c]
               apply lem  

/-!
- Problem 2: show that members of the sorted list are members of the given list(remove sorry). 
-/

/-- Members of the sorted list are members of the given list -/
theorem selectionSort_mem_mem {a : ℕ} {l : List ℕ} (hyp : a ∈ selectionSort l) : a ∈ l := by 
  rw[selectionSort] at hyp
  have c : ¬ l = []  := by  
    by_contra h1
    simp[h1] at hyp 
  simp[c] at hyp 
  by_cases h1 : a = smallest l c
  · simp[h1]
    apply smallest_in_list 
  · simp[h1] at hyp 
    have lemm : a ∈ List.remove (smallest l c) l := by 
      apply selectionSort_mem_mem hyp
    apply List.mem_of_mem_remove lemm
termination_by _ _ => l.length
decreasing_by  apply remove_mem_length   
               apply smallest_in_list l c 

theorem selectionSort_mem (l : List ℕ) (a : ℕ) : a ∈ l ↔ a ∈ selectionSort l := by 
  apply Iff.intro
  · apply selectionSort_mem_of_mem
  · apply selectionSort_mem_mem

/-!
- Problems 3: Prove that the results of `selectionSort` is sorted (remove the sorry).
-/


/-- The result of `selectionSort` is sorted -/
theorem selectionSort_sorted (l : List ℕ) : (selectionSort l).sorted := by 
  rw[selectionSort]
  by_cases c : l = []
  · simp[c]
    simp[List.sorted]
  · simp[c]
    simp[List.sorted] 
    apply And.intro
    · simp[List.le_all]
      intro a h1 
      have h2 : a ∈ List.remove (smallest l c) l := by 
        apply selectionSort_mem_mem h1       
      have h3 : a ∈ l := by
        apply List.mem_of_mem_remove h2
      apply smallest_le
      assumption
    · apply selectionSort_sorted
termination_by _ _ => l.length
decreasing_by  apply remove_mem_length   
               apply smallest_in_list l c

      