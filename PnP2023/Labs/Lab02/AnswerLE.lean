import PnP2023.Lec_01_25.Answer

namespace Waffle

theorem Answer.eq_of_le_le (a b  : Answer) : 
  a ≤ b → b ≤ a → a = b := by 
  intros h1 h2 
  cases c1 : h1  
  case no_le => 
    cases c2 : h2 <;> rfl
  case le_yes => 
    cases c2 : h2 <;> rfl 
  case refl => 
    rfl 
