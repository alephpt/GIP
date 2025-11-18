import Gip.ParadoxIsomorphism

open Gip.ParadoxIsomorphism
open CategoryTheory

#check RussellObj
#check ZeroDivObj
#check F_RussellZeroDiv
#check F_ZeroDivRussell
#check russellRoundtrip
#check zeroDivRoundtrip
#check paradox_isomorphism_RussellZeroDiv

-- Verify that the isomorphism exists
example : Nonempty ((F_RussellZeroDiv ⋙ F_ZeroDivRussell) ≅ 𝟭 RussellCat) := by
  exact ⟨russellRoundtrip⟩

example : Nonempty ((F_ZeroDivRussell ⋙ F_RussellZeroDiv) ≅ 𝟭 ZeroDivCat) := by
  exact ⟨zeroDivRoundtrip⟩

-- Check that the functors preserve the structure
example : F_RussellZeroDiv.obj RussellObj.contained = ZeroDivObj.defined := rfl
example : F_RussellZeroDiv.obj RussellObj.not_contained = ZeroDivObj.undefined := rfl
example : F_ZeroDivRussell.obj ZeroDivObj.defined = RussellObj.contained := rfl
example : F_ZeroDivRussell.obj ZeroDivObj.undefined = RussellObj.not_contained := rfl

-- Verify the round-trip property
example (X : RussellObj) : (F_RussellZeroDiv ⋙ F_ZeroDivRussell).obj X = X := by
  cases X <;> rfl

example (X : ZeroDivObj) : (F_ZeroDivRussell ⋙ F_RussellZeroDiv).obj X = X := by
  cases X <;> rfl

#eval "Paradox isomorphism formalized successfully!"