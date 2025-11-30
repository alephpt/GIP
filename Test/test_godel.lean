/-
Test file for Gödel's Incompleteness Theorem formalization.
This verifies that our categorical isomorphisms compile and work correctly.
-/

import Gip.ParadoxIsomorphism

open Gip.ParadoxIsomorphism
open CategoryTheory

-- Test that Gödel category is properly defined
#check GödelCat
#check GödelObj.provable
#check GödelObj.unprovable

-- Test functors
#check F_GödelToRussell
#check F_RussellToGödel
#check F_GödelToZeroDiv
#check F_ZeroDivToGödel

-- Test isomorphisms
#check gödel_russell_isomorphism
#check gödel_zerodiv_isomorphism

-- Verify the functors compose correctly
example : (F_GödelToRussell ⋙ F_RussellToGödel).obj GödelObj.provable = GödelObj.provable := rfl
example : (F_GödelToRussell ⋙ F_RussellToGödel).obj GödelObj.unprovable = GödelObj.unprovable := rfl

example : (F_GödelToZeroDiv ⋙ F_ZeroDivToGödel).obj GödelObj.provable = GödelObj.provable := rfl
example : (F_GödelToZeroDiv ⋙ F_ZeroDivToGödel).obj GödelObj.unprovable = GödelObj.unprovable := rfl

-- Verify the mapping logic
example : F_GödelToRussell.obj GödelObj.provable = RussellObj.not_contained := rfl
example : F_GödelToRussell.obj GödelObj.unprovable = RussellObj.contained := rfl

example : F_GödelToZeroDiv.obj GödelObj.provable = ZeroDivObj.defined := rfl
example : F_GödelToZeroDiv.obj GödelObj.unprovable = ZeroDivObj.undefined := rfl

-- Test that the isomorphism theorems actually provide isomorphisms
example : ∃ (F : GödelCat ⥤ RussellCat) (G : RussellCat ⥤ GödelCat),
    Nonempty (F ⋙ G ≅ 𝟭 GödelCat) ∧ Nonempty (G ⋙ F ≅ 𝟭 RussellCat) := by
  exact gödel_russell_isomorphism

example : ∃ (F : GödelCat ⥤ ZeroDivCat) (G : ZeroDivCat ⥤ GödelCat),
    Nonempty (F ⋙ G ≅ 𝟭 GödelCat) ∧ Nonempty (G ⋙ F ≅ 𝟭 ZeroDivCat) := by
  exact gödel_zerodiv_isomorphism

#print "All Gödel formalization tests passed!"