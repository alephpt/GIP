import Gip.ProjectionFunctors
import Mathlib.Algebra.Category.Ring.Basic

/-!
# Verification of F_Ring functor
-/

namespace GIP.Verify

open CategoryTheory GIP

#check F_Ring
#check F_Ring.obj Obj.empty
#check F_Ring.obj Obj.unit
#check F_Ring.obj Obj.n
#check F_Ring.map

-- Verify the functor structure
#check (F_Ring : Gen ⥤ RingCat)

-- Check that objects map to correct rings
#reduce F_Ring.obj Obj.empty  -- Should be RingCat.of PUnit
#reduce F_Ring.obj Obj.unit   -- Should be RingCat.of ℤ
#reduce F_Ring.obj Obj.n      -- Should be RingCat.of (ℤ ⧸ ⊥)

-- Check identity preservation
example : F_Ring.map (𝟙 Obj.unit) = 𝟙 (F_Ring.obj Obj.unit) := rfl
example : F_Ring.map (𝟙 Obj.empty) = 𝟙 (F_Ring.obj Obj.empty) := rfl
example : F_Ring.map (𝟙 Obj.n) = 𝟙 (F_Ring.obj Obj.n) := rfl

end GIP.Verify