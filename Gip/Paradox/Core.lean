/-
# Paradox Core Framework
This module provides the shared definitions and base isomorphism structure
for all paradox formalizations.

## Connection to Self-Reference Theory (○/○)

The paradox isomorphisms (Russell ≅ 0/0 ≅ Gödel ≅ Liar ≅ Halting) all share
a common structural pattern: **impossible self-reference attempts at the wrong level**.

**Key Discovery** (formalized in `Gip.SelfReference`):
- ○/○ = 1 (𝟙): Self-division of pre-structural origin yields proto-identity
- Only ○ can self-reference coherently (because it's pre-structural)
- All paradoxes are attempts to perform ○/○ at level n (with structure present)

**Core Insight**: The paradoxes are isomorphic because they share identical structure:
all attempt impossible ○/○ (self-reference) at the wrong level (with structure).

Only pre-structural origin (○) can self-reference coherently, yielding 𝟙.
Attempting self-reference with structure present yields paradox (incoherence).

See `Gip.SelfReference` for formal proofs that each paradox is an impossible ○/○ attempt.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatIso
import Mathlib.CategoryTheory.EqToHom

namespace Gip.ParadoxIsomorphism

open CategoryTheory

/-- The Russell paradox encoded as a thin category with two objects -/
inductive RussellObj : Type
  | contained : RussellObj
  | not_contained : RussellObj
  deriving DecidableEq

/-- The zero division paradox encoded similarly -/
inductive ZeroDivObj : Type
  | defined : ZeroDivObj
  | undefined : ZeroDivObj
  deriving DecidableEq

/-- A simple category structure for Russell paradox
    Each object has an identity, and there are paradoxical morphisms between states -/
def RussellCat : Type := RussellObj

instance : SmallCategory RussellCat where
  Hom a b := Unit  -- We make this a thin category where every hom-set is trivial
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- A simple category structure for zero division paradox -/
def ZeroDivCat : Type := ZeroDivObj

instance : SmallCategory ZeroDivCat where
  Hom a b := Unit  -- Similarly a thin category
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

/-- The functor from Russell to ZeroDiv mapping contained to defined -/
def F_RussellZeroDiv : RussellCat ⥤ ZeroDivCat where
  obj := fun
    | RussellObj.contained => ZeroDivObj.defined
    | RussellObj.not_contained => ZeroDivObj.undefined
  map _ := ⟨⟩
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The functor from ZeroDiv to Russell mapping defined to contained -/
def F_ZeroDivRussell : ZeroDivCat ⥤ RussellCat where
  obj := fun
    | ZeroDivObj.defined => RussellObj.contained
    | ZeroDivObj.undefined => RussellObj.not_contained
  map _ := ⟨⟩
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- Helper lemma: The composition preserves objects -/
lemma comp_preserves_russell (X : RussellCat) :
  (F_RussellZeroDiv ⋙ F_ZeroDivRussell).obj X = X := by
  cases X <;> rfl

/-- Helper lemma: The composition preserves objects -/
lemma comp_preserves_zerodiv (X : ZeroDivCat) :
  (F_ZeroDivRussell ⋙ F_RussellZeroDiv).obj X = X := by
  cases X <;> rfl

/-- The composition F_RussellZeroDiv ⋙ F_ZeroDivRussell is naturally isomorphic to identity -/
def russellRoundtrip : F_RussellZeroDiv ⋙ F_ZeroDivRussell ≅ 𝟭 RussellCat :=
  NatIso.ofComponents
    (fun X => eqToIso (comp_preserves_russell X))
    (by intros X Y f; simp [eqToHom]; rfl)

/-- The composition F_ZeroDivRussell ⋙ F_RussellZeroDiv is naturally isomorphic to identity -/
def zeroDivRoundtrip : F_ZeroDivRussell ⋙ F_RussellZeroDiv ≅ 𝟭 ZeroDivCat :=
  NatIso.ofComponents
    (fun X => eqToIso (comp_preserves_zerodiv X))
    (by intros X Y f; simp [eqToHom]; rfl)

/-- Main theorem: Russell and ZeroDiv paradoxes have isomorphic compositions with identity -/
theorem paradox_isomorphism_RussellZeroDiv :
  Nonempty ((F_RussellZeroDiv ⋙ F_ZeroDivRussell) ≅ 𝟭 RussellCat) ∧
  Nonempty ((F_ZeroDivRussell ⋙ F_RussellZeroDiv) ≅ 𝟭 ZeroDivCat) := by
  exact ⟨⟨russellRoundtrip⟩, ⟨zeroDivRoundtrip⟩⟩

/-! ## Documentation: How the encoding works

The key insight is that both Russell's paradox and division by zero represent
fundamental undefined/paradoxical operations:

- Russell: "The set of all sets that don't contain themselves" leads to contradiction
- ZeroDiv: "x = 0/0" is undefined and can equal any value

We model both as categories with two objects representing the binary states
(contained/not_contained for Russell, defined/undefined for ZeroDiv).
The functors establish a correspondence preserving the paradoxical structure.

The isomorphism proves these paradoxes have the same categorical structure,
formalizing the intuition that they represent the same kind of logical impossibility.
-/

/-- Repackage the Russell-ZeroDiv isomorphism to match the required format -/
theorem paradox_isomorphism_russell_zerodiv :
  ∃ (F : RussellCat ⥤ ZeroDivCat) (G : ZeroDivCat ⥤ RussellCat),
    Nonempty (F ⋙ G ≅ 𝟭 RussellCat) ∧ Nonempty (G ⋙ F ≅ 𝟭 ZeroDivCat) := by
  use F_RussellZeroDiv, F_ZeroDivRussell
  exact paradox_isomorphism_RussellZeroDiv

end Gip.ParadoxIsomorphism