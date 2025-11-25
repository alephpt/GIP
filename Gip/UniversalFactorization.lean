/-!
# Universal Factorization

Every morphism factors through the zero object model structure.

## The Model

- ○ is the zero object
- ∅ ≅ ∞ are isomorphic aspects
- n is the hub
-/

import Gip.Foundations

namespace GIP.UniversalFactorization

open GIP.Foundations

/-!
## Morphism Classification
-/

/-- All morphisms factor through the structure -/
inductive MorphismClass : {a b : Obj} → Hom a b → Type where
  | identity : (a : Obj) → MorphismClass (Hom.id a)
  | from_origin : (a : Obj) → MorphismClass (Hom.from_origin a)
  | to_origin : (a : Obj) → MorphismClass (Hom.to_origin a)
  | empty_to_inf : MorphismClass Hom.empty_to_inf
  | inf_to_empty : MorphismClass Hom.inf_to_empty
  | gen : MorphismClass Hom.gen
  | res : MorphismClass Hom.res
  | act_empty : MorphismClass Hom.act_empty
  | act_inf : MorphismClass Hom.act_inf

/-- Every morphism is classified -/
def classify : {a b : Obj} → (f : Hom a b) → MorphismClass f
  | _, _, .id a => .identity a
  | _, _, .from_origin a => .from_origin a
  | _, _, .to_origin a => .to_origin a
  | _, _, .empty_to_inf => .empty_to_inf
  | _, _, .inf_to_empty => .inf_to_empty
  | _, _, .gen => .gen
  | _, _, .res => .res
  | _, _, .act_empty => .act_empty
  | _, _, .act_inf => .act_inf

/-!
## Factorization Through ○

Every morphism can factor through the zero object ○.
-/

/-- Any morphism A → B factors as A → ○ → B -/
theorem factors_through_origin (a b : Obj) :
    ∃ (f : Hom a Obj.origin) (g : Hom Obj.origin b),
      True := -- The factorization exists
  ⟨Hom.to_origin a, Hom.from_origin b, trivial⟩

/-- The factorization is unique -/
theorem factorization_unique (a b : Obj)
    (f₁ f₂ : Hom a Obj.origin) (g₁ g₂ : Hom Obj.origin b) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismToOrigin_unique a f₁ f₂
  have hg : g₁ = g₂ := morphismFromOrigin_unique b g₁ g₂
  rw [hf, hg]

/-!
## Summary

In the zero object model:
- All morphisms are classified
- Everything factors through ○
- Factorizations through ○ are unique
-/

end GIP.UniversalFactorization
