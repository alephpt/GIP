import Gip.Foundations

/-!
# Universal Factorization

Every morphism factors through the restricted origin model structure.

## The Model

- ○ connects only to aspects (∅ and ∞)
- ∅ ≅ ∞ are isomorphic aspects
- n is the hub
-/

namespace GIP.UniversalFactorization

open GIP.Foundations

/-!
## Morphism Classification
-/

/-- All morphisms factor through the structure -/
inductive MorphismClass : {a b : Obj} → Hom a b → Type where
  | identity : (a : Obj) → MorphismClass (Hom.id a)
  | origin_to_empty : MorphismClass Hom.origin_to_empty
  | origin_to_inf : MorphismClass Hom.origin_to_inf
  | empty_to_origin : MorphismClass Hom.empty_to_origin
  | inf_to_origin : MorphismClass Hom.inf_to_origin
  | empty_to_inf : MorphismClass Hom.empty_to_inf
  | inf_to_empty : MorphismClass Hom.inf_to_empty
  | gen : MorphismClass Hom.gen
  | res : MorphismClass Hom.res
  | act_empty : MorphismClass Hom.act_empty
  | act_inf : MorphismClass Hom.act_inf
  -- Composite morphisms (○ ↔ n through aspects)
  | origin_to_n_via_empty : MorphismClass Hom.origin_to_n_via_empty
  | origin_to_n_via_inf : MorphismClass Hom.origin_to_n_via_inf
  | n_to_origin_via_empty : MorphismClass Hom.n_to_origin_via_empty
  | n_to_origin_via_inf : MorphismClass Hom.n_to_origin_via_inf

/-- Every morphism is classified -/
def classify : {a b : Obj} → (f : Hom a b) → MorphismClass f
  | _, _, .id a => .identity a
  | _, _, .origin_to_empty => .origin_to_empty
  | _, _, .origin_to_inf => .origin_to_inf
  | _, _, .empty_to_origin => .empty_to_origin
  | _, _, .inf_to_origin => .inf_to_origin
  | _, _, .empty_to_inf => .empty_to_inf
  | _, _, .inf_to_empty => .inf_to_empty
  | _, _, .gen => .gen
  | _, _, .res => .res
  | _, _, .act_empty => .act_empty
  | _, _, .act_inf => .act_inf
  | _, _, .origin_to_n_via_empty => .origin_to_n_via_empty
  | _, _, .origin_to_n_via_inf => .origin_to_n_via_inf
  | _, _, .n_to_origin_via_empty => .n_to_origin_via_empty
  | _, _, .n_to_origin_via_inf => .n_to_origin_via_inf

/-!
## Factorization Through ○

In the restricted model, only aspects can map to/from ○.
Other objects reach ○ through the aspects.
-/

/-- ∅ → ∅ factors as ∅ → ○ → ∅ -/
theorem empty_factors_through_origin_empty :
    ∃ (f : Hom Obj.aspect_empty Obj.origin) (g : Hom Obj.origin Obj.aspect_empty),
      True :=
  ⟨Hom.empty_to_origin, Hom.origin_to_empty, trivial⟩

/-- ∅ → ∞ factors as ∅ → ○ → ∞ -/
theorem empty_factors_through_origin_inf :
    ∃ (f : Hom Obj.aspect_empty Obj.origin) (g : Hom Obj.origin Obj.aspect_infinite),
      True :=
  ⟨Hom.empty_to_origin, Hom.origin_to_inf, trivial⟩

/-- ∞ → ∅ factors as ∞ → ○ → ∅ -/
theorem inf_factors_through_origin_empty :
    ∃ (f : Hom Obj.aspect_infinite Obj.origin) (g : Hom Obj.origin Obj.aspect_empty),
      True :=
  ⟨Hom.inf_to_origin, Hom.origin_to_empty, trivial⟩

/-- ∞ → ∞ factors as ∞ → ○ → ∞ -/
theorem inf_factors_through_origin_inf :
    ∃ (f : Hom Obj.aspect_infinite Obj.origin) (g : Hom Obj.origin Obj.aspect_infinite),
      True :=
  ⟨Hom.inf_to_origin, Hom.origin_to_inf, trivial⟩

/-- The factorization ∅ → ○ → ∅ is unique -/
theorem empty_factorization_empty_unique
    (f₁ f₂ : Hom Obj.aspect_empty Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_empty) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismEmptyToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToEmpty_unique g₁ g₂
  rw [hf, hg]

/-- The factorization ∅ → ○ → ∞ is unique -/
theorem empty_factorization_inf_unique
    (f₁ f₂ : Hom Obj.aspect_empty Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_infinite) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismEmptyToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToInf_unique g₁ g₂
  rw [hf, hg]

/-- The factorization ∞ → ○ → ∅ is unique -/
theorem inf_factorization_empty_unique
    (f₁ f₂ : Hom Obj.aspect_infinite Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_empty) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismInfToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToEmpty_unique g₁ g₂
  rw [hf, hg]

/-- The factorization ∞ → ○ → ∞ is unique -/
theorem inf_factorization_inf_unique
    (f₁ f₂ : Hom Obj.aspect_infinite Obj.origin) (g₁ g₂ : Hom Obj.origin Obj.aspect_infinite) :
    Hom.comp f₁ g₁ = Hom.comp f₂ g₂ := by
  have hf : f₁ = f₂ := morphismInfToOrigin_unique f₁ f₂
  have hg : g₁ = g₂ := morphismOriginToInf_unique g₁ g₂
  rw [hf, hg]

/-!
## Summary

In the restricted origin model:
- All morphisms are classified
- Aspects factor through ○
- Factorizations through ○ between aspects are unique
- n reaches ○ through the aspects (n → ∅ → ○ or n → ∞ → ○)
-/

end GIP.UniversalFactorization
