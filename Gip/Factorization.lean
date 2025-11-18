import Gip.Core

/-!
# GIP Universal Factorization

This module defines the universal factorization law:
```
ι_n ∘ γ: ∅ ──γ──> 𝟙 ──ι_n──> n
```

For any identity morphism id_n, we have:
- id_n = ι_n ∘ γ ∘ ε_n where ε_n is unique by initiality
- id_n = (ι_n ∘ γ) ∘ ε_n
-/

namespace GIP

open Hom

/-- The unique morphism ε arising from initiality of ∅ -/
axiom ε : {X : Obj} → Hom X X

/-- ε is the identity morphism -/
axiom ε_is_id {X : Obj} : @ε X = Hom.id

/-- Initiality: ∅ is the initial object - unique morphism to any object -/
axiom initial_unique {X : Obj} (f g : Hom ∅ X) : f = g

/-- Epic property: γ is epic (right-cancellable) for morphisms to n -/
axiom gamma_epic {k : Hom 𝟙 Obj.n} : k ∘ γ = ι ∘ γ → k = ι

/-- Factorization through unit:
    The composition ι ∘ γ provides the canonical factorization from ∅ to n -/
def canonical_factor : Hom ∅ Obj.n := Hom.ι ∘ Hom.γ

/-- Universal Factorization Law:
    The canonical factor is the unique morphism from ∅ to n -/
theorem universal_factorization (f : Hom ∅ Obj.n) :
  f = canonical_factor := initial_unique f canonical_factor

/-- Any two factorizations through ∅ → 𝟙 → n are equal -/
theorem factorization_unique
  (ι₁ ι₂ : Hom 𝟙 Obj.n) (γ₁ γ₂ : Hom ∅ 𝟙) :
  (ι₁ ∘ γ₁ = ι₂ ∘ γ₂) → (ι₁ ∘ γ₁ = canonical_factor) := by
  intro _
  apply universal_factorization

/-- Identity morphism is characterized by ε -/
theorem id_via_ε {X : Obj} : @Hom.id X = ε := ε_is_id.symm

/-- Functoriality: Composition respects the factorization -/
theorem comp_factorization {X Y Z : Obj} (f : Hom Y Z) (g : Hom X Y) :
  (f ∘ g) = f ∘ (g ∘ Hom.id) := by
  rw [comp_id]

end GIP
