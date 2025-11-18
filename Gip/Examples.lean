import Gip.Core
import Gip.Factorization

/-!
# GIP Examples

Demonstrations of the GIP system in action.
-/

namespace GIP.Examples

open GIP Hom Obj

/-- Example: Basic morphism γ: ∅ → 𝟙 -/
example : Hom ∅ 𝟙 := γ

/-- Example: Morphism ι: 𝟙 → n -/
example : Hom 𝟙 n := ι

/-- Example: Canonical factorization ∅ → 𝟙 → n -/
example : Hom ∅ n := ι ∘ γ

/-- Example: Identity morphism on n -/
example : Hom n n := Hom.id

/-- Example: Canonical factor is ι ∘ γ -/
example : canonical_factor = ι ∘ γ := rfl

/-- Example: ε is identity -/
example : @ε n = Hom.id := ε_is_id

/-- Example: Universal factorization - all morphisms ∅ → n are equal -/
example (f : Hom ∅ n) : f = canonical_factor := universal_factorization f

/-- Example: Composition associativity -/
example (f : Hom 𝟙 n) (g : Hom ∅ 𝟙) :
  (f ∘ g) ∘ Hom.id = f ∘ (g ∘ Hom.id) := comp_assoc f g Hom.id

/-- Example: Identity laws -/
example (f : Hom ∅ 𝟙) : Hom.id ∘ f = f := id_comp f
example (f : Hom ∅ 𝟙) : f ∘ Hom.id = f := comp_id f

end GIP.Examples
