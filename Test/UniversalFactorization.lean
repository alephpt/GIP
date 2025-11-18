import Gip.UniversalFactorization

/-!
# Tests for Universal Factorization

This file tests the universal factorization theorems.
-/

namespace Test.UniversalFactorization

open GIP GIP.Hom GIP.Obj GIP.UniversalFactorization

/-- Test that empty is initial -/
example (f g : Hom ∅ 𝟙) : f = g := empty_initial f g

/-- Test universal factorization -/
example (f : Hom ∅ n) : f = ι ∘ γ := universal_factorization 0 f

/-- Test that the factorization is unique -/
example (f : Hom ∅ n) :
  ∃ (path : Hom ∅ 𝟙 × Hom 𝟙 n),
    f = path.2 ∘ path.1 ∧ path = (γ, ι) := by
  have ⟨path, hf, _, heq⟩ := unique_factorization_via_modal_topology f
  exact ⟨path, hf, heq⟩

/-- Test complete factorization characterization -/
example (f : Hom ∅ n) (g : Hom ∅ 𝟙) (h : Hom 𝟙 n) :
  f = h ∘ g → (g = γ ∧ h = ι) := by
  intro hf
  have ⟨_, hfact⟩ := complete_factorization f
  exact hfact g h hf

/-- Test initiality equivalence -/
example : (∀ {Y : Obj} (f g : Hom ∅ Y), f = g) ↔ (∀ f : Hom ∅ n, f = ι ∘ γ) :=
  initiality_iff_factorization

end Test.UniversalFactorization