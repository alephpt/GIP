/-
Register 0: The Empty Object ∅ (Version 2)
Complete proofs using the computational morphism structure
Based on categorical/definitions/register0_empty_v2.md
-/

import Gen.MorphismsV2
import Gen.CategoryLawsV2

namespace Gen
namespace Register0

/-
SECTION 2: Initial Object Properties
Theorem 2.1: ∅ is the initial object
-/

theorem empty_is_initial :
  ∀ (X : GenObj), ∃! (f : GenMorphism ∅ X), True := by
  exact CategoryLaws.empty_initial

-- More detailed version with explicit uniqueness
theorem empty_initial_explicit (X : GenObj) :
  ∃ (f : GenMorphism ∅ X), ∀ (g : GenMorphism ∅ X), g = f := by
  cases X
  case empty =>
    use GenMorphism.id_empty
    exact Gen.id_empty_unique

  case unit =>
    use γ
    exact Gen.genesis_unique

  case nat n =>
    use GenMorphism.genesis_inst n
    exact Gen.morphism_from_empty_unique n

/-
SECTION 3: Endomorphism Structure
Proposition 3.1: End(∅) = {id_∅}
-/

theorem empty_endomorphism_trivial :
  ∀ (f : GenMorphism ∅ ∅), f = GenMorphism.id_empty := by
  exact Gen.id_empty_unique

-- Count of endomorphisms
theorem empty_endo_count :
  ∃! (f : GenMorphism ∅ ∅), True := by
  use GenMorphism.id_empty
  constructor
  · trivial
  · intro f _
    exact empty_endomorphism_trivial f

/-
SECTION 3.2: No incoming morphisms (except from itself)
-/

theorem no_morphisms_to_empty :
  ∀ (X : GenObj) (f : GenMorphism X ∅), X = ∅ := by
  intro X f
  cases X
  case empty => rfl
  case unit =>
    -- No morphism 𝟙 → ∅ exists
    cases f  -- No constructor matches
  case nat n =>
    -- No morphism n → ∅ exists
    cases f  -- No constructor matches

-- Alternative formulation
theorem morphism_to_empty_criterion (X : GenObj) :
  (∃ (f : GenMorphism X ∅), True) ↔ X = ∅ := by
  constructor
  · intro ⟨f, _⟩
    exact no_morphisms_to_empty X f
  · intro h
    subst h
    use GenMorphism.id_empty
    trivial

/-
SECTION 4: Composition Properties with Empty
-/

-- Composition with identity from empty
theorem comp_with_id_empty {X : GenObj} (f : GenMorphism ∅ X) :
  GenMorphism.comp GenMorphism.id_empty f = f := by
  exact Gen.right_identity f

-- Any composition ending at empty must start at empty
theorem comp_to_empty {X Y : GenObj}
    (f : GenMorphism X Y) (g : GenMorphism Y ∅) :
  X = ∅ := by
  have hy := no_morphisms_to_empty Y g
  subst hy
  exact no_morphisms_to_empty X f

/-
SECTION 5: Universal Property
The universal property of the initial object
-/

theorem initial_universal_property :
  ∀ (X : GenObj) (f g : GenMorphism ∅ X), f = g := by
  intro X f g
  cases X
  · exact empty_endomorphism_trivial f ▸ empty_endomorphism_trivial g
  · exact Gen.genesis_unique f ▸ Gen.genesis_unique g
  · exact Gen.morphism_from_empty_unique _ f ▸
          Gen.morphism_from_empty_unique _ g

-- Morphisms from empty commute with everything
theorem morphism_from_empty_commutes {X Y Z : GenObj}
    (f : GenMorphism ∅ X) (g : GenMorphism X Y) (h : GenMorphism ∅ Y)
    (k : GenMorphism Y Z) :
  k ∘ (g ∘ f) = k ∘ h := by
  have : g ∘ f = h := initial_universal_property Y (g ∘ f) h
  rw [this]

/-
SECTION 6: Factorization Properties
-/

-- Every morphism from empty to a natural factors through unit
theorem empty_to_nat_factors (n : Nat) :
  ∀ (f : GenMorphism ∅ (GenObj.nat n)),
    f = (ι n) ∘ γ := by
  intro f
  cases f
  case genesis_inst m =>
    -- The only way to get ∅ → nat is through genesis_inst
    -- which is definitionally equal to ι_m ∘ γ
    rfl

-- Unique factorization through unit
theorem unique_factorization_through_unit (n : Nat) :
  ∀ (f : GenMorphism ∅ (GenObj.nat n)),
    ∃! (g : GenMorphism ∅ 𝟙), ∃! (h : GenMorphism 𝟙 (GenObj.nat n)),
      f = h ∘ g := by
  intro f
  -- The unique factorization is γ and ι_n
  use γ
  constructor
  · use ι n
    constructor
    · constructor
      · exact empty_to_nat_factors n f
      · intro h' ⟨hcomp, _⟩
        -- h' must be ι_n by uniqueness
        have : h' ∘ γ = f := hcomp
        rw [← empty_to_nat_factors n f] at this
        -- Both h' ∘ γ and ι n ∘ γ equal f
        have eq1 : h' ∘ γ = GenMorphism.genesis_inst n := by
          rw [this]
          cases f
          case genesis_inst => rfl
        have eq2 : ι n ∘ γ = GenMorphism.genesis_inst n := by
          rfl
        -- Therefore h' = ι n
        cases h'
        case instantiation m =>
          congr
          -- From eq1: genesis_inst m = genesis_inst n
          injection eq1
  · intro g' ⟨h', ⟨⟨hcomp, _⟩, _⟩⟩
    -- g' must be γ by uniqueness
    exact Gen.genesis_unique g'

/-
SECTION 7: Relationships with Other Registers
-/

-- Empty is strictly before unit in the register hierarchy
theorem empty_before_unit :
  (∃ (f : GenMorphism ∅ 𝟙), True) ∧
  ¬(∃ (g : GenMorphism 𝟙 ∅), True) := by
  constructor
  · use γ
    trivial
  · exact Gen.no_morphism_to_empty_from_unit

-- Empty is strictly before all naturals
theorem empty_before_nat (n : Nat) :
  (∃ (f : GenMorphism ∅ (GenObj.nat n)), True) ∧
  ¬(∃ (g : GenMorphism (GenObj.nat n) ∅), True) := by
  constructor
  · use GenMorphism.genesis_inst n
    trivial
  · exact Gen.no_morphism_to_empty_from_nat n

/-
SECTION 8: Summary Properties
-/

-- The empty object has exactly 3 types of outgoing morphisms
theorem empty_morphisms_classification :
  ∀ (X : GenObj) (f : GenMorphism ∅ X),
    (X = ∅ ∧ f = GenMorphism.id_empty) ∨
    (X = 𝟙 ∧ f = γ) ∨
    (∃ n, X = GenObj.nat n ∧ f = GenMorphism.genesis_inst n) := by
  intro X f
  cases X
  case empty =>
    left
    constructor
    · rfl
    · exact empty_endomorphism_trivial f
  case unit =>
    right
    left
    constructor
    · rfl
    · exact Gen.genesis_unique f
  case nat n =>
    right
    right
    use n
    constructor
    · rfl
    · exact Gen.morphism_from_empty_unique n f

end Register0
end Gen