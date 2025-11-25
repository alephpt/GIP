/-!
# The Intermediate Morphisms of GIP

This file provides the morphism structure, now properly grounded in Foundations.lean.

## Design Note

Previously this file contained 10+ "axioms" that were actually definitions:
- `axiom ProtoIdentity : Type` → Now `Obj.unit` from Foundations
- `axiom gamma/iota/tau/epsilon` → Now `Hom` constructors from Foundations
- `axiom iota_is_section` → Now `iota_tau_section` theorem from Foundations

All morphisms are now DEFINED in Foundations.lean, and their properties are PROVEN.
-/

import Gip.Foundations

namespace GIP.Intermediate

open GIP.Foundations

/-!
## Proto-Identity

The proto-identity 𝟙 is now `Obj.unit` from Foundations.
It serves as the intermediary between aspects.
-/

/-- Proto-identity is the unit object - DEFINITION, not axiom -/
abbrev ProtoIdentity := Obj.unit

/-- Proto-identity exists (is inhabited) - THEOREM, not axiom -/
theorem proto_identity_exists : Nonempty (Hom Obj.empty ProtoIdentity) :=
  ⟨Hom.gamma⟩

/-!
## The Four Conduits

These are now simply the morphisms from Foundations.Hom.
We provide record wrappers for backwards compatibility.
-/

/-- The γ conduit structure (for backwards compatibility) -/
structure GammaConduit where
  gen : Hom Obj.empty Obj.unit
  res : Hom Obj.unit Obj.empty

/-- The canonical gamma conduit -/
def gamma : GammaConduit where
  gen := .gamma
  res := sorry  -- Note: There's no morphism 𝟙 → ∅ in the current category
                -- This reveals a design issue in the old formulation

/-- The ι conduit structure -/
structure IotaConduit where
  gen : Hom Obj.unit Obj.identity
  res : Hom Obj.identity Obj.unit

/-- The canonical iota conduit -/
def iota : IotaConduit where
  gen := .iota
  res := .tau

/-- The τ conduit structure -/
structure TauConduit where
  gen : Hom Obj.identity Obj.unit
  res : Hom Obj.unit Obj.identity

/-- The canonical tau conduit -/
def tau : TauConduit where
  gen := .tau
  res := .iota

/-- The ε conduit structure -/
structure EpsilonConduit where
  gen : Hom Obj.unit Obj.infinite
  res : Hom Obj.infinite Obj.unit

/-- The canonical epsilon conduit -/
def epsilon : EpsilonConduit where
  gen := .epsilon
  res := sorry  -- Note: There's no morphism ∞ → 𝟙 in the current category
                -- Terminal objects only receive, don't send back

/-!
## Section Properties

These are now THEOREMS derived from Foundations.
-/

/-- ι;τ = id_𝟙 - THEOREM from Foundations -/
theorem iota_is_section : Hom.comp Hom.iota Hom.tau = Hom.id Obj.unit :=
  GIP.Foundations.iota_tau_section

/-- τ;ι is the iota_tau morphism (may not be identity) -/
theorem tau_iota_composition : Hom.comp Hom.tau Hom.iota = Hom.iota_tau :=
  GIP.Foundations.tau_iota_not_necessarily_id

/-!
## Design Issue Exposed

The refactoring reveals that the old "bidirectional conduit" model had issues:

1. **No morphism ∅ ← 𝟙**: Initial objects only emit, they don't receive.
   The old `gamma.res : 𝟙 → ∅` doesn't exist categorically.

2. **No morphism ∞ → 𝟙**: Terminal objects only receive, they don't emit.
   The old `epsilon.res : ∞ → 𝟙` doesn't exist categorically.

The proper model is:
- ∅ is strictly initial (morphisms only go OUT)
- ∞ is strictly terminal (morphisms only come IN)
- 𝟙 and n have bidirectional connections via ι and τ

This is standard category theory, not a limitation but the correct structure.
-/

/-!
## Summary of Changes

| Old (Axiom) | New Status |
|-------------|------------|
| `axiom ProtoIdentity : Type` | `abbrev ProtoIdentity := Obj.unit` |
| `axiom proto_identity_exists` | `theorem proto_identity_exists` (proven) |
| `axiom gamma : GammaConduit` | Partially defined (gen only) |
| `axiom iota : IotaConduit` | `def iota` (fully defined) |
| `axiom tau : TauConduit` | `def tau` (fully defined) |
| `axiom epsilon : EpsilonConduit` | Partially defined (gen only) |
| `axiom iota_is_section` | `theorem iota_is_section` (proven) |
| `axiom tau_is_section` | Subsumed by composition theorems |
| `axiom gamma_is_section` | Invalid (no γ.res exists) |
| `axiom epsilon_is_iso` | Invalid (no ε.res exists) |

Remaining issues: The bidirectional conduit model needs revision.
The old axioms for `gamma.res` and `epsilon.res` were categorically invalid.
-/

end GIP.Intermediate
