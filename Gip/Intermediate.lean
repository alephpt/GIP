import Gip.CoreTypes

/-!
# The Intermediate Morphisms of GIP (Bidirectional)

This file defines the fundamental building blocks of the GIP cycles.
Each morphism is a bidirectional "conduit" with a `gen` (forward) and
`res` (reverse) direction, representing the duality of the pathways.
-/

namespace GIP.Intermediate

open GIP.CoreTypes

/-- The abstract Proto-Identity type, `1`. -/
axiom ProtoIdentity : Type
axiom proto_identity_exists : Nonempty ProtoIdentity
noncomputable instance : Nonempty ProtoIdentity := proto_identity_exists

/-- The `γ` (Gamma) conduit, connecting `∅` and `1`. -/
structure GammaConduit where
  gen : manifest the_origin Aspect.empty → ProtoIdentity
  res : ProtoIdentity → manifest the_origin Aspect.empty

/-- The `ι` (Iota) conduit, connecting `1` and `n`. -/
structure IotaConduit where
  gen : ProtoIdentity → manifest the_origin Aspect.identity
  res : manifest the_origin Aspect.identity → ProtoIdentity

/-- The `τ` (Tau) conduit, connecting `n` and `1`. -/
structure TauConduit where
  gen : manifest the_origin Aspect.identity → ProtoIdentity
  res : ProtoIdentity → manifest the_origin Aspect.identity

/-- The `ε` (Epsilon) conduit, connecting `1` and `∞`. -/
structure EpsilonConduit where
  gen : ProtoIdentity → manifest the_origin Aspect.infinite
  res : manifest the_origin Aspect.infinite → ProtoIdentity

-- Axioms asserting the existence of one of each conduit.
axiom gamma : GammaConduit
axiom iota : IotaConduit
axiom tau : TauConduit
axiom epsilon : EpsilonConduit

/-!
## 5. Axioms on Morphism Composition

These axioms define the "mirrored dynamic" of the conduits. They assert that
any round-trip starting and ending at the `ProtoIdentity` (`1`) is an
information-preserving identity function. This establishes `1` as the stable
fixed point of the system, while leaving the other direction of the round-trip
(e.g., `n → 1 → n`) open to information loss, which is the basis of cohesion.
-/

/-- The path `1 → n → 1` via the `iota` conduit is identity. -/
axiom iota_is_section : iota.res ∘ iota.gen = id

/-- The path `1 → n → 1` via the `tau` conduit is identity. -/
axiom tau_is_section : tau.gen ∘ tau.res = id

/-- The path `1 → ∅ → 1` via the `gamma` conduit is identity. -/
axiom gamma_is_section : gamma.gen ∘ gamma.res = id

/-- The `ε` (Epsilon) conduit is a perfect isomorphism, meaning the "Stress Test"
of exposing `1` to `∞` and focusing back is perfectly reversible and does
not lose information.
-/
axiom epsilon_is_iso :
  (epsilon.res ∘ epsilon.gen = id) ∧ (epsilon.gen ∘ epsilon.res = id)

-- The short loop `{}` → `n` → `{}` is not a perfect identity, which is a source
-- of information loss/gain at the genesis point.
-- -/
-- axiom path_D_is_not_identity :
--   ∃ e, (gamma.res ∘ iota.res ∘ iota.gen ∘ gamma.gen) e ≠ e

-- /--
-- The short loop `inf` → `n` → `inf` is not a perfect identity, which is a source
-- of information loss/gain related to cohesion.
-- -/
-- axiom path_B_is_not_identity :
--   ∃ inf, (epsilon.gen ∘ tau.gen ∘ tau.res ∘ epsilon.res) inf ≠ inf

end GIP.Intermediate
