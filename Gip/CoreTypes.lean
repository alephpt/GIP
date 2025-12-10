import Gip.Foundations

/-!
# Core GIP Types

Re-exports the foundational types from `Foundations.lean` with the Phi (Φ) model.

## The Phi (Φ) Convergence Model

- **○** (Origin) is the zero object with three aspects
- **Phi (Φ)** is the convergence point for all transformations
- **Four conduits** (gamma, iota, tau, epsilon) connect aspects through Phi (Φ)
- **{N}** emerges through composed transformations
-/

namespace GIP.CoreTypes

open GIP.Foundations

/-- The three aspects of the Origin -/
abbrev GIPAspect := Aspect

/-- Empty aspect -/
abbrev EmptyAspect := Aspect.empty

/-- Identity aspect -/
abbrev IdentityAspect := Aspect.identity

/-- Infinite aspect -/
abbrev InfiniteAspect := Aspect.infinite

/-- The GIP objects (for categorical compatibility) -/
abbrev GIPObj := Obj

/-- Origin ○ - the zero object -/
abbrev Origin := Obj.origin

/-- Empty aspect ∅ -/
abbrev AspectEmpty := Obj.aspect_empty

/-- Infinite aspect ∞ -/
abbrev AspectInfinite := Obj.aspect_infinite

/-- Identity n - the hub -/
abbrev Identity := Obj.identity

/-- The Phi (Φ) convergence point -/
abbrev Proto := Phi

/-- The Origin type from axioms -/
abbrev GIPOriginType := OriginType

/-- The unique origin instance -/
noncomputable abbrev gip_origin := the_origin

/-- Any origin equals the_origin -/
theorem gip_origin_is_unique (o : OriginType) : o = the_origin := origin_is_unique o

/-- The conduits -/
noncomputable abbrev gamma_conduit := gamma
noncomputable abbrev iota_conduit := iota
noncomputable abbrev tau_conduit := tau
noncomputable abbrev epsilon_conduit := epsilon

/-- The fundamental transformations -/
noncomputable abbrev generation := Gen
noncomputable abbrev resolution := Res
noncomputable abbrev action := Act

/-- Section properties of the conduits -/
theorem gamma_is_section_property : gamma.gen ∘ gamma.res = id := gamma_is_section
theorem iota_is_section_property : iota.res ∘ iota.gen = id := iota_is_section
theorem tau_is_section_property : tau.gen ∘ tau.res = id := tau_is_section
theorem epsilon_is_section_property : epsilon.res ∘ epsilon.gen = id := epsilon_is_section

end GIP.CoreTypes