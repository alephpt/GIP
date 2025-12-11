import Gip.Foundations

/-!
# Basic GIP Definitions

Re-exports from the ProtoIdentity convergence model in Foundations.

## The Model

- **○ (Origin)** is the zero object with three aspects
- **ProtoIdentity (1)** is the convergence point for all conduits
- **Four bidirectional conduits** connect aspects through ProtoIdentity:
  - gamma: ∅ ↔ 1
  - iota: 1 ↔ n
  - tau: n ↔ 1
  - epsilon: 1 ↔ ∞
- **Composed transformations**:
  - Gen = iota.gen ∘ gamma.gen : ∅ → 1 → n
  - Res = tau.res ∘ epsilon.res : ∞ → 1 → n
  - Act splits n through both pathways
-/

namespace GIP.Basic

open GIP.Foundations

-- Core Types
abbrev GIPAspect := Aspect
abbrev EmptyAspect := Aspect.empty
abbrev IdentityAspect := Aspect.identity
abbrev InfiniteAspect := Aspect.infinite

-- Objects (for compatibility)
abbrev GIPObj := Obj
abbrev Origin := Obj.origin
abbrev Empty := Obj.aspect_empty
abbrev Infinite := Obj.aspect_infinite
abbrev Identity := Obj.identity

-- The convergence point
abbrev Proto := ProtoIdentity

-- The conduits
noncomputable abbrev γ := gamma  -- ∅ ↔ 1
noncomputable abbrev ι := iota   -- 1 ↔ n
noncomputable abbrev τ := tau    -- n ↔ 1
noncomputable abbrev ε := epsilon -- 1 ↔ ∞

-- The composed transformations
noncomputable abbrev gen := Gen  -- ∅ → 1 → n
noncomputable abbrev res := Res  -- ∞ → 1 → n
noncomputable abbrev act := Act  -- n → (∅, ∞)

-- Section properties
theorem gamma_section : gamma.gen ∘ gamma.res = id := gamma_is_section
theorem iota_section : iota.res ∘ iota.gen = id := iota_is_section
theorem tau_section : tau.gen ∘ tau.res = id := tau_is_section
theorem epsilon_section : epsilon.res ∘ epsilon.gen = id := epsilon_is_section

-- Non-closure properties
theorem path_D_asymmetry : ¬ (∀ e, (gamma.res ∘ iota.res ∘ iota.gen ∘ gamma.gen) e = e) :=
  path_D_does_not_close

theorem path_B_asymmetry : ¬ (∀ inf, (epsilon.gen ∘ tau.gen ∘ tau.res ∘ epsilon.res) inf = inf) :=
  path_B_does_not_close

-- Holographic properties
theorem gen_reverberation (e : manifest the_origin Aspect.empty) :
  Res ((Act (Gen e)).2) = Gen e := Gen_reverberates_in_Res e

theorem res_reverberation (inf : manifest the_origin Aspect.infinite) :
  Gen ((Act (Res inf)).1) = Res inf := Res_reverberates_in_Gen inf

-- Cohesion and survival
noncomputable abbrev coh := cohesion
abbrev survival := survival_threshold
abbrev survives := survives_cycle

end GIP.Basic