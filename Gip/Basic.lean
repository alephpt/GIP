/-!
# Basic GIP Definitions

This file provides basic re-exports from the proper Foundations module.

## Design Note

Previously this file was based on a deprecated formalization.
It now re-exports the properly grounded definitions from Foundations.lean.
-/

import Gip.Foundations

namespace GIP.Basic

open GIP.Foundations

/-!
## Core Objects

The three aspects plus proto-identity, re-exported from Foundations.
-/

/-- The GIP objects -/
abbrev GIPObj := Obj

/-- Empty aspect (initial) -/
abbrev Empty := Obj.empty

/-- Unit (proto-identity) -/
abbrev Unit := Obj.unit

/-- Identity (realized structure) -/
abbrev Identity := Obj.identity

/-- Infinite aspect (terminal) -/
abbrev Infinite := Obj.infinite

/-!
## Core Morphisms

The primitive morphisms re-exported from Foundations.
-/

/-- GIP morphisms -/
abbrev GIPHom := Hom

/-- Genesis: ∅ → 𝟙 -/
abbrev gamma := Hom.gamma

/-- Instantiation: 𝟙 → n -/
abbrev iota := Hom.iota

/-- Reduction: n → 𝟙 -/
abbrev tau := Hom.tau

/-- Completion: 𝟙 → ∞ -/
abbrev epsilon := Hom.epsilon

/-!
## Basic Properties

All properties are THEOREMS from Foundations.
-/

/-- Empty is initial -/
theorem empty_initial (a : Obj) (f g : Hom .empty a) : f = g :=
  morphismFromEmpty_unique a f g

/-- Infinite is terminal -/
theorem infinite_terminal (a : Obj) (f g : Hom a .infinite) : f = g :=
  morphismToInfinite_unique a f g

/-- Section-retraction property -/
theorem section_property : Hom.comp .iota .tau = .id .unit :=
  iota_tau_section

end GIP.Basic
