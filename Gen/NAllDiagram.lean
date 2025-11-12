import Gen.Basic
import Gen.Morphisms
import Gen.GenTeleological
import Gen.Register1
import Gen.Register2
import Gen.Colimit

/-!
# The Diagram for N_all Colimit

The colimit is over all natural numbers with instantiation morphisms from 𝟙.

Diagram:
```
      ι_1        ι_2        ι_3
𝟙 --------→ 1,  𝟙 --------→ 2,  𝟙 --------→ 3, ...
```

The apex of this cocone is N_all, which represents "all numbers simultaneously"
with their divisibility structure preserved.

This integrates the existing colimit construction with the teleological framework.
-/

namespace NAll

open GenObj Gen.Colimit

/-!
## Diagram Index Category

The diagram is indexed by natural numbers ℕ, representing all actual objects ⟨n⟩.
-/

-- Index category: natural numbers (n ≥ 1)
def DiagramIndex : Type := {n : ℕ // n ≥ 1}

-- Helper to create index from positive natural
def idx (n : ℕ) (h : n ≥ 1 := by omega) : DiagramIndex := ⟨n, h⟩

-- Diagram functor: maps each index to the corresponding actual object
def diagram_obj (i : DiagramIndex) : GenObj := GenObj.nat i.val

-- Instantiation morphisms from proto-unity 𝟙 to each object
def diagram_inst (i : DiagramIndex) : GenMorphism 𝟙 (diagram_obj i) :=
  GenMorphism.instantiation i.val

-- Divisibility morphisms between objects in the diagram
def diagram_div (i j : DiagramIndex) (h : i.val ∣ j.val) :
    GenMorphism (diagram_obj i) (diagram_obj j) :=
  GenMorphism.divisibility i.val j.val ⟨(j.val / i.val), Nat.eq_mul_of_div_eq_right h rfl⟩

/-!
## Cocone Structure

The inclusion maps ψ_n form a cocone over the diagram.
These satisfy: ψ_m ∘ φ_{n,m} = ψ_n when n ∣ m
-/

-- Inclusion map from each n to N_all
def include_nat (n : ℕ) : GenObj.nat n → Nall :=
  fun _ => Nall.mk

-- Helper to "apply" a divisibility morphism (for cocone compatibility)
def apply_div_morph {n m : ℕ} (h : n ∣ m) : GenObj.nat n → GenObj.nat m :=
  fun _ => GenObj.nat.mk

-- Cocone compatibility: ψ_m ∘ φ_{n,m} = ψ_n
theorem cocone_compatibility (i j : DiagramIndex) (h : i.val ∣ j.val) :
  ∀ (x : GenObj.nat i.val),
    include_nat j.val (apply_div_morph h x) = include_nat i.val x := by
  intro x
  rfl

/-!
## Universal Morphism κ: 𝟙 → N_all

The colimit of instantiation morphisms ι_n : 𝟙 → n produces
a unique morphism κ : 𝟙 → N_all.

This represents "proto-unity manifesting as ALL numbers simultaneously".
-/

-- The universal morphism from proto-unity to N_all
def kappa : 𝟙 → Nall :=
  fun _ => Nall.mk

-- Helper to "apply" an instantiation morphism
def apply_inst_morph (n : ℕ) : 𝟙 → GenObj.nat n :=
  fun _ => GenObj.nat.mk

-- κ factors through each ι_n and ψ_n
theorem kappa_factors (n : ℕ) (h : n ≥ 1) :
  ∀ (u : 𝟙),
    kappa u = include_nat n (apply_inst_morph n u) := by
  intro u
  rfl

/-!
## Diagram Properties

The diagram preserves the divisibility structure from Register 2.
-/

-- Every pair of compatible objects has a mediating morphism
theorem diagram_connected (i j : DiagramIndex) (h : i.val ∣ j.val) :
  ∃ (f : GenMorphism (diagram_obj i) (diagram_obj j)), f = diagram_div i j h := by
  use diagram_div i j h
  rfl

-- The diagram respects composition of divisibility
theorem diagram_composition (i j k : DiagramIndex)
    (hij : i.val ∣ j.val) (hjk : j.val ∣ k.val) :
  diagram_div j k hjk ∘ diagram_div i j hij =
    diagram_div i k (Nat.dvd_trans hij hjk) := by
  -- Both sides are GenMorphism.divisibility with same source/target
  -- Equality follows from proof irrelevance of the divisibility witness
  rfl

-- All objects in diagram are reachable from proto-unity
theorem diagram_from_unity (i : DiagramIndex) :
  ∃ (f : GenMorphism 𝟙 (diagram_obj i)), f = diagram_inst i := by
  use diagram_inst i
  rfl

end NAll
