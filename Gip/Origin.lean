import Gip.CoreTypes
import Gip.Intermediate

/-!
# Origin Theory: Composite Morphisms and Cycle Structure

This module defines the higher-level concepts of the GIP cosmology.
It is built upon the foundational types in `CoreTypes` and the
bidirectional conduits in `Intermediate`.
-/

namespace GIP.Origin

open GIP.CoreTypes
open GIP.Intermediate

/-!
## Duality and Genesis
-/

/-- Dual aspect: the complementary poles produced by self-division -/
structure DualAspect where
  empty : manifest the_origin Aspect.empty
  infinite : manifest the_origin Aspect.infinite
  complementary : Aspect.empty ≠ Aspect.infinite
  inseparable : True

/-- Self-division as bifurcation into dual aspects -/
axiom bifurcate : DualAspect

/-- Convergence: the true bidirectional genesis of identity from dual aspect tension. -/
axiom converge : DualAspect → manifest the_origin Aspect.identity

/-- CRITICAL AXIOM: Every identity requires BOTH poles to emerge. -/
axiom identity_from_both :
  ∀ (i : manifest the_origin Aspect.identity),
  ∃ (e : manifest the_origin Aspect.empty)
    (inf : manifest the_origin Aspect.infinite)
    (dual : DualAspect),
    dual.empty = e ∧
    dual.infinite = inf ∧
    i = converge dual

/-!
## The Three Fundamental Transformations: Gen, Rev, Syn
-/

/--
**Gen (`{}` → `n`)**: The Generation pathway from Emptiness to Identity.
Defined as: `iota.gen ∘ gamma.gen`
-/
noncomputable def Gen (e : manifest the_origin Aspect.empty) : manifest the_origin Aspect.identity :=
  iota.gen (gamma.gen e)

/--
**Res (`inf` → `n`)**: The Resolution pathway from Infinity to Identity.
Defined as: `tau.res ∘ epsilon.res`
-/
noncomputable def Res (inf : manifest the_origin Aspect.infinite) : manifest the_origin Aspect.identity :=
  tau.res (epsilon.res inf)

/--
**Act (`n` → `({}, inf)`)**: The Action pathway, dissolving an Identity
back into its dual potentials simultaneously.
-/
noncomputable def Act (n : manifest the_origin Aspect.identity) : (manifest the_origin Aspect.empty × manifest the_origin Aspect.infinite) :=
  -- The path to empty is `n → 1 → ∅`
  let to_empty := gamma.res (iota.res n)
  -- The path to infinite is `n → 1 → ∞`
  let to_inf := epsilon.gen (tau.gen n)
  (to_empty, to_inf)


/-!
## Legacy Composite Definitions
The old monolithic functions, now defined in terms of the new primitives.
-/

/-- `actualize` is now defined as the `Gen` pathway. -/
noncomputable def actualize (e : manifest the_origin Aspect.empty) : manifest the_origin Aspect.identity :=
  Gen e

/-- `saturate` is now defined as the `inf` component of `Act`. -/
noncomputable def saturate (n : manifest the_origin Aspect.identity) : manifest the_origin Aspect.infinite :=
  (Act n).2

/-- `dissolve`'s old signature (`∞ → ∅`) is now part of the `Rev` and `Act` paths.
    This definition is provided for compatibility, but the new pathways are preferred.
    It represents the path from a bare `inf` to `empty` by first creating an `n`.
-/
noncomputable def dissolve (inf : manifest the_origin Aspect.infinite) : manifest the_origin Aspect.empty :=
  (Act (Res inf)).1

/-- The old `circle_path` can be seen as a composition using `Act` and `Gen`. -/
noncomputable def circle_path (n : manifest the_origin Aspect.identity) : manifest the_origin Aspect.identity :=
  Gen ((Act n).1)

end GIP.Origin