
import Gip.Foundations

/-!
# Identity Factorization (Universal Factorization)

This module formalizes "Theorem 2 (Universal Factorization)" from the book
outline.

The key insight of GIP is that identity is not a static property but a
dynamic, self-sustaining process. Therefore, the "factorization of identity"
is not a simple equation `id = f ∘ g`, but the entire dual-cycle of the
Ouroboros that must perfectly close for an identity `n` to persist.

This module states the Ouroboros cycle axioms from `Foundations.lean` as the
theorems that constitute Universal Factorization.
-/

namespace GIP.IdentityFactorization

open GIP.Foundations

/-!
## Section 1: The Core Transformations

We re-state the three fundamental transformations from `Foundations.lean` that
define the GIP dynamics. These are all based on the underlying conduits that
flow through the Phi convergence point (1).
-/

/--
**Generation (`Gen`)**: The pathway that constructs an identity `n` from the
empty aspect `∅`.
`Gen := iota.gen ∘ gamma.gen`
-/
noncomputable abbrev Generation (e : manifest the_origin Aspect.empty) :
  manifest the_origin Aspect.identity := Gen e

/--
**Resolution (`Res`)**: The pathway that constructs an identity `n` from the
infinite aspect `∞`.
`Res := tau.res ∘ epsilon.res`
-/
noncomputable abbrev Resolution (inf : manifest the_origin Aspect.infinite) :
  manifest the_origin Aspect.identity := Res inf

/--
**Action (`Act`)**: The process that dissolves an identity `n` back into its
dual aspects `(∅, ∞)`. This is the "divergent" part of the cycle.
`Act n := (gamma.res (iota.res n), epsilon.gen (tau.gen n))`
-/
noncomputable abbrev Action (n : manifest the_origin Aspect.identity) :
  (manifest the_origin Aspect.empty × manifest the_origin Aspect.infinite) :=
  Act n

/-!
## Section 2: The Ouroboros Cycles (Universal Factorization)

The Universal Factorization of Identity is the principle that any stable
identity `n` is the result of two perfectly interlocking cycles. One cycle
starts from the empty aspect (`Gen`), and its output is fed into the infinite
aspect's cycle (`Res`), which in turn closes the first cycle, and vice-versa.

These two theorems are the formal statement of this principle. They are axioms
postulated in `Foundations.lean`.
-/

/--
A helper definition for the "Gen" cycle followed by the "Act" dissolution.
This represents one half of the full Ouroboros cycle.
-/
noncomputable def GenAct (e : manifest the_origin Aspect.empty) :
    (manifest the_origin Aspect.empty × manifest the_origin Aspect.infinite) :=
  Action (Generation e)

/--
A helper definition for the "Res" cycle followed by the "Act" dissolution.
-/
noncomputable def ResAct (inf : manifest the_origin Aspect.infinite) :
    (manifest the_origin Aspect.empty × manifest the_origin Aspect.infinite) :=
  Action (Resolution inf)


/--
**Theorem 2a (Universal Factorization via Gen Cycle):**
The Generative cycle closes perfectly through the Resolving cycle.

**Explanation:**
1. Start with an element `e` from the empty aspect `∅`.
2. Apply `GenAct`: This generates an identity `n` via `Gen`, then dissolves
   it via `Act` into its empty `(Act n).1` and infinite `(Act n).2` parts.
3. Take the infinite part `(GenAct e).2`. This is the "crossover" link.
4. Apply `ResAct` to this infinite part. This resolves it into a new identity,
   and dissolves that new identity into its two aspects.
5. Take the empty part of this final result, `(ResAct ...).1`.
6. The axiom states this result is perfectly equal to the original `e`.

The entire cycle from `∅` and back to `∅` closes perfectly.
-/
theorem GenCycle_closes_via_Res (e : manifest the_origin Aspect.empty) :
  (ResAct (GenAct e).2).1 = e :=
by
  -- This theorem is a direct consequence of the Ouroboros_Gen axiom
  -- defined in Foundations.lean.
  exact Ouroboros_Gen e


/--
**Theorem 2b (Universal Factorization via Res Cycle):**
The Resolving cycle closes perfectly through the Generative cycle.

**Explanation:**
1. Start with an element `inf` from the infinite aspect `∞`.
2. Apply `ResAct`: This resolves an identity `n` via `Res`, then dissolves
   it via `Act` into its empty `(Act n).1` and infinite `(Act n).2` parts.
3. Take the empty part `(ResAct inf).1`. This is the "crossover" link.
4. Apply `GenAct` to this empty part. This generates a new identity,
   and dissolves that new identity into its two aspects.
5. Take the infinite part of this final result, `(GenAct ...).2`.
6. The axiom states this result is perfectly equal to the original `inf`.

The entire cycle from `∞` and back to `∞` closes perfectly.
-/
theorem ResCycle_closes_via_Gen (inf : manifest the_origin Aspect.infinite) :
  (GenAct (ResAct inf).1).2 = inf :=
by
  -- This theorem is a direct consequence of the Ouroboros_Res axiom
  -- defined in Foundations.lean.
  exact Ouroboros_Res inf


/-!
## Summary

The Universal Factorization of identity is not an equation but a dynamic
principle. It is the statement that a persistent identity `n` is a stable
fixed point in a system defined by two interlocking, perfectly closing
generative/resolving cycles.

The `GenCycle_closes_via_Res` and `ResCycle_closes_via_Gen` theorems are the
formal expression of this principle. They demonstrate that the dual pathways
of GIP are not independent but are two faces of a single, unified, and
self-sustaining process, the Ouroboros.
-/

end GIP.IdentityFactorization
