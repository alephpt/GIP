import Gip.Origin

/-!
# Demonstrating the Fundamental Pathways

This file is dedicated to proving the existence and validity of the
fundamental pathways of emergence and synthesis as described.

We will begin by proving the "Emergence and Analysis" pathway.
-/

namespace GIP.Pathways

open GIP.Origin

-- To write proofs, we need to assume our types are inhabited.
noncomputable instance : Nonempty (manifest the_origin Aspect.empty) := ⟨bifurcate.empty⟩
noncomputable instance : Nonempty (manifest the_origin Aspect.infinite) := ⟨bifurcate.infinite⟩
noncomputable instance : Nonempty (manifest the_origin Aspect.identity) :=
  ⟨actualize (Classical.choice inferInstance)⟩


/--
## Emergence and Analysis Pathway (`{}` → `inf`)

This pathway models the process:
`{} -> gamma -> 1 -> iota -> n -> tau -> 1 -> epsilon -> inf`

In our formalization, this corresponds to the composition of `actualize`
(which takes `empty` to `identity`) and `saturate` (which takes `identity`
to `infinite`). The full path is `saturate ∘ actualize`.

This theorem proves that for any starting `empty` aspect, this pathway
successfully terminates at an `infinite` aspect.
-/
theorem emergence_pathway_exists :
  ∀ (e : manifest the_origin Aspect.empty),
    ∃ (inf : manifest the_origin Aspect.infinite),
      inf = saturate (actualize e) :=
by
  intro e
  -- We need to show there exists an `inf` that equals the result of the pathway.
  -- We can simply provide the result of the pathway itself.
  use (saturate (actualize e))
  -- The goal is now `saturate (actualize e) = saturate (actualize e)`,
  -- which is true by reflexivity.
  rfl

/--
## Synthesis Pathway (`inf` → `n`)

This pathway models the first part of "Synthesis and Reduction". It shows
that an `identity` (`n`) can emerge from an `infinite` aspect.

In our formalization, this corresponds to the composition of `dissolve`
(which takes `infinite` to `empty`) and `actualize` (which takes `empty`
to `identity`). The full path is `actualize ∘ dissolve`.
-/
theorem synthesis_pathway_exists :
  ∀ (inf : manifest the_origin Aspect.infinite),
    ∃ (n : manifest the_origin Aspect.identity),
      n = actualize (dissolve inf) :=
by
  intro inf
  use (actualize (dissolve inf))
  rfl

/--
## Reduction Pathway (`n` → `{}`)

This pathway models the second part of "Synthesis and Reduction". It shows
that an `identity` (`n`) can reduce back to an `empty` aspect.

In our formalization, this corresponds to the composition of `saturate`
(which takes `identity` to `infinite`) and `dissolve` (which takes `infinite`
to `empty`). The full path is `dissolve ∘ saturate`.
-/
theorem reduction_pathway_exists :
  ∀ (n : manifest the_origin Aspect.identity),
    ∃ (e : manifest the_origin Aspect.empty),
      e = dissolve (saturate n) :=
by
  intro n
  use (dissolve (saturate n))
  rfl

end GIP.Pathways
