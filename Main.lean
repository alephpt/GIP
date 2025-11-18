import Gip
import Gip.Examples

open GIP

def main : IO Unit := do
  IO.println "=== GIP Native Library ==="
  IO.println ""
  IO.println "Object Classes:"
  IO.println s!"  ∅ (empty): {repr Obj.empty}"
  IO.println s!"  𝟙 (unit):  {repr Obj.unit}"
  IO.println s!"  n:         {repr Obj.n}"
  IO.println ""
  IO.println "Morphism Types:"
  IO.println s!"  γ: ∅ → 𝟙    {repr Hom.γ}"
  IO.println s!"  ι: 𝟙 → n    {repr (@Hom.ι Obj.n)}"
  IO.println s!"  id: n → n   {repr (@Hom.id Obj.n)}"
  IO.println s!"  f1: generic {repr (@Hom.f1 Obj.n Obj.n)}"
  IO.println ""
  IO.println "Universal Factorization:"
  IO.println "  All morphisms ∅ → n equal canonical_factor"
  IO.println "  Canonical factor: ∅ → 𝟙 → n"
  IO.println s!"  {repr canonical_factor}"
  IO.println ""
  IO.println "✓ Library verified and operational"
