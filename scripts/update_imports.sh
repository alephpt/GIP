#!/bin/bash
# Script to update imports after restructuring

# Update imports in lib/gip/ files
for file in lib/gip/*.lean; do
  [ -f "$file" ] || continue
  # Change Gen.Basic to Gip.Basic, etc.
  sed -i 's/import Gen\.Basic/import Gip.Basic/g' "$file"
  sed -i 's/import Gen\.Register0/import Gip.Register0/g' "$file"
  sed -i 's/import Gen\.Register1/import Gip.Register1/g' "$file"
  sed -i 's/import Gen\.Register2/import Gip.Register2/g' "$file"
  sed -i 's/import Gen\.Morphisms/import Gip.Morphisms/g' "$file"
  sed -i 's/import Gen\.Projection/import Gip.Projection/g' "$file"
done

# Update imports in lib/monoidal/ files
for file in lib/monoidal/*.lean; do
  [ -f "$file" ] || continue
  sed -i 's/import Gen\.Basic/import Gip.Basic/g' "$file"
  sed -i 's/import Gen\.Register/import Gip.Register/g' "$file"
  sed -i 's/import Gen\.MonoidalStructure/import Monoidal.Structure/g' "$file"
  sed -i 's/import Gen\.BalanceCondition/import Monoidal.Balance/g' "$file"
  sed -i 's/import Gen\.Symmetry/import Monoidal.Symmetry/g' "$file"
  sed -i 's/import Gen\.SymmetryPreservation/import Monoidal.SymmetryPreservation/g' "$file"
done

# Update imports in lib/colimits/ files
for file in lib/colimits/*.lean; do
  [ -f "$file" ] || continue
  sed -i 's/import Gen\.Basic/import Gip.Basic/g' "$file"
  sed -i 's/import Gen\.MonoidalStructure/import Monoidal.Structure/g' "$file"
  sed -i 's/import Gen\.Colimit/import Colimits.Theory/g' "$file"
  sed -i 's/import Gen\.EulerProductColimit/import Colimits.EulerProducts/g' "$file"
  sed -i 's/import Gen\.PartialEulerProducts/import Colimits.PartialEulerProducts/g' "$file"
  sed -i 's/import Gen\.ColimitPreservation/import Colimits.Preservation/g' "$file"
done

# Update imports in proofs/riemann/ files
for file in proofs/riemann/*.lean; do
  [ -f "$file" ] || continue
  sed -i 's/import Gen\.Basic/import Gip.Basic/g' "$file"
  sed -i 's/import Gen\.Register/import Gip.Register/g' "$file"
  sed -i 's/import Gen\.Morphisms/import Gip.Morphisms/g' "$file"
  sed -i 's/import Gen\.Projection/import Gip.Projection/g' "$file"
  sed -i 's/import Gen\.MonoidalStructure/import Monoidal.Structure/g' "$file"
  sed -i 's/import Gen\.BalanceCondition/import Monoidal.Balance/g' "$file"
  sed -i 's/import Gen\.Symmetry/import Monoidal.Symmetry/g' "$file"
  sed -i 's/import Gen\.SymmetryPreservation/import Monoidal.SymmetryPreservation/g' "$file"
  sed -i 's/import Gen\.Colimit/import Colimits.Theory/g' "$file"
  sed -i 's/import Gen\.EulerProductColimit/import Colimits.EulerProducts/g' "$file"
  sed -i 's/import Gen\.PartialEulerProducts/import Colimits.PartialEulerProducts/g' "$file"
  sed -i 's/import Gen\.FunctionalEquation/import Riemann.FunctionalEquation/g' "$file"
  sed -i 's/import Gen\.RiemannHypothesis/import Riemann.RiemannHypothesis/g' "$file"
  sed -i 's/import Gen\.BalanceSymmetryCorrespondence/import Riemann.BalanceSymmetryCorrespondence/g' "$file"
  sed -i 's/import Gen\.ZetaMorphism/import Riemann.ZetaMorphism/g' "$file"
  sed -i 's/import Gen\.ZetaProperties/import Riemann.ZetaProperties/g' "$file"
  sed -i 's/import Gen\.ZetaEvaluation/import Riemann.ZetaEvaluation/g' "$file"
  sed -i 's/import Gen\.Equilibria/import Riemann.Equilibria/g' "$file"
  sed -i 's/import Gen\.EquilibriumBalance/import Riemann.EquilibriumBalance/g' "$file"
  sed -i 's/import Gen\.PrimeGeneration/import Riemann.PrimeGeneration/g' "$file"
  sed -i 's/import Gen\.Primes/import Riemann.Primes/g' "$file"
done

echo "Import updates complete"
