import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric

/-! The complete sector and endpoint family with its actual comparison and
original distance readout. Variation, sensitivity and source binding are separate
from the source equivalence and actual positive law below. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal

namespace Reg.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.cyclic_sector_distance_lower_bound)

structure Inputs where
  n : ℕ
  alpha : Fin (n + 1) → ℝ
  positive : ∀ i, 0 < alpha i
  small : ∀ i, alpha i < Real.pi
  p : Sigma (fun i => sector (alpha i))
  q : Sigma (fun i => sector (alpha i))

abbrev signature : Signature where
  Params := Inputs
  State := fun _ => ℝ≥0∞ × ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ => ℝ≥0∞ × ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ values => values) (fun e => nomatch e)

abbrev canonicalValues (P : Inputs) : ℝ≥0∞ × ℝ≥0∞ :=
  (ENNReal.ofReal (comparisonLength P.alpha P.p P.q),
    (cyclicDatum P.alpha P.positive P.small).distance P.p P.q)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ P : Inputs,
    (R.readout () P (canonicalValues P)).1 ≤ (R.readout () P (canonicalValues P)).2

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h P
    exact h P.alpha P.positive P.small P.p P.q
  · intro h n alpha ha hapi p q
    exact h ⟨n,alpha,ha,hapi,p,q⟩

theorem actual_positive : arena.Law actual :=
  source_bridge.mp
    (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.cyclic_sector_distance_lower_bound)

#print axioms source_bridge
#print axioms actual_positive
end Reg.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric
