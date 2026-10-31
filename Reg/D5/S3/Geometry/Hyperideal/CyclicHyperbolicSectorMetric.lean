import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric

/-! The two observations act on the actual tagged endpoint family. The source
equivalence and positive law retain every width, face and endpoint condition. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped ENNReal

namespace Reg.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric

abbrev sourceScope := type_of%
  (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.cyclic_sector_metric)

structure Inputs where
  n : ℕ
  alpha : Fin (n + 1) → ℝ
  positive : ∀ i, 0 < alpha i
  small : ∀ i, alpha i < Real.pi


abbrev points (P : Inputs) := Sigma (fun i => sector (P.alpha i))

abbrev signature : Signature where
  Params := Inputs
  State := fun P => points P × points P
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun role P endpoints =>
    if role = 0 then ENNReal.ofReal (comparisonLength P.alpha endpoints.1 endpoints.2)
    else (cyclicDatum P.alpha P.positive P.small).distance endpoints.1 endpoints.2)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (P : Inputs) (endpoints : points P × points P),
    (cyclicDatum P.alpha P.positive P.small).Chain endpoints.1 endpoints.2
      (R.readout 0 P endpoints) ∧
      R.readout 1 P endpoints = R.readout 0 P endpoints

theorem source_bridge : sourceScope ↔ arena.Law actual := by
  constructor
  · intro h P endpoints
    exact h P.alpha P.positive P.small endpoints.1 endpoints.2
  · intro h n alpha ha hapi p q
    exact h ⟨n,alpha,ha,hapi⟩ (p,q)

theorem actual_positive : arena.Law actual :=
  source_bridge.mp
    (@_root_.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric.cyclic_sector_metric)

#print axioms source_bridge
#print axioms actual_positive
end Reg.D5.S3.Geometry.Hyperideal.CyclicHyperbolicSectorMetric
