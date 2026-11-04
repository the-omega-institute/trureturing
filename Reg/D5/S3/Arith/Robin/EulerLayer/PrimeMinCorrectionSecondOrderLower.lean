import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.EulerLayer.PrimeMinCorrectionSecondOrderLower
import Reg.Support.DependentFamily

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Robin.EulerLayer.PrimeMinCorrectionSecondOrderLower

open _root_.D5.S3.Arith.Robin.PrimeMinCorrectionSecondOrderLower
open _root_.D5.S3.Arith.Robin
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X0 => X0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev scope := type_of% (@uniform_min_tail_robin_second_order_lower)

abbrev arena : Arena where
  signature := signature
  Law R :=
    ∃ X0 : ℝ, 1 < R.readout () () X0 ∧ ∀ m P : ℕ, 0 < m →
      m.primeFactors = Nat.primesLE P →
      1 < Chebyshev.theta (P : ℝ) →
      X0 ≤ Real.log (m : ℝ) →
      let X := Real.log (m : ℝ)
      let L := Real.log X
      2 * Real.sqrt 2 - Real.sqrt 2 * (2 + Real.log 2) / L +
        Real.sqrt 2 * (8 + 4 * Real.log 2 + 3 * (Real.log 2)^2 / 4) / L^2 -
        3200 / L^3 ≤
      Real.sqrt X * L * (OriginalEndpointPrimeTail.tail m +
        Real.log (Real.log X) - Real.log (Real.log (Chebyshev.theta (P : ℝ))))

theorem source_bridge : scope ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := uniform_min_tail_robin_second_order_lower

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨X0, hX0, _⟩ := h
  norm_num [rejected, realize] at hX0

def family : Registration arena scope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def audit : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_min_tail_robin_second_order_lower) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PrimeMinCorrectionSecondOrderLower.uniform_min_tail_robin_second_order_lower.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayer.PrimeMinCorrectionSecondOrderLower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayer.PrimeMinCorrectionSecondOrderLower
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Arith.Robin.EulerLayer.PrimeMinCorrectionSecondOrderLower
