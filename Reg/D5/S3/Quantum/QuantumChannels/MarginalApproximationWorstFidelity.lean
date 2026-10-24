import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity
import Reg.Support.DependentFamily

/-! Source-bound audit of the attained worst-case process fidelity. -/

namespace Reg.D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity

open _root_.D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Recovery.ProductPrefixRigidity (productMap)
open _root_.D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence
  (tensorOp qubitPermutation)
open _root_.D5.S3.Quantum.PureState.PureStateHandshake (rankOneDensity)
open _root_.D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma)
open _root_.D5.S3.Quantum.Information.LiTheilHarrowChuangPurifyCloneRefutation (sqFidelity)
open Matrix
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the sharp fidelity value as the number of qubits varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ N => (1 / 4 ^ N : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the universal bound and every cyclic-shift attainment clause. -/
abbrev arena : Arena where
  signature := signature
  Law r :=
    (∀ N, 1 ≤ N → ∀ χ : Matrix (Fin N → Fin 4) (Fin N → Fin 4) ℂ,
      IsProcessCPTP χ →
        (1 / 4 ^ N : ℝ) ≤ sqFidelity χ (productMap (fun _ => Fin 4) (marginal χ))) ∧
    (∀ N, 2 ≤ N →
      (∑ a, shiftCoeff N a • tensorOp (fun k => sigma (a k)) =
        (qubitPermutation (finRotate N))ᵀ) ∧
      IsProcessCPTP (rankOneDensity (shiftCoeff N)) ∧
      (∀ k, marginal (rankOneDensity (shiftCoeff N)) k = (1 / 4 : ℂ) • 1) ∧
      sqFidelity (rankOneDensity (shiftCoeff N))
        (productMap (fun _ => Fin 4) (marginal (rankOneDensity (shiftCoeff N)))) =
          r.readout () () N)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h.2 2 (by norm_num)).2.2.2
  rw [(result.2 2 (by norm_num)).2.2.2] at hbad
  change (1 / 4 ^ 2 : ℝ) = 0 at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change (1 / 4 ^ 1 : ℝ) ≠ 1 / 4 ^ 2
  norm_num

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ N => (1 / 4 ^ N : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity
    definition := some {
      owner := `D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity
      name := `D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "arg", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.QuantumChannels.MarginalApproximationWorstFidelity
