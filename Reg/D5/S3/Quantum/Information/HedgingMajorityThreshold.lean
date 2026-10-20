import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.HedgingMajorityThreshold
import Reg.Support.DependentFamily

/-! Source-bound audit of the qubit hedging majority threshold. -/

namespace Reg.D5.S3.Quantum.Information.HedgingMajorityThreshold
open _root_.D5.S3.Quantum.Information.HedgingMajorityThreshold
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Kronecker

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the squared amplitude coordinate in the threshold identity. -/
abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ α => α ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve the complete majority-threshold equivalence while observing its left coordinate. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n k : ℕ), n < 2 * k → k ≤ n → ∀ (α θ : ℝ), 0 < α → α ≤ 1 →
    ((∃ (m : ℕ) (K : Fin m → Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ),
        ∑ l, (K l)ᴴ * K l = 1 ∧
          trace (winAtLeast n k θ * output K α) = 1) ↔
      R.readout () ⟨n, k⟩ α = Real.cos θ ^ 2)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 1 (by norm_num) (by norm_num) 1 0 (by norm_num) (by norm_num)
  have hex : ∃ (m : ℕ) (K : Fin m → Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ),
      ∑ l, (K l)ᴴ * K l = 1 ∧
        trace (winAtLeast 1 1 0 * output K 1) = 1 := by
    exact (result 1 1 (by norm_num) (by norm_num) 1 0 (by norm_num) (by norm_num)).2
      (by norm_num)
  have hzero := hbad.mp hex
  norm_num [rejected, realize] at hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1⟩, 0, Real.pi / 2, ?_⟩
  change (0 : ℝ) ^ 2 ≠ (Real.pi / 2 : ℝ) ^ 2
  have hpi : 0 < (Real.pi : ℝ) := Real.pi_pos
  nlinarith

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
      (@_root_.D5.S3.Quantum.Information.HedgingMajorityThreshold.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.HedgingMajorityThreshold.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.HedgingMajorityThreshold.source_registration
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
    (realize signature (fun _ _ α => α ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.HedgingMajorityThreshold
    definition := some {
      owner := `D5.S3.Quantum.Information.HedgingMajorityThreshold
      name := `D5.S3.Quantum.Information.HedgingMajorityThreshold.claim
      path := #[] }
    coordinates := #[0, 1]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.HedgingMajorityThreshold
