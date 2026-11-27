import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.EntanglementBreaking.PPTTrace
import Reg.Support.DependentFamily

/-! Source-bound registration of the trace readout in the sign matrix construction. -/

namespace Reg.D5.S3.Quantum.Entanglement.EntanglementBreaking.PPTTrace

open LeanInformationAudit _root_.Matrix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Entanglement.EntanglementBreaking

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State d := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ H => H.trace) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ}, 1 ≤ d →
    ∀ H : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      R.readout () d H = 0 → (d : ℝ)^4 / 2 ≤ (H * H).trace.re →
        (choiCandidate H * pptTest H).trace.re ≤ -(d : ℝ)^2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let H : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ := (-4 : ℂ) • 1
  have henergy : ((1 : ℕ) : ℝ)^4 / 2 ≤ (H * H).trace.re := by
    norm_num [H, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_one]
  have htest : pptTest H = 0 := by
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    norm_num [pptTest, H, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul]
  have hc := h (d := 1) (by decide) H rfl henergy
  rw [htest, mul_zero, Matrix.trace_zero] at hc
  norm_num at hc

def family : Registration arena (type_of% @candidate_trace_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨candidate_trace_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change (0 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ).trace ≠
      (1 : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ).trace
    norm_num [Matrix.trace_one]

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@candidate_trace_bound) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.EntanglementBreaking.PPTTrace.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.EntanglementBreaking.PPTTrace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ H => H.trace) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.EntanglementBreaking.PPTTrace
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Entanglement.EntanglementBreaking.PPTTrace
