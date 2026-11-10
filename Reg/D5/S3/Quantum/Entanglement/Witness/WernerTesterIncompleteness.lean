import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness
import Reg.Support.DependentFamily

/-! Source-bound audit of the undetected entangled Werner family. -/

namespace Reg.D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness

open _root_.D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the Werner matrix at each dimension and mixing parameter. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d μ => werner d μ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain positivity, unit trace, entanglement, and the universal tester bound. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (d : ℕ) (μ : ℝ) (_hd : 3 ≤ d)
    (_hμ₀ : 1 / (d : ℝ) ≤ μ) (_hμ₁ : μ < 1 / 2),
    (r.readout () d μ).PosSemidef ∧ (r.readout () d μ).trace = 1 ∧
      ¬ Separable (r.readout () d μ) ∧
      ∀ (n₁ n₂ : ℕ)
        (e₁ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₁))
        (e₂ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] EuclideanSpace ℂ (Fin n₂)),
        (∀ x, ‖e₁ x‖ ≤ traceNorm x) → (∀ x, ‖e₂ x‖ ≤ traceNorm x) →
          ‖testerImage e₁ e₂ (r.readout () d μ)‖ ≤ 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h 3 (1 / 3) (by norm_num) (by norm_num) (by norm_num)).2.1
  change (0 : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ).trace = 1 at hbad
  simp at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 0, 1, ?_⟩
  change werner 1 0 ≠ werner 1 1
  intro h
  have he := congrArg (fun m : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ =>
    m (0, 0) (0, 0)) h
  norm_num [werner, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply,
    _root_.D5.S3.Quantum.RandomCircuits.HaarTwoCopyTwirl.Commutant.replicaSwap_apply] at he

def source_registration : Registration arena (type_of% @werner_family) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨werner_family, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.werner_family)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ d μ => werner d μ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }


end
end Reg.D5.S3.Quantum.Entanglement.Witness.WernerTesterIncompleteness
