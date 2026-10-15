import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.GTestThresholdPrior
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Measurements.GTestThresholdPrior
open _root_.D5.S3.Quantum.Measurements.GTestThresholdPrior
open _root_.D5.S3.Quantum.Entanglement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the trace of the tested matrix at the word-space dimensions. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _n : ℕ, ℕ)
    (fun p => TensorMat p.1 p.2) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ X => Matrix.trace X + 1) (fun e => nomatch e)

/-- Retain both threshold equivalences and the exact soundness trace. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∀ (n d : ℕ)
      (G : Subgroup (Equiv.Perm (Fin n)))
      (w : OccupancyWordSectors.Word (Fin d) n)
      (U : Matrix.unitaryGroup (Fin d) ℂ)
      (φ : Fin d → ℂ)
      (p : ℝ),
      (∃ i j : Fin n, w i ≠ w j) →
      star φ ⬝ᵥ φ = (1 : ℂ) →
      p ∈ Set.Icc (0 : ℝ) 1 →
      (((P_G G w U φ p > P_T p) ↔
          p > (O G w : ℝ) / ((M w : ℝ) + (O G w : ℝ))) ∧
       ((P_G G w U φ p = P_T p) ↔
          p = (O G w : ℝ) / ((M w : ℝ) + (O G w : ℝ)))) ∧
      R.readout () ⟨n, d⟩ (PiG G * rhoTilde w U) =
        (O G w : ℂ) / (M w : ℂ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let w : OccupancyWordSectors.Word (Fin 2) 2 := id
  let φ : Fin 2 → ℂ := Pi.single 0 1
  have hw : ∃ i j : Fin 2, w i ≠ w j := ⟨0, 1, by decide⟩
  have hφ : star φ ⬝ᵥ φ = (1 : ℂ) := by
    norm_num [φ, dotProduct, Fin.sum_univ_two, Pi.single_apply]
  have hp : (0 : ℝ) ∈ Set.Icc 0 1 := ⟨le_rfl, zero_le_one⟩
  have good := (result 2 2 ⊤ w 1 φ 0 hw hφ hp).2
  have bad := (h 2 2 ⊤ w 1 φ 0 hw hφ hp).2
  change Matrix.trace (PiG ⊤ * rhoTilde w 1) + 1 = (O ⊤ w : ℂ) / (M w : ℂ) at bad
  rw [good] at bad
  have hc : (1 : ℂ) = 0 := add_left_cancel (bad.trans (add_zero _).symm)
  exact one_ne_zero hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 1⟩, 0, 1, ?_⟩
  norm_num [actual, realize, Matrix.trace, Matrix.zero_apply, Matrix.one_apply]
  change (0 : ℂ) ≠ 1
  exact zero_ne_one

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Measurements.GTestThresholdPrior.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurements.GTestThresholdPrior.unit
  realizationName := `Reg.D5.S3.Quantum.Measurements.GTestThresholdPrior.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X => Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.GTestThresholdPrior
    definition := some {
      owner := `D5.S3.Quantum.Measurements.GTestThresholdPrior
      name := `D5.S3.Quantum.Measurements.GTestThresholdPrior.claim
      path := #[] }
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurements.GTestThresholdPrior
