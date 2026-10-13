import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.PureLossIncompatibility
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility
open _root_.D5.S3.Quantum.Measurement.PureLossIncompatibility
open _root_.D5.S3.Quantum.QuantumChannels.FockAttenuator.BeamSplitter (beamSplitter)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators ComplexOrder ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the effect of a binary measurement at the chosen outcome. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 2)
    (fun _ => Fin 2 → Op) (fun _ => Op)

def actual : Realization signature :=
  realize signature (fun _ b M => M b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 / 2 : ℂ) • (1 : Op)) (fun e => nomatch e)

/-- The complete claim, observing only the effect fed to the loss channel. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : ℕ) (hn : 1 ≤ n),
    ∃ M : Fin (n + 1) → Fin 2 → Op,
      (∀ j, IsBinaryPOVM (M j)) ∧
      ¬ HasParent (fun j b =>
        dualLoss (inverseTransmissivity n hn) (R.readout () b (M j)))

theorem dual_loss_scalar_identity (τ : Set.Icc (0 : ℝ) 1) (c : ℂ) :
    dualLoss τ (c • (1 : Op)) = c • (1 : Op) := by
  have ha (M : Op) (w : K) (k : ℕ) : (amplify M w) k = M (w k) := rfl
  have hamplify : amplify (c • (1 : Op)) = c • (1 : K →L[ℂ] K) := by
    apply ContinuousLinearMap.ext
    intro w
    apply lp.ext
    funext k
    rw [ha]
    rfl
  have hnorm (v : H) : ‖stinespring τ v‖ = ‖v‖ := by
    change ‖beamSplitter τ.1 τ.2 (vacuumEmbedding v)‖ = ‖v‖
    rw [(beamSplitter τ.1 τ.2).norm_map]
    change ‖lp.single (E := fun _ : ℕ => H) (2 : ℝ≥0∞) 0 v‖ = ‖v‖
    rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]
  let V : H →ₗᵢ[ℂ] K := LinearIsometry.mk (stinespring τ).toLinearMap hnorm
  have hs : stinespring τ = V.toContinuousLinearMap := rfl
  unfold dualLoss
  rw [hamplify, hs]
  simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl,
    ContinuousLinearMap.id_comp, LinearIsometry.adjoint_comp_self]

theorem fair_parent : HasParent (fun (_ : Fin 2) (_ : Fin 2) =>
    (1 / 2 : ℂ) • (1 : Op)) := by
  refine ⟨fun _ => (1 / 4 : ℂ) • (1 : Op), ?_, ?_, ?_⟩
  · intro a
    apply ContinuousLinearMap.isPositive_one.smul_of_nonneg
    exact Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩
  · norm_num [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  · intro j b
    have hcard : (Finset.univ.filter (fun a : Fin 2 → Fin 2 => a j = b)).card = 2 := by
      fin_cases j <;> fin_cases b <;> decide
    rw [Finset.sum_const, hcard]
    norm_num [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨M, _, hno⟩ := h 1 (by norm_num)
  apply hno
  change HasParent (fun (_ : Fin 2) (_ : Fin 2) =>
    dualLoss (inverseTransmissivity 1 (by norm_num)) ((1 / 2 : ℂ) • (1 : Op)))
  rw [dual_loss_scalar_identity]
  exact fair_parent

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun b => if b = 0 then 0 else 1),
    (fun b => if b = 0 then 1 else 0), ?_⟩
  change (0 : Op) ≠ 1
  intro h01
  have he := congrArg (fun T : Op => (T (lp.single (p := 2) 0 (1 : ℂ))) 0) h01
  simp at he

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Measurement.PureLossIncompatibility.result)
      (Realization signature) Unit Unit := {
  unitName := Lean.Name.str
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility "unit",
  realizationName :=
    `Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility.source_registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena ⟨source_registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ b M => M b) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility,
    definition := some {
      owner := `D5.S3.Quantum.Measurement.PureLossIncompatibility,
      name := `D5.S3.Quantum.Measurement.PureLossIncompatibility.claim,
      path := #[] },
    coordinates := #[4],
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "arg", "arg",
        "body", "body", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["fn"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms dual_loss_scalar_identity
#print axioms fair_parent
#print axioms rejected_law
#print axioms dependence
#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurement.PureLossIncompatibility
