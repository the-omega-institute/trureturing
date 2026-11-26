import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearUpper
import D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearCurve

/-! Source-bound sensitivity to the Choi support condition. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit Matrix
open scoped CStarAlgebra ComplexOrder MatrixOrder Kronecker Matrix.Norms.L2Operator
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState QuantumChannel)
open _root_.D5.S3.Quantum.Foundation.FiniteDensityPurification (toMState)
open _root_.D5.S3.Quantum.Divergence.CanonicalChannelDPI (actual_kraus_representation)
open _root_.D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction (E amp ptr ptr_amp)
open _root_.D5.S3.Quantum.Divergence.CompleteHockeyStickNonlinearCurve
open _root_.D5.S3.Quantum.Divergence.CompleteHockeyStickRefutation (amp_psd)
open _root_.D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open _root_.Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearUpper
  (singletonChannel singleton_span)
open UnitaryReconstruction.LiuWildChoiObstruction (normalizedChoi pairMatrix)
open private completeCurveValues from D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearCurve
open private posTrace_neg_psd from D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction

namespace Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearCurve

abbrev signature : Signature where
  Params := Type
  State B := B → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ B := (B → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ _ v w => v = w) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ v w => v = w ∨ w = 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Nonempty A] (N : QuantumChannel A B) (γ : ℝ) (_hγ : 1 < γ)
    (_hspan : Submodule.span ℂ
      (Set.range fun p : (Fin (Fintype.card B) × Fin (Fintype.card A)) ×
          (Fin (Fintype.card B) × Fin (Fintype.card A)) =>
        ((actual_kraus_representation N).kraus p.1)ᴴ *
          (actual_kraus_representation N).kraus p.2) = ⊤)
    (_hS : ∀ v : B → ℂ, (∀ i : A, (fun p : A × B => if p.1 = i then v p.2 else 0) ∈
      (pairMatrix (normalizedChoi N)).mulVecLin.range) → R.readout () B v 0),
    ∃ c C δ : ℝ, 0 < c ∧ 0 < C ∧ 0 < δ ∧ ∀ a : ℝ, 0 < a → a ≤ δ →
      c * a ^ 2 ≤ a - completeCurve N γ a ∧ a - completeCurve N γ a ≤ C * a ^ 2

private theorem singleton_curve (N : QuantumChannel Unit Unit) (a : ℝ) :
    completeCurve N 2 a = 0 := by
  have hset : insert 0 (completeCurveValues N 2 a) = ({0} : Set ℝ) := by
    ext y
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_iff_left_iff_imp]
    rintro ⟨R, fR, dR, ρ, σ, hρ, _, _, _, hm, _, rfl⟩
    letI := fR
    letI := dR
    have hs : ptr (amp N ρ) = ptr (amp N σ) := by rw [ptr_amp, ptr_amp, hm]
    have heq : amp N ρ = amp N σ := by
      ext ⟨r, i⟩ ⟨s, j⟩
      cases i
      cases j
      simpa [ptr, partialTraceRight] using congrFun (congrFun hs r) s
    have hd : amp N ρ - (2 : ℝ) • amp N ρ = -(amp N ρ) := by module
    rw [E, ← heq, hd]
    exact posTrace_neg_psd (amp_psd N hρ)
  rw [completeCurve, hset, csSup_singleton]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let N := singletonChannel Unit Unit
  obtain ⟨_, C, δ, _, hC, hδ, hbound⟩ :=
    h N 2 (by norm_num) (singleton_span N) (fun _ _ => Or.inr rfl)
  let a := min δ (1 / (C + 1))
  have ha : 0 < a := lt_min hδ (by positivity)
  have hupper := (hbound a ha (min_le_left _ _)).2
  rw [singleton_curve] at hupper
  have hCa : (C + 1) * a ≤ 1 := by
    simpa [mul_comm] using (le_div_iff₀ (by positivity : 0 < C + 1)).mp (min_le_right δ _)
  have hstrict : C * a < 1 := by linarith only [hCa, ha]
  nlinarith only [hupper, mul_pos ha (sub_pos.mpr hstrict)]

private theorem sensitivity : Sensitivity arena actual := by
  refine ⟨?_, fun e => nomatch e⟩
  intro i
  refine ⟨rejected, ?_, rfl, rejected_law⟩
  intro j h
  exact (h (Subsingleton.elim j i)).elim

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨Unit, 0, 1, ?_⟩
  intro h
  have he : (1 : Unit → ℂ) = 0 := (congrFun h 0).mp rfl
  exact one_ne_zero (congrFun he ())

def family : Registration arena (type_of% @quadratic_loss_near_zero) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quadratic_loss_near_zero, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

def audit : Contract.Registration.{
    _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@quadratic_loss_near_zero) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Divergence.CompleteHockeyStickNonlinearCurve.quadratic_loss_near_zero.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearCurve.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v w => v = w) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearCurve
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "domain", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end Reg.D5.S3.Quantum.Divergence.CompleteHockeyStick.NonlinearCurve
