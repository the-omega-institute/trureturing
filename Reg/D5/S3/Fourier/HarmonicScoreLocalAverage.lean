import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.HarmonicScoreLocalAverage
import Reg.Support.DependentFamily
import Batteries.Tactic.OpenPrivate

/-! Both laws observe the full cutoff score at the scaled time. -/

set_option autoImplicit false

namespace Reg.D5.S3.Fourier.HarmonicScoreLocalAverage

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.HarmonicScoreLocalAverage
open LeanInformationAudit MeasureTheory Set

noncomputable section

universe u

abbrev signature : Signature where
  Params := Σ J : Type u, Σ _ : Finset J, Σ _ : J → ℝ, Σ _ : J → ℝ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ q v => cutoffScore q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 v)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev averageArena : Arena where
  signature := signature.{u}
  Law readout := ∀ {J : Type u} (s : Finset J) (g w : J → ℝ) {X Y T r h b : ℝ}
    (_hX : 0 < X) (_hXY : X ≤ Y) (_hYT : Y ≤ T) (_hr : 0 < r) (_hh : 0 < h)
    (_hg : ∀ j ∈ s, 0 < g j) (_hw : ∀ j ∈ s, 0 ≤ w j),
    cutoffScore s g w X (b / r) - (h * X / r) * cutoffMass s g w X -
        (cutoffMass s g w Y - cutoffMass s g w X) -
        (2 * r / (h * Y)) * (cutoffMass s g w T - cutoffMass s g w Y) ≤
      (1 / h) * (∫ v in b..b + h, readout.readout () ⟨J, s, g, w, T⟩ (v / r))

abbrev pointArena : Arena where
  signature := signature.{u}
  Law readout := ∀ {J : Type u} (s : Finset J) (g w : J → ℝ) {X Y T r h b : ℝ}
    (_hX : 0 < X) (_hXY : X ≤ Y) (_hYT : Y ≤ T) (_hr : 0 < r) (_hh : 0 < h)
    (_hg : ∀ j ∈ s, 0 < g j) (_hw : ∀ j ∈ s, 0 ≤ w j),
    ∃ v ∈ Icc b (b + h),
      cutoffScore s g w X (b / r) - (h * X / r) * cutoffMass s g w X -
          (cutoffMass s g w Y - cutoffMass s g w X) -
          (2 * r / (h * Y)) * (cutoffMass s g w T - cutoffMass s g w Y) ≤
        readout.readout () ⟨J, s, g, w, T⟩ (v / r)

open private cutoff from D5.S3.Fourier.HarmonicScoreLocalAverage

private theorem rejected_average_law : ¬ averageArena.{u}.Law rejected.{u} := by
  intro law
  have h := @law (ULift.{u} Unit) ∅ (fun _ => 1) (fun _ => 1) 1 1 1 1 1 0
    zero_lt_one le_rfl le_rfl zero_lt_one zero_lt_one
    (fun _ _ => zero_lt_one) (fun _ _ => zero_le_one)
  norm_num [cutoffScore, cutoffMass, cutoff, rejected, realize,
    intervalIntegral.integral_const, smul_eq_mul] at h

private theorem rejected_point_law : ¬ pointArena.{u}.Law rejected.{u} := by
  intro law
  obtain ⟨_, _, h⟩ := @law (ULift.{u} Unit) ∅ (fun _ => 1) (fun _ => 1) 1 1 1 1 1 0
    zero_lt_one le_rfl le_rfl zero_lt_one zero_lt_one
    (fun _ _ => zero_lt_one) (fun _ _ => zero_le_one)
  norm_num [cutoffScore, cutoffMass, cutoff, rejected, realize] at h

private theorem actual_dependence : ObservationalDependence signature.{u} actual.{u} := by
  classical
  intro i
  let j : ULift.{u} Unit := ⟨()⟩
  refine ⟨⟨ULift.{u} Unit, {j}, fun _ => 1, fun _ => 1, 1⟩, 0, Real.pi / 2, ?_⟩
  norm_num [actual, realize, cutoffScore, cutoff, Real.sin_pi_div_two]

private theorem rejection_sensitivity (law : Realization signature.{u} → Prop)
    (hbad : ¬ law rejected.{u}) :
    Sensitivity { signature := signature.{u}, Law := law } actual.{u} := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, hbad⟩
    exact fun j hj => (hj (Subsingleton.elim _ _)).elim
  · intro e
    exact nomatch e

def averageEvidence :
    Registration averageArena.{u} (type_of% @cutoffScore_average_lower.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cutoffScore_average_lower.{u}, rejected, rejected_average_law⟩
  sensitivity := rejection_sensitivity _ rejected_average_law
  dependence := actual_dependence

def pointEvidence : Registration pointArena.{u} (type_of% @exists_cutoffScore_ge.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_cutoffScore_ge.{u}, rejected, rejected_point_law⟩
  sensitivity := rejection_sensitivity _ rejected_point_law
  dependence := actual_dependence

def averageAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cutoffScore_average_lower.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.HarmonicScoreLocalAverage.averageUnit
  realizationName := `Reg.D5.S3.Fourier.HarmonicScoreLocalAverage.averageEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨averageArena⟩
  objectArena := .source ⟨averageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source averageArena ⟨averageEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q v => cutoffScore q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.HarmonicScoreLocalAverage
    definition := none
    coordinates := #[0, 1, 2, 3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def pointAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_cutoffScore_ge.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.HarmonicScoreLocalAverage.pointUnit
  realizationName := `Reg.D5.S3.Fourier.HarmonicScoreLocalAverage.pointEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨pointArena⟩
  objectArena := .source ⟨pointArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pointArena ⟨pointEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q v => cutoffScore q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.HarmonicScoreLocalAverage
    definition := none
    coordinates := #[0, 1, 2, 3, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.HarmonicScoreLocalAverage
