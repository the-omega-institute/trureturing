/- SOURCE_ONLY / UNCOMPILED, 2026-10-25.
Faithful full-source four-slot candidates for both actual residual-cross
public theorems. No native kernel, AST/sourceSelection, enrollment,
registration, originality, KPI or official acceptance claim is made.
The second readout is the WHOLE infinite term function, not a coefficient
extracted from the complete series. Both original source domains remain.
-/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set Filter
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross
open D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross

/- Same body as the source-private halfline. No source-private theorem or
private compiled name is referenced. All analytic owners below are public. -/
private abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))

private def decayingInput (t : ℝ) : ℂ := (Real.exp ((-2 : ℝ) * t) : ℂ)

private theorem decayingInput_l1 : Integrable decayingInput halfline := by
  exact (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).ofReal

private theorem laplace_decayingInput {a : ℝ} (ha : 0 < a) :
    literalSourceLaplace a decayingInput = ((1 / (a + 2) : ℝ) : ℂ) := by
  unfold literalSourceLaplace
  calc
    _ = ((∫ t : ℝ, Real.exp (-(a + 2) * t) ∂halfline : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        simp only [decayingInput, ← Complex.ofReal_mul]
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
    _ = _ := by
      change ((∫ t : ℝ in Ioi 0, Real.exp (-(a + 2) * t) : ℝ) : ℂ) = _
      rw [integral_exp_mul_Ioi (by linarith : -(a + 2) < 0) 0]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]

private theorem first_laplace_decayingInput {a : ℝ} (ha : 0 < a) :
    literalSourceFirstLaplaceMoment a decayingInput =
      ((1 / (a + 2) ^ 2 : ℝ) : ℂ) := by
  have hG2 : Real.Gamma 2 = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  have hmoment :
      (∫ t : ℝ in Ioi 0, t * Real.exp (-((a + 2) * t))) =
        (1 / (a + 2) ^ 2 : ℝ) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (2 : ℝ)) (r := a + 2) (by norm_num) (by linarith)
    norm_num [Real.rpow_two, hG2, div_pow] at h
    simpa only [one_div] using h
  unfold literalSourceFirstLaplaceMoment
  calc
    _ = ((∫ t : ℝ, t * Real.exp (-((a + 2) * t)) ∂halfline : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        simp only [decayingInput, Complex.ofReal_mul]
        have he : Real.exp (-a * t) * Real.exp ((-2 : ℝ) * t) =
            Real.exp (-((a + 2) * t)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [mul_assoc, ← Complex.ofReal_mul, he]
    _ = _ := by
      change ((∫ t : ℝ in Ioi 0, t * Real.exp (-((a + 2) * t)) : ℝ) : ℂ) = _
      rw [hmoment]

private theorem layer_zero (a c : ℝ) :
    actualResidualLayerCrossValue a c (fun _ : ℝ => (0 : ℂ)) = 0 := by
  simp [actualResidualLayerCrossValue, literalSourceLaplace,
    literalSourceFirstLaplaceMoment]

private theorem layer_decaying_one :
    actualResidualLayerCrossValue 1 1 decayingInput = (1 / 108 : ℝ) := by
  rw [actualResidualLayerCrossValue, if_pos rfl]
  simp only [laplace_decayingInput (by norm_num : (0 : ℝ) < 1),
    first_laplace_decayingInput (by norm_num : (0 : ℝ) < 1)]
  norm_num [Complex.normSq_apply, map_div₀, map_ofNat]

private theorem layer_decaying_five_quarters :
    actualResidualLayerCrossValue (5 / 4) (5 / 4) decayingInput =
      (192 / 54925 : ℝ) := by
  rw [actualResidualLayerCrossValue, if_pos rfl]
  simp only [laplace_decayingInput (by norm_num : (0 : ℝ) < 5 / 4),
    first_laplace_decayingInput (by norm_num : (0 : ℝ) < 5 / 4)]
  norm_num [Complex.normSq_apply, map_div₀, map_ofNat]

/- Legal source witnesses are recorded with their actual L1 proofs.
State itself remains the whole original function space, not this pair. -/
private theorem layer_admissible_separation :
    ∃ (a c : ℝ) (u₀ u₁ : ℝ → ℂ),
      0 < a ∧ 0 < c ∧ Integrable u₀ halfline ∧ Integrable u₁ halfline ∧
        actualResidualLayerCrossValue a c u₀ ≠
          actualResidualLayerCrossValue a c u₁ := by
  refine ⟨1, 1, (fun _ : ℝ => (0 : ℂ)), decayingInput,
    by norm_num, by norm_num, by simp, decayingInput_l1, ?_⟩
  rw [layer_zero, layer_decaying_one]
  norm_num

private theorem series_admissible_separation :
    ∃ (a : ℝ) (u₀ u₁ : ℝ → ℂ),
      0 < a ∧ Integrable u₀ halfline ∧ Integrable u₁ halfline ∧
        (fun n : ℕ => actualResidualLayerCrossValue a ((n : ℝ) + 1 / 4) u₀) ≠
          (fun n : ℕ => actualResidualLayerCrossValue a ((n : ℝ) + 1 / 4) u₁) := by
  refine ⟨5 / 4, (fun _ : ℝ => (0 : ℂ)), decayingInput,
    by norm_num, by simp, decayingInput_l1, ?_⟩
  intro heq
  have h₁ : actualResidualLayerCrossValue (5 / 4) (5 / 4)
        (fun _ : ℝ => (0 : ℂ)) =
      actualResidualLayerCrossValue (5 / 4) (5 / 4) decayingInput := by
    simpa only [Nat.cast_one,
      show (1 : ℝ) + 1 / 4 = 5 / 4 by norm_num] using congrFun heq 1
  rw [layer_zero, layer_decaying_five_quarters] at h₁
  norm_num at h₁

namespace Layer

abbrev signature : Signature where
  Params := (_ : ℝ) × ℝ
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p u => actualResidualLayerCrossValue p.1 p.2 u)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/- Every original binder, source domain and equality remains.
In particular c=a and c≠a are retained inside the original public readout. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {a c : ℝ} (_ha : 0 < a) (_hc : 0 < c) {u : ℝ → ℂ}
    (_hu : Integrable u halfline),
    (∫ ξ : ℝ, (actualResidualLayer a c ξ : ℂ) *
      actualSourceSpectralCross u ξ).re = r.readout () ⟨a, c⟩ u

private theorem source_reconstruction :
    (type_of% (@actual_residual_layer_cross_value)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := hall (a := 1) (c := 1) (by norm_num) (by norm_num)
    (u := fun _ : ℝ => (0 : ℂ)) (by simp)
  change (∫ ξ : ℝ, (actualResidualLayer 1 1 ξ : ℂ) *
    actualSourceSpectralCross (fun _ : ℝ => (0 : ℂ)) ξ).re = (-1 : ℝ) at hbad
  have htrue := actual_residual_layer_cross_value (a := 1) (c := 1)
    (by norm_num) (by norm_num) (u := fun _ : ℝ => (0 : ℂ)) (by simp)
  rw [htrue, layer_zero] at hbad
  norm_num at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨a, c, u₀, u₁, _ha, _hc, _hu₀, _hu₁, hsep⟩ :=
    layer_admissible_separation
  exact ⟨⟨a, c⟩, u₀, u₁, hsep⟩

def familyRegistration : Registration arena
    (type_of% (@actual_residual_layer_cross_value)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_residual_layer_cross_value, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- SOURCE_ONLY proposed raw path, not AST-verified.
Original binders: a=0,c=1,ha=2,hc=3,u=4,hu=5. Select the WHOLE Eq RHS.
Parameter packing follows the existing two-coordinate dependent family. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_residual_layer_cross_value) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross.actual_residual_layer_cross_value.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross.Layer.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p u => actualResidualLayerCrossValue p.1 p.2 u)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Layer

namespace CompleteSeries

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a u => fun n : ℕ =>
    actualResidualLayerCrossValue a ((n : ℝ) + 1 / 4) u)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ : ℕ => (1 : ℝ))
    (fun e => nomatch e)

/- The original actual complex L1 conjunct, whole HasSum, literal Fourier
cross, limit integral and every source hypothesis are all retained. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {a : ℝ} (_ha : 0 < a) {u : ℝ → ℂ}
    (_hu : Integrable u halfline),
    Integrable (fun ξ : ℝ =>
      ((actualBareQuarterWeight ξ / (ξ ^ 2 + a ^ 2) : ℝ) : ℂ) *
        actualSourceSpectralCross u ξ) volume ∧
    HasSum (r.readout () a u)
      (∫ ξ : ℝ,
        ((actualBareQuarterWeight ξ / (ξ ^ 2 + a ^ 2) : ℝ) : ℂ) *
          actualSourceSpectralCross u ξ).re

private theorem source_reconstruction :
    (type_of% (@actual_residual_reflected_cross_complete_series)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall (a := 1) (by norm_num)
    (u := fun _ : ℝ => (0 : ℂ)) (by simp)).2
  have hs : Summable (fun _ : ℕ => (1 : ℝ)) := hbad.summable
  exact one_ne_zero ((summable_const_iff (1 : ℝ)).mp hs)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨a, u₀, u₁, _ha, _hu₀, _hu₁, hsep⟩ :=
    series_admissible_separation
  exact ⟨a, u₀, u₁, hsep⟩

def familyRegistration : Registration arena
    (type_of% (@actual_residual_reflected_cross_complete_series)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_residual_reflected_cross_complete_series,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- SOURCE_ONLY proposed raw path, not AST-verified.
Original binders: a=0,ha=1,u=2,hu=3. Select the WHOLE first HasSum
operand after the right And branch. Pinned HasSum has a final default
SummationFilter argument, so reaching its term function takes fn/fn/arg.
This is lexical u-state binding; functionOperand mode is deliberately false. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_residual_reflected_cross_complete_series)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross.actual_residual_reflected_cross_complete_series.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross.CompleteSeries.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a u => fun n : ℕ =>
    actualResidualLayerCrossValue a ((n : ℝ) + 1 / 4) u)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end CompleteSeries

end Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross
