/- SOURCE_ONLY / UNCOMPILED, 2026-10-25.
Faithful final positive-tail registration candidate. All five source
binders and all three conclusions are retained. Only the existing positive
tail tsum occurrence in the signed equation is selected. Source AST
selection, elaboration and audit admissibility have NOT been run.
The dependence witness is 0 versus exp(-2t) on the original halfline;
its genuine L1, L2 and shifted Gamma graph proofs are supplied below.
No source theorem or domain is weakened for this registration. -/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample.Symbol
open D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
open D5.S3.Weil.ZetaGamma.FormCore.SourceGammaResidualCross
open D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross.PositiveTail

private abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
private def zeroExtension (u : ℝ → ℂ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u
private def decayingInput (t : ℝ) : ℂ := (Real.exp ((-2 : ℝ) * t) : ℂ)

private theorem decayingInput_l1 : Integrable decayingInput halfline := by
  exact (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).ofReal

private theorem decayingInput_l2 : MemLp decayingInput 2 halfline := by
  apply (memLp_two_iff_integrable_sq_norm decayingInput_l1.aestronglyMeasurable).2
  have h := integrableOn_exp_mul_Ioi (by norm_num : (-4 : ℝ) < 0) 0
  convert h using 1
  funext t
  simp only [decayingInput, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), pow_two]
  rw [← Real.exp_add]
  congr 1
  ring

/- The source phase has the original positive sign +I*ξ*t.
No Fourier convention is silently changed. -/
private theorem decayingInput_fourier (ξ : ℝ) :
    unitarySourceFourier (zeroExtension decayingInput) ξ =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹ *
        (-(1 : ℂ) / ((-2 : ℂ) + Complex.I * (ξ : ℂ))) := by
  let m : ℂ := (-2 : ℂ) + Complex.I * (ξ : ℂ)
  have hm : m.re < 0 := by
    dsimp [m]
    norm_num
  have hPoint : (fun t : ℝ => sourcePhase ξ t * zeroExtension decayingInput t) =
      (Ioi (0 : ℝ)).indicator (fun t : ℝ => Complex.exp (m * (t : ℂ))) := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · simp only [zeroExtension, Set.indicator_of_mem ht, decayingInput, sourcePhase]
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      dsimp [m]
      ring
    · simp [zeroExtension, ht]
  rw [unitarySourceFourier_eq_integral, hPoint,
    integral_indicator measurableSet_Ioi, integral_exp_mul_complex_Ioi hm 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]

private theorem decayingInput_fourier_sq (ξ : ℝ) :
    ‖unitarySourceFourier (zeroExtension decayingInput) ξ‖ ^ 2 =
      ‖((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹‖ ^ 2 / (ξ ^ 2 + 4) := by
  have hm : ‖(-2 : ℂ) + Complex.I * (ξ : ℂ)‖ ^ 2 = ξ ^ 2 + 4 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
      Complex.re_ofNat, Complex.im_ofNat, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [decayingInput_fourier, norm_mul, mul_pow, norm_div, div_pow, hm]
  norm_num <;> ring

/- Reuse the actual residual L1 theorem to pay W/(ξ²+4).
Its original actual pointwise symbol is retained. -/
private theorem decayingInput_gamma_domain (c : ℝ) :
    Integrable (fun ξ : ℝ => (gammaWeight ξ + c) *
      ‖unitarySourceFourier (zeroExtension decayingInput) ξ‖ ^ 2) volume := by
  have hResidual :=
    (D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1.actual_digamma_quarter_resolvent_l1_domain_and_series
      2 (by norm_num)).1
  have hW : Integrable (fun ξ : ℝ =>
      actualBareQuarterWeight ξ / (ξ ^ 2 + 4)) volume := by
    simpa only [actualBareQuarterWeight, show (2 : ℝ) ^ 2 = 4 by norm_num] using hResidual
  have hGraph : InActualBareQuarterGraph (zeroExtension decayingInput) := by
    change Integrable (fun ξ : ℝ => actualBareQuarterWeight ξ *
      ‖unitarySourceFourier (zeroExtension decayingInput) ξ‖ ^ 2) volume
    convert hW.const_mul (‖((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹‖ ^ 2) using 1
    funext ξ
    rw [decayingInput_fourier_sq]
    ring
  have hU₁ : Integrable (zeroExtension decayingInput) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 decayingInput_l1
  have hU₂ : MemLp (zeroExtension decayingInput) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 decayingInput_l2
  exact (shifted_actual_gamma_graph_equivalence hU₁ hU₂ c).mpr hGraph

private theorem laplace_decayingInput {a : ℝ} (ha : 0 < a) :
    literalSourceLaplace a decayingInput = ((1 / (a + 2) : ℝ) : ℂ) := by
  calc
    _ = ((∫ t : ℝ, Real.exp ((-(a + 2)) * t) ∂halfline) : ℂ) := by
      unfold literalSourceLaplace
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simp only [decayingInput, ← Complex.ofReal_mul]
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
    _ = ((1 / (a + 2) : ℝ) : ℂ) := by
      change ((∫ t : ℝ in Ioi 0, Real.exp ((-(a + 2)) * t)) : ℂ) = _
      rw [integral_exp_mul_Ioi (by linarith : -(a + 2) < 0) 0]
      simp

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ u => ∑' n : ℕ, actualGammaPositiveTailTerm u n)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/- Complete original telescope, Summable and Integrable conclusions,
and full signed equation. No series/domain assertion becomes a premise. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (c : ℝ) {u : ℝ → ℂ}
    (_hu₁ : Integrable u halfline) (_hu₂ : MemLp u 2 halfline)
    (_hGamma : Integrable (fun ξ : ℝ =>
      (gammaWeight ξ + c) * ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2) volume),
    Summable (actualGammaPositiveTailTerm u) ∧
    Integrable (fun ξ : ℝ =>
      (gammaWeight ξ + c) * ‖unitarySourceFourier (fun t : ℝ => u |t|) ξ‖ ^ 2) volume ∧
    Real.sqrt Real.pi *
      ((∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (zeroExtension u) ξ‖ ^ 2) -
      (∫ ξ : ℝ, (gammaWeight ξ + c) *
        ‖unitarySourceFourier (fun t : ℝ => u |t|) ξ‖ ^ 2) / 2) =
      r.readout () c u +
        ((64 / 25 : ℝ) + (6 / 5) * ((Complex.digamma 1).re - Real.log (2 * Real.pi))) *
          Complex.normSq (literalSourceLaplace (5 / 4) u) -
        (6 / 5) * ((starRingEnd ℂ) (literalSourceLaplace (5 / 4) u) *
          literalSourceFirstLaplaceMoment (5 / 4) u).re

private theorem source_reconstruction :
    (type_of% (@actual_gamma_literal_even_difference_positive_tail_and_resonance)) ↔
      arena.Law actual := Iff.rfl

private theorem zero_gamma_domain (c : ℝ) :
    Integrable (fun ξ : ℝ => (gammaWeight ξ + c) *
      ‖unitarySourceFourier (zeroExtension (fun _ : ℝ => (0 : ℂ))) ξ‖ ^ 2) volume := by
  simp [zeroExtension, unitarySourceFourier_eq_integral]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall 0 (u := fun _ : ℝ => (0 : ℂ))
    (by simp) MemLp.zero' (zero_gamma_domain 0)).2.2
  norm_num [rejected, realize, zeroExtension, unitarySourceFourier_eq_integral,
    actualGammaPositiveTailTerm, literalSourceLaplace,
    literalSourceFirstLaplaceMoment] at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  /- Both states below satisfy the source L1, L2 and Gamma-graph premises.
  Summability is taken from the ORIGINAL theorem at this lawful witness. -/
  have hGamma := decayingInput_gamma_domain 0
  have hTail := (actual_gamma_literal_even_difference_positive_tail_and_resonance
    0 decayingInput_l1 decayingInput_l2 hGamma).1
  have h0 : 0 < actualGammaPositiveTailTerm decayingInput 0 := by
    unfold actualGammaPositiveTailTerm
    norm_num only [Nat.cast_zero, zero_add]
    rw [laplace_decayingInput (a := (9 / 4 : ℝ)) (by norm_num)]
    norm_num [Complex.normSq_apply]
  have hle : actualGammaPositiveTailTerm decayingInput 0 ≤
      ∑' n : ℕ, actualGammaPositiveTailTerm decayingInput n :=
    hTail.le_tsum 0 (fun n _ => actual_gamma_positive_tail_term_nonnegative decayingInput n)
  have hPositive : 0 < ∑' n : ℕ, actualGammaPositiveTailTerm decayingInput n := h0.trans_le hle
  refine ⟨(0 : ℝ), (fun _ : ℝ => (0 : ℂ)), decayingInput, ?_⟩
  change (∑' n : ℕ, actualGammaPositiveTailTerm (fun _ : ℝ => (0 : ℂ)) n) ≠
    ∑' n : ℕ, actualGammaPositiveTailTerm decayingInput n
  have hZero : (∑' n : ℕ, actualGammaPositiveTailTerm (fun _ : ℝ => (0 : ℂ)) n) = 0 := by
    simp [actualGammaPositiveTailTerm, literalSourceLaplace]
  rw [hZero]
  exact ne_of_lt hPositive

def familyRegistration : Registration arena
    (type_of% (@actual_gamma_literal_even_difference_positive_tail_and_resonance)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_gamma_literal_even_difference_positive_tail_and_resonance,
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

/- AST path is a SOURCE_ONLY candidate, not inspected or admitted.
Five original bodies: c,u,hu1,hu2,hGamma; two And right operands;
Eq RHS; subtraction LHS; addition LHS. Original u is state binder 1. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_gamma_literal_even_difference_positive_tail_and_resonance)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross.actual_gamma_literal_even_difference_positive_tail_and_resonance.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross.PositiveTail.familyRegistration
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
    (fun _ _ u => ∑' n : ℕ, actualGammaPositiveTailTerm u n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceActualGammaCross.PositiveTail

