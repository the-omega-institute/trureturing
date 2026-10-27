/- SOURCE_ONLY / UNCOMPILED, 2026-10-25.
Faithful registrations for the two actual bare-quarter core results.
Both original telescopes and all graph/domain/integrability/equality
conclusions are retained. The selected occurrence is the original real
quarter Hankel value; all signs and coefficients remain in the source law.
Dependence uses lawful 0 and exp(-2t) inputs, with an explicit bare-quarter
graph paid by ActualGammaResidualL1(a=2), never by the later Gamma owner.
No native/report job has run. Source reconstruction, all four slots and
sourceSelection AST paths below are uncompiled preparation candidates. -/

import Mathlib.Analysis.Real.Cardinality
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

import Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.WeightAndCorrelationReadouts

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure

private abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
private def zeroExtension (u : ℝ → ℂ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u
private def decayingInput (t : ℝ) : ℂ := (Real.exp ((-2 : ℝ) * t) : ℂ)

private theorem decayingInput_l1 : Integrable decayingInput halfline := by
  exact (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).ofReal

private theorem decayingInput_l2 : MemLp decayingInput 2 halfline := by
  apply (memLp_two_iff_integrable_sq_norm decayingInput_l1.aestronglyMeasurable).2
  have h := integrableOn_exp_mul_Ioi (by norm_num : (-4 : ℝ) < 0) 0
  change Integrable (fun t : ℝ => Real.exp ((-4 : ℝ) * t)) halfline at h
  apply h.congr
  exact Filter.Eventually.of_forall fun t => by
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
  rfl

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
private theorem decayingInput_quarter_graph :
    InActualBareQuarterGraph (zeroExtension decayingInput) := by
  have hResidual :=
    (D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1.actual_digamma_quarter_resolvent_l1_domain_and_series
      2 (by norm_num)).1
  have hW : Integrable (fun ξ : ℝ =>
      actualBareQuarterWeight ξ / (ξ ^ 2 + 4)) volume := by
    simpa only [actualBareQuarterWeight, show (2 : ℝ) ^ 2 = 4 by norm_num] using hResidual
  change Integrable (fun ξ : ℝ => actualBareQuarterWeight ξ *
    ‖unitarySourceFourier (zeroExtension decayingInput) ξ‖ ^ 2) volume
  convert hW.const_mul (‖((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹‖ ^ 2) using 1
  funext ξ
  rw [decayingInput_fourier_sq]
  ring

private theorem laplace_decayingInput {a : ℝ} (ha : 0 < a) :
    D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.literalLaplace a decayingInput = ((1 / (a + 2) : ℝ) : ℂ) := by
  calc
    _ = ((∫ t : ℝ, Real.exp ((-(a + 2)) * t) ∂halfline : ℝ) : ℂ) := by
      unfold D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.literalLaplace
      rw [← integral_complex_ofReal]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simp only [decayingInput, ← Complex.ofReal_mul]
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
    _ = ((1 / (a + 2) : ℝ) : ℂ) := by
      change ((∫ t : ℝ in Ioi 0, Real.exp ((-(a + 2)) * t) : ℝ) : ℂ) = _
      rw [integral_exp_mul_Ioi (by linarith : -(a + 2) < 0) 0]
      simp only [mul_zero, Real.exp_zero, neg_div_neg_eq]


private theorem zero_quarter_graph :
    InActualBareQuarterGraph (zeroExtension (fun _ : ℝ => (0 : ℂ))) := by
  simp [InActualBareQuarterGraph, zeroExtension, unitarySourceFourier_eq_integral]

private theorem decayingInput_hankel_positive :
    0 < (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) decayingInput).re := by
  let L : ℕ → ℝ := fun n => Complex.normSq
    (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.literalLaplace ((1 / 4 : ℝ) + n) decayingInput)
  obtain ⟨_, _, _, _, hS, hH, _, _, _⟩ :=
    D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.positive_hankel_actual_l2_domain_quarter_sharp
      (k := (1 / 4 : ℝ)) (by norm_num) decayingInput decayingInput_l2
  have hL : Summable L := hS
  have h0 : L 0 = (16 / 81 : ℝ) := by
    dsimp [L]
    norm_num only [Nat.cast_zero, add_zero]
    rw [laplace_decayingInput (a := (1 / 4 : ℝ)) (by norm_num)]
    norm_num [Complex.normSq_apply]
  have hle : L 0 ≤ ∑' n : ℕ, L n :=
    hL.le_tsum 0 (fun n _ => Complex.normSq_nonneg _)
  have hPositive : 0 < ∑' n : ℕ, L n := by
    rw [h0] at hle
    linarith
  rw [hH, ← Complex.ofReal_tsum, Complex.ofReal_re]
  exact hPositive

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ u =>
    (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/- Actual input certificates are included for BOTH states; the nonzero
input's graph also participates in the rejected-law contradictions below.
The Hankel dependence value uses frozen L2 summability/value, not a later
actual-Gamma identity. -/
private theorem lawful_dependence_witness :
    Integrable (fun _ : ℝ => (0 : ℂ)) halfline ∧
    MemLp (fun _ : ℝ => (0 : ℂ)) 2 halfline ∧
    InActualBareQuarterGraph (zeroExtension (fun _ : ℝ => (0 : ℂ))) ∧
    Integrable decayingInput halfline ∧
    MemLp decayingInput 2 halfline ∧
    InActualBareQuarterGraph (zeroExtension decayingInput) ∧
    0 < (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) decayingInput).re := by
  exact ⟨by simp, MemLp.zero', zero_quarter_graph,
    decayingInput_l1, decayingInput_l2, decayingInput_quarter_graph,
    decayingInput_hankel_positive⟩

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), decayingInput, ?_⟩
  change (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel
      (1 / 4) (fun _ : ℝ => (0 : ℂ))).re ≠
    (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) decayingInput).re
  have hZero : (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel
      (1 / 4) (fun _ : ℝ => (0 : ℂ))).re = 0 := by
    simp [D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel,
      D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.hankelIntegrand]
  rw [hZero]
  exact ne_of_lt lawful_dependence_witness.2.2.2.2.2.2


namespace EvenZeroDomainAndIdentity

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {u : ℝ → ℂ} (_hu₁ : Integrable u halfline) (_hu₂ : MemLp u 2 halfline),
    (InActualBareQuarterGraph (actualEvenZeroExtension u) ↔
      InActualBareQuarterGraph (zeroExtension u)) ∧
    (InActualBareQuarterGraph (zeroExtension u) →
      actualBareQuarterEnergy (actualEvenZeroExtension u) =
        2 * actualBareQuarterEnergy (zeroExtension u) - r.readout () () u)

private theorem source_reconstruction :
    (type_of% (@actual_bare_quarter_even_zero_domain_and_identity)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hBad := (hall (u := decayingInput) decayingInput_l1 decayingInput_l2).2
    decayingInput_quarter_graph
  have hGood := (actual_bare_quarter_even_zero_domain_and_identity
    decayingInput_l1 decayingInput_l2).2 decayingInput_quarter_graph
  change actualBareQuarterEnergy (actualEvenZeroExtension decayingInput) =
    2 * actualBareQuarterEnergy (zeroExtension decayingInput) - (-1 : ℝ) at hBad
  change actualBareQuarterEnergy (actualEvenZeroExtension decayingInput) =
    2 * actualBareQuarterEnergy (zeroExtension decayingInput) -
      (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) decayingInput).re at hGood
  linarith [decayingInput_hankel_positive]

def familyRegistration : Registration arena
    (type_of% (@actual_bare_quarter_even_zero_domain_and_identity)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_bare_quarter_even_zero_domain_and_identity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

 /- Source selection is an UNINSPECTED source-only AST candidate.
Only the original real Hankel value is selected. Source u is binder 0.
Complete original domains, implication, integrability and coefficients stay. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_bare_quarter_even_zero_domain_and_identity) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.actual_bare_quarter_even_zero_domain_and_identity.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.EvenZeroDomainAndIdentity.familyRegistration
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
    (fun _ _ u => (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end EvenZeroDomainAndIdentity

namespace ReflectedCross

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {u : ℝ → ℂ} (_hu₁ : Integrable u halfline) (_hu₂ : MemLp u 2 halfline)
    (_hU : InActualBareQuarterGraph (zeroExtension u)),
    Integrable (fun ξ : ℝ => (actualBareQuarterWeight ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)) volume ∧
    (∫ ξ : ℝ, (actualBareQuarterWeight ξ : ℂ) *
      (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
        unitarySourceFourier (zeroExtension u) (-ξ)).re =
      -(r.readout () () u) / 2

private theorem source_reconstruction :
    (type_of% (@actual_bare_quarter_reflected_cross)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hBad := (hall (u := decayingInput) decayingInput_l1 decayingInput_l2
    decayingInput_quarter_graph).2
  have hGood := (actual_bare_quarter_reflected_cross
    decayingInput_l1 decayingInput_l2 decayingInput_quarter_graph).2
  change (∫ ξ : ℝ, (actualBareQuarterWeight ξ : ℂ) *
    (starRingEnd ℂ) (unitarySourceFourier (zeroExtension decayingInput) ξ) *
      unitarySourceFourier (zeroExtension decayingInput) (-ξ)).re =
    -(-1 : ℝ) / 2 at hBad
  change (∫ ξ : ℝ, (actualBareQuarterWeight ξ : ℂ) *
    (starRingEnd ℂ) (unitarySourceFourier (zeroExtension decayingInput) ξ) *
      unitarySourceFourier (zeroExtension decayingInput) (-ξ)).re =
    -(D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) decayingInput).re / 2 at hGood
  linarith [decayingInput_hankel_positive]

def familyRegistration : Registration arena
    (type_of% (@actual_bare_quarter_reflected_cross)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_bare_quarter_reflected_cross, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

 /- Source selection is an UNINSPECTED source-only AST candidate.
Only the original real Hankel value is selected. Source u is binder 0.
Complete original domains, implication, integrability and coefficients stay. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_bare_quarter_reflected_cross) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.actual_bare_quarter_reflected_cross.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.ReflectedCross.familyRegistration
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
    (fun _ _ u => (D5.S3.Weil.ZetaGamma.FormCore.PositiveHankelL2.actualHankel (1 / 4) u).re)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end ReflectedCross

end Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure

/- Additional full-source laws: SOURCE_ONLY / UNCOMPILED. -/

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.RemainingFourierReadouts

private theorem source_extension_zero :
    zeroExtension (fun _ : ℝ => (0 : ℂ)) = (fun _ : ℝ => (0 : ℂ)) := by
  funext t
  simp [zeroExtension]

private theorem even_extension_zero :
    actualEvenZeroExtension (fun _ : ℝ => (0 : ℂ)) = (fun _ : ℝ => (0 : ℂ)) := by
  funext t
  change zeroExtension (fun _ : ℝ => (0 : ℂ)) t +
    zeroExtension (fun _ : ℝ => (0 : ℂ)) (-t) = 0
  simp [zeroExtension]

private theorem unitary_zero (ξ : ℝ) :
    unitarySourceFourier (fun _ : ℝ => (0 : ℂ)) ξ = 0 := by
  simp [unitarySourceFourier_eq_integral]

private theorem normalizer_ne_zero :
    ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)⁻¹ ≠ 0 := by
  have hS : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr hS.ne')

private theorem global_exp_fourier_square_positive :
    0 < ‖unitarySourceFourier (zeroExtension decayingInput) 0‖ ^ 2 := by
  rw [decayingInput_fourier_sq]
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr normalizer_ne_zero)) (by norm_num)

private theorem lawful_zero_input :
    Integrable (fun _ : ℝ => (0 : ℂ)) halfline ∧
    MemLp (fun _ : ℝ => (0 : ℂ)) 2 halfline ∧
    Integrable (fun _ : ℝ => (0 : ℂ)) volume ∧
    MemLp (fun _ : ℝ => (0 : ℂ)) 2 volume := by
  exact ⟨by simp, MemLp.zero', by simp, MemLp.zero'⟩

private theorem lawful_exp_input :
    Integrable decayingInput halfline ∧
    MemLp decayingInput 2 halfline ∧
    Integrable (zeroExtension decayingInput) volume ∧
    MemLp (zeroExtension decayingInput) 2 volume ∧
    0 < ‖unitarySourceFourier (zeroExtension decayingInput) 0‖ ^ 2 := by
  exact ⟨decayingInput_l1, decayingInput_l2,
    (integrable_indicator_iff measurableSet_Ioi).2 decayingInput_l1,
    (memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 decayingInput_l2,
    global_exp_fourier_square_positive⟩

private theorem exp_fourier_nonzero :
    unitarySourceFourier (zeroExtension decayingInput) 0 ≠ 0 := by
  intro hZero
  have hPositive := lawful_exp_input.2.2.2.2
  simp [hZero] at hPositive

private theorem even_exp_fourier_nonzero :
    unitarySourceFourier (actualEvenZeroExtension decayingInput) 0 ≠ 0 := by
  have hEq := actual_even_zero_fourier lawful_exp_input.1 (0 : ℝ)
  change unitarySourceFourier (actualEvenZeroExtension decayingInput) 0 =
    unitarySourceFourier (zeroExtension decayingInput) 0 +
      unitarySourceFourier (zeroExtension decayingInput) (-(0 : ℝ)) at hEq
  rw [neg_zero] at hEq
  rw [hEq]
  simpa only [two_mul] using
    (mul_ne_zero (show (2 : ℂ) ≠ 0 by norm_num) exp_fourier_nonzero)

namespace SquaredIntegrable

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => fun ξ : ℝ => ‖unitarySourceFourier f ξ‖ ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ : ℝ => (1 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {f : ℝ → ℂ} (_hf₁ : Integrable f volume) (_hf₂ : MemLp f 2 volume),
    Integrable (r.readout () () f) volume

private theorem source_reconstruction :
    (type_of% (@unitarySourceFourier_squared_integrable)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hBad : Integrable (fun _ : ℝ => (1 : ℝ)) volume :=
    hall (f := fun _ : ℝ => (0 : ℂ)) lawful_zero_input.2.2.1 lawful_zero_input.2.2.2
  have hFinite : IsFiniteMeasure (volume : Measure ℝ) :=
    (integrable_const_iff_isFiniteMeasure (μ := (volume : Measure ℝ))
      (c := (1 : ℝ)) (by norm_num)).mp hBad
  exact ((not_isFiniteMeasure_iff (μ := (volume : Measure ℝ))).2 Real.volume_univ) hFinite

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), zeroExtension decayingInput, ?_⟩
  intro h
  have hAt := congrFun h (0 : ℝ)
  change ‖unitarySourceFourier (fun _ : ℝ => (0 : ℂ)) 0‖ ^ 2 =
    ‖unitarySourceFourier (zeroExtension decayingInput) 0‖ ^ 2 at hAt
  rw [unitary_zero, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hAt
  exact (ne_of_gt lawful_exp_input.2.2.2.2) hAt.symm

def familyRegistration : Registration arena
    (type_of% (@unitarySourceFourier_squared_integrable)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@unitarySourceFourier_squared_integrable, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- UNINSPECTED AST candidate. The original f/u is state binder0.
Output is the COMPLETE selected frequency function; no frequency binder is
hoisted, fixed, manufactured or used as an extra premise. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@unitarySourceFourier_squared_integrable) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.unitarySourceFourier_squared_integrable.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.RemainingFourierReadouts.SquaredIntegrable.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => fun ξ : ℝ => ‖unitarySourceFourier f ξ‖ ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end SquaredIntegrable

namespace EvenZeroFourier

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ u => unitarySourceFourier (zeroExtension u)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ : ℝ => (-1 : ℂ)) (fun e => nomatch e)

/- Only the FIRST original RHS Fourier FUNCTION is read out.
The LHS and the literal second negative-frequency summand remain unchanged. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ {u : ℝ → ℂ} (_hu : Integrable u halfline) (ξ : ℝ),
    unitarySourceFourier (actualEvenZeroExtension u) ξ =
      r.readout () () u ξ + unitarySourceFourier (zeroExtension u) (-ξ)

private theorem source_reconstruction :
    (type_of% (@actual_even_zero_fourier)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hBad := hall (u := fun _ : ℝ => (0 : ℂ)) lawful_zero_input.1 (0 : ℝ)
  change unitarySourceFourier (actualEvenZeroExtension (fun _ : ℝ => (0 : ℂ))) 0 =
    (-1 : ℂ) + unitarySourceFourier (zeroExtension (fun _ : ℝ => (0 : ℂ))) (-(0 : ℝ)) at hBad
  rw [even_extension_zero, source_extension_zero] at hBad
  norm_num [unitary_zero] at hBad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), decayingInput, ?_⟩
  intro h
  have hAt := congrFun h (0 : ℝ)
  change unitarySourceFourier (zeroExtension (fun _ : ℝ => (0 : ℂ))) 0 =
    unitarySourceFourier (zeroExtension decayingInput) 0 at hAt
  rw [source_extension_zero, unitary_zero] at hAt
  exact exp_fourier_nonzero hAt.symm

def familyRegistration : Registration arena
    (type_of% (@actual_even_zero_fourier)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_even_zero_fourier, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- UNINSPECTED AST candidate. The original f/u is state binder0.
Output is the COMPLETE selected frequency function; no frequency binder is
hoisted, fixed, manufactured or used as an extra premise. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_even_zero_fourier) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.actual_even_zero_fourier.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.RemainingFourierReadouts.EvenZeroFourier.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => unitarySourceFourier (zeroExtension u)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end EvenZeroFourier

namespace LiteralEvenFourier

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ u => unitarySourceFourier (actualEvenZeroExtension u))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ : ℝ => (-1 : ℂ)) (fun e => nomatch e)

/- Original arbitrary u and real ξ stay unrestricted: no L1/L2 premise is
added to this literal AE-invariance theorem. Those hypotheses certify only
our chosen dependence witness, not the original source law. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (u : ℝ → ℂ) (ξ : ℝ),
    unitarySourceFourier (fun t : ℝ => u |t|) ξ = r.readout () () u ξ

private theorem source_reconstruction :
    (type_of% (@actual_literal_even_fourier)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hBad := hall (fun _ : ℝ => (0 : ℂ)) (0 : ℝ)
  change unitarySourceFourier (fun _ : ℝ => (0 : ℂ)) 0 = (-1 : ℂ) at hBad
  norm_num [unitary_zero] at hBad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), decayingInput, ?_⟩
  intro h
  have hAt := congrFun h (0 : ℝ)
  change unitarySourceFourier (actualEvenZeroExtension (fun _ : ℝ => (0 : ℂ))) 0 =
    unitarySourceFourier (actualEvenZeroExtension decayingInput) 0 at hAt
  rw [even_extension_zero, unitary_zero] at hAt
  exact even_exp_fourier_nonzero hAt.symm

def familyRegistration : Registration arena
    (type_of% (@actual_literal_even_fourier)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_literal_even_fourier, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- UNINSPECTED AST candidate. The original f/u is state binder0.
Output is the COMPLETE selected frequency function; no frequency binder is
hoisted, fixed, manufactured or used as an extra premise. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_literal_even_fourier) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.actual_literal_even_fourier.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.RemainingFourierReadouts.LiteralEvenFourier.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => unitarySourceFourier (actualEvenZeroExtension u)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end LiteralEvenFourier

end Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.RemainingFourierReadouts
