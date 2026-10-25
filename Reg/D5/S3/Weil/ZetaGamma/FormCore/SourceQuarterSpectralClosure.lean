/- SOURCE_ONLY / UNCOMPILED, 2026-10-25.
Faithful registrations for the two actual bare-quarter core results.
Both original telescopes and all graph/domain/integrability/equality
conclusions are retained. The selected occurrence is the original real
quarter Hankel value; all signs and coefficients remain in the source law.
Dependence uses lawful 0 and exp(-2t) inputs, with an explicit bare-quarter
graph paid by ActualGammaResidualL1(a=2), never by the later Gamma owner.
No native/report job has run. Source reconstruction, all four slots and
sourceSelection AST paths below are uncompiled preparation candidates. -/

import D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

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
    _ = ((∫ t : ℝ, Real.exp ((-(a + 2)) * t) ∂halfline) : ℂ) := by
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
      change ((∫ t : ℝ in Ioi 0, Real.exp ((-(a + 2)) * t)) : ℂ) = _
      rw [integral_exp_mul_Ioi (by linarith : -(a + 2) < 0) 0]
      simp


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
  rw [hH]
  simpa only [Complex.ofReal_re] using hPositive

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

/- Additional SOURCE_ONLY / UNCOMPILED full-source candidates. -/

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.BareQuarterWeightReadout

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ ξ => actualBareQuarterWeight ξ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

private theorem weight_zero : actualBareQuarterWeight 0 = 0 := by
  simp [actualBareQuarterWeight]

private theorem weight_one_lower : (64 / 17 : ℝ) ≤ actualBareQuarterWeight 1 := by
  let f : ℕ → ℝ := fun n =>
    1 / ((n : ℝ) + 1 / 4) -
      ((n : ℝ) + 1 / 4) / ((1 : ℝ) ^ 2 + ((n : ℝ) + 1 / 4) ^ 2)
  have hRaw :=
    (D5.S3.Weil.ZetaGamma.FormCore.ActualGammaResidualL1.actual_digamma_quarter_resolvent_l1_domain_and_series
      1 (by norm_num)).2.2.2.2 (1 : ℝ)
  have hS : HasSum f (actualBareQuarterWeight 1) := by
    simpa only [f, actualBareQuarterWeight] using hRaw
  have hRow (n : ℕ) : 0 ≤ f n := by
    dsimp only [f]
    have hc : 0 < ((n : ℝ) + 1 / 4) := by positivity
    have hd : 0 < (1 : ℝ) ^ 2 + ((n : ℝ) + 1 / 4) ^ 2 := by positivity
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ hd hc).2
    nlinarith
  have h0 : f 0 = (64 / 17 : ℝ) := by norm_num [f]
  have hLe : f 0 ≤ ∑' n : ℕ, f n :=
    hS.summable.le_tsum 0 (fun n _ => hRow n)
  rw [h0, hS.tsum_eq] at hLe
  exact hLe

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  change actualBareQuarterWeight 0 ≠ actualBareQuarterWeight 1
  rw [weight_zero]
  exact ne_of_lt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 64 / 17) weight_one_lower)

namespace Nonneg

abbrev arena : Arena where
  signature := signature
  Law r := ∀ ξ : ℝ, 0 ≤ r.readout () () ξ

private theorem source_reconstruction :
    (type_of% (@actual_bare_quarter_nonneg)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hBad := hall 0
  norm_num [rejected, realize] at hBad

def familyRegistration : Registration arena
    (type_of% (@actual_bare_quarter_nonneg)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_bare_quarter_nonneg, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- UNINSPECTED AST candidate. Original ξ is binder0; .body.arg selects
only W(ξ), the final RHS operand of LE.le. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_bare_quarter_nonneg) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.actual_bare_quarter_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.BareQuarterWeightReadout.Nonneg.familyRegistration
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
    (fun _ _ ξ => actualBareQuarterWeight ξ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Nonneg

namespace Even

abbrev arena : Arena where
  signature := signature
  Law r := ∀ ξ : ℝ, actualBareQuarterWeight (-ξ) = r.readout () () ξ

private theorem source_reconstruction :
    (type_of% (@actual_bare_quarter_even)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hBad : actualBareQuarterWeight (-(0 : ℝ)) = (-1 : ℝ) := hall 0
  rw [neg_zero, weight_zero] at hBad
  norm_num at hBad

def familyRegistration : Registration arena
    (type_of% (@actual_bare_quarter_even)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_bare_quarter_even, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- UNINSPECTED AST candidate. Original ξ is binder0; .body.arg selects
only W(ξ), the final RHS operand of Eq. The literal W(-ξ) LHS stays fixed. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_bare_quarter_even) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.actual_bare_quarter_even.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.BareQuarterWeightReadout.Even.familyRegistration
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
    (fun _ _ ξ => actualBareQuarterWeight ξ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Even

end Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.BareQuarterWeightReadout
