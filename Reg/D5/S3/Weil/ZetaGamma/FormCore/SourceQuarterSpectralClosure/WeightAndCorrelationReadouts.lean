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

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure
open LeanInformationAudit


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

/- SOURCE_ONLY / UNCOMPILED. Insert after `end Even` and before the
closing BareQuarterWeightReadout namespace in the existing Reg owner.
This reuses that owner's signature, actual, and private actual_dependence. -/
namespace Measurability

open scoped Cardinal

private theorem exists_nonmeasurable_real_set :
    ∃ s : Set ℝ, ¬ MeasurableSet s := by
  classical
  by_contra! hall
  have hcount : #(MeasurableSpace.countableGeneratingSet ℝ) ≤ ℵ₀ :=
    (MeasurableSpace.countable_countableGeneratingSet (α := ℝ)).le_aleph0
  have hbound : #{s : Set ℝ // MeasurableSet s} ≤ 𝔠 := by
    have hg := MeasurableSpace.cardinal_measurableSet_le_continuum
      (s := MeasurableSpace.countableGeneratingSet ℝ)
      (hcount.trans Cardinal.aleph0_le_continuum)
    rw [MeasurableSpace.generateFrom_countableGeneratingSet] at hg
    exact hg
  let f : Set ℝ → {s : Set ℝ // MeasurableSet s} := fun s => ⟨s, hall s⟩
  have hf : Function.Injective f := by
    intro s t hst
    exact congrArg Subtype.val hst
  have hlarge : #(Set ℝ) ≤ 𝔠 :=
    (Cardinal.mk_le_of_injective hf).trans hbound
  have hpower : (2 : Cardinal) ^ 𝔠 ≤ 𝔠 := by
    simpa only [Cardinal.mk_set, Cardinal.mk_real] using hlarge
  exact (not_le_of_gt (Cardinal.cantor 𝔠)) hpower

private theorem exists_nonmeasurable_real_function :
    ∃ f : ℝ → ℝ, ¬ Measurable f := by
  classical
  obtain ⟨s, hs⟩ := exists_nonmeasurable_real_set
  refine ⟨s.indicator (fun _ => (1 : ℝ)), ?_⟩
  intro hf
  exact hs ((measurable_indicator_const_iff (1 : ℝ)).1 hf)

private def badFunction : ℝ → ℝ :=
  Classical.choose exists_nonmeasurable_real_function

private theorem badFunction_not_measurable : ¬ Measurable badFunction :=
  Classical.choose_spec exists_nonmeasurable_real_function

def rejected : Realization signature :=
  realize signature (fun _ _ => badFunction) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := Measurable (r.readout () ())

private theorem source_reconstruction :
    (type_of% (@actual_bare_quarter_measurable)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  change ¬ Measurable badFunction
  exact badFunction_not_measurable

def familyRegistration : Registration arena
    (type_of% (@actual_bare_quarter_measurable)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_bare_quarter_measurable, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- UNCOMPILED AST candidate: the final argument of the unchanged closed
Measurable W is W itself. The selector introduces state only to its
observation model; it adds no binder or premise to the source theorem. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_bare_quarter_measurable) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.actual_bare_quarter_measurable.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.BareQuarterWeightReadout.Measurability.familyRegistration
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
      path := #["arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end Measurability

end Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.BareQuarterWeightReadout

/- Additional full-source laws: SOURCE_ONLY / UNCOMPILED. -/

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.RemainingCorrelationCandidates

/- Reconstruct identical source-private definitions by their bodies. No
source-private compiled name, proof, additional source premise or graph
assumption is imported. The actual readout is the entire original lambda. -/
private abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
private def zeroExtension (u : ℝ → ℂ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u

private def spectralCross (u : ℝ → ℂ) : ℝ → ℂ := fun ξ =>
  (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
    unitarySourceFourier (zeroExtension u) (-ξ)

/- These L1, L2 and exact plus-phase Fourier witnesses are the same legal
0/exp(-2t) mechanism already prepared in this Reg owner's core candidates.
No Gamma graph, later actual-Gamma theorem or target conclusion is used. -/
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

private theorem decayingInput_fourier_zero_ne :
    unitarySourceFourier (zeroExtension decayingInput) 0 ≠ 0 := by
  have hs : (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2
      (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)).ne'
  rw [decayingInput_fourier]
  apply mul_ne_zero (inv_ne_zero hs)
  norm_num

private theorem spectralCross_zero (ξ : ℝ) :
    spectralCross (fun _ : ℝ => (0 : ℂ)) ξ = 0 := by
  simp [spectralCross, zeroExtension, unitarySourceFourier_eq_integral]

private theorem spectralCross_decaying_zero_ne : spectralCross decayingInput 0 ≠ 0 := by
  change (starRingEnd ℂ) (unitarySourceFourier (zeroExtension decayingInput) 0) *
    unitarySourceFourier (zeroExtension decayingInput) (-0) ≠ 0
  simp only [neg_zero]
  exact mul_ne_zero (by
    simpa only [starRingEnd_apply, star_ne_zero] using decayingInput_fourier_zero_ne)
    decayingInput_fourier_zero_ne

/- Both states are legal under EVERY original source hypothesis. The
separation is of complete functions; evaluation at xi=0 only proves their
inequality and does not replace the selected original function readout. -/
private theorem admissible_cross_separation :
    Integrable (fun _ : ℝ => (0 : ℂ)) halfline ∧
    MemLp (fun _ : ℝ => (0 : ℂ)) 2 halfline ∧
    Integrable decayingInput halfline ∧ MemLp decayingInput 2 halfline ∧
    spectralCross (fun _ : ℝ => (0 : ℂ)) ≠ spectralCross decayingInput := by
  refine ⟨by simp, MemLp.zero', decayingInput_l1, decayingInput_l2, ?_⟩
  intro heq
  have hzero := congrFun heq (0 : ℝ)
  rw [spectralCross_zero] at hzero
  exact spectralCross_decaying_zero_ne hzero.symm

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
  realize signature (fun _ _ u => spectralCross u) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ : ℝ => (0 : ℂ)), decayingInput, ?_⟩
  change spectralCross (fun _ : ℝ => (0 : ℂ)) ≠ spectralCross decayingInput
  exact admissible_cross_separation.2.2.2.2

namespace UnweightedIntegrable

/- A nonzero constant over all of R is genuinely nonintegrable. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => (1 : ℂ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {u : ℝ → ℂ} (_hu₁ : Integrable u halfline) (_hu₂ : MemLp u 2 halfline),
    Integrable (r.readout () () u) volume

private theorem source_reconstruction :
    (type_of% (@actual_unweighted_reflected_cross_integrable)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := hall (u := fun _ : ℝ => (0 : ℂ)) (by simp) MemLp.zero'
  change Integrable (fun _ : ℝ => (1 : ℂ)) volume at hbad
  have hFinite : IsFiniteMeasure (volume : Measure ℝ) :=
    (integrable_const_iff_isFiniteMeasure (by norm_num : (1 : ℂ) ≠ 0)).mp hbad
  have hfin := @measure_lt_top ℝ _ (volume : Measure ℝ) hFinite univ
  simpa using hfin

def familyRegistration : Registration arena
    (type_of% (@actual_unweighted_reflected_cross_integrable)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_unweighted_reflected_cross_integrable, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- SOURCE_ONLY raw selector proposal; not elaborated/AST-verified.
Cross all three original binders u=0,hu1=1,hu2=2. Integrable applies
its original function before its final measure, so select fn/arg.
The complete function is selected OUTSIDE its xi-lambda: Output=R->C,
stateBinder=0 is original u, and functionOperand is deliberately false. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_unweighted_reflected_cross_integrable) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.actual_unweighted_reflected_cross_integrable.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.RemainingCorrelationCandidates.UnweightedIntegrable.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => spectralCross u)
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

end UnweightedIntegrable

namespace ConstantRealCrossZero

/- This compactly supported L1 counter-readout has ACTUAL real integral 1.
It avoids relying on totalization of a divergent Bochner integral. -/
private def rejectedIntegrand : ℝ → ℂ :=
  (Ioc (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℂ))

def rejected : Realization signature :=
  realize signature (fun _ _ _ => rejectedIntegrand) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {u : ℝ → ℂ} (_hu₁ : Integrable u halfline) (_hu₂ : MemLp u 2 halfline),
    (∫ ξ : ℝ, r.readout () () u ξ).re = 0

private theorem source_reconstruction :
    (type_of% (@actual_constant_reflected_cross_re_zero)) ↔
      arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := hall (u := fun _ : ℝ => (0 : ℂ)) (by simp) MemLp.zero'
  change (∫ ξ : ℝ, (Ioc (0 : ℝ) 1).indicator (fun _ : ℝ => (1 : ℂ)) ξ).re = 0 at hbad
  rw [integral_indicator measurableSet_Ioc] at hbad
  norm_num at hbad

def familyRegistration : Registration arena
    (type_of% (@actual_constant_reflected_cross_re_zero)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_constant_reflected_cross_re_zero, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- SOURCE_ONLY raw selector proposal; not elaborated/AST-verified.
Cross u/hu1/hu2, then Eq's original LHS (fn/arg), Complex.re's argument,
and integral's final integrand argument (arg,arg). Select the WHOLE lambda.
The source's scalar RHS 0, integration, and .re all remain in the Law. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_constant_reflected_cross_re_zero) (Realization signature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.actual_constant_reflected_cross_re_zero.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.RemainingCorrelationCandidates.ConstantRealCrossZero.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ u => spectralCross u)
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
      path := #["body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end ConstantRealCrossZero

end Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceQuarterSpectralClosure.RemainingCorrelationCandidates
