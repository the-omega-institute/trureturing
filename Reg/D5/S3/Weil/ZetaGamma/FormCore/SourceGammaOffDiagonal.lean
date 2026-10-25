/- Faithful original-domain registrations for all six public Fourier-kernel
suppliers. Native proof and current source binding are checked separately.
Each law preserves the complete original source telescope, integrability
conjuncts, physical/spectral integrals, and the signed resonance expression.
Each selected occurrence is the WHOLE final equation RHS. Infinite parameter
and state domains are retained; no per-fiber dependence claim is imposed.
-/

import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
import Reg.Support.DependentFamily
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
open D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open LeanInformationAudit

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal


abbrev inverseKernelSignature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

namespace ResolventInverse

def actual : Realization inverseKernelSignature :=
  realize inverseKernelSignature (fun _ a z => actualResolventKernel a z)
    (fun e => nomatch e)

def rejected : Realization inverseKernelSignature :=
  realize inverseKernelSignature (fun _ _ _ => (-1 : ℂ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := inverseKernelSignature
  Law r := ∀ {a : ℝ} (_ha : 0 < a) (z : ℝ),
    Integrable (actualResolventSymbol a) volume ∧
      actualL1MultiplierKernel (actualResolventSymbol a) z =
        r.readout () a z

private theorem source_reconstruction :
    (type_of% (@actual_resolvent_inverse_kernel)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall (a := 1) (by norm_num) 0).2
  rw [(actual_resolvent_inverse_kernel (a := 1) (by norm_num) 0).2] at hbad
  norm_num [rejected, realize, actualResolventKernel] at hbad

private theorem actual_dependence :
    ObservationalDependence inverseKernelSignature actual := by
  intro i
  refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
  change actualResolventKernel 1 0 ≠ actualResolventKernel 1 1
  intro heq
  have hre := congrArg Complex.re heq
  have hexp : Real.exp (-1 : ℝ) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  norm_num [actualResolventKernel, Complex.div_re] at hre
  have hexpre := Complex.exp_ofReal_re (-1 : ℝ)
  simp only [Complex.ofReal_neg, Complex.ofReal_one] at hexpre
  rw [hexpre] at hre
  linarith

def familyRegistration : Registration arena
    (type_of% (@actual_resolvent_inverse_kernel)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_resolvent_inverse_kernel, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Full original binders: a, ha, z. Only the equation RHS is selected;
a is genuine parameter coordinate 0, and z is original state binder 2. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_resolvent_inverse_kernel)
    (Realization inverseKernelSignature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.actual_resolvent_inverse_kernel.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.ResolventInverse.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize inverseKernelSignature
    (fun _ a z => actualResolventKernel a z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end ResolventInverse

namespace ResonantInverse

def actual : Realization inverseKernelSignature :=
  realize inverseKernelSignature (fun _ a z =>
    ((Real.exp (-a * |z|) * (1 - a * |z|) / (4 * a ^ 2) : ℝ) : ℂ))
    (fun e => nomatch e)

def rejected : Realization inverseKernelSignature :=
  realize inverseKernelSignature (fun _ _ _ => (-1 : ℂ))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := inverseKernelSignature
  Law r := ∀ {a : ℝ} (_ha : 0 < a) (z : ℝ),
    Integrable (actualResonantSymbol a) volume ∧
      actualL1MultiplierKernel (actualResonantSymbol a) z =
        r.readout () a z

private theorem source_reconstruction :
    (type_of% (@actual_resonant_inverse_kernel)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall (a := 1) (by norm_num) 0).2
  rw [(actual_resonant_inverse_kernel (a := 1) (by norm_num) 0).2] at hbad
  norm_num [rejected, realize] at hbad

private theorem actual_dependence :
    ObservationalDependence inverseKernelSignature actual := by
  intro i
  refine ⟨(1 : ℝ), (0 : ℝ), (1 : ℝ), ?_⟩
  change
    ((Real.exp (-(1 : ℝ) * |(0 : ℝ)|) *
      (1 - (1 : ℝ) * |(0 : ℝ)|) / (4 * (1 : ℝ) ^ 2) : ℝ) : ℂ) ≠
    ((Real.exp (-(1 : ℝ) * |(1 : ℝ)|) *
      (1 - (1 : ℝ) * |(1 : ℝ)|) / (4 * (1 : ℝ) ^ 2) : ℝ) : ℂ)
  norm_num

def familyRegistration : Registration arena
    (type_of% (@actual_resonant_inverse_kernel)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_resonant_inverse_kernel, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Retains the signed original exp(-a|z|)*(1-a|z|)/(4a²) scalar.
No absolute value or positivity law replaces the actual resonance kernel. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_resonant_inverse_kernel)
    (Realization inverseKernelSignature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.actual_resonant_inverse_kernel.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.ResonantInverse.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize inverseKernelSignature (fun _ a z =>
    ((Real.exp (-a * |z|) * (1 - a * |z|) / (4 * a ^ 2) : ℝ) : ℂ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end ResonantInverse



/- Definition bodies match the original private literal source domain.
They are transparent local notation, not a different mathematical carrier. -/
private abbrev halfline : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
private def zeroExtension (u : ℝ → ℂ) : ℝ → ℂ := (Ioi (0 : ℝ)).indicator u

private def decayingInput (t : ℝ) : ℂ := (Real.exp ((-2 : ℝ) * t) : ℂ)

private theorem decayingInput_l1 : Integrable decayingInput halfline := by
  exact (integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0).ofReal

private theorem laplace_decayingInput :
    (∫ t : ℝ, (Real.exp (-(1 : ℝ) * t) : ℂ) * decayingInput t ∂halfline) =
      (1 / 3 : ℂ) := by
  have hexp : (∫ t : ℝ in Ioi 0, Real.exp ((-3 : ℝ) * t)) = (1 / 3 : ℝ) := by
    rw [integral_exp_mul_Ioi (by norm_num : (-3 : ℝ) < 0) 0]
    norm_num
  calc
    _ = ∫ t : ℝ, (Real.exp ((-3 : ℝ) * t) : ℂ) ∂halfline := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simp only [decayingInput, ← Complex.ofReal_mul]
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
    _ = Complex.ofReal (∫ t : ℝ, Real.exp ((-3 : ℝ) * t) ∂halfline) :=
      integral_complex_ofReal
    _ = (1 / 3 : ℂ) := by
      change Complex.ofReal (∫ t : ℝ in Ioi 0, Real.exp ((-3 : ℝ) * t)) = _
      rw [hexp]
      norm_num

private theorem first_laplace_decayingInput :
    (∫ t : ℝ, (t : ℂ) * (Real.exp (-(1 : ℝ) * t) : ℂ) *
      decayingInput t ∂halfline) = (1 / 9 : ℂ) := by
  have hG2 : Real.Gamma 2 = 1 := by
    simpa using Real.Gamma_nat_eq_factorial 1
  have hmoment :
      (∫ t : ℝ in Ioi 0, t * Real.exp (-((3 : ℝ) * t))) = (1 / 9 : ℝ) := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
      (a := (2 : ℝ)) (r := (3 : ℝ)) (by norm_num) (by norm_num)
    norm_num [Real.rpow_two, hG2] at h
    exact h
  calc
    _ = ∫ t : ℝ, ((t * Real.exp (-((3 : ℝ) * t)) : ℝ) : ℂ) ∂halfline := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by
        simp only [decayingInput, Complex.ofReal_mul]
        have he : Real.exp (-(1 : ℝ) * t) * Real.exp ((-2 : ℝ) * t) =
            Real.exp (-((3 : ℝ) * t)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [mul_assoc, ← Complex.ofReal_mul, he]
    _ = Complex.ofReal (∫ t : ℝ, t * Real.exp (-((3 : ℝ) * t)) ∂halfline) :=
      integral_complex_ofReal
    _ = (1 / 9 : ℂ) := by
      change Complex.ofReal (∫ t : ℝ in Ioi 0, t * Real.exp (-((3 : ℝ) * t))) = _
      rw [hmoment]
      norm_num

abbrev generalCrossSignature : Signature where
  Params := ℝ → ℂ
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev rateCrossSignature : Signature where
  Params := ℝ
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev momentSignature : Signature where
  Params := ℝ
  State _ := ℝ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

namespace GeneralCross

def actual : Realization generalCrossSignature :=
  realize generalCrossSignature (fun _ p u => ∫ z : ℝ × ℝ,
      actualL1MultiplierKernel p (z.1 + z.2) *
        ((starRingEnd ℂ) (u z.1) * u z.2) ∂halfline.prod halfline) (fun e => nomatch e)

def rejected : Realization generalCrossSignature :=
  realize generalCrossSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := generalCrossSignature
  Law r := ∀ {p u : ℝ → ℂ} (_hp : Integrable p volume) (_hu : Integrable u halfline),
    Integrable (fun ξ : ℝ => p ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)) volume ∧
    Integrable (fun z : ℝ × ℝ =>
      actualL1MultiplierKernel p (z.1 + z.2) *
        ((starRingEnd ℂ) (u z.1) * u z.2)) (halfline.prod halfline) ∧
    (∫ ξ : ℝ, p ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)) = r.readout () p u

private theorem source_reconstruction :
    (type_of% (@actual_l1_reflected_unitary_cross_kernel)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hp := (actual_resolvent_inverse_kernel (a := 1) (by norm_num) 0).1
  have hbad := (hall (p := actualResolventSymbol 1) (u := fun _ => (0 : ℂ))
    hp (by simp)).2.2
  norm_num [rejected, realize, zeroExtension, unitarySourceFourier_eq_integral] at hbad

private theorem actual_dependence : ObservationalDependence generalCrossSignature actual := by
  intro i
  refine ⟨actualResolventSymbol 1, (fun _ : ℝ => (0 : ℂ)), decayingInput, ?_⟩
  have hp := (actual_resolvent_inverse_kernel (a := 1) (by norm_num) 0).1
  have hcross := (actual_l1_reflected_unitary_cross_kernel hp decayingInput_l1).2.2
  have hsquare := (actual_resolvent_reflected_cross_laplace_square
    (a := 1) (by norm_num) decayingInput_l1).2.2
  have hv : (∫ z : ℝ × ℝ,
      actualL1MultiplierKernel (actualResolventSymbol 1) (z.1 + z.2) *
        ((starRingEnd ℂ) (decayingInput z.1) * decayingInput z.2) ∂halfline.prod halfline) = (1 / 18 : ℂ) := by
    rw [← hcross, hsquare, laplace_decayingInput]
    norm_num [Complex.normSq_apply]
  dsimp only [actual, realize]
  change (∫ z : ℝ × ℝ,
    actualL1MultiplierKernel (actualResolventSymbol 1) (z.1 + z.2) *
      ((starRingEnd ℂ) ((0 : ℂ)) * (0 : ℂ)) ∂halfline.prod halfline) ≠ _
  simp only [map_zero, zero_mul, mul_zero, integral_zero]
  rw [hv]
  norm_num

def familyRegistration : Registration arena (type_of% (@actual_l1_reflected_unitary_cross_kernel)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_l1_reflected_unitary_cross_kernel, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Original telescope has four binders. The selected observation is the
whole final equation RHS, preserving every other original source clause.
The raw path is a SOURCE_ONLY proposal pending actual scoped binding. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_l1_reflected_unitary_cross_kernel) (Realization generalCrossSignature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.actual_l1_reflected_unitary_cross_kernel.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.GeneralCross.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize generalCrossSignature (fun _ p u => ∫ z : ℝ × ℝ,
      actualL1MultiplierKernel p (z.1 + z.2) *
        ((starRingEnd ℂ) (u z.1) * u z.2) ∂halfline.prod halfline)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end GeneralCross

namespace ResolventLaplace

def actual : Realization rateCrossSignature :=
  realize rateCrossSignature (fun _ a u => (Complex.normSq (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline) : ℂ) /
      ((2 * a : ℝ) : ℂ)) (fun e => nomatch e)

def rejected : Realization rateCrossSignature :=
  realize rateCrossSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := rateCrossSignature
  Law r := ∀ {a : ℝ} (_ha : 0 < a) {u : ℝ → ℂ} (_hu : Integrable u halfline),
    Integrable (fun t : ℝ => (Real.exp (-a * t) : ℂ) * u t) halfline ∧
    Integrable (fun ξ : ℝ => actualResolventSymbol a ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)) volume ∧
    (∫ ξ : ℝ, actualResolventSymbol a ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)) = r.readout () a u

private theorem source_reconstruction :
    (type_of% (@actual_resolvent_reflected_cross_laplace_square)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall (a := 1) (by norm_num) (u := fun _ => (0 : ℂ)) (by simp)).2.2
  norm_num [rejected, realize, zeroExtension, unitarySourceFourier_eq_integral] at hbad

private theorem actual_dependence : ObservationalDependence rateCrossSignature actual := by
  intro i
  refine ⟨(1 : ℝ), (fun _ : ℝ => (0 : ℂ)), decayingInput, ?_⟩
  change
    (Complex.normSq (∫ t : ℝ, (Real.exp (-(1 : ℝ) * t) : ℂ) * (0 : ℂ) ∂halfline) : ℂ) /
      ((2 * (1 : ℝ) : ℝ) : ℂ) ≠
    (Complex.normSq (∫ t : ℝ, (Real.exp (-(1 : ℝ) * t) : ℂ) * decayingInput t ∂halfline) : ℂ) /
      ((2 * (1 : ℝ) : ℝ) : ℂ)
  rw [laplace_decayingInput]
  norm_num [Complex.normSq_apply]

def familyRegistration : Registration arena (type_of% (@actual_resolvent_reflected_cross_laplace_square)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_resolvent_reflected_cross_laplace_square, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Original telescope has four binders. The selected observation is the
whole final equation RHS, preserving every other original source clause.
The raw path is a SOURCE_ONLY proposal pending actual scoped binding. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_resolvent_reflected_cross_laplace_square) (Realization rateCrossSignature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.actual_resolvent_reflected_cross_laplace_square.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.ResolventLaplace.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rateCrossSignature (fun _ a u => (Complex.normSq (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline) : ℂ) /
      ((2 * a : ℝ) : ℂ))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end ResolventLaplace

namespace ResonantPhysical

def actual : Realization rateCrossSignature :=
  realize rateCrossSignature (fun _ a u => ∫ z : ℝ × ℝ,
      ((Real.exp (-a * (z.1 + z.2)) * (1 - a * (z.1 + z.2)) /
          (4 * a ^ 2) : ℝ) : ℂ) *
        ((starRingEnd ℂ) (u z.1) * u z.2) ∂halfline.prod halfline) (fun e => nomatch e)

def rejected : Realization rateCrossSignature :=
  realize rateCrossSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := rateCrossSignature
  Law r := ∀ {a : ℝ} (_ha : 0 < a) {u : ℝ → ℂ} (_hu : Integrable u halfline),
    Integrable (fun ξ : ℝ => actualResonantSymbol a ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)) volume ∧
    (∫ ξ : ℝ, actualResonantSymbol a ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)) = r.readout () a u

private theorem source_reconstruction :
    (type_of% (@actual_resonant_reflected_cross_kernel)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall (a := 1) (by norm_num) (u := fun _ => (0 : ℂ)) (by simp)).2
  norm_num [rejected, realize, zeroExtension, unitarySourceFourier_eq_integral] at hbad

private theorem actual_dependence : ObservationalDependence rateCrossSignature actual := by
  intro i
  refine ⟨(1 : ℝ), (fun _ : ℝ => (0 : ℂ)), decayingInput, ?_⟩
  have hcross := (actual_resonant_reflected_cross_kernel
    (a := 1) (by norm_num) decayingInput_l1).2
  have hmoment := (actual_resonant_reflected_cross_laplace_moment
    (a := 1) (by norm_num) decayingInput_l1).2
  rw [laplace_decayingInput, first_laplace_decayingInput] at hmoment
  have hv : (∫ z : ℝ × ℝ,
      ((Real.exp (-(1 : ℝ) * (z.1 + z.2)) * (1 - (1 : ℝ) * (z.1 + z.2)) /
          (4 * (1 : ℝ) ^ 2) : ℝ) : ℂ) *
        ((starRingEnd ℂ) (decayingInput z.1) * decayingInput z.2) ∂halfline.prod halfline).re = (1 / 108 : ℝ) := by
    rw [← hcross]
    norm_num [Complex.normSq_apply] at hmoment ⊢
    exact hmoment
  intro heq
  dsimp only [actual, realize] at heq
  have hre := congrArg Complex.re heq
  change (∫ z : ℝ × ℝ,
    ((Real.exp (-(1 : ℝ) * (z.1 + z.2)) *
      (1 - (1 : ℝ) * (z.1 + z.2)) / (4 * (1 : ℝ) ^ 2) : ℝ) : ℂ) *
      ((starRingEnd ℂ) (0 : ℂ) * (0 : ℂ)) ∂halfline.prod halfline).re = _ at hre
  simp only [map_zero, zero_mul, mul_zero, integral_zero, Complex.zero_re] at hre
  rw [hv] at hre
  norm_num at hre

def familyRegistration : Registration arena (type_of% (@actual_resonant_reflected_cross_kernel)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_resonant_reflected_cross_kernel, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Original telescope has four binders. The selected observation is the
whole final equation RHS, preserving every other original source clause.
The raw path is a SOURCE_ONLY proposal pending actual scoped binding. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_resonant_reflected_cross_kernel) (Realization rateCrossSignature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.actual_resonant_reflected_cross_kernel.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.ResonantPhysical.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rateCrossSignature (fun _ a u => ∫ z : ℝ × ℝ,
      ((Real.exp (-a * (z.1 + z.2)) * (1 - a * (z.1 + z.2)) /
          (4 * a ^ 2) : ℝ) : ℂ) *
        ((starRingEnd ℂ) (u z.1) * u z.2) ∂halfline.prod halfline)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end ResonantPhysical

namespace ResonantMoment

def actual : Realization momentSignature :=
  realize momentSignature (fun _ a u => Complex.normSq (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline) /
      (4 * a ^ 2) -
    (((starRingEnd ℂ) (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline)) *
      (∫ t : ℝ, (t : ℂ) * (Real.exp (-a * t) : ℂ) * u t ∂halfline)).re /
        (2 * a)) (fun e => nomatch e)

def rejected : Realization momentSignature :=
  realize momentSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := momentSignature
  Law r := ∀ {a : ℝ} (_ha : 0 < a) {u : ℝ → ℂ} (_hu : Integrable u halfline),
    Integrable (fun t : ℝ => (t : ℂ) * (Real.exp (-a * t) : ℂ) * u t) halfline ∧
    (∫ ξ : ℝ, actualResonantSymbol a ξ *
        (starRingEnd ℂ) (unitarySourceFourier (zeroExtension u) ξ) *
          unitarySourceFourier (zeroExtension u) (-ξ)).re = r.readout () a u

private theorem source_reconstruction :
    (type_of% (@actual_resonant_reflected_cross_laplace_moment)) ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall (a := 1) (by norm_num) (u := fun _ => (0 : ℂ)) (by simp)).2
  norm_num [rejected, realize, zeroExtension, unitarySourceFourier_eq_integral] at hbad

private theorem actual_dependence : ObservationalDependence momentSignature actual := by
  intro i
  refine ⟨(1 : ℝ), (fun _ : ℝ => (0 : ℂ)), decayingInput, ?_⟩
  change
    Complex.normSq (∫ t : ℝ, (Real.exp (-(1 : ℝ) * t) : ℂ) * (0 : ℂ) ∂halfline) /
        (4 * (1 : ℝ) ^ 2) -
      (((starRingEnd ℂ) (∫ t : ℝ, (Real.exp (-(1 : ℝ) * t) : ℂ) * (0 : ℂ) ∂halfline)) *
        (∫ t : ℝ, (t : ℂ) * (Real.exp (-(1 : ℝ) * t) : ℂ) * (0 : ℂ) ∂halfline)).re /
          (2 * (1 : ℝ)) ≠ _
  dsimp only [actual, realize]
  rw [laplace_decayingInput, first_laplace_decayingInput]
  norm_num [Complex.normSq_apply]

def familyRegistration : Registration arena (type_of% (@actual_resonant_reflected_cross_laplace_moment)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨@actual_resonant_reflected_cross_laplace_moment, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Original telescope has four binders. The selected observation is the
whole final equation RHS, preserving every other original source clause.
The raw path is a SOURCE_ONLY proposal pending actual scoped binding. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_resonant_reflected_cross_laplace_moment) (Realization momentSignature) Type Unit where
  unitName := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.actual_resonant_reflected_cross_laplace_moment.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal.ResonantMoment.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize momentSignature (fun _ a u => Complex.normSq (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline) /
      (4 * a ^ 2) -
    (((starRingEnd ℂ) (∫ t : ℝ, (Real.exp (-a * t) : ℂ) * u t ∂halfline)) *
      (∫ t : ℝ, (t : ℂ) * (Real.exp (-a * t) : ℂ) * u t ∂halfline)).re /
        (2 * a))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms registration

end ResonantMoment


end Reg.D5.S3.Weil.ZetaGamma.FormCore.SourceGammaOffDiagonal
