import D5.S3.Arith.Robin.ActualContinuousFactorialCompensation.Basic
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped BigOperators Topology ArithmeticFunction
open _root_.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation

/- Compiled source-owner audit attempts; four-slot registrations unfinished.
The existing enrolled DependentFamily.realize interface is used below to
retain the actual readouts and complete original laws. No regularity or
arithmetic hypothesis is added. The exact source bridges and the available
whole-family variation/sensitivity terms below are compiled proof sources.

Unfinished four-slot obligations, per target:
* finite_smoothing: actual readout Z_h; exact all-real floor/factorial law below;
  actual observational dependence and faithful sourceSelection/binding unpaid.
* G_eq_integral: actual readout G; complete half-line identity below;
  actual observational dependence and faithful sourceSelection/binding unpaid.
* slope_measurable: actual readout slope; exact measurability law below;
  no nonmeasurable whole-family intervention is supplied, so variation,
  sensitivity, observational dependence and sourceSelection/binding unpaid.
* compensation: actual readout G; full completed contract below, including
  actual restricted-ae HasDerivAt and deriv bound; actual observational
  dependence and sourceSelection/binding unpaid. This is not an audit of a
  generic assumed-regularity theorem.
Continuation is unknown in all four attempts. No Contract.Registration or
DependentFamily.Registration is fabricated with missing proof fields.
The unfinished registrations are tracked at
https://github.com/the-omega-institute/trureturing/issues/25738.
No declared_validated status is claimed. -/

/- The public Basic.G_formula is the exact source supplier consumed by the
SignedLaplace D5 proof; this mirror retains the existing laws and bridges. -/

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def smoothingActual : Realization signature :=
  realize signature (fun _ _ x => Z_h x) (fun e => nomatch e)

abbrev smoothingArena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ} (hx : 1 ≤ x),
    (V.readout () ()) x = x * ((1 + gamma - Real.log x) * H x + 2 * J x) -
      Real.log (⌊x⌋₊.factorial : ℝ) - L * ⌊x⌋₊

private theorem smoothingActual_law : smoothingArena.Law smoothingActual :=
  @finite_smoothing

private theorem smoothingBridge :
    (type_of% (@finite_smoothing)) ↔ smoothingArena.Law smoothingActual := Iff.rfl

def smoothingRejected : Realization signature :=
  realize signature (fun _ _ x => Z_h x + 1) (fun e => nomatch e)

private theorem smoothingRejected_law : ¬ smoothingArena.Law smoothingRejected := by
  intro h
  have he := h (x := (1 : ℝ)) (by norm_num)
  have ha := finite_smoothing (x := (1 : ℝ)) (by norm_num)
  change Z_h 1 + 1 = _ at he
  linarith

private theorem smoothingVariation : Variation smoothingArena smoothingActual :=
  ⟨smoothingActual_law, smoothingRejected, smoothingRejected_law⟩

private theorem smoothingSensitivity : Sensitivity smoothingArena smoothingActual := by
  constructor
  · intro i
    refine ⟨smoothingRejected, ?_, rfl, smoothingRejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

def integralActual : Realization signature :=
  realize signature (fun _ _ x => G x) (fun e => nomatch e)

abbrev integralArena : Arena where
  signature := signature
  Law V := ∀ {x : ℝ} (hx : 1 ≤ x),
    (V.readout () ()) x = ∫ t in (1 : ℝ)..x, slope t

private theorem integralActual_law : integralArena.Law integralActual :=
  @G_eq_integral

private theorem integralBridge :
    (type_of% (@G_eq_integral)) ↔ integralArena.Law integralActual := Iff.rfl

def integralRejected : Realization signature :=
  realize signature (fun _ _ x => G x + 1) (fun e => nomatch e)

private theorem integralRejected_law : ¬ integralArena.Law integralRejected := by
  intro h
  have he := h (x := (1 : ℝ)) (by norm_num)
  have ha := G_eq_integral (x := (1 : ℝ)) (by norm_num)
  change G 1 + 1 = _ at he
  linarith

private theorem integralVariation : Variation integralArena integralActual :=
  ⟨integralActual_law, integralRejected, integralRejected_law⟩

private theorem integralSensitivity : Sensitivity integralArena integralActual := by
  constructor
  · intro i
    refine ⟨integralRejected, ?_, rfl, integralRejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

def measurableActual : Realization signature :=
  realize signature (fun _ _ x => slope x) (fun e => nomatch e)

abbrev measurableArena : Arena where
  signature := signature
  Law V := Measurable (V.readout () ())

private theorem measurableActual_law : measurableArena.Law measurableActual :=
  @slope_measurable

private theorem measurableBridge :
    (type_of% (@slope_measurable)) ↔ measurableArena.Law measurableActual := Iff.rfl

def compensationActual : Realization signature :=
  realize signature (fun _ _ x => G x) (fun e => nomatch e)

abbrev compensationArena : Arena where
  signature := signature
  Law V := (V.readout () ()) 1 = 0 ∧
    ContinuousOn (V.readout () ()) (Ici (1 : ℝ)) ∧
    (∀ X : ℝ, 1 ≤ X → AbsolutelyContinuousOnInterval (V.readout () ()) 1 X) ∧
    (∀ x : ℝ, 1 ≤ x → |(V.readout () ()) x| ≤
      (gamma + 2) * Real.log x + (Real.log x) ^ 2 / 2) ∧
    (∀ t : ℝ, 0 ≤ t → |(V.readout () ()) (Real.exp t)| ≤ (gamma + 2) * t + t ^ 2 / 2) ∧
    (∀ x : ℝ, 1 ≤ x → slope x =
      (gamma + Real.log x) * epsilon x + 2 * T_epsilon x ∧
      |slope x| ≤ (gamma + 2 + Real.log x) / x) ∧
    (∀ᵐ x : ℝ ∂volume.restrict (Ici (1 : ℝ)),
      HasDerivAt (V.readout () ()) (slope x) x ∧
      |deriv (V.readout () ()) x| ≤ (gamma + 2 + Real.log x) / x)

private theorem compensationActual_law : compensationArena.Law compensationActual :=
  @compensation

private theorem compensationBridge :
    (type_of% (@compensation)) ↔ compensationArena.Law compensationActual := Iff.rfl

def compensationRejected : Realization signature :=
  realize signature (fun _ _ x => G x + 1) (fun e => nomatch e)

private theorem compensationRejected_law : ¬ compensationArena.Law compensationRejected := by
  intro h
  have he := h.1
  have ha := compensation.1
  change G 1 + 1 = 0 at he
  linarith

private theorem compensationVariation : Variation compensationArena compensationActual :=
  ⟨compensationActual_law, compensationRejected, compensationRejected_law⟩

private theorem compensationSensitivity : Sensitivity compensationArena compensationActual := by
  constructor
  · intro i
    refine ⟨compensationRejected, ?_, rfl, compensationRejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim
  · intro e
    exact nomatch e

namespace H_harmonic

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
  realize signature (fun _ _ => H) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (x : ℝ),
    (V.readout () ()) x = (harmonic ⌊x⌋₊ : ℝ)

private theorem actual_law : arena.Law actual := @H_harmonic

private theorem sourceBridge :
    (type_of% (@H_harmonic)) ↔ arena.Law actual := Iff.rfl

end H_harmonic

namespace epsilonDensity_integrable

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
  realize signature (fun _ _ => epsilonDensity) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := IntegrableOn (V.readout () ()) (Ioi (1 : ℝ))

private theorem actual_law : arena.Law actual := @epsilonDensity_integrable

private theorem sourceBridge :
    (type_of% (@epsilonDensity_integrable)) ↔ arena.Law actual := Iff.rfl

end epsilonDensity_integrable

end Reg.D5.S3.Arith.Robin.ActualContinuousFactorialCompensation
