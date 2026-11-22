import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.PetzDyadicEscapeSpectrum
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the Petz rate profile and its binomial inverse obstruction. -/

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.PetzDyadicEscapeSpectrum
open _root_.PetzStripGramRemainder (stripGram)
open _root_.Reg.Support.SingleDependentReadout (signature sensitivity)
open scoped BigOperators

namespace Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum

universe u

private abbrev scalarRelation : Signature := signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)
private abbrev realSignature : Signature := signature Unit (fun _ => ℝ) (fun _ => ℝ)
private abbrev massSignature : Signature := signature ℕ (fun n => Fin (n + 1) → ℝ) (fun _ => ℝ)
private abbrev supportSignature : Signature :=
  signature ℕ (fun m => Finset (Fin (2 * m - 1 + 1))) (fun _ => ℕ)
private abbrev constantSignature : Signature := signature ℕ (fun _ => ℝ) (fun _ => ℝ)
private abbrev coalescingSignature : Signature :=
  signature (Σ _ : ℕ, Σ _ : ℝ, ℝ) (fun _ => ℝ) (fun _ => ℝ)

private def rejectedRelation : Realization scalarRelation :=
  realize scalarRelation (fun _ _ _ _ => False) (fun e => nomatch e)

private def realObservation (f : ℝ → ℝ) : Realization realSignature :=
  realize realSignature (fun _ _ x => f x) (fun e => nomatch e)

private theorem eqDependence : ObservationalDependence scalarRelation
    (realize scalarRelation (fun _ _ x y => x = y) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro equal
  have h := congrFun equal 0
  change ((0 : ℝ) = 0) = (1 = 0) at h
  norm_num at h

private theorem leDependence : ObservationalDependence scalarRelation
    (realize scalarRelation (fun _ _ x y => x ≤ y) (fun e => nomatch e)) := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro equal
  have h := congrFun equal 0
  change ((0 : ℝ) ≤ 0) = (1 ≤ 0) at h
  norm_num at h

private theorem expDependence : ObservationalDependence realSignature
    (realize realSignature (fun _ _ x => Real.exp x) (fun e => nomatch e)) := by
  intro role
  exact ⟨(), 0, 1, fun equal => zero_ne_one (Real.exp_injective equal)⟩

namespace DiagonalError

private def actual : Realization realSignature :=
  realize realSignature (fun _ _ x => |x|) (fun e => nomatch e)

private def rejected : Realization realSignature :=
  realObservation (fun _ => 1)

abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ {ι : Type u} [Fintype ι]
      (rates weights : ι → ℝ) {eps s : ℝ}, 0 < eps → 0 < s →
      (∀ i, 0 ≤ rates i) → (∀ i, 0 < weights i) →
      (∀ i, Real.log (Real.exp (-(rates i / eps))) - Real.log (eps * weights i) ≤ 0) →
      let frequency (i : ι) :=
        (s * eps) * (Real.log (Real.exp (-(rates i / eps))) - Real.log (eps * weights i))
      R.readout () () ((∑ i, weights i * stripGram (frequency i) (frequency i)) / s -
        rateProfile rates weights s) ≤ eps * ∑ i, weights i * |Real.log (eps * weights i)|

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  have h := law (ι := ULift.{u} Unit) (fun _ => 0) (fun _ => 1) (eps := 1) (s := 1)
    zero_lt_one zero_lt_one (fun _ => le_rfl) (fun _ => zero_lt_one) (by simp)
  change (1 : ℝ) ≤ 1 * ∑ _ : ULift.{u} Unit, (1 : ℝ) * |Real.log (1 * 1)| at h
  norm_num at h

def family : Registration arena.{u} (type_of% @diagonal_log_ratio_profile_error.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@diagonal_log_ratio_profile_error.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change |(0 : ℝ)| ≠ |1|
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@diagonal_log_ratio_profile_error.{u}) (Realization realSignature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PetzDyadicEscapeSpectrum.diagonal_log_ratio_profile_error.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.DiagonalError.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DiagonalError

namespace MomentSum

private def actual : Realization scalarRelation :=
  realize scalarRelation (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization scalarRelation :=
  rejectedRelation

abbrev arena : Arena where
  signature := scalarRelation
  Law R := ∀ {ι : Type u} [Fintype ι] (rates weights : ι → ℝ) (k : ℕ),
      R.readout () () (rateMoment rates weights k) (∑ i, weights i * rates i ^ k)

private theorem rejectedLaw : ¬ arena.{u}.Law rejected :=
  fun law => law (ι := ULift.{u} Unit) (fun _ => 0) (fun _ => 0) 0

def family : Registration arena.{u} (type_of% @rateMoment_eq_sum.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rateMoment_eq_sum.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := eqDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rateMoment_eq_sum.{u}) (Realization scalarRelation) Unit Unit where
  unitName := `D5.S3.Analytic.PetzDyadicEscapeSpectrum.rateMoment_eq_sum.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.MomentSum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarRelation (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MomentSum

namespace ProfileLaplace

private def actual : Realization scalarRelation :=
  realize scalarRelation (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization scalarRelation :=
  rejectedRelation

abbrev arena : Arena where
  signature := scalarRelation
  Law R := ∀ {ι : Type u} [Fintype ι] (rates weights : ι → ℝ) (s : ℝ),
      R.readout () () (rateProfile rates weights s)
        ((tiltedRateMoment rates weights 0 s - rateMoment rates weights 0 +
          s * rateMoment rates weights 1) / s)

private theorem rejectedLaw : ¬ arena.{u}.Law rejected :=
  fun law => law (ι := ULift.{u} Unit) (fun _ => 0) (fun _ => 0) 0

def family : Registration arena.{u} (type_of% @rateProfile_eq_laplace.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rateProfile_eq_laplace.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := eqDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@rateProfile_eq_laplace.{u}) (Realization scalarRelation) Unit Unit where
  unitName := `D5.S3.Analytic.PetzDyadicEscapeSpectrum.rateProfile_eq_laplace.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.ProfileLaplace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarRelation (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ProfileLaplace

namespace MomentDerivative

private def actual : Realization realSignature :=
  realize realSignature (fun _ _ x => -x) (fun e => nomatch e)

private def rejected : Realization realSignature :=
  realObservation (fun _ => 1)

abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ {ι : Type u} [Fintype ι] (rates weights : ι → ℝ) (k : ℕ) (s : ℝ),
      HasDerivAt (tiltedRateMoment rates weights k)
        (R.readout () () (tiltedRateMoment rates weights (k + 1) s)) s

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  let rates : ULift.{u} Unit → ℝ := fun _ => 0
  let weights : ULift.{u} Unit → ℝ := fun _ => 0
  have bad : HasDerivAt (tiltedRateMoment rates weights 0) 1 0 := law rates weights 0 0
  have actual : HasDerivAt (tiltedRateMoment rates weights 0) 0 0 := by
    simpa [tiltedRateMoment, weights] using hasDerivAt_tiltedRateMoment rates weights 0 0
  exact one_ne_zero (bad.unique actual)

def family : Registration arena.{u} (type_of% @hasDerivAt_tiltedRateMoment.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_tiltedRateMoment.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨(), 0, 1, ?_⟩
    change -(0 : ℝ) ≠ -1
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_tiltedRateMoment.{u}) (Realization realSignature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PetzDyadicEscapeSpectrum.hasDerivAt_tiltedRateMoment.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.MomentDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ x => -x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end MomentDerivative

namespace ProfileDerivative

private def actual : Realization realSignature :=
  realize realSignature (fun _ _ x => Real.exp x) (fun e => nomatch e)

private def rejected : Realization realSignature :=
  realObservation (fun _ => 0)

abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ {ι : Type u} [Fintype ι] (rates weights : ι → ℝ) {s : ℝ}, s ≠ 0 →
      HasDerivAt (rateProfile rates weights)
        (∑ i, weights i * ((1 - (1 + s * rates i) * R.readout () () (-(s * rates i))) / s ^ 2)) s

private theorem rejectedLaw : ¬ arena.{u}.Law rejected := by
  intro law
  let rates : ULift.{u} Unit → ℝ := fun _ => 0
  let weights : ULift.{u} Unit → ℝ := fun _ => 1
  have h := law rates weights (s := 1) one_ne_zero
  have bad : HasDerivAt (rateProfile rates weights) 1 1 := by
    simpa [rejected, realObservation, realize, rates, weights] using h
  have actual : HasDerivAt (rateProfile rates weights) 0 1 := by
    simpa [rates, weights] using hasDerivAt_rateProfile rates weights (s := 1) one_ne_zero
  exact one_ne_zero (bad.unique actual)

def family : Registration arena.{u} (type_of% @hasDerivAt_rateProfile.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasDerivAt_rateProfile.{u}, rejected, rejectedLaw.{u}⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := expDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@hasDerivAt_rateProfile.{u}) (Realization realSignature) Unit Unit where
  unitName := `D5.S3.Analytic.PetzDyadicEscapeSpectrum.hasDerivAt_rateProfile.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.ProfileDerivative.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ x => Real.exp x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg",
        "body", "arg", "fn", "arg", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ProfileDerivative

namespace Normalized

private def actual : Realization massSignature :=
  realize massSignature (fun _ _ weights => Finset.univ.sum weights) (fun e => nomatch e)

private def rejected : Realization massSignature :=
  realize massSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := massSignature
  Law R := ∀ (n : ℕ), 0 < n →
      (∀ j, 0 ≤ evenBinomial n j) ∧ (∀ j, 0 ≤ oddBinomial n j) ∧
        R.readout () n (evenBinomial n) = 1 ∧ (∑ j, oddBinomial n j) = 1

private theorem rejectedLaw : ¬ arena.Law rejected :=
  fun law => zero_ne_one (law 1 (by decide)).2.2.1

def family : Registration arena (type_of% @binomial_laws_normalized) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@binomial_laws_normalized, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨0, (fun _ => 0), (fun _ => 1), ?_⟩
    change (∑ _ : Fin 1, (0 : ℝ)) ≠ ∑ _ : Fin 1, (1 : ℝ)
    simp

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@binomial_laws_normalized) (Realization massSignature) Unit Unit where
  unitName := `D5.S3.Analytic.PetzDyadicEscapeSpectrum.binomial_laws_normalized.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.Normalized.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ weights => Finset.univ.sum weights) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Normalized

namespace EqualMean

private def actual : Realization scalarRelation :=
  realize scalarRelation (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization scalarRelation :=
  rejectedRelation

abbrev arena : Arena where
  signature := scalarRelation
  Law R := ∀ (n : ℕ), 1 < n → ∀ r0 eta : ℝ,
      R.readout () () (rateMoment (binomialRate n r0 eta) (evenBinomial n) 1)
        (rateMoment (binomialRate n r0 eta) (oddBinomial n) 1)

private theorem rejectedLaw : ¬ arena.Law rejected := fun law => law 2 (by decide) 0 0

def family : Registration arena (type_of% @binomial_laws_equal_mean) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@binomial_laws_equal_mean, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := eqDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@binomial_laws_equal_mean) (Realization scalarRelation) Unit Unit where
  unitName := `D5.S3.Analytic.PetzDyadicEscapeSpectrum.binomial_laws_equal_mean.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.EqualMean.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarRelation (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EqualMean

namespace SupportCard

private def actual : Realization supportSignature :=
  realize supportSignature (fun _ _ support => support.card) (fun e => nomatch e)

private def rejected : Realization supportSignature :=
  realize supportSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := supportSignature
  Law R := ∀ (m : ℕ), 0 < m →
      R.readout () m (Finset.univ.filter (fun j => evenBinomial (2 * m - 1) j ≠ 0)) = m ∧
      (Finset.univ.filter (fun j => oddBinomial (2 * m - 1) j ≠ 0)).card = m

private theorem rejectedLaw : ¬ arena.Law rejected :=
  fun law => Nat.zero_ne_one (law 1 (by decide)).1

def family : Registration arena (type_of% @binomial_laws_support_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@binomial_laws_support_card, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨1, ∅, {0}, ?_⟩
    change (∅ : Finset (Fin (2 * 1 - 1 + 1))).card ≠ ({0} : Finset (Fin (2 * 1 - 1 + 1))).card
    simp

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@binomial_laws_support_card) (Realization supportSignature) Unit Unit where
  unitName := `D5.S3.Analytic.PetzDyadicEscapeSpectrum.binomial_laws_support_card.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.SupportCard.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize supportSignature (fun _ _ support => support.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end SupportCard

namespace BinomialLaplace

private def actual : Realization scalarRelation :=
  realize scalarRelation (fun _ _ x y => x = y) (fun e => nomatch e)

private def rejected : Realization scalarRelation :=
  rejectedRelation

abbrev arena : Arena where
  signature := scalarRelation
  Law R := ∀ (n : ℕ) (r0 eta s : ℝ),
      R.readout () ()
        (tiltedRateMoment (binomialRate n r0 eta) (evenBinomial n) 0 s -
          tiltedRateMoment (binomialRate n r0 eta) (oddBinomial n) 0 s)
        (Real.exp (-(s * r0)) * (1 - Real.exp (-(s * eta))) ^ n / (2 : ℝ) ^ (n - 1))

private theorem rejectedLaw : ¬ arena.Law rejected := fun law => law 2 0 0 0

def family : Registration arena (type_of% @binomial_laplace_difference) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@binomial_laplace_difference, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := eqDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@binomial_laplace_difference) (Realization scalarRelation) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PetzDyadicEscapeSpectrum.binomial_laplace_difference.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.BinomialLaplace.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarRelation (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BinomialLaplace

namespace BinomialProfile

private def actual : Realization realSignature :=
  realize realSignature (fun _ _ x => Real.exp x) (fun e => nomatch e)

private def rejected : Realization realSignature :=
  realObservation (fun _ => 1)

abbrev arena : Arena where
  signature := realSignature
  Law R := ∀ (n : ℕ), 1 < n → ∀ r0 eta s : ℝ,
      rateProfile (binomialRate n r0 eta) (evenBinomial n) s -
        rateProfile (binomialRate n r0 eta) (oddBinomial n) s =
        Real.exp (-(s * r0)) * (1 - R.readout () () (-(s * eta))) ^ n /
          ((2 : ℝ) ^ (n - 1) * s)

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro law
  have bad :
      rateProfile (binomialRate 2 0 1) (evenBinomial 2) 1 -
        rateProfile (binomialRate 2 0 1) (oddBinomial 2) 1 = 0 := by
    simpa [rejected, realObservation, realize] using law 2 (by decide) 0 1 1
  have positive := binomial_profile_difference 2 (by decide) 0 1 1
  rw [bad] at positive
  have hstep : 0 < 1 - Real.exp (-(1 * (1 : ℝ))) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
  have hright :
      0 < Real.exp (-(1 * (0 : ℝ))) * (1 - Real.exp (-(1 * (1 : ℝ)))) ^ (2 : ℕ) /
        ((2 : ℝ) ^ (2 - 1 : ℕ) * 1) :=
    div_pos (mul_pos (Real.exp_pos _) (pow_pos hstep _)) (by positivity)
  exact (ne_of_gt hright) positive.symm

def family : Registration arena (type_of% @binomial_profile_difference) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@binomial_profile_difference, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := expDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@binomial_profile_difference) (Realization realSignature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PetzDyadicEscapeSpectrum.binomial_profile_difference.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.BinomialProfile.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize realSignature (fun _ _ x => Real.exp x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "arg",
        "fn", "arg", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end BinomialProfile

namespace UniformConstant

private def actual : Realization constantSignature :=
  realize constantSignature (fun _ n rMin => binomialUniformConstant n rMin) (fun e => nomatch e)

private def rejected : Realization constantSignature :=
  realize constantSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := constantSignature
  Law R := ∀ (n : ℕ) {rMin : ℝ}, 0 < rMin → 0 < R.readout () n rMin

private theorem rejectedLaw : ¬ arena.Law rejected :=
  fun law => (lt_irrefl (0 : ℝ)) (law 2 (rMin := 1) zero_lt_one)

def family : Registration arena (type_of% @binomialUniformConstant_pos) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@binomialUniformConstant_pos, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨2, 1, 2, ?_⟩
    change binomialUniformConstant 2 1 ≠ binomialUniformConstant 2 2
    norm_num [binomialUniformConstant]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@binomialUniformConstant_pos) (Realization constantSignature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PetzDyadicEscapeSpectrum.binomialUniformConstant_pos.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.UniformConstant.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize constantSignature (fun _ n rMin => binomialUniformConstant n rMin) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end UniformConstant

namespace ProfileBound

private def actual : Realization scalarRelation :=
  realize scalarRelation (fun _ _ x y => x ≤ y) (fun e => nomatch e)

private def rejected : Realization scalarRelation :=
  rejectedRelation

abbrev arena : Arena where
  signature := scalarRelation
  Law R := ∀ (n : ℕ), 1 < n → ∀ {rMin r0 eta s : ℝ},
      0 < rMin → rMin ≤ r0 → 0 ≤ eta → 0 < s →
      R.readout () ()
        |rateProfile (binomialRate n r0 eta) (evenBinomial n) s -
          rateProfile (binomialRate n r0 eta) (oddBinomial n) s|
        (Real.exp (-(s * r0)) * s ^ (n - 1) * eta ^ n / (2 : ℝ) ^ (n - 1)) ∧
      Real.exp (-(s * r0)) * s ^ (n - 1) * eta ^ n / (2 : ℝ) ^ (n - 1) ≤
        binomialUniformConstant n rMin * eta ^ n

private theorem rejectedLaw : ¬ arena.Law rejected :=
  fun law => (law 2 (by decide) (rMin := 1) (r0 := 1) (eta := 1) (s := 1)
    zero_lt_one le_rfl zero_le_one zero_lt_one).1

def family : Registration arena (type_of% @binomial_profile_difference_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@binomial_profile_difference_bound, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := leDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@binomial_profile_difference_bound) (Realization scalarRelation) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PetzDyadicEscapeSpectrum.binomial_profile_difference_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.ProfileBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarRelation (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ProfileBound

namespace TransportLowerBound

private def actual : Realization scalarRelation :=
  realize scalarRelation (fun _ _ eta cost => eta ≤ cost) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarRelation
  Law R := ∀ (n : ℕ), 0 < n → ∀ (r0 : ℝ) {eta : ℝ}, 0 ≤ eta →
      R.readout () () eta
        (finiteWasserstein1 (binomialRate n r0 eta) (evenBinomial n) (oddBinomial n))

private theorem rejectedLaw : ¬ arena.Law rejectedRelation :=
  fun law => law 1 (by decide) 0 (eta := 0) le_rfl

def family : Registration arena (type_of% @binomial_wasserstein_lower_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@binomial_wasserstein_lower_bound, rejectedRelation, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejectedRelation rejectedLaw
  dependence := leDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@binomial_wasserstein_lower_bound) (Realization scalarRelation) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PetzDyadicEscapeSpectrum.binomial_wasserstein_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.TransportLowerBound.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarRelation (fun _ _ eta cost => eta ≤ cost) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end TransportLowerBound

namespace CoalescingWitness

private def actual : Realization coalescingSignature :=
  realize coalescingSignature (fun _ p s =>
    rateProfile (binomialRate (2 * p.1 - 1) p.2.1 p.2.2) (evenBinomial (2 * p.1 - 1)) s -
      rateProfile (binomialRate (2 * p.1 - 1) p.2.1 p.2.2) (oddBinomial (2 * p.1 - 1)) s)
    (fun e => nomatch e)

private def rejected : Realization coalescingSignature :=
  realize coalescingSignature
    (fun _ p _ => binomialUniformConstant (2 * p.1 - 1) p.2.1 * p.2.2 ^ (2 * p.1 - 1) + 1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := coalescingSignature
  Law R := ∀ (m : ℕ), 2 ≤ m → ∀ {rMin rMax eta : ℝ},
      0 < rMin → 0 < eta → rMin + ((2 * m - 1 : ℕ) : ℝ) * eta ≤ rMax →
      let n := 2 * m - 1
      let rates := binomialRate n rMin eta
      let evenWeights := evenBinomial n
      let oddWeights := oddBinomial n
      StrictMono rates ∧
      (∀ j, rates j ∈ Set.Icc rMin rMax) ∧
      (∀ j, 0 ≤ evenWeights j ∧ 0 ≤ oddWeights j) ∧
      (Finset.univ.filter (fun j => evenWeights j ≠ 0)).card = m ∧
      (Finset.univ.filter (fun j => oddWeights j ≠ 0)).card = m ∧
      (∑ j, evenWeights j) = 1 ∧ (∑ j, oddWeights j) = 1 ∧
      rateMoment rates evenWeights 1 = rateMoment rates oddWeights 1 ∧
      (∀ s : ℝ, 0 < s →
        |R.readout () ⟨m, rMin, eta⟩ s| ≤ binomialUniformConstant n rMin * eta ^ n) ∧
      eta ≤ finiteWasserstein1 rates evenWeights oddWeights

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro law
  have h := law 2 (by decide) (rMin := 1) (rMax := 4) (eta := 1) zero_lt_one zero_lt_one
    (by norm_num)
  obtain ⟨_, _, _, _, _, _, _, _, herror, _⟩ := h
  have hbad := herror 1 zero_lt_one
  dsimp [rejected, realize] at hbad
  have h := le_trans (le_abs_self _) hbad
  linarith

def family : Registration arena (type_of% @coalescing_binomial_witness) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@coalescing_binomial_witness, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := by
    intro role
    refine ⟨⟨2, 0, 1⟩, 0, 1, ?_⟩
    change (rateProfile (binomialRate 3 0 1) (evenBinomial 3) 0 -
        rateProfile (binomialRate 3 0 1) (oddBinomial 3) 0) ≠
      (rateProfile (binomialRate 3 0 1) (evenBinomial 3) 1 -
        rateProfile (binomialRate 3 0 1) (oddBinomial 3) 1)
    rw [binomial_profile_difference 3 (by decide), binomial_profile_difference 3 (by decide)]
    simp only [mul_zero, mul_one, div_zero]
    have hstep : 0 < 1 - Real.exp (-(1 : ℝ)) :=
      sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
    exact ne_of_lt (by positivity)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@coalescing_binomial_witness) (Realization coalescingSignature) Unit Unit where
  unitName :=
    `D5.S3.Analytic.PetzDyadicEscapeSpectrum.coalescing_binomial_witness.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.CoalescingWitness.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coalescingSignature (fun _ p s =>
    rateProfile (binomialRate (2 * p.1 - 1) p.2.1 p.2.2) (evenBinomial (2 * p.1 - 1)) s -
      rateProfile (binomialRate (2 * p.1 - 1) p.2.1 p.2.2) (oddBinomial (2 * p.1 - 1)) s)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[0, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "fn", "arg", "body", "body", "fn", "arg", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end CoalescingWitness

namespace HolderObstruction

private def actual : Realization scalarRelation :=
  realize scalarRelation (fun _ _ cost bound => cost ≤ bound) (fun e => nomatch e)

private def rejected : Realization scalarRelation :=
  realize scalarRelation (fun _ _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := scalarRelation
  Law R := ∀ (m : ℕ), 2 ≤ m → ∀ {rMin rMax alpha : ℝ},
      0 < rMin → rMin < rMax → 1 < ((2 * m - 1 : ℕ) : ℝ) * alpha →
      ¬ ∃ C : ℝ, 0 ≤ C ∧
        ∀ (rates w v : Fin (2 * m - 1 + 1) → ℝ) (delta : ℝ),
          StrictMono rates →
          (∀ j, rates j ∈ Set.Icc rMin rMax) →
          (∀ j, 0 ≤ w j ∧ 0 ≤ v j) →
          (Finset.univ.filter (fun j => w j ≠ 0)).card = m →
          (Finset.univ.filter (fun j => v j ≠ 0)).card = m →
          (∑ j, w j) = 1 → (∑ j, v j) = 1 →
          rateMoment rates w 1 = rateMoment rates v 1 →
          0 < delta →
          (∀ s : ℝ, 0 < s → |rateProfile rates w s - rateProfile rates v s| ≤ delta) →
          R.readout () () (finiteWasserstein1 rates w v) (C * delta ^ alpha)

private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro law
  apply law 2 (by decide) (rMin := 1) (rMax := 2) (alpha := 1)
    zero_lt_one (by norm_num) (by norm_num)
  exact ⟨0, le_rfl, by intros; trivial⟩

def family : Registration arena (type_of% @no_uniform_holder_inverse) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@no_uniform_holder_inverse, rejected, rejectedLaw⟩
  sensitivity := sensitivity arena.Law actual rejected rejectedLaw
  dependence := leDependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@no_uniform_holder_inverse) (Realization scalarRelation) Unit Unit where
  unitName := `D5.S3.Analytic.PetzDyadicEscapeSpectrum.no_uniform_holder_inverse.__information_unit
  realizationName := `Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum.HolderObstruction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarRelation (fun _ _ cost bound => cost ≤ bound) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.PetzDyadicEscapeSpectrum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg",
        "arg", "body", "arg", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "fn",
        "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end HolderObstruction

#print axioms DiagonalError.audit
#print axioms MomentSum.audit
#print axioms ProfileLaplace.audit
#print axioms MomentDerivative.audit
#print axioms ProfileDerivative.audit
#print axioms Normalized.audit
#print axioms EqualMean.audit
#print axioms SupportCard.audit
#print axioms BinomialLaplace.audit
#print axioms BinomialProfile.audit
#print axioms UniformConstant.audit
#print axioms ProfileBound.audit
#print axioms TransportLowerBound.audit
#print axioms CoalescingWitness.audit
#print axioms HolderObstruction.audit

end Reg.D5.S3.Analytic.PetzDyadicEscapeSpectrum
