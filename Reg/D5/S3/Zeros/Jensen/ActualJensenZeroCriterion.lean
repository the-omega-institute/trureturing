import Batteries.Tactic.OpenPrivate
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
import D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
import Reg.Support.SingleDependentReadout

/-! Source-bound audit of the Cauchy zero-exclusion theorem. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
open _root_.D5.S3.Zeros.Jensen.ActualSourceJensenFixedWindow
open _root_.D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open _root_.D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open _root_.D5.S3.Weil.ZeroData.UnconditionalCanonicalZeroData
open _root_.D5.S3.Analytic.Fourier.XiThetaTransform
open _root_.D5.S3.Analytic.ShiftedXiPoisson.ShiftedPoissonSemigroup
open private source_map from D5.S3.Zeros.Jensen.SourceJensenIntegralExtension
open private xi_square_source_at_zero from D5.S3.Zeros.Resolvent.XiSquareExteriorRemainder
open LeanInformationAudit Filter Metric Polynomial Set
open scoped Topology

namespace Reg.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion

noncomputable section
universe u

abbrev cauchySignature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℂ) (fun _ => ℝ)

def cauchyActual : Realization cauchySignature :=
  realize cauchySignature (fun _ _ z => z.im) (fun e => nomatch e)

def cauchyRejected : Realization cauchySignature :=
  realize cauchySignature (fun _ _ _ => 1) (fun e => nomatch e)

def cauchyArena : Arena where
  signature := cauchySignature
  Law R := ∀ {ι : Type u} {l : Filter ι} [l.NeBot]
      (p : ι → ℂ[X]) (F : ℂ → ℂ) (_hF : AnalyticOnNhd ℂ F univ)
      (_h0 : F 0 ≠ 0) (_hconv : TendstoLocallyUniformlyOn (fun i z => (p i).eval z) F l univ)
      (_hroot : ∀ᶠ i in l, AllRootsReal (p i)),
    ∀ c : ℂ, F c = 0 → R.readout () () c = 0

private theorem cauchyRejectedLaw : ¬ cauchyArena.{u}.Law cauchyRejected := by
  intro h
  let p : ℂ[X] := X + 1
  let F : ℂ → ℂ := fun z => p.eval z
  have hF : AnalyticOnNhd ℂ F univ :=
    p.differentiable.differentiableOn.analyticOnNhd isOpen_univ
  have h0 : F 0 ≠ 0 := by simp [F, p]
  have hConv : TendstoLocallyUniformlyOn (fun (_ : ULift.{u} Unit) => F) F
      (pure ⟨()⟩) univ := by
    apply TendstoUniformlyOn.tendstoLocallyUniformlyOn
    rw [tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall (fun _ _ _ => by simpa using hε)
  have hRoot : AllRootsReal p := by
    intro z hz
    have hz' : z + 1 = 0 := by simpa [p] using hz
    simpa using congrArg Complex.im hz'
  have hBad := @h (ULift.{u} Unit) (pure ⟨()⟩) inferInstance (fun _ => p) F hF h0
    hConv (Eventually.of_forall fun _ => hRoot) (-1) (by simp [F, p])
  exact one_ne_zero (show (1 : ℝ) = 0 from hBad)

def cauchyEvidence : Registration cauchyArena.{u}
    (type_of% (@allZerosReal_of_locallyUniform.{u})) where
  actual := cauchyActual
  bridge := Iff.rfl
  variation := ⟨allZerosReal_of_locallyUniform, cauchyRejected, cauchyRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    cauchyArena.Law cauchyActual cauchyRejected cauchyRejectedLaw
  dependence := by
    intro _
    refine ⟨(), (0 : ℂ), Complex.I, ?_⟩
    change (0 : ℂ).im ≠ Complex.I.im
    norm_num

def cauchyRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@allZerosReal_of_locallyUniform.{u}) (Realization cauchySignature) Unit Unit where
  unitName := `Reg.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion.cauchy_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion.cauchyEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨cauchyArena.{u}⟩
  objectArena := .source ⟨cauchyArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cauchyArena.{u} ⟨cauchyEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cauchySignature (fun _ _ z => z.im) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def realCoordinate : Realization cauchySignature :=
  realize cauchySignature (fun _ _ z => z.re) (fun e => nomatch e)

def zeroCoordinate : Realization cauchySignature :=
  realize cauchySignature (fun _ _ _ => 0) (fun e => nomatch e)

def reverseArena : Arena where
  signature := cauchySignature
  Law R :=
    let coordinate : ℂ → ℝ := R.readout () ()
    (∀ n : ℕ, 1 ≤ n → ∀ z : ℂ, (sourceJensenPolynomial n).eval z = 0 →
      coordinate ⟨z.im, z.re⟩ = 0) →
    ∀ (s : ℂ), riemannZeta s = 0 → (¬ ∃ m : ℕ, s = -2 * (m + 1)) →
      s ≠ 1 → coordinate s = (1 : ℝ) / 2

private theorem reverseRejectedLaw : ¬ reverseArena.Law zeroCoordinate := by
  intro h
  let s := zetaZeroData.zero 0
  have hs := zetaZeroData_isNontrivial 0
  have htrivial : ¬ ∃ m : ℕ, s = -2 * (m + 1) := by
    rintro ⟨m, hm⟩
    have hg := hs.2.1
    change 0 < s.re at hg
    have hre := congrArg Complex.re hm
    simp [Complex.mul_re, Complex.add_re] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    linarith
  have hone : s ≠ 1 := by
    intro he
    have hh := hs.2.2
    change s.re < 1 at hh
    simp [he] at hh
  have hbad : (0 : ℝ) = 1 / 2 := h (fun _ _ _ _ => rfl) s hs.1 htrivial hone
  norm_num at hbad

def reverseEvidence : Registration reverseArena (type_of% rh_of_actual_jensen_tower) where
  actual := realCoordinate
  bridge := Iff.rfl
  variation := ⟨rh_of_actual_jensen_tower, zeroCoordinate, reverseRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    reverseArena.Law realCoordinate zeroCoordinate reverseRejectedLaw
  dependence := by
    intro _
    refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
    change (0 : ℂ).re ≠ (1 : ℂ).re
    norm_num

def reflectionArena : Arena where
  signature := cauchySignature
  Law R := ∀ n : ℕ, AllRootsReal (sourceJensenPolynomial n) ↔
    ∀ z : ℂ, (sourcePolynomial n).eval z = 0 → R.readout () () z = 0

private theorem reflectionRejectedLaw : ¬ reflectionArena.Law cauchyRejected := by
  intro h
  have ha : (sourceThetaCoefficient 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (source_theta_normalized.2.2.2 1))
  have evaluation (z : ℂ) :
      (sourceJensenPolynomial 1).eval z = 1 + (sourceThetaCoefficient 1 : ℂ) * z := by
    simp [sourceJensenPolynomial, Finset.sum_range_succ, source_theta_coefficient_zero,
      Nat.descFactorial]
  have hroot : AllRootsReal (sourceJensenPolynomial 1) := by
    intro z hz
    rw [evaluation] at hz
    have hi := congrArg Complex.im hz
    simp [Complex.mul_im] at hi
    exact hi.resolve_left (Complex.ofReal_ne_zero.mp ha)
  have hbase : (sourceJensenPolynomial 1).eval (-(sourceThetaCoefficient 1 : ℂ)⁻¹) = 0 := by
    rw [evaluation]
    simp [ha]
  have hpoint : (sourcePolynomial 1).eval (sourceThetaCoefficient 1 : ℂ)⁻¹ = 0 := by
    rw [sourcePolynomial, source_map, eval_comp]
    simpa only [eval_mul, eval_C, eval_X, neg_one_mul] using hbase
  exact one_ne_zero (show (1 : ℝ) = 0 from (h 1).mp hroot _ hpoint)

def reflectionEvidence :
    Registration reflectionArena (type_of% sourceJensen_real_iff_reflected) where
  actual := cauchyActual
  bridge := Iff.rfl
  variation := ⟨sourceJensen_real_iff_reflected, cauchyRejected, reflectionRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    reflectionArena.Law cauchyActual cauchyRejected reflectionRejectedLaw
  dependence := by
    intro _
    refine ⟨(), (0 : ℂ), Complex.I, ?_⟩
    change (0 : ℂ).im ≠ Complex.I.im
    norm_num

abbrev sourceSignature := _root_.Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℂ) (fun _ => ℂ)

def sourceActual : Realization sourceSignature :=
  realize sourceSignature (fun _ _ z => sourceF z) (fun e => nomatch e)

def sourceRejected : Realization sourceSignature :=
  realize sourceSignature (fun _ _ _ => 0) (fun e => nomatch e)

def sourceArena : Arena where
  signature := sourceSignature
  Law R := R.readout () () = xiSquareSource

private theorem sourceRejectedLaw : ¬ sourceArena.Law sourceRejected := by
  intro h
  exact zero_ne_one (show (0 : ℂ) = 1 from (congrFun h 0).trans xi_square_source_at_zero)

def sourceEvidence : Registration sourceArena (type_of% sourceF_eq_xiSquareSource) where
  actual := sourceActual
  bridge := Iff.rfl
  variation := ⟨sourceF_eq_xiSquareSource, sourceRejected, sourceRejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sourceArena.Law sourceActual sourceRejected sourceRejectedLaw
  dependence := by
    intro _
    let s := zetaZeroData.zero 0
    let w : ℂ := -Complex.I * (s - 1 / 2)
    have hcoord : (1 / 2 : ℂ) + Complex.I * w = s := by
      dsimp [w]
      ring_nf
      norm_num [Complex.I_sq]
    have hz : xiSquareSource (w ^ 2) = 0 := by
      rw [xi_square_source_entire_and_composition.2, hcoord,
        (xiReading_eq_zero_iff_nontrivial s).mpr
          (zetaZeroData_isNontrivial 0), zero_div]
    refine ⟨(), (0 : ℂ), w ^ 2, ?_⟩
    change sourceF 0 ≠ sourceF (w ^ 2)
    rw [sourceF_eq_xiSquareSource, xi_square_source_at_zero, hz]
    exact one_ne_zero

def reverseRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    rh_of_actual_jensen_tower (Realization cauchySignature) Unit Unit where
  unitName := `Reg.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion.reverse_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion.reverseEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨reverseArena⟩
  objectArena := .source ⟨reverseArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reverseArena ⟨reverseEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cauchySignature (fun _ _ z => z.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def reflectionRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sourceJensen_real_iff_reflected (Realization cauchySignature) Unit Unit where
  unitName := `Reg.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion.reflection_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion.reflectionEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨reflectionArena⟩
  objectArena := .source ⟨reflectionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source reflectionArena ⟨reflectionEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cauchySignature (fun _ _ z => z.im) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def sourceRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    sourceF_eq_xiSquareSource (Realization sourceSignature) Unit Unit where
  unitName := `Reg.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion.source_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion.sourceEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨sourceEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sourceSignature (fun _ _ z => sourceF z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Zeros.Jensen.ActualJensenZeroCriterion
