import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Convexity.PositivePairedPoissonCubature
import Reg.Support.SingleDependentReadout

/-! Complete source-bound audits of inverse synthesis, Haar moments and finite cubature. -/

open _root_.D5.S3.Analytic.Convexity.PositivePairedPoissonCubature
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Analytic.Convexity.PositivePairedPoissonCubature

/-- Observe real coefficients on the full, infinite sequence and index domain. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ → ℝ)
    (fun _ => ℕ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ f n => f n) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(fun n => (n : ℝ)), 0, 1, ?_⟩
  norm_num [actual, realize]

private theorem single_weighted :
    Summable (fun n : ℕ => |(Pi.single 0 1 : ℕ → ℝ) (n + 1)| * (2 : ℝ) ^ (n + 1)) := by
  simp

private theorem single_small :
    2 * weightedMass 2 (Pi.single 0 1) ≤ (1 : ℝ) / 16 := by
  simp [weightedMass]

namespace Audit1

/-- The complete original telescope and every conclusion clause are retained. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {D σ M : ℝ} {f : ℕ → ℝ}
    (_hσ : 1 < σ) (_hD : 0 ≤ D) (_hpair : D * σ ^ 2 < 1)
    (_hM : 0 < M) (_hmean : f 0 = M)
    (_hweighted : Summable (fun n : ℕ => |f (n + 1)| * σ ^ (n + 1)))
    (_hsmall : 2 * weightedMass σ f ≤ M / 16),
    Summable (fun n : ℕ => |pairedMultiplier D σ n|) ∧
    pairedMultiplier D σ 0 = 1 ∧
    (∀ n : ℕ, 0 < pairedMultiplier D σ n ∧
      pairedMultiplier D σ n ≤ (1 / σ) ^ n) ∧
    Summable (fun n : ℕ => |inverseCoeff D σ f n|) ∧
    inverseCoeff D σ f 0 = M ∧
    2 * (∑' n : ℕ, |inverseCoeff D σ f (n + 1)|) ≤ 4 * weightedMass σ f ∧
    4 * weightedMass σ f ≤ M / 8 ∧
    Continuous (cosineDensity (inverseCoeff D σ f)) ∧
    (∀ θ : ℝ, cosineDensity (inverseCoeff D σ f) (-θ) =
      cosineDensity (inverseCoeff D σ f) θ) ∧
    Function.Periodic (cosineDensity (inverseCoeff D σ f)) (2 * Real.pi) ∧
    (∀ θ : ℝ, M / 2 < cosineDensity (inverseCoeff D σ f) θ) ∧
    (∀ n : ℕ, pairedMultiplier D σ n * inverseCoeff D σ f n = R.readout () f n) ∧
    (∀ θ : ℝ,
      cosineDensity (fun n => pairedMultiplier D σ n * inverseCoeff D σ f n) θ =
        cosineDensity f θ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (D := 0) (σ := 2) (M := 1) (f := Pi.single 0 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by simp) single_weighted single_small
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hcoeff, _⟩ := hh
  have hc := hcoeff 0
  norm_num [rejected, realize, inverseCoeff, pairedMultiplier] at hc

def family : Registration arena (type_of% @weighted_positive_paired_poisson_inverse) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_positive_paired_poisson_inverse, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_positive_paired_poisson_inverse)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Convexity.PositivePairedPoissonCubature.weighted_positive_paired_poisson_inverse.audit
  realizationName := `Reg.D5.S3.Analytic.Convexity.PositivePairedPoissonCubature.Audit1.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f n => f n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Convexity.PositivePairedPoissonCubature
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "arg", "arg", "arg",
        "arg", "arg", "arg", "arg", "arg", "arg", "fn", "arg",
        "body", "arg"]
      stateBinder := 11
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Audit1

namespace Audit2

/-- The complete original telescope and every conclusion clause are retained. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {c : ℕ → ℝ}
    (_hs : Summable (fun n : ℕ => |c n|)),
    IntervalIntegrable (cosineDensity c) volume 0 (2 * Real.pi) ∧
    haarMean (cosineDensity c) = R.readout () c 0 ∧
    ∀ k : ℕ, 0 < k →
      IntervalIntegrable (fun θ => cosineDensity c θ * Real.cos ((k : ℝ) * θ))
        volume 0 (2 * Real.pi) ∧
      haarMean (fun θ => cosineDensity c θ * Real.cos ((k : ℝ) * θ)) = c k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (c := fun _ => 0) (by simp)).2.1
  norm_num [rejected, realize, haarMean, cosineDensity] at hh

def family : Registration arena (type_of% @cosineDensity_haar_moments) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cosineDensity_haar_moments, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@cosineDensity_haar_moments) (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Convexity.PositivePairedPoissonCubature.cosineDensity_haar_moments.audit
  realizationName := `Reg.D5.S3.Analytic.Convexity.PositivePairedPoissonCubature.Audit2.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f n => f n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Convexity.PositivePairedPoissonCubature
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #[
        "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Audit2

namespace Audit3

/-- The complete original telescope and every conclusion clause are retained. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {D σ M : ℝ} {f : ℕ → ℝ}
    (_hσ : 1 < σ) (_hD : 0 ≤ D) (_hpair : D * σ ^ 2 < 1)
    (_hM : 0 < M) (_hmean : f 0 = M)
    (_hweighted : Summable (fun n : ℕ => |f (n + 1)| * σ ^ (n + 1)))
    (_hsmall : 2 * weightedMass σ f ≤ M / 16) (L : ℕ),
    ∃ J : ℕ, 1 ≤ J ∧ J ≤ L + 1 ∧
      ∃ (t : Fin J → ℝ) (θ : Fin J → ℝ),
        (∀ j, 0 ≤ t j) ∧ (∑ j, t j = M / 2) ∧
        (∀ j, θ j ∈ Icc 0 (2 * Real.pi)) ∧
        ∀ k : ℕ, 1 ≤ k → k ≤ L →
          (∑ j, t j * pairedMultiplier D σ k * Real.cos ((k : ℝ) * θ j)) =
            R.readout () f k / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨J, _, _, t, θ, ht, hmass, _, hmom⟩ :=
    h (D := 0) (σ := 2) (M := 1) (f := Pi.single 0 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simp) single_weighted single_small 1
  have hm := hmom 1 (by norm_num) (by norm_num)
  have hb : (∑ j, t j * pairedMultiplier 0 2 1 * Real.cos ((1 : ℝ) * θ j)) ≤
      (1 : ℝ) / 8 := by
    calc
      _ ≤ ∑ j, t j * pairedMultiplier 0 2 1 := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_of_le_one_right
          (mul_nonneg (ht j) (by norm_num [pairedMultiplier])) (Real.cos_le_one _)
      _ = (∑ j, t j) * pairedMultiplier 0 2 1 := by rw [Finset.sum_mul]
      _ = 1 / 8 := by rw [hmass]; norm_num [pairedMultiplier]
  norm_num [rejected, realize] at hm
  simp only [one_mul] at hb
  linarith

def family : Registration arena (type_of% @weighted_positive_paired_poisson_finite_cubature) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_positive_paired_poisson_finite_cubature, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_positive_paired_poisson_finite_cubature)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Analytic.Convexity.PositivePairedPoissonCubature.weighted_positive_paired_poisson_finite_cubature.audit
  realizationName := `Reg.D5.S3.Analytic.Convexity.PositivePairedPoissonCubature.Audit3.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ f n => f n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Convexity.PositivePairedPoissonCubature
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #[
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "arg", "arg",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "body",
        "body", "body", "arg", "fn", "arg"]
      stateBinder := 15
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Audit3

end Reg.D5.S3.Analytic.Convexity.PositivePairedPoissonCubature
