/- GID: D5/S1/Words/AdmissibleWords/FiveModeFisherImmersion
   generality: G
   mirror-B: D5/B/S1/Words/AdmissibleWords/FiveModeFisherImmersion
   mirror-E: none(waiver:analytically-proved)
   anchors: []
   utility: none
   digest: Actual five-mode simplex coordinates realize Fisher geometry by a smooth immersion. -/

import D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

/- The classical square-root Fisher construction, consumed here by
   the actual five-mode law. This asserts neither a completed Mathlib
   RiemannianMetric instance nor a total map from the 5040 family or RH. -/

set_option autoImplicit false
noncomputable section

namespace D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion

open scoped ContDiff
open D5.S1.Words.AdmissibleWords.FiveModeMixedCoordinates

/-- The genuine four-dimensional tangent lift into the mass-one hyperplane. -/
def tangentLift : (Fin 4 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  ContinuousLinearMap.pi (Fin.cases
    (-∑ i : Fin 4, ContinuousLinearMap.proj i)
    (fun i => ContinuousLinearMap.proj i))

/-- The omitted probability is determined by mass conservation. -/
def simplexLaw (q : Fin 4 → ℝ) : Fin 5 → ℝ :=
  tangentLift q + Fin.cons 1 (fun _ => 0)

/-- The actual open domain of the affine simplex chart. -/
def chartDomain : Set (Fin 4 → ℝ) := {q | ∀ s, 0 < simplexLaw q s}

/-- Classical square-root coordinates, scaled to the sphere of radius two. -/
def squareRootChart (q : Fin 4 → ℝ) : Fin 5 → ℝ :=
  fun s => 2 * Real.sqrt (simplexLaw q s)

/-- The actual derivative of the square-root map on the positive domain. -/
def squareRootDerivative (q : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] (Fin 5 → ℝ) :=
  ContinuousLinearMap.pi (fun s => (Real.sqrt (simplexLaw q s))⁻¹ •
    (ContinuousLinearMap.proj s).comp tangentLift)

private theorem tangentLift_injective : Function.Injective tangentLift := by
  intro u v h
  funext i
  have hi := congrFun h i.succ
  simpa [tangentLift] using hi

private theorem simplexLaw_sum (q : Fin 4 → ℝ) : ∑ s, simplexLaw q s = 1 := by
  simp [simplexLaw, tangentLift, Fin.sum_univ_succ]
  ring

private theorem simplexLaw_contDiff : ContDiff ℝ ∞ simplexLaw :=
  tangentLift.contDiff.add contDiff_const

private theorem simplexLaw_hasFDerivAt (q : Fin 4 → ℝ) :
    HasFDerivAt simplexLaw tangentLift q := by
  simpa [simplexLaw] using tangentLift.hasFDerivAt.add_const (Fin.cons 1 (fun _ => 0))

private theorem chartDomain_isOpen : IsOpen chartDomain := by
  change IsOpen {q : Fin 4 → ℝ | ∀ s, 0 < simplexLaw q s}
  simp only [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun s =>
    isOpen_lt continuous_const
      ((continuous_apply s).comp simplexLaw_contDiff.continuous)

private theorem simplexLaw_exact_chart :
    (∀ q, q ∈ chartDomain ↔ simplexLaw q ∈ openSimplex) ∧
      (∀ p ∈ openSimplex, ∃! q, q ∈ chartDomain ∧ simplexLaw q = p) := by
  constructor
  · intro q
    exact ⟨fun h => ⟨h, simplexLaw_sum q⟩, fun h => h.1⟩
  · intro p hp
    let q : Fin 4 → ℝ := fun i => p i.succ
    have heq : simplexLaw q = p := by
      funext s
      refine Fin.cases ?_ (fun i => ?_) s
      · have hsum := hp.2
        rw [Fin.sum_univ_succ] at hsum
        simp only [simplexLaw, tangentLift, ContinuousLinearMap.pi_apply,
          Pi.add_apply, Fin.cases_zero, Fin.cons_zero]
        simp only [neg_apply, sum_apply,
          ContinuousLinearMap.proj_apply]
        dsimp [q]
        linarith only [hsum]
      · simp [simplexLaw, tangentLift, q]
    refine ⟨q, ⟨?_, heq⟩, ?_⟩
    · change ∀ s, 0 < simplexLaw q s
      rw [heq]
      exact hp.1
    · intro r hr
      funext i
      have hi := congrFun hr.2 i.succ
      simpa [simplexLaw, tangentLift, q] using hi

private theorem squareRootChart_contDiffOn :
    ContDiffOn ℝ ∞ squareRootChart chartDomain := by
  apply contDiffOn_pi.2
  intro s
  have hcoord : ContDiffOn ℝ ∞ (fun q => simplexLaw q s) chartDomain :=
    ((contDiff_apply ℝ (fun _ : Fin 5 => ℝ) s).comp simplexLaw_contDiff).contDiffOn
  exact contDiffOn_const.mul (hcoord.sqrt (fun q hq => (hq s).ne'))

private theorem squareRootChart_hasFDerivAt {q : Fin 4 → ℝ} (hq : q ∈ chartDomain) :
    HasFDerivAt squareRootChart (squareRootDerivative q) q := by
  apply hasFDerivAt_pi.2
  intro s
  have hcoord := (ContinuousLinearMap.proj s).hasFDerivAt.comp q
    (simplexLaw_hasFDerivAt q)
  have hout := ((Real.hasDerivAt_sqrt (hq s).ne').comp_hasFDerivAt q hcoord).const_mul 2
  have hsqrt : Real.sqrt (simplexLaw q s) ≠ 0 := (Real.sqrt_pos.2 (hq s)).ne'
  have hcoef : (2 : ℝ) * (1 / (2 * Real.sqrt (simplexLaw q s))) =
      (Real.sqrt (simplexLaw q s))⁻¹ := by field_simp [hsqrt]
  change HasFDerivAt (fun x => 2 * Real.sqrt (simplexLaw x s))
    ((Real.sqrt (simplexLaw q s))⁻¹ • (ContinuousLinearMap.proj s).comp tangentLift) q
  simpa only [Function.comp_def, ContinuousLinearMap.proj_apply, smul_smul, hcoef] using hout

private theorem squareRootDerivative_injective {q : Fin 4 → ℝ}
    (hq : q ∈ chartDomain) : Function.Injective (squareRootDerivative q) := by
  intro u v huv
  apply tangentLift_injective
  funext s
  have hs := congrFun huv s
  have hne : (Real.sqrt (simplexLaw q s))⁻¹ ≠ 0 :=
    inv_ne_zero (Real.sqrt_pos.2 (hq s)).ne'
  exact (mul_left_cancel₀ hne) (by simpa [squareRootDerivative] using hs)

private theorem squareRootDerivative_pullback {q : Fin 4 → ℝ}
    (hq : q ∈ chartDomain) (u v : Fin 4 → ℝ) :
    ∑ s, squareRootDerivative q u s * squareRootDerivative q v s =
      fisher (simplexLaw q) (tangentLift u) (tangentLift v) := by
  apply Finset.sum_congr rfl
  intro s _hs
  simp only [squareRootDerivative, ContinuousLinearMap.pi_apply,
    smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  calc
    _ = tangentLift u s * tangentLift v s /
        (Real.sqrt (simplexLaw q s) * Real.sqrt (simplexLaw q s)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [Real.mul_self_sqrt (hq s).le]

private theorem squareRootChart_sphere {q : Fin 4 → ℝ} (hq : q ∈ chartDomain) :
    ∑ s, squareRootChart q s ^ 2 = 4 := by
  calc
    ∑ s, squareRootChart q s ^ 2 = ∑ s, 4 * simplexLaw q s := by
      apply Finset.sum_congr rfl
      intro s _hs
      dsimp [squareRootChart]
      rw [mul_pow, Real.sq_sqrt (hq s).le]
      norm_num
    _ = 4 := by rw [← Finset.mul_sum, simplexLaw_sum]; norm_num

/-- The actual five-mode affine chart has a smooth injective square-root
    differential. Its Euclidean pairing is exactly the existing Fisher form,
    and its pullback is positive on every nonzero four-dimensional direction. -/
theorem five_mode_fisher_chart_immersion :
    IsOpen chartDomain ∧
      (∀ q, q ∈ chartDomain ↔ simplexLaw q ∈ openSimplex) ∧
      (∀ p ∈ openSimplex, ∃! q, q ∈ chartDomain ∧ simplexLaw q = p) ∧
      ContDiffOn ℝ ∞ squareRootChart chartDomain ∧
      ∀ q ∈ chartDomain,
        HasFDerivAt squareRootChart (squareRootDerivative q) q ∧
        Function.Injective (squareRootDerivative q) ∧
        ∑ s, squareRootChart q s ^ 2 = 4 ∧
        (∀ u v, ∑ s, squareRootDerivative q u s * squareRootDerivative q v s =
          fisher (simplexLaw q) (tangentLift u) (tangentLift v)) ∧
        ∀ u : Fin 4 → ℝ, u ≠ 0 → 0 < fisher (simplexLaw q) (tangentLift u) (tangentLift u) := by
  classical
  refine ⟨chartDomain_isOpen, simplexLaw_exact_chart.1, simplexLaw_exact_chart.2,
    squareRootChart_contDiffOn, ?_⟩
  intro q hq
  refine ⟨squareRootChart_hasFDerivAt hq, squareRootDerivative_injective hq,
    squareRootChart_sphere hq, squareRootDerivative_pullback hq, ?_⟩
  intro u hu
  have hne : squareRootDerivative q u ≠ 0 := by
    intro hz
    apply hu
    apply squareRootDerivative_injective hq
    simpa using hz
  obtain ⟨s, hs⟩ : ∃ s, squareRootDerivative q u s ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  rw [← squareRootDerivative_pullback hq]
  exact Finset.sum_pos' (fun s _ => mul_self_nonneg _)
    ⟨s, Finset.mem_univ _, mul_self_pos.2 hs⟩

#print axioms five_mode_fisher_chart_immersion

end D5.S1.Words.AdmissibleWords.FiveModeFisherImmersion
