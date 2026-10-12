/- GID: D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization
   generality: I
   mirror-B: D5/B/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.claim; result=D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.result; claim=D5/S3/Analytic/OptimalRecovery/ChebyshevCenterRegularization.claim
   digest: A real two-dimensional feasible set has a Chebyshev center that minimizes no strictly weighted quadratic regularizer. -/

/- Source: Foucart–Liao, arXiv:2310.09677, §5 Question 2.
   admission_basis: open-problem-resolution (#15463; Refuted)
   escape_witness: none
   Direct frozen dependencies: none (pinned Mathlib only).
   Definitions:
     feasible: proof_shape definition; consumers=claim, feasible_coordinates
     IsChebyshevCenter: proof_shape definition; consumers=claim, center_certificate
     IsRegularizer: proof_shape definition; consumers=claim, not_regularizer
     claim: proof_shape definition; consumer=result
     point: proof_shape definition; consumers=projection, measurement, datum, center,
       contacts, not_regularizer
     projection: proof_shape definition; consumers=feasible_coordinates, not_regularizer, result
     measurement: proof_shape definition; consumers=feasible_coordinates, not_regularizer, result
     datum: proof_shape definition; consumers=feasible_coordinates, not_regularizer, result
     center: proof_shape definition; consumers=containment, center_certificate,
       not_regularizer, result
   Per-declaration proof_shape and live consumers:
     norm_square: bind-only; consumers=feasible_coordinates, containment,
       bounded, center_certificate, not_regularizer
     feasible_coordinates: bind-only; consumers=contacts, containment, bounded
     contacts: bind-only; consumers=center_certificate, result
     containment: content; consumer=center_certificate
     bounded: bind-only; consumer=result
     center_certificate: content; consumer=result
     not_regularizer: bind-only; consumer=result
     result: content; designated refutation conclusion
   The containment certificate uses a polynomial identity and nonnegative
   multipliers on the feasible set. The three contact points certify optimality. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open scoped RealInnerProductSpace

namespace D5.S3.Analytic.OptimalRecovery.ChebyshevCenterRegularization

/-- The feasible set `{f : ‖P f‖ ≤ ε, ‖y − Λ f‖ ≤ η}`. -/
def feasible {n m : ℕ} (P : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (Λ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin m)) (ε η : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {f | ‖P f‖ ≤ ε ∧ ‖y - Λ f‖ ≤ η}

/-- `c` is a Chebyshev center of `C`: its worst-case distance is no larger than any other point's. -/
def IsChebyshevCenter {E : Type*} [NormedAddCommGroup E] (C : Set E) (c : E) : Prop :=
  ∀ c' : E, ∀ M : ℝ, (∀ f ∈ C, ‖f - c'‖ ≤ M) → ∀ f ∈ C, ‖f - c‖ ≤ M

/-- `c` minimizes `(1 − τ)‖P f‖² + τ‖y − Λ f‖²`. -/
def IsRegularizer {n m : ℕ} (P : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (Λ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin m)) (τ : ℝ) (c : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ f, (1 - τ) * ‖P c‖ ^ 2 + τ * ‖y - Λ c‖ ^ 2 ≤
    (1 - τ) * ‖P f‖ ^ 2 + τ * ‖y - Λ f‖ ^ 2

def claim : Prop :=
  ∀ (n m : ℕ) (P : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (Λ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (y : EuclideanSpace ℝ (Fin m)) (ε η : ℝ), 0 < ε → 0 < η →
    (feasible P Λ y ε η).Nonempty → Bornology.IsBounded (feasible P Λ y ε η) →
    ∀ c, IsChebyshevCenter (feasible P Λ y ε η) c →
      ∃ τ ∈ Set.Ioo (0 : ℝ) 1, IsRegularizer P Λ y τ c

private def point (x z : ℝ) : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![x, z]

private def projection : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun f := point (f 0) 0
  map_add' f h := by ext i; fin_cases i <;> simp [point]
  map_smul' a f := by ext i; fin_cases i <;> simp [point]

private def measurement : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun f := point ((f 0 - f 1) / 2) (f 1)
  map_add' f h := by
    ext i
    fin_cases i
    · simp [point]; ring
    · simp [point]
  map_smul' a f := by
    ext i
    fin_cases i
    · simp [point]; ring
    · simp [point]

private def datum : EuclideanSpace ℝ (Fin 2) := point 1 0
private def center : EuclideanSpace ℝ (Fin 2) := point (3/5) (-1/5)

private lemma norm_square (f : EuclideanSpace ℝ (Fin 2)) :
    ‖f‖ ^ 2 = (f 0) ^ 2 + (f 1) ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

private lemma feasible_coordinates (f : EuclideanSpace ℝ (Fin 2)) :
    f ∈ feasible projection measurement datum 1 1 ↔
      (f 0) ^ 2 ≤ 1 ∧ (f 0 - f 1 - 2) ^ 2 + 4 * (f 1) ^ 2 - 4 ≤ 0 := by
  have hp : ‖projection f‖ ^ 2 = (f 0) ^ 2 := by
    rw [norm_square]; simp [projection, point]
  have hm : ‖datum - measurement f‖ ^ 2 =
      (1 - (f 0 - f 1) / 2) ^ 2 + (f 1) ^ 2 := by
    rw [norm_square]; simp [measurement, datum, point]
  change (‖projection f‖ ≤ 1 ∧ ‖datum - measurement f‖ ≤ 1) ↔ _
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor
    · nlinarith [norm_nonneg (projection f)]
    · nlinarith [norm_nonneg (datum - measurement f)]
  · rintro ⟨h₁, h₂⟩
    constructor
    · nlinarith [norm_nonneg (projection f)]
    · nlinarith [norm_nonneg (datum - measurement f)]

private lemma contacts :
    point 1 (3/5) ∈ feasible projection measurement datum 1 1 ∧
    point (-1/5) (-3/5) ∈ feasible projection measurement datum 1 1 ∧
    point 1 (-1) ∈ feasible projection measurement datum 1 1 := by
  constructor
  · rw [feasible_coordinates]; norm_num [point]
  constructor <;> rw [feasible_coordinates] <;> norm_num [point]

private lemma containment (f : EuclideanSpace ℝ (Fin 2))
    (hf : f ∈ feasible projection measurement datum 1 1) : ‖f - center‖ ^ 2 ≤ 4/5 := by
  obtain ⟨hx, hg⟩ := (feasible_coordinates f).mp hf
  have hx₁ : f 0 ≤ 1 := by nlinarith [sq_nonneg (f 0 - 1)]
  have hzsq : (f 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (f 0 - f 1 - 2)]
  have hz : -1 ≤ f 1 := by nlinarith [sq_nonneg (f 1 + 1)]
  have hden : 0 < 4 - f 0 + f 1 := by linarith
  have hweight : 0 ≤ 17 - 11 * f 0 + 2 * f 1 := by linarith
  have hleft := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx₁)
    (sq_nonneg (4 - f 0 + 7 * f 1))
  have hright := mul_nonpos_of_nonneg_of_nonpos hweight hg
  have hid :
      10 * (4 - f 0 + f 1) * ((f 0 - 3/5)^2 + (f 1 + 1/5)^2 - 4/5) =
      (f 0 - 1) * (4 - f 0 + 7 * f 1)^2 +
        (17 - 11 * f 0 + 2 * f 1) * ((f 0 - f 1 - 2)^2 + 4*(f 1)^2 - 4) := by ring
  have hprod : 10 * (4 - f 0 + f 1) *
      ((f 0 - 3/5)^2 + (f 1 + 1/5)^2 - 4/5) ≤ 0 := by
    rw [hid]; exact add_nonpos hleft hright
  have hq : (f 0 - 3/5)^2 + (f 1 + 1/5)^2 - 4/5 ≤ 0 := by
    by_contra hq
    have hpos := mul_pos (by linarith : 0 < 10 * (4 - f 0 + f 1)) (lt_of_not_ge hq)
    linarith
  rw [norm_square]
  simp [center, point]
  nlinarith

private lemma bounded : Bornology.IsBounded (feasible projection measurement datum 1 1) := by
  apply (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))).mpr
  refine ⟨2, fun f hf => ?_⟩
  obtain ⟨hx, hg⟩ := (feasible_coordinates f).mp hf
  have hz : (f 1)^2 ≤ 1 := by nlinarith [sq_nonneg (f 0 - f 1 - 2)]
  rw [Metric.mem_closedBall, dist_zero_right]
  have hn := norm_square f
  nlinarith [norm_nonneg f]

private lemma center_certificate :
    IsChebyshevCenter (feasible projection measurement datum 1 1) center := by
  intro c' M hM f hf
  obtain ⟨hA, hB, hD⟩ := contacts
  have ha := hM _ hA
  have hb := hM _ hB
  have hd := hM _ hD
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans ha
  have ha₂ : ‖point 1 (3/5) - c'‖^2 ≤ M^2 := by
    nlinarith [norm_nonneg (point 1 (3/5) - c')]
  have hb₂ : ‖point (-1/5) (-3/5) - c'‖^2 ≤ M^2 := by
    nlinarith [norm_nonneg (point (-1/5) (-3/5) - c')]
  have hd₂ : ‖point 1 (-1) - c'‖^2 ≤ M^2 := by
    nlinarith [norm_nonneg (point 1 (-1) - c')]
  rw [norm_square] at ha₂ hb₂ hd₂
  simp [point] at ha₂ hb₂ hd₂
  have hcontact :
      (5/12:ℝ) * ((1 - c' 0)^2 + (3/5 - c' 1)^2) +
      (1/3:ℝ) * ((-1/5 - c' 0)^2 + (-3/5 - c' 1)^2) +
      (1/4:ℝ) * ((1 - c' 0)^2 + (-1 - c' 1)^2) =
      4/5 + (c' 0 - 3/5)^2 + (c' 1 + 1/5)^2 := by ring
  have hbound : (4/5:ℝ) ≤ M^2 := by
    nlinarith [sq_nonneg (c' 0 - 3/5), sq_nonneg (c' 1 + 1/5)]
  have hcontained := containment f hf
  nlinarith [norm_nonneg (f - center)]

private lemma not_regularizer (τ : ℝ) (hτ : 0 < τ) :
    ¬ IsRegularizer projection measurement datum τ center := by
  intro h
  have hv := h (point (3/5) (-7/25))
  simp only [norm_square] at hv
  norm_num [projection, measurement, datum, center, point] at hv
  nlinarith

theorem result : ¬ claim := by
  intro h
  obtain ⟨τ, hτ, hr⟩ := h 2 2 projection measurement datum 1 1
    (by norm_num) (by norm_num) ⟨point 1 (3/5), contacts.1⟩ bounded center center_certificate
  exact not_regularizer τ hτ.1 hr

end D5.S3.Analytic.OptimalRecovery.ChebyshevCenterRegularization
