/- GID: D5/S3/Observer/Hankel/ExactGramianSeries
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/ExactGramianSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Actual infinite Gramian series converge, solve Stein equations, and are positive definite under full observation. -/

import D5.S3.Observer.Hankel.BalancedSteinEnergy
import D5.S3.Observer.Hankel.PositiveGramianBalancing
import D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.ExactGramianSeries

open Matrix
open D5.S3.Observer.Hankel.BalancedSteinEnergy
open scoped BigOperators MatrixOrder Matrix.Norms.L2Operator Topology

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The ordinary real matrix quadratic form, using a finite coordinate vector. -/
def quadratic (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ := x ⬝ᵥ M.mulVec x

private def quadraticMap (x : ι → ℝ) : Matrix ι ι ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => quadratic M x
      map_add' := by intro M N; simp [quadratic, add_mulVec, dotProduct_add]
      map_smul' := by intro a M; simp [quadratic, smul_mulVec, dotProduct_smul] }

/-- Congruence of the quadratic form under an actual matrix action. -/
theorem quadratic_congruence (M : Matrix ι ι ℝ) (T : Matrix ι κ ℝ) (x : κ → ℝ) :
    quadratic (Tᴴ * M * T) x = quadratic M (T.mulVec x) := by
  simp only [quadratic, conjTranspose_eq_transpose_of_trivial, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_transpose]

/-- The identity matrix measures the same Euclidean energy as the reduction theorem. -/
@[simp] theorem quadratic_one (x : ι → ℝ) : quadratic (1 : Matrix ι ι ℝ) x = squareSum x := by
  simp [quadratic, squareSum, dotProduct, pow_two]

/-- A diagonal quadratic form is the existing diagonal-energy definition. -/
@[simp] theorem quadratic_diagonal (w x : ι → ℝ) : quadratic (diagonal w) x = energy w x := by
  unfold quadratic energy dotProduct
  apply Finset.sum_congr rfl
  intro i _
  rw [mulVec_diagonal]
  ring

/-- The actual observation Gram term at time k. -/
def observationTerm (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) (k : ℕ) : Matrix ι ι ℝ :=
  (C * A ^ k)ᴴ * (C * A ^ k)

/-- The undiscounted infinite observability Gramian, constructed as a series. -/
def observationGramian (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) : Matrix ι ι ℝ :=
  ∑' k, observationTerm A C k

/-- The controllability Gramian is constructed by the dual observation series. -/
def controlGramian (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) : Matrix ι ι ℝ :=
  observationGramian Aᴴ Bᴴ

/-- An explicit exponential power bound supplies square-summable powers, even
when the single-step operator norm is not below one. -/
theorem power_square_summable_of_bound (A : Matrix ι ι ℝ) (M q : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hb : ∀ k : ℕ, ‖A ^ k‖ ≤ M * q ^ k) :
    Summable (fun k : ℕ => ‖A ^ k‖ ^ 2) := by
  have hq : q ^ 2 < 1 := by nlinarith
  have hs : Summable (fun k : ℕ => M ^ 2 * (q ^ 2) ^ k) :=
    (summable_geometric_of_lt_one (sq_nonneg q) hq).mul_left _
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ hs
  intro k
  have hh := mul_self_le_mul_self (norm_nonneg (A ^ k)) (hb k)
  simpa only [← pow_two, mul_pow, ← pow_mul, Nat.mul_comm] using hh

/-- Operator-norm convergence of the actual Gramian terms. -/
theorem observationTerm_summable (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) : Summable (observationTerm A C) := by
  have hs : Summable (fun k : ℕ => ‖C‖ ^ 2 * ‖A ^ k‖ ^ 2) := hA.mul_left _
  apply Summable.of_norm_bounded hs
  intro k
  rw [observationTerm, l2_opNorm_conjTranspose_mul_self]
  have hh := mul_self_le_mul_self (norm_nonneg (C * A ^ k)) (l2_opNorm_mul C (A ^ k))
  nlinarith [hh]

/-- Taking the adjoint preserves the square-summable-power stability premise. -/
theorem adjoint_power_square_summable (A : Matrix ι ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) :
    Summable (fun k : ℕ => ‖Aᴴ ^ k‖ ^ 2) := by
  simpa only [← conjTranspose_pow, l2_opNorm_conjTranspose] using hA

private theorem term_quadratic (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (x : ι → ℝ) (k : ℕ) :
    quadratic (observationTerm A C k) x = squareSum ((C * A ^ k).mulVec x) := by
  have h := quadratic_congruence (1 : Matrix κ κ ℝ) (C * A ^ k) x
  simpa only [mul_one, quadratic_one, observationTerm] using h

/-- The full quadratic form is exactly the energy of all actual future readouts. -/
theorem observationGramian_energy (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) (x : ι → ℝ) :
    quadratic (observationGramian A C) x = ∑' k, squareSum ((C * A ^ k).mulVec x) := by
  have hs := observationTerm_summable A C hA
  change quadraticMap x (∑' k, observationTerm A C k) = _
  rw [(quadraticMap x).map_tsum hs]
  exact tsum_congr (fun k => term_quadratic A C x k)

/-- The energy series is summable, independently of observability. -/
theorem observation_energy_summable (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) (x : ι → ℝ) :
    Summable (fun k => squareSum ((C * A ^ k).mulVec x)) := by
  have hs := (observationTerm_summable A C hA).mapL (quadraticMap x)
  exact hs.congr (fun k => term_quadratic A C x k)

private theorem observationGramian_hermitian (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) :
    (observationGramian A C).IsHermitian := by
  change star (∑' k, observationTerm A C k) = ∑' k, observationTerm A C k
  rw [tsum_star]
  apply tsum_congr
  intro k
  exact (Matrix.isHermitian_conjTranspose_mul_self (C * A ^ k))

/-- Positivity of the actual series does not require full observation. -/
theorem observationGramian_posSemidef (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) :
    (observationGramian A C).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (observationGramian_hermitian A C)
  intro x
  change 0 ≤ quadratic (observationGramian A C) x
  rw [observationGramian_energy A C hA]
  exact tsum_nonneg (fun _ => squareSum_nonneg _)

/-- Full future observation gives strict positive definiteness of the actual sum.
The hypothesis is joint injectivity of the genuine readouts, not positivity of
a separately supplied matrix. -/
theorem observationGramian_posDef (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hobs : ∀ x : ι → ℝ, (∀ k : ℕ, (C * A ^ k).mulVec x = 0) → x = 0) :
    (observationGramian A C).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (observationGramian_hermitian A C)
  intro x hx
  have hex : ∃ k : ℕ, (C * A ^ k).mulVec x ≠ 0 := by
    by_contra! hh
    exact hx (hobs x hh)
  obtain ⟨k, hk⟩ := hex
  have hpos : 0 < squareSum ((C * A ^ k).mulVec x) := by
    have hp := (dotProduct_star_self_pos_iff).mpr hk
    simpa only [star_trivial, dotProduct, ← pow_two, squareSum] using hp
  change 0 < quadratic (observationGramian A C) x
  rw [observationGramian_energy A C hA]
  exact hpos.trans_le ((observation_energy_summable A C hA x).le_tsum k
    (fun j _ => squareSum_nonneg _))

/-- Exact discrete Lyapunov/Stein equality from splitting the convergent series. -/
theorem observationGramian_stein (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) :
    Aᴴ * observationGramian A C * A + Cᴴ * C = observationGramian A C := by
  have hs := observationTerm_summable A C hA
  have hstep (k : ℕ) : observationTerm A C (k + 1) = Aᴴ * observationTerm A C k * A := by
    simp only [observationTerm, pow_succ, conjTranspose_mul, Matrix.mul_assoc]
  have he := hs.tsum_eq_zero_add
  simp only [observationTerm, pow_zero, mul_one] at he
  have ht : (∑' k, observationTerm A C (k + 1)) =
      Aᴴ * observationGramian A C * A := by
    simp_rw [hstep]
    rw [(hs.mul_left Aᴴ).tsum_mul_right A, hs.tsum_mul_left Aᴴ]
    rfl
  change observationGramian A C = Cᴴ * C + ∑' k, observationTerm A C (k + 1) at he
  rw [ht] at he
  exact (add_comm _ _).trans he.symm

/-- Exact control Stein equality for the actual dual Gramian series. -/
theorem controlGramian_stein (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) :
    A * controlGramian A B * Aᴴ + B * Bᴴ = controlGramian A B := by
  simpa only [controlGramian, conjTranspose_conjTranspose] using
    observationGramian_stein Aᴴ Bᴴ (adjoint_power_square_summable A hA)

/-- The control construction is the usual forward-reachability Gramian series. -/
theorem controlGramian_series (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ) :
    controlGramian A B = ∑' k : ℕ, (A ^ k * B) * (A ^ k * B)ᴴ := by
  unfold controlGramian observationGramian
  apply tsum_congr
  intro k
  simp only [observationTerm, ← conjTranspose_pow, ← conjTranspose_mul,
    conjTranspose_conjTranspose]

/-- Full dual observation (equivalently controllability in finite dimension)
proves positive definiteness of the actual control Gramian. -/
theorem controlGramian_posDef (A : Matrix ι ι ℝ) (B : Matrix ι κ ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2))
    (hcon : ∀ x : ι → ℝ, (∀ k : ℕ, (Bᴴ * Aᴴ ^ k).mulVec x = 0) → x = 0) :
    (controlGramian A B).PosDef :=
  observationGramian_posDef Aᴴ Bᴴ (adjoint_power_square_summable A hA) hcon


private theorem euclidean_mul {η : Type} [Fintype η] [DecidableEq η]
    (M : Matrix ι κ ℝ) (N : Matrix κ η ℝ) :
    (M * N).toEuclideanLin = M.toEuclideanLin.comp N.toEuclideanLin := by
  ext x i
  exact congrFun (Matrix.mulVec_mulVec M N (WithLp.ofLp x)).symm i

/-- The actual matrix series represents the repository's undiscounted
observability Gramian on Euclidean state coordinates. This identifies the
existing owner rather than silently introducing a second operator Gramian. -/
theorem observationGramian_eq_existing (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ) :
    Matrix.toEuclideanCLM (observationGramian A C) =
      D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity.discountedObservabilityGramian
        A.toEuclideanLin C.toEuclideanLin 1 := by
  let e : Matrix ι ι ℝ ≃L[ℝ] (EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :=
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := ι)).toLinearEquiv.toContinuousLinearEquiv
  change e (∑' k, observationTerm A C k) = _
  rw [e.map_tsum]
  apply tsum_congr
  intro k
  have hp : (A ^ k).toEuclideanLin = A.toEuclideanLin ^ k := by
    have he := congrArg ContinuousLinearMap.toLinearMap (map_pow Matrix.toEuclideanCLM A k)
    exact he
  have hm : (C * A ^ k).toEuclideanLin = C.toEuclideanLin.comp (A.toEuclideanLin ^ k) := by
    rw [euclidean_mul, hp]
  have hl : (observationTerm A C k).toEuclideanLin =
      (C.toEuclideanLin.comp (A.toEuclideanLin ^ k)).adjoint.comp
        (C.toEuclideanLin.comp (A.toEuclideanLin ^ k)) := by
    rw [observationTerm, euclidean_mul, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hm]
  have hc := congrArg LinearMap.toContinuousLinearMap hl
  simpa [e, D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity.discountedGramianTerm,
    D5.S3.Observer.Linear.DiscountedObservabilityGramianPositivity.observedIterate,
    ← LinearMap.adjoint_toContinuousLinearMap] using hc

/-- The finite observation window and the exact terminal-state remainder
partition the actual infinite Gramian. -/
theorem observationGramian_finite_remainder (A : Matrix ι ι ℝ) (C : Matrix κ ι ℝ)
    (hA : Summable (fun k : ℕ => ‖A ^ k‖ ^ 2)) (N : ℕ) :
    observationGramian A C =
      (∑ k ∈ Finset.range N, observationTerm A C k) +
        (A ^ N)ᴴ * observationGramian A C * A ^ N := by
  have hs := observationTerm_summable A C hA
  have he := hs.sum_add_tsum_nat_add N
  have ht : (∑' k : ℕ, observationTerm A C (k + N)) =
      (A ^ N)ᴴ * observationGramian A C * A ^ N := by
    have heq (k : ℕ) : observationTerm A C (k + N) =
        (A ^ N)ᴴ * observationTerm A C k * A ^ N := by
      simp only [observationTerm, pow_add, conjTranspose_mul, Matrix.mul_assoc]
    simp_rw [heq]
    rw [(hs.mul_left (A ^ N)ᴴ).tsum_mul_right (A ^ N), hs.tsum_mul_left (A ^ N)ᴴ]
    rfl
  rw [ht] at he
  exact he.symm

#print axioms observationGramian_posDef
#print axioms observationGramian_stein
#print axioms controlGramian_stein

end D5.S3.Observer.Hankel.ExactGramianSeries
