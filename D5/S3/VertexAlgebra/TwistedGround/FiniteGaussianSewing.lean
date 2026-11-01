/- GID: D5/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FiniteGaussianSewing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite polynomial rows of the actual block Gaussian coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.FiniteSqueezedVacuum
import D5.S3.VertexAlgebra.TwistedGround.InfiniteGaussianFock
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! Classical bilinear Gaussian/Fock coefficient calculus. External blocks
are arbitrary. Only the shared blocks enter the analytic estimates. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Ring

namespace D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
open MvPolynomial
open FactorialFockQuadraticEstimate
open FactorialFockMetric (weight)
open FiniteSqueezedVacuum

universe u v w
variable {H : Type u} [Fintype H] [DecidableEq H]

/-- Coefficients of a finite polynomial times the actual native Gaussian.
Every monomial acts by the original creation shift, without factorial rescaling. -/
def polynomialGaussian (A : Matrix H H ℂ) :
    MvPolynomial H ℂ →ₗ[ℂ] ((H →₀ ℕ) → ℂ) :=
  (Finsupp.lsum ℂ (fun α =>
    LinearMap.toSpanSingleton ℂ _ (created α (gaussianCoefficient A)))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

private theorem polynomialGaussian_monomial (A : Matrix H H ℂ)
    (α : H →₀ ℕ) (c : ℂ) :
    polynomialGaussian A (monomial α c) = c • created α (gaussianCoefficient A) := by
  simp [polynomialGaussian, monomial, AddMonoidAlgebra.lsingle,
    Finsupp.lsum_single, LinearMap.toSpanSingleton_apply]

private theorem polynomialGaussian_one (A : Matrix H H ℂ) :
    polynomialGaussian A 1 = gaussianCoefficient A := by
  rw [one_def, polynomialGaussian_monomial, one_smul, created_zero]

private theorem polynomialGaussian_X_mul (A : Matrix H H ℂ)
    (i : H) (p : MvPolynomial H ℂ) :
    polynomialGaussian A (X i * p) = created (Finsupp.single i 1) (polynomialGaussian A p) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [X, monomial_mul_monomial, one_mul, polynomialGaussian_monomial,
      polynomialGaussian_monomial, ← created_add]
    funext d
    by_cases h : Finsupp.single i 1 ≤ d <;> simp [created, h]
  | add p q hp hq =>
    rw [mul_add, map_add, hp, hq, map_add]
    funext d
    by_cases h : Finsupp.single i 1 ≤ d <;> simp [created, h]

private theorem polynomialGaussian_square_summable (A : Matrix H H ℂ)
    (hsym : ∀ i j, A i j = A j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1) (p : MvPolynomial H ℂ) :
    Summable (fun n : H →₀ ℕ => (weight n : ℝ) * ‖polynomialGaussian A p n‖ ^ 2) := by
  induction p using MvPolynomial.induction_on' with
  | monomial α c =>
    convert (created_square_summable A hsym hA α).mul_left (‖c‖ ^ 2) using 1
    funext n
    simp only [polynomialGaussian_monomial, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    ring
  | add p q hp hq =>
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ ((hp.add hq).mul_left 2)
    intro n
    simp only [map_add, Pi.add_apply]
    have hn := norm_add_le (polynomialGaussian A p n) (polynomialGaussian A q n)
    have hsq : ‖polynomialGaussian A p n + polynomialGaussian A q n‖ ^ 2 ≤
        2 * (‖polynomialGaussian A p n‖ ^ 2 + ‖polynomialGaussian A q n‖ ^ 2) := by
      nlinarith [sq_nonneg (‖polynomialGaussian A p n‖ - ‖polynomialGaussian A q n‖),
        norm_nonneg (polynomialGaussian A p n + polynomialGaussian A q n)]
    nlinarith [mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (weight n))]

/-- Actual external row of a native Gaussian block matrix. -/
def row {X : Type v} [Fintype X] [DecidableEq X]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) (d : X →₀ ℕ) (n : H →₀ ℕ) : ℂ :=
  gaussianCoefficient K (d.sumElim n)

private theorem row_zero {X : Type v} [Fintype X] [DecidableEq X]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) :
    row K 0 = gaussianCoefficient (fun i j => K (.inr i) (.inr j)) := by
  funext n
  have h := InfiniteGaussianFock.gaussianCoefficient_enlarge K Sum.inr Sum.inr_injective n
  simpa [row, Finsupp.sumElim_eq_add] using h

private theorem row_step {X : Type v} [Fintype X] [DecidableEq X]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ)
    (hsym : ∀ i j, K i j = K j i) (d : X →₀ ℕ) (i : X) (n : H →₀ ℕ) :
    (d i + 1 : ℂ) * row K (d + Finsupp.single i 1) n =
      (∑ j, K (.inl i) (.inl j) *
        (if d j = 0 then 0 else row K (d - Finsupp.single j 1) n)) +
      ∑ j, K (.inl i) (.inr j) * created (Finsupp.single j 1) (row K d) n := by
  have hadd : d.sumElim n + Finsupp.single (.inl i) 1 =
      (d + Finsupp.single i 1).sumElim n := by
    ext (j | j) <;> simp [Finsupp.sumElim_apply]
  have hleft (j : X) : d.sumElim n - Finsupp.single (.inl j) 1 =
      (d - Finsupp.single j 1).sumElim n := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.tsub_apply]
  have hright (j : H) : d.sumElim n - Finsupp.single (.inr j) 1 =
      d.sumElim (n - Finsupp.single j 1) := by
    ext (k | k) <;> simp [Finsupp.sumElim_apply, Finsupp.tsub_apply]
  have h := congrFun (gaussian_annihilate K hsym (.inl i)) (d.sumElim n)
  simpa only [annihilate, Finsupp.sumElim_inl, hadd, Fintype.sum_sum_type,
    created_single, Finsupp.sumElim_inr, hleft, hright, row] using h

/-- Every fixed external row is a finite polynomial times its shared native
Gaussian, for arbitrary symmetric full matrices. No full-block contraction
or mixed-block bound is imposed, and the external coefficient is ordinary. -/
theorem row_polynomial {X : Type v} [Fintype X] [DecidableEq X]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ)
    (hsym : ∀ i j, K i j = K j i) (d : X →₀ ℕ) :
    ∃ p : MvPolynomial H ℂ,
      polynomialGaussian (fun i j => K (.inr i) (.inr j)) p = row K d := by
  classical
  let A : Matrix H H ℂ := fun i j => K (.inr i) (.inr j)
  have go : ∀ m (e : X →₀ ℕ), e.degree = m →
      ∃ p : MvPolynomial H ℂ, polynomialGaussian A p = row K e := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro e he
      by_cases hz : e = 0
      · subst e
        exact ⟨1, (polynomialGaussian_one A).trans (row_zero K).symm⟩
      obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
        by_contra h
        apply hz
        ext i
        simpa using not_exists.mp h i
      let r := e - Finsupp.single i 1
      have hre : r + Finsupp.single i 1 = e := Finsupp.sub_add_single_one_cancel hi
      have hrd : r.degree < m := by
        have h := congrArg Finsupp.degree hre
        simp only [Finsupp.degree_add, Finsupp.degree_single] at h
        omega
      obtain ⟨p, hp⟩ := ih r.degree hrd r rfl
      have hj (j : X) : (r - Finsupp.single j 1).degree < m :=
        (Finsupp.degree_mono tsub_le_self).trans_lt hrd
      choose q hq using fun j : X => ih _ (hj j) (r - Finsupp.single j 1) rfl
      let q' : X → MvPolynomial H ℂ := fun j => if r j = 0 then 0 else q j
      refine ⟨(r i + 1 : ℂ)⁻¹ • ((∑ j, K (.inl i) (.inl j) • q' j) +
        ∑ j, K (.inl i) (.inr j) • (X j * p)), ?_⟩
      have hn : (r i + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (r i)
      rw [map_smul, map_add, map_sum, map_sum]
      simp_rw [map_smul, polynomialGaussian_X_mul, hp]
      funext n
      simp only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul]
      have hq' (j : X) : polynomialGaussian A (q' j) n =
          if r j = 0 then 0 else row K (r - Finsupp.single j 1) n := by
        by_cases h : r j = 0 <;> simp [q', h, hq]
      simp_rw [hq']
      rw [← row_step K hsym r i n, hre]
      exact inv_mul_cancel_left₀ hn _
  exact go d.degree d rfl

/-- Genuine absolute summability of the all-occupation factorial contraction
of two finite polynomial insertions, using only strict shared contractions. -/
theorem polynomial_pair_norm_summable (A B : Matrix H H ℂ)
    (hAsym : ∀ i j, A i j = A j i) (hBsym : ∀ i j, B i j = B j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) B‖ < 1)
    (p q : MvPolynomial H ℂ) :
    Summable (fun n : H →₀ ℕ => ‖(weight n : ℂ) *
      polynomialGaussian A p n * polynomialGaussian B q n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    _ ((polynomialGaussian_square_summable A hAsym hA p).add
      (polynomialGaussian_square_summable B hBsym hB q))
  intro n
  simp only [norm_mul, Complex.norm_natCast]
  have hsq := sq_nonneg (‖polynomialGaussian A p n‖ - ‖polynomialGaussian B q n‖)
  have hw : 0 ≤ (weight n : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_nonneg hw hsq]

/-- Absolute convergence for actual arbitrary external Gaussian rows. -/
theorem row_pair_norm_summable {X : Type v} {Y : Type w}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (K : Matrix (X ⊕ H) (X ⊕ H) ℂ) (L : Matrix (Y ⊕ H) (Y ⊕ H) ℂ)
    (hK : ∀ i j, K i j = K j i) (hL : ∀ i j, L i j = L j i)
    (hA : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => K (.inr i) (.inr j))‖ < 1)
    (hB : ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (fun i j => L (.inr i) (.inr j))‖ < 1)
    (d : X →₀ ℕ) (e : Y →₀ ℕ) :
    Summable (fun n : H →₀ ℕ => ‖(weight n : ℂ) *
      gaussianCoefficient K (d.sumElim n) * gaussianCoefficient L (e.sumElim n)‖) := by
  obtain ⟨p, hp⟩ := row_polynomial K hK d
  obtain ⟨q, hq⟩ := row_polynomial L hL e
  simpa only [hp, hq, row] using polynomial_pair_norm_summable _ _
    (fun i j => hK (.inr i) (.inr j)) (fun i j => hL (.inr i) (.inr j)) hA hB p q

end D5.S3.VertexAlgebra.TwistedGround.FiniteGaussianSewing
