/- GID: D5/S3/Quantum/Algebra/Approximate/Compression
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/Approximate/Compression
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Taylor correction in the associative endomorphism algebra of a nonassociative product. -/

module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Tactic

/-! The correction is the Taylor construction of Kitaev,
*Almost-idempotent quantum channels and approximate C*-algebras*,
arXiv:2405.02434v2, equations (3.4)--(3.6) and (7.1).
The associative algebra in the correction is an algebra of operators;
no associative multiplication on the underlying target is required. -/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace D5.S3.Quantum.Algebra.Approximate.Compression

open scoped BigOperators Topology

/-- Taylor evaluation of `(1 + z)^(-1/2)` in an associative Banach algebra. -/
def inverseSqrt {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] (d : A) : A :=
  ∑' n : ℕ, Ring.choose (-1 / 2 : ℝ) n • d ^ n

private theorem binomial_summable_norm {A : Type*} [NormedRing A]
    [NormedAlgebra ℝ A] [NormOneClass A] (d : A) (hd : ‖d‖ < 1) (a : ℝ) :
    Summable (fun n : ℕ => ‖Ring.choose a n • d ^ n‖) := by
  have hrad : (‖d‖₊ : ENNReal) < (binomialSeries ℝ a).radius :=
    lt_of_lt_of_le (by exact_mod_cast hd) binomialSeries_radius_ge_one
  have hs := (binomialSeries ℝ a).summable_norm_mul_pow hrad
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_norm] at hs
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (norm_pow_le d n) (norm_nonneg _)) hs

private theorem binomial_mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [NormOneClass A] (d : A) (hd : ‖d‖ < 1) (a b : ℝ) :
    (∑' n : ℕ, Ring.choose a n • d ^ n) *
        (∑' n : ℕ, Ring.choose b n • d ^ n) =
      ∑' n : ℕ, Ring.choose (a + b) n • d ^ n := by
  rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (binomial_summable_norm d hd a) (binomial_summable_norm d hd b)]
  apply tsum_congr
  intro n
  rw [Ring.add_choose_eq n (Commute.all a b), Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [smul_mul_smul_comm, ← pow_add, Finset.mem_antidiagonal.mp hij]

private theorem inverseSqrt_sq {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [NormOneClass A] (d : A) (hd : ‖d‖ < 1) :
    inverseSqrt d * inverseSqrt d = ∑' n : ℕ, (-d) ^ n := by
  unfold inverseSqrt
  rw [binomial_mul d hd]
  apply tsum_congr
  intro n
  norm_num only [show (-1 / 2 : ℝ) + -1 / 2 = -1 by norm_num]
  rw [show (-1 : ℝ) = -(1 : ℝ) by norm_num, Ring.choose_neg', Ring.multichoose_one]
  simp only [Units.smul_def, zsmul_eq_mul, mul_one, Int.cast_negOnePow_natCast]
  rw [← smul_pow, neg_one_smul]


/-- The Taylor inverse square root commutes with every operator commuting with its argument. -/
private theorem commute_inverseSqrt {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (t d : A) (h : Commute t d) : Commute t (inverseSqrt d) := by
  exact Commute.tsum_right t (fun n => (h.pow_right n).smul_right _)

/-- The Taylor expression corrects an almost involution to an exact involution. -/
private theorem corrected_involution_sq {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [NormOneClass A] (t : A) (ht : ‖t ^ 2 - 1‖ < 1) :
    (t * inverseSqrt (t ^ 2 - 1)) ^ 2 = 1 := by
  have hcomm : Commute t (t ^ 2 - 1) := (Commute.refl t).pow_right 2 |>.sub_right (Commute.one_right t)
  have h := commute_inverseSqrt t (t ^ 2 - 1) hcomm
  rw [h.mul_pow, pow_two (inverseSqrt _), inverseSqrt_sq _ ht]
  have hgeom := mul_neg_geom_series (-(t ^ 2 - 1)) (by rw [norm_neg]; exact ht)
  convert hgeom using 1 <;> noncomm_ring

/-- The exact compression associated to a nearly involutive operator. -/
def correction {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] (t : A) : A :=
  (1 / 2 : ℝ) • (1 + t * inverseSqrt (t ^ 2 - 1))

/-- Idempotence is established inside the associative operator algebra. -/
theorem correction_idempotent {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] [NormOneClass A] (t : A) (ht : ‖t ^ 2 - 1‖ < 1) :
    correction t * correction t = correction t := by
  have h := corrected_involution_sq t ht
  unfold correction
  rw [smul_mul_smul_comm]
  have he : (1 + t * inverseSqrt (t ^ 2 - 1)) * (1 + t * inverseSqrt (t ^ 2 - 1)) =
      (2 : ℝ) • (1 + t * inverseSqrt (t ^ 2 - 1)) := by
    rw [pow_two] at h
    simp only [add_mul, mul_add, one_mul, mul_one, h, two_smul]
    abel
  rw [he, smul_smul]
  norm_num

end D5.S3.Quantum.Algebra.Approximate.Compression
