/- GID: D5/S3/QuadraticForms/ThreeWayPositiveKernel
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ThreeWayPositiveKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original three-way law supplies a positive complex Gram kernel. -/

module

public import D5.S3.QuadraticForms.ThreeWayBalance
public import Mathlib.Analysis.InnerProductSpace.Reproducing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Topology.Instances.Rat
import Mathlib.Tactic

/-! Positive Gram kernels derived on the original additive group. -/

public section

noncomputable section

namespace D5.S3.QuadraticForms.ThreeWayPositiveKernel

open scoped BigOperators ComplexConjugate ComplexOrder
open Finset

private theorem rational_gram_nonneg {A ι : Type*} [AddCommGroup A] [Fintype ι]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (hB : ∀ x, 0 ≤ B x x)
    (x : ι → A) (a : ι → ℚ) :
    0 ≤ ∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * B (x i) (x j) := by
  classical
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) a
  choose n hn using hd
  have hd0 : (d : ℤ) ≠ 0 := nonZeroDivisors.ne_zero d.property
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
  have hnR (i) : (n i : ℝ) = (d : ℝ) * (a i : ℝ) := by
    have h := hn i
    change (n i : ℚ) = (d : ℤ) • a i at h
    exact_mod_cast h
  have hp := hB (∑ i, n i • x i)
  have he : B (∑ i, n i • x i) (∑ i, n i • x i) =
      (d : ℝ)^2 * (∑ i, ∑ j, (a i : ℝ) * (a j : ℝ) * B (x i) (x j)) := by
    simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
      zsmul_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [hnR]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he] at hp
  exact nonneg_of_mul_nonneg_right hp (sq_pos_of_ne_zero hdR)

private theorem real_gram_nonneg {A ι : Type*} [AddCommGroup A] [Fintype ι]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (hB : ∀ x, 0 ≤ B x x)
    (x : ι → A) (a : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, a i * a j * B (x i) (x j) := by
  have hd : DenseRange (fun a : ι → ℚ => fun i => (a i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  exact hd.induction_on a (isClosed_le continuous_const (by fun_prop))
    (fun c => rational_gram_nonneg B hB x c)

private def gram {A : Type*} [AddCommGroup A]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (U : A →+ A) (x y : A) : ℂ :=
  ⟨B x y, (B x y + 2 * B (U x) y) / Real.sqrt 3⟩

private theorem gram_hermitian {A : Type*} [AddCommGroup A]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (U : A →+ A)
    (hs : ∀ x y, B x y = B y x)
    (ht : ∀ x y, B (U x) y + B x (U y) = -B x y) :
    Matrix.IsHermitian (gram B U) := by
  ext x y
  apply Complex.ext
  · change B y x = B x y
    exact hs y x
  · change -((B y x + 2 * B (U y) x) / Real.sqrt 3) =
      (B x y + 2 * B (U x) y) / Real.sqrt 3
    rw [← neg_div, hs y x, hs (U y) x]
    congr 1
    linarith [ht x y]

set_option maxHeartbeats 1600000 in
-- The expanded complex-to-real coefficient identity requires polynomial normalization.
private theorem complex_gram_nonneg {A ι : Type*} [AddCommGroup A] [Fintype ι]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (U : A →+ A)
    (hB : ∀ x, 0 ≤ B x x)
    (hv : ∀ x y, B (U x) (U y) = B x y)
    (ht : ∀ x y, B (U x) y + B x (U y) = -B x y)
    (x : ι → A) (z : ι → ℂ) :
    0 ≤ (∑ i, ∑ j, conj (z i) * gram B U (x i) (x j) * z j).re := by
  classical
  let y : ι ⊕ ι → A := Sum.elim x (fun i => U (x i))
  let c : ι ⊕ ι → ℝ := Sum.elim
    (fun i => (z i).re + (z i).im / Real.sqrt 3)
    (fun i => 2 * (z i).im / Real.sqrt 3)
  have hp := real_gram_nonneg B hB y c
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have he (i j : ι) :
      (conj (z i) * gram B U (x i) (x j) * z j).re =
        c (.inl i) * c (.inl j) * B (x i) (x j) +
        c (.inl i) * c (.inr j) * B (x i) (U (x j)) +
        c (.inr i) * c (.inl j) * B (U (x i)) (x j) +
        c (.inr i) * c (.inr j) * B (U (x i)) (U (x j)) := by
    have ht' : B (x i) (U (x j)) = -B (x i) (x j) - B (U (x i)) (x j) := by
      linarith [ht (x i) (x j)]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      gram, c, Sum.elim_inl, Sum.elim_inr]
    rw [hv, ht']
    field_simp
    ring_nf
    simp only [hsq]
    ring
  simp only [Complex.re_sum, he, Finset.sum_add_distrib] 
  simp only [y, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_add_distrib] at hp
  convert hp using 1
  ring

private theorem gram_posSemidef {A : Type*} [AddCommGroup A]
    (B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ) (U : A →+ A)
    (hB : ∀ x, 0 ≤ B x x) (hs : ∀ x y, B x y = B y x)
    (hv : ∀ x y, B (U x) (U y) = B x y)
    (ht : ∀ x y, B (U x) y + B x (U y) = -B x y) :
    Matrix.PosSemidef (gram B U) := by
  classical
  have hh := gram_hermitian B U hs ht
  refine ⟨hh, ?_⟩
  intro z
  apply Complex.nonneg_iff.mpr
  constructor
  · have hp := complex_gram_nonneg B U hB hv ht (fun i : z.support => (i : A))
      (fun i => z i)
    have hinner (i : A) : (∑ j : z.support, conj (z i) * gram B U i j * z j) =
        ∑ j ∈ z.support, conj (z i) * gram B U i j * z j :=
      Finset.sum_coe_sort z.support
        (fun j : A => conj (z i) * gram B U i j * z j)
    simp_rw [hinner] at hp
    have houter : (∑ i : z.support, ∑ j ∈ z.support,
        conj (z i) * gram B U i j * z j) =
        ∑ i ∈ z.support, ∑ j ∈ z.support, conj (z i) * gram B U i j * z j :=
      Finset.sum_coe_sort z.support
        (fun i : A => ∑ j ∈ z.support, conj (z i) * gram B U i j * z j)
    rw [houter] at hp
    simpa only [Finsupp.sum, starRingEnd_apply] using hp
  · have hstar : star (z.sum fun i zi => z.sum fun j zj => star zi * gram B U i j * zj) =
        (z.sum fun i zi => z.sum fun j zj => star zi * gram B U i j * zj) := by
      simp only [star_finsuppSum, Pi.star_apply, star_mul, star_star]
      rw [Finsupp.sum_comm]
      unfold Finsupp.sum
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (z i) * (star (gram B U j i) * z j) =
        star (z i) * gram B U i j * z j
      rw [hh.apply]
      ring
    have hi := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at hi
    simp only [Complex.star_def]
    linarith

/-- The scalar Gram entry forced by the three-way law, with inner products
conjugate-linear in the first label. -/
@[expose] def complexGram {A : Type*} [AddCommGroup A] (U : A →+ A) (q : A → ℝ)
    (x y : A) : ℂ :=
  let b : A → A → ℝ := fun x y => (q (x + y) - q (x - y)) / 4
  ⟨b x y, (b x y + 2 * b (U x) y) / Real.sqrt 3⟩

/-- The nonnegative universal three-way law on an arbitrary additive group supplies
its forced complex positive kernel, without any scalar or topological structure on A. -/
theorem three_way_positive_kernel {A : Type*} [AddCommGroup A]
    (U : A →+ A) (q : A → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hT : ∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y) :
    Matrix.PosSemidef (complexGram U q) ∧
    (∀ x, complexGram U q x x = (q x : ℂ)) ∧
    (∀ x y z, complexGram U q (x + y) z =
      complexGram U q x z + complexGram U q y z) := by
  obtain ⟨hi, hD, _, hp, Q, hQ⟩ :=
    ThreeWayBalance.three_way_quadratic_structure U q hq hT
  let B : A →ₗ[ℤ] A →ₗ[ℤ] ℝ := (1 / 2 : ℝ) • Q.polarBilin
  have hb (x y : A) : B x y = (q (x + y) - q (x - y)) / 4 := by
    change (1 / 2 : ℝ) * (Q (x + y) - Q x - Q y) = _
    rw [hQ, hQ, hQ]
    linarith [hp x y]
  have hb' (x y : A) : B x y = (q (x + y) - q x - q y) / 2 := by
    change (1 / 2 : ℝ) * (Q (x + y) - Q x - Q y) = _
    rw [hQ, hQ, hQ]
    ring
  have hs (x y : A) : B x y = B y x := by
    rw [hb', hb', add_comm x y]
    ring
  have hd (x : A) : B x x = q x := by
    change (1 / 2 : ℝ) * QuadraticMap.polar Q x x = _
    rw [Q.polar_self, hQ]
    simp
  have hv (x y : A) : B (U x) (U y) = B x y := by
    rw [hb', hb', ← map_add, hi, hi, hi]
  have hDz (x y : A) : B x (y + U y + U (U y)) = 0 := by
    rw [hb', hD, show q (y + U y + U (U y)) = 0 from by
      have h := hD 0 y
      have hzero : q 0 = 0 := (hQ 0).symm.trans Q.map_zero
      simpa only [zero_add, hzero] using h]
    ring
  have ht (x y : A) : B (U x) y + B x (U y) = -B x y := by
    have h := hDz (U x) y
    simp only [map_add] at h
    rw [hv, hv x (U y)] at h
    linarith
  have hg : complexGram U q = gram B U := by
    funext x y
    simp only [complexGram, gram, hb]
  rw [hg]
  refine ⟨gram_posSemidef B U (fun x => by rw [hd]; exact hq x) hs hv ht, ?_, ?_⟩
  · intro x
    apply Complex.ext
    · exact hd x
    · change (B x x + 2 * B (U x) x) / Real.sqrt 3 = 0
      have h := ht x x
      rw [← hs (U x) x] at h
      have hz : B x x + 2 * B (U x) x = 0 := by linarith
      rw [hz, zero_div]
  · intro x y z
    apply Complex.ext
    · simp [gram, map_add]
    · simp [gram, map_add]
      ring

end D5.S3.QuadraticForms.ThreeWayPositiveKernel
