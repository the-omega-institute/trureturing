/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicAnalyticLaurentBridge
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicAnalyticLaurentBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Complete Laurent products identify double-contour coefficients with the independently defined formal coefficients. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicAnalyticCoefficientBridge
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
The substitution x = a v makes a times either original kernel regular in
both variables. All sums below use the usual complex topology. The auxiliary
power series are used only to calculate coefficients of the original
LaurentSeries; they do not change the kernels or their annular integrals.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology ENNReal
open Filter Metric Set MeasureTheory

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicAnalyticLaurentBridge

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open OriginalGaussianCubicKernel OriginalGaussianCubicAnalytic
open OriginalGaussianCubicAnalyticCoefficientBridge

private abbrev PS := PowerSeries ℂ
private abbrev BPS := PowerSeries PS
private abbrev inclusion : PS →+* LaurentSeries ℂ := HahnSeries.ofPowerSeries ℤ ℂ

private def scalarSum (p : PS) (a : ℂ) : ℂ :=
  ∑' j : ℕ, PowerSeries.coeff j p * a ^ j

private lemma product_hasSum {p q : PS} {a u v : ℂ}
    (hp : HasSum (fun j : ℕ => PowerSeries.coeff j p * a ^ j) u)
    (hq : HasSum (fun j : ℕ => PowerSeries.coeff j q * a ^ j) v) :
    HasSum (fun j : ℕ => PowerSeries.coeff j (p * q) * a ^ j) (u * v) := by
  have h := hasSum_sum_range_mul_of_summable_norm hp.summable.norm hq.summable.norm
  rw [hp.tsum_eq, hq.tsum_eq] at h
  convert h using 1
  funext n
  rw [PowerSeries.coeff_mul, Finset.sum_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
  apply Finset.sum_congr rfl
  intro j hj
  have he : j + (n - j) = n := Nat.add_sub_of_le
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))
  rw [show a ^ n = a ^ j * a ^ (n - j) by rw [← pow_add, he]]
  ring

private lemma scalarSum_mul {p q : PS} {a : ℂ}
    (hp : Summable (fun j : ℕ => ‖PowerSeries.coeff j p * a ^ j‖))
    (hq : Summable (fun j : ℕ => ‖PowerSeries.coeff j q * a ^ j‖)) :
    scalarSum (p * q) a = scalarSum p a * scalarSum q a ∧
      Summable (fun j : ℕ => ‖PowerSeries.coeff j (p * q) * a ^ j‖) := by
  have h := product_hasSum hp.of_norm.hasSum hq.of_norm.hasSum
  exact ⟨h.tsum_eq, h.summable.norm⟩

private lemma scalarSum_add {p q : PS} {a : ℂ}
    (hp : Summable (fun j : ℕ => ‖PowerSeries.coeff j p * a ^ j‖))
    (hq : Summable (fun j : ℕ => ‖PowerSeries.coeff j q * a ^ j‖)) :
    scalarSum (p + q) a = scalarSum p a + scalarSum q a ∧
      Summable (fun j : ℕ => ‖PowerSeries.coeff j (p + q) * a ^ j‖) := by
  have h := hp.of_norm.hasSum.add hq.of_norm.hasSum
  simp only [← add_mul, ← map_add] at h
  exact ⟨h.tsum_eq, h.summable.norm⟩

private lemma scalarSum_neg (p : PS) (a : ℂ) : scalarSum (-p) a = -scalarSum p a := by
  simp only [scalarSum, map_neg, neg_mul, tsum_neg]

private lemma monomial_hasSum (n : ℕ) (c a : ℂ) :
    HasSum (fun j : ℕ => PowerSeries.coeff j (PowerSeries.monomial n c) * a ^ j)
      (c * a ^ n) := by
  convert hasSum_single (β := ℕ) n
    (f := fun j => PowerSeries.coeff j (PowerSeries.monomial n c) * a ^ j)
    (fun j hj => by simp [PowerSeries.coeff_monomial, hj]) using 1
  simp

private lemma scalarSum_monomial (n : ℕ) (c a : ℂ) :
    scalarSum (PowerSeries.monomial n c) a = c * a ^ n :=
  (monomial_hasSum n c a).tsum_eq

private lemma scalarSum_finset {ι : Type*} (S : Finset ι) (p : ι → PS) (a : ℂ)
    (hp : ∀ i ∈ S, Summable (fun j : ℕ => ‖PowerSeries.coeff j (p i) * a ^ j‖)) :
    scalarSum (∑ i ∈ S, p i) a = ∑ i ∈ S, scalarSum (p i) a ∧
      Summable (fun j : ℕ => ‖PowerSeries.coeff j (∑ i ∈ S, p i) * a ^ j‖) := by
  classical
  have h := hasSum_sum (fun i hi => (hp i hi).of_norm.hasSum)
  have hh : HasSum (fun j : ℕ => PowerSeries.coeff j (∑ i ∈ S, p i) * a ^ j)
      (∑ i ∈ S, scalarSum (p i) a) := by
    simpa only [map_sum, Finset.sum_mul, scalarSum] using h
  exact ⟨hh.tsum_eq, hh.summable.norm⟩

/- Products in the modulus variable involve only a finite antidiagonal at
each degree. The two scalar Cauchy products are absolutely convergent. -/
private lemma normal_mul {P Q : BPS} {a v F G : ℂ}
    (hP : ∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d P) * a ^ j‖))
    (hQ : ∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d Q) * a ^ j‖))
    (hF : HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d P) a * v ^ d) F)
    (hG : HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d Q) a * v ^ d) G) :
    (∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d (P * Q)) * a ^ j‖)) ∧
    HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d (P * Q)) a * v ^ d) (F * G) := by
  have hc (d : ℕ) :
      scalarSum (PowerSeries.coeff d (P * Q)) a =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal d,
          scalarSum (PowerSeries.coeff ij.1 P) a *
            scalarSum (PowerSeries.coeff ij.2 Q) a ∧
      Summable (fun j : ℕ =>
        ‖PowerSeries.coeff j (PowerSeries.coeff d (P * Q)) * a ^ j‖) := by
    rw [PowerSeries.coeff_mul]
    have h := scalarSum_finset (Finset.HasAntidiagonal.antidiagonal d)
      (fun ij => PowerSeries.coeff ij.1 P * PowerSeries.coeff ij.2 Q) a
      (fun ij _ => (scalarSum_mul (hP ij.1) (hQ ij.2)).2)
    have he (i j : ℕ) :
        scalarSum (PowerSeries.coeff i P * PowerSeries.coeff j Q) a =
          scalarSum (PowerSeries.coeff i P) a * scalarSum (PowerSeries.coeff j Q) a :=
      (scalarSum_mul (hP i) (hQ j)).1
    simpa only [he] using h
  let p : PS := PowerSeries.mk (fun d => scalarSum (PowerSeries.coeff d P) a)
  let q : PS := PowerSeries.mk (fun d => scalarSum (PowerSeries.coeff d Q) a)
  have hm := product_hasSum (p := p) (q := q) hF hG
  refine ⟨fun d => (hc d).2, ?_⟩
  have he (d : ℕ) : PowerSeries.coeff d (p * q) =
      scalarSum (PowerSeries.coeff d (P * Q)) a := by
    simpa only [PowerSeries.coeff_mul, p, q, PowerSeries.coeff_mk] using (hc d).1.symm
  simpa only [he] using hm

private lemma normal_add {P Q : BPS} {a v F G : ℂ}
    (hP : ∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d P) * a ^ j‖))
    (hQ : ∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d Q) * a ^ j‖))
    (hF : HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d P) a * v ^ d) F)
    (hG : HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d Q) a * v ^ d) G) :
    (∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d (P + Q)) * a ^ j‖)) ∧
    HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d (P + Q)) a * v ^ d) (F + G) := by
  refine ⟨fun d => by
    rw [map_add]
    exact (scalarSum_add (hP d) (hQ d)).2, ?_⟩
  convert hF.add hG using 1
  funext d
  rw [map_add, (scalarSum_add (hP d) (hQ d)).1, add_mul]

private lemma normal_neg {P : BPS} {a v F : ℂ}
    (hP : ∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d P) * a ^ j‖))
    (hF : HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d P) a * v ^ d) F) :
    (∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d (-P)) * a ^ j‖)) ∧
    HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d (-P)) a * v ^ d) (-F) := by
  refine ⟨fun d => by simpa only [map_neg, neg_mul, norm_neg] using hP d, ?_⟩
  simpa only [map_neg, scalarSum_neg, neg_mul] using hF.neg

private lemma normal_horizontal {p : PS} {a v f : ℂ}
    (hp : HasSum (fun j : ℕ => PowerSeries.coeff j p * a ^ j) f) :
    (∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d (PowerSeries.C p : BPS)) * a ^ j‖)) ∧
    HasSum (fun d : ℕ => scalarSum
      (PowerSeries.coeff d (PowerSeries.C p : BPS)) a * v ^ d) f := by
  have h0 : scalarSum p a = f := hp.tsum_eq
  refine ⟨fun d => ?_, ?_⟩
  · by_cases hd : d = 0
    · simpa [hd] using hp.summable.norm
    · simp [PowerSeries.coeff_C, hd]
  · convert hasSum_single (β := ℕ) 0
      (f := fun d => scalarSum (PowerSeries.coeff d (PowerSeries.C p : BPS)) a * v ^ d)
      (fun d hd => by simp [PowerSeries.coeff_C, hd, scalarSum]) using 1
    simp [h0]

private lemma normal_vertical {p : PS} {a v f : ℂ}
    (hp : HasSum (fun d : ℕ => PowerSeries.coeff d p * v ^ d) f) :
    (∀ d, Summable (fun j : ℕ => ‖PowerSeries.coeff j
      (PowerSeries.coeff d (PowerSeries.map (PowerSeries.C : ℂ →+* PS) p)) * a ^ j‖)) ∧
    HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d
      (PowerSeries.map (PowerSeries.C : ℂ →+* PS) p)) a * v ^ d) f := by
  have hc (c : ℂ) : scalarSum (PowerSeries.C c) a = c := by
    simpa only [PowerSeries.monomial_zero_eq_C_apply, pow_zero, mul_one] using
      scalarSum_monomial 0 c a
  refine ⟨fun d => ?_, ?_⟩
  · rw [PowerSeries.coeff_map]
    simpa only [PowerSeries.monomial_zero_eq_C_apply] using
      (monomial_hasSum 0 (PowerSeries.coeff d p) a).summable.norm
  · simpa only [PowerSeries.coeff_map, hc] using hp

private lemma normal_diagonal {p : PS} {a v f : ℂ}
    (hp : HasSum (fun d : ℕ => PowerSeries.coeff d p * (a * v) ^ d) f) :
    (∀ d, Summable (fun j : ℕ => ‖PowerSeries.coeff j
      (PowerSeries.coeff d (PowerSeries.rescale (PowerSeries.X : PS)
        (PowerSeries.map (PowerSeries.C : ℂ →+* PS) p))) * a ^ j‖)) ∧
    HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d
      (PowerSeries.rescale (PowerSeries.X : PS)
        (PowerSeries.map (PowerSeries.C : ℂ →+* PS) p))) a * v ^ d) f := by
  have hc (d : ℕ) : PowerSeries.coeff d
      (PowerSeries.rescale (PowerSeries.X : PS)
        (PowerSeries.map (PowerSeries.C : ℂ →+* PS) p)) =
      PowerSeries.monomial d (PowerSeries.coeff d p) := by
    rw [PowerSeries.coeff_rescale, PowerSeries.coeff_map]
    ext j
    simp [PowerSeries.coeff_mul_C, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_monomial]
  refine ⟨fun d => by rw [hc]; exact (monomial_hasSum _ _ _).summable.norm, ?_⟩
  convert hp using 1
  funext d
  rw [hc, scalarSum_monomial, mul_pow]
  ring

private def poleSeries (b : ℂ) : PS :=
  (2 * (PowerSeries.X - PowerSeries.C b) ^ 2)⁻¹

private lemma pole_coeff {b : ℂ} (hb : b ≠ 0) (n : ℕ) :
    PowerSeries.coeff n (poleSeries b) =
      (1 / 2 : ℂ) * (b ^ (n + 2))⁻¹ * (n + 1 : ℂ) := by
  let p : PS := PowerSeries.invUnitsSub (Units.mk0 b hb)
  let q : PS := PowerSeries.C (1 / 2 : ℂ) * p ^ 2
  have hp : p * (PowerSeries.C b - PowerSeries.X) = 1 :=
    PowerSeries.invUnitsSub_mul_sub (Units.mk0 b hb)
  have hq : q * (2 * (PowerSeries.X - PowerSeries.C b) ^ 2) = 1 := by
    have hn : PowerSeries.C (1 / 2 : ℂ) * (2 : PS) = 1 := by
      norm_num [← map_ofNat, ← map_mul]
    calc
      _ = (PowerSeries.C (1 / 2 : ℂ) * 2) *
          (p * (PowerSeries.C b - PowerSeries.X)) ^ 2 := by dsimp [q]; ring
      _ = 1 := by rw [hn, hp]; simp
  have heq : q = poleSeries b :=
    (PowerSeries.eq_inv_iff_mul_eq_one (by simp [hb] :
      PowerSeries.constantCoeff (2 * (PowerSeries.X - PowerSeries.C b) ^ 2 : PS) ≠ 0)).mpr hq
  rw [← heq, q, PowerSeries.coeff_C_mul, pow_two, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ]
  have hterm (j : ℕ) (hj : j ∈ Finset.range (n + 1)) :
      PowerSeries.coeff j p * PowerSeries.coeff (n - j) p = (b ^ (n + 2))⁻¹ := by
    have hjn : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    simp only [p, PowerSeries.coeff_invUnitsSub, one_divp]
    change (b ^ (j + 1))⁻¹ * (b ^ (n - j + 1))⁻¹ = (b ^ (n + 2))⁻¹
    rw [← mul_inv, ← pow_add]
    congr 2
    omega
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

private lemma pole_hasSum {a b : ℂ} (hb : b ≠ 0) (ha : ‖a‖ < ‖b‖) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (poleSeries b) * a ^ n)
      ((2 * (a - b) ^ 2)⁻¹) := by
  have h := (Complex.one_div_sub_sq_hasFPowerSeriesOnBall_zero hb).hasSum
    (show a ∈ eball (0 : ℂ) ‖b‖ₑ by
      simpa only [mem_eball_zero_iff, enorm_lt_coe, ← coe_nnnorm, NNReal.coe_lt_coe] using ha)
  convert h.mul_left (1 / 2 : ℂ) using 1
  · funext n
    simp only [pole_coeff hb, FormalMultilinearSeries.ofScalars_apply_eq,
      zero_add, smul_eq_mul]
    ring
  · have he : (b - a) ^ 2 = (a - b) ^ 2 := by ring
    simp only [one_div, he, mul_inv_rev]
    ring

private def externalSeries (b root : ℂ) : PS :=
  PowerSeries.mk (fun n => root * halfBinomial n / b ^ (n + 1))

private def regularNumerator (b : ℂ) : BPS :=
  let A : BPS := PowerSeries.C PowerSeries.X
  let B : BPS := PowerSeries.C (PowerSeries.C b)
  B * (A + B + 2) + PowerSeries.X * (2 * A * B + A + B)

private def regularTT (b root : ℂ) : BPS :=
  let A : BPS := PowerSeries.C PowerSeries.X
  PowerSeries.C halfSeries * PowerSeries.map (PowerSeries.C : ℂ →+* PS) halfSeries *
    PowerSeries.rescale (PowerSeries.X : PS)
      (PowerSeries.map (PowerSeries.C : ℂ →+* PS) (externalSeries b root)) *
    (A * regularNumerator b * PowerSeries.C (poleSeries b) +
      PowerSeries.rescale (PowerSeries.X : PS)
        (PowerSeries.map (PowerSeries.C : ℂ →+* PS) scalarCSeries))

private def regularUT (b root : ℂ) : BPS :=
  -(PowerSeries.C halfSeries * PowerSeries.map (PowerSeries.C : ℂ →+* PS) halfSeries *
    PowerSeries.rescale (PowerSeries.X : PS)
      (PowerSeries.map (PowerSeries.C : ℂ →+* PS) (externalSeries b root))) *
    (PowerSeries.X * regularNumerator b *
        PowerSeries.map (PowerSeries.C : ℂ →+* PS) (poleSeries b) +
      PowerSeries.rescale (PowerSeries.X : PS)
        (PowerSeries.map (PowerSeries.C : ℂ →+* PS) scalarCSeries))

private lemma regular_evaluation {b a v : ℂ} (hb : b ≠ 0) (root : ℂ)
    (ha : ‖a‖ < beta b) (hv : ‖v‖ < beta b) :
    ((∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d (regularTT b root)) * a ^ j‖)) ∧
      HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d (regularTT b root)) a * v ^ d)
        (H a * H v * externalOmega b root (a * v) *
          (a * (b * (a + b + 2) + v * (2 * a * b + a + b)) /
            (2 * (a - b) ^ 2) + scalarC (a * v)))) ∧
    ((∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d (regularUT b root)) * a ^ j‖)) ∧
      HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d (regularUT b root)) a * v ^ d)
        (-(H a * H v * externalOmega b root (a * v)) *
          (v * (b * (a + b + 2) + v * (2 * a * b + a + b)) /
            (2 * (v - b) ^ 2) + scalarC (a * v)))) := by
  have ha1 : ‖a‖ < 1 := ha.trans_le (min_le_left _ _)
  have hv1 : ‖v‖ < 1 := hv.trans_le (min_le_left _ _)
  have hab : ‖a‖ < ‖b‖ := ha.trans_le (min_le_right _ _)
  have hvb : ‖v‖ < ‖b‖ := hv.trans_le (min_le_right _ _)
  have hav1 : ‖a * v‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha1.le (norm_nonneg v)).trans_lt
      (by simpa using hv1)
  have havb : ‖a * v‖ < ‖b‖ := by
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right ha1.le (norm_nonneg v)).trans_lt
      (by simpa using hvb)
  have hE : HasSum (fun n : ℕ => PowerSeries.coeff n (externalSeries b root) *
      (a * v) ^ n) (externalOmega b root (a * v)) := by
    have h := (H_hasSum (show ‖a * v / b‖ < 1 by
      rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hb)).mpr havb)).1
    convert h.mul_left (root / b) using 1
    · funext n
      simp only [externalSeries, PowerSeries.coeff_mk, div_pow, pow_succ]
      field_simp [hb]
      <;> ring
    · rfl
  have hC : HasSum (fun n : ℕ => PowerSeries.coeff n scalarCSeries *
      (a * v) ^ n) (scalarC (a * v)) := by
    obtain ⟨eta, hxe, he1⟩ := exists_between hav1
    have he : 0 < eta := (norm_nonneg _).trans_lt hxe
    have h := (scalarC_powerSeries (eta := ⟨eta, he.le⟩) he he1).hasSum
      (show a * v ∈ eball (0 : ℂ) (⟨eta, he.le⟩ : ℝ≥0∞) by
        simpa only [mem_eball_zero_iff, enorm_lt_coe, ← coe_nnnorm,
          NNReal.coe_lt_coe] using hxe)
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, zero_add, smul_eq_mul] using h
  have hHA := normal_horizontal (v := v)
    (show HasSum (fun n : ℕ => PowerSeries.coeff n halfSeries * a ^ n) (H a) by
      simpa only [halfSeries, PowerSeries.coeff_mk] using (H_hasSum ha1).1)
  have hHV := normal_vertical (a := a)
    (show HasSum (fun n : ℕ => PowerSeries.coeff n halfSeries * v ^ n) (H v) by
      simpa only [halfSeries, PowerSeries.coeff_mk] using (H_hasSum hv1).1)
  have hExt := normal_diagonal hE
  have hCs := normal_diagonal hC
  have hPA := normal_horizontal (v := v) (pole_hasSum hb hab)
  have hPV := normal_vertical (a := a) (pole_hasSum hb hvb)
  have hconst (c : ℂ) := normal_horizontal (v := v)
    (show HasSum (fun j : ℕ => PowerSeries.coeff j (PowerSeries.C c) * a ^ j) c by
      simpa only [PowerSeries.monomial_zero_eq_C_apply, pow_zero, mul_one] using
        monomial_hasSum 0 c a)
  have hA := normal_horizontal (v := v)
    (show HasSum (fun j : ℕ => PowerSeries.coeff j (PowerSeries.X : PS) * a ^ j) a by
      simpa only [PowerSeries.X_eq, pow_one, one_mul] using monomial_hasSum 1 1 a)
  have hV := normal_vertical (a := a)
    (show HasSum (fun j : ℕ => PowerSeries.coeff j (PowerSeries.X : PS) * v ^ j) v by
      simpa only [PowerSeries.X_eq, pow_one, one_mul] using monomial_hasSum 1 1 v)
  have hB := hconst b
  have hTwo : (∀ d, Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d (2 : BPS)) * a ^ j‖)) ∧
      HasSum (fun d : ℕ => scalarSum (PowerSeries.coeff d (2 : BPS)) a * v ^ d) 2 := by
    simpa only [map_ofNat] using hconst 2
  have hAB := normal_mul hA.1 hB.1 hA.2 hB.2
  have hTwoAB := normal_mul hTwo.1 hAB.1 hTwo.2 hAB.2
  have hABplus := normal_add hA.1 hB.1 hA.2 hB.2
  have hN0 := normal_mul hB.1
    (normal_add hABplus.1 hTwo.1 hABplus.2 hTwo.2).1 hB.2
    (normal_add hABplus.1 hTwo.1 hABplus.2 hTwo.2).2
  have hN1 := normal_mul hV.1
    (normal_add (normal_add hTwoAB.1 hA.1 hTwoAB.2 hA.2).1 hB.1
      (normal_add hTwoAB.1 hA.1 hTwoAB.2 hA.2).2 hB.2).1 hV.2
    (normal_add (normal_add hTwoAB.1 hA.1 hTwoAB.2 hA.2).1 hB.1
      (normal_add hTwoAB.1 hA.1 hTwoAB.2 hA.2).2 hB.2).2
  have hN := normal_add hN0.1 hN1.1 hN0.2 hN1.2
  have hBase0 := normal_mul hHA.1 hHV.1 hHA.2 hHV.2
  have hBase := normal_mul hBase0.1 hExt.1 hBase0.2 hExt.2
  have hAN := normal_mul hA.1 hN.1 hA.2 hN.2
  have hVN := normal_mul hV.1 hN.1 hV.2 hN.2
  have hTpolar := normal_mul hAN.1 hPA.1 hAN.2 hPA.2
  have hUpolar := normal_mul hVN.1 hPV.1 hVN.2 hPV.2
  have hTbracket := normal_add hTpolar.1 hCs.1 hTpolar.2 hCs.2
  have hUbracket := normal_add hUpolar.1 hCs.1 hUpolar.2 hCs.2
  have hT := normal_mul hBase.1 hTbracket.1 hBase.2 hTbracket.2
  have hMinus := normal_neg hBase.1 hBase.2
  have hU := normal_mul hMinus.1 hUbracket.1 hMinus.2 hUbracket.2
  exact ⟨by simpa only [regularTT, regularNumerator, PowerSeries.map_X,
      div_eq_mul_inv] using hT,
    by simpa only [regularUT, regularNumerator, PowerSeries.map_X,
      div_eq_mul_inv] using hU⟩

private lemma regular_kernels {b a v : ℂ} (root : ℂ) (ha : a ≠ 0) :
    H a * H v * externalOmega b root (a * v) *
        (a * (b * (a + b + 2) + v * (2 * a * b + a + b)) /
          (2 * (a - b) ^ 2) + scalarC (a * v)) =
      a * TT b root a (a * v) ∧
    -(H a * H v * externalOmega b root (a * v)) *
        (v * (b * (a + b + 2) + v * (2 * a * b + a + b)) /
          (2 * (v - b) ^ 2) + scalarC (a * v)) =
      a * UT b root a (a * v) := by
  constructor
  · simp only [TT, omega, polarNumerator, mul_div_cancel_left₀ _ ha]
    field_simp [ha]
    <;> ring
  · have hden : (a * b - a * v) ^ 2 = a ^ 2 * (v - b) ^ 2 := by ring
    simp only [UT, omega, polarNumerator, mul_div_cancel_left₀ _ ha, hden,
      mul_inv_rev, inv_pow]
    field_simp [ha]
    <;> ring

private lemma rescale_inverse {k : Type*} [Field k] (c : k) (p : PowerSeries k)
    (hp : PowerSeries.constantCoeff p ≠ 0) :
    PowerSeries.rescale c p⁻¹ = (PowerSeries.rescale c p)⁻¹ := by
  have ht : PowerSeries.constantCoeff (PowerSeries.rescale c p) ≠ 0 := by
    simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_rescale, pow_zero, one_mul] using hp
  apply (PowerSeries.eq_inv_iff_mul_eq_one ht).mpr
  rw [← map_mul, PowerSeries.inv_mul_cancel p hp, map_one]

private lemma map_inverse {k l : Type*} [Field k] [Field l]
    (f : k →+* l) (p : PowerSeries k) (hp : PowerSeries.constantCoeff p ≠ 0) :
    PowerSeries.map f p⁻¹ = (PowerSeries.map f p)⁻¹ := by
  have ht : PowerSeries.constantCoeff (PowerSeries.map f p) ≠ 0 := by
    intro h
    apply hp
    apply f.injective
    simpa only [map_zero, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map] using h
  apply (PowerSeries.eq_inv_iff_mul_eq_one ht).mpr
  rw [← map_mul, PowerSeries.inv_mul_cancel p hp, map_one]

private lemma inclusion_inverse (p : PS) (hp : PowerSeries.constantCoeff p ≠ 0) :
    inclusion p⁻¹ = (inclusion p)⁻¹ := by
  have hm : inclusion p⁻¹ * inclusion p = 1 := by
    rw [← map_mul, PowerSeries.inv_mul_cancel p hp, map_one]
  have hn : inclusion p ≠ 0 := by
    intro he
    rw [he, mul_zero] at hm
    exact zero_ne_one hm
  apply mul_right_cancel₀ hn
  rw [inv_mul_cancel₀ hn]
  exact hm

private lemma rescale_constant {R : Type*} [CommSemiring R] (c r : R) :
    PowerSeries.rescale c (PowerSeries.C r) = PowerSeries.C r := by
  ext n
  by_cases hn : n = 0
  · simp [hn, PowerSeries.coeff_rescale]
  · simp [PowerSeries.coeff_rescale, PowerSeries.coeff_C, hn]

private lemma omega_regularization :
    let a : LaurentSeries ℂ := HahnSeries.single 1 1
    PowerSeries.C a * PowerSeries.rescale a formalOmega =
      PowerSeries.map inclusion
        (PowerSeries.C halfSeries * PowerSeries.map (PowerSeries.C : ℂ →+* PS) halfSeries) := by
  dsimp only
  ext d
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, formalOmega,
    PowerSeries.coeff_mk, omegaCoefficient, PowerSeries.coeff_map,
    PowerSeries.coeff_C_mul, inclusion, map_mul, PowerSeries.coeff_map,
    HahnSeries.ofPowerSeries_C, halfSeries, PowerSeries.coeff_mk]
  rw [← mul_assoc, ← pow_succ', HahnSeries.single_pow]
  simp only [nsmul_eq_mul, Int.cast_natCast, mul_one, one_pow,
    HahnSeries.single_mul_single]
  have he : ((d + 1 : ℕ) : ℤ) + (-(d : ℤ) - 1) = 0 := by omega
  rw [he]
  simp only [one_mul, ← HahnSeries.C_apply]
  ring

private lemma external_regularization (b root : ℂ) :
    PowerSeries.map inclusion
      (PowerSeries.rescale (PowerSeries.X : PS)
        (PowerSeries.map (PowerSeries.C : ℂ →+* PS) (externalSeries b root))) =
      PowerSeries.rescale (HahnSeries.single 1 1 : LaurentSeries ℂ)
        (formalExternalOmega b root) := by
  ext d
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_rescale, PowerSeries.coeff_map,
    map_mul, map_pow, inclusion, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C,
    externalSeries, formalExternalOmega, PowerSeries.coeff_mk]

private lemma scalar_regularization :
    PowerSeries.map inclusion
      (PowerSeries.rescale (PowerSeries.X : PS)
        (PowerSeries.map (PowerSeries.C : ℂ →+* PS) scalarCSeries)) =
      PowerSeries.rescale (HahnSeries.single 1 1 : LaurentSeries ℂ)
        (PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries) := by
  ext d
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_rescale,
    PowerSeries.coeff_map, map_mul, map_pow, inclusion,
    HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C]

private lemma regular_formal {b : ℂ} (hb : b ≠ 0) (root : ℂ) :
    let a : LaurentSeries ℂ := HahnSeries.single 1 1
    PowerSeries.map inclusion (regularTT b root) =
      PowerSeries.C a * PowerSeries.rescale a (cubicTTSeries b root) ∧
    PowerSeries.map inclusion (regularUT b root) =
      PowerSeries.C a * PowerSeries.rescale a (cubicUTSeries b root) := by
  let a : LaurentSeries ℂ := HahnSeries.single 1 1
  let B : LaurentSeries ℂ := HahnSeries.C b
  let A : AnnulusSeries := PowerSeries.C a
  let BB : AnnulusSeries := PowerSeries.C B
  let V : AnnulusSeries := PowerSeries.X
  have ha : a ≠ 0 := by
    intro h
    have hh := congrArg (fun p : LaurentSeries ℂ => p.coeff 1) h
    simpa [a] using hh
  have hB : B ≠ 0 := by
    intro h
    have hh := congrArg (fun p : LaurentSeries ℂ => p.coeff 0) h
    exact hb (by simpa [B] using hh)
  have hTTpole : PowerSeries.map inclusion (PowerSeries.C (poleSeries b) : BPS) =
      (2 * (A - BB) ^ 2)⁻¹ := by
    have hi : inclusion (poleSeries b) = (2 * (a - B) ^ 2)⁻¹ := by
      rw [poleSeries, inclusion_inverse (2 * (PowerSeries.X - PowerSeries.C b) ^ 2)
        (by simp [hb])]
      congr 1
      simp only [map_mul, map_ofNat, map_pow, map_sub, inclusion,
        HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C, a, B]
    have hd : (2 * (A - BB) ^ 2) = PowerSeries.C (2 * (a - B) ^ 2) := by
      simp only [A, BB, map_mul, map_pow, map_sub, map_ofNat]
    rw [PowerSeries.map_C, hi, hd, PowerSeries.C_inv]
  have hUTpole : PowerSeries.map inclusion
      (PowerSeries.map (PowerSeries.C : ℂ →+* PS) (poleSeries b)) =
      (2 * (BB - V) ^ 2)⁻¹ := by
    have hcomp : inclusion.comp (PowerSeries.C : ℂ →+* PS) =
        (HahnSeries.C : ℂ →+* LaurentSeries ℂ) := by
      ext c
      exact HahnSeries.ofPowerSeries_C c
    rw [← PowerSeries.map_comp, hcomp, poleSeries,
      map_inverse (HahnSeries.C : ℂ →+* LaurentSeries ℂ)
        (2 * (PowerSeries.X - PowerSeries.C b) ^ 2) (by simp [hb])]
    congr 1
    simp only [map_mul, map_ofNat, map_pow, map_sub, PowerSeries.map_X,
      PowerSeries.map_C, BB, V]
    ring
  have hden0 : PowerSeries.constantCoeff
      (2 * (PowerSeries.C (a * B) - (PowerSeries.X : AnnulusSeries)) ^ 2) ≠ 0 := by
    simp [ha, hB]
  have hden : PowerSeries.rescale a
      ((2 * (PowerSeries.C (a * B) - (PowerSeries.X : AnnulusSeries)) ^ 2)⁻¹) =
      PowerSeries.C (a⁻¹ ^ 2) * (2 * (BB - V) ^ 2)⁻¹ := by
    rw [rescale_inverse _ _ hden0]
    have he : PowerSeries.rescale a
        (2 * (PowerSeries.C (a * B) - (PowerSeries.X : AnnulusSeries)) ^ 2) =
        PowerSeries.C (a ^ 2) * (2 * (BB - V) ^ 2) := by
      simp only [map_mul, map_ofNat, map_pow, map_sub, rescale_constant,
        PowerSeries.rescale_X, BB, V, map_mul]
      ring
    rw [he, PowerSeries.mul_inv_rev, PowerSeries.C_inv, ← inv_pow]
    ring
  have hTTden : PowerSeries.rescale a ((2 * (A - BB) ^ 2)⁻¹) =
      (2 * (A - BB) ^ 2)⁻¹ := by
    have he : (2 * (A - BB) ^ 2) =
        PowerSeries.C (2 * (a - B) ^ 2) := by
      simp only [A, BB, map_mul, map_pow, map_sub, map_ofNat]
    rw [he, PowerSeries.C_inv, rescale_constant]
  have hN : PowerSeries.map inclusion (regularNumerator b) =
      BB * (A + BB + 2) + V * (2 * A * BB + A + BB) := by
    simp only [regularNumerator, map_add, map_mul, map_ofNat, PowerSeries.map_C,
      PowerSeries.map_X, inclusion, HahnSeries.ofPowerSeries_X,
      HahnSeries.ofPowerSeries_C, A, BB, a, B, V]
  have hTTnum : PowerSeries.rescale a
      (A * BB * (A + BB) + 2 * (1 + V) * A * BB + V * (A + BB)) =
      A * (BB * (A + BB + 2) + V * (2 * A * BB + A + BB)) := by
    simp only [map_add, map_mul, map_ofNat, map_one, A, BB,
      rescale_constant, PowerSeries.rescale_X, V]
    ring
  have hUTnum : PowerSeries.rescale a
      (V * (A * BB * (A + BB + 2) + V * (A + BB + 2 * A * BB))) =
      A ^ 2 * V * (BB * (A + BB + 2) + V * (2 * A * BB + A + BB)) := by
    simp only [map_add, map_mul, map_ofNat, A, BB,
      rescale_constant, PowerSeries.rescale_X, V]
    ring
  have hcancel : A ^ 2 * PowerSeries.C (a⁻¹ ^ 2) = 1 := by
    simpa only [A, ← map_pow, ← map_mul, ← mul_pow, mul_inv_cancel₀ ha,
      one_pow, map_one]
  have hO := omega_regularization
  have hE := external_regularization b root
  have hC := scalar_regularization
  change PowerSeries.map inclusion (regularTT b root) =
      A * PowerSeries.rescale a (cubicTTSeries b root) ∧
    PowerSeries.map inclusion (regularUT b root) =
      A * PowerSeries.rescale a (cubicUTSeries b root)
  constructor
  · unfold regularTT
    rw [map_mul, map_mul, ← hO, hE, map_add,
      map_mul, map_mul, hN, hTTpole, hC]
    change _ = A * PowerSeries.rescale a
      (formalOmega * formalExternalOmega b root *
        ((A * BB * (A + BB) + 2 * (1 + V) * A * BB + V * (A + BB)) *
          (2 * (A - BB) ^ 2)⁻¹ +
          PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries))
    rw [map_mul, map_mul, map_add, map_mul, hTTnum, hTTden]
    simp only [PowerSeries.map_C, inclusion, HahnSeries.ofPowerSeries_X]
    ring
  · unfold regularUT
    rw [map_mul, map_neg, map_mul, ← hO, hE, map_add,
      map_mul, map_mul, PowerSeries.map_X, hN, hUTpole, hC]
    change _ = A * PowerSeries.rescale a
      (-(formalOmega * formalExternalOmega b root) *
        (V * (A * BB * (A + BB + 2) + V * (A + BB + 2 * A * BB)) *
          (2 * (PowerSeries.C (a * B) - V) ^ 2)⁻¹ +
          PowerSeries.map (HahnSeries.C : ℂ →+* LaurentSeries ℂ) scalarCSeries))
    rw [map_mul, map_neg, map_mul, map_add, map_mul, hUTnum, hden]
    have hc := hcancel
    linear_combination (norm := ring_nf)
      ((A * PowerSeries.rescale a formalOmega *
        PowerSeries.rescale a (formalExternalOmega b root)) *
        V * (BB * (A + BB + 2) + V * (2 * A * BB + A + BB)) *
        (2 * (BB - V) ^ 2)⁻¹) * hc
/- The majorant is independent of the circle parameter. This proves the
termwise Laurent integral, including the case in which there is no residue. -/
private lemma shifted_series_contour (p : PS) (s d : ℕ) {r : ℝ} (hr : 0 < r)
    (hp : Summable (fun j : ℕ => ‖PowerSeries.coeff j p‖ * r ^ j)) :
    negativeContour (fun a => scalarSum p a / a ^ (d + 1)) s r =
      if s ≤ d then PowerSeries.coeff (d - s) p else 0 := by
  let f : ℕ → ℂ → ℂ := fun j a =>
    PowerSeries.coeff j p * a ^ j / a ^ (d + 1) * a ^ s
  let g : ℂ → ℂ := fun a => scalarSum p a / a ^ (d + 1) * a ^ s
  let c : ℂ := (2 * Real.pi * Complex.I)⁻¹
  have hne (theta : ℝ) : circleMap 0 r theta ≠ 0 := circleMap_ne_center hr.ne'
  have hnorm (theta : ℝ) : ‖circleMap 0 r theta‖ = r := by
    simpa only [norm_circleMap_zero, abs_of_pos hr]
  have hpoint (theta : ℝ) : HasSum (fun j : ℕ => f j (circleMap 0 r theta))
      (g (circleMap 0 r theta)) := by
    have hs : Summable (fun j : ℕ =>
        ‖PowerSeries.coeff j p * circleMap 0 r theta ^ j‖) := by
      simpa only [norm_mul, norm_pow, hnorm theta] using hp
    simpa only [scalarSum, f, g, div_eq_mul_inv, mul_assoc] using
      (hs.of_norm.hasSum.mul_right ((circleMap 0 r theta ^ (d + 1))⁻¹)).mul_right
        (circleMap 0 r theta ^ s)
  have hInt : HasSum (fun j : ℕ => ∮ a in C(0, r), f j a)
      (∮ a in C(0, r), g a) := by
    unfold circleIntegral
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun j _ => (‖PowerSeries.coeff j p‖ * r ^ j) *
        (r ^ (s + 1) / r ^ (d + 1)))
    · intro j
      have hcont : Continuous (fun theta : ℝ =>
          deriv (circleMap 0 r) theta • f j (circleMap 0 r theta)) := by
        simp only [deriv_circleMap, f, smul_eq_mul]
        exact ((continuous_circleMap 0 r).mul_const Complex.I).mul
          ((((continuous_const.mul ((continuous_circleMap 0 r).pow j)).div
            ((continuous_circleMap 0 r).pow (d + 1))
            (fun theta => pow_ne_zero _ (hne theta))).mul
            ((continuous_circleMap 0 r).pow s)))
      exact hcont.aestronglyMeasurable
    · intro j
      exact Filter.Eventually.of_forall (fun theta _ => by
        simp only [f, norm_smul, norm_mul, norm_div, norm_pow, deriv_circleMap,
          hnorm theta, Complex.norm_I, mul_one]
        rw [pow_succ]
        exact le_of_eq (by ring))
    · exact Filter.Eventually.of_forall (fun _ _ => hp.mul_right _)
    · simpa only [tsum_mul_right] using
        (intervalIntegrable_const : IntervalIntegrable
          (fun _ : ℝ => (∑' j : ℕ, ‖PowerSeries.coeff j p‖ * r ^ j) *
            (r ^ (s + 1) / r ^ (d + 1))) volume 0 (2 * Real.pi))
    · exact Filter.Eventually.of_forall (fun theta _ =>
        (hpoint theta).const_smul (deriv (circleMap 0 r) theta))
  have hTerm (j : ℕ) : c * (∮ a in C(0, r), f j a) =
      if j + s = d then PowerSeries.coeff j p else 0 := by
    have heq : (∮ a in C(0, r), f j a) =
        PowerSeries.coeff j p *
          ∮ a in C(0, r), a ^ ((j : ℤ) + s - (d + 1 : ℕ)) := by
      rw [← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr hr.le
      intro a ha
      have ha0 : a ≠ 0 := by
        have hna : ‖a‖ = r := by simpa using ha
        exact norm_pos_iff.mp (hna.symm ▸ hr)
      simp only [f, zpow_sub₀ ha0, zpow_add₀ ha0, zpow_natCast]
      ring
    rw [heq]
    by_cases hj : j + s = d
    · rw [if_pos hj, show (j : ℤ) + s - (d + 1 : ℕ) = -1 by omega]
      have hres : (∮ a in C(0, r), a ^ (-1 : ℤ)) = 2 * Real.pi * Complex.I := by
        simpa only [sub_zero, zpow_neg_one] using
          circleIntegral.integral_sub_center_inv (0 : ℂ) hr.ne'
      rw [hres]
      dsimp [c]
      field_simp [Complex.two_pi_I_ne_zero]
      <;> ring
    · rw [if_neg hj]
      have hn : (j : ℤ) + s - (d + 1 : ℕ) ≠ -1 := by omega
      have hzero := circleIntegral.integral_sub_zpow_of_ne hn (0 : ℂ) 0 r
      simp only [sub_zero] at hzero
      rw [hzero, mul_zero, mul_zero]
  have hsum := hInt.mul_left c
  change HasSum (fun j : ℕ => c * ∮ a in C(0, r), f j a)
    (negativeContour (fun a => scalarSum p a / a ^ (d + 1)) s r) at hsum
  simp only [hTerm] at hsum
  by_cases hsd : s ≤ d
  · rw [if_pos hsd]
    have hs : HasSum (fun j : ℕ => if j + s = d then PowerSeries.coeff j p else 0)
        (PowerSeries.coeff (d - s) p) := by
      convert hasSum_single (β := ℕ) (d - s)
        (f := fun j => if j + s = d then PowerSeries.coeff j p else 0)
        (fun j hj => by rw [if_neg (by omega)]) using 1
      rw [if_pos (Nat.sub_add_cancel hsd)]
    exact hsum.unique hs
  · rw [if_neg hsd]
    have hn (j : ℕ) : ¬j + s = d := by omega
    have hs : HasSum (fun j : ℕ => if j + s = d then PowerSeries.coeff j p else 0) 0 := by
      simpa only [if_neg (hn _)] using
        (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
    exact hsum.unique hs

private lemma regular_formal_coefficient {P : BPS} {K : AnnulusSeries}
    (h : PowerSeries.map inclusion P =
      PowerSeries.C (HahnSeries.single 1 1 : LaurentSeries ℂ) *
        PowerSeries.rescale (HahnSeries.single 1 1 : LaurentSeries ℂ) K)
    (s d : ℕ) :
    negativeCoefficient K s d =
      if s ≤ d then PowerSeries.coeff (d - s) (PowerSeries.coeff d P) else 0 := by
  let a : LaurentSeries ℂ := HahnSeries.single 1 1
  have hc := congrArg (PowerSeries.coeff d) h
  simp only [PowerSeries.coeff_map, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_rescale, ← mul_assoc, ← pow_succ'] at hc
  have hinv : (HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ)) * a ^ (d + 1) = 1 := by
    simp only [a, HahnSeries.single_pow, nsmul_eq_mul, mul_one, one_pow,
      HahnSeries.single_mul_single]
    rw [show -(d : ℤ) - 1 + ((d + 1 : ℕ) : ℤ) = 0 by omega]
    exact HahnSeries.C_one
  have hK : PowerSeries.coeff d K =
      HahnSeries.single (-(d : ℤ) - 1) (1 : ℂ) * inclusion (PowerSeries.coeff d P) := by
    rw [hc, ← mul_assoc, hinv, one_mul]
  rw [negativeCoefficient, hK, HahnSeries.coeff_single_mul, one_mul]
  change (inclusion (PowerSeries.coeff d P)).coeff
    (-(s : ℤ) - 1 - (-(d : ℤ) - 1)) = _
  rw [show -(s : ℤ) - 1 - (-(d : ℤ) - 1) = (d : ℤ) - s by omega]
  by_cases hsd : s ≤ d
  · rw [if_pos hsd, show (d : ℤ) - s = ((d - s : ℕ) : ℤ) by omega]
    exact LaurentSeries.coeff_coe_powerSeries _ _
  · rw [if_neg hsd, PowerSeries.coeff_coe, if_pos (by omega)]

private lemma original_fixed_a_coefficients {b a : ℂ} (hb : b ≠ 0) (root : ℂ)
    (ha0 : a ≠ 0) (ha : ‖a‖ < beta b) {eta : ℝ}
    (heta : 0 < eta) (hetab : eta < ‖a‖ * beta b) (d : ℕ) :
    (cauchyPowerSeries (TT b root a) 0 eta).coeff d =
      scalarSum (PowerSeries.coeff d (regularTT b root)) a / a ^ (d + 1) ∧
    (cauchyPowerSeries (UT b root a) 0 eta).coeff d =
      scalarSum (PowerSeries.coeff d (regularUT b root)) a / a ^ (d + 1) := by
  have hbeta : 0 < beta b := lt_min (by norm_num) (norm_pos_iff.mpr hb)
  have hxseries (x : ℂ) (hx : ‖x‖ < ‖a‖ * beta b) :
      HasSum (fun n : ℕ => scalarSum (PowerSeries.coeff n (regularTT b root)) a /
        a ^ (n + 1) * x ^ n) (TT b root a x) ∧
      HasSum (fun n : ℕ => scalarSum (PowerSeries.coeff n (regularUT b root)) a /
        a ^ (n + 1) * x ^ n) (UT b root a x) := by
    have hv : ‖x / a‖ < beta b := by
      rw [norm_div]
      exact (div_lt_iff₀ (norm_pos_iff.mpr ha0)).mpr (by nlinarith)
    obtain ⟨hT, hU⟩ := regular_evaluation hb root ha hv
    obtain ⟨heT, heU⟩ := regular_kernels (b := b) (v := x / a) root ha0
    have he : a * (x / a) = x := by field_simp [ha0]
    rw [he] at hT hU heT heU
    rw [heT] at hT
    rw [heU] at hU
    constructor
    · convert hT.2.mul_left a⁻¹ using 1
      · funext n
        rw [div_pow, pow_succ]
        field_simp [ha0]
        <;> ring
      · field_simp [ha0]
    · convert hU.2.mul_left a⁻¹ using 1
      · funext n
        rw [div_pow, pow_succ]
        field_simp [ha0]
        <;> ring
      · field_simp [ha0]
  have hT : HasFPowerSeriesAt (TT b root a)
      (.ofScalars ℂ (fun n => scalarSum (PowerSeries.coeff n (regularTT b root)) a /
        a ^ (n + 1))) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
      (mul_pos (norm_pos_iff.mpr ha0) hbeta)] with x hx
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      zero_add, mul_comm] using (hxseries x (by simpa using hx)).1
  have hU : HasFPowerSeriesAt (UT b root a)
      (.ofScalars ℂ (fun n => scalarSum (PowerSeries.coeff n (regularUT b root)) a /
        a ^ (n + 1))) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
      (mul_pos (norm_pos_iff.mpr ha0) hbeta)] with x hx
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul,
      zero_add, mul_comm] using (hxseries x (by simpa using hx)).2
  obtain ⟨hcT, hcU⟩ := literal_modulus_series hb root ha
    (eta := ⟨eta, heta.le⟩) heta hetab
  exact ⟨by simpa only [FormalMultilinearSeries.coeff_ofScalars] using
      congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff d)
        (hcT.hasFPowerSeriesAt.eq_formalMultilinearSeries hT),
    by simpa only [FormalMultilinearSeries.coeff_ofScalars] using
      congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff d)
        (hcU.hasFPowerSeriesAt.eq_formalMultilinearSeries hU)⟩

/-- The actual two circle integrals equal the existing formal cubic
coefficients. The amplitude is arbitrary, so in particular both geometric
roots of (1+b) root² = 1 are included. -/
theorem doubleContour_eq_negativeCoefficient {b : ℂ} (hb : b ≠ 0) (root : ℂ)
    (s d : ℕ) {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) :
    doubleContour (TT b root) s d r eta = negativeCoefficient (cubicTTSeries b root) s d ∧
    doubleContour (UT b root) s d r eta = negativeCoefficient (cubicUTSeries b root) s d := by
  obtain ⟨hT, hU⟩ := doubleContour_eq_integrated_cauchy hb root s d hr hrb heta hetab
  have hcircle (a : ℂ) (ha : a ∈ sphere (0 : ℂ) r) := by
    have hna : ‖a‖ = r := by simpa using ha
    have ha0 : a ≠ 0 := norm_pos_iff.mp (hna.symm ▸ hr)
    exact original_fixed_a_coefficients hb root ha0
      (by simpa only [hna] using hrb) heta (by simpa only [hna] using hetab) d
  have hnormal := regular_evaluation (a := (r : ℂ)) (v := 0) hb root
    (by simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr] using hrb)
    (by simpa using lt_min (by norm_num : (0 : ℝ) < 1) (norm_pos_iff.mpr hb))
  have hTp : Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d (regularTT b root))‖ * r ^ j) := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] using hnormal.1.1 d
  have hUp : Summable (fun j : ℕ =>
      ‖PowerSeries.coeff j (PowerSeries.coeff d (regularUT b root))‖ * r ^ j) := by
    simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr] using hnormal.2.1 d
  obtain ⟨hTf, hUf⟩ := regular_formal hb root
  constructor
  · rw [hT, regular_formal_coefficient hTf s d]
    calc
      _ = negativeContour (fun a => scalarSum (PowerSeries.coeff d (regularTT b root)) a /
          a ^ (d + 1)) s r := by
        unfold negativeContour
        congr 1
        apply circleIntegral.integral_congr hr.le
        intro a ha
        rw [(hcircle a ha).1]
      _ = _ := shifted_series_contour _ s d hr hTp
  · rw [hU, regular_formal_coefficient hUf s d]
    calc
      _ = negativeContour (fun a => scalarSum (PowerSeries.coeff d (regularUT b root)) a /
          a ^ (d + 1)) s r := by
        unfold negativeContour
        congr 1
        apply circleIntegral.integral_congr hr.le
        intro a ha
        rw [(hcircle a ha).2]
      _ = _ := shifted_series_contour _ s d hr hUp

/-- Evaluation uses the original formal coefficients, with genuine complex
HasSum convergence on every strict admissible disk. -/
theorem original_formal_coefficients_hasSum {b x : ℂ} (hb : b ≠ 0) (root : ℂ)
    (s : ℕ) {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) (hx : ‖x‖ < eta) :
    HasSum (fun d : ℕ => negativeCoefficient (cubicTTSeries b root) s d * x ^ d)
      (Tcoeff b root s x) ∧
    HasSum (fun d : ℕ => negativeCoefficient (cubicUTSeries b root) s d * x ^ d)
      (Ucoeff b root s x) := by
  have h := integrated_literal_hasSum hb root s hr hrb heta hetab hx
  have hT (d : ℕ) := (doubleContour_eq_negativeCoefficient hb root s d hr hrb heta hetab).1
  have hU (d : ℕ) := (doubleContour_eq_negativeCoefficient hb root s d hr hrb heta hetab).2
  simpa only [hT, hU] using h

/-- Every modulus in the original disk admits strict fixed contours. -/
theorem original_formal_coefficients_hasSum_disk {b x : ℂ} (hb : b ≠ 0) (root : ℂ)
    (s : ℕ) (hx : ‖x‖ < beta b ^ 2) :
    HasSum (fun d : ℕ => negativeCoefficient (cubicTTSeries b root) s d * x ^ d)
      (Tcoeff b root s x) ∧
    HasSum (fun d : ℕ => negativeCoefficient (cubicUTSeries b root) s d * x ^ d)
      (Ucoeff b root s x) := by
  have hbeta : 0 < beta b := lt_min (by norm_num) (norm_pos_iff.mpr hb)
  have hi : ‖x‖ / beta b < beta b := by
    apply (div_lt_iff₀ hbeta).mpr
    simpa only [pow_two] using hx
  obtain ⟨r, hir, hrb⟩ := exists_between hi
  have hr : 0 < r := (div_nonneg (norm_nonneg x) hbeta.le).trans_lt hir
  have hxr : ‖x‖ < r * beta b := (div_lt_iff₀ hbeta).mp hir
  obtain ⟨eta, hxe, he⟩ := exists_between hxr
  exact original_formal_coefficients_hasSum hb root s hr hrb
    ((norm_nonneg x).trans_lt hxe) he hxe

/-- The formal coefficients inherit the actual double Cauchy majorant and
the absolute two-index sum needed for evaluating the sewing recurrences. -/
theorem original_formal_coefficients_bounds {b x : ℂ} (hb : b ≠ 0) (root : ℂ)
    (s : ℕ) {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) (hx : ‖x‖ < eta) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ t d : ℕ,
      ‖negativeCoefficient (cubicTTSeries b root) t d‖ ≤ M * r ^ (t + 1) / eta ^ d ∧
      ‖negativeCoefficient (cubicUTSeries b root) t d‖ ≤ M * r ^ (t + 1) / eta ^ d) ∧
    Summable (fun td : ℕ × ℕ => ‖pairScalar s (td.1 + 1) / (td.1 + 1 : ℂ) *
      negativeCoefficient (cubicTTSeries b root) (td.1 + 1) td.2 * x ^ td.2‖) ∧
    Summable (fun td : ℕ × ℕ => ‖pairScalar s (td.1 + 1) / (td.1 + 1 : ℂ) *
      negativeCoefficient (cubicUTSeries b root) (td.1 + 1) td.2 * x ^ td.2‖) := by
  have hT (t d : ℕ) := (doubleContour_eq_negativeCoefficient hb root t d hr hrb heta hetab).1
  have hU (t d : ℕ) := (doubleContour_eq_negativeCoefficient hb root t d hr hrb heta hetab).2
  refine ⟨?_, ?_⟩
  · simpa only [hT, hU] using double_contours_bound hb root hr hrb heta hetab
  · simpa only [hT, hU] using double_contours_absolute hb root s hr hrb heta hetab hx

private lemma positive_supported_tsum (f : ℕ → ℂ) (n : ℕ)
    (hf : ∀ t : ℕ, n < t → f t = 0) :
    (∑' t : ℕ, f (t + 1)) = ∑ t ∈ Finset.Icc 1 n, f t := by
  classical
  calc
    _ = ∑ t ∈ Finset.range n, f (t + 1) := by
      apply tsum_eq_sum
      intro t ht
      have hnt : n ≤ t := by simpa only [Finset.mem_range, not_lt] using ht
      exact hf (t + 1) (by omega)
    _ = _ := by
      apply Finset.sum_bij (fun t _ => t + 1)
      · intro t ht
        have htn : t < n := Finset.mem_range.mp ht
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      · intro t ht u hu he
        omega
      · intro u hu
        obtain ⟨hu1, hun⟩ := Finset.mem_Icc.mp hu
        exact ⟨u - 1, Finset.mem_range.mpr (by omega), by omega⟩
      · intro t ht
        rfl

/-- The finite formal recurrences evaluate to the actual scalar annular
sewing equations. The double sums are absolutely convergent before they
are interchanged, and the original unhalved pairScalar is used. -/
theorem evaluated_original_sewing {b x : ℂ} (hb : b ≠ 0) (root : ℂ)
    (hroot : (1 + b) * root ^ 2 = 1) (s : ℕ) (hs : 0 < s)
    (hx : ‖x‖ < beta b ^ 2) :
    Summable (fun t : ℕ => pairScalar s (t + 1) / (t + 1 : ℂ) *
      Tcoeff b root (t + 1) x) ∧
    Summable (fun t : ℕ => pairScalar s (t + 1) / (t + 1 : ℂ) *
      Ucoeff b root (t + 1) x) ∧
    Tcoeff b root s x + x ^ s * (∑' t : ℕ,
      pairScalar s (t + 1) / (t + 1 : ℂ) * Ucoeff b root (t + 1) x) = 0 ∧
    Ucoeff b root s x + x ^ s * (∑' t : ℕ,
      pairScalar s (t + 1) / (t + 1 : ℂ) * Tcoeff b root (t + 1) x) =
        -x ^ s * currentRow b root s := by
  have hbeta : 0 < beta b := lt_min (by norm_num) (norm_pos_iff.mpr hb)
  have hi : ‖x‖ / beta b < beta b := by
    apply (div_lt_iff₀ hbeta).mpr
    simpa only [pow_two] using hx
  obtain ⟨r, hir, hrb⟩ := exists_between hi
  have hr : 0 < r := (div_nonneg (norm_nonneg x) hbeta.le).trans_lt hir
  obtain ⟨eta, hxe, hetab⟩ := exists_between ((div_lt_iff₀ hbeta).mp hir)
  have heta : 0 < eta := (norm_nonneg x).trans_lt hxe
  let T : ℕ → ℕ → ℂ := fun t d => negativeCoefficient (cubicTTSeries b root) t d
  let U : ℕ → ℕ → ℂ := fun t d => negativeCoefficient (cubicUTSeries b root) t d
  let k : ℕ → ℂ := fun t => pairScalar s (t + 1) / (t + 1 : ℂ)
  let WT : ℕ × ℕ → ℂ := fun tn => k tn.1 * T (tn.1 + 1) tn.2 * x ^ tn.2
  let WU : ℕ × ℕ → ℂ := fun tn => k tn.1 * U (tn.1 + 1) tn.2 * x ^ tn.2
  obtain ⟨_, hTab, hUab⟩ := original_formal_coefficients_bounds hb root s hr hrb heta hetab hxe
  have hTW : Summable WT := hTab.of_norm
  have hUW : Summable WU := hUab.of_norm
  have hTsum (t : ℕ) := (original_formal_coefficients_hasSum_disk hb root t hx).1
  have hUsum (t : ℕ) := (original_formal_coefficients_hasSum_disk hb root t hx).2
  have hTinner (t : ℕ) : (∑' n : ℕ, WT (t, n)) =
      k t * Tcoeff b root (t + 1) x := by
    have h := ((hTsum (t + 1)).mul_left (k t)).tsum_eq
    simpa only [WT, T, mul_assoc] using h
  have hUinner (t : ℕ) : (∑' n : ℕ, WU (t, n)) =
      k t * Ucoeff b root (t + 1) x := by
    have h := ((hUsum (t + 1)).mul_left (k t)).tsum_eq
    simpa only [WU, U, mul_assoc] using h
  have hTrows : Summable (fun t : ℕ => k t * Tcoeff b root (t + 1) x) := by
    simpa only [hTinner] using hTW.prod
  have hUrows : Summable (fun t : ℕ => k t * Ucoeff b root (t + 1) x) := by
    simpa only [hUinner] using hUW.prod
  have hTswap : (∑' n : ℕ, ∑' t : ℕ, WT (t, n)) =
      ∑' t : ℕ, k t * Tcoeff b root (t + 1) x := by
    rw [hTW.tsum_comm]
    simp only [hTinner]
  have hUswap : (∑' n : ℕ, ∑' t : ℕ, WU (t, n)) =
      ∑' t : ℕ, k t * Ucoeff b root (t + 1) x := by
    rw [hUW.tsum_comm]
    simp only [hUinner]
  have hTouter : HasSum (fun n : ℕ => ∑' t : ℕ, WT (t, n))
      (∑' t : ℕ, k t * Tcoeff b root (t + 1) x) := by
    rw [← hTswap]
    exact hTW.prod_symm.prod.hasSum
  have hUouter : HasSum (fun n : ℕ => ∑' t : ℕ, WU (t, n))
      (∑' t : ℕ, k t * Ucoeff b root (t + 1) x) := by
    rw [← hUswap]
    exact hUW.prod_symm.prod.hasSum
  have hfiniteT (n : ℕ) : (∑' t : ℕ, k t * T (t + 1) n) =
      ∑ t ∈ Finset.Icc 1 n, pairScalar s t / (t : ℂ) * T t n := by
    apply positive_supported_tsum (fun t => pairScalar s t / (t : ℂ) * T t n) n
    intro t hnt
    rw [show T t n = 0 from cubic_tt_pole_bound b root hb t n hnt.le, mul_zero]
  have hfiniteU (n : ℕ) : (∑' t : ℕ, k t * U (t + 1) n) =
      ∑ t ∈ Finset.Icc 1 n, pairScalar s t / (t : ℂ) * U t n := by
    apply positive_supported_tsum (fun t => pairScalar s t / (t : ℂ) * U t n) n
    intro t hnt
    rw [show U t n = 0 from cubic_ut_pole_bound b root hb t n hnt, mul_zero]
  have hrec (n : ℕ) :
      T s (n + s) = -(∑' t : ℕ, k t * U (t + 1) n) ∧
      U s (n + s) = -(if n = 0 then currentRow b root s else 0) -
        ∑' t : ℕ, k t * T (t + 1) n := by
    obtain ⟨hT, hU⟩ := cubic_original_coefficient_identity b root hb hroot s (n + s) hs
    have he : (n + s = s) ↔ n = 0 := by omega
    simpa only [T, U, if_pos (show s ≤ n + s by omega), Nat.add_sub_cancel_right,
      he, ← hfiniteT n, ← hfiniteU n] using And.intro hT hU
  have hTtail : HasSum (fun n : ℕ => T s (n + s) * x ^ (n + s))
      (-x ^ s * (∑' t : ℕ, k t * Ucoeff b root (t + 1) x)) := by
    convert hUouter.mul_left (-x ^ s) using 1
    funext n
    rw [(hrec n).1, pow_add]
    simp only [WU, tsum_mul_right]
    ring
  have hcurrent : HasSum (fun n : ℕ =>
      (if n = 0 then currentRow b root s else 0) * x ^ n) (currentRow b root s) := by
    convert hasSum_single (β := ℕ) 0
      (f := fun n => (if n = 0 then currentRow b root s else 0) * x ^ n)
      (fun n hn => by simp [hn]) using 1
    simp
  have hUtail : HasSum (fun n : ℕ => U s (n + s) * x ^ (n + s))
      (-x ^ s * (currentRow b root s +
        ∑' t : ℕ, k t * Tcoeff b root (t + 1) x)) := by
    convert (hcurrent.add hTouter).mul_left (-x ^ s) using 1
    funext n
    rw [(hrec n).2, pow_add]
    simp only [WT, tsum_mul_right]
    ring
  have hTzero : (∑ n ∈ Finset.range s, T s n * x ^ n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [show T s n = 0 from cubic_tt_pole_bound b root hb s n
      (Nat.le_of_lt (Finset.mem_range.mp hn)), zero_mul]
  have hUzero : (∑ n ∈ Finset.range s, U s n * x ^ n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [show U s n = 0 from cubic_ut_pole_bound b root hb s n
      (Finset.mem_range.mp hn), zero_mul]
  have hTeval := (hasSum_nat_add_iff (f := fun n : ℕ => T s n * x ^ n) s).mp hTtail
  have hUeval := (hasSum_nat_add_iff (f := fun n : ℕ => U s n * x ^ n) s).mp hUtail
  rw [hTzero, add_zero] at hTeval
  rw [hUzero, add_zero] at hUeval
  have hTeq := (hTsum s).unique hTeval
  have hUeq := (hUsum s).unique hUeval
  refine ⟨hTrows, hUrows, ?_, ?_⟩
  · change Tcoeff b root s x + x ^ s * (∑' t : ℕ,
      k t * Ucoeff b root (t + 1) x) = 0
    rw [hTeq]
    ring
  · change Ucoeff b root s x + x ^ s * (∑' t : ℕ,
      k t * Tcoeff b root (t + 1) x) = -x ^ s * currentRow b root s
    rw [hUeq]
    ring

private lemma sqrt_index_ne_zero (n : ℕ) : (Real.sqrt (n + 1 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < n + 1)))

private lemma sqrt_index_sq (n : ℕ) :
    (Real.sqrt (n + 1 : ℝ) : ℂ) ^ 2 = (n + 1 : ℂ) := by
  exact_mod_cast (Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1))

private lemma normalized_matrix_row {z : ℂ} (hz : z ≠ 0) (n m : ℕ) (c : ℂ) :
    OriginalGaussianMatrix.matrixEntry z (n + 1) (m + 1) *
        (c / ((Real.sqrt (m + 1 : ℝ) : ℂ) * z ^ (m + 1))) =
      ((z ^ 2) ^ (n + 1) / ((Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1))) *
        (pairScalar (n + 1) (m + 1) / (m + 1 : ℂ) * c) := by
  have hm : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hpow : (z ^ 2) ^ (n + 1) = (z ^ (n + 1)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 (n + 1)]
  rw [OriginalGaussianMatrix.matrixEntry, pow_add, hpow]
  field_simp [sqrt_index_ne_zero n, sqrt_index_ne_zero m, hz, hm]
  <;> ring_nf
  <;> simp only [sqrt_index_sq m]
  <;> ring

/-- The Hilbert vectors are formed from the actual contour coefficients
using the proved lp membership. The existing signed block theorem is
applied only after the actual scalar sewing equations have been evaluated. -/
theorem original_hilbert_correspondence {b z : ℂ} (root : ℂ)
    (hroot : (1 + b) * root ^ 2 = 1) (hz0 : 0 < ‖z‖) (hz : ‖z‖ < beta b) :
    let p : OriginalGaussianResolvent.H :=
      ⟨pValue b root z, (normalized_coefficients_mem root hz0 hz).2.2.1⟩
    let q : OriginalGaussianResolvent.H :=
      ⟨qValue b root z, (normalized_coefficients_mem root hz0 hz).2.2.2⟩
    p = selfOperator z (eVector b root z hz) ∧
      q = mixedOperator z (eVector b root z hz) := by
  let p : OriginalGaussianResolvent.H :=
    ⟨pValue b root z, (normalized_coefficients_mem root hz0 hz).2.2.1⟩
  let q : OriginalGaussianResolvent.H :=
    ⟨qValue b root z, (normalized_coefficients_mem root hz0 hz).2.2.2⟩
  let e := eVector b root z hz
  change p = selfOperator z e ∧ q = mixedOperator z e
  have hb : b ≠ 0 := norm_pos_iff.mp (hz0.trans (hz.trans_le (min_le_right _ _)))
  have hz1 : ‖z‖ < 1 := hz.trans_le (min_le_left _ _)
  have hzN : z ≠ 0 := norm_pos_iff.mp hz0
  have hx : ‖z ^ 2‖ < beta b ^ 2 := by
    rw [norm_pow]
    nlinarith [norm_nonneg z, lt_min (by norm_num : (0 : ℝ) < 1) (norm_pos_iff.mpr hb)]
  have hp (n : ℕ) : p n + (∑' m : ℕ,
      OriginalGaussianMatrix.matrixEntry z (n + 1) (m + 1) * q m) =
        -(0 : OriginalGaussianResolvent.H) n := by
    obtain ⟨_, _, hT, _⟩ := evaluated_original_sewing hb root hroot (n + 1) (by omega) hx
    change pValue b root z n + (∑' m : ℕ,
      OriginalGaussianMatrix.matrixEntry z (n + 1) (m + 1) * qValue b root z m) = 0
    simp only [pValue, qValue, normalized_matrix_row hzN, tsum_mul_left]
    have h := congrArg (fun w : ℂ =>
      w / ((Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1))) hT
    convert h using 1 <;> ring
  have hq (n : ℕ) : q n + (∑' m : ℕ,
      OriginalGaussianMatrix.matrixEntry z (n + 1) (m + 1) * p m) = -e n := by
    obtain ⟨_, _, _, hU⟩ := evaluated_original_sewing hb root hroot (n + 1) (by omega) hx
    change qValue b root z n + (∑' m : ℕ,
      OriginalGaussianMatrix.matrixEntry z (n + 1) (m + 1) * pValue b root z m) =
        -eValue b root z n
    simp only [pValue, qValue, normalized_matrix_row hzN, tsum_mul_left]
    have h := congrArg (fun w : ℂ =>
      w / ((Real.sqrt (n + 1 : ℝ) : ℂ) * z ^ (n + 1))) hU
    convert h using 1
    · ring
    · have hpow : (z ^ 2) ^ (n + 1) = (z ^ (n + 1)) ^ 2 := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 (n + 1)]
      simp only [eValue, hpow]
      field_simp [sqrt_index_ne_zero n, hzN]
      <;> ring
  have hblocks := (original_coefficient_equations_iff hz1 e 0 p q).mp ⟨hp, hq⟩
  simpa only [map_zero, add_zero] using hblocks

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicAnalyticLaurentBridge
