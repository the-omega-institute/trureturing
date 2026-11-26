/- GID: D5/S3/Quantum/Analysis/RefinedBMVThreeSpectrumReduction
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/RefinedBMVThreeSpectrumReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The three-spectral-value trace lower bounds from log-gap positivity. -/

import D5.S3.Quantum.Analysis.RefinedBMVUniformDiscriminant
import D5.S3.Quantum.Analysis.RefinedBMVUniformThreeSpectrum

/-! The ordered scalar discriminant gives the uniform three-spectral-value comparison. -/

open scoped BigOperators
open Filter Set

namespace RefinedBMV.DividedDifference

open DimThree (defect gaps mem_gaps_iff_total)
open UniformThreeSpectrum (ScalarPairing)

private theorem defect_mul_roots (p : ℕ) (c a x y : ℝ) :
    defect p (c*a) (c*x) (c*y) = c^(3*p) * defect p a x y := by
  unfold defect
  rw [mul_sub]
  congr 1
  · rw [← List.sum_map_mul_left]
    apply congrArg List.sum
    refine List.map_congr_left fun g hg => ?_
    have ht := (mem_gaps_iff_total p g).mp hg
    change ((c*a)^3)^g.1 * ((c*x)^3)^g.2.1 * ((c*y)^3)^g.2.2 =
      c^(3*p) * ((a^3)^g.1 * (x^3)^g.2.1 * (y^3)^g.2.2)
    have hpow : ((c^3)^g.1 * (c^3)^g.2.1 * (c^3)^g.2.2) = c^(3*p) := by
      rw [← pow_add, ← pow_add, ht, ← pow_mul]
    rw [← hpow]
    simp only [mul_pow]
    ring
  · have h : c * a * (c * x) * (c * y) = c^3 * (a*x*y) := by ring
    rw [h, mul_pow, ← pow_mul]
    ring

theorem quartic_scale (p : ℕ) (c a x y : ℝ) :
    quartic p (c*a) (c*x) (c*y) = c^(12*p) * quartic p a x y := by
  unfold quartic
  simp only [defect_mul_roots]
  rw [show 12 * p = (3*p)*4 by omega, pow_mul c (3*p) 4]
  ring

private theorem continuous_defect (p : ℕ) {α : Type*} [TopologicalSpace α]
    {a x y : α → ℝ} (ha : Continuous a) (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun z => defect p (a z) (x z) (y z)) := by
  unfold defect
  apply Continuous.sub _ <| continuous_const.mul (((ha.mul hx).mul hy).pow p)
  generalize gaps p = g
  induction g with
  | nil => simpa using (continuous_const : Continuous (fun _ : α => (0 : ℝ)))
  | cons g gs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((((ha.pow 3).pow g.1).mul ((hx.pow 3).pow g.2.1)).mul
      ((hy.pow 3).pow g.2.2)).add ih

private theorem continuous_quartic (p : ℕ) {α : Type*} [TopologicalSpace α]
    {a x y : α → ℝ} (ha : Continuous a) (hx : Continuous x) (hy : Continuous y) :
    Continuous (fun z => quartic p (a z) (x z) (y z)) := by
  have hd := continuous_defect p ha hx hy
  have hq := (continuous_defect p ha ha hy).mul (continuous_defect p hx hx hy)
  have hw := (continuous_defect p ha hx hx).mul (continuous_defect p ha hy hy)
  exact ((continuous_const.mul hq).mul hw).sub (((hd.pow 2).sub hq).sub hw |>.pow 2)

/-- Positivity in log-gap coordinates gives the unnormalized nonnegative-root result. -/
theorem quartic_nonneg_of_log_gaps (p : ℕ)
    (certificate : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      0 ≤ clearedQuartic (p : ℝ) (Real.exp (3*s)) (Real.exp (3*(s+t)))
        (Real.exp ((p : ℝ)*s)) (Real.exp ((p : ℝ)*(s+t))))
    {a x y : ℝ} (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) :
    0 ≤ quartic p a x y := by
  have strict (b u v : ℝ) (hb : 0 < b) (hbu : b < u) (huv : u < v) :
      0 ≤ quartic p b u v := by
    have hu : 0 < u := hb.trans hbu
    have hv : 0 < v := hu.trans huv
    let s := Real.log (u/b)
    let t := Real.log (v/u)
    have hs : 0 ≤ s := Real.log_nonneg ((one_le_div hb).mpr hbu.le)
    have ht : 0 ≤ t := Real.log_nonneg ((one_le_div hu).mpr huv.le)
    have hx' : Real.exp s = u/b := Real.exp_log (div_pos hu hb)
    have hy' : Real.exp (s+t) = v/b := by
      rw [Real.exp_add, hx', Real.exp_log (div_pos hv hu)]
      field_simp
    have h := certificate s t hs ht
    simp only [← Nat.cast_ofNat (R := ℝ) (n := 3), Real.exp_nat_mul, hx', hy'] at h
    rw [clearedQuartic_eq] at h
    have h₀ : 0 < denominator ((u/b)^3) ((v/b)^3) := by
      have h1 : 1 < u/b := (lt_div_iff₀ hb).2 (by simpa using hbu)
      have h2 : u/b < v/b := (div_lt_div_iff_of_pos_right hb).2 huv
      have h3 : 0 < u/b := div_pos hu hb
      have h4 : 0 < v/b := div_pos hv hb
      have h23 := pow_lt_pow_left₀ h2 h3.le (by decide : (3 : ℕ) ≠ 0)
      have h13 := pow_lt_pow_left₀ h1 (by positivity : 0 ≤ (1 : ℝ)) (by decide : (3 : ℕ) ≠ 0)
      simp only [one_pow] at h13
      unfold denominator
      exact mul_pos (mul_pos (sub_pos.mpr h13) (sub_pos.mpr (h13.trans h23))) (sub_pos.mpr h23)
    have hscale : 0 < 16 * denominator ((u/b)^3) ((v/b)^3)^4 := by positivity
    have hh := nonneg_of_mul_nonneg_right h hscale
    have hh' := mul_nonneg (pow_nonneg hb.le (12*p)) hh
    rw [← quartic_scale] at hh'
    simpa [mul_div_cancel₀ _ hb.ne', mul_comm b] using hh'
  let f (t : ℝ) := quartic p (a+t) (x+2*t) (y+3*t)
  have hf : Continuous f := continuous_quartic p (by fun_prop) (by fun_prop) (by fun_prop)
  have hs : Ioi (0 : ℝ) ⊆ { t | 0 ≤ f t } := by
    intro t ht
    have ht' : 0 < t := ht
    exact strict _ _ _ (by linarith) (by linarith) (by linarith)
  have hc₀ : Continuous (fun _ : ℝ => (0 : ℝ)) := continuous_const
  have hc := closure_minimal hs (isClosed_le hc₀ hf)
  have hz : (0 : ℝ) ∈ closure (Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    change (0 : ℝ) ≤ 0
    exact le_rfl
  have h0 : 0 ≤ f 0 := hc hz
  simpa [f] using h0

open DimThree (paired)

private theorem homogeneous_swap_general (p : ℕ) (a x y : ℝ) :
    homogeneousThree p x a y = homogeneousThree p a x y := by
  unfold homogeneousThree homogeneousTwo
  simp only [Finset.mul_sum]
  calc
    _ = ∑ j ∈ Finset.range (p + 1), ∑ i ∈ Finset.range (p - j + 1),
        x ^ i * (a ^ j * y ^ (p - i - j)) := by
      apply Finset.sum_comm'
      intro i j
      simp only [Finset.mem_range]
      omega
    _ = _ := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [show p - i - j = p - j - i by omega]
      ring

theorem defect_swap_general (p : ℕ) (a x y : ℝ) :
    defect p x a y = defect p a x y := by
  rw [defect_eq_homogeneous, defect_eq_homogeneous, homogeneous_swap_general, mul_comm x a]

private theorem pairing_ordered_of_quartic (p : ℕ) {a x y : ℝ}
    (ha : 0 ≤ a) (hax : a ≤ x) (hxy : x ≤ y) (hqrt : 0 ≤ quartic p a x y) :
    defect p a x y ≤ paired (defect p) a x y := by
  have hx := ha.trans hax
  have hy := hx.trans hxy
  let d := defect p a x y
  let q := defect p a a y * defect p x x y
  let w := defect p a x x * defect p a y y
  have hn {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      0 ≤ defect p a x y := (Real.sqrt_nonneg _).trans (DimThree.defect_corner p ha hx hy)
  have hd : 0 ≤ d := hn ha hx hy
  have hq : 0 ≤ q := mul_nonneg (hn ha ha hy) (hn hx hx hy)
  have hw : 0 ≤ w := mul_nonneg (hn ha hx hx) (hn ha hy hy)
  change 0 ≤ 4 * q * w - (d ^ 2 - q - w) ^ 2 at hqrt
  have hs : (d ^ 2 - q - w) ^ 2 ≤ (2 * Real.sqrt q * Real.sqrt w) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hq, Real.sq_sqrt hw]
    linarith
  have hs' : d ^ 2 - q - w ≤ 2 * Real.sqrt q * Real.sqrt w := by
    have h := (sq_le_sq₀ (abs_nonneg (d ^ 2 - q - w))
      (by positivity : 0 ≤ 2 * Real.sqrt q * Real.sqrt w)).mp (by rwa [sq_abs])
    exact (le_abs_self _).trans h
  have hsum : d ≤ Real.sqrt q + Real.sqrt w := by
    apply (sq_le_sq₀ hd (by positivity)).mp
    nlinarith [Real.sq_sqrt hq, Real.sq_sqrt hw]
  change d ≤ Real.sqrt q + Real.sqrt (defect p a x x * defect p a y y) at hsum
  rw [← UniformThreeSpectrum.defect_cycle_all p a x x,
    ← UniformThreeSpectrum.defect_cycle_all p a y y] at hsum
  change d ≤ Real.sqrt q + Real.sqrt (defect p x x a * defect p y y a) at hsum
  unfold paired
  linarith [Real.sqrt_nonneg (defect p a a x * defect p y y x)]

theorem scalarPairing_of_quartic (p : ℕ)
    (hcert : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → 0 ≤ quartic p a b c) :
    ScalarPairing p := by
  intro a b c ha hb hc
  have hs (x y z : ℝ) : paired (defect p) y x z = paired (defect p) x y z := by
    unfold paired
    rw [mul_comm (defect p y y z) (defect p x x z)]
    abel
  have hr (x y z : ℝ) : paired (defect p) y z x = paired (defect p) x y z := by
    unfold paired
    rw [mul_comm (defect p z z y) (defect p x x y),
      mul_comm (defect p y y z) (defect p x x z)]
    abel
  have ordered (x y z : ℝ) (hx : 0 ≤ x) (hxy : x ≤ y) (hyz : y ≤ z) :=
    pairing_ordered_of_quartic p hx hxy hyz (hcert x y z hx hxy hyz)
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact ordered a b c ha hab hbc
    · rcases le_total a c with hac | hca
      · have h := ordered a c b ha hac hcb
        rw [← defect_swap_general p a c b, ← hs a c b,
          ← UniformThreeSpectrum.defect_cycle_all p c a b, ← hr c a b] at h
        exact h
      · simpa only [UniformThreeSpectrum.defect_cycle_all p c a b, hr c a b] using
          ordered c a b hc hca hab
  · rcases le_total a c with hac | hca
    · simpa only [defect_swap_general p a b c, hs a b c] using ordered b a c hb hba hac
    · rcases le_total b c with hbc | hcb
      · simpa only [UniformThreeSpectrum.defect_cycle_all p a b c, hr a b c] using
          ordered b c a hb hbc hca
      · have h := ordered c b a hc hcb hba
        rw [← UniformThreeSpectrum.defect_cycle_all p c b a, ← hr c b a,
          defect_swap_general p a b c, hs a b c] at h
        exact h


open Matrix NormedSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Scalar positivity of the explicit log-gap polynomial suffices for the refined
product bound with at most three distinct eigenvalues of the first factor. -/
theorem product_bound_of_log_gaps {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (A B : Matrix n n ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hs : (Finset.univ.image hA.isHermitian.eigenvalues).card ≤ 3)
    (certificate : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      0 ≤ clearedQuartic (p : ℝ) (Real.exp (3*s)) (Real.exp (3*(s+t)))
        (Real.exp ((p : ℝ)*s)) (Real.exp ((p : ℝ)*(s+t)))) :
    trace (((A ^ ((p : ℝ) / 3)) * B) ^ 3) ≤ DimThree.wordMean p A B := by
  exact UniformThreeSpectrum.product_bound
    (scalarPairing_of_quartic p (fun _ _ _ => quartic_nonneg_of_log_gaps p certificate))
    (defect_swap_general p) A B hA hB hs

/-- Scalar positivity of the explicit log-gap polynomial suffices for the refined
exponential bound with at most three distinct eigenvalues of the first matrix. -/
theorem exponential_bound_of_log_gaps {n : Type*} [Fintype n] [DecidableEq n]
    (p : ℕ) (H K : Matrix n n ℂ) (hH : H.IsHermitian) (hK : K.IsHermitian)
    (hs : (Finset.univ.image hH.eigenvalues).card ≤ 3)
    (certificate : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      0 ≤ clearedQuartic (p : ℝ) (Real.exp (3*s)) (Real.exp (3*(s+t)))
        (Real.exp ((p : ℝ)*s)) (Real.exp ((p : ℝ)*(s+t)))) :
    trace (exp ((p : ℝ) • H + (3 : ℝ) • K)) ≤ DimThree.wordMean p (exp H) (exp K) := by
  exact UniformThreeSpectrum.exponential_bound
    (scalarPairing_of_quartic p (fun _ _ _ => quartic_nonneg_of_log_gaps p certificate))
    (defect_swap_general p) H K hH hK hs

#print axioms product_bound_of_log_gaps
#print axioms exponential_bound_of_log_gaps

end RefinedBMV.DividedDifference
