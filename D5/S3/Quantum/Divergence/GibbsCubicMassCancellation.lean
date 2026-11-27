/- GID: D5/S3/Quantum/Divergence/GibbsCubicMassCancellation
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/GibbsCubicMassCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A joint bound on square-log entropy and cubic mass in centered Gibbs translation. -/

import D5.S3.Quantum.Divergence.GibbsCubicSignedMoment
import Mathlib.Analysis.Calculus.Deriv.Shift
import OmegaBuild.Commands

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Divergence.GibbsCubicMassCancellation

private theorem sq_mul_log_le_cubic {z : ℝ} (hz : 0 < z) :
    z ^ 2 * Real.log z ≤ (z - 1) + (3 / 2 : ℝ) * (z - 1) ^ 2 +
      (1 / 3 : ℝ) * (z - 1) ^ 3 := by
  let gap (y : ℝ) : ℝ :=
    (1 / 3 : ℝ) * y ^ 3 + (1 / 2 : ℝ) * y ^ 2 - y + 1 / 6 - y ^ 2 * Real.log y
  let gap' (y : ℝ) : ℝ := y ^ 2 - 1 - 2 * (y * Real.log y)
  have hgap (y : ℝ) (hy : 0 < y) : HasDerivAt gap (gap' y) y := by
    have hlog := (hasDerivAt_pow 2 y).mul (Real.hasDerivAt_log hy.ne')
    have h := (((((hasDerivAt_pow 3 y).const_mul (1 / 3 : ℝ)).add
      ((hasDerivAt_pow 2 y).const_mul (1 / 2 : ℝ))).sub (hasDerivAt_id' y)).add_const
      (1 / 6 : ℝ)).sub hlog
    convert h using 1
    dsimp only [gap']
    field_simp [hy.ne']
    ring
  have hgap' (y : ℝ) (hy : 0 < y) :
      HasDerivAt gap' (2 * (y - 1 - Real.log y)) y := by
    have h := ((hasDerivAt_pow 2 y).sub_const 1).sub
      ((Real.hasDerivAt_mul_log hy.ne').const_mul (2 : ℝ))
    convert h using 1
    ring
  have hc : ConvexOn ℝ (Set.Ioi 0) gap := by
    refine convexOn_of_hasDerivWithinAt2_nonneg (f' := gap')
      (f'' := fun y => 2 * (y - 1 - Real.log y)) (convex_Ioi 0) ?_ ?_ ?_ ?_
    · refine continuousOn_of_forall_continuousAt (fun y hy => ?_)
      exact (hgap y hy).continuousAt
    · intro y hy
      rw [interior_Ioi] at hy
      exact (hgap y hy).hasDerivWithinAt
    · intro y hy
      rw [interior_Ioi] at hy
      exact (hgap' y hy).hasDerivWithinAt
    · intro y hy
      rw [interior_Ioi] at hy
      exact mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.log_le_sub_one_of_pos hy))
  have h1 : (1 : ℝ) ∈ interior (Set.Ioi 0) := by
    rw [interior_Ioi]
    exact Set.mem_Ioi.mpr zero_lt_one
  have hd1 : HasDerivAt gap 0 1 := by simpa [gap'] using hgap 1 zero_lt_one
  have hmin := hc.isMinOn_of_rightDeriv_eq_zero h1
    (hd1.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi 1))
  have hzero : gap 1 = 0 := by norm_num [gap]
  have hnonneg : 0 ≤ gap z := by
    simpa only [hzero] using (isMinOn_iff.mp hmin z hz)
  dsimp only [gap] at hnonneg
  linarith only [hnonneg]

private theorem centered_polynomial_nonneg {ι : Type*} [Fintype ι] (p y : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmass : (∑ i, p i) = 1) (hmean : (∑ i, p i * y i) = 0)
    (k₀ k₁ k₂ k₃ : ℝ)
    (hpoint : ∀ i, p i ≠ 0 → 0 ≤ k₀ + k₁ * y i + k₂ * y i ^ 2 + k₃ * y i ^ 3) :
    0 ≤ k₀ + k₂ * (∑ i, p i * y i ^ 2) + k₃ * (∑ i, p i * y i ^ 3) := by
  calc
    0 ≤ ∑ i, p i * (k₀ + k₁ * y i + k₂ * y i ^ 2 + k₃ * y i ^ 3) :=
      Finset.sum_nonneg fun i _ => by
        by_cases hi : p i = 0
        · simp [hi]
        exact mul_nonneg (hp i) (hpoint i hi)
    _ = ∑ i, (k₀ * p i + k₁ * (p i * y i) + k₂ * (p i * y i ^ 2) +
        k₃ * (p i * y i ^ 3)) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hmass, hmean, mul_one,
        mul_zero, add_zero]

private theorem mass_error_le {v h : ℝ} (hv : 0 ≤ v) (hvmax : v ≤ 5 / 32)
    (hh : 0 ≤ h) (hsharp : h ≤ (31 / 8 : ℝ) * v - v ^ 2 / (7 / 8 : ℝ)) :
    h * (h - 2 * v) / (2 + h) ≤ (13 / 32 : ℝ) * v := by
  have hden : 0 < 2 + h := by linarith
  have hlinear : h ≤ (31 / 8 : ℝ) * v :=
    hsharp.trans (sub_le_self _ (div_nonneg (sq_nonneg v) (by norm_num)))
  have hquot (m q : ℝ) (hm : h ≤ m) (hq : q = m / (2 + m)) : h / (2 + h) ≤ q := by
    rw [hq, div_le_div_iff₀ hden (by linarith : 0 < 2 + m)]
    linarith only [hm]
  by_cases herr : h ≤ 2 * v
  · exact (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hh
      (sub_nonpos.mpr herr)) hden.le).trans (by positivity)
  have herr₀ : 0 ≤ h - 2 * v := by linarith
  rw [mul_comm h, mul_div_assoc, mul_comm (h - 2 * v)]
  by_cases hsmall : v ≤ 1 / 8
  · have hq : h / (2 + h) ≤ 31 / 159 :=
      hquot (31 / 64) _ (by linarith only [hlinear, hsmall]) (by norm_num)
    have he : h - 2 * v ≤ (15 / 8 : ℝ) * v := by linarith only [hlinear]
    calc
      _ ≤ (31 / 159 : ℝ) * ((15 / 8 : ℝ) * v) :=
        mul_le_mul hq he herr₀ (by norm_num)
      _ ≤ _ := by nlinarith only [hv]
  · have hq : h / (2 + h) ≤ 155 / 667 :=
      hquot (155 / 256) _ (by linarith only [hlinear, hvmax]) (by norm_num)
    have hvlarge : (1 / 8 : ℝ) ≤ v := le_of_not_ge hsmall
    have hvsq := mul_nonneg hv (sub_nonneg.mpr hvlarge)
    have he : h - 2 * v ≤ (97 / 56 : ℝ) * v := by nlinarith only [hsharp, hvsq]
    calc
      _ ≤ (155 / 667 : ℝ) * ((97 / 56 : ℝ) * v) :=
        mul_le_mul hq he herr₀ (by norm_num)
      _ ≤ _ := by nlinarith only [hv]

/-- The joint square-log and cubic-mass bound for a finite probability with mean one.
The positive interval containing the support may have upper endpoint at most 54/25
times its lower endpoint. The supported values also satisfy the cap 15/8. -/
theorem squareLog_sub_cubicMass_le {ι : Type*} [Fintype ι] (p z : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hmass : (∑ i, p i) = 1) (hmean : (∑ i, p i * z i) = 1)
    {a b : ℝ} (ha : 0 < a) (hinterval : ∀ i, p i ≠ 0 → a ≤ z i ∧ z i ≤ b)
    (hratio : b ≤ (54 / 25 : ℝ) * a) (hcap : ∀ i, p i ≠ 0 → z i ≤ 15 / 8) :
    let v := ∑ i, p i * (z i - 1) ^ 2
    3 * (∑ i, p i * z i ^ 2 * Real.log (z i)) -
      (1 + v) * Real.log (∑ i, p i * z i ^ 3) ≤ (61 / 32 : ℝ) * v := by
  intro v
  let y (i : ι) : ℝ := z i - 1
  let c := ∑ i, p i * y i ^ 3
  let h := 3 * v + c
  have hymean : (∑ i, p i * y i) = 0 := by
    simp only [y, mul_sub, mul_one, Finset.sum_sub_distrib, hmean, hmass, sub_self]
  have hpoly (k₀ k₁ k₂ k₃ : ℝ)
      (hpoint : ∀ i, p i ≠ 0 → 0 ≤ k₀ + k₁ * y i + k₂ * y i ^ 2 + k₃ * y i ^ 3) :
      0 ≤ k₀ + k₂ * v + k₃ * c :=
    centered_polynomial_nonneg p y hp hmass hymean k₀ k₁ k₂ k₃ hpoint
  have hv : 0 ≤ v := Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (sq_nonneg _)
  have hb : 1 ≤ b := calc
    1 = ∑ i, p i * z i := hmean.symm
    _ ≤ ∑ i, p i * b := Finset.sum_le_sum fun i _ => by
      by_cases hi : p i = 0
      · simp [hi]
      exact mul_le_mul_of_nonneg_left (hinterval i hi).2 (hp i)
    _ = b := by rw [← Finset.sum_mul, hmass, one_mul]
  have hvar : v ≤ (b - 1) * (1 - a) := by
    have hh := hpoly ((b - 1) * (1 - a)) (b + a - 2) (-1) 0 (by
      intro i hi
      have hz := hinterval i hi
      have hproduct := mul_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr hz.2)
      nlinarith only [hproduct, show y i = z i - 1 from rfl])
    linarith only [hh]
  have hvmax : v ≤ 5 / 32 := calc
    v ≤ (b - 1) * (1 - a) := hvar
    _ ≤ (b - 1) * (1 - (25 / 54 : ℝ) * b) :=
      mul_le_mul_of_nonneg_left (by linarith only [hratio]) (sub_nonneg.mpr hb)
    _ ≤ 5 / 32 := by nlinarith only [sq_nonneg (b - 79 / 50)]
  have hh : 0 ≤ h := by
    have hh' := hpoly 0 0 3 1 (by
      intro i hi
      have hproduct := mul_nonneg (sq_nonneg (y i)) (show 0 ≤ z i + 2 by
        linarith only [ha, (hinterval i hi).1])
      have hi' : z i + 2 = y i + 3 := by dsimp [y]; ring
      rw [hi'] at hproduct
      nlinarith only [hproduct])
    simpa only [h, zero_add, one_mul] using hh'
  have hmass₃ : (∑ i, p i * z i ^ 3) = 1 + h := calc
    _ = ∑ i, (p i + 3 * (p i * y i) + 3 * (p i * y i ^ 2) + p i * y i ^ 3) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      dsimp only [y]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hmass, hymean,
        mul_zero, add_zero, h, c, v, y]
      ring
  let d : ℝ := 7 / 8
  let k := v / d
  have hsharp : h ≤ (31 / 8 : ℝ) * v - v ^ 2 / (7 / 8 : ℝ) := by
    have htest := hpoly (d * k ^ 2) (2 * d * k - k ^ 2) (d - 2 * k) (-1) (by
      intro i hi
      have hcutoff : 0 ≤ d - y i := by dsimp only [d, y]; linarith only [hcap i hi]
      nlinarith only [mul_nonneg hcutoff (sq_nonneg (y i + k))])
    dsimp only [h, d, k] at htest ⊢
    ring_nf at htest ⊢
    linarith only [htest]
  have hlog : 3 * (∑ i, p i * z i ^ 2 * Real.log (z i)) ≤ (3 / 2 : ℝ) * v + h := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ i, (3 * (p i * y i) + (9 / 2 : ℝ) * (p i * y i ^ 2) + p i * y i ^ 3) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        by_cases hi : p i = 0
        · simp [hi]
        have hpoint := mul_le_mul_of_nonneg_left
          (sq_mul_log_le_cubic (ha.trans_le (hinterval i hi).1))
          (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (hp i))
        dsimp only [y]
        linarith only [hpoint]
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hymean, mul_zero, zero_add,
          h, c, v, y]
        ring
  have hlower : 2 * h / (2 + h) ≤ Real.log (1 + h) := by
    rw [add_comm 2 h]
    exact Real.le_log_one_add_of_nonneg hh
  have hden : 2 + h ≠ 0 := by linarith
  rw [hmass₃]
  calc
    _ ≤ (3 / 2 : ℝ) * v + h - (1 + v) * (2 * h / (2 + h)) :=
      sub_le_sub hlog (mul_le_mul_of_nonneg_left hlower (by positivity))
    _ = (3 / 2 : ℝ) * v + h * (h - 2 * v) / (2 + h) := by
      field_simp [hden]
      ring
    _ ≤ _ := by linarith only [mass_error_le hv hvmax hh hsharp]

open GibbsCubicTranslationEntropy (cubicEntropy correction spectralWeight spectralRatio)
open GibbsCubicSignedMoment (spectralPair_centeredMoments)

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem spectralPair_scaledLaw (B U : Matrix n n ℂ) {t : ℝ} (ht : 0 < t)
    (hB : B.PosDef) (hM : (t • B + U).PosDef)
    (hNorm : (B ^ 3).trace.re = 1) (hCenter : (B ^ 2 * U).trace.re = 0) :
    let p := spectralWeight hB.isHermitian hM.isHermitian
    let z := fun q => spectralRatio hB.isHermitian hM.isHermitian q / t
    (∀ q, 0 ≤ p q) ∧ (∀ q, 0 < z q) ∧
    (∑ q, p q) = 1 ∧ (∑ q, p q * z q) = 1 ∧
    t ^ 2 * (∑ q, p q * (z q - 1) ^ 2) = (B * U ^ 2).trace.re := by
  intro p z
  let x := spectralRatio hB.isHermitian hM.isHermitian
  obtain ⟨hmass, hmean, hsecond, _⟩ :=
    spectralPair_centeredMoments B U t hB hM.isHermitian hNorm hCenter
  change (∑ q, p q) = 1 at hmass
  change (∑ q, p q * x q) = t at hmean
  change (∑ q, p q * (x q - t) ^ 2) = (B * U ^ 2).trace.re at hsecond
  have hp (q : n × n) : 0 ≤ p q :=
    mul_nonneg (pow_nonneg (hB.eigenvalues_pos q.1).le 3) (sq_nonneg _)
  have hz (q : n × n) : 0 < z q :=
    div_pos (div_pos (hM.eigenvalues_pos q.2) (hB.eigenvalues_pos q.1)) ht
  refine ⟨hp, hz, hmass, ?_, ?_⟩
  · change (∑ q, p q * (x q / t)) = 1
    simp only [← mul_div_assoc, ← Finset.sum_div, hmean, div_self ht.ne']
  · rw [← hsecond, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    change t ^ 2 * (p q * (x q / t - 1) ^ 2) = p q * (x q - t) ^ 2
    field_simp [ht.ne']

/-- The exact two-sided derivative along the centered Gibbs ray. Dividing the
spectral ratios by the translation parameter cancels all terms proportional to its logarithm. -/
theorem hasDerivAt_cubicEntropy_centered (B U : Matrix n n ℂ) {t : ℝ} (ht : 0 < t)
    (hB : B.PosDef) (hM : (t • B + U).PosDef)
    (hNorm : (B ^ 3).trace.re = 1) (hCenter : (B ^ 2 * U).trace.re = 0) :
    let p := spectralWeight hB.isHermitian hM.isHermitian
    let z := fun q => spectralRatio hB.isHermitian hM.isHermitian q / t
    let v := ∑ q, p q * (z q - 1) ^ 2
    HasDerivAt (fun s : ℝ => cubicEntropy B (s • B + U))
      (3 * (t ^ 2 * (3 * (∑ q, p q * z q ^ 2 * Real.log (z q)) -
        (1 + v) * Real.log (∑ q, p q * z q ^ 3)) + correction B (t • B + U))) t := by
  intro p z v
  let M := t • B + U
  let x := spectralRatio hB.isHermitian hM.isHermitian
  obtain ⟨hp, hz, hmass, hmean, _⟩ := spectralPair_scaledLaw B U ht hB hM hNorm hCenter
  change (∀ q, 0 ≤ p q) at hp
  change (∀ q, 0 < z q) at hz
  change (∑ q, p q) = 1 at hmass
  change (∑ q, p q * z q) = 1 at hmean
  have hx (q : n × n) : x q = t * z q := by
    change x q = t * (x q / t)
    field_simp [ht.ne']
  have hS : (∑ q, p q * z q ^ 2) = 1 + v := calc
    _ = ∑ q, (p q * (z q - 1) ^ 2 + 2 * (p q * z q) - p q) := by
      refine Finset.sum_congr rfl (fun q _ => ?_)
      ring
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
        hmean, hmass, mul_one, v]
      ring
  have hpow (k : ℕ) : (∑ q, p q * x q ^ k) = t ^ k * ∑ q, p q * z q ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hx q, mul_pow]
    ring
  have hTpos : 0 < ∑ q, p q * z q ^ 3 := by
    obtain ⟨q, hq, hqp⟩ := (Finset.sum_pos_iff_of_nonneg (fun q _ => hp q)).mp
      (show 0 < ∑ q, p q by rw [hmass]; exact zero_lt_one)
    exact Finset.sum_pos' (fun q _ => mul_nonneg (hp q) (pow_nonneg (hz q).le 3))
      ⟨q, hq, mul_pos hqp (pow_pos (hz q) 3)⟩
  have hlog : (∑ q, p q * x q ^ 2 * Real.log (x q)) =
      t ^ 2 * ((∑ q, p q * z q ^ 2 * Real.log (z q)) + (1 + v) * Real.log t) := by
    rw [← hS, Finset.sum_mul, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [hx q, Real.log_mul ht.ne' (hz q).ne']
    ring
  have hlogMass : Real.log (∑ q, p q * x q ^ 3) =
      3 * Real.log t + Real.log (∑ q, p q * z q ^ 3) := by
    rw [hpow 3, Real.log_mul (pow_ne_zero 3 ht.ne') hTpos.ne', Real.log_pow]
    norm_num
  let slope :=
    9 * (∑ q, p q * x q ^ 2 * Real.log (x q)) -
      3 * (∑ q, p q * x q ^ 2) * Real.log (∑ q, p q * x q ^ 3) +
      3 * correction B M
  have hright : HasDerivWithinAt (fun s : ℝ => cubicEntropy B (M + s • B))
      slope (Set.Ici 0) 0 :=
    GibbsCubicTranslationEntropy.hasDerivWithinAt_cubicEntropy_spectral_pair B M hB
      hM.posSemidef
  have hd := GibbsCubicTranslationEntropy.hasDerivAt_cubicEntropy B M hB hM
  have hu := uniqueDiffWithinAt_Ici (0 : ℝ)
  rw [(hd.hasDerivWithinAt.derivWithin hu).symm.trans (hright.derivWithin hu)] at hd
  have hd0 : HasDerivAt (fun s : ℝ => cubicEntropy B (M + s • B)) slope (t - t) := by
    rwa [sub_self]
  have htranslated := hd0.comp_sub_const t t
  have htranslate (s : ℝ) : M + (s - t) • B = s • B + U := by
    dsimp only [M]
    rw [sub_smul]
    abel
  have hcoeff : slope = 3 * (t ^ 2 * (3 * (∑ q, p q * z q ^ 2 * Real.log (z q)) -
      (1 + v) * Real.log (∑ q, p q * z q ^ 3)) + correction B M) := by
    dsimp only [slope]
    rw [hlog, hpow 2, hS, hlogMass]
    ring
  simpa only [htranslate, hcoeff, M] using htranslated

/-- Under the scalar support bounds on the actual spectral ratios, the joint
part of the Gibbs translation slope is at most 61/32 times the variance.
The noncommuting trace-pair correction is retained explicitly. -/
theorem deriv_cubicEntropy_div_three_le (B U : Matrix n n ℂ) {t : ℝ} (ht : 0 < t)
    (hB : B.PosDef) (hM : (t • B + U).PosDef)
    (hNorm : (B ^ 3).trace.re = 1) (hCenter : (B ^ 2 * U).trace.re = 0)
    {a b : ℝ} (ha : 0 < a) (hratio : b ≤ (54 / 25 : ℝ) * a)
    (hinterval : ∀ q, a ≤ spectralRatio hB.isHermitian hM.isHermitian q / t ∧
      spectralRatio hB.isHermitian hM.isHermitian q / t ≤ b)
    (hcap : ∀ q, spectralRatio hB.isHermitian hM.isHermitian q / t ≤ 15 / 8) :
    deriv (fun s : ℝ => cubicEntropy B (s • B + U)) t / 3 ≤
      (61 / 32 : ℝ) * (B * U ^ 2).trace.re + correction B (t • B + U) := by
  let p := spectralWeight hB.isHermitian hM.isHermitian
  let z := fun q => spectralRatio hB.isHermitian hM.isHermitian q / t
  let v := ∑ q, p q * (z q - 1) ^ 2
  obtain ⟨hp, _, hmass, hmean, hvar⟩ := spectralPair_scaledLaw B U ht hB hM hNorm hCenter
  change t ^ 2 * v = (B * U ^ 2).trace.re at hvar
  have hs := squareLog_sub_cubicMass_le p z hp hmass hmean ha
    (fun q _ => hinterval q) hratio (fun q _ => hcap q)
  have hd := hasDerivAt_cubicEntropy_centered B U ht hB hM hNorm hCenter
  dsimp only at hs hd
  have hb := mul_le_mul_of_nonneg_left hs (sq_nonneg t)
  rw [hd.deriv, ← hvar]
  dsimp only [v]
  linarith only [hb]

end D5.S3.Quantum.Divergence.GibbsCubicMassCancellation
