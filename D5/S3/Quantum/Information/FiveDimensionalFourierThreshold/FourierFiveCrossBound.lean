/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveCrossBound
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/FourierFiveCrossBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Small rectangular compressions of the normalized five-point Fourier matrix obey exact norm bounds. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.FourierFivePhases

/-! Rectangular Fourier bounds for masks with at most five selected indices. -/

open scoped BigOperators ComplexConjugate
open QuantumPhaseEstimationGeneral

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

abbrev Idx := Fin 5

def fiveEntry (i j : Idx) : ℂ := scale 5 * kernel 5 i j

private theorem fiveEntry_symm (i j : Idx) : fiveEntry i j = fiveEntry j i := by
  rw [fiveEntry, fiveEntry, kernel_symm]

private theorem scale_five_sq_re : ‖scale 5‖ ^ 2 = (1 / 5 : ℝ) := by
  unfold scale
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ↑(5 : ℕ))]
  norm_num

private theorem fiveEntry_sq (i j : Idx) : ‖fiveEntry i j‖ ^ 2 = (1 / 5 : ℝ) := by
  simp [fiveEntry, kernel, scale_five_sq_re]

private theorem fiveEntry_gram (u v : Idx) (T : Finset Idx)
    (huv : u ≠ v) (hT : T.card = 2 ∨ T.card = 3) :
    ‖∑ j ∈ T, fiveEntry u j * conj (fiveEntry v j)‖ ≤ Real.goldenRatio / 5 := by
  let m := ZMod.finEquiv 5 u - ZMod.finEquiv 5 v
  have hm : m ≠ 0 := sub_ne_zero.mpr ((ZMod.finEquiv 5).injective.ne huv)
  have row (j : Idx) : fiveEntry u j * conj (fiveEntry v j) =
      ((1 / 5 : ℝ) : ℂ) * pentagonPhase (m * ZMod.finEquiv 5 j) := by
    have hc (a : ZMod 5) : conj (pentagonPhase a) = pentagonPhase (-a) := by
      rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj]
      simp [ZMod.stdAddChar_apply]
    simp only [fiveEntry, kernel_five_eq_pentagonPhase, map_mul, hc]
    rw [← show (ZMod.finEquiv 5 u * ZMod.finEquiv 5 j) +
        -(ZMod.finEquiv 5 v * ZMod.finEquiv 5 j) = m * ZMod.finEquiv 5 j by
          dsimp [m]; ring, AddChar.map_add_eq_mul]
    have hscale : scale 5 * conj (scale 5) = ((1 / 5 : ℝ) : ℂ) := by
      have h := Complex.mul_conj (scale 5)
      rw [Complex.normSq_eq_norm_sq, scale_five_sq_re] at h
      exact h
    rw [← hscale]
    ring
  simp_rw [row, ← Finset.mul_sum]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 5)]
  have h := pentagonPhase_small_sum T m hm hT
  linarith only [h]

def coeffEnergy (I : Finset Idx) (a : Idx → ℂ) : ℝ := ∑ i ∈ I, ‖a i‖ ^ 2

def crossForm (I J : Finset Idx) (a b : Idx → ℂ) : ℂ :=
  ∑ j ∈ J, (∑ i ∈ I, a i * fiveEntry i j) * b j

private theorem crossForm_flip (I J : Finset Idx) (a b : Idx → ℂ) :
    crossForm I J a b = crossForm J I b a := by
  unfold crossForm
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [fiveEntry_symm i j]
  ring

def crossCap (n : ℕ) : ℝ := ((n : ℝ) - 2 + Real.goldenRatio) / 5

private theorem coeffEnergy_nonneg (I : Finset Idx) (a : Idx → ℂ) :
    0 ≤ coeffEnergy I a := Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem cross_restricted_energy (I J : Finset Idx) (a : Idx → ℂ) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hIJ : I.card + J.card ≤ n) (hI : I.card ≤ J.card) :
    (∑ j ∈ J, ‖∑ i ∈ I, a i * fiveEntry i j‖ ^ 2) ≤ crossCap n * coeffEnergy I a := by
  have hphi : (1 : ℝ) ≤ Real.goldenRatio := by
    unfold Real.goldenRatio
    have h := (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 5)).2
      (by norm_num)
    linarith only [h]
  have hcard : I.card ≤ 2 := by omega
  rcases (show I.card = 0 ∨ I.card = 1 ∨ I.card = 2 by omega) with h | h | h
  · rw [Finset.card_eq_zero.mp h]
    simp [coeffEnergy]
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    simp only [Finset.sum_singleton, norm_mul, mul_pow, fiveEntry_sq, Finset.sum_const,
      nsmul_eq_mul, coeffEnergy]
    simp only [Finset.card_singleton] at hIJ
    have hJ : (J.card : ℝ) + 1 ≤ n := by exact_mod_cast (show J.card + 1 ≤ n by omega)
    have ha : (J.card : ℝ) / 5 ≤ crossCap n := by
      unfold crossCap
      linarith only [hJ, hphi]
    calc
      _ = (J.card : ℝ) / 5 * ‖a i‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right ha (sq_nonneg _)
  · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp h
    simp only [Finset.card_pair huv] at hI hIJ
    have hk : J.card = 2 ∨ J.card = 3 := by omega
    have hJ : (J.card : ℝ) + 2 ≤ n := by exact_mod_cast (show J.card + 2 ≤ n by omega)
    simp only [Finset.sum_pair huv, coeffEnergy]
    let Z := ∑ j ∈ J, fiveEntry u j * conj (fiveEntry v j)
    have hgram : ‖Z‖ ≤ Real.goldenRatio / 5 := fiveEntry_gram u v J huv hk
    have hexpand :
        (∑ j ∈ J, ‖a u * fiveEntry u j + a v * fiveEntry v j‖ ^ 2) =
          (J.card : ℝ) * (‖a u‖ ^ 2 + ‖a v‖ ^ 2) / 5 +
            2 * (a u * conj (a v) * Z).re := by
      have hrow (j : Idx) :
          ‖a u * fiveEntry u j + a v * fiveEntry v j‖ ^ 2 =
            (‖a u‖ ^ 2 + ‖a v‖ ^ 2) / 5 +
              2 * (a u * conj (a v) * (fiveEntry u j * conj (fiveEntry v j))).re := by
        rw [Complex.sq_norm, Complex.normSq_add]
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
        simp only [norm_mul, mul_pow, fiveEntry_sq, map_mul]
        rw [show a u * fiveEntry u j * (conj (a v) * conj (fiveEntry v j)) =
            a u * conj (a v) * (fiveEntry u j * conj (fiveEntry v j)) by ring]
        ring
      simp_rw [hrow, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      rw [← Finset.mul_sum, ← Complex.re_sum, ← Finset.mul_sum]
      dsimp [Z]
      ring
    have hterm : (a u * conj (a v) * Z).re ≤ ‖a u‖ * ‖a v‖ * (Real.goldenRatio / 5) := by
      apply (Complex.re_le_norm _).trans
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left hgram (by positivity)
    have hprod : 2 * (a u * conj (a v) * Z).re ≤
          (Real.goldenRatio / 5) * (‖a u‖ ^ 2 + ‖a v‖ ^ 2) := by
      have hs := mul_nonneg (show 0 ≤ Real.goldenRatio / 5 by positivity)
        (sq_nonneg (‖a u‖ - ‖a v‖))
      nlinarith only [hterm, hs]
    have hc : (J.card : ℝ) / 5 + Real.goldenRatio / 5 ≤ crossCap n := by
      unfold crossCap
      linarith only [hJ]
    rw [hexpand]
    calc
      _ ≤ ((J.card : ℝ) / 5 + Real.goldenRatio / 5) * (‖a u‖ ^ 2 + ‖a v‖ ^ 2) := by
        linarith only [hprod]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)

/-- The squared bilinear form bound is the squared operator norm bound on the submatrix. -/
theorem crossForm_sq_le (I J : Finset Idx) (a b : Idx → ℂ) {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hIJ : I.card + J.card ≤ n) :
    ‖crossForm I J a b‖ ^ 2 ≤ crossCap n * (coeffEnergy I a * coeffEnergy J b) := by
  have ordered (I J : Finset Idx) (a b : Idx → ℂ) (hIJ : I.card + J.card ≤ n)
      (hI : I.card ≤ J.card) :
      ‖crossForm I J a b‖ ^ 2 ≤ crossCap n * (coeffEnergy I a * coeffEnergy J b) := by
    unfold crossForm
    let g (j : Idx) := ∑ i ∈ I, a i * fiveEntry i j
    have ht := norm_sum_le J (fun j => g j * b j)
    simp only [norm_mul] at ht
    have hc := Finset.sum_mul_sq_le_sq_mul_sq J (fun j => ‖g j‖) (fun j => ‖b j‖)
    have hs := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity)).2 ht
    have hb := mul_le_mul_of_nonneg_right (cross_restricted_energy I J a hn hIJ hI)
      (coeffEnergy_nonneg J b)
    change (∑ j ∈ J, ‖g j‖ ^ 2) * (∑ j ∈ J, ‖b j‖ ^ 2) ≤
      (crossCap n * coeffEnergy I a) * coeffEnergy J b at hb
    exact (hs.trans hc).trans (by simpa only [← mul_assoc] using hb)
  rcases le_total I.card J.card with h | h
  · exact ordered I J a b hIJ h
  · rw [crossForm_flip, mul_comm (coeffEnergy I a)]
    exact ordered J I b a (by omega) h

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
