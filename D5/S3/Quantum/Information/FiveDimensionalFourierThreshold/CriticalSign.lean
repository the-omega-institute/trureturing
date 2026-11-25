/- GID: D5/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/FiveDimensionalFourierThreshold/CriticalSign
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every compatible sign mask at the five-dimensional sharp cutoff is critical and every row has unequal Born probabilities. -/

import D5.S3.Quantum.Information.FiveDimensionalFourierThreshold.RankFourReference

/-! Sign masks with arbitrary ties and the rank-four harmonic improvement. -/

open scoped BigOperators InnerProductSpace
open InnerProductSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Information.FiveDimensionalFourierThreshold

abbrev FiveRow := Idx ⊕ Idx
abbrev fiveLaw := basisLaw coordinateBasisFive fourierBasisFive

section Tables

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Both implications are weak, so every subset of the tied rows is allowed. -/
def SignCompatible (p q : ι → ℝ) (s : Finset ι) : Prop :=
  (∀ i ∈ s, q i ≤ p i) ∧ ∀ i ∉ s, p i ≤ q i

theorem signCompatible_compl {p q : ι → ℝ} {s : Finset ι}
    (hs : SignCompatible p q s) : SignCompatible q p sᶜ := by
  classical
  constructor
  · intro i hi
    exact hs.2 i (Finset.mem_compl.mp hi)
  · intro i hi
    exact hs.1 i (by simpa only [Finset.mem_compl, not_not] using hi)

theorem harmonicTerm_half_min {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
    min p q / 2 ≤ harmonicTerm p q := by
  have hw : 0 ≤ p + q := add_nonneg hp hq
  rcases hw.eq_or_lt with h | h
  · have hp₀ : p = 0 := by linarith
    have hq₀ : q = 0 := by linarith
    simp [harmonicTerm, hp₀, hq₀]
  · unfold harmonicTerm
    apply (le_div_iff₀ h).mpr
    rcases le_total p q with hpq | hqp
    · rw [min_eq_left hpq]
      nlinarith only [mul_nonneg hp (sub_nonneg.mpr hpq)]
    · rw [min_eq_right hqp]
      nlinarith only [mul_nonneg hq (sub_nonneg.mpr hqp)]

theorem sum_min_eq_maskMass {p q : ι → ℝ} {s : Finset ι}
    (hs : SignCompatible p q s) :
    ∑ i, min (p i) (q i) = maskMass q s + maskMass p sᶜ := by
  unfold maskMass
  rw [← Finset.sum_compl_add_sum s (fun i => min (p i) (q i))]
  rw [add_comm]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => min_eq_right (hs.1 i hi)
  · exact Finset.sum_congr rfl fun i hi => min_eq_left (hs.2 i (Finset.mem_compl.mp hi))

theorem maskMass_add_compl (p : ι → ℝ) (s : Finset ι) :
    maskMass p sᶜ + maskMass p s = ∑ i, p i :=
  Finset.sum_compl_add_sum s p

/-- Harmonic lower bound with an explicit improvement supported on any complementary rows. -/
theorem harmonicOverlap_ge_sign_mask {p q : ι → ℝ} {s t : Finset ι}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hpSum : ∑ i, p i = 2)
    (hs : SignCompatible p q s)
    (ht : ∀ i ∈ t, i ∉ s ∧ 0 < p i + q i ∧
      0.09 * (p i + q i) ≤ q i - p i) :
    (2 - maskMass p s + maskMass q s) / 2 + 0.045 * maskMass p t ≤
      harmonicOverlap p q := by
  classical
  have hr (i : ι) :
      min (p i) (q i) / 2 + (if i ∈ t then 0.045 * p i else 0) ≤
        harmonicTerm (p i) (q i) := by
    by_cases hi : i ∈ t
    · obtain ⟨his, hw, hgap⟩ := ht i hi
      rw [if_pos hi, min_eq_left (hs.2 i his)]
      unfold harmonicTerm
      apply (le_div_iff₀ hw).mpr
      nlinarith only [mul_nonneg (hp i) (sub_nonneg.mpr hgap)]
    · simpa only [if_neg hi, add_zero] using harmonicTerm_half_min (hp i) (hq i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) fun i _ => hr i
  rw [Finset.sum_add_distrib, ← Finset.sum_div, sum_min_eq_maskMass hs] at hsum
  rw [Finset.sum_ite_mem, Finset.univ_inter] at hsum
  rw [← Finset.mul_sum] at hsum
  have hm := maskMass_add_compl p s
  rw [hpSum] at hm
  change (maskMass q s + maskMass p sᶜ) / 2 + 0.045 * maskMass p t ≤
    harmonicOverlap p q at hsum
  linarith only [hm, hsum]

theorem sign_mask_mass_gap {p q : ι → ℝ} {s : Finset ι}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hpSum : ∑ i, p i = 2)
    (hs : SignCompatible p q s) (hD : harmonicOverlap p q ≤ sharpD) :
    2 * sharpC ^ 2 ≤ maskMass p s - maskMass q s := by
  have h := harmonicOverlap_ge_sign_mask (t := ∅) hp hq hpSum hs
    (by simp)
  simp only [maskMass, Finset.sum_empty, mul_zero, add_zero] at h
  simp only [maskMass]
  rw [sharpD_eq] at hD
  linarith only [h, hD]

end Tables

theorem fiveLaw_nonneg (x : CoordinateFive) (i : FiveRow) : 0 ≤ fiveLaw x i := by
  cases i <;> exact sq_nonneg _

theorem fiveLaw_sum_unit (x : CoordinateFive) (hx : ‖x‖ = 1) :
    ∑ i, fiveLaw x i = 2 := by
  rw [basisLaw_sum, hx]
  norm_num

theorem fiveScore_swap (x y : CoordinateFive) : fiveScore y x = fiveScore x y := by
  unfold fiveScore score
  apply Finset.sum_congr rfl
  intro i _
  unfold scoreTerm
  rw [add_comm (fiveLaw y i)]
  congr 1
  ring

theorem harmonicOverlap_le_sharpD_of_cutoff {x y : CoordinateFive}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hS : sharpCutoff ≤ fiveScore x y) :
    harmonicOverlap (fiveLaw x) (fiveLaw y) ≤ sharpD := by
  change sharpCutoff ≤ score (fiveLaw x) (fiveLaw y) at hS
  rw [score_eq_sub_overlap, fiveLaw_sum_unit x hx, fiveLaw_sum_unit y hy,
    sharpCutoff_eq] at hS
  rw [sharpD_eq]
  linarith only [hS]

/-- Difference-product class for two pairs. Changing their internal order changes only the sign. -/
def CriticalPairProduct (I J : Finset Idx) : Prop :=
  ∃ a a' b b' : Idx, I = {a, a'} ∧ J = {b, b'} ∧
    let m := (ZMod.finEquiv 5 a - ZMod.finEquiv 5 a') *
      (ZMod.finEquiv 5 b - ZMod.finEquiv 5 b')
    m = 1 ∨ m = -1

def CriticalFiveMask (s : Finset FiveRow) : Prop :=
  (s.toLeft.card = 2 ∧ CriticalPairProduct s.toLeft s.toRightᶜ) ∨
  (s.toRight.card = 2 ∧ CriticalPairProduct s.toLeftᶜ s.toRight)

theorem criticalPairProduct_card {I J : Finset Idx} (h : CriticalPairProduct I J) :
    I.card = 2 ∧ J.card = 2 := by
  rcases h with ⟨a, a', b, b', rfl, rfl, h⟩
  dsimp at h
  have hzero : ¬ ((0 : ZMod 5) = 1 ∨ (0 : ZMod 5) = -1) := by decide
  have ha : a ≠ a' := by
    intro he
    subst a'
    exact hzero (by simpa only [sub_self, zero_mul] using h)
  have hb : b ≠ b' := by
    intro he
    subst b'
    exact hzero (by simpa only [sub_self, mul_zero] using h)
  simp [ha, hb]

theorem criticalFiveMask_compl {s : Finset FiveRow} (hs : CriticalFiveMask s) :
    CriticalFiveMask sᶜ := by
  have hl : (sᶜ).toLeft = s.toLeftᶜ := by ext i; simp
  have hr : (sᶜ).toRight = s.toRightᶜ := by ext i; simp
  unfold CriticalFiveMask at hs ⊢
  rw [hl, hr, compl_compl, compl_compl]
  rcases hs with ⟨_, h⟩ | ⟨_, h⟩
  · exact Or.inr ⟨(criticalPairProduct_card h).2, h⟩
  · exact Or.inl ⟨(criticalPairProduct_card h).1, h⟩

/-- Strict relative difference for the amplitude errors on the four complementary rows. -/
private theorem rankFour_row_gap {u v : ℝ}
    (hu : 0 ≤ u) (hu' : u < 0.305) (hv : u + 0.029 < v) :
    0 < u ^ 2 + v ^ 2 ∧ 0.09 * (u ^ 2 + v ^ 2) < v ^ 2 - u ^ 2 := by
  have hv₀ : 0 < v := by linarith
  have hscale : (0.334 : ℝ) * u < 0.305 * v := by linarith
  have hsq := (sq_lt_sq₀ (by positivity : 0 ≤ (0.334 : ℝ) * u)
    (by positivity : 0 ≤ (0.305 : ℝ) * v)).mpr hscale
  rw [mul_pow, mul_pow] at hsq
  constructor
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hv₀ _)
  · nlinarith only [hsq, sq_nonneg u]

/-- The tail-mass improvement excludes a critical four-column mask at the closed cutoff. -/
theorem rankFour_overlap_gt_sharpD {p q : FiveRow → ℝ} {s t : Finset FiveRow}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpSum : ∑ i, p i = 2) (hs : SignCompatible p q s)
    (hsmall : maskMass p s - maskMass q s ≤ 1 + sharpSigma)
    (hrows : ∀ i ∈ t, i ∉ s ∧ Real.sqrt (p i) < 0.305 ∧
      Real.sqrt (p i) + 0.029 < Real.sqrt (q i))
    (htail : (0.228 : ℝ) ^ 2 < maskMass p t) :
    sharpD < harmonicOverlap p q := by
  have h := harmonicOverlap_ge_sign_mask hp hq hpSum hs
    (t := t) (by
      intro i hi
      obtain ⟨his, hu, hv⟩ := hrows i hi
      have hh := rankFour_row_gap (Real.sqrt_nonneg _) hu hv
      rw [Real.sq_sqrt (hp i), Real.sq_sqrt (hq i)] at hh
      exact ⟨his, hh.1, hh.2.le⟩)
  unfold sharpD
  linarith only [h, hsmall, htail, sharp_sigma_bounds.2, sharp_sqrt_five_bounds.1]

/-- The two exact diameter comparisons leave only the critical four- and five-row classes. -/
private theorem noncritical_diameters :
    1 + Real.sqrt (3 / 5) < 2 * sharpC ^ 2 ∧
      2 * Real.sqrt (4 / 5) < 2 * sharpC ^ 2 := by
  have h₁ : Real.sqrt (3 / 5 : ℝ) < 0.775 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h₂ : Real.sqrt (4 / 5 : ℝ) < 0.895 :=
    (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [sharpC_sq]
  constructor <;> linarith [sharp_sqrt_five_bounds.1]

section NoncriticalMasks

open scoped ComplexConjugate
open QuantumPhaseEstimationGeneral

private theorem criticalPairProduct_comm (I J : Finset Idx) :
    CriticalPairProduct I J ↔ CriticalPairProduct J I := by
  constructor <;> rintro ⟨a, a', b, b', rfl, rfl, h⟩ <;>
    exact ⟨b, b', a, a', rfl, rfl, by simpa only [mul_comm] using h⟩

/-- For a difference of ±2, the two phases have the smaller pentagon chord sum. -/
private theorem noncritical_phase_pair_norm (a b : ZMod 5) (hne : a ≠ b)
    (hn : ¬ (b - a = 1 ∨ b - a = -1)) : ‖pentagonPhase a + pentagonPhase b‖ ≤ 1 := by
  have hdiff : b - a = 2 ∨ b - a = 3 := by
    have hres : ∀ d : ZMod 5, d ≠ 0 → ¬ (d = 1 ∨ d = -1) → d = 2 ∨ d = 3 := by decide
    exact hres (b - a) (sub_ne_zero.mpr hne.symm) hn
  have hfactor : pentagonPhase a + pentagonPhase b =
      pentagonPhase a * (1 + pentagonPhase (b - a)) := by
    rw [mul_add, mul_one, ← AddChar.map_add_eq_mul, show a + (b - a) = b by abel]
  have hcos : Real.cos (2 * Real.pi * 2 / 5) = -Real.cos (Real.pi / 5) := by
    rw [show 2 * Real.pi * 2 / 5 = Real.pi - Real.pi / 5 by ring, Real.cos_pi_sub]
  have hcos' : Real.cos (2 * Real.pi * 3 / 5) = -Real.cos (Real.pi / 5) := by
    rw [show 2 * Real.pi * 3 / 5 = 2 * Real.pi - 2 * Real.pi * 2 / 5 by ring,
      Real.cos_two_pi_sub, hcos]
  have hre : (pentagonPhase (b - a)).re = -Real.cos (Real.pi / 5) := by
    rw [pentagonPhase_re]
    rcases hdiff with h | h
    · simpa only [h, show (2 : ZMod 5).val = 2 by decide, Nat.cast_ofNat] using hcos
    · simpa only [h, show (3 : ZMod 5).val = 3 by decide, Nat.cast_ofNat] using hcos'
  rw [hfactor, norm_mul, pentagonPhase_norm, one_mul]
  apply (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [Complex.sq_norm, Complex.normSq_add, Complex.normSq_eq_norm_sq (pentagonPhase _),
    pentagonPhase_norm, Complex.normSq_one, one_mul, Complex.conj_re, hre]
  have h := D5.S3.Constants.PentagonCosines.pentagon_golden_cosines.1
  unfold Real.goldenRatio at h
  linarith only [h, sharp_sqrt_five_bounds.1]

private theorem fiveEntry_mul_conj (u v j : Idx) :
    fiveEntry u j * conj (fiveEntry v j) =
      ((1 / 5 : ℝ) : ℂ) *
        pentagonPhase ((ZMod.finEquiv 5 u - ZMod.finEquiv 5 v) * ZMod.finEquiv 5 j) := by
  have hc (a : ZMod 5) : conj (pentagonPhase a) = pentagonPhase (-a) := by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj]
    simp [ZMod.stdAddChar_apply]
  simp only [fiveEntry, kernel_five_eq_pentagonPhase, map_mul, hc]
  rw [sub_mul, sub_eq_add_neg, AddChar.map_add_eq_mul]
  have hscale : scale 5 * conj (scale 5) = ((1 / 5 : ℝ) : ℂ) := by
    have h := Complex.mul_conj (scale 5)
    rw [Complex.normSq_eq_norm_sq, scale_five_sq_re] at h
    exact h
  rw [← hscale]
  ring

/-- Three columns reduce to the negative of the sum over the two omitted columns. -/
private theorem noncritical_fiveEntry_gram (u v : Idx) (huv : u ≠ v) (J : Finset Idx)
    (hn₂ : J.card = 2 → ¬ CriticalPairProduct {u, v} J)
    (hn₃ : J.card = 3 → ¬ CriticalPairProduct {u, v} Jᶜ)
    (hJ : J.card = 2 ∨ J.card = 3) :
    ‖∑ j ∈ J, fiveEntry u j * conj (fiveEntry v j)‖ ≤ 1 / 5 := by
  let m := ZMod.finEquiv 5 u - ZMod.finEquiv 5 v
  have hm : m ≠ 0 := sub_ne_zero.mpr ((ZMod.finEquiv 5).injective.ne huv)
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let e : Idx ≃ ZMod 5 := (ZMod.finEquiv 5).toEquiv.trans (Equiv.mulLeft₀ m hm)
  have hpair (T : Finset Idx) (hT : T.card = 2) (hn : ¬ CriticalPairProduct {u, v} T) :
      ‖∑ j ∈ T, pentagonPhase (e j)‖ ≤ 1 := by
    obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hT
    rw [Finset.sum_pair hab]
    apply noncritical_phase_pair_norm _ _ (e.injective.ne hab)
    intro h
    apply hn
    refine ⟨u, v, b, a, rfl, by rw [Finset.pair_comm], ?_⟩
    change m * ZMod.finEquiv 5 b - m * ZMod.finEquiv 5 a = 1 ∨
      m * ZMod.finEquiv 5 b - m * ZMod.finEquiv 5 a = -1 at h
    simpa only [m, mul_sub] using h
  simp_rw [fiveEntry_mul_conj, ← Finset.mul_sum]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 5)]
  change (1 / 5 : ℝ) * ‖∑ j ∈ J, pentagonPhase (e j)‖ ≤ 1 / 5
  suffices h : ‖∑ j ∈ J, pentagonPhase (e j)‖ ≤ 1 by linarith only [h]
  rcases hJ with h | h
  · exact hpair J h (hn₂ h)
  · have hc : Jᶜ.card = 2 := by rw [Finset.card_compl, Fintype.card_fin, h]
    have htotal := Finset.sum_compl_add_sum J (fun j => pentagonPhase (e j))
    rw [e.sum_comp, sum_pentagonPhase] at htotal
    have heq : (∑ j ∈ J, pentagonPhase (e j)) = -(∑ j ∈ Jᶜ, pentagonPhase (e j)) :=
      eq_neg_of_add_eq_zero_right (by simpa only [add_comm] using htotal)
    rw [heq, norm_neg]
    exact hpair Jᶜ hc (hn₃ h)

private theorem noncritical_restricted_energy (I J : Finset Idx) (a : Idx → ℂ)
    {n : ℕ} (hn : n ≤ 5) (hIJ : I.card + J.card ≤ n) (hI : I.card ≤ J.card)
    (hn₂ : I.card = 2 → J.card = 2 → ¬ CriticalPairProduct I J)
    (hn₃ : I.card = 2 → J.card = 3 → ¬ CriticalPairProduct I Jᶜ) :
    (∑ j ∈ J, ‖∑ i ∈ I, a i * fiveEntry i j‖ ^ 2) ≤
      ((n : ℝ) - 1) / 5 * coeffEnergy I a := by
  rcases (show I.card = 0 ∨ I.card = 1 ∨ I.card = 2 by omega) with h | h | h
  · rw [Finset.card_eq_zero.mp h]
    simp [coeffEnergy]
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp h
    simp only [Finset.sum_singleton, norm_mul, mul_pow, fiveEntry_sq, Finset.sum_const,
      nsmul_eq_mul, coeffEnergy]
    simp only [Finset.card_singleton] at hIJ
    have hJ : (J.card : ℝ) + 1 ≤ n := by exact_mod_cast (show J.card + 1 ≤ n by omega)
    calc
      _ = (J.card : ℝ) / 5 * ‖a i‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hJ]) (sq_nonneg _)
  · obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp h
    simp only [Finset.card_pair huv] at hI hIJ
    have hk : J.card = 2 ∨ J.card = 3 := by omega
    have hJ : (J.card : ℝ) + 2 ≤ n := by exact_mod_cast (show J.card + 2 ≤ n by omega)
    simp only [Finset.sum_pair huv, coeffEnergy]
    let Z := ∑ j ∈ J, fiveEntry u j * conj (fiveEntry v j)
    have hgram : ‖Z‖ ≤ 1 / 5 :=
      noncritical_fiveEntry_gram u v huv J (hn₂ h) (hn₃ h) hk
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
    have hterm : (a u * conj (a v) * Z).re ≤ ‖a u‖ * ‖a v‖ * ((1 / 5 : ℝ)) := by
      apply (Complex.re_le_norm _).trans
      simp only [norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_left hgram (by positivity)
    have hprod : 2 * (a u * conj (a v) * Z).re ≤
          ((1 / 5 : ℝ)) * (‖a u‖ ^ 2 + ‖a v‖ ^ 2) := by
      have hs := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 5)
        (sq_nonneg (‖a u‖ - ‖a v‖))
      nlinarith only [hterm, hs]
    rw [hexpand]
    calc
      _ ≤ ((J.card : ℝ) / 5 + 1 / 5) * (‖a u‖ ^ 2 + ‖a v‖ ^ 2) := by
        linarith only [hprod]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith only [hJ]) (by positivity)

private theorem noncritical_crossForm_sq_le (I J : Finset Idx) (a b : Idx → ℂ) {n : ℕ}
    (hn : n ≤ 5) (hIJ : I.card + J.card ≤ n)
    (hn₂₂ : I.card = 2 → J.card = 2 → ¬ CriticalPairProduct I J)
    (hn₂₃ : I.card = 2 → J.card = 3 → ¬ CriticalPairProduct I Jᶜ)
    (hn₃₂ : I.card = 3 → J.card = 2 → ¬ CriticalPairProduct J Iᶜ) :
    ‖crossForm I J a b‖ ^ 2 ≤ ((n : ℝ) - 1) / 5 * (coeffEnergy I a * coeffEnergy J b) := by
  have ordered (I J : Finset Idx) (a b : Idx → ℂ) (hIJ : I.card + J.card ≤ n)
      (hI : I.card ≤ J.card) (h₂ : I.card = 2 → J.card = 2 → ¬ CriticalPairProduct I J)
      (h₃ : I.card = 2 → J.card = 3 → ¬ CriticalPairProduct I Jᶜ) :
      ‖crossForm I J a b‖ ^ 2 ≤ ((n : ℝ) - 1) / 5 * (coeffEnergy I a * coeffEnergy J b) := by
    unfold crossForm
    let g (j : Idx) := ∑ i ∈ I, a i * fiveEntry i j
    have ht := norm_sum_le J (fun j => g j * b j)
    simp only [norm_mul] at ht
    have hc := Finset.sum_mul_sq_le_sq_mul_sq J (fun j => ‖g j‖) (fun j => ‖b j‖)
    have hs := (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun _ _ => by positivity)).2 ht
    have hb := mul_le_mul_of_nonneg_right (noncritical_restricted_energy I J a hn hIJ hI h₂ h₃)
      (coeffEnergy_nonneg J b)
    change (∑ j ∈ J, ‖g j‖ ^ 2) * (∑ j ∈ J, ‖b j‖ ^ 2) ≤
      (((n : ℝ) - 1) / 5 * coeffEnergy I a) * coeffEnergy J b at hb
    exact (hs.trans hc).trans (by simpa only [← mul_assoc] using hb)
  rcases le_total I.card J.card with h | h
  · exact ordered I J a b hIJ h hn₂₂ hn₂₃
  · rw [crossForm_flip, mul_comm (coeffEnergy I a)]
    exact ordered J I b a (by omega) h
      (fun hj hi hpair => hn₂₂ hi hj ((criticalPairProduct_comm _ _).mp hpair))
      (fun hj hi => hn₃₂ hi hj)

private theorem five_synthesis_sq_bounds (s : Finset (Idx ⊕ Idx)) (w : EuclideanSpace ℂ s)
    {cap : ℝ}
    (hc : ∀ a b : Idx → ℂ, ‖crossForm s.toLeft s.toRight a b‖ ^ 2 ≤
      cap * (coeffEnergy s.toLeft a * coeffEnergy s.toRight b))
    (hcap : 0 ≤ cap) :
    (1 - Real.sqrt (cap)) * ‖w‖ ^ 2 ≤
        ‖maskSynthesis coordinateBasisFive fourierBasisFive s w‖ ^ 2 ∧
    ‖maskSynthesis coordinateBasisFive fourierBasisFive s w‖ ^ 2 ≤
        (1 + Real.sqrt (cap)) * ‖w‖ ^ 2 := by
  let e (i : Idx ⊕ Idx) : ℂ := if h : i ∈ s then w ⟨i, h⟩ else 0
  let a (i : Idx) : ℂ := e (Sum.inl i)
  let b (j : Idx) : ℂ := e (Sum.inr j)
  let U := ∑ i ∈ s.toLeft, a i • coordinateBasisFive i
  let V := ∑ j ∈ s.toRight, b j • fourierBasisFive j
  have hvec : maskSynthesis coordinateBasisFive fourierBasisFive s w = U + V := by
    let v : Idx ⊕ Idx → CoordinateFive := Sum.elim coordinateBasisFive fourierBasisFive
    calc
      _ = ∑ i : s, e i.val • v i.val := by
        change (∑ i : s, w i • v i.val) = _
        apply Finset.sum_congr rfl
        intro i _
        simp [e, i.property]
      _ = ∑ i ∈ s, e i • v i := Finset.sum_coe_sort s (fun i => e i • v i)
      _ = U + V := Finset.sum_sum_eq_sum_toLeft_add_sum_toRight s _
  have hcoeff : ‖w‖ ^ 2 = coeffEnergy s.toLeft a + coeffEnergy s.toRight b := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ = ∑ i : s, ‖e i.val‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        simp [e, i.property]
      _ = ∑ i ∈ s, ‖e i‖ ^ 2 := Finset.sum_coe_sort s (fun i => ‖e i‖ ^ 2)
      _ = _ := Finset.sum_sum_eq_sum_toLeft_add_sum_toRight s _
  have hcross := hc (fun i => conj (a i)) b
  rw [← inner_basis_sums] at hcross
  have hconj : coeffEnergy s.toLeft (fun i => conj (a i)) = coeffEnergy s.toLeft a := by
    simp [coeffEnergy]
  rw [hconj] at hcross
  have hU : ‖U‖ ^ 2 = coeffEnergy s.toLeft a := norm_sq_basis_sum _ _ _
  have hV : ‖V‖ ^ 2 = coeffEnergy s.toRight b := norm_sq_basis_sum _ _ _
  have hnorm : 2 * ‖⟪U, V⟫_ℂ‖ ≤ Real.sqrt (cap) * ‖w‖ ^ 2 := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).1
    simp only [mul_pow, Real.sq_sqrt hcap, hcoeff]
    have h := mul_nonneg hcap
      (sq_nonneg (coeffEnergy s.toLeft a - coeffEnergy s.toRight b))
    change ‖⟪U, V⟫_ℂ‖ ^ 2 ≤ _ at hcross
    nlinarith only [h, hcross]
  have hreal := abs_le.mp (Complex.abs_re_le_norm ⟪U, V⟫_ℂ)
  rw [hvec, norm_add_sq (𝕜 := ℂ), hU, hV]
  change (1 - _) * ‖w‖ ^ 2 ≤ _ + 2 * (⟪U, V⟫_ℂ).re + _ ∧
    _ + 2 * (⟪U, V⟫_ℂ).re + _ ≤ (1 + _) * ‖w‖ ^ 2
  constructor <;> linarith only [hcoeff, hnorm, hreal.1, hreal.2]

private theorem noncritical_small_mask_bound (x y : CoordinateFive) (s : Finset FiveRow)
    (hx : ‖x‖ = 1) (_hy : ‖y‖ = 1) (hs : s.card ≤ 4)
    (hn : ¬ CriticalPairProduct s.toLeft s.toRight) :
    maskMass (fiveLaw x) s - maskMass (fiveLaw y) s ≤ 1 + Real.sqrt (3 / 5) := by
  have hcard := s.card_toLeft_add_card_toRight
  have hu (a b : Idx → ℂ) :
      ‖crossForm s.toLeft s.toRight a b‖ ^ 2 ≤
        (3 / 5 : ℝ) * (coeffEnergy s.toLeft a * coeffEnergy s.toRight b) := by
    simpa only [Nat.cast_ofNat, show ((4 : ℝ) - 1) / 5 = 3 / 5 by norm_num] using
      noncritical_crossForm_sq_le s.toLeft s.toRight a b (n := 4) (by decide)
        (by omega) (fun _ _ => hn) (by omega) (by omega)
  have hx' : maskMass (fiveLaw x) s ≤ 1 + Real.sqrt (3 / 5) := by
    rw [maskMass_eq_norm_adjoint]
    exact adjoint_upper_of_sq_bound _ (by positivity)
      (fun w => (five_synthesis_sq_bounds s w hu (by norm_num)).2) _ hx
  have hy' : 0 ≤ maskMass (fiveLaw y) s := Finset.sum_nonneg fun i _ => fiveLaw_nonneg y i
  linarith only [hx', hy']

private theorem noncritical_balanced_mask_bound (x y : CoordinateFive)
    (s : Finset FiveRow) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hs : s.card = 5) (hn : ¬ CriticalFiveMask s) :
    maskMass (fiveLaw x) s - maskMass (fiveLaw y) s ≤ 2 * Real.sqrt (4 / 5) := by
  have hcard := s.card_toLeft_add_card_toRight
  have hu (a b : Idx → ℂ) :
      ‖crossForm s.toLeft s.toRight a b‖ ^ 2 ≤
        (4 / 5 : ℝ) * (coeffEnergy s.toLeft a * coeffEnergy s.toRight b) := by
    simpa only [Nat.cast_ofNat, show ((5 : ℝ) - 1) / 5 = 4 / 5 by norm_num] using
      noncritical_crossForm_sq_le s.toLeft s.toRight a b (n := 5) (by decide)
        (by omega) (by omega)
        (fun hl _ h => hn (Or.inl ⟨hl, h⟩))
        (fun _ hr h => hn (Or.inr ⟨hr, (criticalPairProduct_comm _ _).mp h⟩))
  have hpos : 0 < 1 - Real.sqrt (4 / 5 : ℝ) := by
    have hlt : Real.sqrt (4 / 5 : ℝ) < 1 :=
      (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
    linarith only [hlt]
  have hx' : maskMass (fiveLaw x) s ≤ 1 + Real.sqrt (4 / 5) := by
    rw [maskMass_eq_norm_adjoint]
    exact adjoint_upper_of_sq_bound _ (by positivity)
      (fun w => (five_synthesis_sq_bounds s w hu (by norm_num)).2) _ hx
  have hy' : 1 - Real.sqrt (4 / 5) ≤ maskMass (fiveLaw y) s := by
    rw [maskMass_eq_norm_adjoint]
    exact adjoint_lower_of_sq_bound _ hpos
      (fun w => (five_synthesis_sq_bounds s w hu (by norm_num)).1)
      (by simpa [finrank_euclideanSpace] using hs) _ hy
  linarith only [hx', hy']

end NoncriticalMasks

private theorem rankFour_reference (x y : CoordinateFive) (s : Finset FiveRow)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hpair : CriticalPairProduct s.toLeft s.toRight) :
    Nonempty (RankFourReference x y s) := by
  obtain ⟨i, i', j, j', hi, hj, hprod⟩ := hpair
  obtain ⟨u, a, b, hmask, _, _⟩ := criticalMasks_affine i i' j j' hprod
  rw [← hi, ← hj, Finset.toLeft_disjSum_toRight] at hmask
  rw [← hmask]
  exact rankFourReference_affine x y hx hy u a b

private theorem rankFour_tail (x y : CoordinateFive) (s : Finset FiveRow)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hpair : CriticalPairProduct s.toLeft s.toRight)
    (hgap : 2 * sharpC ^ 2 ≤ maskMass (fiveLaw x) s - maskMass (fiveLaw y) s) :
    maskMass (fiveLaw x) s - maskMass (fiveLaw y) s ≤ 1 + sharpSigma ∧
    ∃ t : Finset FiveRow, (0.228 : ℝ) ^ 2 < maskMass (fiveLaw x) t ∧
      ∀ i ∈ t, i ∉ s ∧ Real.sqrt (fiveLaw x i) < 0.305 ∧
        Real.sqrt (fiveLaw x i) + 0.029 < Real.sqrt (fiveLaw y i) := by
  obtain ⟨r⟩ := rankFour_reference x y s hx hy hpair
  have hσ := sharp_sigma_bounds
  have hA : (0.14934 : ℝ) ≤ 1 - sharpSigma := by linarith only [hσ.2]
  have hG : (0.573 : ℝ) ≤ sharpSigma - sharpB := by
    linarith only [hσ.1, sharp_b_bounds.2]
  have hb : r.dx + r.dy ≤ 0.0034488 := by
    rw [r.mass_diff, sharpC_sq] at hgap
    linarith only [hgap, hσ.2, sharp_sqrt_five_bounds.1]
  have hx' : (0.573 : ℝ) * r.rx ^ 2 ≤ 2 * r.dx :=
    (mul_le_mul_of_nonneg_right hG (sq_nonneg _)).trans r.x_gap
  have hy' : (0.14934 : ℝ) * r.ry ^ 2 ≤ 2 * r.dy :=
    (mul_le_mul_of_nonneg_right hA (sq_nonneg _)).trans r.y_gap
  have hrx : r.rx < 0.111 := by
    apply (sq_lt_sq₀ r.rx_nonneg (by norm_num)).mp
    linarith only [hx', hb, r.dy_nonneg]
  have hsum : r.rx + r.ry < 0.243 := by
    have h₁ : r.rx ≤ Real.sqrt ((2 / 0.573 : ℝ) * r.dx) := by
      apply (Real.le_sqrt r.rx_nonneg (mul_nonneg (by norm_num) r.dx_nonneg)).mpr
      linarith only [hx']
    have h₂ : r.ry ≤ Real.sqrt ((2 / 0.14934 : ℝ) * r.dy) := by
      apply (Real.le_sqrt r.ry_nonneg (mul_nonneg (by norm_num) r.dy_nonneg)).mpr
      linarith only [hy']
    refine ((add_le_add h₁ h₂).trans (sharp_two_errors (by norm_num) (by norm_num)
      r.dx_nonneg r.dy_nonneg)).trans_lt ?_
    have hnonneg : 0 ≤ ((2 / 0.573 : ℝ) + 2 / 0.14934) * (r.dx + r.dy) :=
      mul_nonneg (by norm_num) (add_nonneg r.dx_nonneg r.dy_nonneg)
    exact (Real.sqrt_lt hnonneg (by norm_num)).mpr (by linarith only [hb])
  have hA₂ : Real.sqrt (1 - sharpSigma) / 2 < 0.1933 := by
    have ht : Real.sqrt (1 - sharpSigma) < 0.3866 :=
      (Real.sqrt_lt (by linarith only [hA]) (by norm_num)).mpr (by linarith only [hσ.1])
    linarith
  have hy₀ : (0.4653 : ℝ) < Real.sqrt (2 / (7 + Real.sqrt 5)) := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    apply (lt_div_iff₀ (by positivity)).mpr
    linarith only [sharp_sqrt_five_bounds.2]
  have htail : (0.228 : ℝ) ^ 2 < maskMass (fiveLaw x) r.tail := by
    have hlow : (0.386 : ℝ) < Real.sqrt (1 - sharpSigma) :=
      (Real.lt_sqrt (by norm_num)).mpr (by linarith only [hA])
    have hrt : Real.sqrt 2 < 1.415 :=
      (Real.sqrt_lt (by norm_num) (by norm_num)).mpr (by norm_num)
    have hmul : Real.sqrt 2 * r.rx ≤ (1.415 : ℝ) * 0.111 :=
      mul_le_mul hrt.le hrx.le r.rx_nonneg (by norm_num)
    exact (Real.lt_sqrt (by norm_num)).mp (by linarith only [r.tail_x, hlow, hmul])
  refine ⟨by linarith only [r.mass_diff, r.dx_nonneg, r.dy_nonneg], r.tail, htail, ?_⟩
  intro i hi
  obtain ⟨his, hx₀, hy₀'⟩ := r.tail_rows i hi
  exact ⟨his, by linarith only [hx₀, hA₂, hrx], by linarith only [hx₀, hy₀', hA₂, hy₀, hsum]⟩

private theorem critical_sign_small_side (x y : CoordinateFive) (s : Finset FiveRow)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hS : sharpCutoff ≤ fiveScore x y)
    (hs : SignCompatible (fiveLaw x) (fiveLaw y) s) (hcard : s.card ≤ 5) :
    s.card = 5 ∧ CriticalFiveMask s := by
  have hD := harmonicOverlap_le_sharpD_of_cutoff hx hy hS
  have hg := sign_mask_mass_gap (fiveLaw_nonneg x) (fiveLaw_nonneg y)
    (fiveLaw_sum_unit x hx) hs hD
  by_cases h5 : s.card = 5
  · refine ⟨h5, ?_⟩
    by_contra hn
    exact (not_le_of_gt noncritical_diameters.2)
      (hg.trans (noncritical_balanced_mask_bound x y s hx hy h5 hn))
  · exfalso
    by_cases hc : CriticalPairProduct s.toLeft s.toRight
    · obtain ⟨hu, t, ht, hr⟩ := rankFour_tail x y s hx hy hc hg
      exact (not_lt_of_ge hD) (rankFour_overlap_gt_sharpD
        (fiveLaw_nonneg x) (fiveLaw_nonneg y) (fiveLaw_sum_unit x hx) hs hu hr ht)
    · exact (not_le_of_gt noncritical_diameters.1)
        (hg.trans (noncritical_small_mask_bound x y s hx hy (by omega) hc))

/-- At the closed cutoff every compatible tie assignment gives a critical five-row mask. -/
theorem critical_sign_mask_at_cutoff (x y : CoordinateFive) (s : Finset FiveRow)
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hS : sharpCutoff ≤ fiveScore x y)
    (hs : SignCompatible (fiveLaw x) (fiveLaw y) s) :
    s.card = 5 ∧ CriticalFiveMask s := by
  by_cases hsmall : s.card ≤ 5
  · exact critical_sign_small_side x y s hx hy hS hs hsmall
  · have hcard : sᶜ.card + s.card = 10 := by
      simpa using Finset.card_compl_add_card s
    have hS' : sharpCutoff ≤ fiveScore y x := by rwa [fiveScore_swap]
    obtain ⟨hc, hm⟩ := critical_sign_small_side y x sᶜ hy hx hS'
      (signCompatible_compl hs) (by omega)
    exact ⟨by omega, by simpa using criticalFiveMask_compl hm⟩

/-- Toggling a tied row would produce compatible masks of different sizes. -/
theorem fiveLaw_ne_at_cutoff (x y : CoordinateFive) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (hS : sharpCutoff ≤ fiveScore x y) (i : FiveRow) :
    fiveLaw x i ≠ fiveLaw y i := by
  classical
  intro hi
  let s : Finset FiveRow := Finset.univ.filter fun j => fiveLaw y j < fiveLaw x j
  have hs : SignCompatible (fiveLaw x) (fiveLaw y) s := by
    constructor
    · intro j hj
      exact le_of_lt (by simpa [s] using hj)
    · intro j hj
      exact le_of_not_gt (by simpa [s] using hj)
  have hin : i ∉ s := by simp [s, hi]
  have ht : SignCompatible (fiveLaw x) (fiveLaw y) (insert i s) := by
    constructor
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi.ge
      · exact hs.1 j hj
    · intro j hj
      exact hs.2 j (fun hs' => hj (Finset.mem_insert_of_mem hs'))
  have hc := (critical_sign_mask_at_cutoff x y s hx hy hS hs).1
  have hc' := (critical_sign_mask_at_cutoff x y (insert i s) hx hy hS ht).1
  rw [Finset.card_insert_of_notMem hin, hc] at hc'
  omega

end D5.S3.Quantum.Information.FiveDimensionalFourierThreshold
