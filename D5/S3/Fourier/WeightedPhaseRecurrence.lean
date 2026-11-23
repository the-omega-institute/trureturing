/- GID: D5/S3/Fourier/WeightedPhaseRecurrence
   generality: G
   mirror-B: D5/B/S3/Fourier/WeightedPhaseRecurrence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Fejer product gives finite interval recurrence for normalized weighted phase loss. -/

import D5.S3.Zeros.Repulsion.FejerNearCollisionBound
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators

namespace D5.S3.Fourier.WeightedPhaseRecurrence

open FejerNearCollisionBound (fejerKernel fejer_square)

noncomputable section

/-- Weighted cosine loss at a real time relative to a family of target angles. -/
def phaseLoss {J : Type*} [Fintype J] (g θ p : J → ℝ) (t : ℝ) : ℝ :=
  ∑ j, p j * (1 - Real.cos (g j * t - θ j))

private def modes (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

private theorem mem_modes {N : ℕ} {k : ℤ} : k ∈ modes N ↔ |k| ≤ (N : ℤ) :=
  Finset.mem_Icc.trans abs_le.symm

private def triangle (N : ℕ) (k : ℤ) : ℝ :=
  1 - ((|k| : ℤ) : ℝ) / (N : ℝ)

private def edge (N : ℕ) (k : ℤ) : ℝ :=
  (if k = (N : ℤ) then 1 / 2 else 0) + (if k = -(N : ℤ) then 1 / 2 else 0)

private def expI (x : ℝ) : ℂ :=
  Complex.exp ((x : ℂ) * Complex.I)

private theorem fourier_fejer {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (∑ k ∈ modes N, (triangle N k : ℂ) * expI ((k : ℝ) * x)) =
      (fejerKernel N x : ℂ) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  apply Complex.ext
  · simp only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re, Complex.ofReal_im,
      zero_mul, sub_zero, expI, Complex.exp_ofReal_mul_I_re]
    unfold fejerKernel
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k hk h
    have hle := mem_modes.mp hk
    have hge : ¬ |k| < (N : ℤ) := fun hlt => h (Finset.mem_filter.mpr ⟨hk, hlt⟩)
    have heq : |k| = (N : ℤ) := le_antisymm hle (le_of_not_gt hge)
    simp [triangle, heq, hN']
  · simp only [Complex.ofReal_im, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
      zero_mul, add_zero, expI, Complex.exp_ofReal_mul_I_im]
    let f (k : ℤ) := triangle N k * Real.sin ((k : ℝ) * x)
    change ∑ k ∈ modes N, f k = 0
    have hneg : (∑ k ∈ modes N, f k) = ∑ k ∈ modes N, -f k := by
      refine Finset.sum_nbij' Neg.neg Neg.neg ?_ ?_ ?_ ?_ ?_
      · intro k hk
        simpa only [mem_modes, abs_neg] using hk
      · intro k hk
        simpa only [mem_modes, abs_neg] using hk
      · simp
      · simp
      · intro k _
        simp [f, triangle]
    rw [Finset.sum_neg_distrib] at hneg
    linarith only [hneg]

private theorem fourier_edge (N : ℕ) (x : ℝ) :
    (∑ k ∈ modes N, (edge N k : ℂ) * expI ((k : ℝ) * x)) =
      (Real.cos ((N : ℝ) * x) : ℂ) := by
  have hpos : (N : ℤ) ∈ modes N := mem_modes.mpr (by simp)
  have hneg : -(N : ℤ) ∈ modes N := mem_modes.mpr (by simp)
  simp only [edge, Complex.ofReal_add, add_mul, Finset.sum_add_distrib, apply_ite
    (fun r : ℝ => (r : ℂ)), ite_mul, Complex.ofReal_zero, zero_mul,
    Finset.sum_ite_eq', hpos, hneg, if_true, Int.cast_natCast, Int.cast_neg,
    neg_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  apply Complex.ext
  · simp [expI, Complex.add_re, Complex.mul_re, Complex.div_re,
      Complex.normSq_ofNat, Complex.exp_ofReal_mul_I_re]
    ring
  · simp [expI, Complex.add_im, Complex.mul_im, Complex.div_re, Complex.div_im,
      Complex.normSq_ofNat, Complex.exp_ofReal_mul_I_im]
    ring

private theorem normSq_expI_sub_one (x : ℝ) :
    Complex.normSq (expI x - 1) = 2 * (1 - Real.cos x) := by
  unfold expI
  rw [Complex.normSq_sub, Complex.normSq_eq_norm_sq (Complex.exp _),
    Complex.norm_exp_ofReal_mul_I]
  simp [Complex.exp_ofReal_mul_I_re]
  ring

private theorem fejer_defect {N : ℕ} (hN : 0 < N) (x : ℝ) :
    (1 - Real.cos x) * fejerKernel N x = (1 - Real.cos ((N : ℝ) * x)) / N := by
  have hpow (n : ℕ) : expI ((n : ℝ) * x) = expI x ^ n := by
    unfold expI
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h := congrArg Complex.normSq (geom_sum_mul (expI x) N)
  rw [Complex.normSq_mul, normSq_expI_sub_one, ← hpow, normSq_expI_sub_one] at h
  rw [fejer_square hN x]
  change (1 - Real.cos x) * (1 / (N : ℝ) *
      Complex.normSq (∑ r ∈ Finset.range N, expI ((r : ℝ) * x))) = _
  simp_rw [hpow]
  rw [← mul_div_assoc, one_div_mul_eq_div, ← mul_div_assoc]
  congr 1
  linarith only [h]

private def frequencyBox {J : Type*} [Fintype J] (N : ℕ) : Finset (J → ℤ) :=
  Fintype.piFinset fun _ => modes N

private theorem prod_cosine_expansion {J : Type*} [Fintype J]
    (N : ℕ) (b : J → ℤ → ℝ) (x y : J → ℝ)
    (hy : ∀ j, ∑ k ∈ modes N, (b j k : ℂ) * expI ((k : ℝ) * x j) = (y j : ℂ)) :
    (∑ k ∈ frequencyBox N, (∏ j, b j (k j)) *
      Real.cos (∑ j, (k j : ℝ) * x j)) = ∏ j, y j := by
  have h := Finset.prod_univ_sum (fun _ : J => modes N)
    (fun j k => (b j k : ℂ) * expI ((k : ℝ) * x j))
  simp only [hy] at h
  have hprod (k : J → ℤ) : (∏ j, expI ((k j : ℝ) * x j)) =
      expI (∑ j, (k j : ℝ) * x j) := by
    unfold expI
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
  simp only [Finset.prod_mul_distrib, ← Complex.ofReal_prod, hprod] at h
  have hre := congrArg Complex.re h.symm
  simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, expI, Complex.exp_ofReal_mul_I_re, frequencyBox] using hre

private def weights {J : Type*} [Fintype J] [DecidableEq J]
    (N : ℕ) (ε : ℝ) (p : J → ℝ) (k : J → ℤ) : ℝ :=
  (ε - 1 / (N : ℝ)) * (∏ j, triangle N (k j)) +
    ∑ i, (p i / (N : ℝ)) * ∏ j, (if j = i then edge N (k j) else triangle N (k j))

private theorem weighted_fejer_expansion {J : Type*} [Fintype J] [DecidableEq J]
    {N : ℕ} (hN : 0 < N) (ε : ℝ) (p x : J → ℝ) (hp : ∑ j, p j = 1) :
    (∑ k ∈ frequencyBox N, weights N ε p k * Real.cos (∑ j, (k j : ℝ) * x j)) =
      (ε - ∑ j, p j * (1 - Real.cos (x j))) * ∏ j, fejerKernel N (x j) := by
  let F (j : J) := fejerKernel N (x j)
  let C (j : J) := Real.cos ((N : ℝ) * x j)
  let K := ∏ j, F j
  let L (i : J) := ∏ j ∈ Finset.univ.erase i, F j
  have hsplit (i : J) : L i * F i = K :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  have heq (i : J) :
      (∏ j, if j = i then C j else F j) = L i * C i := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), if_pos rfl]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    rw [if_neg (Finset.ne_of_mem_erase hj)]
  have hbulk := prod_cosine_expansion N (fun _ : J => triangle N) x F
    (fun j => fourier_fejer hN (x j))
  have hedge (i : J) := prod_cosine_expansion N
    (fun j k => if j = i then edge N k else triangle N k) x
    (fun j => if j = i then C j else F j)
    (fun j => by
      by_cases hji : j = i
      · simpa only [hji, if_pos rfl] using fourier_edge N (x i)
      · simpa only [hji, if_false] using fourier_fejer hN (x j))
  calc
    _ = (ε - 1 / (N : ℝ)) * K + ∑ i, (p i / (N : ℝ)) * (L i * C i) := by
      simp only [weights, add_mul, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
      rw [← Finset.mul_sum, hbulk, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.mul_sum, hedge i, heq]
    _ = ε * K - ∑ i, p i * (1 - Real.cos (x i)) * K := by
      have hdefect (i : J) :
          p i * (1 - Real.cos (x i)) * K =
            (p i / (N : ℝ)) * K - (p i / (N : ℝ)) * (L i * C i) := by
        rw [← hsplit i]
        calc
          _ = (p i * L i) * ((1 - Real.cos (x i)) * F i) := by ring
          _ = _ := by rw [show (1 - Real.cos (x i)) * F i = (1 - C i) / N
                           from fejer_defect hN (x i)]; ring
      simp_rw [hdefect, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div, hp]
      ring
    _ = _ := by rw [sub_mul, Finset.sum_mul]

private theorem weights_mass {J : Type*} [Fintype J] [DecidableEq J]
    {N : ℕ} (hN : 0 < N) (ε : ℝ) (p : J → ℝ) (hp : ∑ j, p j = 1) :
    ∑ k ∈ frequencyBox N, weights N ε p k = ε * (N : ℝ) ^ Fintype.card J := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpeak : fejerKernel N 0 = (N : ℝ) := by
    rw [fejer_square hN]
    simp [Complex.normSq_natCast, hN', pow_two, ← mul_assoc]
  simpa [hpeak] using weighted_fejer_expansion hN ε p (fun _ => 0) hp

private theorem cosine_integral_lower (a R δ ξ φ : ℝ) (hδ : 0 < δ) (hξ : δ ≤ |ξ|) :
    -(2 / δ) ≤ ∫ t in a..a + R, Real.cos (ξ * t - φ) := by
  have hξ' : ξ ≠ 0 := abs_pos.mp (hδ.trans_le hξ)
  have heq : (∫ t in a..a + R, Real.cos (ξ * t - φ)) =
      (Real.sin (ξ * (a + R) - φ) - Real.sin (ξ * a - φ)) / ξ := by
    simp only [sub_eq_add_neg]
    rw [intervalIntegral.integral_comp_mul_add Real.cos hξ', integral_cos]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]
  have habs : |Real.sin (ξ * (a + R) - φ) - Real.sin (ξ * a - φ)| ≤ 2 := by
    exact (abs_sub _ _).trans ((add_le_add (Real.abs_sin_le_one _)
      (Real.abs_sin_le_one _)).trans_eq (by norm_num))
  have hbound : |∫ t in a..a + R, Real.cos (ξ * t - φ)| ≤ 2 / δ := by
    rw [heq, abs_div]
    exact (div_le_div_of_nonneg_right habs (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left (by norm_num) hδ hξ)
  exact (abs_le.mp hbound).1

private theorem window_from_cosine_certificate {K : Type*} [Fintype K] [DecidableEq K]
    (o : K) (c ξ φ : K → ℝ) (a R δ : ℝ)
    (hR : 0 < R) (hδ : 0 < δ)
    (hc : ∀ k, 0 ≤ c k) (hξo : ξ o = 0)
    (hzero : ∀ k, ξ k = 0 → Real.cos (φ k) = 1)
    (hgap : ∀ k, ξ k ≠ 0 → δ ≤ |ξ k|)
    (hbudget : R * δ * c o > 2 * ((∑ k, c k) - c o)) :
    ∃ t ∈ Icc a (a + R), 0 < ∑ k, c k * Real.cos (ξ k * t - φ k) := by
  let f (k : K) (t : ℝ) : ℝ := c k * Real.cos (ξ k * t - φ k)
  have hcont (k : K) : Continuous (f k) := by dsimp [f]; fun_prop
  have hR' : a ≤ a + R := by linarith
  have hterm (k : K) : -(2 / δ) * c k ≤ ∫ t in a..a + R, f k t := by
    by_cases hξ : ξ k = 0
    · simp [f, hξ, Real.cos_neg, hzero k hξ]
      exact le_trans (neg_nonpos.mpr (mul_nonneg (by positivity) (hc k)))
        (mul_nonneg hR.le (hc k))
    · unfold f
      rw [intervalIntegral.integral_const_mul, mul_comm (-(2 / δ))]
      exact mul_le_mul_of_nonneg_left (cosine_integral_lower a R δ _ _ hδ (hgap k hξ)) (hc k)
  have horigin : (∫ t in a..a + R, f o t) = R * c o := by
    simp [f, hξo, Real.cos_neg, hzero o hξo]
  have herase : (∑ k ∈ Finset.univ.erase o, c k) = (∑ k, c k) - c o := by
    rw [← Finset.sum_erase_add Finset.univ c (Finset.mem_univ o)]
    ring
  have htotal : 0 < ∫ t in a..a + R, ∑ k, f k t := by
    rw [intervalIntegral.integral_finsetSum (fun k _ => (hcont k).intervalIntegrable _ _)]
    rw [← Finset.sum_erase_add Finset.univ (fun k => ∫ t in a..a + R, f k t)
      (Finset.mem_univ o), horigin]
    have hsum := Finset.sum_le_sum (s := Finset.univ.erase o) (fun k _ => hterm k)
    rw [← Finset.mul_sum, herase] at hsum
    have hbudget' : 2 * ((∑ k, c k) - c o) / δ < R * c o := by
      apply (div_lt_iff₀ hδ).2
      calc
        _ < R * δ * c o := hbudget
        _ = R * c o * δ := by ring
    have hnormalize : -(2 / δ) * ((∑ k, c k) - c o) =
        -(2 * ((∑ k, c k) - c o) / δ) := by ring
    rw [hnormalize] at hsum
    linarith
  by_contra! h
  have hnonpos : (∫ t in a..a + R, ∑ k, f k t) ≤ 0 := by
    rw [← intervalIntegral.integral_zero (a := a) (b := a + R) (μ := volume)]
    exact intervalIntegral.integral_mono_on hR'
      ((continuous_finsetSum _ fun k _ => hcont k).intervalIntegrable _ _)
      (by simp) h
  linarith

/-- A finite band of compatible exact resonances and a lower bound for the other
frequencies give a uniform time window for normalized weighted phase loss. -/
theorem weighted_phase_recurrence {J : Type*} [Fintype J]
    (g θ p : J → ℝ) (N : ℕ) (ε δ a R : ℝ)
    (hN : 0 < N) (hp : ∀ j, 0 ≤ p j) (hpsum : ∑ j, p j = 1)
    (hε : 1 / (N : ℝ) < ε) (hδ : 0 < δ) (hR : 0 < R)
    (hzero : ∀ k : J → ℤ, (∀ j, |k j| ≤ (N : ℤ)) →
      (∑ j, (k j : ℝ) * g j) = 0 → Real.cos (∑ j, (k j : ℝ) * θ j) = 1)
    (hgap : ∀ k : J → ℤ, (∀ j, |k j| ≤ (N : ℤ)) →
      (∑ j, (k j : ℝ) * g j) ≠ 0 → δ ≤ |∑ j, (k j : ℝ) * g j|)
    (hbudget : R * δ * (ε - 1 / (N : ℝ)) >
      2 * (ε * (N : ℝ) ^ Fintype.card J - (ε - 1 / (N : ℝ)))) :
    ∃ t ∈ Icc a (a + R), phaseLoss g θ p t < ε := by
  classical
  let B := frequencyBox (J := J) N
  let c (k : B) := weights N ε p k.val
  let o : B := ⟨0, Fintype.mem_piFinset.mpr fun _ => mem_modes.mpr (by simp)⟩
  have hb (k : B) (j : J) : |k.val j| ≤ (N : ℤ) :=
    mem_modes.mp (Fintype.mem_piFinset.mp k.property j)
  have hc (k : B) : 0 ≤ c k := by
    have htriangle (j : J) : 0 ≤ triangle N (k.val j) := by
      apply sub_nonneg.mpr
      have hN' : (0 : ℝ) < N := by positivity
      rw [div_le_iff₀ hN', one_mul]
      exact_mod_cast hb k j
    have hedge (j : J) : 0 ≤ edge N (k.val j) := by unfold edge; positivity
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hε.le) (Finset.prod_nonneg fun j _ =>
      htriangle j)) (Finset.sum_nonneg fun i _ => mul_nonneg (by positivity : 0 ≤ p i / (N : ℝ))
        (Finset.prod_nonneg fun j _ => by by_cases h : j = i <;> simp [h, hedge, htriangle]))
  have hN' : (N : ℤ) ≠ 0 := by positivity
  have hc0 : c o = ε - 1 / (N : ℝ) := by
    change weights N ε p 0 = _
    simp [weights, triangle, edge, hN', Ne.symm hN']
  have hmass : (∑ k : B, c k) = ε * (N : ℝ) ^ Fintype.card J := by
    simpa only [c, Finset.sum_coe_sort, B] using weights_mass hN ε p hpsum
  obtain ⟨t, ht, hs⟩ := window_from_cosine_certificate o c
    (fun k => ∑ j, (k.val j : ℝ) * g j) (fun k => ∑ j, (k.val j : ℝ) * θ j)
    a R δ hR hδ hc (by simp [o])
    (fun k => hzero k.val (hb k)) (fun k => hgap k.val (hb k))
    (by simpa only [hc0, hmass] using hbudget)
  have hx (k : J → ℤ) :
      (∑ j, (k j : ℝ) * g j) * t - (∑ j, (k j : ℝ) * θ j) =
        ∑ j, (k j : ℝ) * (g j * t - θ j) := by
    simp only [mul_sub, ← mul_assoc, Finset.sum_sub_distrib, Finset.sum_mul]
  simp_rw [hx] at hs
  rw [show (∑ k : B, c k * Real.cos (∑ j, (k.val j : ℝ) * (g j * t - θ j))) =
      (ε - phaseLoss g θ p t) * ∏ j, fejerKernel N (g j * t - θ j) by
    simpa only [c, Finset.sum_coe_sort, B, phaseLoss] using
      weighted_fejer_expansion hN ε p (fun j => g j * t - θ j) hpsum] at hs
  have hK : 0 ≤ ∏ j, fejerKernel N (g j * t - θ j) := by
    apply Finset.prod_nonneg
    intro j _
    rw [fejer_square hN]
    positivity
  exact ⟨t, ht, sub_pos.mp (pos_of_mul_pos_left hs hK)⟩

end

end D5.S3.Fourier.WeightedPhaseRecurrence
