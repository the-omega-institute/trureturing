/- GID: D5/S3/Arith/Robin/Analytic/OmegaTail/Binning
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaTail/Binning
   mirror-E: none(waiver:general-integral-estimates)
   anchors: []
   utility: none
   digest: Entropy and logarithmic moment bounds for finite interval bins. -/

import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Set MeasureTheory Finset
open scoped Topology BigOperators

namespace D5.S3.Arith.Robin.Analytic.OmegaTail.Binning

/-- Replacing a density on an interval by its average increases its binary entropy. -/
private theorem entropy_average {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hg : IntegrableOn g (Ioc a b))
    (hh : IntegrableOn (fun u => binEntropy (g u)) (Ioc a b))
    (h01 : ∀ᵐ u ∂volume.restrict (Ioc a b), g u ∈ Icc (0 : ℝ) 1) :
    (∫ u in Ioc a b, binEntropy (g u)) ≤
      (b - a) * binEntropy ((∫ u in Ioc a b, g u) / (b - a)) := by
  have hvol : volume (Ioc a b) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hvreal : volume.real (Ioc a b) = b - a :=
    Real.volume_real_Ioc_of_le hab.le
  have hj := strictConcave_binEntropy.concaveOn.le_map_set_average
    binEntropy_continuous.continuousOn isClosed_Icc hvol
    (by simp [Real.volume_Ioc]) h01 hg hh
  simp only [setAverage_eq, hvreal, smul_eq_mul] at hj
  have hm := mul_le_mul_of_nonneg_left hj (sub_pos.mpr hab).le
  simpa only [← mul_assoc, mul_inv_cancel₀ (sub_pos.mpr hab).ne', one_mul,
    div_eq_mul_inv, mul_comm (∫ u in Ioc a b, g u) (b - a)⁻¹] using hm

/-- On a narrow multiplicative bin the right-endpoint cost loses at most its log width. -/
private theorem endpoint_moment_le {g : ℝ → ℝ} {a b eta : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (heta : log (b / a) ≤ eta)
    (hg : IntegrableOn g (Ioc a b))
    (hgl : IntegrableOn (fun u => g u * log u) (Ioc a b))
    (hgn : ∀ u ∈ Ioc a b, 0 ≤ g u) :
    (∫ u in Ioc a b, g u) * log b ≤
      (∫ u in Ioc a b, g u * log u) + eta * ∫ u in Ioc a b, g u := by
  have hb : 0 < b := ha.trans_le hab
  have hfun : ∀ u ∈ Ioc a b, g u * log b ≤ g u * log u + eta * g u := by
    intro u hu
    have hlog : log b - log u ≤ eta := by
      have hlu : log a ≤ log u := log_le_log ha hu.1.le
      rw [log_div hb.ne' ha.ne'] at heta
      linarith
    have hmul := mul_le_mul_of_nonneg_left hlog (hgn u hu)
    nlinarith
  have h := setIntegral_mono_on (hg.mul_const (log b))
    (hgl.add (hg.const_mul eta)) measurableSet_Ioc hfun
  change (∫ u in Ioc a b, g u * log b) ≤
    ∫ u in Ioc a b, g u * log u + eta * g u at h
  simpa only [integral_add hgl (hg.const_mul eta), integral_mul_const,
    integral_const_mul] using h

private lemma uniform_bin_sum {g : ℝ → ℝ} {A B : ℝ} (hAB : A < B)
    (hg : ContinuousOn g (Icc A B)) {n : ℕ} (hn : 0 < n) :
    ∑ j : Fin n, ∫ u in Ioc (A + (B - A) * (j : ℕ) / n)
      (A + (B - A) * (((j : ℕ) + 1 : ℕ) : ℝ) / n), g u = ∫ u in Ioc A B, g u := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  let t : ℕ → ℝ := fun k => A + (B - A) * k / n
  have hbound : ∀ k ≤ n, t k ∈ Icc A B := by
    intro k hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    have hl : 0 ≤ (B - A) * (k : ℝ) / n := by positivity
    have hu : (B - A) * (k : ℝ) / n ≤ B - A :=
      (div_le_iff₀ hnreal).mpr (mul_le_mul_of_nonneg_left hkn (sub_pos.mpr hAB).le)
    dsimp [t]
    constructor <;> linarith
  have hstep : ∀ k : ℕ, t k < t (k + 1) := by
    intro k
    dsimp [t]
    push_cast
    have hp : 0 < (B - A) / n := div_pos (sub_pos.mpr hAB) (by exact_mod_cast hn)
    have he : (B - A) * ((k : ℝ) + 1) / n = (B - A) * k / n + (B - A) / n := by ring
    rw [he]
    linarith
  have hi : ∀ k < n, IntervalIntegrable g volume (t k) (t (k + 1)) := by
    intro k hk
    apply ContinuousOn.intervalIntegrable_of_Icc (hstep k).le
    apply hg.mono
    exact Icc_subset_Icc (hbound k hk.le).1 (hbound (k + 1) hk).2
  have h := intervalIntegral.sum_integral_adjacent_intervals hi
  have h0 : t 0 = A := by simp [t]
  have hn' : t n = B := by dsimp [t]; field_simp; ring
  rw [h0, hn', intervalIntegral.integral_of_le hAB.le] at h
  change (∑ j : Fin n, (fun k : ℕ => ∫ u in Ioc (t k) (t (k + 1)), g u) j) = _
  calc
    _ = ∑ k ∈ range n, ∫ u in Ioc (t k) (t (k + 1)), g u :=
      Fin.sum_univ_eq_sum_range (fun k : ℕ => ∫ u in Ioc (t k) (t (k + 1)), g u) n
    _ = ∑ k ∈ range n, ∫ u in t k..t (k + 1), g u := by
      apply sum_congr rfl
      intro k hk
      exact (intervalIntegral.integral_of_le (hstep k).le).symm
    _ = _ := h

/-- A positive continuous density on a compact interval admits finitely many
ordered bins preserving mass and entropy with arbitrarily small logarithmic cost loss. -/
theorem compact_bins {g : ℝ → ℝ} {A B eta : ℝ} (hA : 0 < A) (hAB : A < B)
    (hg : ContinuousOn g (Icc A B)) (h01 : ∀ u ∈ Icc A B, g u ∈ Ioo (0 : ℝ) 1)
    (heta : 0 < eta) :
    ∃ n : ℕ, 0 < n ∧ ∃ a b r : Fin n → ℝ,
      (∀ j, 0 < a j ∧ a j < b j ∧ 0 < r j ∧ r j < b j - a j) ∧
      (Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) ∧
      (∑ j, r j) = (∫ u in Ioc A B, g u) ∧
      (∫ u in Ioc A B, binEntropy (g u)) ≤
        (∑ j, (b j - a j) * binEntropy (r j / (b j - a j))) ∧
      (∑ j, r j * log (b j)) ≤ (∫ u in Ioc A B, g u * log u) +
        eta * ∫ u in Ioc A B, g u := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max 0 ((B - A) / (eta * A)))
  have hnpos : 0 < n := by
    have : (0 : ℝ) < n := (le_max_left _ _).trans_lt hn
    exact_mod_cast this
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  let t : ℕ → ℝ := fun k => A + (B - A) * k / n
  let a : Fin n → ℝ := fun j => t j
  let b : Fin n → ℝ := fun j => t ((j : ℕ) + 1)
  let r : Fin n → ℝ := fun j => ∫ u in Ioc (a j) (b j), g u
  have hbound : ∀ k ≤ n, t k ∈ Icc A B := by
    intro k hk
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    have hl : 0 ≤ (B - A) * (k : ℝ) / n := by positivity
    have hu : (B - A) * (k : ℝ) / n ≤ B - A :=
      (div_le_iff₀ hnreal).mpr (mul_le_mul_of_nonneg_left hkn (sub_pos.mpr hAB).le)
    dsimp [t]
    constructor <;> linarith
  have hstep : ∀ k : ℕ, t (k + 1) - t k = (B - A) / n := by
    intro k
    dsimp [t]
    push_cast
    ring
  have hwidth : 0 < (B - A) / n := div_pos (sub_pos.mpr hAB) hnreal
  have hab : ∀ j, a j < b j := by
    intro j
    apply sub_pos.mp
    change 0 < t ((j : ℕ) + 1) - t j
    rw [hstep]
    exact hwidth
  have hsub : ∀ j, Icc (a j) (b j) ⊆ Icc A B := by
    intro j
    exact Icc_subset_Icc (hbound j (Nat.le_of_lt j.isLt)).1
      (hbound ((j : ℕ) + 1) j.isLt).2
  have hapos : ∀ j, 0 < a j := by
    intro j
    exact hA.trans_le (hbound j j.isLt.le).1
  have hg' : ∀ j, IntegrableOn g (Ioc (a j) (b j)) := by
    intro j
    exact ((hg.mono (hsub j)).intervalIntegrable_of_Icc (hab j).le).1
  have hhc : ContinuousOn (fun u => binEntropy (g u)) (Icc A B) :=
    binEntropy_continuous.comp_continuousOn hg
  have hhh : ∀ j, IntegrableOn (fun u => binEntropy (g u)) (Ioc (a j) (b j)) := by
    intro j
    exact ((hhc.mono (hsub j)).intervalIntegrable_of_Icc (hab j).le).1
  have hglc : ContinuousOn (fun u => g u * log u) (Icc A B) :=
    hg.mul (continuousOn_log.mono (fun u hu => ne_of_gt (hA.trans_le hu.1)))
  have hgg : ∀ j, IntegrableOn (fun u => g u * log u) (Ioc (a j) (b j)) := by
    intro j
    exact ((hglc.mono (hsub j)).intervalIntegrable_of_Icc (hab j).le).1
  have hmass : ∑ j, r j = ∫ u in Ioc A B, g u := by
    simpa only [r, a, b, t] using uniform_bin_sum hAB hg hnpos
  have hhsum : (∑ j : Fin n, ∫ u in Ioc (a j) (b j), binEntropy (g u)) =
      ∫ u in Ioc A B, binEntropy (g u) := by
    simpa only [a, b, t] using uniform_bin_sum hAB hhc hnpos
  have hlsum : (∑ j : Fin n, ∫ u in Ioc (a j) (b j), g u * log u) =
      ∫ u in Ioc A B, g u * log u := by
    simpa only [a, b, t] using uniform_bin_sum hAB hglc hnpos
  have horder : ∀ i j : Fin n, i < j → b i ≤ a j := by
    intro i j hij
    have hcast : ((i : ℕ) + 1 : ℝ) ≤ (j : ℕ) := by exact_mod_cast hij
    dsimp [a, b, t]
    push_cast at hcast ⊢
    exact add_le_add_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcast (sub_pos.mpr hAB).le) hnreal.le) A
  refine ⟨n, hnpos, a, b, r, ?_, ?_, hmass, ?_, ?_⟩
  · intro j
    have hfc := hg.mono (hsub j)
    have hgp : 0 < ∫ u in a j..b j, g u := by
      apply intervalIntegral.integral_pos (hab j) hfc
      · intro u hu
        exact (h01 u (hsub j ⟨hu.1.le, hu.2⟩)).1.le
      · exact ⟨a j, ⟨le_rfl, (hab j).le⟩,
          (h01 (a j) (hsub j ⟨le_rfl, (hab j).le⟩)).1⟩
    have hgu : (∫ u in a j..b j, g u) < b j - a j := by
      have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (hab j) hfc (continuousOn_const (c := (1 : ℝ)))
        (fun u hu => (h01 u (hsub j ⟨hu.1.le, hu.2⟩)).2.le)
        ⟨a j, ⟨le_rfl, (hab j).le⟩,
          (h01 (a j) (hsub j ⟨le_rfl, (hab j).le⟩)).2⟩
      simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_one] using hlt
    rw [intervalIntegral.integral_of_le (hab j).le] at hgp hgu
    exact ⟨hapos j, hab j, hgp, hgu⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact Ioc_disjoint_Ioc_of_le (horder i j hlt)
    · exact (Ioc_disjoint_Ioc_of_le (horder j i hgt)).symm
  · rw [← hhsum]
    apply sum_le_sum
    intro j _
    apply entropy_average (hab j) (hg' j) (hhh j)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact ⟨(h01 u (hsub j ⟨hu.1.le, hu.2⟩)).1.le,
      (h01 u (hsub j ⟨hu.1.le, hu.2⟩)).2.le⟩
  · calc
      ∑ j, r j * log (b j) ≤ ∑ j, ((∫ u in Ioc (a j) (b j), g u * log u) + eta * r j) := by
        apply sum_le_sum
        intro j _
        apply endpoint_moment_le (hapos j) (hab j).le _ (hg' j) (hgg j)
          (fun u hu => (h01 u (hsub j ⟨hu.1.le, hu.2⟩)).1.le)
        have hsmall : (B - A) / n < eta * A := by
          have hnat := (le_max_right 0 ((B - A) / (eta * A))).trans_lt hn
          apply (div_lt_iff₀ hnreal).mpr
          have ht := (div_lt_iff₀ (mul_pos heta hA)).mp hnat
          nlinarith
        have hupper := log_le_sub_one_of_pos (div_pos (hapos j |>.trans (hab j)) (hapos j))
        have hwidthj : b j - a j = (B - A) / n := hstep j
        have hratio : b j / a j - 1 < eta := by
          apply (sub_lt_iff_lt_add).mpr
          apply (div_lt_iff₀ (hapos j)).mpr
          have hAaj := (hbound j j.isLt.le).1
          nlinarith
        exact hupper.trans hratio.le
      _ = (∫ u in Ioc A B, g u * log u) + eta * ∫ u in Ioc A B, g u := by
        rw [sum_add_distrib, ← mul_sum, hmass, hlsum]

end D5.S3.Arith.Robin.Analytic.OmegaTail.Binning
