/- GID: D5/S3/Quantum/Entanglement/SpectralFamilyGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/SpectralFamilyGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite spectra have an attained variance maximum, diameter bounds, and a simplex support certificate. -/

import D5.S3.TotalVariation.HellingerDivergence
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Finset.Max

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.SpectralFamilyGeometry

open D5.S3.TotalVariation.Hellinger
open D5.S3.TotalVariation.HellingerDivergence
open D5.S3.TotalVariation.Bhattacharyya
open scoped BigOperators

noncomputable section

variable {Sector Coord : Type*} [Fintype Sector] [Fintype Coord]

/-- The Gram energy of the square-root residual spectra. -/
def spectralGramEnergy (spectrum : Sector → Coord → ℝ) (p : Sector → ℝ) : ℝ :=
  ∑ s, ∑ t, p s * p t * bhattacharyya (spectrum s) (spectrum t)

/-- The weighted pairwise variance of the square-root spectral vectors. -/
def spectralPairVariance (spectrum : Sector → Coord → ℝ) (p : Sector → ℝ) : ℝ :=
  ∑ s, ∑ t, p s * p t * hellingerSq (spectrum s) (spectrum t)

/-- The squared Euclidean gap between zero-padded square-root spectra. -/
def spectralGap (spectrum : Sector → Coord → ℝ) (s t : Sector) : ℝ :=
  hellingerSq (spectrum s) (spectrum t)

/-- Attained finite-family variance, sharp diameter comparison, zero criterion, and the
simplex support certificate of an optimal weight. This coordinatewise probability-family
statement also applies to spectra sorted in a common decreasing coordinate order and padded
with zeros. Without that ordering, its zero criterion compares coordinate functions, rather
than identifying spectra up to independent permutations. -/
theorem finite_spectral_family_geometry
    [Nonempty Sector] (spectrum : Sector → Coord → ℝ)
    (hnonneg : ∀ s j, 0 ≤ spectrum s j)
    (hnormal : ∀ s, ∑ j, spectrum s j = 1) :
    (∀ p ∈ stdSimplex ℝ Sector,
      spectralPairVariance spectrum p = 2 * (1 - spectralGramEnergy spectrum p)) ∧
    ∃ p ∈ stdSimplex ℝ Sector, ∃ s t : Sector,
      (∀ r ∈ stdSimplex ℝ Sector,
        spectralPairVariance spectrum r ≤ spectralPairVariance spectrum p) ∧
      (∀ a b : Sector, spectralGap spectrum a b ≤ spectralGap spectrum s t) ∧
      spectralGap spectrum s t / 2 ≤ spectralPairVariance spectrum p ∧
      spectralPairVariance spectrum p ≤ spectralGap spectrum s t ∧
      (spectralPairVariance spectrum p = 0 ↔
        ∀ a b : Sector, spectrum a = spectrum b) ∧
      (∀ a : Sector,
        spectralGramEnergy spectrum p ≤
          ∑ t, p t * bhattacharyya (spectrum a) (spectrum t) ∧
        (0 < p a → spectralGramEnergy spectrum p =
          ∑ t, p t * bhattacharyya (spectrum a) (spectrum t))) ∧
      (∀ r ∈ stdSimplex ℝ Sector,
        (∀ u ∈ stdSimplex ℝ Sector,
          spectralGramEnergy spectrum r ≤ spectralGramEnergy spectrum u) ↔
        ∀ a : Sector,
          spectralGramEnergy spectrum r ≤
            ∑ t, r t * bhattacharyya (spectrum a) (spectrum t) ∧
          (0 < r a → spectralGramEnergy spectrum r =
            ∑ t, r t * bhattacharyya (spectrum a) (spectrum t))) := by
  classical
  have gram_energy_eq_sum_sq
      (spectrum : Sector → Coord → ℝ)
      (hnonneg : ∀ s j, 0 ≤ spectrum s j) (w : Sector → ℝ) :
      spectralGramEnergy spectrum w =
        ∑ j : Coord, (∑ s : Sector, w s * Real.sqrt (spectrum s j)) ^ 2 := by
    classical
    have hroot (s t : Sector) (j : Coord) :
        Real.sqrt (spectrum s j * spectrum t j) =
          Real.sqrt (spectrum s j) * Real.sqrt (spectrum t j) :=
      Real.sqrt_mul (hnonneg s j) _
    calc
      spectralGramEnergy spectrum w =
          ∑ s : Sector, ∑ t : Sector, ∑ j : Coord,
            (w s * Real.sqrt (spectrum s j)) *
              (w t * Real.sqrt (spectrum t j)) := by
        unfold spectralGramEnergy
        simp_rw [bhattacharyya, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro t _
        apply Finset.sum_congr rfl
        intro j _
        rw [hroot]
        ring
      _ = ∑ s : Sector, ∑ j : Coord, ∑ t : Sector,
            (w s * Real.sqrt (spectrum s j)) *
              (w t * Real.sqrt (spectrum t j)) := by
        apply Finset.sum_congr rfl
        intro s _
        exact Finset.sum_comm
      _ = ∑ j : Coord, ∑ s : Sector, ∑ t : Sector,
            (w s * Real.sqrt (spectrum s j)) *
              (w t * Real.sqrt (spectrum t j)) := Finset.sum_comm
      _ = ∑ j : Coord, (∑ s : Sector, w s * Real.sqrt (spectrum s j)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_two, Finset.sum_mul_sum]
  have gram_energy_nonneg
      (spectrum : Sector → Coord → ℝ)
      (hnonneg : ∀ s j, 0 ≤ spectrum s j) (w : Sector → ℝ) :
      0 ≤ spectralGramEnergy spectrum w := by
    rw [gram_energy_eq_sum_sq spectrum hnonneg w]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have gram_energy_expansion
      (spectrum : Sector → Coord → ℝ) (p r : Sector → ℝ) :
      spectralGramEnergy spectrum r = spectralGramEnergy spectrum p +
        2 * (∑ a : Sector, (r a - p a) *
          ∑ b : Sector, p b * bhattacharyya (spectrum a) (spectrum b)) +
        spectralGramEnergy spectrum (fun a => r a - p a) := by
    classical
    let d : Sector → ℝ := fun a => r a - p a
    have hr (a : Sector) : r a = p a + d a := by dsimp [d]; ring
    have hsymm (a b : Sector) :
        bhattacharyya (spectrum a) (spectrum b) =
          bhattacharyya (spectrum b) (spectrum a) := by
      unfold bhattacharyya
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm]
    have hcross :
        (∑ a : Sector, ∑ b : Sector,
          p a * d b * bhattacharyya (spectrum a) (spectrum b)) =
        ∑ a : Sector, ∑ b : Sector,
          d a * p b * bhattacharyya (spectrum a) (spectrum b) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hsymm b a]
      ring
    have hrow :
        (∑ a : Sector, d a *
          ∑ b : Sector, p b * bhattacharyya (spectrum a) (spectrum b)) =
        ∑ a : Sector, ∑ b : Sector,
          d a * p b * bhattacharyya (spectrum a) (spectrum b) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    calc
      spectralGramEnergy spectrum r =
          ∑ a : Sector, ∑ b : Sector,
            (p a + d a) * (p b + d b) *
              bhattacharyya (spectrum a) (spectrum b) := by
        unfold spectralGramEnergy
        simp_rw [hr]
      _ = spectralGramEnergy spectrum p +
          2 * (∑ a : Sector, d a *
            ∑ b : Sector, p b * bhattacharyya (spectrum a) (spectrum b)) +
          spectralGramEnergy spectrum d := by
        unfold spectralGramEnergy
        simp_rw [show ∀ a b : Sector,
          (p a + d a) * (p b + d b) *
            bhattacharyya (spectrum a) (spectrum b) =
          p a * p b * bhattacharyya (spectrum a) (spectrum b) +
          d a * p b * bhattacharyya (spectrum a) (spectrum b) +
          p a * d b * bhattacharyya (spectrum a) (spectrum b) +
          d a * d b * bhattacharyya (spectrum a) (spectrum b) from
            fun a b => by ring]
        simp_rw [Finset.sum_add_distrib]
        rw [hcross, hrow]
        ring
      _ = _ := rfl
  have gram_energy_scale
      (spectrum : Sector → Coord → ℝ) (w : Sector → ℝ) (c : ℝ) :
      spectralGramEnergy spectrum (fun a => c * w a) =
        c ^ 2 * spectralGramEnergy spectrum w := by
    unfold spectralGramEnergy
    calc
      (∑ a : Sector, ∑ b : Sector,
        (c * w a) * (c * w b) * bhattacharyya (spectrum a) (spectrum b)) =
        ∑ a : Sector, ∑ b : Sector,
          c ^ 2 * (w a * w b * bhattacharyya (spectrum a) (spectrum b)) := by
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = c ^ 2 *
          ∑ a : Sector, ∑ b : Sector,
            w a * w b * bhattacharyya (spectrum a) (spectrum b) := by
        simp_rw [← Finset.mul_sum]
  have hpair (s t : Sector) :
      hellingerSq (spectrum s) (spectrum t) =
        2 * (1 - bhattacharyya (spectrum s) (spectrum t)) := by
    exact hellinger_sq_eq_two_sub (spectrum s) (spectrum t)
      ⟨hnonneg s, hnormal s⟩ ⟨hnonneg t, hnormal t⟩
  have hvariance (p : Sector → ℝ) (hp : p ∈ stdSimplex ℝ Sector) :
      spectralPairVariance spectrum p = 2 * (1 - spectralGramEnergy spectrum p) := by
    have hp_sum : ∑ s, p s = 1 := hp.2
    have hweight : (∑ s : Sector, ∑ t : Sector, p s * p t) = 1 := by
      simp_rw [← Finset.mul_sum]
      simp [hp_sum]
    unfold spectralPairVariance spectralGramEnergy
    calc
      (∑ s : Sector, ∑ t : Sector,
          p s * p t * hellingerSq (spectrum s) (spectrum t)) =
          ∑ s : Sector, ∑ t : Sector,
            (2 * (p s * p t) -
              2 * (p s * p t * bhattacharyya (spectrum s) (spectrum t))) := by
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro t _
        rw [hpair]
        ring
      _ = 2 * (∑ s : Sector, ∑ t : Sector, p s * p t) -
          2 * (∑ s : Sector, ∑ t : Sector,
            p s * p t * bhattacharyya (spectrum s) (spectrum t)) := by
        simp_rw [Finset.sum_sub_distrib]
        simp_rw [← Finset.mul_sum]
      _ = 2 * (1 - ∑ s : Sector, ∑ t : Sector,
            p s * p t * bhattacharyya (spectrum s) (spectrum t)) := by
        rw [hweight]
        ring
  have hcontinuous : Continuous (spectralPairVariance spectrum) := by
    unfold spectralPairVariance
    fun_prop
  have hsimplex : (stdSimplex ℝ Sector).Nonempty := by
    obtain ⟨s⟩ := ‹Nonempty Sector›
    exact ⟨Pi.single s 1, single_mem_stdSimplex ℝ s⟩
  obtain ⟨p, hp, hpmax⟩ :=
    (isCompact_stdSimplex ℝ Sector).exists_isMaxOn hsimplex hcontinuous.continuousOn
  obtain ⟨st, _, hdiam⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Sector × Sector))
      (fun st => spectralGap spectrum st.1 st.2) Finset.univ_nonempty
  rcases st with ⟨s, t⟩
  have hdiam' (a b : Sector) : spectralGap spectrum a b ≤ spectralGap spectrum s t :=
    hdiam (a, b) (Finset.mem_univ _)
  have hupper : spectralPairVariance spectrum p ≤ spectralGap spectrum s t := by
    have hp_sum : ∑ a, p a = 1 := hp.2
    have hweight : (∑ a : Sector, ∑ b : Sector, p a * p b) = 1 := by
      simp_rw [← Finset.mul_sum]
      simp [hp_sum]
    calc
      spectralPairVariance spectrum p ≤
          ∑ a : Sector, ∑ b : Sector,
            p a * p b * spectralGap spectrum s t := by
        unfold spectralPairVariance
        apply Finset.sum_le_sum
        intro a _
        apply Finset.sum_le_sum
        intro b _
        exact mul_le_mul_of_nonneg_left (hdiam' a b)
          (mul_nonneg (hp.1 a) (hp.1 b))
      _ = (∑ a : Sector, ∑ b : Sector, p a * p b) *
          spectralGap spectrum s t := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_mul]
      _ = spectralGap spectrum s t := by rw [hweight, one_mul]
  have hlower : spectralGap spectrum s t / 2 ≤ spectralPairVariance spectrum p := by
    let r : Sector → ℝ := fun u =>
      (if u = s then (1/2 : ℝ) else 0) + (if u = t then 1/2 else 0)
    have hr : r ∈ stdSimplex ℝ Sector := by
      constructor
      · intro u
        dsimp [r]
        positivity
      · dsimp [r]
        simp_rw [Finset.sum_add_distrib]
        simp
        norm_num
    have hrvalue : spectralPairVariance spectrum r = spectralGap spectrum s t / 2 := by
      have hsingle (a : Sector) (f : Sector → ℝ) :
          (∑ u : Sector, (if u = a then (1/2 : ℝ) else 0) * f u) =
            (1/2 : ℝ) * f a := by
        simp_rw [ite_mul, zero_mul]
        simp
      have hpair_sum (a b : Sector) :
          (∑ u : Sector, ∑ v : Sector,
            (if u = a then (1/2 : ℝ) else 0) *
              (if v = b then (1/2 : ℝ) else 0) *
                hellingerSq (spectrum u) (spectrum v)) =
            hellingerSq (spectrum a) (spectrum b) / 4 := by
        calc
          (∑ u : Sector, ∑ v : Sector,
            (if u = a then (1/2 : ℝ) else 0) *
              (if v = b then (1/2 : ℝ) else 0) *
                hellingerSq (spectrum u) (spectrum v)) =
              ∑ u : Sector, (if u = a then (1/2 : ℝ) else 0) *
                (∑ v : Sector, (if v = b then (1/2 : ℝ) else 0) *
                  hellingerSq (spectrum u) (spectrum v)) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [Finset.mul_sum]
            simp_rw [mul_assoc]
          _ = ∑ u : Sector, (if u = a then (1/2 : ℝ) else 0) *
                ((1/2 : ℝ) * hellingerSq (spectrum u) (spectrum b)) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [hsingle]
          _ = (1/2 : ℝ) * ((1/2 : ℝ) *
                hellingerSq (spectrum a) (spectrum b)) := hsingle a _
          _ = hellingerSq (spectrum a) (spectrum b) / 4 := by ring
      unfold spectralPairVariance spectralGap
      dsimp [r]
      simp only [add_mul, mul_add, Finset.sum_add_distrib]
      simp_rw [hpair_sum]
      rw [hellinger_sq_self, hellinger_sq_self,
        hellinger_sq_comm (spectrum t) (spectrum s)]
      ring
    rw [← hrvalue]
    exact hpmax hr
  have hzero : spectralPairVariance spectrum p = 0 ↔
      ∀ a b : Sector, spectrum a = spectrum b := by
    constructor
    · intro hz a b
      have hD0 : spectralGap spectrum s t = 0 := by
        have hDnonneg := hellinger_sq_nonneg (spectrum s) (spectrum t)
        change 0 ≤ spectralGap spectrum s t at hDnonneg
        linarith
      have hab0 : spectralGap spectrum a b = 0 :=
        le_antisymm ((hdiam' a b).trans_eq hD0)
          (hellinger_sq_nonneg (spectrum a) (spectrum b))
      exact (hellinger_sq_eq_zero_iff (spectrum a) (spectrum b)
        (hnonneg a) (hnonneg b)).mp hab0
    · intro hsame
      unfold spectralPairVariance
      apply Finset.sum_eq_zero
      intro a _
      apply Finset.sum_eq_zero
      intro b _
      rw [hsame a b, hellinger_sq_self]
      ring
  have hqmin (r : Sector → ℝ) (hr : r ∈ stdSimplex ℝ Sector) :
      spectralGramEnergy spectrum p ≤ spectralGramEnergy spectrum r := by
    have hmax := hpmax hr
    change spectralPairVariance spectrum r ≤ spectralPairVariance spectrum p at hmax
    rw [hvariance r hr, hvariance p hp] at hmax
    linarith
  have hnecessary (p : Sector → ℝ) (hp : p ∈ stdSimplex ℝ Sector)
      (hqmin : ∀ r ∈ stdSimplex ℝ Sector,
        spectralGramEnergy spectrum p ≤ spectralGramEnergy spectrum r) :
      ∀ a : Sector,
        spectralGramEnergy spectrum p ≤
          ∑ b, p b * bhattacharyya (spectrum a) (spectrum b) ∧
        (0 < p a → spectralGramEnergy spectrum p =
          ∑ b, p b * bhattacharyya (spectrum a) (spectrum b)) := by
    let row : Sector → ℝ := fun a =>
      ∑ b : Sector, p b * bhattacharyya (spectrum a) (spectrum b)
    have hweighted : (∑ a : Sector, p a * row a) =
        spectralGramEnergy spectrum p := by
      unfold spectralGramEnergy
      apply Finset.sum_congr rfl
      intro a _
      dsimp [row]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    have hrow_ge (a : Sector) : spectralGramEnergy spectrum p ≤ row a := by
      let e : Sector → ℝ := fun b => if a = b then 1 else 0
      have he : e ∈ stdSimplex ℝ Sector := ite_eq_mem_stdSimplex ℝ a
      let r : ℝ → Sector → ℝ := fun ε b => (1 - ε) * p b + ε * e b
      have hr (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
          r ε ∈ stdSimplex ℝ Sector := by
        have hconv := (convex_stdSimplex ℝ Sector) hp he
          (sub_nonneg.mpr hε1) hε0 (by ring : (1 - ε) + ε = 1)
        convert hconv using 1
        funext b
        simp [r, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have hd (ε : ℝ) : (fun b => r ε b - p b) =
          fun b => ε * (e b - p b) := by
        funext b
        dsimp [r]
        ring
      have hlin (ε : ℝ) :
          (∑ b : Sector, (r ε b - p b) * row b) =
            ε * (row a - spectralGramEnergy spectrum p) := by
        calc
          (∑ b : Sector, (r ε b - p b) * row b) =
              ε * ((∑ b : Sector, e b * row b) -
                ∑ b : Sector, p b * row b) := by
            calc
              (∑ b : Sector, (r ε b - p b) * row b) =
                  ∑ b : Sector, ε * (e b * row b - p b * row b) := by
                apply Finset.sum_congr rfl
                intro b _
                rw [congrFun (hd ε) b]
                ring
              _ = ε * (∑ b : Sector, (e b * row b - p b * row b)) := by
                rw [Finset.mul_sum]
              _ = ε * ((∑ b : Sector, e b * row b) -
                    ∑ b : Sector, p b * row b) := by
                rw [Finset.sum_sub_distrib]
          _ = ε * (row a - spectralGramEnergy spectrum p) := by
            rw [hweighted]
            have heval : (∑ b : Sector, e b * row b) = row a := by simp [e]
            rw [heval]
      have hquad (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
          0 ≤ 2 * ε * (row a - spectralGramEnergy spectrum p) +
            ε ^ 2 * spectralGramEnergy spectrum (fun b => e b - p b) := by
        have hmin := hqmin (r ε) (hr ε hε0.le hε1)
        have hexp := gram_energy_expansion spectrum p (r ε)
        change spectralGramEnergy spectrum (r ε) =
          spectralGramEnergy spectrum p +
            2 * (∑ b : Sector, (r ε b - p b) * row b) +
            spectralGramEnergy spectrum (fun b => r ε b - p b) at hexp
        rw [hlin, hd, gram_energy_scale] at hexp
        linarith
      by_contra hnot
      let A := row a - spectralGramEnergy spectrum p
      let B := spectralGramEnergy spectrum (fun b => e b - p b)
      have hA : A < 0 := sub_neg.mpr (lt_of_not_ge hnot)
      have hsmall : 0 < min (1 : ℝ) (-A) := lt_min zero_lt_one (neg_pos.mpr hA)
      obtain ⟨ε, hεpos, hεsmall⟩ := exists_pos_mul_lt hsmall (|B| + 1)
      have hε1 : ε ≤ 1 := by
        have hmin := min_le_left (1 : ℝ) (-A)
        nlinarith [mul_nonneg (le_of_lt hεpos) (abs_nonneg B)]
      have hεB : ε * B < -A := by
        have hmin := min_le_right (1 : ℝ) (-A)
        nlinarith [mul_nonneg (le_of_lt hεpos) (sub_nonneg.mpr (le_abs_self B))]
      have hnegative : 2 * A + ε * B < 0 := by linarith
      have hprod := mul_neg_of_pos_of_neg hεpos hnegative
      have hnonnegative : 0 ≤ 2 * ε * A + ε ^ 2 * B := hquad ε hεpos hε1
      nlinarith
    intro a
    refine ⟨hrow_ge a, ?_⟩
    intro ha
    have hsum : (∑ b : Sector,
        p b * (row b - spectralGramEnergy spectrum p)) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib]
      rw [hweighted, ← Finset.sum_mul, hp.2]
      ring
    have hterm (b : Sector) : 0 ≤
        p b * (row b - spectralGramEnergy spectrum p) :=
      mul_nonneg (hp.1 b) (sub_nonneg.mpr (hrow_ge b))
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b _ => hterm b)).mp hsum a (Finset.mem_univ a)
    have hdiff : row a - spectralGramEnergy spectrum p = 0 :=
      (mul_eq_zero.mp hz).resolve_left (ne_of_gt ha)
    change spectralGramEnergy spectrum p = row a
    linarith
  refine ⟨hvariance, p, hp, s, t, hpmax, hdiam', hlower, hupper, hzero, ?_, ?_⟩
  · exact hnecessary p hp hqmin
  · intro r hr
    constructor
    · exact hnecessary r hr
    intro hcert u hu
    let rowR : Sector → ℝ := fun a =>
      ∑ b : Sector, r b * bhattacharyya (spectrum a) (spectrum b)
    have hweightedR : (∑ a : Sector, r a * rowR a) =
        spectralGramEnergy spectrum r := by
      unfold spectralGramEnergy
      apply Finset.sum_congr rfl
      intro a _
      dsimp [rowR]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    have hlinear : 0 ≤ ∑ a : Sector, (u a - r a) * rowR a := by
      have hsum : (∑ a : Sector, u a * rowR a) ≥
          spectralGramEnergy spectrum r := by
        calc
          (∑ a : Sector, u a * rowR a) ≥
              ∑ a : Sector, u a * spectralGramEnergy spectrum r := by
            apply Finset.sum_le_sum
            intro a _
            exact mul_le_mul_of_nonneg_left (hcert a).1 (hu.1 a)
          _ = spectralGramEnergy spectrum r := by
            rw [← Finset.sum_mul, hu.2, one_mul]
      simp_rw [sub_mul, Finset.sum_sub_distrib, hweightedR]
      linarith
    have hexp := gram_energy_expansion spectrum r u
    change spectralGramEnergy spectrum u = spectralGramEnergy spectrum r +
      2 * (∑ a : Sector, (u a - r a) * rowR a) +
      spectralGramEnergy spectrum (fun a => u a - r a) at hexp
    have hpsd := gram_energy_nonneg spectrum hnonneg (fun a => u a - r a)
    linarith

#print axioms finite_spectral_family_geometry

end

end D5.S3.Quantum.Entanglement.SpectralFamilyGeometry
