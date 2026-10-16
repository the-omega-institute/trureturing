/- GID: D5/S3/Analytic/EulerGerm/GoldenCandidateOrbit
   generality: I
   mirror-B: D5/B/S3/Analytic/EulerGerm/GoldenCandidateOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Classify all prime channels of the logarithmically scaled golden candidate. -/

import D5.S3.Analytic.EulerGerm.LocalFactorUniversalScaling
import D5.S3.Analytic.GermWindow.GermZeroCertificateReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.EulerGerm.GoldenCandidateOrbit

open D5.S3.Analytic.GermWindow.GermZeroCertificateReduction

noncomputable section

/-- The real scale taking a prime-local germ back to the prime-two observer. -/
def goldenCandidateOrbitScale (p : Nat.Primes) : ℝ :=
  Real.log 2 / Real.log (p : ℝ)

/-- The real part of the prime-local candidate obtained from the certified
prime-two candidate by universal logarithmic scaling. -/
def goldenCandidateOrbit (p : Nat.Primes) : ℝ :=
  goldenCandidateOrbitScale p * c.re

private theorem orbit_log_two_pos : 0 < Real.log (2 : ℝ) :=
  Real.log_pos (by norm_num)

private theorem orbit_log_prime_pos (p : Nat.Primes) :
    0 < Real.log (p : ℝ) :=
  Real.log_pos (by exact_mod_cast p.prop.one_lt)

private theorem goldenRatio_gt_1618 :
    (1618 : ℝ) / 1000 < Real.goldenRatio := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem two_phi_cube_mul_candidate_gt_two :
    2 < 2 * Real.goldenRatio ^ 3 * c.re := by
  have hc : (238 : ℝ) / 1000 < c.re := by norm_num [c]
  have hphi : (1618 : ℝ) / 1000 < Real.goldenRatio :=
    goldenRatio_gt_1618
  have hcube :
      2 * (1618 / 1000 : ℝ) + 1 < Real.goldenRatio ^ 3 := by
    nlinarith [Real.goldenRatio_sq]
  nlinarith

private theorem goldenRatio_lt_13_eighths :
    Real.goldenRatio < (13 : ℝ) / 8 := by
  rw [Real.goldenRatio]
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith

private theorem two_phi_cube_mul_candidate_lt_nine_fourths :
    2 * Real.goldenRatio ^ 3 * c.re < (9 : ℝ) / 4 := by
  have hcpos : 0 < c.re := by norm_num [c]
  have hc : c.re < (1 : ℝ) / 4 := by norm_num [c]
  have hphi : Real.goldenRatio < (13 : ℝ) / 8 :=
    goldenRatio_lt_13_eighths
  have hcube : Real.goldenRatio ^ 3 < (17 : ℝ) / 4 := by
    nlinarith [Real.goldenRatio_sq]
  have hmul : Real.goldenRatio ^ 3 * c.re <
      (17 : ℝ) / 4 * c.re := by
    exact mul_lt_mul_of_pos_right hcube hcpos
  have hmul' : (17 : ℝ) / 4 * c.re < (17 : ℝ) / 16 := by
    nlinarith
  nlinarith

private theorem log_three_lt_two_log_two :
    Real.log (3 : ℝ) < 2 * Real.log 2 := by
  have h := Real.strictMonoOn_log (show (0 : ℝ) < 3 by norm_num)
    (show (0 : ℝ) < 4 by norm_num) (by norm_num : (3 : ℝ) < 4)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    calc
      Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  rw [hlog4] at h
  exact h

private theorem log_five_gt_nine_fourths_log_two :
    (9 : ℝ) / 4 * Real.log 2 < Real.log (5 : ℝ) := by
  have hpow : (2 : ℝ) ^ 9 < (5 : ℝ) ^ 4 := by norm_num
  have hlog := Real.strictMonoOn_log (show (0 : ℝ) < 2 ^ 9 by positivity)
    (show (0 : ℝ) < 5 ^ 4 by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog ⊢
  linarith

theorem gc_orbit_two_prime_straddle :
    1 / (2 * Real.goldenRatio ^ 3) <
        goldenCandidateOrbit ⟨3, Nat.prime_three⟩ ∧
      goldenCandidateOrbit ⟨3, Nat.prime_three⟩ <
        1 / Real.goldenRatio ^ 2 ∧
      goldenCandidateOrbit ⟨5, by norm_num⟩ <
        1 / (2 * Real.goldenRatio ^ 3) := by
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog2lt3 : Real.log 2 < Real.log (3 : ℝ) :=
    Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
  have hratio3 : Real.log 2 / Real.log 3 < 1 := by
    rw [div_lt_iff₀ hlog3]
    linarith
  have hprod3 :
      1 < (Real.log 2 / Real.log 3) *
        (2 * Real.goldenRatio ^ 3 * c.re) := by
    have hlog3' : Real.log 3 <
        Real.log 2 * (2 * Real.goldenRatio ^ 3 * c.re) := by
      nlinarith [log_three_lt_two_log_two,
        orbit_log_two_pos, two_phi_cube_mul_candidate_gt_two]
    rw [div_mul_eq_mul_div]
    apply (lt_div_iff₀ hlog3).2
    simpa only [one_mul] using hlog3'
  have hlow3 :
      1 / (2 * Real.goldenRatio ^ 3) <
        goldenCandidateOrbit ⟨3, Nat.prime_three⟩ := by
    unfold goldenCandidateOrbit goldenCandidateOrbitScale
    change 1 / (2 * Real.goldenRatio ^ 3) <
      (Real.log 2 / Real.log 3) * c.re
    apply (div_lt_iff₀
      (by positivity : (0 : ℝ) < 2 * Real.goldenRatio ^ 3)).2
    calc
      (1 : ℝ) < (Real.log 2 / Real.log 3) *
          (2 * Real.goldenRatio ^ 3 * c.re) := hprod3
      _ = (Real.log 2 / Real.log 3 * c.re) *
          (2 * Real.goldenRatio ^ 3) := by ring
  have hupp3 :
      goldenCandidateOrbit ⟨3, Nat.prime_three⟩ <
        1 / Real.goldenRatio ^ 2 := by
    unfold goldenCandidateOrbit goldenCandidateOrbitScale
    have hc := c_in_golden_window.2
    have hcpos : 0 < c.re := by norm_num [c]
    calc
      Real.log 2 / Real.log 3 * c.re < 1 * c.re :=
        mul_lt_mul_of_pos_right hratio3 hcpos
      _ < 1 / Real.goldenRatio ^ 2 := by simpa only [one_mul] using hc
  have hlog5 : (9 : ℝ) / 4 * Real.log 2 < Real.log 5 :=
    log_five_gt_nine_fourths_log_two
  have hratio5 :
      (Real.log 2 / Real.log 5) *
        (2 * Real.goldenRatio ^ 3 * c.re) < 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (Real.log_pos (by norm_num))).2
    nlinarith [hlog5, two_phi_cube_mul_candidate_lt_nine_fourths,
      orbit_log_two_pos]
  have hlow5 :
      goldenCandidateOrbit ⟨5, by norm_num⟩ <
        1 / (2 * Real.goldenRatio ^ 3) := by
    unfold goldenCandidateOrbit goldenCandidateOrbitScale
    change (Real.log 2 / Real.log 5) * c.re <
      1 / (2 * Real.goldenRatio ^ 3)
    apply (lt_div_iff₀
      (by positivity : (0 : ℝ) < 2 * Real.goldenRatio ^ 3)).2
    have htarget :
        (Real.log 2 / Real.log 5 * c.re) *
            (2 * Real.goldenRatio ^ 3) < 1 := by
      calc
        (Real.log 2 / Real.log 5 * c.re) *
            (2 * Real.goldenRatio ^ 3) =
            (Real.log 2 / Real.log 5) *
              (2 * Real.goldenRatio ^ 3 * c.re) := by ring
        _ < 1 := hratio5
    exact htarget
  exact ⟨hlow3, hupp3, hlow5⟩

private theorem goldenCandidateOrbit_prime_ge_five_below
    (p : Nat.Primes) (hp : 5 ≤ p.1) :
    goldenCandidateOrbit p < 1 / (2 * Real.goldenRatio ^ 3) := by
  have hlogp : 0 < Real.log (p : ℝ) := orbit_log_prime_pos p
  have hlog5lep : Real.log (5 : ℝ) ≤ Real.log (p : ℝ) := by
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hp)
  have hratio :
      (Real.log 2 / Real.log (p : ℝ)) *
        (2 * Real.goldenRatio ^ 3 * c.re) < 1 := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hlogp).2
    nlinarith [log_five_gt_nine_fourths_log_two,
      two_phi_cube_mul_candidate_lt_nine_fourths,
      orbit_log_two_pos]
  unfold goldenCandidateOrbit goldenCandidateOrbitScale
  change (Real.log 2 / Real.log (p.1 : ℝ)) * c.re <
    1 / (2 * Real.goldenRatio ^ 3)
  apply (lt_div_iff₀
    (by positivity : (0 : ℝ) < 2 * Real.goldenRatio ^ 3)).2
  calc
    (Real.log 2 / Real.log (p.1 : ℝ) * c.re) *
        (2 * Real.goldenRatio ^ 3) < 1 := by
      calc
        (Real.log 2 / Real.log (p.1 : ℝ) * c.re) *
            (2 * Real.goldenRatio ^ 3) =
            (Real.log 2 / Real.log (p.1 : ℝ)) *
              (2 * Real.goldenRatio ^ 3 * c.re) := by ring
        _ < 1 := hratio

theorem scaled_gc_orbit_window_iff (p : Nat.Primes) :
    (1 / (2 * Real.goldenRatio ^ 3) < goldenCandidateOrbit p ∧
      goldenCandidateOrbit p < 1 / Real.goldenRatio ^ 2) ↔
      p.1 = 2 ∨ p.1 = 3 := by
  constructor
  · intro h
    by_contra hnot
    have hp2 : p.1 ≠ 2 := by
      intro hp
      exact hnot (Or.inl hp)
    have hp3 : p.1 ≠ 3 := by
      intro hp
      exact hnot (Or.inr hp)
    have hp5 : 5 ≤ p.1 := by
      by_contra hlt
      have hp2le : 2 ≤ p.1 := p.prop.two_le
      have hp4 : p.1 ≤ 4 := by omega
      have hcases : p.1 = 2 ∨ p.1 = 3 ∨ p.1 = 4 := by omega
      rcases hcases with h2 | h3 | h4
      · exact hp2 h2
      · exact hp3 h3
      · have hnotprime : ¬ Nat.Prime 4 := by norm_num
        exact hnotprime (h4 ▸ p.prop)
    have hb := goldenCandidateOrbit_prime_ge_five_below p hp5
    exact lt_irrefl _ (h.1.trans hb)
  · intro h
    rcases h with hp | hp
    · have heq : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp
      subst p
      unfold goldenCandidateOrbit goldenCandidateOrbitScale
      have hlog : Real.log (2 : ℝ) ≠ 0 := orbit_log_two_pos.ne'
      simpa [hlog] using c_in_golden_window
    · have heq : p = ⟨3, Nat.prime_three⟩ := Subtype.ext hp
      subst p
      exact ⟨(gc_orbit_two_prime_straddle).1, (gc_orbit_two_prime_straddle).2.1⟩


#print axioms gc_orbit_two_prime_straddle
#print axioms scaled_gc_orbit_window_iff

end
end D5.S3.Analytic.EulerGerm.GoldenCandidateOrbit
