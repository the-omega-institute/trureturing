/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion
   generality: I
   mirror-B: D5/B/S3/Analytic/Displacement/GoldenDisplacementSurfaceRegion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Determines the exact convergence region of the golden displacement surface. -/

import D5.S3.Analytic.Displacement.GoldenDisplacementFaceHeatAbscissa

/- Provenance: Native proof over pinned mathlib, reusing the frozen nonnegative Euler bridge.
   Search receipt (2026-08-14): searched D5 and pinned Mathlib for the displacement
   prime-power API, `Nat.Primes.summable_rpow`, product summability, geometric majorants,
   and shifted summability; all cited declarations were hits, while the exact region was a miss. -/

open D5.S3.Analytic.GoldenEulerBeta
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDisplacementComplexEulerProduct
open GoldenDisplacementEulerProduct
open GoldenDisplacementFaceHeatAbscissa
open GoldenSubstitutionOrbit

namespace GoldenDisplacementSurfaceRegion

noncomputable section

private theorem goldenRatio_gt_three_halves : (3 : ℝ) / 2 < Real.goldenRatio := by
  nlinarith [Real.goldenRatio_sq, Real.one_lt_goldenRatio,
    Real.goldenRatio_lt_two]

private theorem prime_real_pos (p : Nat.Primes) : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos

/-- The substitution start has the linear lower bound inherited from the golden
Euler exponent account. -/
theorem goldenSubstStart_linear_lower_bound (v : ℕ) :
    Real.goldenRatio * v + Real.goldenRatio - 2 ≤ (goldenSubstStart v : ℝ) := by
  have hgrowth := o5_beta_growth v
  rw [o5_beta_eq_substitution_start_sub_conjugate, one_div,
    Real.inv_goldenRatio] at hgrowth
  have hv : 0 ≤ (v : ℝ) := by positivity
  nlinarith [Real.goldenRatio_sub_goldenConj, Real.one_sub_goldenConj,
    Real.goldenConj_neg]

/-- A prime-power displacement coefficient is one real power of its prime. -/
theorem dTerm_prime_pow_rpow {s w : ℝ} {p : ℕ} (hp : p.Prime) (e : ℕ) :
    dTerm s w (p ^ e) =
      (p : ℝ) ^ (-(s * goldenSubstStart e + w * e)) := by
  have hp0 : (0 : ℝ) ≤ p := by exact_mod_cast hp.pos.le
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [dTerm_prime_pow hp e, ← Real.rpow_mul_natCast hp0,
    ← Real.rpow_mul_natCast hp0, ← Real.rpow_add hppos]
  congr 1
  ring

/-- Exact convergence region of the nonnegative displacement surface. -/
theorem dTerm_summable_iff {s w : ℝ} (hs : 0 ≤ s) :
    Summable (dTerm s w) ↔
      ∀ k, 1 < s * (goldenSubstStart (k + 1) : ℝ) + w * (k + 1) := by
  constructor
  · intro hsum k
    have hslice : Summable (fun p : Nat.Primes =>
        dTerm s w ((p : ℕ) ^ (k + 1))) := by
      apply hsum.comp_injective
      intro p q hpq
      apply Subtype.ext
      exact Nat.pow_left_injective (Nat.succ_ne_zero k) hpq
    have hrpow : Summable (fun p : Nat.Primes =>
        (p : ℝ) ^ (-(s * (goldenSubstStart (k + 1) : ℝ) +
          w * (k + 1)))) := by
      refine hslice.congr fun p => ?_
      simpa only [Nat.cast_add, Nat.cast_one] using
        dTerm_prime_pow_rpow (s := s) (w := w) p.prop (k + 1)
    have hexponent := Nat.Primes.summable_rpow.mp hrpow
    linarith
  · intro hexact
    have hc : 0 < s * Real.goldenRatio + w := by
      have htwo := hexact 1
      have hstart : goldenSubstStart 2 = 3 := by decide
      norm_num [hstart] at htwo
      nlinarith [goldenRatio_gt_three_halves]
    let c : ℝ := s * Real.goldenRatio + w
    obtain ⟨N, hN⟩ := exists_nat_gt
      ((1 + s * (2 - Real.goldenRatio)) / c)
    have hscaled :
        1 + s * (2 - Real.goldenRatio) < (N : ℝ) * c :=
      (div_lt_iff₀ hc).mp hN
    let A : ℝ := c * ((N : ℝ) + 1) - s * (2 - Real.goldenRatio)
    have hA : 1 < A := by
      dsimp [A]
      nlinarith
    let r : ℝ := -A
    let q : ℝ := (2 : ℝ) ^ (-c)
    have hr : r < -1 := by dsimp [r]; linarith
    have hq_nonneg : 0 ≤ q := by dsimp [q]; positivity
    have hq_lt_one : q < 1 := by
      exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have hbase : Summable (fun p : Nat.Primes => (p : ℝ) ^ r) :=
      Nat.Primes.summable_rpow.mpr hr
    have hslice (k : ℕ) : Summable (fun p : Nat.Primes =>
        (p : ℝ) ^ (-(s * (goldenSubstStart (k + 1) : ℝ) +
          w * (k + 1)))) := by
      apply Nat.Primes.summable_rpow.mpr
      linarith [hexact k]
    have hexponent (k : ℕ) :
        A + c * (k : ℝ) ≤
          s * (goldenSubstStart (k + N + 1) : ℝ) + w * (k + N + 1) := by
      have hlinear := goldenSubstStart_linear_lower_bound (k + N + 1)
      have hmul := mul_le_mul_of_nonneg_left hlinear hs
      dsimp [A, c]
      norm_num [Nat.cast_add, Nat.cast_one] at hmul ⊢
      nlinarith
    have hterm (k : ℕ) (p : Nat.Primes) :
        (p : ℝ) ^ (-(s * (goldenSubstStart (k + N + 1) : ℝ) +
          w * (k + N + 1))) ≤ (p : ℝ) ^ r * q ^ k := by
      have hp_one : 1 ≤ (p : ℝ) := by exact_mod_cast p.prop.one_lt.le
      have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
      have hk : 0 ≤ (k : ℝ) := by positivity
      calc
        (p : ℝ) ^ (-(s * (goldenSubstStart (k + N + 1) : ℝ) +
            w * (k + N + 1))) ≤ (p : ℝ) ^ (-(A + c * (k : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le hp_one (by linarith [hexponent k])
        _ = (p : ℝ) ^ r * (p : ℝ) ^ (-c * (k : ℝ)) := by
          rw [← Real.rpow_add (prime_real_pos p)]
          dsimp [r]
          congr 1
          ring
        _ ≤ (p : ℝ) ^ r * (2 : ℝ) ^ (-c * (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos (z := -c * (k : ℝ))
              (by norm_num) hp_two
              (mul_nonpos_of_nonpos_of_nonneg (by linarith) hk)) (by positivity)
        _ = (p : ℝ) ^ r * q ^ k := by
          dsimp [q]
          rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    have htsum (k : ℕ) :
        (∑' p : Nat.Primes,
          (p : ℝ) ^ (-(s * (goldenSubstStart (k + N + 1) : ℝ) +
            w * (k + N + 1)))) ≤
          (∑' p : Nat.Primes, (p : ℝ) ^ r) * q ^ k := by
      have hsliceTail : Summable (fun p : Nat.Primes =>
          (p : ℝ) ^ (-(s * (goldenSubstStart (k + N + 1) : ℝ) +
            w * (k + N + 1)))) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hslice (k + N)
      calc
        (∑' p : Nat.Primes,
            (p : ℝ) ^ (-(s * (goldenSubstStart (k + N + 1) : ℝ) +
              w * (k + N + 1)))) ≤
            ∑' p : Nat.Primes, (p : ℝ) ^ r * q ^ k :=
          hsliceTail.tsum_le_tsum (hterm k) (hbase.mul_right (q ^ k))
        _ = (∑' p : Nat.Primes, (p : ℝ) ^ r) * q ^ k := tsum_mul_right
    have houterTail : Summable (fun k : ℕ =>
        ∑' p : Nat.Primes,
          (p : ℝ) ^ (-(s * (goldenSubstStart (k + N + 1) : ℝ) +
            w * (k + N + 1)))) :=
      ((summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left
        (∑' p : Nat.Primes, (p : ℝ) ^ r)).of_nonneg_of_le
          (fun _ => by positivity) htsum
    have houter : Summable (fun k : ℕ =>
        ∑' p : Nat.Primes,
          (p : ℝ) ^ (-(s * (goldenSubstStart (k + 1) : ℝ) +
            w * (k + 1)))) := by
      apply (summable_nat_add_iff (f := fun k : ℕ =>
        ∑' p : Nat.Primes,
          (p : ℝ) ^ (-(s * (goldenSubstStart (k + 1) : ℝ) +
            w * (k + 1)))) N).mp
      simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using houterTail
    have hswapped : Summable (fun kp : ℕ × Nat.Primes =>
        (kp.2 : ℝ) ^ (-(s * (goldenSubstStart (kp.1 + 1) : ℝ) +
          w * (kp.1 + 1)))) :=
      (summable_prod_of_nonneg (fun _ => by positivity)).mpr ⟨hslice, houter⟩
    have hprimePowers : Summable (fun pk : Nat.Primes × ℕ =>
        (pk.1 : ℝ) ^ (-(s * (goldenSubstStart (pk.2 + 1) : ℝ) +
          w * (pk.2 + 1)))) :=
      (Equiv.prodComm Nat.Primes ℕ).summable_iff.mpr hswapped
    have hlocal : Summable (fun pk : Nat.Primes × ℕ =>
        dTerm s w ((pk.1 : ℕ) ^ (pk.2 + 1))) := by
      refine hprimePowers.congr fun pk => ?_
      simpa only [Nat.cast_add, Nat.cast_one] using
        (dTerm_prime_pow_rpow (s := s) (w := w) pk.1.prop (pk.2 + 1)).symm
    exact summable_of_summable_prime_power_tail (dTerm s w)
      (dTerm_zero s w) (dTerm_one s w) (dTerm_nonneg s w)
      (fun h => dTerm_mul_of_coprime h) hlocal

/-- On the hidden-product axis the exact threshold is `s = 1/2`. -/
theorem nS_dirichlet_summable_iff {s : ℝ} :
    Summable (dTerm s 0) ↔ 1 / 2 < s := by
  constructor
  · intro hsum
    have hslice : Summable (fun p : Nat.Primes => dTerm s 0 (p : ℕ)) := by
      apply hsum.comp_injective
      intro p q hpq
      exact Subtype.ext hpq
    have hstart : goldenSubstStart 1 = 2 := by decide
    have hrpow : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-(2 * s))) := by
      refine hslice.congr fun p => ?_
      rw [← pow_one (p : ℕ)]
      rw [dTerm_prime_pow_rpow p.prop 1, hstart]
      norm_num
      congr 1
      ring
    have := Nat.Primes.summable_rpow.mp hrpow
    linarith
  · intro hs
    have hs0 : 0 ≤ s := by linarith
    apply (dTerm_summable_iff (s := s) (w := 0) hs0).mpr
    intro k
    have hstartOne : goldenSubstStart 1 = 2 := by decide
    have hstart : 2 ≤ goldenSubstStart (k + 1) := by
      rw [← hstartOne]
      exact goldenSubstStart_mono (by omega)
    have hstartReal : (2 : ℝ) ≤ goldenSubstStart (k + 1) := by
      exact_mod_cast hstart
    have hmul := mul_le_mul_of_nonneg_left hstartReal hs0
    norm_num
    nlinarith

/-- The former half-plane is contained in the exact convergence region. -/
theorem exponent_gt_one_of_half_plane {s w : ℝ} (hs : 0 ≤ s)
    (hsw : 1 < s + w) (k : ℕ) :
    1 < s * goldenSubstStart (k + 1) + w * (k + 1) := by
  have hstart := self_le_goldenSubstStart (k + 1)
  have hstartReal : ((k + 1 : ℕ) : ℝ) ≤ goldenSubstStart (k + 1) := by
    exact_mod_cast hstart
  have hmul := mul_le_mul_of_nonneg_left hstartReal hs
  have hk : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_pos k
  have hsw0 : 0 ≤ s + w := hsw.le.trans' (by norm_num)
  have hscale := mul_le_mul_of_nonneg_left hk hsw0
  norm_num at hscale
  push_cast at hmul ⊢
  nlinarith

/-- A convergent point strictly outside the former sufficient half-plane. -/
theorem summable_dTerm_outside_half_plane :
    Summable (dTerm 1 (-(1 / 2))) := by
  apply (dTerm_summable_iff (s := 1) (w := -(1 / 2)) (by norm_num)).mpr
  intro k
  cases k with
  | zero =>
      norm_num [show goldenSubstStart 1 = 2 by decide]
  | succ k =>
      have hlinear := goldenSubstStart_linear_lower_bound (Nat.succ k + 1)
      have hk : 0 ≤ (k : ℝ) := by positivity
      norm_num [Nat.cast_add, Nat.cast_succ] at hlinear ⊢
      nlinarith [goldenRatio_gt_three_halves]

example : Summable (dTerm 1 (-(1 / 2))) := summable_dTerm_outside_half_plane

end

end GoldenDisplacementSurfaceRegion
