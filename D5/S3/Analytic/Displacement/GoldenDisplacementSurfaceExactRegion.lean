/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementSurfaceExactRegion
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves the exact region for all real parameters; no sign case remains open. -/

import D5.S1.Deficit.Displacement.GoldenSubstStartSharpness
import D5.S3.Analytic.Displacement.GoldenDisplacementSurfaceRegion

open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDisplacementEulerProduct
open GoldenDisplacementFaceHeatAbscissa
open GoldenDisplacementSurfaceRegion
open GoldenSubstStartSharpness

namespace GoldenDisplacementSurfaceExactRegion

noncomputable section

private theorem dTerm_summable_iff_of_neg {s w : ℝ} (hs : s < 0) :
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
      by_contra hnot
      have hcle : s * Real.goldenRatio + w ≤ 0 := le_of_not_gt hnot
      obtain ⟨v, hv⟩ := golden_subst_start_error_upper_sharp
        Real.goldenRatio⁻¹ (inv_pos.mpr Real.goldenRatio_pos)
      have herr : 0 <
          (goldenSubstStart v : ℝ) - Real.goldenRatio * (v : ℝ) := by
        linarith
      cases v with
      | zero => simp [goldenSubstStart_zero] at herr
      | succ k =>
          have hscaled :
              (s * Real.goldenRatio + w) * ((k + 1 : ℕ) : ℝ) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hcle (by positivity)
          have herror : s *
              ((goldenSubstStart (k + 1) : ℝ) -
                Real.goldenRatio * ((k + 1 : ℕ) : ℝ)) < 0 :=
            mul_neg_of_neg_of_pos hs herr
          have hexponent := hexact k
          norm_num [Nat.cast_add, Nat.cast_one] at hscaled herror hexponent
          nlinarith
    let c : ℝ := s * Real.goldenRatio + w
    obtain ⟨N, hN⟩ := exists_nat_gt
      ((1 - s * Real.goldenRatio⁻¹) / c)
    have hscaled :
        1 - s * Real.goldenRatio⁻¹ < (N : ℝ) * c :=
      (div_lt_iff₀ hc).mp hN
    let A : ℝ := c * ((N : ℝ) + 1) + s * Real.goldenRatio⁻¹
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
      have hlinear := (golden_subst_start_error_window (k + N + 1)).2
      have hmul := mul_le_mul_of_nonpos_left hlinear hs.le
      dsimp [A, c]
      norm_num [Nat.cast_add, Nat.cast_one] at hmul ⊢
      nlinarith
    have hterm (k : ℕ) (p : Nat.Primes) :
        (p : ℝ) ^ (-(s * (goldenSubstStart (k + N + 1) : ℝ) +
          w * (k + N + 1))) ≤ (p : ℝ) ^ r * q ^ k := by
      have hp_one : 1 ≤ (p : ℝ) := by exact_mod_cast p.prop.one_lt.le
      have hp_two : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
      have hp_pos : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
      have hk : 0 ≤ (k : ℝ) := by positivity
      calc
        (p : ℝ) ^ (-(s * (goldenSubstStart (k + N + 1) : ℝ) +
            w * (k + N + 1))) ≤ (p : ℝ) ^ (-(A + c * (k : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_le hp_one (by linarith [hexponent k])
        _ = (p : ℝ) ^ r * (p : ℝ) ^ (-c * (k : ℝ)) := by
          rw [← Real.rpow_add hp_pos]
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

/-- Exact convergence region of the golden displacement surface for all real parameters. -/
theorem dTerm_summable_iff (s w : ℝ) :
    Summable (dTerm s w) ↔
      ∀ k, 1 < s * (goldenSubstStart (k + 1) : ℝ) + w * (k + 1) := by
  by_cases hs : 0 ≤ s
  · exact GoldenDisplacementSurfaceRegion.dTerm_summable_iff hs
  · exact dTerm_summable_iff_of_neg (lt_of_not_ge hs)

end

end GoldenDisplacementSurfaceExactRegion
