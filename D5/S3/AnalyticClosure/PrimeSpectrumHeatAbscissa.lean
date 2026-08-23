/- GID: D5/S3/AnalyticClosure/PrimeSpectrumHeatAbscissa
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Linear growth of prime-spectrum exponents fixes the heat abscissa. -/

import Mathlib
import D5.S3.Midline.UniversalHeatTrace

/- Provenance: Native proof over pinned mathlib. -/

/- Search receipt (2026-08-21).

   Candidates searched and inspected:
   * Every Lean file in `D5/S3/AnalyticClosure` and `D5/S3/Midline`, plus
     `D5/S3/Midline/HeatLayers/GoldenHeatLayers.lean` and every Lean file in
     `D5/S3/Analytic/Displacement`.
   * The pinned files `Mathlib/NumberTheory/SumPrimeReciprocals.lean`,
     `Mathlib/Topology/Algebra/InfiniteSum/Real.lean`,
     `Mathlib/Topology/Algebra/InfiniteSum/Ring.lean`, and
     `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` were inspected for an
     existing criterion in equivalent or `iff` form.
   * SL-028 self-checks covered `IsHeatAbscissa`, prime-by-natural product
     summability, reciprocal abscissae, and the declaration-name fragments
     `PrimeSpectrumHeatAbscissa` and `prime_spectrum_heat_abscissa`. No general
     statement equivalent to the theorem below was found.

   Load-bearing declarations:
   * `D5.S3.Midline.UniversalHeatTrace.IsHeatAbscissa` supplies the conclusion's
     two strict-side obligations.
   * `Nat.Primes.summable_rpow` supplies both the convergent prime slices and
     the divergent ground-layer obstruction.
   * `Real.rpow_def_of_pos`, `Real.rpow_le_rpow_of_exponent_le`,
     `Real.rpow_le_rpow_of_nonpos`, and `Real.rpow_mul_natCast` convert the heat
     terms and establish their geometric majorant.
   * `summable_prod_of_nonneg`, `summable_geometric_of_lt_one`,
     `Summable.tsum_le_tsum`, `tsum_mul_right`, and
     `Equiv.prodComm.summable_iff` assemble the double series.
   * `div_lt_iff₀` and `lt_div_iff₀` (`Mathlib/Algebra/Order/GroupWithZero/
     Basic.lean`, lines 1146 and 1142) carry the two threshold comparisons that
     are the content of the abscissa claim: `1 < s * b0` on the summable side
     and `s * b0 < 1` on the divergent side.
   * `Real.rpow_add` (`Pow/Real.lean:207`) splits the majorant into its prime
     and geometric factors, `Real.rpow_lt_one_of_one_lt_of_neg`
     (`Pow/Real.lean:662`) supplies the ratio below one, and
     `Summable.prod_factor` (`Topology/Algebra/InfiniteSum/Constructions.lean:230`,
     reached by `to_additive` from `Multipliable.prod_factor`) extracts the
     ground-layer slice used in the divergent direction.

   Near-neighbours deliberately not imported:
   * `D5/S3/Midline/GoldenHeatSpectrum.lean:148` proves only the `o5Beta`
     instance. Importing that `I`-tagged module would make this parameterized
     result depend on one instance family; the proof instead imports only the
     `G`-tagged definition module.
   * `D5/S3/Midline/HeatLayers/GoldenHeatLayers.lean:94` proves a boundary-
     divergent theorem for each golden layer, not for a prime-by-natural
     spectrum under an abstract growth hypothesis.
   * `D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatAbscissa.lean:118`
     derives a golden face-length instance from the golden spectrum.

   Openness provenance: repository-wide D5 searches found zero occurrences of
   `metallicBeta`, `metallicSpectrum`, `metallic_power_law`, and `metallic_heat`.
   Thus no non-golden metallic instance can currently state the needed
   spectrum theorem, while the parameterized result below supplies that base.

   Why this is stated in general form: the argument below never consults the
   value of `beta` beyond the two hypotheses, so stating it for an arbitrary
   `beta` costs nothing over stating it for any one spectrum. The natural-
   generality rule recorded in the repository specification's generality-tag
   definition requires that a result which generalizes at no cost be stated in
   general form, so the near-identical shape of this argument and the frozen
   golden-instance argument is compliance with that rule rather than a
   duplicated proof. The general statement is in any case not derivable from
   the instance, since an arbitrary `beta` cannot be obtained from a fixed one.

   The inspected-candidate and load-bearing lists are separate and are not
   claimed exhaustive. -/

namespace D5.S3.AnalyticClosure.PrimeSpectrumHeatAbscissa

open D5.S3.Midline.UniversalHeatTrace

noncomputable section

private theorem prime_real_pos (p : Nat.Primes) : 0 < (p : Real) := by
  exact_mod_cast p.prop.pos

private theorem exp_neg_prime_spectrum (beta : Nat → Real) (s : Real)
    (pk : Nat.Primes × Nat) :
    Real.exp (-s * (beta (pk.2 + 1) * Real.log (pk.1 : Real))) =
      (pk.1 : Real) ^ (-s * beta (pk.2 + 1)) := by
  rw [Real.rpow_def_of_pos (prime_real_pos pk.1)]
  congr 1
  ring

private theorem critical_mul_lt {b0 s : Real} (h0 : 0 < b0)
    (hs : 1 / b0 < s) : 1 < s * b0 := by
  exact (div_lt_iff₀ h0).mp (by simpa [div_eq_mul_inv] using hs)

private theorem summable_prime_spectrum_rpow (beta : Nat → Real) (b0 s : Real)
    (h0 : 0 < b0)
    (h2 : ∀ k : Nat, b0 + (k : Real) ≤ beta (k + 1))
    (hs : 1 / b0 < s) :
    Summable (fun pk : Nat.Primes × Nat =>
      (pk.1 : Real) ^ (-s * beta (pk.2 + 1))) := by
  have hcritical : 1 < s * b0 := critical_mul_lt h0 hs
  have hspos : 0 < s := by
    have habscissa : 0 < 1 / b0 := by positivity
    linarith
  let r : Real := -s * b0
  let q : Real := (2 : Real) ^ (-s)
  have hr : r < -1 := by
    dsimp [r]
    linarith
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq_lt_one : q < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbase : Summable (fun p : Nat.Primes => (p : Real) ^ r) :=
    Nat.Primes.summable_rpow.mpr hr
  have hslice (k : Nat) :
      Summable (fun p : Nat.Primes =>
        (p : Real) ^ (-s * beta (k + 1))) := by
    apply Nat.Primes.summable_rpow.mpr
    have hbeta := h2 k
    have hk : 0 ≤ (k : Real) := by positivity
    nlinarith
  have hterm (k : Nat) (p : Nat.Primes) :
      (p : Real) ^ (-s * beta (k + 1)) ≤
        (p : Real) ^ r * q ^ k := by
    have hp_one : 1 ≤ (p : Real) := by
      exact_mod_cast p.prop.one_lt.le
    have hp_two : (2 : Real) ≤ (p : Real) := by
      exact_mod_cast p.prop.two_le
    have hbeta := h2 k
    have hk : 0 ≤ (k : Real) := by positivity
    calc
      (p : Real) ^ (-s * beta (k + 1)) ≤
          (p : Real) ^ (-s * (b0 + (k : Real))) :=
        Real.rpow_le_rpow_of_exponent_le hp_one (by nlinarith)
      _ = (p : Real) ^ r * (p : Real) ^ (-s * (k : Real)) := by
        rw [← Real.rpow_add (prime_real_pos p)]
        dsimp [r]
        congr 1
        ring
      _ ≤ (p : Real) ^ r * (2 : Real) ^ (-s * (k : Real)) := by
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (z := -s * (k : Real))
            (by norm_num) hp_two
            (mul_nonpos_of_nonpos_of_nonneg (by linarith) hk)) (by positivity)
      _ = (p : Real) ^ r * q ^ k := by
        dsimp [q]
        rw [← Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 2)]
  have htsum (k : Nat) :
      (∑' p : Nat.Primes, (p : Real) ^ (-s * beta (k + 1))) ≤
        (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k := by
    calc
      (∑' p : Nat.Primes, (p : Real) ^ (-s * beta (k + 1))) ≤
          ∑' p : Nat.Primes, (p : Real) ^ r * q ^ k :=
        (hslice k).tsum_le_tsum (hterm k) (hbase.mul_right (q ^ k))
      _ = (∑' p : Nat.Primes, (p : Real) ^ r) * q ^ k := tsum_mul_right
  have houter : Summable (fun k : Nat =>
      ∑' p : Nat.Primes, (p : Real) ^ (-s * beta (k + 1))) :=
    ((summable_geometric_of_lt_one hq_nonneg hq_lt_one).mul_left
      (∑' p : Nat.Primes, (p : Real) ^ r)).of_nonneg_of_le
        (fun _ => by positivity) htsum
  have hswapped : Summable (fun kp : Nat × Nat.Primes =>
      (kp.2 : Real) ^ (-s * beta (kp.1 + 1))) :=
    (summable_prod_of_nonneg (fun _ => by positivity)).mpr ⟨hslice, houter⟩
  exact (Equiv.prodComm Nat.Primes Nat).summable_iff.mpr hswapped

/-- A prime-by-natural spectrum whose first exponent is positive and whose
exponents grow at least linearly from it has heat abscissa equal to the
reciprocal of that first exponent. -/
theorem prime_spectrum_heat_abscissa (beta : Nat → Real) (b0 : Real)
    (h0 : 0 < b0) (h1 : beta 1 = b0)
    (h2 : ∀ k : Nat, b0 + (k : Real) ≤ beta (k + 1)) :
    IsHeatAbscissa
      (fun pk : Nat.Primes × Nat =>
        beta (pk.2 + 1) * Real.log (pk.1 : Real))
      (1 / b0) := by
  constructor
  · intro s hs
    simpa only [exp_neg_prime_spectrum] using
      summable_prime_spectrum_rpow beta b0 s h0 h2 hs
  · intro s hs hsum
    have hswapped : Summable (fun kp : Nat × Nat.Primes =>
        Real.exp (-s * (beta (kp.1 + 1) * Real.log (kp.2 : Real)))) :=
      (Equiv.prodComm Nat.Primes Nat).summable_iff.mp hsum
    have hsub : Summable (fun p : Nat.Primes =>
        Real.exp (-s * (beta 1 * Real.log (p : Real)))) :=
      hswapped.prod_factor 0
    have hrpow : Summable (fun p : Nat.Primes =>
        (p : Real) ^ (-s * b0)) := by
      refine hsub.congr fun p => ?_
      rw [Real.rpow_def_of_pos (prime_real_pos p), h1]
      congr 1
      ring
    have hexponent : -s * b0 < -1 := Nat.Primes.summable_rpow.mp hrpow
    have hbelow : s * b0 < 1 :=
      (lt_div_iff₀ h0).mp (by simpa [div_eq_mul_inv] using hs)
    linarith

#print axioms prime_spectrum_heat_abscissa

end

end D5.S3.AnalyticClosure.PrimeSpectrumHeatAbscissa
