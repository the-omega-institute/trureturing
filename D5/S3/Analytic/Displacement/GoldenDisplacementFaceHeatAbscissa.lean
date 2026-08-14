/- GID: D5/S3/Analytic/Displacement/GoldenDisplacementFaceHeatAbscissa
   generality: I
   mirror-B: D5/B/S3/Analytic/Displacement/GoldenDisplacementFaceHeatAbscissa
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Proves the nonnegative Euler summability bridge and exact face heat abscissa. -/

import D5.S3.Analytic.Displacement.GoldenDisplacementFaceHeatTrace
import Mathlib.NumberTheory.EulerProduct.Basic

/- Provenance: Native proof over pinned mathlib. The summability bridge reuses
   `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`,
   `Nat.mem_smoothNumbers_of_lt`, and monotone nonnegative finite sums. The
   golden instance reuses the frozen spectrum abscissa and face divergence.
   Search receipt (2026-08-14): searched D5 and pinned Mathlib for the Euler
   smooth-number API and exact nonnegative summability criteria; all cited
   declarations were direct hits. -/

open D5.S1.Deficit.DoubleFaceLength
open D5.S3.Midline.GoldenHeatSpectrum
open D5.S3.Midline.UniversalHeatTrace
open GoldenDesubstitutionClosedForms
open GoldenDesubstitutionLength
open GoldenDisplacementEulerProduct
open GoldenDisplacementFaceHeatTrace
open GoldenSubstitutionOrbit

namespace GoldenDisplacementFaceHeatAbscissa

noncomputable section

/-- Summability of all positive prime-power tails implies global summability for a
nonnegative real multiplicative function. -/
theorem summable_of_summable_prime_power_tail (f : ℕ → ℝ)
    (hf_zero : f 0 = 0) (hf_one : f 1 = 1) (hf_nonneg : ∀ n, 0 ≤ f n)
    (hf_mul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hlocal : Summable (fun pk : Nat.Primes × ℕ =>
      f ((pk.1 : ℕ) ^ (pk.2 + 1)))) : Summable f := by
  classical
  have htail (p : Nat.Primes) :
      Summable (fun k : ℕ => f ((p : ℕ) ^ (k + 1))) :=
    hlocal.prod_factor p
  have hprime {p : ℕ} (hp : p.Prime) :
      Summable (fun e : ℕ => ‖f (p ^ e)‖) := by
    apply (summable_nat_add_iff (f := fun e : ℕ => ‖f (p ^ e)‖) 1).mp
    simpa only [Real.norm_of_nonneg (hf_nonneg _)] using htail ⟨p, hp⟩
  obtain ⟨tailTotal, htail_sum⟩ := hlocal.prod
  have hlocal_factor (p : Nat.Primes) :
      (∑' e : ℕ, f ((p : ℕ) ^ e)) =
        1 + ∑' k : ℕ, f ((p : ℕ) ^ (k + 1)) := by
    have hfull : Summable (fun e : ℕ => f ((p : ℕ) ^ e)) := by
      simpa only [Real.norm_of_nonneg (hf_nonneg _)] using hprime p.prop
    rw [← hfull.sum_add_tsum_nat_add 1]
    simp [hf_one]
  have hsmooth_bound (N : ℕ) :
      (∑' m : N.smoothNumbers, f m) ≤
        Real.exp tailTotal := by
    have hEuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      hf_one hf_mul hprime N
    have hprod :
        (∏ p ∈ N.primesBelow, ∑' e : ℕ, f (p ^ e)) =
          ∏ p ∈ N.primesBelow, (1 + ∑' k : ℕ, f (p ^ (k + 1))) := by
      apply Finset.prod_congr rfl
      intro p hp
      simpa using hlocal_factor ⟨p, Nat.prime_of_mem_primesBelow hp⟩
    rw [hEuler.2.tsum_eq, hprod]
    calc
      ∏ p ∈ N.primesBelow,
          (1 + ∑' k : ℕ, f (p ^ (k + 1))) ≤
          Real.exp (∑ p ∈ N.primesBelow,
            ∑' k : ℕ, f (p ^ (k + 1))) :=
        Real.prod_one_add_le_exp_sum _ fun p =>
          tsum_nonneg fun k => hf_nonneg _
      _ ≤ Real.exp tailTotal := by
        apply Real.exp_le_exp.mpr
        rw [← Finset.sum_subtype_of_mem
          (fun p : ℕ => ∑' k : ℕ, f (p ^ (k + 1)))
          (fun p hp => Nat.prime_of_mem_primesBelow hp)]
        exact sum_le_hasSum (L := SummationFilter.unconditional Nat.Primes)
          (N.primesBelow.subtype Nat.Prime)
          (fun _ _ => tsum_nonneg fun k => hf_nonneg _) htail_sum
  apply summable_of_sum_range_le hf_nonneg
    (c := Real.exp tailTotal)
  intro N
  have hEuler := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf_one hf_mul hprime N
  have hsmooth : Summable (fun m : N.smoothNumbers => f m) := hEuler.2.summable
  calc
    ∑ n ∈ Finset.range N, f n =
        ∑ n ∈ (Finset.range N).filter (fun n => n ∈ N.smoothNumbers), f n := by
      symm
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hs : n ∈ N.smoothNumbers
      · simp [hs]
      · have hn_zero : n = 0 := by
          by_contra hn_zero
          exact hs (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn_zero)
            (Finset.mem_range.mp hn))
        simp [hn_zero, hf_zero]
    _ = ∑ m ∈ (Finset.range N).subtype (fun n => n ∈ N.smoothNumbers), f m := by
      exact (Finset.sum_subtype_eq_sum_filter (s := Finset.range N) f).symm
    _ ≤ ∑' m : N.smoothNumbers, f m :=
      hsmooth.sum_le_tsum _ fun m _ => hf_nonneg m
    _ ≤ Real.exp tailTotal := hsmooth_bound N

private theorem dTerm_face_eq (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    dTerm σ (-Real.goldenConj * σ) n = Real.exp (-σ * lambdaPlus n) := by
  have hnSpos : (0 : ℝ) < nS n := by exact_mod_cast Nat.pos_of_ne_zero (nS_ne_zero n)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [dTerm, if_neg hn, lambdaPlus_eq_log_nS_sub_goldenConj_log _ hn,
    Real.rpow_def_of_pos hnSpos, Real.rpow_def_of_pos hnpos, ← Real.exp_add]
  congr 1
  ring

/-- The expansion face has the exact heat abscissa `1 / φ²`. -/
theorem faceLength_heat_abscissa_exact :
    IsHeatAbscissa faceLength (1 / Real.goldenRatio ^ 2) := by
  constructor
  · intro σ hσ
    have hlocal : Summable (fun pk : Nat.Primes × ℕ =>
        dTerm σ (-Real.goldenConj * σ) ((pk.1 : ℕ) ^ (pk.2 + 1))) := by
      refine (golden_heat_abscissa.1 σ hσ).congr fun pk => ?_
      rcases pk with ⟨p, k⟩
      rw [dTerm_face_eq σ (pow_ne_zero _ p.prop.ne_zero),
        lambdaPlus_prime_pow_eq_goldenSpectrum]
    have hglobal : Summable (dTerm σ (-Real.goldenConj * σ)) :=
      summable_of_summable_prime_power_tail
        (dTerm σ (-Real.goldenConj * σ))
        (dTerm_zero _ _) (dTerm_one _ _) (dTerm_nonneg _ _) (fun h =>
          dTerm_mul_of_coprime h) hlocal
    refine (hglobal.comp_injective Nat.succ_injective).congr fun k => ?_
    simpa only [Function.comp_apply, faceLength, Nat.succ_eq_add_one] using
      dTerm_face_eq σ (Nat.succ_ne_zero k)
  · intro σ hσ
    exact not_summable_faceLength_heat hσ.le

example : IsHeatAbscissa faceLength (1 / Real.goldenRatio ^ 2) :=
  faceLength_heat_abscissa_exact

end

end GoldenDisplacementFaceHeatAbscissa
