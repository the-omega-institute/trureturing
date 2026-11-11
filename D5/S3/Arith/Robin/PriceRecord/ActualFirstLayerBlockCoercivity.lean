/- GID: D5/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualFirstLayerBlockCoercivity
   mirror-E: none(waiver:finite-quantitative-analysis)
   anchors: []
   utility: none
   digest: Finite theta-mass coercivity for both sides of the complete first-layer loss. -/

import D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone

/-! Finite prime blocks charge the canonical complete loss through their theta mass. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity

open Finset Real
open D5.S3.Arith.Robin.PriceRecord.ActualRecordHigherLayerResidual
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone

private def block (a b : ℝ) : Finset ℕ :=
  Nat.primesLE ⌊b⌋₊ \ Nat.primesLE ⌊a⌋₊

private theorem mem_block {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {p : ℕ} :
    p ∈ block a b ↔ p.Prime ∧ a < (p : ℝ) ∧ (p : ℝ) ≤ b := by
  simp only [block, mem_sdiff, Nat.mem_primesLE]
  constructor
  · rintro ⟨⟨hpb, hp⟩, hpa⟩
    refine ⟨hp, ?_, (Nat.le_floor_iff (ha.trans hab)).mp hpb⟩
    by_contra h
    exact hpa ⟨(Nat.le_floor_iff ha).mpr (le_of_not_gt h), hp⟩
  · rintro ⟨hp, hap, hpb⟩
    refine ⟨⟨(Nat.le_floor_iff (ha.trans hab)).mpr hpb, hp⟩, ?_⟩
    rintro ⟨hpa, _⟩
    exact (not_le_of_gt hap) ((Nat.le_floor_iff ha).mp hpa)

private theorem theta_block_le_count {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    Chebyshev.theta b - Chebyshev.theta a ≤ (block a b).card * log b := by
  have hsub : Nat.primesLE ⌊a⌋₊ ⊆ Nat.primesLE ⌊b⌋₊ :=
    Nat.primesLE_mono (Nat.floor_mono hab.le)
  have heq : Chebyshev.theta b - Chebyshev.theta a =
      ∑ p ∈ block a b, log p := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE,
      ← sum_sdiff hsub]
    simp [block]
  rw [heq]
  calc
    _ ≤ ∑ _p ∈ block a b, log b := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpp, _, hpb⟩ := (mem_block (by linarith) hab.le).mp hp
      exact log_le_log (by exact_mod_cast hpp.pos) hpb
    _ = _ := by simp

private theorem first_margin {X : ℝ} {p : ℕ} (hp : p.Prime) :
    rawLayerMargin X p 1 = log (1 + 1 / (p : ℝ)) - log p / (X * log X) := by
  rw [rawLayerMargin, golden_layer_marginal_one_eq_log_one_add_inv hp]
  unfold referencePrice
  field_simp [hp.log_pos.ne']

private theorem missing_margin {X b : ℝ} (hX : 1 < X) (hb : 1 < b)
    (hbX : b + 1 / 2 < X) {p : ℕ} (hp : p.Prime) (hpb : (p : ℝ) ≤ b) :
    1 / (b + 1 / 2) - 1 / X ≤ rawLayerMargin X p 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hX0 : 0 < X := by linarith
  have hlX : 0 < log X := log_pos hX
  have hlog : log p ≤ log X := log_le_log hp0 (by linarith)
  have hprice : log p / (X * log X) ≤ 1 / X := by
    apply (div_le_div_iff₀ (mul_pos hX0 hlX) hX0).mpr
    nlinarith
  have hgain : 1 / ((p : ℝ) + 1 / 2) ≤ log (1 + 1 / (p : ℝ)) := by
    have h := (lt_log_one_add_of_pos (one_div_pos.mpr hp0)).le
    have heq : 2 * (1 / (p : ℝ)) / (1 / (p : ℝ) + 2) =
        1 / ((p : ℝ) + 1 / 2) := by field_simp; ring
    rwa [heq] at h
  have hrecip : 1 / (b + 1 / 2) ≤ 1 / ((p : ℝ) + 1 / 2) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  rw [first_margin hp]
  linarith

private theorem occupied_margin {X a : ℝ} (hX : 1 < X) (hXa : X < a)
    {p : ℕ} (hp : p.Prime) (hap : a < (p : ℝ)) :
    1 / X - 1 / a ≤ -rawLayerMargin X p 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hX0 : 0 < X := by linarith
  have ha0 : 0 < a := by linarith
  have hlX : 0 < log X := log_pos hX
  have hlog : log X ≤ log p := log_le_log hX0 (by linarith)
  have hprice : 1 / X ≤ log p / (X * log X) := by
    apply (div_le_div_iff₀ hX0 (mul_pos hX0 hlX)).mpr
    nlinarith
  have hgain : log (1 + 1 / (p : ℝ)) ≤ 1 / (p : ℝ) := by
    have h := log_le_sub_one_of_pos (show 0 < 1 + 1 / (p : ℝ) by positivity)
    linarith
  have hrecip : 1 / (p : ℝ) ≤ 1 / a := one_div_le_one_div_of_le ha0 hap.le
  rw [first_margin hp]
  linarith

private theorem positive_margin_mem {X : ℝ} (hX : 1 < X) (m : ℕ)
    {p : ℕ} (hp : p.Prime) (hg : 0 < rawLayerMargin X p 1) :
    p ∈ lossPrimes X m := by
  have hprice : 0 < referencePrice X :=
    one_div_pos.mpr (mul_pos (by linarith) (log_pos hX))
  have hgain : referencePrice X < goldenLayerMarginal p 1 := by
    unfold rawLayerMargin at hg
    exact sub_pos.mp ((mul_pos_iff_of_pos_left hp.log_pos).mp hg)
  have hc : 1 ≤ optimalLayerCount (referencePrice X) p := by
    have hi := Set.ext_iff.mp (positive_layers_eq_count_interval hprice hp) 1
    exact (hi.mp ⟨le_rfl, hp, hgain⟩).2
  apply mem_union_left
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]
  change (D5.S3.Arith.Robin.ActualTwoPriceDefect.strictInteger
    (referencePrice X)).factorization p ≠ 0
  rw [D5.S3.Arith.Robin.ActualTwoPriceDefect.strictInteger_counts hprice]
  omega

private theorem loss_nonneg (X : ℝ) (m p : ℕ) : 0 ≤ layerLoss X m p 1 := by
  unfold layerLoss
  split_ifs
  · exact sub_nonneg.mpr (le_max_left _ _)
  · simpa using le_max_right (rawLayerMargin X p 1) 0

private theorem block_loss {X a b c : ℝ} {m : ℕ}
    (hmem : block a b ⊆ lossPrimes X m)
    (hloss : ∀ p ∈ block a b, c ≤ layerLoss X m p 1) :
    (block a b).card * c ≤ completeFirstLayerLoss X m := by
  calc
    _ = ∑ _p ∈ block a b, c := by simp
    _ ≤ ∑ p ∈ block a b, layerLoss X m p 1 := sum_le_sum hloss
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hmem (fun p _ _ => loss_nonneg X m p)

private theorem theta_to_loss {X a b c : ℝ} {m : ℕ}
    (ha : 1 < a) (hab : a < b) (hc : 0 ≤ c)
    (hloss : (block a b).card * c ≤ completeFirstLayerLoss X m) :
    c * (Chebyshev.theta b - Chebyshev.theta a) / log b ≤
      completeFirstLayerLoss X m := by
  have hlb : 0 < log b := log_pos (lt_trans ha hab)
  apply (div_le_iff₀ hlb).mpr
  have htheta := mul_le_mul_of_nonneg_left (theta_block_le_count ha hab) hc
  have hsum := mul_le_mul_of_nonneg_right hloss hlb.le
  nlinarith

/-- Missing primes in the literal interval `(a,b]` charge the complete loss,
including its optimizer-only support. Zero theta mass is allowed. -/
theorem missing_block_theta_lower_bound {X a b : ℝ} {m Q : ℕ}
    (hX : 4 < X) (_hm : 2 ≤ m) (hsupport : m.primeFactors = Nat.primesLE Q)
    (ha : 1 < a) (hab : a < b) (hQa : (Q : ℝ) ≤ a) (hbX : b + 1 / 2 < X) :
    (X - b - 1 / 2) * (Chebyshev.theta b - Chebyshev.theta a) /
      (X * (b + 1 / 2) * log b) ≤ completeFirstLayerLoss X m := by
  have hX1 : 1 < X := by linarith
  have hb : 1 < b := ha.trans hab
  have hc : 0 < 1 / (b + 1 / 2) - 1 / X := by
    apply sub_pos.mpr
    exact one_div_lt_one_div_of_lt (by linarith) hbX
  have hlocal (p : ℕ) (hp : p ∈ block a b) :
      p ∈ lossPrimes X m ∧
      1 / (b + 1 / 2) - 1 / X ≤ layerLoss X m p 1 := by
    obtain ⟨hpp, hap, hpb⟩ := (mem_block (by linarith) hab.le).mp hp
    have hg := missing_margin hX1 hb hbX hpp hpb
    have hg0 : 0 < rawLayerMargin X p 1 := hc.trans_le hg
    have hnot : p ∉ m.primeFactors := by
      rw [hsupport]
      intro hpQ
      have hpQ' : (p : ℝ) ≤ Q := by exact_mod_cast (Nat.mem_primesLE.mp hpQ).1
      linarith
    have hv : m.factorization p = 0 := by
      by_contra h
      exact hnot (by rwa [← Nat.support_factorization, Finsupp.mem_support_iff])
    refine ⟨positive_margin_mem hX1 m hpp hg0, ?_⟩
    simpa [layerLoss, hv, max_eq_left hg0.le] using hg
  have hs := block_loss (fun p hp => (hlocal p hp).1) (fun p hp => (hlocal p hp).2)
  have ht := theta_to_loss ha hab hc.le hs
  convert ht using 1
  field_simp
  ring

/-- Occupied primes in `(a,b]` charge the same complete loss, with all other
prime contributions nonnegative. No record or analytic hypothesis is used. -/
theorem occupied_block_theta_lower_bound {X a b : ℝ} {m Q : ℕ}
    (hX : 4 < X) (_hm : 2 ≤ m) (hsupport : m.primeFactors = Nat.primesLE Q)
    (ha : 1 < a) (hab : a < b) (hbQ : b ≤ (Q : ℝ)) (hXa : X < a) :
    (a - X) * (Chebyshev.theta b - Chebyshev.theta a) /
      (X * a * log b) ≤ completeFirstLayerLoss X m := by
  have hX1 : 1 < X := by linarith
  have hc : 0 < 1 / X - 1 / a := by
    exact sub_pos.mpr (one_div_lt_one_div_of_lt (by linarith) hXa)
  have hlocal (p : ℕ) (hp : p ∈ block a b) :
      p ∈ lossPrimes X m ∧ 1 / X - 1 / a ≤ layerLoss X m p 1 := by
    obtain ⟨hpp, hap, hpb⟩ := (mem_block (by linarith) hab.le).mp hp
    have hpQ : p ≤ Q := by exact_mod_cast hpb.trans hbQ
    have hpm : p ∈ m.primeFactors := by rw [hsupport]; exact Nat.mem_primesLE.mpr ⟨hpQ, hpp⟩
    have hv : 1 ≤ m.factorization p := by
      have hne : m.factorization p ≠ 0 := by
        rwa [← Finsupp.mem_support_iff, Nat.support_factorization]
      omega
    have hg := occupied_margin hX1 hXa hpp hap
    refine ⟨mem_union_right _ hpm, ?_⟩
    have hmax : 0 ≤ max (rawLayerMargin X p 1) 0 := le_max_right _ _
    simp only [layerLoss, ite_eq_left hv]
    linarith
  have hs := block_loss (fun p hp => (hlocal p hp).1) (fun p hp => (hlocal p hp).2)
  have ht := theta_to_loss ha hab hc.le hs
  convert ht using 1
  field_simp

#print axioms missing_block_theta_lower_bound
#print axioms occupied_block_theta_lower_bound

end D5.S3.Arith.Robin.PriceRecord.ActualFirstLayerBlockCoercivity
