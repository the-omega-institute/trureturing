/- GID: D5/S3/Arith/Robin/PriceRecord/FixedLayerFiniteActivation
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/FixedLayerFiniteActivation
   mirror-E: none(waiver:general-finite-analysis)
   anchors: []
   utility: none
   digest: Capped activation and omitted layers of the integer Robin tangent cost. -/

import D5.S3.Arith.Robin.PriceRecord.BoundaryPrimePrice
import D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
import D5.S3.Arith.GoldenResourceOptimalInteger
import Mathlib.Algebra.BigOperators.Intervals

/-! The capped formula telescopes exact Euler increments. The supported estimate
bounds the contribution of all omitted layers using an arbitrary cap at each prime. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation

open Finset Real
open scoped BigOperators
open BoundaryPrimePrice
  (benefit_log integer_gap_attained priceObjective probability probability_mem)
open FixedSupportIntegerActivationEnvelope (eulerTerm linearCost supportedAdmissible)
open OwnClockFixedSupport (primeSupport)
open D5.S3.Arith.GoldenResourceOptimalInteger (goldenLayerMarginal golden_layer_strict_decrease)

/-- The charge for an exponent above one, plus the remaining Euler term. -/
def localCost (p : ℕ) (q : ℝ) (a : ℕ) : ℝ :=
  q * ((a : ℝ) - 1) + eulerTerm p a

/-- At layer `j ≥ 2`, this is `J(p⁻ʲ) - J(p⁻⁽ʲ⁺¹⁾)`. -/
def layerGain (p j : ℕ) : ℝ :=
  goldenLayerMarginal p j * log (p : ℝ)

/-- The total clipped charge for layers two through the cap. -/
def clippedLayers (p : ℕ) (q : ℝ) (K : ℕ) : ℝ :=
  ∑ j ∈ Finset.Ioc 1 K, min q (layerGain p j)

lemma layerGain_eq_eulerTerm_sub {p j : ℕ} (hp : p.Prime) (hj : 1 ≤ j) :
    layerGain p j = eulerTerm p (j - 1) - eulerTerm p j := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpInvPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr (zero_lt_one.trans hp1)
  have hpInvLt : (p : ℝ)⁻¹ < 1 := (inv_lt_one₀ (zero_lt_one.trans hp1)).mpr hp1
  have hden (n : ℕ) (hn : 1 ≤ n) : 0 < 1 - (p : ℝ)⁻¹ ^ n :=
    sub_pos.mpr (pow_lt_one₀ hpInvPos.le hpInvLt (by omega))
  rw [layerGain, goldenLayerMarginal, div_mul_cancel₀ _ hp.log_pos.ne',
    log_div (hden (j + 1) (by omega)).ne' (hden j hj).ne']
  unfold eulerTerm
  rw [show j - 1 + 1 = j by omega]
  simp only [one_div, inv_pow]
  ring

private lemma layerGain_lt {p i j : ℕ} (hp : p.Prime) (hi : 1 ≤ i) (hij : i < j) :
    layerGain p j < layerGain p i := by
  exact mul_lt_mul_of_pos_right (golden_layer_strict_decrease hp hi hij) hp.log_pos

private lemma sum_layerGain {p a K : ℕ} (hp : p.Prime) (haK : a ≤ K) :
    (∑ j ∈ Finset.Ioc a K, layerGain p j) = eulerTerm p a - eulerTerm p K := by
  refine Nat.le_induction ?_ ?_ K haK
  · simp only [Finset.Ioc_self, sum_empty, sub_self]
  · intro n hn ih
    rw [Finset.sum_Ioc_succ_top hn, ih]
    rw [layerGain_eq_eulerTerm_sub hp (by omega)]
    simp only [Nat.add_sub_cancel]
    ring

private lemma localCost_eq_sums {p a K : ℕ} {q : ℝ} (hp : p.Prime) (ha : 1 ≤ a) (haK : a ≤ K) :
    localCost p q a = eulerTerm p K +
      ((∑ _j ∈ Finset.Ioc 1 a, q) + ∑ j ∈ Finset.Ioc a K, layerGain p j) := by
  rw [sum_layerGain hp haK, sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub ha,
    Nat.cast_one]
  unfold localCost
  ring

/-- The capped formula belongs to the cost image of the entire admissible interval and is its
least element. The last strictly profitable layer selects an exponent even when a layer ties. -/
theorem capped_minimum_isLeast {p K : ℕ} {q : ℝ} (hp : p.Prime) (hK : 1 ≤ K) :
    IsLeast (localCost p q '' Set.Icc (1 : ℕ) K) (eulerTerm p K + clippedLayers p q K) := by
  classical
  let eligible := (Finset.Icc 1 K).filter (fun j => j = 1 ∨ q < layerGain p j)
  have hnonempty : eligible.Nonempty :=
    ⟨1, mem_filter.mpr ⟨mem_Icc.mpr ⟨le_rfl, hK⟩, Or.inl rfl⟩⟩
  obtain ⟨a, haMem, haTop⟩ := Finset.exists_mem_eq_sup eligible hnonempty id
  have haEligible : a ∈ Finset.Icc 1 K ∧ (a = 1 ∨ q < layerGain p a) := mem_filter.mp haMem
  obtain ⟨ha, haK⟩ := mem_Icc.mp haEligible.1
  have hleft : (∑ j ∈ Finset.Ioc 1 a, min q (layerGain p j)) = ∑ _j ∈ Finset.Ioc 1 a, q := by
    apply sum_congr rfl
    intro j hj
    obtain ⟨hj1, hja⟩ := mem_Ioc.mp hj
    have hactive : q < layerGain p a := haEligible.2.resolve_left (by omega)
    apply min_eq_left
    rcases eq_or_lt_of_le hja with heq | hlt
    · simpa only [heq] using hactive.le
    · exact (hactive.trans (layerGain_lt hp hj1.le hlt)).le
  have hright : (∑ j ∈ Finset.Ioc a K, min q (layerGain p j)) =
      ∑ j ∈ Finset.Ioc a K, layerGain p j := by
    apply sum_congr rfl
    intro j hj
    obtain ⟨haj, hjK⟩ := mem_Ioc.mp hj
    apply min_eq_right
    by_contra! hactive
    have hjMem : j ∈ eligible :=
      mem_filter.mpr ⟨mem_Icc.mpr ⟨ha.trans haj.le, hjK⟩, Or.inr hactive⟩
    have hjTop := Finset.le_sup (f := id) hjMem
    rw [haTop] at hjTop
    exact (not_le_of_gt haj) hjTop
  have heq : eulerTerm p K + clippedLayers p q K = localCost p q a := by
    rw [clippedLayers,
      ← Finset.sum_Ioc_consecutive (fun j => min q (layerGain p j)) ha haK,
      hleft, hright, localCost_eq_sums hp ha haK]
  refine ⟨⟨a, ⟨ha, haK⟩, heq.symm⟩, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  have hb1 : 1 ≤ b := hb.1
  have hbK : b ≤ K := hb.2
  rw [clippedLayers,
    ← Finset.sum_Ioc_consecutive (fun j => min q (layerGain p j)) hb1 hbK,
    localCost_eq_sums hp hb1 hbK]
  exact add_le_add_right (add_le_add
    (sum_le_sum (fun j _ => min_le_left q (layerGain p j)))
    (sum_le_sum (fun j _ => min_le_right q (layerGain p j)))) _

private lemma probability_natCast (p a : ℕ) :
    probability (p : ℝ) (a : ℝ) = 1 / (p : ℝ) ^ (a + 1) := by
  unfold probability
  rw [show (a : ℝ) + 1 = ((a + 1 : ℕ) : ℝ) by simp,
    rpow_neg (Nat.cast_nonneg p : (0 : ℝ) ≤ p), rpow_natCast]
  simp only [one_div]

private lemma eulerTerm_nonneg {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) : 0 ≤ eulerTerm p a := by
  have hprob := probability_mem (by exact_mod_cast hp.one_lt : (1 : ℝ) < p)
    (by exact_mod_cast ha : (1 : ℝ) ≤ a)
  rw [probability_natCast] at hprob
  exact neg_nonneg.mpr (log_nonpos (sub_nonneg.mpr hprob.2.le) (sub_le_self _ hprob.1.le))

private lemma localCost_eq_priceObjective {p a : ℕ} {q : ℝ} (hp : p.Prime) (ha : 1 ≤ a) :
    localCost p q a = -priceObjective (p : ℝ) (q / log (p : ℝ)) (a : ℝ) - q -
      log (1 - (p : ℝ) ^ (-1 : ℝ)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hcharge : q / log (p : ℝ) * (a : ℝ) * log (p : ℝ) = q * (a : ℝ) := by
    rw [mul_right_comm, div_mul_cancel₀ _ hp.log_pos.ne']
  rw [priceObjective, benefit_log hp1 haR, probability_natCast, hcharge]
  unfold localCost eulerTerm
  ring

private def localMinimum (p : ℕ) (q : ℝ) : ℝ :=
  sInf (localCost p q '' Set.Ici (1 : ℕ))

/-- The positive-price uncapped minimum is attained on the same natural exponent domain. -/
private theorem local_minimum_isLeast {p : ℕ} {q : ℝ} (hp : p.Prime) (hq : 0 < q) :
    IsLeast (localCost p q '' Set.Ici (1 : ℕ)) (localMinimum p q) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨k, hk, _, hkMax⟩ := integer_gap_attained hp1 (div_pos hq hp.log_pos)
  have hk0 : 0 ≤ k := (by norm_num : (0 : ℤ) ≤ 1).trans hk
  have hkNat : 1 ≤ k.toNat := by
    have hkCast : (1 : ℤ) ≤ (k.toNat : ℤ) := by rwa [Int.toNat_of_nonneg hk0]
    exact_mod_cast hkCast
  have hkReal : (k.toNat : ℝ) = (k : ℝ) := by
    simpa only [Int.cast_natCast] using
      congrArg (fun n : ℤ => (n : ℝ)) (Int.toNat_of_nonneg hk0)
  have hleast : IsLeast (localCost p q '' Set.Ici (1 : ℕ)) (localCost p q k.toNat) := by
    refine ⟨⟨k.toNat, hkNat, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    have haNat : 1 ≤ a := ha
    have haInt : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast haNat
    have hopt := hkMax (a : ℤ) haInt
    rw [Int.cast_natCast, ← hkReal] at hopt
    rw [localCost_eq_priceObjective hp haNat, localCost_eq_priceObjective hp hkNat]
    exact sub_le_sub_right (sub_le_sub_right (neg_le_neg hopt) q) _
  rw [localMinimum, hleast.csInf_eq]
  exact hleast

private lemma clippedLayers_le_cost {p a m : ℕ} {q : ℝ} (hp : p.Prime) (hq : 0 ≤ q)
    (ha : 1 ≤ a) (hm : 1 ≤ m) : clippedLayers p q m ≤ localCost p q a := by
  by_cases ham : a ≤ m
  · have hcap := (capped_minimum_isLeast (q := q) hp hm).2
      (show localCost p q a ∈ localCost p q '' Set.Icc (1 : ℕ) m from ⟨a, ⟨ha, ham⟩, rfl⟩)
    exact (le_add_of_nonneg_left (eulerTerm_nonneg hp hm)).trans hcap
  · have hma : m ≤ a := (lt_of_not_ge ham).le
    have hmaR : (m : ℝ) ≤ a := by exact_mod_cast hma
    calc
      clippedLayers p q m ≤ ∑ _j ∈ Finset.Ioc 1 m, q :=
        sum_le_sum (fun j _ => min_le_left q (layerGain p j))
      _ = ((m : ℝ) - 1) * q := by
        rw [sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hm, Nat.cast_one]
      _ ≤ q * ((a : ℝ) - 1) := by
        rw [mul_comm ((m : ℝ) - 1) q]
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hmaR 1) hq
      _ ≤ localCost p q a := le_add_of_nonneg_right (eulerTerm_nonneg hp ha)

/-- The omitted layers of the uncapped minimum are bounded using any finite cap above `m`. -/
private theorem omitted_layers_bounds {p m K : ℕ} {q : ℝ} (hp : p.Prime) (hq : 0 < q)
    (hm : 2 ≤ m) (hmK : m ≤ K) :
    0 ≤ localMinimum p q - clippedLayers p q m ∧
      localMinimum p q - clippedLayers p q m ≤ ((K - m : ℕ) : ℝ) * q + eulerTerm p K := by
  have hm1 : 1 ≤ m := by omega
  have hleast := local_minimum_isLeast hp hq
  obtain ⟨a, ha, heq⟩ := hleast.1
  have hlower : clippedLayers p q m ≤ localMinimum p q :=
    (clippedLayers_le_cost hp hq.le ha hm1).trans heq.le
  obtain ⟨b, hb, hbEq⟩ := (capped_minimum_isLeast (q := q) hp (hm1.trans hmK)).1
  have hupper : localMinimum p q ≤ eulerTerm p K + clippedLayers p q K :=
    (hleast.2 ⟨b, hb.1, rfl⟩).trans hbEq.le
  have htail : (∑ j ∈ Finset.Ioc m K, min q (layerGain p j)) ≤ ((K - m : ℕ) : ℝ) * q := by
    calc
      (∑ j ∈ Finset.Ioc m K, min q (layerGain p j)) ≤ ∑ _j ∈ Finset.Ioc m K, q :=
        sum_le_sum (fun j _ => min_le_left q (layerGain p j))
      _ = _ := by rw [sum_const, Nat.card_Ioc, nsmul_eq_mul]
  rw [clippedLayers,
    ← Finset.sum_Ioc_consecutive (fun j => min q (layerGain p j)) hm1 hmK] at hupper
  refine ⟨sub_nonneg.mpr hlower, ?_⟩
  unfold clippedLayers
  linarith only [hupper, htail]

/-- The infimum of the full supported integer image at a fixed tangent price. -/
def fixedPriceMinimum (S : Finset ℕ) (lam : ℝ) : ℝ :=
  sInf {v | ∃ a : ℕ → ℕ, supportedAdmissible S a ∧ linearCost S lam a = v}

theorem sum_local_minima_isLeast {S : Finset ℕ} {lam : ℝ} (hS : primeSupport S)
    (hlam : 0 < lam) :
    IsLeast {v | ∃ a : ℕ → ℕ, supportedAdmissible S a ∧ linearCost S lam a = v}
      (∑ p ∈ S, localMinimum p (lam * log (p : ℝ))) := by
  classical
  have hleast (p : ℕ) (hp : p ∈ S) :=
    local_minimum_isLeast (hS p hp) (mul_pos hlam (hS p hp).log_pos)
  have hex (p : ℕ) (hp : p ∈ S) : ∃ a : ℕ, 1 ≤ a ∧
      localCost p (lam * log (p : ℝ)) a = localMinimum p (lam * log (p : ℝ)) :=
    (hleast p hp).1
  let a : ℕ → ℕ := fun p => if hp : p ∈ S then Classical.choose (hex p hp) else 1
  have ha (p : ℕ) (hp : p ∈ S) : 1 ≤ a p ∧
      localCost p (lam * log (p : ℝ)) (a p) = localMinimum p (lam * log (p : ℝ)) := by
    dsimp only [a]
    rw [dite_eq_left hp]
    exact Classical.choose_spec (hex p hp)
  have hlinear (b : ℕ → ℕ) : linearCost S lam b =
      ∑ p ∈ S, localCost p (lam * log (p : ℝ)) (b p) := by
    unfold linearCost
    apply sum_congr rfl
    intro p _
    unfold localCost
    ring
  refine ⟨⟨a, fun p hp => (ha p hp).1, ?_⟩, ?_⟩
  · rw [hlinear]
    exact sum_congr rfl (fun p hp => (ha p hp).2)
  · rintro _ ⟨b, hb, rfl⟩
    rw [hlinear]
    exact sum_le_sum (fun p hp => (hleast p hp).2 ⟨b p, hb p hp, rfl⟩)

/-- The omitted-layer estimate sums over any finite prime support, with a cap per prime. -/
theorem fixed_price_omitted_layers {S : Finset ℕ} {lam : ℝ} {m : ℕ}
    (hS : primeSupport S) (hlam : 0 < lam) (hm : 2 ≤ m)
    (K : ℕ → ℕ) (hK : ∀ p ∈ S, m ≤ K p) :
    0 ≤ fixedPriceMinimum S lam - (∑ p ∈ S, clippedLayers p (lam * log (p : ℝ)) m) ∧
      fixedPriceMinimum S lam - (∑ p ∈ S, clippedLayers p (lam * log (p : ℝ)) m) ≤
        ∑ p ∈ S, (((K p - m : ℕ) : ℝ) * (lam * log (p : ℝ)) + eulerTerm p (K p)) := by
  have hlocal (p : ℕ) (hp : p ∈ S) :=
    omitted_layers_bounds (hS p hp) (mul_pos hlam (hS p hp).log_pos) hm (hK p hp)
  simp only [fixedPriceMinimum, (sum_local_minima_isLeast hS hlam).csInf_eq,
    ← sum_sub_distrib]
  exact ⟨sum_nonneg (fun p hp => (hlocal p hp).1), sum_le_sum (fun p hp => (hlocal p hp).2)⟩

end D5.S3.Arith.Robin.PriceRecord.FixedLayerFiniteActivation
