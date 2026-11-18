/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Exchange generality: I mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Exchange mirror-E: none(waiver:evidence-not-specified-by-formal-manifest) anchors: [] utility: none digest: Budget-feasible equal-cardinality prime exchanges and their injective count. -/
import D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Data.Fintype.Prod
import D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff
import Mathlib.Analysis.Complex.ExponentialBounds
import D5.S3.Arith.Robin.Analytic.OmegaTailUpper
import D5.S3.Weil.ZetaBridge.FermiMellin
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Topology BigOperators
open Real Filter MeasureTheory Finset Set Asymptotics
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
/-- Disjoint removable and insertable prime bins around a prime base. -/
structure ExchangeSystem (ι : Type*) where
  base : Finset ℕ
  neg : ι → Finset ℕ
  pos : ι → Finset ℕ
  base_prime : ∀ p ∈ base, Nat.Prime p
  neg_subset : ∀ i, neg i ⊆ base
  pos_prime : ∀ i p, p ∈ pos i → Nat.Prime p
  pos_base : ∀ i, Disjoint (pos i) base
  neg_disjoint : Pairwise (fun i j => Disjoint (neg i) (neg j))
  pos_disjoint : Pairwise (fun i j => Disjoint (pos i) (pos j))
/-- Actual logarithmic bins avoid a reserve trimmed below three quarters of P. -/
def logarithmicExchangeSystem (n : ℕ) (P s : ℝ) (node : ℕ → ℝ) (R : Finset ℕ) (hP : 0 < P) (hs : 0 < s) (hmono : Monotone node) (hzero : node 0 = 0) (hfar : 3 * P / 4 ≤ P * exp (-node n / s)) (hR : R ⊆ primeInterval (P / 2) (3 * P / 4)) : ExchangeSystem (Fin n) := by
  have hneg (i j : ℕ) (hij : i ≤ j) : P * exp (-node j / s) ≤ P * exp (-node i / s) := by
    apply mul_le_mul_of_nonneg_left _ hP.le
    exact exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg (hmono hij)) hs.le)
  have hpos (i j : ℕ) (hij : i ≤ j) : P * exp (node i / s) ≤ P * exp (node j / s) := by
    apply mul_le_mul_of_nonneg_left _ hP.le
    exact exp_le_exp.mpr (div_le_div_of_nonneg_right (hmono hij) hs.le)
  have hnegP (i : ℕ) : P * exp (-node i / s) ≤ P := by
    simpa [hzero] using hneg 0 i (Nat.zero_le i)
  have hposP (i : ℕ) : P ≤ P * exp (node i / s) := by
    simpa [hzero] using hpos 0 i (Nat.zero_le i)
  refine {
    base := Nat.primesLE ⌊P⌋₊ \ R
    neg := fun i => primeInterval (P * exp (-node (i.val + 1) / s))
      (P * exp (-node i.val / s))
    pos := fun i => primeInterval (P * exp (node i.val / s))
      (P * exp (node (i.val + 1) / s))
    base_prime := ?_
    neg_subset := ?_
    pos_prime := ?_
    pos_base := ?_
    neg_disjoint := ?_
    pos_disjoint := ?_ }
  · intro p hp
    exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
  · intro i p hp
    obtain ⟨hp, hpprime⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hp
    refine Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr
      ⟨hhi.trans (Nat.floor_mono (hnegP i.val)), hpprime⟩, ?_⟩
    intro hr
    have hrhi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hR hr)).1).2
    have hh := Nat.floor_mono (hfar.trans (hneg (i.val + 1) n (by omega)))
    omega
  · intro i p hp
    exact (Finset.mem_filter.mp hp).2
  · intro i
    apply Finset.disjoint_left.mpr
    intro p hp hb
    have hpgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
    have hble := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hb).1).1
    have hh := Nat.floor_mono (hposP i.val)
    omega
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpi).1
    have hj := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpj).1
    rcases lt_or_gt_of_ne hij with hij | hij
    · have hh := Nat.floor_mono (hneg (i.val + 1) j.val (by omega))
      omega
    · have hh := Nat.floor_mono (hneg (j.val + 1) i.val (by omega))
      omega
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpi).1
    have hj := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpj).1
    rcases lt_or_gt_of_ne hij with hij | hij
    · have hh := Nat.floor_mono (hpos (i.val + 1) j.val (by omega))
      omega
    · have hh := Nat.floor_mono (hpos (j.val + 1) i.val (by omega))
      omega
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Independently choose the same prescribed cardinality on both sides. -/
abbrev Choices (E : ExchangeSystem ι) (h : ι → ℕ) := ((i : ι) → ↥((E.neg i).powersetCard (h i))) × ((i : ι) → ↥((E.pos i).powersetCard (h i)))
def removed (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Finset ℕ := univ.biUnion (fun i => (z.1 i).val)
def inserted (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Finset ℕ := univ.biUnion (fun i => (z.2 i).val)
def support (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Finset ℕ := (E.base \ removed E h z) ∪ inserted E h z
def value (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : ℕ := ∏ p ∈ support E h z, p
private lemma neg_selection (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) (i : ι) : (z.1 i).val ⊆ E.neg i ∧ (z.1 i).val.card = h i := mem_powersetCard.mp (z.1 i).property
private lemma pos_selection (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) (i : ι) : (z.2 i).val ⊆ E.pos i ∧ (z.2 i).val.card = h i := mem_powersetCard.mp (z.2 i).property
private lemma removed_subset (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : removed E h z ⊆ E.base := by
  intro p hp
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
  exact E.neg_subset i ((neg_selection E h z i).1 hi)
private lemma inserted_disjoint (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Disjoint (inserted E h z) E.base := by
  apply disjoint_left.mpr
  intro p hp hb
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
  exact disjoint_left.mp (E.pos_base i) ((pos_selection E h z i).1 hi) hb
private lemma support_prime (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : ∀ p ∈ support E h z, Nat.Prime p := by
  intro p hp
  rcases mem_union.mp hp with hp | hp
  · exact E.base_prime p (mem_sdiff.mp hp).1
  · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
    exact E.pos_prime i p ((pos_selection E h z i).1 hi)
private lemma neg_pairwise (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Set.PairwiseDisjoint (univ : Finset ι) (fun i => (z.1 i).val) := by
  intro i _ j _ hij
  exact (E.neg_disjoint hij).mono (neg_selection E h z i).1 (neg_selection E h z j).1
private lemma pos_pairwise (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Set.PairwiseDisjoint (univ : Finset ι) (fun i => (z.2 i).val) := by
  intro i _ j _ hij
  exact (E.pos_disjoint hij).mono (pos_selection E h z i).1 (pos_selection E h z j).1
private lemma removed_card (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : (removed E h z).card = ∑ i, h i := by
  rw [removed, card_biUnion (neg_pairwise E h z)]
  exact sum_congr rfl (fun i _ => (neg_selection E h z i).2)
private lemma inserted_card (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : (inserted E h z).card = ∑ i, h i := by
  rw [inserted, card_biUnion (pos_pairwise E h z)]
  exact sum_congr rfl (fun i _ => (pos_selection E h z i).2)
private lemma support_card (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : (support E h z).card = E.base.card := by
  have hd : Disjoint (E.base \ removed E h z) (inserted E h z) := (inserted_disjoint E h z).symm.mono_left sdiff_subset
  have hc := card_le_card (removed_subset E h z)
  rw [support, card_union_of_disjoint hd, card_sdiff_of_subset (removed_subset E h z),
    removed_card, inserted_card]
  rw [removed_card] at hc
  omega
/-- Unique factorization and bin separation recover every individual choice. -/
theorem exchange_value_injective (E : ExchangeSystem ι) (h : ι → ℕ) : Function.Injective (value E h) := by
  intro z w he
  have hs : support E h z = support E h w := prime_product_injective (support_prime E h z) (support_prime E h w) he
  have hr : removed E h z = removed E h w := by
    ext p
    by_cases hp : p ∈ E.base
    · have hz : p ∉ inserted E h z := fun hh =>
        disjoint_left.mp (inserted_disjoint E h z) hh hp
      have hw : p ∉ inserted E h w := fun hh =>
        disjoint_left.mp (inserted_disjoint E h w) hh hp
      have hh := Finset.ext_iff.mp hs p
      simp only [support, mem_union, Finset.mem_sdiff, hp, true_and, hz, hw, or_false] at hh
      exact not_iff_not.mp hh
    · exact iff_of_false (fun hh => hp (removed_subset E h z hh))
        (fun hh => hp (removed_subset E h w hh))
  have ha : inserted E h z = inserted E h w := by
    ext p
    by_cases hp : p ∈ E.base
    · exact iff_of_false
        (fun hh => disjoint_left.mp (inserted_disjoint E h z) hh hp)
        (fun hh => disjoint_left.mp (inserted_disjoint E h w) hh hp)
    · have hh := Finset.ext_iff.mp hs p
      simpa only [support, mem_union, Finset.mem_sdiff, hp, false_and, false_or] using hh
  apply Prod.ext
  · funext i
    apply Subtype.ext
    calc
      (z.1 i).val = removed E h z ∩ E.neg i := (bin_union_inter E.neg (fun j => (z.1 j).val) E.neg_disjoint
          (fun j => (neg_selection E h z j).1) i).symm
      _ = removed E h w ∩ E.neg i := by rw [hr]
      _ = (w.1 i).val := bin_union_inter E.neg (fun j => (w.1 j).val)
        E.neg_disjoint (fun j => (neg_selection E h w j).1) i
  · funext i
    apply Subtype.ext
    calc
      (z.2 i).val = inserted E h z ∩ E.pos i := (bin_union_inter E.pos (fun j => (z.2 j).val) E.pos_disjoint
          (fun j => (pos_selection E h z j).1) i).symm
      _ = inserted E h w ∩ E.pos i := by rw [ha]
      _ = (w.2 i).val := bin_union_inter E.pos (fun j => (w.2 j).val)
        E.pos_disjoint (fun j => (pos_selection E h w j).1) i
/-- Equal removal and insertion preserve the number of distinct prime factors. -/
theorem omega_exchange_value (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : ArithmeticFunction.cardDistinctFactors (value E h z) = E.base.card := by
  rw [value, omega_prime_product (support_prime E h z), support_card]
/-- Independent finite choices have the product of binomial cardinalities. -/
theorem card_exchange_choices (E : ExchangeSystem ι) (h : ι → ℕ) : Fintype.card (Choices E h) = ∏ i, (E.neg i).card.choose (h i) * (E.pos i).card.choose (h i) := by
  simp only [Choices, Fintype.card_prod, Fintype.card_pi, Fintype.card_coe,
    card_powersetCard, prod_mul_distrib]
/-- Every choice satisfies the same worst-endpoint cost; no averaging is used. -/
theorem log_exchange_value_le (E : ExchangeSystem ι) (h : ι → ℕ) (P D s : ℝ) (t : ι → ℝ) (hbase : ∑ p ∈ E.base, log (p : ℝ) ≤ P - D) (hneg : ∀ i p, p ∈ E.neg i → log P - t i / s ≤ log (p : ℝ)) (hpos : ∀ i p, p ∈ E.pos i → log (p : ℝ) ≤ log P + t i / s) (z : Choices E h) : log (value E h z : ℝ) ≤ P - D + (2 / s) * ∑ i, t i * (h i : ℝ) := by
  have hne : ∀ p ∈ support E h z, (p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (support_prime E h z p hp).ne_zero
  have hd : Disjoint (E.base \ removed E h z) (inserted E h z) := (inserted_disjoint E h z).symm.mono_left sdiff_subset
  have hn : ∑ p ∈ removed E h z, log (p : ℝ) ≥ ∑ i, (h i : ℝ) * (log P - t i / s) := by
    rw [removed, sum_biUnion (neg_pairwise E h z)]
    apply sum_le_sum
    intro i _
    calc
      (h i : ℝ) * (log P - t i / s) =
          ∑ _p ∈ (z.1 i).val, (log P - t i / s) := by
        simp [(neg_selection E h z i).2]
        ring
      _ ≤ ∑ p ∈ (z.1 i).val, log (p : ℝ) := sum_le_sum (fun p hp => hneg i p ((neg_selection E h z i).1 hp))
  have hp : ∑ p ∈ inserted E h z, log (p : ℝ) ≤ ∑ i, (h i : ℝ) * (log P + t i / s) := by
    rw [inserted, sum_biUnion (pos_pairwise E h z)]
    apply sum_le_sum
    intro i _
    calc
      ∑ p ∈ (z.2 i).val, log (p : ℝ) ≤
          ∑ _p ∈ (z.2 i).val, (log P + t i / s) := sum_le_sum (fun p hp => hpos i p ((pos_selection E h z i).1 hp))
      _ = _ := by simp [(pos_selection E h z i).2]; ring
  have hid : (∑ i, (h i : ℝ) * (log P + t i / s)) - (∑ i, (h i : ℝ) * (log P - t i / s)) = (2 / s) * ∑ i, t i * (h i : ℝ) := by
    rw [← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [value, Nat.cast_prod, log_prod hne, support, sum_union hd,
    sum_sdiff_eq_sub (removed_subset E h z)]
  linarith
/-- A feasible prime-exchange family gives a lower bound for the literal tail. -/
theorem balanced_exchange_bound (E : ExchangeSystem ι) (h : ι → ℕ) (P D s : ℝ) (t : ι → ℝ) (lambda x : ℝ) (hbase : ∑ p ∈ E.base, log (p : ℝ) ≤ P - D) (hneg : ∀ i p, p ∈ E.neg i → log P - t i / s ≤ log (p : ℝ)) (hpos : ∀ i p, p ∈ E.pos i → log (p : ℝ) ≤ log P + t i / s) (hbudget : (2 / s) * ∑ i, t i * (h i : ℝ) ≤ D) (hthreshold : threshold lambda x < (E.base.card : ℝ)) (hP : P ≤ log x) (hx : 0 < x) : (∏ i, (E.neg i).card.choose (h i) * (E.pos i).card.choose (h i)) ≤ tailCount lambda x := by
  classical
  have hinj : Function.Injective (support E h) := by
    intro z w he
    exact exchange_value_injective E h (congrArg (fun S : Finset ℕ => ∏ p ∈ S, p) he)
  have hb := prime_family_bound lambda x (univ.image (support E h)) ?_ ?_ ?_ hx
  · simpa only [card_image_of_injective _ hinj, card_univ, card_exchange_choices] using hb
  · intro S hS p hp
    obtain ⟨z, _, rfl⟩ := mem_image.mp hS
    exact support_prime E h z p hp
  · intro S hS
    obtain ⟨z, _, rfl⟩ := mem_image.mp hS
    have ho := omega_exchange_value E h z
    rw [value, omega_prime_product (support_prime E h z)] at ho
    simpa only [ho] using hthreshold
  · intro S hS
    obtain ⟨z, _, rfl⟩ := mem_image.mp hS
    have he := log_exchange_value_le E h P D s t hbase hneg hpos z
    have hlog : log (value E h z : ℝ) = ∑ p ∈ support E h z, log (p : ℝ) := by
      rw [value, Nat.cast_prod, log_prod]
      intro p hp
      exact_mod_cast (support_prime E h z p hp).ne_zero
    rw [hlog] at he
    linarith
/-- The literal half-open logarithmic boxes satisfy the exchange cost hypotheses. -/
theorem logarithmic_exchange_bound (n : ℕ) (P s : ℝ) (node : ℕ → ℝ) (R : Finset ℕ) (hP : 0 < P) (hs : 0 < s) (hmono : Monotone node) (hzero : node 0 = 0) (hfar : 3 * P / 4 ≤ P * exp (-node n / s)) (hR : R ⊆ primeInterval (P / 2) (3 * P / 4)) (h : Fin n → ℕ) (D lambda x : ℝ) (hbase : ∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ) ≤ P - D) (hbudget : (2 / s) * ∑ i : Fin n, node (i.val + 1) * (h i : ℝ) ≤ D) (hthreshold : threshold lambda x < ((Nat.primesLE ⌊P⌋₊ \ R).card : ℝ)) (hPx : P ≤ log x) (hx : 0 < x) : (∏ i : Fin n, (primeInterval (P * exp (-node (i.val + 1) / s)) (P * exp (-node i.val / s))).card.choose (h i) * (primeInterval (P * exp (node i.val / s)) (P * exp (node (i.val + 1) / s))).card.choose (h i)) ≤ tailCount lambda x := by
  let E := logarithmicExchangeSystem n P s node R hP hs hmono hzero hfar hR
  apply balanced_exchange_bound E h P D s (fun i => node (i.val + 1)) lambda x
    hbase ?_ ?_ hbudget hthreshold hPx hx
  · intro i p hp
    obtain ⟨hp, _⟩ := Finset.mem_filter.mp hp
    have hlo := (Finset.mem_Ioc.mp hp).1
    have he : 0 < P * exp (-node (i.val + 1) / s) := mul_pos hP (exp_pos _)
    have hh := log_le_log he ((Nat.floor_lt he.le).mp hlo).le
    rw [log_mul hP.ne' (exp_ne_zero _), log_exp] at hh
    simpa only [neg_div, sub_eq_add_neg] using hh
  · intro i p hp
    obtain ⟨hp, hpprime⟩ := Finset.mem_filter.mp hp
    have hhi := (Finset.mem_Ioc.mp hp).2
    have he : 0 ≤ P * exp (node (i.val + 1) / s) := by positivity
    have hh := log_le_log (by exact_mod_cast hpprime.pos : 0 < (p : ℝ))
      ((Nat.le_floor_iff he).mp hhi)
    rwa [log_mul hP.ne' (exp_ne_zero _), log_exp] at hh
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
/-- The three factorial terms of the real-endpoint prime count. -/
def countingThreeTerms (P : ℝ) : ℝ := P / log P + P / log P ^ 2 + 2 * P / log P ^ 3
/-- The residual after the first three terms has fourth coefficient six. -/
theorem prime_counting_three_terms : Tendsto (fun P : ℝ => (primeCount P - countingThreeTerms P) / (P / log P ^ 4)) atTop (𝓝 6) := by
  have hi : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop 1
  have h := (prime_counting_four_terms.mul hi).add_const 6
  norm_num only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  dsimp only [countingPolynomial, countingThreeTerms]
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring
private lemma prime_counting_error_limit : Tendsto (fun P : ℝ => (primeCount P - P / log P) / (P / log P ^ 2)) atTop (𝓝 1) := by
  apply D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff.second_order_count.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring
/-- A uniform eventual error bound for comparison on moving prime intervals. -/
theorem prime_counting_error_bound : ∀ᶠ P : ℝ in atTop, |primeCount P - P / log P| ≤ 3 * (P / log P ^ 2) := by
  have h := prime_counting_error_limit.abs
  norm_num only [abs_one] at h
  filter_upwards [h.eventually_lt_const (by norm_num : (1 : ℝ) < 3),
    eventually_gt_atTop (1 : ℝ)] with P hbound hP
  have hscale : 0 < P / log P ^ 2 := div_pos (by linarith) (sq_pos_of_pos (log_pos hP))
  rw [abs_div, abs_of_pos hscale] at hbound
  exact ((div_lt_iff₀ hscale).mp hbound).le
/-- The budget after removing the second distinct-prime threshold at cutoff P. -/
def budget (P : ℝ) : ℝ := P - Chebyshev.theta P + (primeCount P - (P / log P + P / log P ^ 2)) * log P
/-- The first two prime-counting coefficients cancel exactly, leaving two. -/
theorem budget_limit : Tendsto (fun P : ℝ => budget P / (P / log P ^ 2)) atTop (𝓝 2) := by
  have hi : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop 1
  have hθ := (theta_error_log_power 2).tendsto_div_nhds_zero
  have h := hθ.neg.add ((prime_counting_three_terms.mul hi).add_const 2)
  norm_num only [neg_zero, mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
  dsimp only [budget, countingThreeTerms]
  field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring
/-- The real prime count has almost constant density on the central interval. The bound is uniform in the moving endpoint t, including both boundaries. -/
theorem central_prime_counting_bound : ∀ᶠ P : ℝ in atTop, ∀ t ∈ Icc (P / 2) (2 * P), |primeCount t - t / log P| ≤ 28 * (P / log P ^ 2) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp prime_counting_error_bound
  filter_upwards [eventually_ge_atTop (2 * max X 1),
    tendsto_log_atTop.eventually_ge_atTop 2] with P hP hlogP
  intro t ht
  have hP0 : 0 < P := by linarith [le_max_right X 1]
  have ht0 : 0 < t := by linarith [ht.1]
  have htX : X ≤ t := by linarith [le_max_left X 1, ht.1]
  have hl0 : 0 < log P := by linarith
  have hlog2 : log (2 : ℝ) < 1 := by linarith [log_two_lt_d9]
  have hloglo : log P - 1 ≤ log t := by
    have h := log_le_log (by positivity : 0 < P / 2) ht.1
    rw [log_div hP0.ne' (by norm_num : (2 : ℝ) ≠ 0)] at h
    linarith
  have hloghi : log t ≤ log P + 1 := by
    have h := log_le_log ht0 ht.2
    rw [log_mul (by norm_num : (2 : ℝ) ≠ 0) hP0.ne'] at h
    linarith
  have htlog : 0 < log t := by linarith
  have hhalf : log P / 2 ≤ log t := by linarith
  have hsq : log P ^ 2 / 4 ≤ log t ^ 2 := by nlinarith
  have hprod : log P ^ 2 / 2 ≤ log t * log P := by nlinarith
  have habs : |log P - log t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have herror : |primeCount t - t / log t| ≤ 24 * (P / log P ^ 2) := by
    refine (hX t htX).trans ?_
    calc
      3 * (t / log t ^ 2) ≤ 3 * ((2 * P) / (log P ^ 2 / 4)) := by
        gcongr
        exact ht.2
      _ = 24 * (P / log P ^ 2) := by ring
  have hchange : |t / log t - t / log P| ≤ 4 * (P / log P ^ 2) := by
    have hid : t / log t - t / log P = t * (log P - log t) / (log t * log P) := by
      field_simp [htlog.ne', hl0.ne'] <;> ring
    rw [hid, abs_div, abs_mul, abs_of_pos ht0,
      abs_of_pos (mul_pos htlog hl0)]
    calc
      t * |log P - log t| / (log t * log P) ≤
          (2 * P) / (log P ^ 2 / 2) := by
        apply div_le_div₀ (by positivity)
        · simpa only [mul_one] using
            mul_le_mul ht.2 habs (abs_nonneg _) (by positivity : 0 ≤ 2 * P)
        · positivity
        · exact hprod
      _ = 4 * (P / log P ^ 2) := by ring
  calc
    |primeCount t - t / log P| ≤
        |primeCount t - t / log t| + |t / log t - t / log P| := abs_sub_le _ _ _
    _ ≤ 24 * (P / log P ^ 2) + 4 * (P / log P ^ 2) := add_le_add herror hchange
    _ = _ := by ring
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper
/-- The localized weight around the moving prime cutoff. -/
def weight (P s t : ℝ) : ℝ := log (1 + exp (-s * |log (t / P)|))
/-- The finite prime remainder at the integer counting endpoint. -/
def remainder (P s x : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊x⌋₊, weight P s p
private lemma softplus_split (v : ℝ) : log (1 + exp v) = max v 0 + log (1 + exp (-|v|)) := by
  by_cases hv : 0 ≤ v
  · rw [abs_of_nonneg hv, max_eq_left hv]
    have h : 1 + exp v = exp v * (1 + exp (-v)) := by
      rw [mul_add, mul_one, ← exp_add]
      simp
      ring
    rw [h, log_mul (exp_ne_zero _) (by positivity), log_exp]
  · have hv' : v ≤ 0 := (lt_of_not_ge hv).le
    rw [abs_of_nonpos hv', max_eq_right hv', neg_neg, zero_add]
private lemma logWeight_split {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) (hs : 0 ≤ s) : log (1 + P ^ s * t ^ (-s)) = (if t ≤ P then s * (log P - log t) else 0) + weight P s t := by
  have he : P ^ s * t ^ (-s) = exp (s * (log P - log t)) := by
    rw [rpow_def_of_pos hP, rpow_def_of_pos ht, ← exp_add]
    congr 1
    ring
  have hl : log (t / P) = log t - log P := log_div ht.ne' hP.ne'
  rw [he, softplus_split]
  have hab : |s * (log P - log t)| = s * |log (t / P)| := by
    rw [abs_mul, abs_of_nonneg hs, hl, ← abs_neg (log t - log P)]
    congr 2
    ring
  rw [hab]
  dsimp only [weight]
  rw [neg_mul]
  congr 1
  split_ifs with h
  · exact max_eq_left (mul_nonneg hs (sub_nonneg.mpr (log_le_log ht h)))
  · exact max_eq_right
      (mul_nonpos_of_nonneg_of_nonpos hs
        (sub_nonpos.mpr (log_le_log hP (le_of_not_ge h))))
/-- The moving remainder is nonnegative. -/
theorem weight_nonneg (P s t : ℝ) : 0 ≤ weight P s t := by
  apply log_nonneg
  have := exp_nonneg (-s * |log (t / P)|)
  linarith
theorem weight_continuousOn {P s a b : ℝ} (hP : 0 < P) (ha : 0 < a) : ContinuousOn (weight P s) (Set.Icc a b) := by
  intro t ht
  have ht0 : 0 < t := ha.trans_le ht.1
  have hl : ContinuousAt (fun u : ℝ => log (u / P)) t := (continuousAt_id.div_const P).log (div_pos ht0 hP).ne'
  have he : ContinuousAt (fun u : ℝ => 1 + exp (-s * |log (u / P)|)) t := continuousAt_const.add ((hl.abs.const_mul (-s)).rexp)
  exact (he.log (by positivity)).continuousWithinAt
/-- The smooth extension of the weight on the left of its peak. -/
def leftWeight (P s t : ℝ) : ℝ := logWeight s (P ^ s) t - s * (log P - log t)
theorem leftWeight_eq_weight {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) (hs : 0 ≤ s) (htP : t ≤ P) : leftWeight P s t = weight P s t := by
  have h := logWeight_split hP ht hs
  rw [if_pos htP] at h
  dsimp only [leftWeight, logWeight]
  rw [div_eq_mul_inv, ← rpow_neg ht.le]
  linarith only [h]
theorem rightWeight_eq_weight {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) (hs : 0 ≤ s) (hPt : P ≤ t) : logWeight s (P ^ s) t = weight P s t := by
  rcases hPt.eq_or_lt with rfl | hPt
  · have h := logWeight_split hP hP hs
    simp only [le_refl, ↓reduceIte, sub_self, mul_zero, zero_add] at h
    dsimp only [logWeight]
    rwa [div_eq_mul_inv, ← rpow_neg hP.le]
  · have h := logWeight_split hP ht hs
    rw [if_neg hPt.not_ge, zero_add] at h
    dsimp only [logWeight]
    rwa [div_eq_mul_inv, ← rpow_neg ht.le]
theorem leftWeight_deriv {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) : HasDerivAt (leftWeight P s) (s / t - abelKernel s (P ^ s) t) t := by
  have h := (logWeight_deriv (s := s) (rpow_pos_of_pos hP s) ht).sub
    (((hasDerivAt_const t (log P)).sub (hasDerivAt_log ht.ne')).const_mul s)
  convert h using 1
  · rfl
  · simp only [div_eq_mul_inv]
    ring
theorem leftWeight_at_cutoff {P s : ℝ} (hP : 0 < P) : leftWeight P s P = log 2 := by
  dsimp only [leftWeight, logWeight]
  rw [div_self (rpow_pos_of_pos hP s).ne']
  norm_num
theorem rightWeight_at_cutoff {P s : ℝ} (hP : 0 < P) : logWeight s (P ^ s) P = log 2 := by
  dsimp only [logWeight]
  rw [div_self (rpow_pos_of_pos hP s).ne']
  norm_num
theorem leftWeight_deriv_nonneg {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) (hs : 0 ≤ s) : 0 ≤ s / t - abelKernel s (P ^ s) t := by
  have htp : 0 < t ^ s := rpow_pos_of_pos ht s
  have hPP : 0 < P ^ s := rpow_pos_of_pos hP s
  dsimp only [abelKernel]
  apply sub_nonneg.mpr
  apply (div_le_div_iff₀ (by positivity : 0 < t * (t ^ s + P ^ s)) ht).mpr
  nlinarith [mul_nonneg hs htp.le]
/-- The localized prime sum is the exact remainder after subtracting the prime-counting ramp, with no asymptotic or endpoint error. -/
theorem prime_weight_split {P s x : ℝ} (hP : 0 < P) (hPx : P ≤ x) (hs : 0 ≤ s) : (∑ p ∈ Nat.primesLE ⌊x⌋₊, log (1 + P ^ s * (p : ℝ) ^ (-s))) = s * ((Nat.primeCounting ⌊P⌋₊ : ℝ) * log P - Chebyshev.theta P) + remainder P s x := by
  classical
  have hsub : Nat.primesLE ⌊P⌋₊ ⊆ Nat.primesLE ⌊x⌋₊ := by
    intro p hp
    obtain ⟨hpP, hpp⟩ := Nat.mem_primesLE.mp hp
    exact Nat.mem_primesLE.mpr ⟨hpP.trans (Nat.floor_le_floor hPx), hpp⟩
  have hfilter : (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ => (p : ℝ) ≤ P) = Nat.primesLE ⌊P⌋₊ := by
    ext p
    constructor
    · intro hp
      obtain ⟨hp, hpP⟩ := mem_filter.mp hp
      exact Nat.mem_primesLE.mpr
        ⟨(Nat.le_floor_iff hP.le).mpr hpP, (Nat.mem_primesLE.mp hp).2⟩
    · intro hp
      exact mem_filter.mpr ⟨hsub hp,
        (Nat.le_floor_iff hP.le).mp (Nat.mem_primesLE.mp hp).1⟩
  have heq : (∑ p ∈ Nat.primesLE ⌊x⌋₊, (if (p : ℝ) ≤ P then s * (log P - log p) else 0)) = s * ((Nat.primeCounting ⌊P⌋₊ : ℝ) * log P - Chebyshev.theta P) := by
    rw [← sum_filter, hfilter, ← mul_sum, sum_sub_distrib,
      sum_const, nsmul_eq_mul, Nat.primesLE_card_eq_primeCounting,
      Chebyshev.theta_eq_sum_primesLE]
  calc
    _ = ∑ p ∈ Nat.primesLE ⌊x⌋₊,
        ((if (p : ℝ) ≤ P then s * (log P - log p) else 0) + weight P s p) := by
      apply sum_congr rfl
      intro p hp
      exact logWeight_split hP
        (by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos) hs
    _ = _ := by rw [sum_add_distrib, heq]; rfl
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
private lemma prime_cdf (t : ℝ) : (∑ p ∈ Finset.Icc 0 ⌊t⌋₊, if p.Prime then (1 : ℝ) else 0) = primeCount t := by
  simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  rw [← Nat.primesLE_eq_filter_Icc_zero, Nat.primesLE_card_eq_primeCounting]
  rfl
/-- A finite prime quadrature bound keeps both endpoint discrepancies and the total variation of the actual weight. -/
theorem prime_quadrature_upper {a b C E : ℝ} {f d : ℝ → ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E) (hd : ContinuousOn d (Set.Icc a b)) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (d t) t) (hcount : ∀ t ∈ Set.Icc a b, |primeCount t - C * t| ≤ E) : (∑ p ∈ primeInterval a b, f p) ≤ C * (∫ t in a..b, f t) + E * (|f a| + |f b| + ∫ t in a..b, |d t|) := by
  classical
  have hfc : ContinuousOn f (Set.Icc a b) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hdi : IntegrableOn d (Set.Icc a b) := hd.integrableOn_Icc; have hfi : IntervalIntegrable f volume a b := hfc.intervalIntegrable_of_Icc hab; have hdt : IntegrableOn (fun t => d t * t) (Set.Icc a b) := (hd.mul continuousOn_id).integrableOn_Icc
  have hdc : IntegrableOn (fun t => d t * primeCount t) (Set.Icc a b) := by
    have h := integrableOn_mul_sum_Icc (fun p : ℕ => if p.Prime then (1 : ℝ) else 0) ha hdi (m := 0)
    simp_rw [prime_cdf] at h
    exact h
  have herror : IntegrableOn (fun t => d t * (primeCount t - C * t)) (Set.Ioc a b) := by
    have h := hdc.sub (hdt.const_mul C)
    convert h.mono_set Set.Ioc_subset_Icc_self using 1
    ext t
    dsimp only [Pi.sub_apply]
    ring
  have habs : IntegrableOn (fun t => E * |d t|) (Set.Ioc a b) := by
    have h : IntegrableOn (fun t => E * |d t|) (Set.Icc a b) := hdi.abs.const_mul E
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hbound : |∫ t in Set.Ioc a b, d t * (primeCount t - C * t)| ≤ E * (∫ t in a..b, |d t|) := by
    calc
      _ ≤ ∫ t in Set.Ioc a b, |d t * (primeCount t - C * t)| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Set.Ioc a b, E * |d t| := by
        apply setIntegral_mono_on herror.abs habs measurableSet_Ioc
        intro t ht
        rw [abs_mul, mul_comm E]
        exact mul_le_mul_of_nonneg_left (hcount t ⟨ht.1.le, ht.2⟩) (abs_nonneg _)
      _ = _ := by rw [integral_const_mul, ← intervalIntegral.integral_of_le hab]
  have hFTC : (∫ t in a..b, f t + d t * t) = b * f b - a * f a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t * f t) _ (hfi.add ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hdt))
    intro t ht
    rw [uIcc_of_le hab] at ht
    convert (hasDerivAt_id t).mul (hf t ht) using 1
    · rfl
    · simp only [id_eq, one_mul]
      ring
  have hlinear : C * (∫ t in a..b, f t) = f b * (C * b) - f a * (C * a) - ∫ t in Set.Ioc a b, d t * (C * t) := by
    rw [intervalIntegral.integral_add hfi ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hdt)] at hFTC
    have he : (∫ t in Set.Ioc a b, d t * (C * t)) = C * (∫ t in a..b, d t * t) := by
      rw [intervalIntegral.integral_of_le hab, ← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by ring)
    rw [he]
    have hcFTC := congrArg (fun r : ℝ => C * r) hFTC
    nlinarith only [hcFTC]
  have hAbel := sum_mul_eq_sub_sub_integral_mul (fun p : ℕ => if p.Prime then (1 : ℝ) else 0) ha hab (fun t ht => (hf t ht).differentiableAt) (hdi.congr_fun (fun t ht => (hf t ht).deriv.symm) measurableSet_Icc)
  simp_rw [prime_cdf] at hAbel
  have hsum : (∑ p ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f p * (if p.Prime then 1 else 0)) = ∑ p ∈ primeInterval a b, f p := by simp [primeInterval, sum_filter, mul_ite]
  rw [hsum] at hAbel
  have hid : (∑ p ∈ primeInterval a b, f p) - C * (∫ t in a..b, f t) = f b * (primeCount b - C * b) - f a * (primeCount a - C * a) - ∫ t in Set.Ioc a b, d t * (primeCount t - C * t) := by
    rw [hAbel, hlinear]
    have hdreplace : (fun t => deriv f t * primeCount t) =ᵐ[volume.restrict (Set.Ioc a b)] (fun t => d t * primeCount t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [(hf t ⟨ht.1.le, ht.2⟩).deriv]
    have hci : IntegrableOn (fun t => d t * (C * t)) (Set.Ioc a b) := by
      have h : IntegrableOn (fun t => C * (d t * t)) (Set.Icc a b) := hdt.const_mul C
      convert h.mono_set Set.Ioc_subset_Icc_self using 1
      ext t
      ring
    have hsplit : (∫ t in Set.Ioc a b, d t * (primeCount t - C * t)) = (∫ t in Set.Ioc a b, d t * primeCount t) - ∫ t in Set.Ioc a b, d t * (C * t) := by
      rw [← integral_sub (hdc.mono_set Set.Ioc_subset_Icc_self) hci]
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => by ring)
    rw [integral_congr_ae hdreplace, hsplit]
    ring
  have hb : |f b * (primeCount b - C * b)| ≤ |f b| * E := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hcount b ⟨hab, le_rfl⟩) (abs_nonneg _)
  have ha' : |f a * (primeCount a - C * a)| ≤ |f a| * E := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hcount a ⟨le_rfl, hab⟩) (abs_nonneg _)
  have habound : (∑ p ∈ primeInterval a b, f p) - C * (∫ t in a..b, f t) ≤ E * (|f a| + |f b| + ∫ t in a..b, |d t|) := by
    rw [hid]
    calc
      _ ≤ |f b * (primeCount b - C * b)| + |f a * (primeCount a - C * a)| +
          |∫ t in Set.Ioc a b, d t * (primeCount t - C * t)| := by
        linarith [le_abs_self (f b * (primeCount b - C * b)), neg_le_abs (f a * (primeCount a - C * a)), neg_le_abs (∫ t in Set.Ioc a b, d t * (primeCount t - C * t))]
      _ ≤ |f b| * E + |f a| * E + E * (∫ t in a..b, |d t|) := by gcongr
      _ = _ := by ring
  linarith only [habound]
private lemma prime_quadrature_increasing {a b C E : ℝ} {f d : ℝ → ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E) (hd : ContinuousOn d (Set.Icc a b)) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (d t) t) (hcount : ∀ t ∈ Set.Icc a b, |primeCount t - C * t| ≤ E) (hdpos : ∀ t ∈ Set.Icc a b, 0 ≤ d t) (hfa : 0 ≤ f a) (hfb : 0 ≤ f b) : (∑ p ∈ primeInterval a b, f p) ≤ C * (∫ t in a..b, f t) + 2 * E * f b := by
  have hi : IntervalIntegrable d volume a b := hd.intervalIntegrable_of_Icc hab; have hFTC : (∫ t in a..b, |d t|) = f b - f a := by
    calc
      _ = ∫ t in a..b, d t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        exact abs_of_nonneg (hdpos t ht)
      _ = _ := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hf t (by rwa [uIcc_of_le hab] at ht)) hi
  have h := prime_quadrature_upper ha hab hE hd hf hcount
  rw [abs_of_nonneg hfa, abs_of_nonneg hfb, hFTC] at h
  convert h using 1 <;> ring
private lemma prime_quadrature_decreasing {a b C E : ℝ} {f d : ℝ → ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hE : 0 ≤ E) (hd : ContinuousOn d (Set.Icc a b)) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (d t) t) (hcount : ∀ t ∈ Set.Icc a b, |primeCount t - C * t| ≤ E) (hdneg : ∀ t ∈ Set.Icc a b, d t ≤ 0) (hfa : 0 ≤ f a) (hfb : 0 ≤ f b) : (∑ p ∈ primeInterval a b, f p) ≤ C * (∫ t in a..b, f t) + 2 * E * f a := by
  have hi : IntervalIntegrable d volume a b := hd.intervalIntegrable_of_Icc hab; have hFTC : (∫ t in a..b, |d t|) = f a - f b := by
    calc
      _ = ∫ t in a..b, -d t := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hab] at ht
        exact abs_of_nonpos (hdneg t ht)
      _ = _ := by
        rw [intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hf t (by rwa [uIcc_of_le hab] at ht)) hi]
        ring
  have h := prime_quadrature_upper ha hab hE hd hf hcount
  rw [abs_of_nonneg hfa, abs_of_nonneg hfb, hFTC] at h
  convert h using 1 <;> ring
/-- The central weight quadrature error is uniform in the moving sharpness parameter. In particular the error does not acquire a factor s. -/
theorem central_prime_weight_upper : ∀ᶠ P : ℝ in atTop, ∀ s : ℝ, 0 ≤ s → (∑ p ∈ primeInterval (P / 2) (2 * P), Exchange.weight P s p) ≤ (∫ t in (P / 2)..(2 * P), Exchange.weight P s t) / log P + 112 * log 2 * (P / log P ^ 2) := by
  filter_upwards [Exchange.central_prime_counting_bound, eventually_gt_atTop (1 : ℝ)] with P hcount hP
  intro s hs
  have hP0 : 0 < P := by linarith
  have hhalf : 0 < P / 2 := by positivity
  have hleft : P / 2 ≤ P := by linarith
  have hright : P ≤ 2 * P := by linarith
  let E : ℝ := 28 * (P / log P ^ 2)
  have hE : 0 ≤ E := by dsimp [E]; positivity
  let z : ℝ := P ^ s
  have hz : 0 < z := rpow_pos_of_pos hP0 s
  let d : ℝ → ℝ := fun t => s / t - OmegaTailUpper.abelKernel s z t
  have hdc : ContinuousOn d (Set.Icc (P / 2) P) := by
    apply ContinuousOn.sub
    · exact continuousOn_const.div continuousOn_id
        (fun t ht => (hhalf.trans_le ht.1).ne')
    · exact OmegaTailUpper.abelKernel_continuousOn hz hhalf
  have hfc : ContinuousOn (Exchange.leftWeight P s) (Set.Icc (P / 2) P) := fun t ht => (Exchange.leftWeight_deriv hP0 (hhalf.trans_le ht.1)).continuousAt.continuousWithinAt
  have hrightc : ContinuousOn (OmegaTailUpper.logWeight s z) (Set.Icc P (2 * P)) := fun t ht => (OmegaTailUpper.logWeight_deriv hz (hP0.trans_le ht.1)).continuousAt.continuousWithinAt
  have hfnonneg (t : ℝ) (ht : t ∈ Set.Icc (P / 2) P) : 0 ≤ Exchange.leftWeight P s t := by
    rw [Exchange.leftWeight_eq_weight hP0 (hhalf.trans_le ht.1) hs ht.2]
    exact Exchange.weight_nonneg _ _ _
  have hgnonneg (t : ℝ) (ht : t ∈ Set.Icc P (2 * P)) : 0 ≤ OmegaTailUpper.logWeight s z t := by
    rw [show z = P ^ s by rfl, Exchange.rightWeight_eq_weight hP0 (hP0.trans_le ht.1) hs ht.1]
    exact Exchange.weight_nonneg _ _ _
  have hL := prime_quadrature_increasing (C := 1 / log P) hhalf.le hleft hE hdc (fun t ht => Exchange.leftWeight_deriv hP0 (hhalf.trans_le ht.1)) (fun t ht => by
      simpa only [one_div_mul_eq_div, E] using hcount t ⟨ht.1, ht.2.trans hright⟩)
    (fun t ht => Exchange.leftWeight_deriv_nonneg hP0 (hhalf.trans_le ht.1) hs)
    (hfnonneg _ ⟨le_rfl, hleft⟩) (hfnonneg _ ⟨hleft, le_rfl⟩)
  have hR := prime_quadrature_decreasing (C := 1 / log P) hP0.le hright hE (OmegaTailUpper.abelKernel_continuousOn hz hP0).neg (fun t ht => OmegaTailUpper.logWeight_deriv hz (hP0.trans_le ht.1)) (fun t ht => by
      simpa only [one_div_mul_eq_div, E] using hcount t ⟨hleft.trans ht.1, ht.2⟩)
    (fun t ht => neg_nonpos.mpr (by
      have ht0 : 0 < t := hP0.trans_le ht.1; have htp : 0 < t ^ s := rpow_pos_of_pos ht0 s
      dsimp only [OmegaTailUpper.abelKernel]
      positivity))
    (hgnonneg _ ⟨le_rfl, hright⟩) (hgnonneg _ ⟨hright, le_rfl⟩)
  rw [Exchange.leftWeight_at_cutoff hP0] at hL
  rw [show z = P ^ s by rfl, Exchange.rightWeight_at_cutoff hP0] at hR
  have hsumL : (∑ p ∈ primeInterval (P / 2) P, Exchange.leftWeight P s p) = ∑ p ∈ primeInterval (P / 2) P, Exchange.weight P s p := by
    apply sum_congr rfl
    intro p hp
    have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1; have hpp := (Finset.mem_filter.mp hp).2
    exact Exchange.leftWeight_eq_weight hP0 (by exact_mod_cast hpp.pos) hs ((Nat.le_floor_iff hP0.le).mp hi.2)
  have hsumR : (∑ p ∈ primeInterval P (2 * P), OmegaTailUpper.logWeight s z p) = ∑ p ∈ primeInterval P (2 * P), Exchange.weight P s p := by
    apply sum_congr rfl
    intro p hp
    have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1; have hpp := (Finset.mem_filter.mp hp).2
    exact Exchange.rightWeight_eq_weight hP0 (by exact_mod_cast hpp.pos) hs ((Nat.floor_lt hP0.le).mp hi.1).le
  have hIL : (∫ t in (P / 2)..P, Exchange.leftWeight P s t) = ∫ t in (P / 2)..P, Exchange.weight P s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hleft] at ht
    exact Exchange.leftWeight_eq_weight hP0 (hhalf.trans_le ht.1) hs ht.2
  have hIR : (∫ t in P..(2 * P), OmegaTailUpper.logWeight s z t) = ∫ t in P..(2 * P), Exchange.weight P s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hright] at ht
    exact Exchange.rightWeight_eq_weight hP0 (hP0.trans_le ht.1) hs ht.1
  rw [hsumL, hIL] at hL
  rw [hsumR, hIR] at hR
  have hsum : (∑ p ∈ primeInterval (P / 2) P, Exchange.weight P s p) + (∑ p ∈ primeInterval P (2 * P), Exchange.weight P s p) = ∑ p ∈ primeInterval (P / 2) (2 * P), Exchange.weight P s p := by
    simp only [primeInterval, sum_filter]
    exact Finset.sum_Ioc_consecutive _ (Nat.floor_le_floor hleft) (Nat.floor_le_floor hright)
  have hInt := intervalIntegral.integral_add_adjacent_intervals ((Exchange.weight_continuousOn (s := s) hP0 hhalf).intervalIntegrable_of_Icc (μ := volume) hleft) ((Exchange.weight_continuousOn (s := s) hP0 hP0).intervalIntegrable_of_Icc (μ := volume) hright); have h := add_le_add hL hR
  rw [hsum] at h
  have heq : (1 / log P) * (∫ t in (P / 2)..P, Exchange.weight P s t) + 2 * E * log 2 + ((1 / log P) * (∫ t in P..(2 * P), Exchange.weight P s t) + 2 * E * log 2) = (∫ t in (P / 2)..(2 * P), Exchange.weight P s t) / log P + 112 * log 2 * (P / log P ^ 2) := by
    rw [← hInt]
    dsimp only [E]
    ring
  exact h.trans_eq heq
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper Exchange
private def kernel (P s t : ℝ) : ℝ := s * P ^ s / (t ^ s + P ^ s)
private lemma kernel_integrable {P s : ℝ} (hP : 0 < P) (hs : 1 < s) : IntegrableOn (kernel P s) (Ioi 0) := (power_kernel_integral hs (rpow_pos_of_pos hP s)).1
private lemma kernel_interval {P s a b : ℝ} (hP : 0 < P) (hs : 1 < s) (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable (kernel P s) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
  exact (kernel_integrable hP hs).mono_set (fun t ht => ha.trans_lt ht.1)
private lemma left_integral {P s a : ℝ} (hP : 0 < P) (hs : 0 ≤ s) (ha : 0 < a) (haP : a ≤ P) : (∫ t in a..P, weight P s t) = P * log 2 - a * weight P s a - s * (P - a) + ∫ t in a..P, kernel P s t := by
  have hPP : 0 < P ^ s := rpow_pos_of_pos hP s; have hcontL : ContinuousOn (leftWeight P s) (Icc a P) := by
    intro t ht; exact (leftWeight_deriv hP (ha.trans_le ht.1)).continuousAt.continuousWithinAt
  have hcontK : ContinuousOn (kernel P s) (Icc a P) := by
    intro t ht
    have ht0 := ha.trans_le ht.1
    exact (continuousAt_const.div ((hasDerivAt_rpow_const (Or.inl ht0.ne')).continuousAt.add continuousAt_const) (by positivity : t ^ s + P ^ s ≠ 0)).continuousWithinAt
  have hli := hcontL.intervalIntegrable_of_Icc (μ := volume) haP; have hki := hcontK.intervalIntegrable_of_Icc (μ := volume) haP; have hFTC : (∫ t in a..P, leftWeight P s t - kernel P s t) = (P * leftWeight P s P - s * P) - (a * leftWeight P s a - s * a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t * leftWeight P s t - s * t) _ (hli.sub hki)
    intro t ht
    rw [uIcc_of_le haP] at ht
    have ht0 : 0 < t := ha.trans_le ht.1; have hd := ((hasDerivAt_id t).mul (leftWeight_deriv (s := s) hP ht0)).sub ((hasDerivAt_id t).const_mul s)
    convert hd using 1
    · rfl
    · dsimp only [kernel, abelKernel, id_eq]
      field_simp [ht0.ne', (by positivity : t ^ s + P ^ s ≠ 0)] <;> ring
  have heq : (∫ t in a..P, leftWeight P s t) = ∫ t in a..P, weight P s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le haP] at ht
    exact leftWeight_eq_weight hP (ha.trans_le ht.1) hs ht.2
  rw [intervalIntegral.integral_sub hli hki, heq, leftWeight_at_cutoff hP, leftWeight_eq_weight hP ha hs haP] at hFTC
  linarith
private lemma right_integral {P s b : ℝ} (hP : 0 < P) (hs : 0 ≤ s) (hPb : P ≤ b) : (∫ t in P..b, weight P s t) = b * weight P s b - P * log 2 + ∫ t in P..b, kernel P s t := by
  have hPP : 0 < P ^ s := rpow_pos_of_pos hP s; have hcontR : ContinuousOn (logWeight s (P ^ s)) (Icc P b) := by
    intro t ht; exact (logWeight_deriv hPP (hP.trans_le ht.1)).continuousAt.continuousWithinAt
  have hcontK : ContinuousOn (kernel P s) (Icc P b) := by
    intro t ht
    have ht0 := hP.trans_le ht.1
    exact (continuousAt_const.div ((hasDerivAt_rpow_const (Or.inl ht0.ne')).continuousAt.add continuousAt_const) (by positivity : t ^ s + P ^ s ≠ 0)).continuousWithinAt
  have hri := hcontR.intervalIntegrable_of_Icc (μ := volume) hPb; have hki := hcontK.intervalIntegrable_of_Icc (μ := volume) hPb; have hFTC : (∫ t in P..b, logWeight s (P ^ s) t - kernel P s t) = b * logWeight s (P ^ s) b - P * logWeight s (P ^ s) P := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t * logWeight s (P ^ s) t) _ (hri.sub hki)
    intro t ht
    rw [uIcc_of_le hPb] at ht
    have ht0 : 0 < t := hP.trans_le ht.1; have hd := (hasDerivAt_id t).mul (logWeight_deriv (s := s) hPP ht0)
    convert hd using 1
    · rfl
    · dsimp only [kernel, abelKernel, id_eq]
      field_simp [ht0.ne', (by positivity : t ^ s + P ^ s ≠ 0)] <;> ring
  have heq : (∫ t in P..b, logWeight s (P ^ s) t) = ∫ t in P..b, weight P s t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hPb] at ht
    exact rightWeight_eq_weight hP (hP.trans_le ht.1) hs ht.1
  rw [intervalIntegral.integral_sub hri hki, heq, rightWeight_at_cutoff hP, rightWeight_eq_weight hP (hP.trans_le hPb) hs hPb] at hFTC
  linarith
private lemma weight_interval {P s a b : ℝ} (hP : 0 < P) (hs : 0 ≤ s) (ha : 0 < a) (haP : a ≤ P) (hPb : P ≤ b) : IntervalIntegrable (weight P s) volume a b := by
  have hl : IntervalIntegrable (weight P s) volume a P := by
    have h : ContinuousOn (leftWeight P s) (Icc a P) := by
      intro t ht; exact (leftWeight_deriv hP (ha.trans_le ht.1)).continuousAt.continuousWithinAt
    apply (h.intervalIntegrable_of_Icc (μ := volume) haP).congr_uIoo
    intro t ht
    rw [uIoo_of_le haP] at ht
    exact leftWeight_eq_weight hP (ha.trans ht.1) hs ht.2.le
  have hr : IntervalIntegrable (weight P s) volume P b := by
    have h : ContinuousOn (logWeight s (P ^ s)) (Icc P b) := by
      intro t ht; exact (logWeight_deriv (rpow_pos_of_pos hP s) (hP.trans_le ht.1)).continuousAt.continuousWithinAt
    apply (h.intervalIntegrable_of_Icc (μ := volume) hPb).congr_uIoo
    intro t ht
    rw [uIoo_of_le hPb] at ht
    exact rightWeight_eq_weight hP (hP.trans ht.1) hs ht.1.le
  exact hl.trans hr
private lemma kernel_head_lower {P s : ℝ} (hP : 0 < P) (hs : 1 < s) : (P / 2) * s * (1 - (2 : ℝ) ^ (-s)) ≤ ∫ t in (0 : ℝ)..(P / 2), kernel P s t := by
  have hs0 : 0 ≤ s := (zero_lt_one.trans hs).le; have hPP : 0 < P ^ s := rpow_pos_of_pos hP s; have hq : (P / 2) ^ s = P ^ s * (2 : ℝ) ^ (-s) := by rw [div_rpow hP.le (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv, rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  have hk := kernel_interval hP hs (le_refl (0 : ℝ)) (by positivity : (0 : ℝ) ≤ P / 2); have hh : ∀ t ∈ Ioo (0 : ℝ) (P / 2), s * (1 - (2 : ℝ) ^ (-s)) ≤ kernel P s t := by
    intro t ht
    have htp : 0 < t ^ s := rpow_pos_of_pos ht.1 s; have htP : t ^ s ≤ P ^ s * (2 : ℝ) ^ (-s) := by
      rw [← hq]
      exact rpow_le_rpow ht.1.le ht.2.le hs0
    have hratio : t ^ s / (t ^ s + P ^ s) ≤ (2 : ℝ) ^ (-s) := by
      calc
        _ ≤ t ^ s / P ^ s := div_le_div_of_nonneg_left htp.le hPP (by linarith)
        _ ≤ _ := (div_le_iff₀ hPP).mpr (by nlinarith only [htP])
    have hid : kernel P s t = s * (1 - t ^ s / (t ^ s + P ^ s)) := by
      dsimp only [kernel]
      field_simp [(by positivity : t ^ s + P ^ s ≠ 0)] <;> ring
    rw [hid]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_left hratio 1) hs0
  have h := intervalIntegral.integral_mono_on_of_le_Ioo (by positivity : (0 : ℝ) ≤ P / 2) intervalIntegrable_const hk hh
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_assoc] using h
private lemma kernel_middle_upper {P s : ℝ} (hP : 0 < P) (hs : 1 < s) : (∫ t in (P / 2)..(2 * P), kernel P s t) ≤ π * P / sin (π / s) - s * (P / 2) + s * (P / 2) * (2 : ℝ) ^ (-s) := by
  have hki := kernel_integrable hP hs; have hk0 := kernel_interval hP hs (le_refl (0 : ℝ)) (by positivity : (0 : ℝ) ≤ P / 2); have hkm := kernel_interval hP hs (by positivity : (0 : ℝ) ≤ P / 2) (by linarith : P / 2 ≤ 2 * P)
  have hwhole : (∫ t in (0 : ℝ)..(2 * P), kernel P s t) ≤ ∫ t in Ioi (0 : ℝ), kernel P s t := by
    rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * P)]
    apply setIntegral_mono_set hki
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      dsimp only [kernel]
      have hs0 : 0 < s := zero_lt_one.trans hs
      positivity
    · exact Eventually.of_forall (fun t ht => ht.1)
  have heval := (power_kernel_integral hs (rpow_pos_of_pos hP s)).2; have hexp : (P ^ s) ^ (1 / s) = P := by rw [← rpow_mul hP.le, mul_one_div_cancel (by linarith : s ≠ 0), rpow_one]
  rw [hexp] at heval
  change (∫ t in Ioi (0 : ℝ), kernel P s t) = _ at heval
  rw [heval, ← intervalIntegral.integral_add_adjacent_intervals hk0 hkm] at hwhole
  have hhead := kernel_head_lower hP hs
  nlinarith only [hwhole, hhead]
/-- The central continuum mass has the exact beta-kernel correction; the two removed tails cost only an exponentially small quantity. -/
theorem central_integral_upper {P s : ℝ} (hP : 0 < P) (hs : 1 < s) : (∫ t in (P / 2)..(2 * P), weight P s t) ≤ P * (π / sin (π / s) - s) + (s / 2 + 2) * P * (2 : ℝ) ^ (-s) := by
  have hs0 : 0 ≤ s := (zero_lt_one.trans hs).le; have ha : 0 < P / 2 := by positivity
  have haP : P / 2 ≤ P := by linarith
  have hPb : P ≤ 2 * P := by linarith
  have hwi := weight_interval hP hs0 ha haP hPb; have hwL := weight_interval hP hs0 ha haP (le_refl P); have hwR := weight_interval hP hs0 hP (le_refl P) hPb; have hsplit := intervalIntegral.integral_add_adjacent_intervals hwL hwR
  rw [left_integral hP hs0 ha haP, right_integral hP hs0 hPb] at hsplit
  have hkiL := kernel_interval hP hs ha.le haP; have hkiR := kernel_interval hP hs hP.le hPb; have hksplit := intervalIntegral.integral_add_adjacent_intervals hkiL hkiR; have htail : weight P s (2 * P) ≤ (2 : ℝ) ^ (-s) := by
    rw [← rightWeight_eq_weight hP (by positivity : 0 < 2 * P) hs0 hPb]
    dsimp only [logWeight]
    have hpow : P ^ s / (2 * P) ^ s = (2 : ℝ) ^ (-s) := by
      rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hP.le, rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      field_simp [(rpow_pos_of_pos hP s).ne', (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) s).ne']
    rw [hpow]
    have h := log_le_sub_one_of_pos (by positivity : 0 < 1 + (2 : ℝ) ^ (-s))
    linarith
  have hk := kernel_middle_upper hP hs; have hhead := weight_nonneg P s (P / 2); have ht := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 2 * P); have hh := mul_nonneg ha.le hhead
  simp only [div_eq_mul_inv] at hsplit hksplit hk hh ht ⊢
  nlinarith only [hsplit, hksplit, hk, ht, hh]
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
/-- Occupancy at logarithmic distance u from the central cutoff. -/
def logistic (u : ℝ) : ℝ := (1 + exp u)⁻¹
/-- The logarithmic Fermi weight. -/
def fermiLog (u : ℝ) : ℝ := log (1 + exp (-u))
/-- Entropy of the logistic occupancy. -/
def entropy (u : ℝ) : ℝ := binEntropy (logistic u)
private lemma logistic_range (u : ℝ) : 0 < logistic u ∧ logistic u < 1 := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_bounds u
private lemma logistic_le_exp (u : ℝ) : logistic u ≤ exp (-u) := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_le_exp_neg u
private lemma logistic_continuous : Continuous logistic := D5.S3.Weil.ZetaBridge.FermiMellin.continuous_fermi
private lemma fermiLog_deriv (u : ℝ) : HasDerivAt fermiLog (-logistic u) u := by
  have h := (((hasDerivAt_id u).neg.exp).const_add 1).log (by positivity : 1 + exp (-u) ≠ 0)
  convert h using 1
  · rfl
  · dsimp [logistic]
    rw [exp_neg]
    field_simp <;> ring
private lemma fermiLog_bounds (u : ℝ) : 0 ≤ fermiLog u ∧ fermiLog u ≤ exp (-u) := by
  constructor
  · exact log_nonneg (by linarith [exp_pos (-u)])
  · have h := log_le_sub_one_of_pos (by positivity : 0 < 1 + exp (-u))
    simpa [fermiLog] using h
private lemma entropy_identity (u : ℝ) : entropy u = fermiLog u + u * logistic u := by
  have he := exp_pos u; have hp : 1 - logistic u = exp u / (1 + exp u) := by
    dsimp [logistic]
    field_simp <;> ring
  have hn : 1 + exp u ≠ 0 := by positivity
  have hj : fermiLog u = log (1 + exp u) - u := by
    dsimp [fermiLog]
    rw [exp_neg, show 1 + (exp u)⁻¹ = (1 + exp u) / exp u by field_simp; ring, log_div hn he.ne', log_exp]
  rw [entropy, binEntropy, hp, logistic, inv_inv, log_inv, log_div he.ne' hn, log_exp, hj]
  field_simp <;> ring
private lemma fermi_real_one : IntegrableOn logistic (Ioi 0) ∧ (∫ u in Ioi (0 : ℝ), logistic u) = log 2 := by
  have hi := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_integrable 1 (by norm_num) 1 (by norm_num); have he := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_at_one 1 (by norm_num); have hp (u : ℝ) : ((u : ℂ) ^ ((1 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re = logistic u := by
    norm_num only [sub_self, Complex.cpow_zero, one_mul]
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re]
    simp only [logistic, one_div, add_comm]
  refine ⟨hi.re.congr (Eventually.of_forall hp), ?_⟩
  calc
    (∫ u in Ioi (0 : ℝ), logistic u) = ∫ u in Ioi (0 : ℝ), ((u : ℂ) ^ ((1 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re := by exact integral_congr_ae (Eventually.of_forall (fun u => (hp u).symm))
    _ = _ := integral_re hi
    _ = log 2 := by rw [he]; simp only [Complex.ofReal_one, div_one, Complex.ofReal_re]
private lemma fermi_real_two : IntegrableOn (fun u => u * logistic u) (Ioi 0) ∧ (∫ u in Ioi (0 : ℝ), u * logistic u) = π ^ 2 / 12 := by
  have hi := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_integrable 1 (by norm_num) 2 (by norm_num); have he := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_eq_of_ne_one 1 (by norm_num) 2 (by norm_num) (by norm_num)
  have hp (u : ℝ) : ((u : ℂ) ^ ((2 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re = u * logistic u := by
    norm_num only [show (2 : ℂ) - 1 = 1 by norm_num, Complex.cpow_one, one_mul]
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re]
    simp only [logistic, div_eq_mul_inv, add_comm]
  refine ⟨hi.re.congr (Eventually.of_forall hp), ?_⟩
  calc
    (∫ u in Ioi (0 : ℝ), u * logistic u) = ∫ u in Ioi (0 : ℝ), ((u : ℂ) ^ ((2 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re := by exact integral_congr_ae (Eventually.of_forall (fun u => (hp u).symm))
    _ = _ := integral_re hi
    _ = π ^ 2 / 12 := by
      rw [he, show Complex.Gamma 2 = 1 by simpa using Complex.Gamma_nat_eq_factorial 1, riemannZeta_two, show (1 : ℂ) - 2 = -1 by norm_num, Complex.cpow_neg_one]
      norm_num [Complex.div_re, Complex.mul_re, ← Complex.ofReal_pow] <;> ring
private lemma exp_integrable : IntegrableOn (fun u : ℝ => exp (-u)) (Ioi 0) := by simpa using integrableOn_exp_mul_Ioi (a := -1) (by norm_num) 0
private lemma fermiLog_integrable : IntegrableOn fermiLog (Ioi 0) := by
  apply exp_integrable.mono' ((continuous_iff_continuousAt.mpr (fun u => (fermiLog_deriv u).continuousAt)).aestronglyMeasurable)
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (fermiLog_bounds u).1]
  exact (fermiLog_bounds u).2
private lemma mul_exp_limit : Tendsto (fun u : ℝ => u * exp (-u)) atTop (𝓝 0) := by simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 (by norm_num)
private lemma mul_fermiLog_limit : Tendsto (fun u : ℝ => u * fermiLog u) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ mul_exp_limit
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_nonneg hu (fermiLog_bounds u).1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu
    exact mul_le_mul_of_nonneg_left (fermiLog_bounds u).2 hu
private lemma integral_fermiLog : (∫ u in Ioi (0 : ℝ), fermiLog u) = π ^ 2 / 12 := by
  have hd (u : ℝ) : HasDerivAt (fun v => v * fermiLog v) (fermiLog u - u * logistic u) u := by convert (hasDerivAt_id u).mul (fermiLog_deriv u) using 1 <;> ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hd u) (fermiLog_integrable.sub fermi_real_two.1) mul_fermiLog_limit
  rw [integral_sub fermiLog_integrable fermi_real_two.1, fermi_real_two.2] at h
  simp only [zero_mul, sub_zero] at h
  linarith
private lemma entropy_continuous : Continuous entropy := binEntropy_continuous.comp logistic_continuous
private lemma entropy_integral : IntegrableOn entropy (Ioi 0) ∧ (∫ u in Ioi (0 : ℝ), entropy u) = π ^ 2 / 6 := by
  refine ⟨(fermiLog_integrable.add fermi_real_two.1).congr (Eventually.of_forall (fun u => (entropy_identity u).symm)), ?_⟩
  simp_rw [entropy_identity]
  rw [integral_add fermiLog_integrable fermi_real_two.1, integral_fermiLog, fermi_real_two.2]
  ring
private lemma logistic_antitone : Antitone logistic := by
  intro u v huv; exact inv_anti₀ (by positivity) (add_le_add_right (exp_le_exp.mpr huv) 1)
private lemma entropy_antitone : AntitoneOn entropy (Ici 0) := by
  intro u hu v hv huv
  apply binEntropy_strictMonoOn.monotoneOn
  · exact ⟨(logistic_range v).1.le, by
      have h := logistic_antitone hv
      norm_num [logistic] at h
      simpa only [logistic, one_div] using h⟩
  · exact ⟨(logistic_range u).1.le, by
      have h := logistic_antitone hu
      norm_num [logistic] at h
      simpa only [logistic, one_div] using h⟩
  · exact logistic_antitone huv
private lemma envelope_integrable : IntegrableOn (fun u : ℝ => (1 + u) * exp (-u)) (Ioi 0) := by
  have h : IntegrableOn (fun u : ℝ => u * exp (-u)) (Ioi 0) := by
    have h := GammaIntegral_convergent (s := 2) (by norm_num)
    norm_num at h
    simpa only [mul_comm] using h
  apply (exp_integrable.add h).congr
  filter_upwards with u
  change exp (-u) + u * exp (-u) = (1 + u) * exp (-u)
  ring
private lemma envelope_tail {U : ℝ} (hU : 0 ≤ U) : (∫ u in Ioi U, (1 + u) * exp (-u)) = (U + 2) * exp (-U) := by
  have hi := envelope_integrable.mono_set (Ioi_subset_Ioi hU); have hl : Tendsto (fun u : ℝ => -(u + 2) * exp (-u)) atTop (𝓝 0) := by
    have he : Tendsto (fun u : ℝ => exp (-u)) atTop (𝓝 0) := tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
    simpa [add_mul, neg_add, neg_mul] using (mul_exp_limit.add (he.const_mul 2)).neg
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => -(v + 2) * exp (-v)) ((1 + u) * exp (-u)) u := by
    convert (((hasDerivAt_id u).add_const 2).neg).mul ((hasDerivAt_id u).neg.exp) using 1
    all_goals first | (funext v; dsimp; ring) | ring
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hd u) hi hl
  convert h using 1 <;> ring
private lemma entropy_truncated {U : ℝ} (hU : 0 ≤ U) : π ^ 2 / 6 - (U + 2) * exp (-U) ≤ ∫ u in (0 : ℝ)..U, entropy u := by
  have hb : ∀ᵐ u ∂(volume.restrict (Ioi U)), entropy u ≤ (1 + u) * exp (-u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [entropy_identity, add_mul, one_mul]
    exact add_le_add (fermiLog_bounds u).2 (mul_le_mul_of_nonneg_left (logistic_le_exp u) (hU.trans hu.le))
  have he := integral_mono_ae (entropy_integral.1.mono_set (Ioi_subset_Ioi hU)) (envelope_integrable.mono_set (Ioi_subset_Ioi hU)) hb
  rw [envelope_tail hU] at he
  rw [← intervalIntegral.integral_Ioi_sub_Ioi entropy_integral.1 hU, entropy_integral.2]
  linarith
/-- A finite uniform grid, chosen before the asymptotic parameter varies. -/
structure Mesh where
  U : ℝ
  n : ℕ
  U_pos : 0 < U
  n_pos : 0 < n
def Mesh.step (G : Mesh) : ℝ := G.U / G.n
def Mesh.node (G : Mesh) (i : ℕ) : ℝ := i * G.step
def Mesh.cost (G : Mesh) : ℝ := 2 * ∑ i ∈ Finset.range G.n, G.step * G.node (i + 1) * logistic (G.node (i + 1))
def Mesh.mass (G : Mesh) : ℝ := 2 * ∑ i ∈ Finset.range G.n, G.step * entropy (G.node (i + 1))
lemma step_pos (G : Mesh) : 0 < G.step := by exact div_pos G.U_pos (by exact_mod_cast G.n_pos)
private lemma node_nonneg (G : Mesh) (i : ℕ) : 0 ≤ G.node i := by exact mul_nonneg (Nat.cast_nonneg i) (step_pos G).le
lemma node_step (G : Mesh) (i : ℕ) : G.node (i+1) - G.node i = G.step := by simp [Mesh.node, Nat.cast_add, Nat.cast_one]; ring
lemma node_end (G : Mesh) : G.node G.n = G.U := by
  dsimp [Mesh.node, Mesh.step]
  exact mul_div_cancel₀ _ (by exact_mod_cast G.n_pos.ne')
lemma node_zero (G : Mesh) : G.node 0 = 0 := by simp [Mesh.node]
private lemma cell_cost (G : Mesh) (i : ℕ) : G.step * G.node (i+1) * logistic (G.node (i+1)) ≤ (∫ u in G.node i..G.node (i+1), u * logistic u) + G.step * ∫ u in G.node i..G.node (i+1), logistic u := by
  have hab : G.node i ≤ G.node (i+1) := by linarith [step_pos G, node_step G i]
  have hq := logistic_continuous.intervalIntegrable (μ := volume) (G.node i) (G.node (i+1)); have huq : IntervalIntegrable (fun u : ℝ => u * logistic u) volume (G.node i) (G.node (i+1)) := (continuous_id.mul logistic_continuous).intervalIntegrable (μ := volume) _ _
  have h : (∫ _ in G.node i..G.node (i+1), G.node (i+1) * logistic (G.node (i+1))) ≤ ∫ u in G.node i..G.node (i+1), u * logistic u + G.step * logistic u := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab intervalIntegrable_const (huq.add (hq.const_mul G.step))
    intro u hu
    have hqu := logistic_antitone hu.2.le; have hbu : G.node (i+1) ≤ u + G.step := by linarith [node_step G i, hu.1]
    calc
      G.node (i+1) * logistic (G.node (i+1)) ≤ G.node (i+1) * logistic u := mul_le_mul_of_nonneg_left hqu (node_nonneg G _)
      _ ≤ (u + G.step) * logistic u := mul_le_mul_of_nonneg_right hbu (logistic_range u).1.le
      _ = u * logistic u + G.step * logistic u := by ring
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add huq (hq.const_mul _), intervalIntegral.integral_const_mul, node_step, smul_eq_mul] at h
  simpa [mul_assoc] using h
private lemma cell_entropy (G : Mesh) (i : ℕ) : (∫ u in G.node i..G.node (i+1), entropy u) - G.step * entropy (G.node (i+1)) ≤ G.step * (entropy (G.node i) - entropy (G.node (i+1))) := by
  have hab : G.node i ≤ G.node (i+1) := by linarith [step_pos G, node_step G i]
  have h : (∫ u in G.node i..G.node (i+1), entropy u) ≤ ∫ _ in G.node i..G.node (i+1), entropy (G.node i) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hab (entropy_continuous.intervalIntegrable (μ := volume) _ _) intervalIntegrable_const
    intro u hu; exact entropy_antitone (node_nonneg G i) ((node_nonneg G i).trans hu.1.le) hu.1.le
  rw [intervalIntegral.integral_const, node_step, smul_eq_mul] at h
  linarith
private lemma truncated_le {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (hp : ∀ u, 0 ≤ u → 0 ≤ f u) {U : ℝ} (hU : 0 ≤ U) : (∫ u in (0 : ℝ)..U, f u) ≤ ∫ u in Ioi (0 : ℝ), f u := by
  rw [intervalIntegral.integral_of_le hU]
  apply setIntegral_mono_set hf
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using hp u hu.le
  · exact Eventually.of_forall (fun u hu => hu.1)
/-- Finite endpoint sampling controls both cost and entropy, with explicit mesh and tail errors. -/
theorem grid_bounds (G : Mesh) : G.cost ≤ π ^ 2 / 6 + 2 * G.step * log 2 ∧ π ^ 2 / 3 - 2 * (G.U + 2) * exp (-G.U) - 2 * G.step * log 2 ≤ G.mass := by
  have hq := intervalIntegral.sum_integral_adjacent_intervals (a := G.node) (n := G.n) (f := logistic) (fun _ _ => logistic_continuous.intervalIntegrable (μ := volume) _ _)
  have huq := intervalIntegral.sum_integral_adjacent_intervals (a := G.node) (n := G.n) (f := fun u => u * logistic u) (fun _ _ => (continuous_id.mul logistic_continuous).intervalIntegrable (μ := volume) _ _)
  have hf := intervalIntegral.sum_integral_adjacent_intervals (a := G.node) (n := G.n) (f := entropy) (fun _ _ => entropy_continuous.intervalIntegrable (μ := volume) _ _)
  rw [node_zero, node_end] at hq huq hf
  constructor
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range G.n) => cell_cost G i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq, huq] at h
    have h₁ := truncated_le fermi_real_two.1 (fun u hu => mul_nonneg hu (logistic_range u).1.le) G.U_pos.le; have h₂ := truncated_le fermi_real_one.1 (fun u _ => (logistic_range u).1.le) G.U_pos.le
    rw [fermi_real_two.2] at h₁
    rw [fermi_real_one.2] at h₂
    dsimp [Mesh.cost]
    nlinarith [mul_le_mul_of_nonneg_left h₂ (step_pos G).le]
  · have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range G.n) => cell_entropy G i)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub', node_zero, node_end, hf] at h
    have hfU : 0 ≤ entropy G.U := binEntropy_nonneg (logistic_range G.U).1.le (logistic_range G.U).2.le
    have h0 : entropy 0 = log 2 := by
      rw [entropy, logistic, exp_zero, show (1 : ℝ) + 1 = 2 by norm_num]
      exact binEntropy_two_inv
    rw [h0] at h
    have ht := entropy_truncated G.U_pos.le
    dsimp [Mesh.mass]
    rw [← Finset.mul_sum]
    nlinarith [mul_nonneg (step_pos G).le hfU]
/-- A fixed grid achieves any prescribed positive cost slack and entropy loss. -/
theorem exists_good_grid {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) : ∃ G : Mesh, G.cost ≤ (π ^ 2 / 6) * (1 + η / 2) ∧ π ^ 2 / 3 - ρ ≤ G.mass := by
  have he : Tendsto (fun u : ℝ => exp (-u)) atTop (𝓝 0) := tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have ht : Tendsto (fun u : ℝ => 2 * (u + 2) * exp (-u)) atTop (𝓝 0) := by simpa [add_mul, mul_add, mul_assoc] using (mul_exp_limit.add (he.const_mul 2)).const_mul 2
  obtain ⟨U, hU, htU⟩ := ((eventually_ge_atTop (1 : ℝ)).and (ht.eventually_lt_const (by linarith : (0 : ℝ) < ρ / 2))).exists
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  let d := min ((π ^ 2 / 6) * η / (4 * log 2)) (ρ / (4 * log 2))
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (U / d))
  have hn1 : 0 < n := by
    have hnR : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn
    exact_mod_cast (lt_trans zero_lt_one hnR)
  let G : Mesh := ⟨U, n, by linarith, hn1⟩
  have hs : G.step ≤ d := by
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    apply (div_le_iff₀ hnR).mpr
    have h := (div_lt_iff₀ hd).mp ((le_max_right _ _).trans_lt hn)
    simpa [mul_comm] using h.le
  have hs₁ : 2 * G.step * log 2 ≤ (π ^ 2 / 6) * η / 2 := by
    have h := hs.trans (min_le_left _ _); have hd' : 0 < 4 * log (2 : ℝ) := by positivity
    have h := (le_div_iff₀ hd').mp h
    nlinarith
  have hs₂ : 2 * G.step * log 2 ≤ ρ / 2 := by
    have h := hs.trans (min_le_right _ _); have hd' : 0 < 4 * log (2 : ℝ) := by positivity
    have h := (le_div_iff₀ hd').mp h
    nlinarith
  obtain ⟨hc, hm⟩ := grid_bounds G
  refine ⟨G, ?_, ?_⟩
  · nlinarith
  · change π ^ 2 / 3 - 2 * (U + 2) * exp (-U) - 2 * G.step * log 2 ≤ G.mass at hm
    linarith
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Exchange
