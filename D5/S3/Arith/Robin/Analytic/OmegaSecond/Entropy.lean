/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Entropy
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Entropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Budget-feasible prime exchanges, finite entropy bounds, and the exact second-threshold counting limit. -/
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
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Nat.Choose.Sum
import D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
open scoped Topology BigOperators
open Real Filter MeasureTheory Finset Set Asymptotics
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
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
def logarithmicExchangeSystem (n : ℕ) (P s : ℝ) (node : ℕ → ℝ) (R : Finset ℕ) (hP : 0 < P) (hs : 0 < s) (hmono : Monotone node) (hzero : node 0 = 0) (hfar : 3 * P / 4 ≤ P * exp (-node n / s)) (hR : R ⊆ primeInterval (P / 2) (3 * P / 4)) : ExchangeSystem (Fin n) := by { have hneg (i j : ℕ) (hij : i ≤ j) : P * exp (-node j / s) ≤ P * exp (-node i / s) := by { apply mul_le_mul_of_nonneg_left _ hP.le; exact exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg (hmono hij)) hs.le) }; have hpos (i j : ℕ) (hij : i ≤ j) : P * exp (node i / s) ≤ P * exp (node j / s) := by { apply mul_le_mul_of_nonneg_left _ hP.le; exact exp_le_exp.mpr (div_le_div_of_nonneg_right (hmono hij) hs.le) }; have hnegP (i : ℕ) : P * exp (-node i / s) ≤ P := by { simpa [hzero] using hneg 0 i (Nat.zero_le i) }; have hposP (i : ℕ) : P ≤ P * exp (node i / s) := by { simpa [hzero] using hpos 0 i (Nat.zero_le i) }; refine { base := Nat.primesLE ⌊P⌋₊ \ R, neg := fun i => primeInterval (P * exp (-node (i.val + 1) / s)) (P * exp (-node i.val / s)), pos := fun i => primeInterval (P * exp (node i.val / s)) (P * exp (node (i.val + 1) / s)), base_prime := ?_, neg_subset := ?_, pos_prime := ?_, pos_base := ?_, neg_disjoint := ?_, pos_disjoint := ?_ }; { intro p hp; exact (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2 }; { intro i p hp; obtain ⟨hp, hpprime⟩ := Finset.mem_filter.mp hp; obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hp; refine Finset.mem_sdiff.mpr ⟨Nat.mem_primesLE.mpr ⟨hhi.trans (Nat.floor_mono (hnegP i.val)), hpprime⟩, ?_⟩; intro hr; have hrhi := (Finset.mem_Ioc.mp (Finset.mem_filter.mp (hR hr)).1).2; have hh := Nat.floor_mono (hfar.trans (hneg (i.val + 1) n (by omega))); omega }; { intro i p hp; exact (Finset.mem_filter.mp hp).2 }; { intro i; apply Finset.disjoint_left.mpr; intro p hp hb; have hpgt := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1; have hble := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hb).1).1; have hh := Nat.floor_mono (hposP i.val); omega }; { intro i j hij; apply Finset.disjoint_left.mpr; intro p hpi hpj; have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpi).1; have hj := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpj).1; rcases lt_or_gt_of_ne hij with hij | hij; { have hh := Nat.floor_mono (hneg (i.val + 1) j.val (by omega)); omega }; { have hh := Nat.floor_mono (hneg (j.val + 1) i.val (by omega)); omega } }; { intro i j hij; apply Finset.disjoint_left.mpr; intro p hpi hpj; have hi := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpi).1; have hj := Finset.mem_Ioc.mp (Finset.mem_filter.mp hpj).1; rcases lt_or_gt_of_ne hij with hij | hij; { have hh := Nat.floor_mono (hpos (i.val + 1) j.val (by omega)); omega }; { have hh := Nat.floor_mono (hpos (j.val + 1) i.val (by omega)); omega } } }
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Choices (E : ExchangeSystem ι) (h : ι → ℕ) := ((i : ι) → ↥((E.neg i).powersetCard (h i))) × ((i : ι) → ↥((E.pos i).powersetCard (h i)))
def removed (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Finset ℕ := univ.biUnion (fun i => (z.1 i).val)
def inserted (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Finset ℕ := univ.biUnion (fun i => (z.2 i).val)
def support (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Finset ℕ := (E.base \ removed E h z) ∪ inserted E h z
def value (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : ℕ := ∏ p ∈ support E h z, p
private lemma neg_selection (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) (i : ι) : (z.1 i).val ⊆ E.neg i ∧ (z.1 i).val.card = h i := mem_powersetCard.mp (z.1 i).property
private lemma pos_selection (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) (i : ι) : (z.2 i).val ⊆ E.pos i ∧ (z.2 i).val.card = h i := mem_powersetCard.mp (z.2 i).property
private lemma removed_subset (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : removed E h z ⊆ E.base := by { intro p hp; obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp; exact E.neg_subset i ((neg_selection E h z i).1 hi) }
private lemma inserted_disjoint (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Disjoint (inserted E h z) E.base := by { apply Finset.disjoint_left.mpr; intro p hp hb; obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp; exact Finset.disjoint_left.mp (E.pos_base i) ((pos_selection E h z i).1 hi) hb }
private lemma support_prime (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : ∀ p ∈ support E h z, Nat.Prime p := by { intro p hp; rcases mem_union.mp hp with hp | hp; { exact E.base_prime p (mem_sdiff.mp hp).1 }; { obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp; exact E.pos_prime i p ((pos_selection E h z i).1 hi) } }
private lemma neg_pairwise (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Set.PairwiseDisjoint (univ : Finset ι) (fun i => (z.1 i).val) := by { intro i _ j _ hij; exact (E.neg_disjoint hij).mono (neg_selection E h z i).1 (neg_selection E h z j).1 }
private lemma pos_pairwise (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Set.PairwiseDisjoint (univ : Finset ι) (fun i => (z.2 i).val) := by { intro i _ j _ hij; exact (E.pos_disjoint hij).mono (pos_selection E h z i).1 (pos_selection E h z j).1 }
private lemma removed_card (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : (removed E h z).card = ∑ i, h i := by { rw [removed, card_biUnion (neg_pairwise E h z)]; exact sum_congr rfl (fun i _ => (neg_selection E h z i).2) }
private lemma inserted_card (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : (inserted E h z).card = ∑ i, h i := by { rw [inserted, card_biUnion (pos_pairwise E h z)]; exact sum_congr rfl (fun i _ => (pos_selection E h z i).2) }
private lemma support_card (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : (support E h z).card = E.base.card := by { have hd : Disjoint (E.base \ removed E h z) (inserted E h z) := (inserted_disjoint E h z).symm.mono_left sdiff_subset; have hc := Finset.card_le_card (removed_subset E h z); rw [support, card_union_of_disjoint hd, card_sdiff_of_subset (removed_subset E h z), removed_card, inserted_card]; rw [removed_card] at hc; omega }
theorem exchange_value_injective (E : ExchangeSystem ι) (h : ι → ℕ) : Function.Injective (value E h) := by
  intro z w he
  have hs : support E h z = support E h w := prime_product_injective (support_prime E h z) (support_prime E h w) he
  have hr : removed E h z = removed E h w := by
    ext p
    by_cases hp : p ∈ E.base
    · have hz : p ∉ inserted E h z := fun hh =>
        Finset.disjoint_left.mp (inserted_disjoint E h z) hh hp
      have hw : p ∉ inserted E h w := fun hh =>
        Finset.disjoint_left.mp (inserted_disjoint E h w) hh hp
      have hh := Finset.ext_iff.mp hs p
      simp only [support, Finset.mem_union, Finset.mem_sdiff, hp, true_and, hz, hw, or_false] at hh
      exact not_iff_not.mp hh
    · exact iff_of_false (fun hh => hp (removed_subset E h z hh))
        (fun hh => hp (removed_subset E h w hh))
  have ha : inserted E h z = inserted E h w := by
    ext p
    by_cases hp : p ∈ E.base
    · exact iff_of_false
        (fun hh => Finset.disjoint_left.mp (inserted_disjoint E h z) hh hp)
        (fun hh => Finset.disjoint_left.mp (inserted_disjoint E h w) hh hp)
    · have hh := Finset.ext_iff.mp hs p
      simpa only [support, Finset.mem_union, Finset.mem_sdiff, hp, false_and, false_or] using hh
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
theorem omega_exchange_value (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : ArithmeticFunction.cardDistinctFactors (value E h z) = E.base.card := by { rw [value, omega_prime_product (support_prime E h z), support_card] }
theorem card_exchange_choices (E : ExchangeSystem ι) (h : ι → ℕ) : Fintype.card (Choices E h) = ∏ i, (E.neg i).card.choose (h i) * (E.pos i).card.choose (h i) := by { simp only [Choices, Fintype.card_prod, Fintype.card_pi, Fintype.card_coe, card_powersetCard, prod_mul_distrib] }
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
theorem balanced_exchange_bound (E : ExchangeSystem ι) (h : ι → ℕ) (P D s : ℝ) (t : ι → ℝ) (lambda x : ℝ) (hbase : ∑ p ∈ E.base, log (p : ℝ) ≤ P - D) (hneg : ∀ i p, p ∈ E.neg i → log P - t i / s ≤ log (p : ℝ)) (hpos : ∀ i p, p ∈ E.pos i → log (p : ℝ) ≤ log P + t i / s) (hbudget : (2 / s) * ∑ i, t i * (h i : ℝ) ≤ D) (hthreshold : threshold lambda x < (E.base.card : ℝ)) (hP : P ≤ log x) (hx : 0 < x) : (∏ i, (E.neg i).card.choose (h i) * (E.pos i).card.choose (h i)) ≤ tailCount lambda x := by classical { have hinj : Function.Injective (support E h) := by { intro z w he; exact exchange_value_injective E h (congrArg (fun S : Finset ℕ => ∏ p ∈ S, p) he) }; have hb := prime_family_bound lambda x (univ.image (support E h)) ?_ ?_ ?_ hx; { simpa only [card_image_of_injective _ hinj, card_univ, card_exchange_choices] using hb }; { intro S hS p hp; obtain ⟨z, _, rfl⟩ := mem_image.mp hS; exact support_prime E h z p hp }; { intro S hS; obtain ⟨z, _, rfl⟩ := mem_image.mp hS; have ho := omega_exchange_value E h z; rw [value, omega_prime_product (support_prime E h z)] at ho; simpa only [ho] using hthreshold }; { intro S hS; obtain ⟨z, _, rfl⟩ := mem_image.mp hS; have he := log_exchange_value_le E h P D s t hbase hneg hpos z; have hlog : log (value E h z : ℝ) = ∑ p ∈ support E h z, log (p : ℝ) := by { rw [value, Nat.cast_prod, log_prod]; intro p hp; exact_mod_cast (support_prime E h z p hp).ne_zero }; rw [hlog] at he; linarith } }
theorem logarithmic_exchange_bound (n : ℕ) (P s : ℝ) (node : ℕ → ℝ) (R : Finset ℕ) (hP : 0 < P) (hs : 0 < s) (hmono : Monotone node) (hzero : node 0 = 0) (hfar : 3 * P / 4 ≤ P * exp (-node n / s)) (hR : R ⊆ primeInterval (P / 2) (3 * P / 4)) (h : Fin n → ℕ) (D lambda x : ℝ) (hbase : ∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ) ≤ P - D) (hbudget : (2 / s) * ∑ i : Fin n, node (i.val + 1) * (h i : ℝ) ≤ D) (hthreshold : threshold lambda x < ((Nat.primesLE ⌊P⌋₊ \ R).card : ℝ)) (hPx : P ≤ log x) (hx : 0 < x) : (∏ i : Fin n, (primeInterval (P * exp (-node (i.val + 1) / s)) (P * exp (-node i.val / s))).card.choose (h i) * (primeInterval (P * exp (node i.val / s)) (P * exp (node (i.val + 1) / s))).card.choose (h i)) ≤ tailCount lambda x := by { let E := logarithmicExchangeSystem n P s node R hP hs hmono hzero hfar hR; apply balanced_exchange_bound E h P D s (fun i => node (i.val + 1)) lambda x hbase ?_ ?_ hbudget hthreshold hPx hx; { intro i p hp; obtain ⟨hp, _⟩ := Finset.mem_filter.mp hp; have hlo := (Finset.mem_Ioc.mp hp).1; have he : 0 < P * exp (-node (i.val + 1) / s) := mul_pos hP (exp_pos _); have hh := log_le_log he ((Nat.floor_lt he.le).mp hlo).le; rw [log_mul hP.ne' (exp_ne_zero _), log_exp] at hh; simpa only [neg_div, sub_eq_add_neg] using hh }; { intro i p hp; obtain ⟨hp, hpprime⟩ := Finset.mem_filter.mp hp; have hhi := (Finset.mem_Ioc.mp hp).2; have he : 0 ≤ P * exp (node (i.val + 1) / s) := by { positivity }; have hh := log_le_log (by exact_mod_cast hpprime.pos : 0 < (p : ℝ)) ((Nat.le_floor_iff he).mp hhi); rwa [log_mul hP.ne' (exp_ne_zero _), log_exp] at hh } }
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
def countingThreeTerms (P : ℝ) : ℝ := P / log P + P / log P ^ 2 + 2 * P / log P ^ 3
theorem prime_counting_three_terms : Tendsto (fun P : ℝ => (primeCount P - countingThreeTerms P) / (P / log P ^ 4)) atTop (𝓝 6) := by { have hi : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop 1; have h := (prime_counting_four_terms.mul hi).add_const 6; norm_num only [mul_zero, zero_add] at h; apply h.congr'; filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; dsimp only [countingPolynomial, countingThreeTerms]; field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring }
private lemma prime_counting_error_limit : Tendsto (fun P : ℝ => (primeCount P - P / log P) / (P / log P ^ 2)) atTop (𝓝 1) := by { apply D5.S3.Arith.Robin.Analytic.ExceptionCount.PrimeCutoff.second_order_count.congr'; filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring }
theorem prime_counting_error_bound : ∀ᶠ P : ℝ in atTop, |primeCount P - P / log P| ≤ 3 * (P / log P ^ 2) := by { have h := prime_counting_error_limit.abs; norm_num only [abs_one] at h; filter_upwards [h.eventually_lt_const (by norm_num : (1 : ℝ) < 3), eventually_gt_atTop (1 : ℝ)] with P hbound hP; have hscale : 0 < P / log P ^ 2 := div_pos (by linarith) (sq_pos_of_pos (log_pos hP)); rw [abs_div, abs_of_pos hscale] at hbound; exact ((div_lt_iff₀ hscale).mp hbound).le }
def budget (P : ℝ) : ℝ := P - Chebyshev.theta P + (primeCount P - (P / log P + P / log P ^ 2)) * log P
theorem budget_limit : Tendsto (fun P : ℝ => budget P / (P / log P ^ 2)) atTop (𝓝 2) := by { have hi : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop 1; have hθ := (theta_error_log_power 2).tendsto_div_nhds_zero; have h := hθ.neg.add ((prime_counting_three_terms.mul hi).add_const 2); norm_num only [neg_zero, mul_zero, zero_add] at h; apply h.congr'; filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; dsimp only [budget, countingThreeTerms]; field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring }
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
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper
def weight (P s t : ℝ) : ℝ := log (1 + exp (-s * |log (t / P)|))
def remainder (P s x : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊x⌋₊, weight P s p
private lemma softplus_split (v : ℝ) : log (1 + exp v) = max v 0 + log (1 + exp (-|v|)) := by { by_cases hv : 0 ≤ v; { rw [abs_of_nonneg hv, max_eq_left hv]; have h : 1 + exp v = exp v * (1 + exp (-v)) := by { rw [mul_add, mul_one, ← exp_add]; simp; ring }; rw [h, log_mul (exp_ne_zero _) (by positivity), log_exp] }; { have hv' : v ≤ 0 := (lt_of_not_ge hv).le; rw [abs_of_nonpos hv', max_eq_right hv', neg_neg, zero_add] } }
private lemma logWeight_split {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) (hs : 0 ≤ s) : log (1 + P ^ s * t ^ (-s)) = (if t ≤ P then s * (log P - log t) else 0) + weight P s t := by { have he : P ^ s * t ^ (-s) = exp (s * (log P - log t)) := by { rw [rpow_def_of_pos hP, rpow_def_of_pos ht, ← exp_add]; congr 1; ring }; have hl : log (t / P) = log t - log P := log_div ht.ne' hP.ne'; rw [he, softplus_split]; have hab : |s * (log P - log t)| = s * |log (t / P)| := by { rw [abs_mul, abs_of_nonneg hs, hl, ← abs_neg (log t - log P)]; congr 2; ring }; rw [hab]; dsimp only [weight]; rw [neg_mul]; congr 1; split_ifs with h; { exact max_eq_left (mul_nonneg hs (sub_nonneg.mpr (log_le_log ht h))) }; { exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hs (sub_nonpos.mpr (log_le_log hP (le_of_not_ge h)))) } }
theorem weight_nonneg (P s t : ℝ) : 0 ≤ weight P s t := by { apply log_nonneg; have := exp_nonneg (-s * |log (t / P)|); linarith }
theorem weight_continuousOn {P s a b : ℝ} (hP : 0 < P) (ha : 0 < a) : ContinuousOn (weight P s) (Set.Icc a b) := by { intro t ht; have ht0 : 0 < t := ha.trans_le ht.1; have hl : ContinuousAt (fun u : ℝ => log (u / P)) t := (continuousAt_id.div_const P).log (div_pos ht0 hP).ne'; have he : ContinuousAt (fun u : ℝ => 1 + exp (-s * |log (u / P)|)) t := continuousAt_const.add ((hl.abs.const_mul (-s)).rexp); exact (he.log (by positivity)).continuousWithinAt }
def leftWeight (P s t : ℝ) : ℝ := logWeight s (P ^ s) t - s * (log P - log t)
theorem leftWeight_eq_weight {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) (hs : 0 ≤ s) (htP : t ≤ P) : leftWeight P s t = weight P s t := by { have h := logWeight_split hP ht hs; rw [if_pos htP] at h; dsimp only [leftWeight, logWeight]; rw [div_eq_mul_inv, ← rpow_neg ht.le]; linarith only [h] }
theorem rightWeight_eq_weight {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) (hs : 0 ≤ s) (hPt : P ≤ t) : logWeight s (P ^ s) t = weight P s t := by { rcases hPt.eq_or_lt with rfl | hPt; { have h := logWeight_split hP hP hs; simp only [le_refl, ↓reduceIte, sub_self, mul_zero, zero_add] at h; dsimp only [logWeight]; rwa [div_eq_mul_inv, ← rpow_neg hP.le] }; { have h := logWeight_split hP ht hs; rw [if_neg hPt.not_ge, zero_add] at h; dsimp only [logWeight]; rwa [div_eq_mul_inv, ← rpow_neg ht.le] } }
theorem leftWeight_deriv {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) : HasDerivAt (leftWeight P s) (s / t - abelKernel s (P ^ s) t) t := by { have h := (logWeight_deriv (s := s) (rpow_pos_of_pos hP s) ht).sub (((hasDerivAt_const t (log P)).sub (hasDerivAt_log ht.ne')).const_mul s); convert h using 1; { rfl }; { simp only [div_eq_mul_inv]; ring } }
theorem leftWeight_at_cutoff {P s : ℝ} (hP : 0 < P) : leftWeight P s P = log 2 := by { dsimp only [leftWeight, logWeight]; rw [div_self (rpow_pos_of_pos hP s).ne']; norm_num }
theorem rightWeight_at_cutoff {P s : ℝ} (hP : 0 < P) : logWeight s (P ^ s) P = log 2 := by { dsimp only [logWeight]; rw [div_self (rpow_pos_of_pos hP s).ne']; norm_num }
theorem leftWeight_deriv_nonneg {P s t : ℝ} (hP : 0 < P) (ht : 0 < t) (hs : 0 ≤ s) : 0 ≤ s / t - abelKernel s (P ^ s) t := by { have htp : 0 < t ^ s := rpow_pos_of_pos ht s; have hPP : 0 < P ^ s := rpow_pos_of_pos hP s; dsimp only [abelKernel]; apply sub_nonneg.mpr; apply (div_le_div_iff₀ (by positivity : 0 < t * (t ^ s + P ^ s)) ht).mpr; nlinarith [mul_nonneg hs htp.le] }
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
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
private lemma prime_cdf (t : ℝ) : (∑ p ∈ Finset.Icc 0 ⌊t⌋₊, if p.Prime then (1 : ℝ) else 0) = primeCount t := by { simp only [← sum_filter, sum_const, nsmul_eq_mul, mul_one]; rw [← Nat.primesLE_eq_filter_Icc_zero, Nat.primesLE_card_eq_primeCounting]; rfl }
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
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper Exchange
private def kernel (P s t : ℝ) : ℝ := s * P ^ s / (t ^ s + P ^ s)
private lemma kernel_integrable {P s : ℝ} (hP : 0 < P) (hs : 1 < s) : IntegrableOn (kernel P s) (Ioi 0) := (power_kernel_integral hs (rpow_pos_of_pos hP s)).1
private lemma kernel_interval {P s a b : ℝ} (hP : 0 < P) (hs : 1 < s) (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable (kernel P s) volume a b := by { apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr; exact (kernel_integrable hP hs).mono_set (fun t ht => ha.trans_lt ht.1) }
private lemma left_integral {P s a : ℝ} (hP : 0 < P) (hs : 0 ≤ s) (ha : 0 < a) (haP : a ≤ P) : (∫ t in a..P, weight P s t) = P * log 2 - a * weight P s a - s * (P - a) + ∫ t in a..P, kernel P s t := by { have hPP : 0 < P ^ s := rpow_pos_of_pos hP s; have hcontL : ContinuousOn (leftWeight P s) (Icc a P) := by { intro t ht; exact (leftWeight_deriv hP (ha.trans_le ht.1)).continuousAt.continuousWithinAt }; have hcontK : ContinuousOn (kernel P s) (Icc a P) := by { intro t ht; have ht0 := ha.trans_le ht.1; exact (continuousAt_const.div ((hasDerivAt_rpow_const (Or.inl ht0.ne')).continuousAt.add continuousAt_const) (by positivity : t ^ s + P ^ s ≠ 0)).continuousWithinAt }; have hli := hcontL.intervalIntegrable_of_Icc (μ := volume) haP; have hki := hcontK.intervalIntegrable_of_Icc (μ := volume) haP; have hFTC : (∫ t in a..P, leftWeight P s t - kernel P s t) = (P * leftWeight P s P - s * P) - (a * leftWeight P s a - s * a) := by { apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t * leftWeight P s t - s * t) _ (hli.sub hki); intro t ht; rw [uIcc_of_le haP] at ht; have ht0 : 0 < t := ha.trans_le ht.1; have hd := ((hasDerivAt_id t).mul (leftWeight_deriv (s := s) hP ht0)).sub ((hasDerivAt_id t).const_mul s); convert hd using 1; { rfl }; { dsimp only [kernel, abelKernel, id_eq]; field_simp [ht0.ne', (by positivity : t ^ s + P ^ s ≠ 0)] <;> ring } }; have heq : (∫ t in a..P, leftWeight P s t) = ∫ t in a..P, weight P s t := by { apply intervalIntegral.integral_congr; intro t ht; rw [uIcc_of_le haP] at ht; exact leftWeight_eq_weight hP (ha.trans_le ht.1) hs ht.2 }; rw [intervalIntegral.integral_sub hli hki, heq, leftWeight_at_cutoff hP, leftWeight_eq_weight hP ha hs haP] at hFTC; linarith }
private lemma right_integral {P s b : ℝ} (hP : 0 < P) (hs : 0 ≤ s) (hPb : P ≤ b) : (∫ t in P..b, weight P s t) = b * weight P s b - P * log 2 + ∫ t in P..b, kernel P s t := by { have hPP : 0 < P ^ s := rpow_pos_of_pos hP s; have hcontR : ContinuousOn (logWeight s (P ^ s)) (Icc P b) := by { intro t ht; exact (logWeight_deriv hPP (hP.trans_le ht.1)).continuousAt.continuousWithinAt }; have hcontK : ContinuousOn (kernel P s) (Icc P b) := by { intro t ht; have ht0 := hP.trans_le ht.1; exact (continuousAt_const.div ((hasDerivAt_rpow_const (Or.inl ht0.ne')).continuousAt.add continuousAt_const) (by positivity : t ^ s + P ^ s ≠ 0)).continuousWithinAt }; have hri := hcontR.intervalIntegrable_of_Icc (μ := volume) hPb; have hki := hcontK.intervalIntegrable_of_Icc (μ := volume) hPb; have hFTC : (∫ t in P..b, logWeight s (P ^ s) t - kernel P s t) = b * logWeight s (P ^ s) b - P * logWeight s (P ^ s) P := by { apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t * logWeight s (P ^ s) t) _ (hri.sub hki); intro t ht; rw [uIcc_of_le hPb] at ht; have ht0 : 0 < t := hP.trans_le ht.1; have hd := (hasDerivAt_id t).mul (logWeight_deriv (s := s) hPP ht0); convert hd using 1; { rfl }; { dsimp only [kernel, abelKernel, id_eq]; field_simp [ht0.ne', (by positivity : t ^ s + P ^ s ≠ 0)] <;> ring } }; have heq : (∫ t in P..b, logWeight s (P ^ s) t) = ∫ t in P..b, weight P s t := by { apply intervalIntegral.integral_congr; intro t ht; rw [uIcc_of_le hPb] at ht; exact rightWeight_eq_weight hP (hP.trans_le ht.1) hs ht.1 }; rw [intervalIntegral.integral_sub hri hki, heq, rightWeight_at_cutoff hP, rightWeight_eq_weight hP (hP.trans_le hPb) hs hPb] at hFTC; linarith }
private lemma weight_interval {P s a b : ℝ} (hP : 0 < P) (hs : 0 ≤ s) (ha : 0 < a) (haP : a ≤ P) (hPb : P ≤ b) : IntervalIntegrable (weight P s) volume a b := by { have hl : IntervalIntegrable (weight P s) volume a P := by { have h : ContinuousOn (leftWeight P s) (Icc a P) := by { intro t ht; exact (leftWeight_deriv hP (ha.trans_le ht.1)).continuousAt.continuousWithinAt }; apply (h.intervalIntegrable_of_Icc (μ := volume) haP).congr_uIoo; intro t ht; rw [uIoo_of_le haP] at ht; exact leftWeight_eq_weight hP (ha.trans ht.1) hs ht.2.le }; have hr : IntervalIntegrable (weight P s) volume P b := by { have h : ContinuousOn (logWeight s (P ^ s)) (Icc P b) := by { intro t ht; exact (logWeight_deriv (rpow_pos_of_pos hP s) (hP.trans_le ht.1)).continuousAt.continuousWithinAt }; apply (h.intervalIntegrable_of_Icc (μ := volume) hPb).congr_uIoo; intro t ht; rw [uIoo_of_le hPb] at ht; exact rightWeight_eq_weight hP (hP.trans ht.1) hs ht.1.le }; exact hl.trans hr }
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
private lemma kernel_middle_upper {P s : ℝ} (hP : 0 < P) (hs : 1 < s) : (∫ t in (P / 2)..(2 * P), kernel P s t) ≤ π * P / sin (π / s) - s * (P / 2) + s * (P / 2) * (2 : ℝ) ^ (-s) := by { have hki := kernel_integrable hP hs; have hk0 := kernel_interval hP hs (le_refl (0 : ℝ)) (by positivity : (0 : ℝ) ≤ P / 2); have hkm := kernel_interval hP hs (by positivity : (0 : ℝ) ≤ P / 2) (by linarith : P / 2 ≤ 2 * P); have hwhole : (∫ t in (0 : ℝ)..(2 * P), kernel P s t) ≤ ∫ t in Ioi (0 : ℝ), kernel P s t := by { rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * P)]; apply setIntegral_mono_set hki; { filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; have ht0 : 0 < t := ht; dsimp only [kernel]; have hs0 : 0 < s := zero_lt_one.trans hs; positivity }; { exact Eventually.of_forall (fun t ht => ht.1) } }; have heval := (power_kernel_integral hs (rpow_pos_of_pos hP s)).2; have hexp : (P ^ s) ^ (1 / s) = P := by { rw [← rpow_mul hP.le, mul_one_div_cancel (by linarith : s ≠ 0), rpow_one] }; rw [hexp] at heval; change (∫ t in Ioi (0 : ℝ), kernel P s t) = _ at heval; rw [heval, ← intervalIntegral.integral_add_adjacent_intervals hk0 hkm] at hwhole; have hhead := kernel_head_lower hP hs; nlinarith only [hwhole, hhead] }
theorem central_integral_upper {P s : ℝ} (hP : 0 < P) (hs : 1 < s) : (∫ t in (P / 2)..(2 * P), weight P s t) ≤ P * (π / sin (π / s) - s) + (s / 2 + 2) * P * (2 : ℝ) ^ (-s) := by { have hs0 : 0 ≤ s := (zero_lt_one.trans hs).le; have ha : 0 < P / 2 := by { positivity }; have haP : P / 2 ≤ P := by { linarith }; have hPb : P ≤ 2 * P := by { linarith }; have hwi := weight_interval hP hs0 ha haP hPb; have hwL := weight_interval hP hs0 ha haP (le_refl P); have hwR := weight_interval hP hs0 hP (le_refl P) hPb; have hsplit := intervalIntegral.integral_add_adjacent_intervals hwL hwR; rw [left_integral hP hs0 ha haP, right_integral hP hs0 hPb] at hsplit; have hkiL := kernel_interval hP hs ha.le haP; have hkiR := kernel_interval hP hs hP.le hPb; have hksplit := intervalIntegral.integral_add_adjacent_intervals hkiL hkiR; have htail : weight P s (2 * P) ≤ (2 : ℝ) ^ (-s) := by { rw [← rightWeight_eq_weight hP (by positivity : 0 < 2 * P) hs0 hPb]; dsimp only [logWeight]; have hpow : P ^ s / (2 * P) ^ s = (2 : ℝ) ^ (-s) := by { rw [mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hP.le, rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]; field_simp [(rpow_pos_of_pos hP s).ne', (rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) s).ne'] }; rw [hpow]; have h := log_le_sub_one_of_pos (by positivity : 0 < 1 + (2 : ℝ) ^ (-s)); linarith }; have hk := kernel_middle_upper hP hs; have hhead := weight_nonneg P s (P / 2); have ht := mul_le_mul_of_nonneg_left htail (by positivity : 0 ≤ 2 * P); have hh := mul_nonneg ha.le hhead; simp only [div_eq_mul_inv] at hsplit hksplit hk hh ht ⊢; nlinarith only [hsplit, hksplit, hk, ht, hh] }
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
def logistic (u : ℝ) : ℝ := (1 + exp u)⁻¹
def fermiLog (u : ℝ) : ℝ := log (1 + exp (-u))
def entropy (u : ℝ) : ℝ := binEntropy (logistic u)
private lemma logistic_range (u : ℝ) : 0 < logistic u ∧ logistic u < 1 := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_bounds u
private lemma logistic_le_exp (u : ℝ) : logistic u ≤ exp (-u) := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_le_exp_neg u
private lemma logistic_continuous : Continuous logistic := D5.S3.Weil.ZetaBridge.FermiMellin.continuous_fermi
private lemma fermiLog_deriv (u : ℝ) : HasDerivAt fermiLog (-logistic u) u := by { have h := (((hasDerivAt_id u).neg.exp).const_add 1).log (by positivity : 1 + exp (-u) ≠ 0); convert h using 1; { rfl }; { dsimp [logistic]; rw [exp_neg]; field_simp <;> ring } }
private lemma fermiLog_bounds (u : ℝ) : 0 ≤ fermiLog u ∧ fermiLog u ≤ exp (-u) := by { constructor; { exact log_nonneg (by linarith [exp_pos (-u)]) }; { have h := log_le_sub_one_of_pos (by positivity : 0 < 1 + exp (-u)); simpa [fermiLog] using h } }
private lemma entropy_identity (u : ℝ) : entropy u = fermiLog u + u * logistic u := by { have he := exp_pos u; have hp : 1 - logistic u = exp u / (1 + exp u) := by { dsimp [logistic]; field_simp <;> ring }; have hn : 1 + exp u ≠ 0 := by { positivity }; have hj : fermiLog u = log (1 + exp u) - u := by { dsimp [fermiLog]; rw [exp_neg, show 1 + (exp u)⁻¹ = (1 + exp u) / exp u by field_simp; ring, log_div hn he.ne', log_exp] }; rw [entropy, binEntropy, hp, logistic, inv_inv, log_inv, log_div he.ne' hn, log_exp, hj]; field_simp <;> ring }
private lemma fermi_real_one : IntegrableOn logistic (Ioi 0) ∧ (∫ u in Ioi (0 : ℝ), logistic u) = log 2 := by
  have hi := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_integrable 1 (by norm_num) 1 (by norm_num); have he := D5.S3.Weil.ZetaBridge.FermiMellin.fermi_mellin_at_one 1 (by norm_num); have hp (u : ℝ) : ((u : ℂ) ^ ((1 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re = logistic u := by
    norm_num only [sub_self, Complex.cpow_zero, one_mul]
    rw [← Complex.ofReal_one, ← Complex.ofReal_add, ← Complex.ofReal_div, Complex.ofReal_re]
    simp only [logistic, one_div, add_comm]
  refine ⟨hi.re.congr (Eventually.of_forall hp), ?_⟩
  calc
    (∫ u in Ioi (0 : ℝ), logistic u) = ∫ u in Ioi (0 : ℝ), ((u : ℂ) ^ ((1 : ℂ) - 1) / ((exp (1 * u) : ℂ) + 1)).re := by exact integral_congr_ae (Eventually.of_forall (fun u => (hp u).symm))
    _ = _ := integral_re hi
    _ = log 2 := by rw [he]; norm_num [Complex.log_re]
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
private lemma fermiLog_integrable : IntegrableOn fermiLog (Ioi 0) := by { apply exp_integrable.mono' ((continuous_iff_continuousAt.mpr (fun u => (fermiLog_deriv u).continuousAt)).aestronglyMeasurable); filter_upwards with u; rw [Real.norm_eq_abs, abs_of_nonneg (fermiLog_bounds u).1]; exact (fermiLog_bounds u).2 }
private lemma mul_exp_limit : Tendsto (fun u : ℝ => u * exp (-u)) atTop (𝓝 0) := by simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 1 (by norm_num)
private lemma mul_fermiLog_limit : Tendsto (fun u : ℝ => u * fermiLog u) atTop (𝓝 0) := by { apply squeeze_zero' _ _ mul_exp_limit; { filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu; exact mul_nonneg hu (fermiLog_bounds u).1 }; { filter_upwards [eventually_ge_atTop (0 : ℝ)] with u hu; exact mul_le_mul_of_nonneg_left (fermiLog_bounds u).2 hu } }
private lemma integral_fermiLog : (∫ u in Ioi (0 : ℝ), fermiLog u) = π ^ 2 / 12 := by { have hd (u : ℝ) : HasDerivAt (fun v => v * fermiLog v) (fermiLog u - u * logistic u) u := by { convert (hasDerivAt_id u).mul (fermiLog_deriv u) using 1 <;> (try funext v) <;> (try dsimp) <;> ring }; have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hd u) (fermiLog_integrable.sub fermi_real_two.1) mul_fermiLog_limit; rw [integral_sub fermiLog_integrable fermi_real_two.1, fermi_real_two.2] at h; simp only [zero_mul, sub_zero] at h; linarith }
private lemma entropy_continuous : Continuous entropy := binEntropy_continuous.comp logistic_continuous
private lemma entropy_integral : IntegrableOn entropy (Ioi 0) ∧ (∫ u in Ioi (0 : ℝ), entropy u) = π ^ 2 / 6 := by { refine ⟨(fermiLog_integrable.add fermi_real_two.1).congr (Eventually.of_forall (fun u => (entropy_identity u).symm)), ?_⟩; simp_rw [entropy_identity]; rw [integral_add fermiLog_integrable fermi_real_two.1, integral_fermiLog, fermi_real_two.2]; ring }
private lemma logistic_antitone : Antitone logistic := by { intro u v huv; exact inv_anti₀ (by positivity) (add_le_add_right (exp_le_exp.mpr huv) 1) }
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
private lemma envelope_integrable : IntegrableOn (fun u : ℝ => (1 + u) * exp (-u)) (Ioi 0) := by { have h : IntegrableOn (fun u : ℝ => u * exp (-u)) (Ioi 0) := by { have h := GammaIntegral_convergent (s := 2) (by norm_num); norm_num at h; simpa only [mul_comm] using h }; apply (exp_integrable.add h).congr; filter_upwards with u; change exp (-u) + u * exp (-u) = (1 + u) * exp (-u); ring }
private lemma envelope_tail {U : ℝ} (hU : 0 ≤ U) : (∫ u in Ioi U, (1 + u) * exp (-u)) = (U + 2) * exp (-U) := by { have hi := envelope_integrable.mono_set (Ioi_subset_Ioi hU); have hl : Tendsto (fun u : ℝ => -(u + 2) * exp (-u)) atTop (𝓝 0) := by { have he : Tendsto (fun u : ℝ => exp (-u)) atTop (𝓝 0) := tendsto_exp_atBot.comp tendsto_neg_atTop_atBot; simpa [add_mul, neg_add, neg_mul] using (mul_exp_limit.add (he.const_mul 2)).neg }; have hd (u : ℝ) : HasDerivAt (fun v : ℝ => -(v + 2) * exp (-v)) ((1 + u) * exp (-u)) u := by { convert (((hasDerivAt_id u).add_const 2).neg).mul ((hasDerivAt_id u).neg.exp) using 1 <;> (try funext v) <;> simp only [id_eq, Pi.mul_apply, Pi.neg_apply] <;> ring }; have h := integral_Ioi_of_hasDerivAt_of_tendsto' (fun u _ => hd u) hi hl; convert h using 1 <;> ring }
private lemma entropy_truncated {U : ℝ} (hU : 0 ≤ U) : π ^ 2 / 6 - (U + 2) * exp (-U) ≤ ∫ u in (0 : ℝ)..U, entropy u := by { have hb : ∀ᵐ u ∂(volume.restrict (Ioi U)), entropy u ≤ (1 + u) * exp (-u) := by { filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu; rw [entropy_identity, add_mul, one_mul]; exact add_le_add (fermiLog_bounds u).2 (mul_le_mul_of_nonneg_left (logistic_le_exp u) (hU.trans hu.le)) }; have he := integral_mono_ae (entropy_integral.1.mono_set (Ioi_subset_Ioi hU)) (envelope_integrable.mono_set (Ioi_subset_Ioi hU)) hb; rw [envelope_tail hU] at he; rw [← intervalIntegral.integral_Ioi_sub_Ioi entropy_integral.1 hU, entropy_integral.2]; linarith }
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
lemma node_end (G : Mesh) : G.node G.n = G.U := by { dsimp [Mesh.node, Mesh.step]; exact mul_div_cancel₀ _ (by exact_mod_cast G.n_pos.ne') }
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
private lemma cell_entropy (G : Mesh) (i : ℕ) : (∫ u in G.node i..G.node (i+1), entropy u) - G.step * entropy (G.node (i+1)) ≤ G.step * (entropy (G.node i) - entropy (G.node (i+1))) := by { have hab : G.node i ≤ G.node (i+1) := by { linarith [step_pos G, node_step G i] }; have h : (∫ u in G.node i..G.node (i+1), entropy u) ≤ ∫ _ in G.node i..G.node (i+1), entropy (G.node i) := by { apply intervalIntegral.integral_mono_on_of_le_Ioo hab (entropy_continuous.intervalIntegrable (μ := volume) _ _) intervalIntegrable_const; intro u hu; exact entropy_antitone (node_nonneg G i) ((node_nonneg G i).trans hu.1.le) hu.1.le }; rw [intervalIntegral.integral_const, node_step, smul_eq_mul] at h; linarith }
private lemma truncated_le {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) (hp : ∀ u, 0 ≤ u → 0 ≤ f u) {U : ℝ} (hU : 0 ≤ U) : (∫ u in (0 : ℝ)..U, f u) ≤ ∫ u in Ioi (0 : ℝ), f u := by { rw [intervalIntegral.integral_of_le hU]; apply setIntegral_mono_set hf; { filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu using hp u hu.le }; { exact Eventually.of_forall (fun u hu => hu.1) } }
theorem grid_bounds (G : Mesh) : G.cost ≤ π ^ 2 / 6 + 2 * G.step * log 2 ∧ π ^ 2 / 3 - 2 * (G.U + 2) * exp (-G.U) - 2 * G.step * log 2 ≤ G.mass := by { have hq := intervalIntegral.sum_integral_adjacent_intervals (a := G.node) (n := G.n) (f := logistic) (fun _ _ => logistic_continuous.intervalIntegrable (μ := volume) _ _); have huq := intervalIntegral.sum_integral_adjacent_intervals (a := G.node) (n := G.n) (f := fun u => u * logistic u) (fun _ _ => (continuous_id.mul logistic_continuous).intervalIntegrable (μ := volume) _ _); have hf := intervalIntegral.sum_integral_adjacent_intervals (a := G.node) (n := G.n) (f := entropy) (fun _ _ => entropy_continuous.intervalIntegrable (μ := volume) _ _); rw [node_zero, node_end] at hq huq hf; constructor; { have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range G.n) => cell_cost G i); rw [Finset.sum_add_distrib, ← Finset.mul_sum, hq, huq] at h; have h₁ := truncated_le fermi_real_two.1 (fun u hu => mul_nonneg hu (logistic_range u).1.le) G.U_pos.le; have h₂ := truncated_le fermi_real_one.1 (fun u _ => (logistic_range u).1.le) G.U_pos.le; rw [fermi_real_two.2] at h₁; rw [fermi_real_one.2] at h₂; dsimp [Mesh.cost]; nlinarith [mul_le_mul_of_nonneg_left h₂ (step_pos G).le] }; { have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range G.n) => cell_entropy G i); rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub', node_zero, node_end, hf] at h; have hfU : 0 ≤ entropy G.U := binEntropy_nonneg (logistic_range G.U).1.le (logistic_range G.U).2.le; have h0 : entropy 0 = log 2 := by { rw [entropy, logistic, exp_zero, show (1 : ℝ) + 1 = 2 by norm_num]; exact binEntropy_two_inv }; rw [h0] at h; have ht := entropy_truncated G.U_pos.le; dsimp [Mesh.mass]; rw [← Finset.mul_sum]; nlinarith [mul_nonneg (step_pos G).le hfU] } }
theorem exists_good_grid {η ρ : ℝ} (hη : 0 < η) (hρ : 0 < ρ) : ∃ G : Mesh, G.cost ≤ (π ^ 2 / 6) * (1 + η / 2) ∧ π ^ 2 / 3 - ρ ≤ G.mass := by { have he : Tendsto (fun u : ℝ => exp (-u)) atTop (𝓝 0) := tendsto_exp_atBot.comp tendsto_neg_atTop_atBot; have ht : Tendsto (fun u : ℝ => 2 * (u + 2) * exp (-u)) atTop (𝓝 0) := by { simpa [add_mul, mul_add, mul_assoc] using (mul_exp_limit.add (he.const_mul 2)).const_mul 2 }; obtain ⟨U, hU, htU⟩ := ((eventually_ge_atTop (1 : ℝ)).and (ht.eventually_lt_const (by linarith : (0 : ℝ) < ρ / 2))).exists; have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num); let d := min ((π ^ 2 / 6) * η / (4 * log 2)) (ρ / (4 * log 2)); have hd : 0 < d := lt_min (by positivity) (by positivity); obtain ⟨n, hn⟩ := exists_nat_gt (max 1 (U / d)); have hn1 : 0 < n := by { have hnR : (1 : ℝ) < n := (le_max_left _ _).trans_lt hn; exact_mod_cast (lt_trans zero_lt_one hnR) }; let G : Mesh := ⟨U, n, by linarith, hn1⟩; have hs : G.step ≤ d := by { have hnR : (0 : ℝ) < n := by { exact_mod_cast hn1 }; apply (div_le_iff₀ hnR).mpr; have h := (div_lt_iff₀ hd).mp ((le_max_right _ _).trans_lt hn); simpa [mul_comm] using h.le }; have hs₁ : 2 * G.step * log 2 ≤ (π ^ 2 / 6) * η / 2 := by { have h := hs.trans (min_le_left _ _); have hd' : 0 < 4 * log (2 : ℝ) := by { positivity }; have h := (le_div_iff₀ hd').mp h; nlinarith }; have hs₂ : 2 * G.step * log 2 ≤ ρ / 2 := by { have h := hs.trans (min_le_right _ _); have hd' : 0 < 4 * log (2 : ℝ) := by { positivity }; have h := (le_div_iff₀ hd').mp h; nlinarith }; obtain ⟨hc, hm⟩ := grid_bounds G; refine ⟨G, ?_, ?_⟩; { nlinarith }; { change π ^ 2 / 3 - 2 * (U + 2) * exp (-U) - 2 * G.step * log 2 ≤ G.mass at hm; linarith } }
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Topology BigOperators
open Real Filter MeasureTheory Finset Set Asymptotics
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
private def term (m : ℕ) (p : ℝ) (j : ℕ) : ℝ := (m.choose j : ℝ) * p ^ j * (1 - p) ^ (m - j)
private lemma term_succ (m j : ℕ) (p : ℝ) (hj : j < m) : term m p (j + 1) * ((j + 1 : ℕ) : ℝ) * (1 - p) = term m p j * ((m - j : ℕ) : ℝ) * p := by { have hc : (m.choose (j + 1) : ℝ) * (j + 1 : ℕ) = (m.choose j : ℝ) * (m - j : ℕ) := by { exact_mod_cast Nat.choose_succ_right_eq m j }; have hd : m - j = m - (j + 1) + 1 := by { omega }; dsimp only [term]; have hp : p ^ (j + 1) = p ^ j * p := pow_succ p j; have hq : (1 - p) ^ (m - j) = (1 - p) ^ (m - (j + 1)) * (1 - p) := by { rw [hd, pow_succ] }; rw [hp, hq]; linear_combination p ^ j * p * (1 - p) ^ (m - (j + 1)) * (1 - p) * hc }
private lemma term_maximum (m a : ℕ) (ha : a ≤ m) (ha0 : 0 < a) (ham : a < m) (j : ℕ) (hj : j ≤ m) :
    term m ((a : ℝ) / m) j ≤ term m ((a : ℝ) / m) a := by
  have hm : (0 : ℝ) < m := by exact_mod_cast ha0.trans ham
  have hap : (0 : ℝ) < a := by exact_mod_cast ha0
  have haR : (a : ℝ) < m := by exact_mod_cast ham
  let p : ℝ := (a : ℝ) / m
  have hp : 0 < p := div_pos hap hm
  have hp1 : 0 < 1 - p := sub_pos.mpr ((div_lt_one hm).mpr haR)
  have hnonneg (i : ℕ) : 0 ≤ term m p i := by unfold term; positivity
  have hrelation (i : ℕ) (hi : i < m) := term_succ m i p hi
  have hcoeff (i : ℕ) (hi : i ≤ m) : ((m - i : ℕ) : ℝ) * p - (i + 1 : ℕ) * (1 - p) = (a : ℝ) - i - 1 + p := by
    rw [Nat.cast_sub hi, Nat.cast_add, Nat.cast_one]
    dsimp only [p]
    field_simp <;> ring
  have hup (i : ℕ) (hi : i < a) : term m p i ≤ term m p (i + 1) := by
    have him : i < m := hi.trans ham
    have hle : ((i + 1 : ℕ) : ℝ) * (1 - p) ≤ ((m - i : ℕ) : ℝ) * p := by
      have hh : (i : ℝ) + 1 ≤ a := by exact_mod_cast hi
      have := hcoeff i him.le
      linarith
    have hh := mul_le_mul_of_nonneg_left hle (hnonneg i)
    have hr := hrelation i him
    have hd : 0 < ((i + 1 : ℕ) : ℝ) * (1 - p) := by positivity
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith only [hh, hr]
  have hdown (i : ℕ) (hai : a ≤ i) (him : i < m) : term m p (i + 1) ≤ term m p i := by
    have hle : ((m - i : ℕ) : ℝ) * p ≤ ((i + 1 : ℕ) : ℝ) * (1 - p) := by
      have hh : (a : ℝ) ≤ i := by exact_mod_cast hai
      have := hcoeff i him.le
      have : p < 1 := by linarith
      linarith
    have hh := mul_le_mul_of_nonneg_left hle (hnonneg i)
    have hr := hrelation i him
    have hd : 0 < ((i + 1 : ℕ) : ℝ) * (1 - p) := by positivity
    apply (mul_le_mul_iff_left₀ hd).mp
    nlinarith only [hh, hr]
  change term m p j ≤ term m p a
  rcases le_total j a with hja | haj
  · have hh : ∀ b, j ≤ b → b ≤ a → term m p j ≤ term m p b := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ b hb ih =>
        intro hba
        exact (ih (by omega)).trans (hup b (by omega))
    exact hh a hja le_rfl
  · have hh : ∀ b, a ≤ b → b ≤ m → term m p b ≤ term m p a := by
      intro b hb
      induction b, hb using Nat.le_induction with
      | base => exact fun _ => le_rfl
      | succ b hb ih =>
        intro hbm
        exact (hdown b hb (by omega)).trans (ih (by omega))
    exact hh j haj hj
theorem log_choose_ge_binEntropy (m a : ℕ) (ha : a ≤ m) : (m : ℝ) * binEntropy ((a : ℝ) / m) - log ((m : ℝ) + 1) ≤
      log (m.choose a : ℝ) := by
  by_cases ha0 : a = 0
  · subst a
    simp only [Nat.cast_zero, zero_div, binEntropy_zero, mul_zero, zero_sub, Nat.choose_zero_right, Nat.cast_one, log_one]
    exact neg_nonpos.mpr (log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m]))
  by_cases ham : a = m
  · subst a
    have hm : (m : ℝ) ≠ 0 := by exact_mod_cast ha0
    simp only [div_self hm, binEntropy_one, mul_zero, zero_sub, Nat.choose_self, Nat.cast_one, log_one]
    exact neg_nonpos.mpr (log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m]))
  have ha0' : 0 < a := Nat.pos_of_ne_zero ha0
  have ham' : a < m := lt_of_le_of_ne ha ham
  have hm : (0 : ℝ) < m := by exact_mod_cast ha0'.trans ham'
  have haR : (0 : ℝ) < a := by exact_mod_cast ha0'
  have haRm : (a : ℝ) < m := by exact_mod_cast ham'
  let p : ℝ := (a : ℝ) / m
  have hp : 0 < p := div_pos haR hm
  have hp1 : 0 < 1 - p := sub_pos.mpr ((div_lt_one hm).mpr haRm)
  have hchoose : (0 : ℝ) < m.choose a := by exact_mod_cast Nat.choose_pos ha
  have hterm : 0 < term m p a := by unfold term; positivity
  have hsum : (∑ j ∈ range (m + 1), term m p j) = 1 := by
    have h := add_pow p (1 - p) m
    simp only [show p + (1 - p) = 1 by ring, one_pow] at h
    calc
      _ = ∑ j ∈ range (m + 1), p ^ j * (1 - p) ^ (m - j) * (m.choose j : ℝ) := by
        apply sum_congr rfl
        intro j hj
        dsimp only [term]
        ring
      _ = 1 := h.symm
  have hmax : 1 ≤ ((m : ℝ) + 1) * term m p a := by
    calc
      1 = ∑ j ∈ range (m + 1), term m p j := hsum.symm
      _ ≤ ∑ _j ∈ range (m + 1), term m p a := by
        apply sum_le_sum
        intro j hj
        exact term_maximum m a ha ha0' ham' j (by simpa using (mem_range.mp hj))
      _ = _ := by simp
  have hlog := log_le_log (by norm_num : (0 : ℝ) < 1) hmax
  have hlogterm : log (term m p a) = log (m.choose a : ℝ) - (m : ℝ) * binEntropy p := by
    dsimp only [term]
    rw [log_mul (mul_pos hchoose (pow_pos hp _)).ne' (pow_pos hp1 _).ne', log_mul hchoose.ne' (pow_pos hp _).ne', log_pow, log_pow,
      binEntropy, log_inv, log_inv, Nat.cast_sub ha]
    have hmp : (m : ℝ) * p = a := by dsimp only [p]; field_simp
    linear_combination -(log p - log (1 - p)) * hmp
  rw [log_one, log_mul (by positivity : (m : ℝ) + 1 ≠ 0) hterm.ne', hlogterm] at hlog
  change (m : ℝ) * binEntropy p - log ((m : ℝ) + 1) ≤ _
  linarith
def entropyLower (m a : ℕ) : ℝ := (m : ℝ) * binEntropy ((a : ℝ) / m) - log ((m : ℝ) + 1)
theorem entropy_lower_scaled {α : Type*} {l : Filter α} (W : α → ℝ) (n k : α → ℕ) {d q : ℝ} (hW : Tendsto W l atTop) (hd : 0 < d) (hn : Tendsto (fun x => (n x : ℝ) / W x) l (𝓝 d)) (hk : Tendsto (fun x => (k x : ℝ) / W x) l (𝓝 (d * q))) : Tendsto (fun x => entropyLower (n x) (k x) / W x) l (𝓝 (d * binEntropy q)) := by { have hnR : Tendsto (fun x => (n x : ℝ)) l atTop := by { apply (hW.atTop_mul_pos hd hn).congr'; filter_upwards [hW.eventually_gt_atTop 0] with x hx; exact mul_div_cancel₀ _ hx.ne' }; have hq : Tendsto (fun x => (k x : ℝ) / n x) l (𝓝 q) := by { have h := hk.div hn hd.ne'; rw [mul_div_cancel_left₀ q hd.ne'] at h; apply h.congr'; filter_upwards [hW.eventually_gt_atTop 0] with x hx; exact div_div_div_cancel_right₀ hx.ne' _ _ }; have hn1 : Tendsto (fun x => ((n x : ℝ) + 1) / W x) l (𝓝 d) := by { have h := hn.add (hW.const_div_atTop 1); simpa only [add_div, add_zero] using h }; have hlog : Tendsto (fun x => log ((n x : ℝ) + 1) / W x) l (𝓝 0) := by { have htop := tendsto_atTop_add_const_right l 1 hnR; have h := (isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp htop).mul hn1; simp only [zero_mul] at h; apply h.congr'; filter_upwards [] with x; dsimp only [Function.comp_def, id_eq]; exact div_mul_div_cancel₀ (by positivity : (n x : ℝ) + 1 ≠ 0) }; have h := (hn.mul (binEntropy_continuous.continuousAt.tendsto.comp hq)).sub hlog; simp only [sub_zero] at h; apply h.congr'; filter_upwards [] with x; dsimp only [entropyLower, Function.comp_def]; ring }
theorem floor_scaled {α : Type*} {l : Filter α} (W : α → ℝ) (M : α → ℕ) {d q : ℝ} (hW : Tendsto W l atTop) (hd : 0 < d) (hq : 0 ≤ q) (hM : Tendsto (fun x => (M x : ℝ) / W x) l (𝓝 d)) : Tendsto (fun x => (⌊q * (M x : ℝ)⌋₊ : ℝ) / W x) l (𝓝 (q * d)) := by { have hMR : Tendsto (fun x => (M x : ℝ)) l atTop := by { apply (hW.atTop_mul_pos hd hM).congr'; filter_upwards [hW.eventually_gt_atTop 0] with x hx; exact mul_div_cancel₀ _ hx.ne' }; have h := ((tendsto_nat_floor_mul_div_atTop hq).comp hMR).mul hM; apply h.congr'; filter_upwards [hMR.eventually_gt_atTop 0] with x hx; exact div_mul_div_cancel₀ hx.ne' }
theorem min_scaled {α : Type*} {l : Filter α} (W : α → ℝ) (M N : α → ℕ) {d : ℝ} (hW : Tendsto W l atTop) (hM : Tendsto (fun x => (M x : ℝ) / W x) l (𝓝 d)) (hN : Tendsto (fun x => (N x : ℝ) / W x) l (𝓝 d)) : Tendsto (fun x => ((min (M x) (N x) : ℕ) : ℝ) / W x) l (𝓝 d) := by { have h := hM.min hN; simp only [min_self] at h; apply h.congr'; filter_upwards [hW.eventually_gt_atTop 0] with x hx; rw [Nat.cast_min, min_div_div_right hx.le] }
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit
def correctionMajorant (s : ℝ) : ℝ := π ^ 2 / (6 * (1 - π ^ 2 / (6 * s ^ 2)))
theorem kernel_correction_upper {s : ℝ} (hs : π ≤ s) : 0 ≤ s * (π / sin (π / s) - s) ∧ s * (π / sin (π / s) - s) ≤ correctionMajorant s := by { have hs0 : 0 < s := pi_pos.trans_le hs; let t : ℝ := π / s; have ht0 : 0 < t := div_pos pi_pos hs0; have ht1 : t ≤ 1 := (div_le_one hs0).mpr hs; have htp : t < π := by { dsimp [t]; exact div_lt_self pi_pos (by linarith [pi_gt_three]) }; have hsin : 0 < sin t := sin_pos_of_pos_of_lt_pi ht0 htp; have hd : 0 < 1 - t ^ 2 / 6 := by { nlinarith }; have hcube := sin_ge_sub_cube ht0.le; have hquot : t / sin t ≤ 1 / (1 - t ^ 2 / 6) := by { apply (div_le_div_iff₀ hsin hd).mpr; nlinarith }; have hnonneg : 0 ≤ t / sin t - 1 := by { have h : 1 ≤ t / sin t := (le_div_iff₀ hsin).mpr (by simpa only [one_mul] using sin_le ht0.le); linarith }; have hbound : t / sin t - 1 ≤ t ^ 2 / (6 * (1 - t ^ 2 / 6)) := by { have hid : 1 / (1 - t ^ 2 / 6) - 1 = t ^ 2 / (6 * (1 - t ^ 2 / 6)) := by { have hd' : 6 - t ^ 2 ≠ 0 := by { nlinarith }; field_simp [hd.ne', hd'] <;> ring }; linarith }; have hid : s * (π / sin (π / s) - s) = s ^ 2 * (t / sin t - 1) := by { dsimp [t]; field_simp [hs0.ne', hsin.ne'] <;> ring }; rw [hid]; constructor; { exact mul_nonneg (sq_nonneg _) hnonneg }; { have hb := mul_le_mul_of_nonneg_left hbound (sq_nonneg s); convert hb using 1; dsimp only [correctionMajorant, t]; field_simp [hs0.ne'] <;> ring } }
theorem correction_majorant_limit : Tendsto correctionMajorant atTop (𝓝 (π ^ 2 / 6)) := by { have hi : Tendsto (fun s : ℝ => 1 / s) atTop (𝓝 0) := tendsto_id.const_div_atTop 1; have h := (tendsto_const_nhds (x := π ^ 2)).div (((tendsto_const_nhds (x := (1 : ℝ))).sub ((hi.pow 2).const_mul (π ^ 2 / 6))).const_mul 6) (by norm_num : 6 * (1 - π ^ 2 / 6 * 0 ^ 2) ≠ 0); norm_num only [zero_pow, mul_zero, sub_zero, one_mul] at h; apply h.congr'; filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs; change π ^ 2 / (6 * (1 - π ^ 2 / 6 * (1 / s) ^ 2)) = π ^ 2 / (6 * (1 - π ^ 2 / (6 * s ^ 2))); congr 1; ring }
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.KernelLimit
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail
private lemma log_softplus_le_exp (v : ℝ) : log (1 + exp v) ≤ exp v := by { simpa only [add_sub_cancel_left] using log_le_sub_one_of_pos (by positivity : 0 < 1 + exp v) }
theorem finite_power_tail {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) (S : Finset ℕ) (hS : ∀ n ∈ S, N < n) :
    ∑ n ∈ S, (n : ℝ) ^ (-s) ≤ (N : ℝ) ^ (1 - s) / (s - 1) := by
  classical
  let M := S.sup id
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsub : S ⊆ Finset.Ioc N M := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨hS n hn, Finset.le_sup (f := id) hn⟩
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-s)) (Icc (N : ℝ) M) := by
    intro a ha b hb hab
    exact rpow_le_rpow_of_nonpos (hN0.trans_le ha.1) hab (by linarith)
  have hsum : (∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-s)) = ∑ n ∈ Finset.Ico N M, ((n + 1 : ℕ) : ℝ) ^ (-s) := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, ← Finset.sum_Ico_add']
  calc
    _ ≤ ∑ n ∈ Finset.Ioc N M, (n : ℝ) ^ (-s) := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => rpow_nonneg (Nat.cast_nonneg _) _)
    _ = _ := hsum
    _ ≤ ∫ t in Ioi (N : ℝ), t ^ (-s) := hanti.sum_Ico_le_integral (integrableOn_Ioi_rpow_of_lt (by linarith) hN0)
        (fun t ht => rpow_nonneg (hN0.trans ht).le _)
    _ = (N : ℝ) ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) hN0]
      rw [show -s + 1 = 1 - s by ring]
      have h1 : s - 1 ≠ 0 := by linarith
      have h2 : 1 - s ≠ 0 := by linarith
      field_simp [h1, h2]
      ring
theorem small_weight_tail {P s : ℝ} (hP : 2 ≤ P) (hs : 0 ≤ s) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n ∧ (n : ℝ) ≤ P / 2) :
    ∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ P * (1 / 2 : ℝ) ^ s := by
  have hP0 : 0 < P := by linarith
  have hsub : S ⊆ Finset.Icc 1 ⌊P / 2⌋₊ := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(hS n hn).1, (Nat.le_floor_iff (by positivity)).mpr (hS n hn).2⟩
  have hcard : (S.card : ℝ) ≤ P := by
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at hc
    have hc' : (S.card : ℝ) ≤ ⌊P / 2⌋₊ := by exact_mod_cast hc
    exact hc'.trans ((Nat.floor_le (by positivity)).trans (by linarith))
  have hpoint (n : ℕ) (hn : n ∈ S) : log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ (1 / 2 : ℝ) ^ s := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (hS n hn).1
    have hratio : (n : ℝ) / P ≤ 1 / 2 := (div_le_iff₀ hP0).mpr (by linarith [(hS n hn).2])
    have hl : log ((n : ℝ) / P) ≤ log (1 / 2 : ℝ) := log_le_log (div_pos hn0 hP0) hratio
    have hl0 : log ((n : ℝ) / P) ≤ 0 := log_nonpos (div_nonneg hn0.le hP0.le) (hratio.trans (by norm_num))
    refine (log_softplus_le_exp _).trans ?_
    rw [abs_of_nonpos hl0, neg_mul_neg, rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact exp_le_exp.mpr (by nlinarith)
  calc
    _ ≤ ∑ n ∈ S, (1 / 2 : ℝ) ^ s := Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * (1 / 2 : ℝ) ^ s := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (rpow_nonneg (by norm_num) _)
theorem large_weight_tail {P s : ℝ} (hP : 2 ≤ P) (hs : 2 ≤ s) (S : Finset ℕ) (hS : ∀ n ∈ S, 2 * P < (n : ℝ)) :
    ∑ n ∈ S, log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ 2 * P * (2 / 3 : ℝ) ^ s := by
  have hP0 : 0 < P := by linarith
  let N := ⌊2 * P⌋₊
  have hNlo : 3 * P / 2 ≤ (N : ℝ) := by
    have h := Nat.lt_floor_add_one (2 * P)
    dsimp [N]
    linarith
  have hN0 : (0 : ℝ) < N := by nlinarith
  have hNN : 0 < N := by exact_mod_cast hN0
  have hS' : ∀ n ∈ S, N < n := by
    intro n hn
    exact (Nat.floor_lt (by positivity : 0 ≤ 2 * P)).mpr (hS n hn)
  have hpoint (n : ℕ) (hn : n ∈ S) : log (1 + exp (-s * |log ((n : ℝ) / P)|)) ≤ P ^ s * (n : ℝ) ^ (-s) := by
    have hn0 : (0 : ℝ) < n := by linarith [hS n hn]
    have hratio : 1 ≤ (n : ℝ) / P := (le_div_iff₀ hP0).mpr (by linarith [hS n hn])
    have hl : 0 ≤ log ((n : ℝ) / P) := log_nonneg hratio
    refine (log_softplus_le_exp _).trans_eq ?_
    rw [abs_of_nonneg hl, log_div hn0.ne' hP0.ne', rpow_def_of_pos hP0, rpow_def_of_pos hn0, ← exp_add]
    congr 1
    ring
  have hfinite := finite_power_tail (by linarith : 1 < s) hNN S hS'
  have hmono : (N : ℝ) ^ (1 - s) ≤ (3 * P / 2) ^ (1 - s) := rpow_le_rpow_of_nonpos (by positivity) hNlo (by linarith)
  have hid : P ^ s * (3 * P / 2) ^ (1 - s) = (3 * P / 2) * (2 / 3 : ℝ) ^ s := by
    rw [rpow_sub (by positivity), rpow_one]
    calc
      P ^ s * ((3 * P / 2) / (3 * P / 2) ^ s) = (3 * P / 2) * (P ^ s / (3 * P / 2) ^ s) := by ring
      _ = (3 * P / 2) * (P / (3 * P / 2)) ^ s := by
        rw [div_rpow hP0.le (by positivity)]
      _ = _ := by
        congr 2
        field_simp [hP0.ne'] <;> ring
  calc
    _ ≤ ∑ n ∈ S, P ^ s * (n : ℝ) ^ (-s) := Finset.sum_le_sum hpoint
    _ = P ^ s * ∑ n ∈ S, (n : ℝ) ^ (-s) := by rw [Finset.mul_sum]
    _ ≤ P ^ s * ((N : ℝ) ^ (1 - s) / (s - 1)) := mul_le_mul_of_nonneg_left hfinite (rpow_nonneg hP0.le _)
    _ ≤ P ^ s * ((3 * P / 2) ^ (1 - s) / (s - 1)) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hmono (by linarith)) (rpow_nonneg hP0.le _)
    _ = ((3 * P / 2) * (2 / 3 : ℝ) ^ s) / (s - 1) := by rw [← mul_div_assoc, hid]
    _ ≤ (3 * P / 2) * (2 / 3 : ℝ) ^ s := div_le_self (by positivity) (by linarith)
    _ ≤ _ := by gcongr; linarith
theorem geometric_sqrt_decay {c q : ℝ} (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun t : ℝ => t * sqrt t * q ^ (c * sqrt t)) atTop (𝓝 0) := by
  let b : ℝ := -c * log q
  have hb : 0 < b := mul_pos_of_neg_of_neg (by linarith) (log_neg hq0 hq1)
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 3 b hb).comp tendsto_sqrt_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_def, rpow_ofNat]
  rw [rpow_def_of_pos hq0]
  have he : -b * sqrt t = log q * (c * sqrt t) := by dsimp [b]; ring
  have hp : sqrt t ^ 3 = t * sqrt t := by
    calc
      sqrt t ^ 3 = sqrt t ^ 2 * sqrt t := by ring
      _ = t * sqrt t := by rw [sq_sqrt ht.le]
  rw [he, hp]
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Tail
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open Exchange Entropy.KernelLimit
private lemma half_power (s : ℝ) : (1 / 2 : ℝ) ^ s = (2 : ℝ) ^ (-s) := by { rw [div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2), one_rpow, one_div, rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] }
def majorant (P s : ℝ) : ℝ := P / (s * log P) * correctionMajorant s + (s / 2 + 2) * P * (1 / 2 : ℝ) ^ s / log P + 112 * log 2 * (P / log P ^ 2) + P * (1 / 2 : ℝ) ^ s + 2 * P * (2 / 3 : ℝ) ^ s
theorem remainder_le_majorant : ∀ᶠ P : ℝ in atTop, ∀ s : ℝ, π ≤ s → 2 ≤ s → ∀ x : ℝ, remainder P s x ≤ majorant P s := by classical { filter_upwards [Exchange.central_prime_weight_upper, eventually_ge_atTop (2 : ℝ)] with P hcentral hP; intro s hsπ hs x; have hP0 : 0 < P := by { linarith }; have hl : 0 < log P := log_pos (by linarith); have hs0 : 0 < s := by { linarith }; let S := Nat.primesLE ⌊x⌋₊; let A := S.filter (fun p : ℕ => (p : ℝ) ≤ P / 2); let B := S.filter (fun p : ℕ => P / 2 < (p : ℝ) ∧ (p : ℝ) ≤ 2 * P); let C := S.filter (fun p : ℕ => 2 * P < (p : ℝ)); have hpartition : remainder P s x = (∑ p ∈ A, weight P s p) + (∑ p ∈ B, weight P s p) + ∑ p ∈ C, weight P s p := by { dsimp only [remainder, A, B, C, S]; simp only [sum_filter]; rw [← sum_add_distrib, ← sum_add_distrib]; apply sum_congr rfl; intro p hp; by_cases hp1 : (p : ℝ) ≤ P / 2; { have hp2 : ¬ 2 * P < (p : ℝ) := by { linarith }; simp [hp1, hp2] }; { by_cases hp2 : (p : ℝ) ≤ 2 * P; { simp [hp1, hp2, lt_of_not_ge hp1] }; { simp [hp1, hp2, lt_of_not_ge hp2] } } }; have hA : (∑ p ∈ A, weight P s p) ≤ P * (1 / 2 : ℝ) ^ s := by { apply Entropy.Tail.small_weight_tail hP hs0.le A; intro p hp; obtain ⟨hpS, hpP⟩ := mem_filter.mp hp; exact ⟨(Nat.mem_primesLE.mp hpS).2.pos, hpP⟩ }; have hC : (∑ p ∈ C, weight P s p) ≤ 2 * P * (2 / 3 : ℝ) ^ s := by { apply Entropy.Tail.large_weight_tail hP hs C; intro p hp; exact (mem_filter.mp hp).2 }; have hsub : B ⊆ primeInterval (P / 2) (2 * P) := by { intro p hp; obtain ⟨hpS, hpL, hpU⟩ := mem_filter.mp hp; refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, (Nat.mem_primesLE.mp hpS).2⟩; { exact (Nat.floor_lt (by positivity : 0 ≤ P / 2)).mpr hpL }; { exact (Nat.le_floor_iff (by positivity : 0 ≤ 2 * P)).mpr hpU } }; have hB : (∑ p ∈ B, weight P s p) ≤ (∫ t in (P / 2)..(2 * P), weight P s t) / log P + 112 * log 2 * (P / log P ^ 2) := by { exact (sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => weight_nonneg _ _ _)).trans (hcentral s hs0.le) }; have hi := Exchange.central_integral_upper hP0 (by linarith : 1 < s); have hi' := div_le_div_of_nonneg_right hi hl.le; rw [← half_power s, add_div] at hi'; have hk := (kernel_correction_upper hsπ).2; have hk' : P * (π / sin (π / s) - s) / log P ≤ P / (s * log P) * correctionMajorant s := by { have h := mul_le_mul_of_nonneg_left hk (div_nonneg hP0.le (mul_pos hs0 hl).le); convert h using 1 <;> field_simp [hs0.ne', hl.ne'] <;> ring }; rw [hpartition]; dsimp only [majorant]; have h := add_le_add (add_le_add hA hB) hC; linarith only [h, hi', hk'] }
private lemma sharpness_top {c : ℝ} (hc : 0 < c) : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc
theorem majorant_limit {c : ℝ} (hc : 0 < c) : Tendsto (fun P : ℝ => majorant P (c * sqrt (log P)) / (P / (log P * sqrt (log P)))) atTop (𝓝 (π ^ 2 / (6 * c))) := by { have hhalf := (Entropy.Tail.geometric_sqrt_decay hc (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).comp tendsto_log_atTop; have hthird := (Entropy.Tail.geometric_sqrt_decay hc (by norm_num : (0 : ℝ) < 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)).comp tendsto_log_atTop; have hsqrt : Tendsto (fun P : ℝ => 1 / sqrt (log P)) atTop (𝓝 0) := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_div_atTop 1; have hlog : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop 1; have hmain := (correction_majorant_limit.comp (sharpness_top hc)).div_const c; have hcontinuum := hhalf.mul ((hsqrt.const_mul (c / 2)).add (hlog.const_mul 2)); have hcount := hsqrt.const_mul (112 * log 2); have h := ((((hmain.add hcontinuum).add hcount).add hhalf).add (hthird.const_mul 2)); norm_num only [mul_zero, zero_add, add_zero] at h; convert h.congr' (show _ =ᶠ[atTop] _ from ?_) using 1; { ring }; { filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; have hP0 : P ≠ 0 := by { linarith }; have hl := log_pos hP; have hs := sqrt_pos.mpr hl; change correctionMajorant (c * sqrt (log P)) / c + (log P * sqrt (log P) * (1 / 2 : ℝ) ^ (c * sqrt (log P))) * (c / 2 * (1 / sqrt (log P)) + 2 * (1 / log P)) + 112 * log 2 * (1 / sqrt (log P)) + log P * sqrt (log P) * (1 / 2 : ℝ) ^ (c * sqrt (log P)) + 2 * (log P * sqrt (log P) * (2 / 3 : ℝ) ^ (c * sqrt (log P))) = majorant P (c * sqrt (log P)) / (P / (log P * sqrt (log P))); dsimp only [majorant]; generalize hr : sqrt (log P) = r; have hr0 : 0 < r := by { rw [← hr]; exact hs }; have hr2 : r ^ 2 = log P := by { rw [← hr]; exact sq_sqrt hl.le }; rw [← hr2]; field_simp [hP0, hr0.ne', hc.ne'] <;> ring } }
theorem moving_weight_upper {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) : ∀ᶠ P : ℝ in atTop, ∀ x : ℝ, remainder P (c * sqrt (log P)) x ≤ (π ^ 2 / (6 * c) + ε) * (P / (log P * sqrt (log P))) := by { filter_upwards [remainder_le_majorant, (sharpness_top hc).eventually_ge_atTop π, (sharpness_top hc).eventually_ge_atTop 2, (majorant_limit hc).eventually_lt_const (by linarith : π ^ 2 / (6 * c) < π ^ 2 / (6 * c) + ε), eventually_gt_atTop (1 : ℝ)] with P hbound hsπ hs hlimit hP; intro x; refine (hbound _ hsπ hs x).trans ?_; have hscale : 0 < P / (log P * sqrt (log P)) := by { have := log_pos hP; positivity }; exact ((div_lt_iff₀ hscale).mp hlimit).le }
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
open D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
open D5.S3.Arith.Robin.Analytic.OmegaTail.Selection
namespace D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
open D5.S3.Arith.Robin.Analytic.OmegaTailUpper
open D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
open D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy.Exchange
def secondScale (x : ℝ) : ℝ := log x / (log (log x) * sqrt (log (log x)))
def saddle (P : ℝ) : ℝ := π / (2 * sqrt 3) * sqrt (log P)
def eulerCost : ℝ := log (1 + ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ))
private lemma pseries_le_square {s : ℝ} (hs : 2 ≤ s) : (∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ ∑' n : ℕ, (n : ℝ) ^ (-2 : ℝ) := by { apply (Real.summable_nat_rpow.mpr (by linarith : -s < -1)).tsum_le_tsum ?_ (Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)); intro n; by_cases hn : n = 0; { subst n; simp [Real.zero_rpow (by linarith : -s ≠ 0)] }; { apply Real.rpow_le_rpow_of_exponent_le; { exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn) }; { linarith } } }
theorem rankin_reduction {x s : ℝ} (hx : exp 1 < x) (hs : 2 ≤ s) : (tailCount 1 x : ℝ) ≤ exp (s * budget (log x) + remainder (log x) s x + eulerCost) := by { have hx0 : 0 < x := (exp_pos 1).trans hx; have hL : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx; have hL0 : 0 < log x := zero_lt_one.trans hL; have hs0 : 0 < s := by { linarith }; have hz : 1 ≤ (log x) ^ s := Real.one_le_rpow hL.le hs0.le; have h := rankin_exponential_bound (T := threshold 1 x) (by linarith : 1 < s) hz hx0; have hprimes : ((Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime) = Nat.primesLE ⌊x⌋₊ := by { rw [Nat.primesLE_eq_filter_Ioc_zero]; congr 1 }; rw [hprimes, prime_weight_split hL0 (log_le_sub_one_of_pos hx0 |>.trans (by linarith)) hs0.le] at h; have heq : s * log x - threshold 1 x * log ((log x) ^ s) + s * ((Nat.primeCounting ⌊log x⌋₊ : ℝ) * log (log x) - Chebyshev.theta (log x)) = s * budget (log x) := by { rw [log_rpow hL0]; dsimp only [threshold, scale, budget, D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount]; field_simp [(log_pos hL).ne'] <;> ring }; have hcost : log (1 + ∑' n : ℕ, (n : ℝ) ^ (-s)) ≤ eulerCost := by { apply log_le_log; { positivity }; { simpa only [add_comm] using add_le_add_left (pseries_le_square hs) 1 } }; change (tailCount 1 x : ℝ) ≤ _ at h; refine h.trans (exp_le_exp.mpr ?_); linarith only [heq, hcost] }
private lemma log_rpow_over_id_zero : Tendsto (fun P : ℝ => (log P * sqrt (log P)) / P) atTop (𝓝 0) := by { have h := (isLittleO_log_rpow_rpow_atTop (3 / 2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero; apply h.congr'; filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; rw [rpow_one, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add (log_pos hP), rpow_one, ← sqrt_eq_rpow] }
theorem secondScale_top : Tendsto secondScale atTop atTop := by { have hp : ∀ᶠ P : ℝ in atTop, 0 < (log P * sqrt (log P)) / P := by { filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; exact div_pos (mul_pos (log_pos hP) (sqrt_pos.mpr (log_pos hP))) (by linarith) }; have h := tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨log_rpow_over_id_zero, hp⟩); change Tendsto (fun x : ℝ => log x / (log (log x) * sqrt (log (log x)))) atTop atTop; simpa only [inv_div, Function.comp_def] using h.comp tendsto_log_atTop }
theorem saddle_budget_limit : Tendsto (fun P : ℝ => saddle P * budget P / (P / (log P * sqrt (log P)))) atTop (𝓝 (π / sqrt 3)) := by
  have h := budget_limit.const_mul (π / (2 * sqrt 3))
  convert h.congr' (show (fun P : ℝ =>
      π / (2 * sqrt 3) * (budget P / (P / log P ^ 2))) =ᶠ[atTop]
        (fun P => saddle P * budget P / (P / (log P * sqrt (log P)))) from ?_) using 1
  · field_simp
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hlog := log_pos hP
    dsimp only [saddle]
    generalize hr : sqrt (log P) = r
    have hr0 : 0 < r := by rw [← hr]; exact sqrt_pos.mpr hlog
    have hr2 : r ^ 2 = log P := by rw [← hr]; exact sq_sqrt hlog.le
    rw [← hr2]
    field_simp [(show P ≠ 0 by linarith), hr0.ne'] <;> ring
private lemma saddle_top : Tendsto saddle atTop atTop := by { have hc : 0 < π / (2 * sqrt 3) := by { positivity }; exact (tendsto_const_mul_atTop_of_pos hc).mpr (tendsto_sqrt_atTop.comp tendsto_log_atTop) }
theorem upper : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, (tailCount 1 x : ℝ) ≤ exp ((2 * π / sqrt 3 + ε) * log x / (log (log x)) ^ (3 / 2 : ℝ)) := by
  intro ε hε
  have hc : 0 < π / (2 * sqrt 3) := by positivity
  have hb := saddle_budget_limit.comp tendsto_log_atTop
  have he := secondScale_top.const_div_atTop eulerCost
  have hsum := (hb.add he).eventually_lt_const (by linarith : π / sqrt 3 + 0 < π / sqrt 3 + ε / 2)
  have hR := tendsto_log_atTop.eventually (Entropy.moving_weight_upper hc (by linarith : 0 < ε / 2))
  have hcoef : π ^ 2 / (6 * (π / (2 * sqrt 3))) = π / sqrt 3 := by
    have hsqrt := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hp := pi_pos.ne'
    have hs := (sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
    field_simp [hp, hs]
    nlinarith
  filter_upwards [hsum, hR, (saddle_top.comp tendsto_log_atTop).eventually_ge_atTop 2, eventually_gt_atTop (exp 1)] with x hsum hR hs hx
  have hx0 : 0 < x := (exp_pos 1).trans hx
  have hL : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx
  have hell : 0 < log (log x) := log_pos hL
  have hscale : 0 < secondScale x := by dsimp [secondScale]; positivity
  have hfront : saddle (log x) * budget (log x) + eulerCost ≤ (π / sqrt 3 + ε / 2) * secondScale x := by
    have hsum' : (saddle (log x) * budget (log x) + eulerCost) / secondScale x < π / sqrt 3 + ε / 2 := by
      simpa only [secondScale, Function.comp_def, ← add_div] using hsum
    exact ((div_lt_iff₀ hscale).mp hsum').le
  have hrem : remainder (log x) (saddle (log x)) x ≤ (π / sqrt 3 + ε / 2) * secondScale x := by
    simpa only [saddle, secondScale, hcoef] using hR x
  refine (rankin_reduction hx hs).trans (exp_le_exp.mpr ?_)
  have heq : (log (log x)) ^ (3 / 2 : ℝ) = log (log x) * sqrt (log (log x)) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add hell,
      rpow_one, ← sqrt_eq_rpow]
  rw [heq, show (2 * π / sqrt 3 + ε) * log x /
      (log (log x) * sqrt (log (log x))) =
      (2 * π / sqrt 3 + ε) * secondScale x by dsimp [secondScale]; ring]
  simp only [Function.comp_def]
  calc
    _ = (saddle (log x) * budget (log x) + eulerCost) +
        remainder (log x) (saddle (log x)) x := by ring
    _ ≤ (π / sqrt 3 + ε / 2) * secondScale x +
        (π / sqrt 3 + ε / 2) * secondScale x := add_le_add hfront hrem
    _ = _ := by ring
def thresholdK (P : ℝ) : ℕ := ⌊P / log P + P / log P ^ 2⌋₊ + 1
def excess (P : ℝ) : ℕ := Nat.primeCounting ⌊P⌋₊ - thresholdK P
def coreBudget (P : ℝ) : ℝ := P - Chebyshev.theta P + (excess P : ℝ) * log (P / 2)
private lemma inverse_log_scale (n : ℕ) : Tendsto (fun P : ℝ => log P ^ n / P) atTop (𝓝 0) := by { simpa only [rpow_natCast, rpow_one] using (isLittleO_log_rpow_rpow_atTop (n : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero }
private lemma rounding_error {P : ℝ} (hP : 1 < P) : 0 ≤ (thresholdK P : ℝ) - (P / log P + P / log P ^ 2) ∧ (thresholdK P : ℝ) - (P / log P + P / log P ^ 2) ≤ 1 := by { have hPpos : 0 < P := zero_lt_one.trans hP; have hlogpos := log_pos hP; have hpos : 0 ≤ P / log P + P / log P ^ 2 := by { positivity }; have hl := Nat.floor_le hpos; have hu := Nat.lt_floor_add_one (P / log P + P / log P ^ 2); simp only [thresholdK, Nat.cast_add, Nat.cast_one]; exact ⟨by linarith, by linarith⟩ }
private lemma rounding_scaled (n : ℕ) : Tendsto (fun P : ℝ => ((thresholdK P : ℝ) - (P / log P + P / log P ^ 2)) / (P / log P ^ n)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (inverse_log_scale n)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hPpos : 0 < P := zero_lt_one.trans hP
    have hlogpos := log_pos hP
    exact div_nonneg (rounding_error hP).1 (by positivity)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP
    have hPpos : 0 < P := zero_lt_one.trans hP
    have hlogpos := log_pos hP
    have hscale : 0 < P / log P ^ n := by positivity
    calc
      _ ≤ 1 / (P / log P ^ n) := div_le_div_of_nonneg_right (rounding_error hP).2 hscale.le
      _ = _ := by rw [one_div_div]
private lemma excess_real_limit : Tendsto (fun P : ℝ => (D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount P - thresholdK P) / (P / log P ^ 3)) atTop (𝓝 2) := by { have hi : Tendsto (fun P : ℝ => 1 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop 1; have h := ((prime_counting_three_terms.mul hi).add_const 2).sub (rounding_scaled 3); norm_num only [mul_zero, zero_add, sub_zero] at h; apply h.congr'; filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; dsimp only [countingThreeTerms]; field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring }
theorem thresholdK_le_primeCount : ∀ᶠ P : ℝ in atTop, thresholdK P ≤ Nat.primeCounting ⌊P⌋₊ := by { filter_upwards [excess_real_limit.eventually_const_lt (by norm_num : (0 : ℝ) < 2), eventually_gt_atTop (1 : ℝ)] with P h hP; have hPpos : 0 < P := zero_lt_one.trans hP; have hlogpos := log_pos hP; have hscale : 0 < P / log P ^ 3 := by { positivity }; have hd := (div_pos_iff_of_pos_right hscale).mp h; change 0 < (Nat.primeCounting ⌊P⌋₊ : ℝ) - thresholdK P at hd; exact_mod_cast (sub_pos.mp hd).le }
theorem excess_limit : Tendsto (fun P : ℝ => (excess P : ℝ) / (P / log P ^ 3)) atTop (𝓝 2) := by { apply excess_real_limit.congr'; filter_upwards [thresholdK_le_primeCount] with P hP; simp only [excess, Nat.cast_sub hP, D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount] }
theorem coreBudget_limit : Tendsto (fun P : ℝ => coreBudget P / (P / log P ^ 2)) atTop (𝓝 2) := by { have hi : Tendsto (fun P : ℝ => log 2 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop (log 2); have h := (budget_limit.sub (rounding_scaled 3)).sub (excess_limit.mul hi); norm_num only [sub_zero, mul_zero] at h; apply h.congr'; filter_upwards [thresholdK_le_primeCount, eventually_gt_atTop (1 : ℝ)] with P hk hP; have hp : P ≠ 0 := by { linarith }; rw [coreBudget, log_div hp (by norm_num : (2 : ℝ) ≠ 0)]; dsimp only [budget, excess, D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel.primeCount]; rw [Nat.cast_sub hk]; field_simp [hp, (log_pos hP).ne'] <;> ring }
def reserve (P : ℝ) : Finset ℕ := primeInterval (P / 2) (3 * P / 4)
private lemma reserve_limit : Tendsto (fun P : ℝ => ((reserve P).card : ℝ) / (P / log P)) atTop (𝓝 (1 / 4 : ℝ)) := by { have hi : Tendsto (fun P : ℝ => 56 / log P) atTop (𝓝 0) := tendsto_log_atTop.const_div_atTop 56; have he : Tendsto (fun P : ℝ => ((reserve P).card : ℝ) / (P / log P) - 1 / 4) atTop (𝓝 0) := by { apply squeeze_zero_norm' _ hi; filter_upwards [central_prime_counting_bound, eventually_gt_atTop (1 : ℝ)] with P h hP; have hp : 0 < P := by { linarith }; have hl := log_pos hP; have h1 := h (P / 2) ⟨le_rfl, by linarith⟩; have h2 := h (3 * P / 4) ⟨by linarith, by linarith⟩; have heq := primeInterval_card (show P / 2 ≤ 3 * P / 4 by linarith); change ((reserve P).card : ℝ) = _ at heq; rw [Real.norm_eq_abs, heq]; have habs : |(primeCount (3 * P / 4) - primeCount (P / 2)) - P / (4 * log P)| ≤ 56 * (P / log P ^ 2) := by { have htri := abs_sub (primeCount (3 * P / 4) - (3 * P / 4) / log P) (primeCount (P / 2) - (P / 2) / log P); have hid : (primeCount (3 * P / 4) - (3 * P / 4) / log P) - (primeCount (P / 2) - (P / 2) / log P) = (primeCount (3 * P / 4) - primeCount (P / 2)) - P / (4 * log P) := by { ring }; rw [hid] at htri; linarith }; have hid : (primeCount (3 * P / 4) - primeCount (P / 2)) / (P / log P) - 1 / 4 = ((primeCount (3 * P / 4) - primeCount (P / 2)) - P / (4 * log P)) / (P / log P) := by { field_simp [hp.ne', hl.ne'] <;> ring }; rw [hid, abs_div, abs_of_pos (div_pos hp hl)]; apply (div_le_iff₀ (div_pos hp hl)).mpr; convert habs using 1 <;> field_simp [hl.ne'] <;> ring }; have h := he.add_const (1 / 4 : ℝ); simpa only [sub_add_cancel, zero_add] using h }
private lemma reserve_enough : ∀ᶠ P : ℝ in atTop, excess P ≤ (reserve P).card := by { have hi : Tendsto (fun P : ℝ => 1 / log P ^ 2) atTop (𝓝 0) := by { simpa only [one_div_pow, zero_pow (by decide : (2 : ℕ) ≠ 0)] using ((tendsto_log_atTop.const_div_atTop 1).pow 2) }; have hr : Tendsto (fun P : ℝ => (excess P : ℝ) / (P / log P)) atTop (𝓝 0) := by { have h := excess_limit.mul hi; norm_num only [mul_zero] at h; apply h.congr'; filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne'] <;> ring }; filter_upwards [hr.eventually_lt reserve_limit (by norm_num : (0 : ℝ) < 1 / 4), eventually_gt_atTop (1 : ℝ)] with P h hP; have hPpos : 0 < P := zero_lt_one.trans hP; have hlogpos := log_pos hP; have hscale : 0 < P / log P := by { positivity }; exact_mod_cast ((div_lt_div_iff_of_pos_right hscale).mp h).le }
private theorem trimmed_core : ∀ᶠ P : ℝ in atTop, ∃ R : Finset ℕ, R ⊆ reserve P ∧ R.card = excess P ∧ (Nat.primesLE ⌊P⌋₊ \ R).card = thresholdK P ∧ (∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ)) ≤ P - coreBudget P := by
  filter_upwards [reserve_enough, thresholdK_le_primeCount, eventually_gt_atTop (1 : ℝ)] with P hR hk hP
  obtain ⟨R, hsub, hcard⟩ := exists_subset_card_eq hR
  have hsub' : R ⊆ Nat.primesLE ⌊P⌋₊ := by
    intro p hp
    obtain ⟨hmem, hprime⟩ := mem_filter.mp (hsub hp)
    apply Nat.mem_primesLE.mpr
    exact ⟨(mem_Ioc.mp hmem).2.trans (Nat.floor_mono (by linarith : 3 * P / 4 ≤ P)), hprime⟩
  refine ⟨R, hsub, hcard, ?_, ?_⟩
  · rw [card_sdiff_of_subset hsub', Nat.primesLE_card_eq_primeCounting, hcard, excess]
    omega
  · have hsum : (∑ p ∈ R, log (p : ℝ)) +
        (∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ)) = Chebyshev.theta P := by
      rw [add_comm, sum_sdiff hsub', Chebyshev.theta_eq_sum_primesLE]
    have hsumlo : (excess P : ℝ) * log (P / 2) ≤ ∑ p ∈ R, log (p : ℝ) := by
      rw [← hcard]
      calc
        _ = ∑ _p ∈ R, log (P / 2) := by simp
        _ ≤ _ := by
          apply sum_le_sum
          intro p hp
          have hpmem := (mem_Ioc.mp (mem_filter.mp (hsub hp)).1).1
          exact log_le_log (by positivity : 0 < P / 2) (Nat.lt_of_floor_lt hpmem).le
    dsimp only [coreBudget]
    linarith
def boxScale (c P : ℝ) : ℝ := P / (log P * (c * sqrt (log P)))
private lemma boxScale_top {c : ℝ} (hc : 0 < c) : Tendsto (boxScale c) atTop atTop := by { have h : Tendsto (fun P : ℝ => P / (log P * sqrt (log P))) atTop atTop := by { have hp : ∀ᶠ P : ℝ in atTop, 0 < (log P * sqrt (log P)) / P := by { filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; have hPpos : 0 < P := zero_lt_one.trans hP; have hlogpos := log_pos hP; positivity }; have h := tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨log_rpow_over_id_zero, hp⟩); simpa only [inv_div, Function.comp_def] using h }; convert h.atTop_div_const hc using 1; ext P; dsimp only [boxScale]; ring }
private lemma exp_saddle_difference {c : ℝ} (hc : 0 < c) (t : ℝ) : Tendsto (fun P : ℝ => (exp (t / (c * sqrt (log P))) - 1) * (c * sqrt (log P))) atTop (𝓝 t) := by { have hs : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc; by_cases ht : t = 0; { subst t; simp }; have hi : Tendsto (fun P : ℝ => t / (c * sqrt (log P))) atTop (𝓝[≠] 0) := by { apply tendsto_nhdsWithin_iff.mpr; refine ⟨hs.const_div_atTop t, ?_⟩; filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; exact div_ne_zero ht (mul_ne_zero hc.ne' (sqrt_pos.mpr (log_pos hP)).ne') }; have h := ((hasDerivAt_exp (0 : ℝ)).tendsto_slope_zero.comp hi).mul_const t; norm_num only [exp_zero, one_mul] at h; apply h.congr'; filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; simp only [Function.comp_def, zero_add, smul_eq_mul]; field_simp [ht, hc.ne', (sqrt_pos.mpr (log_pos hP)).ne'] <;> ring }
private lemma central_endpoint {c : ℝ} (hc : 0 < c) (t : ℝ) : ∀ᶠ P : ℝ in atTop, P * exp (t / (c * sqrt (log P))) ∈ Set.Icc (P / 2) (2 * P) := by { have hs : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc; have he := (hs.const_div_atTop t).rexp; rw [exp_zero] at he; filter_upwards [he.eventually_const_lt (by norm_num : (1 / 2 : ℝ) < 1), he.eventually_lt_const (by norm_num : (1 : ℝ) < 2), eventually_gt_atTop (1 : ℝ)] with P hlo hhi hP; have hp : 0 < P := by { linarith }; constructor <;> nlinarith }
private lemma box_count_limit {c a b : ℝ} (hc : 0 < c) (hab : a ≤ b) : Tendsto (fun P : ℝ => ((primeInterval (P * exp (a / (c * sqrt (log P)))) (P * exp (b / (c * sqrt (log P))))).card : ℝ) / boxScale c P) atTop (𝓝 (b - a)) := by { let A (P : ℝ) := P * exp (a / (c * sqrt (log P))); let B (P : ℝ) := P * exp (b / (c * sqrt (log P))); have hm := (exp_saddle_difference hc b).sub (exp_saddle_difference hc a); have hi : Tendsto (fun P : ℝ => 56 * c / sqrt (log P)) atTop (𝓝 0) := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_div_atTop (56 * c); have he : Tendsto (fun P : ℝ => (((primeInterval (A P) (B P)).card : ℝ) - (B P - A P) / log P) / boxScale c P) atTop (𝓝 0) := by { apply squeeze_zero_norm' _ hi; filter_upwards [central_prime_counting_bound, central_endpoint hc a, central_endpoint hc b, eventually_gt_atTop (1 : ℝ)] with P h ha hb hP; have hp : 0 < P := by { linarith }; have hl := log_pos hP; have hr := sqrt_pos.mpr hl; have hab' : A P ≤ B P := by { dsimp only [A, B]; gcongr }; have hcard := primeInterval_card hab'; have h1 := h (A P) ha; have h2 := h (B P) hb; have herror : |((primeInterval (A P) (B P)).card : ℝ) - (B P - A P) / log P| ≤ 56 * (P / log P ^ 2) := by { rw [hcard]; have ht := abs_sub (primeCount (B P) - B P / log P) (primeCount (A P) - A P / log P); have hid : (primeCount (B P) - B P / log P) - (primeCount (A P) - A P / log P) = (primeCount (B P) - primeCount (A P)) - (B P - A P) / log P := by { ring }; rw [hid] at ht; linarith }; rw [Real.norm_eq_abs, abs_div, abs_of_pos (show 0 < boxScale c P by dsimp [boxScale]; positivity)]; apply (div_le_iff₀ (show 0 < boxScale c P by dsimp [boxScale]; positivity)).mpr; convert herror using 1; dsimp only [boxScale]; have hh := sq_sqrt hl.le; field_simp [hp.ne', hl.ne', hr.ne']; nlinarith }; have h := he.add hm; simp only [zero_add] at h; apply h.congr'; filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; dsimp only [A, B, boxScale]; field_simp [(show P ≠ 0 by linarith), (log_pos hP).ne', hc.ne', (sqrt_pos.mpr (log_pos hP)).ne'] <;> ring }
def negativeBox (G : Exchange.Mesh) (c P : ℝ) (i : Fin G.n) : Finset ℕ := primeInterval (P * exp (-G.node (i + 1) / (c * sqrt (log P)))) (P * exp (-G.node i / (c * sqrt (log P))))
def positiveBox (G : Exchange.Mesh) (c P : ℝ) (i : Fin G.n) : Finset ℕ := primeInterval (P * exp (G.node i / (c * sqrt (log P)))) (P * exp (G.node (i + 1) / (c * sqrt (log P))))
def capacity (G : Exchange.Mesh) (c P : ℝ) (i : Fin G.n) : ℕ := min (negativeBox G c P i).card (positiveBox G c P i).card
def occupancy (G : Exchange.Mesh) (c P : ℝ) (i : Fin G.n) : ℕ := ⌊Exchange.logistic (G.node (i + 1)) * (capacity G c P i : ℝ)⌋₊
def exchangeCost (G : Exchange.Mesh) (c P : ℝ) : ℝ := (2 / (c * sqrt (log P))) * ∑ i : Fin G.n, G.node (i.val + 1) * (occupancy G c P i : ℝ)
def entropyEstimate (G : Exchange.Mesh) (c P : ℝ) : ℝ := 2 * ∑ i, Entropy.entropyLower (capacity G c P i) (occupancy G c P i)
private lemma mesh_node_mono (G : Exchange.Mesh) : Monotone G.node := by { intro i j hij; dsimp [Exchange.Mesh.node]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast hij) (Exchange.step_pos G).le }
private lemma capacity_limit (G : Exchange.Mesh) {c : ℝ} (hc : 0 < c) (i : Fin G.n) : Tendsto (fun P : ℝ => (capacity G c P i : ℝ) / boxScale c P) atTop (𝓝 G.step) := by { have hn := box_count_limit hc (neg_le_neg (mesh_node_mono G (Nat.le_succ (i : ℕ)))); have hp := box_count_limit hc (mesh_node_mono G (Nat.le_succ (i : ℕ))); have hn' : Tendsto (fun P : ℝ => ((negativeBox G c P i).card : ℝ) / boxScale c P) atTop (𝓝 G.step) := by { convert hn using 1; dsimp only [negativeBox]; all_goals simp only [neg_sub_neg, Exchange.node_step] }; have hp' : Tendsto (fun P : ℝ => ((positiveBox G c P i).card : ℝ) / boxScale c P) atTop (𝓝 G.step) := by { simpa only [positiveBox, Exchange.node_step] using hp }; exact Entropy.min_scaled _ _ _ (boxScale_top hc) hn' hp' }
private lemma occupancy_fits (G : Exchange.Mesh) (c P : ℝ) (i : Fin G.n) : occupancy G c P i ≤ capacity G c P i := by { have hq0 : 0 ≤ Exchange.logistic (G.node (i + 1)) := by { dsimp [Exchange.logistic]; positivity }; have hq1 : Exchange.logistic (G.node (i + 1)) ≤ 1 := by { dsimp [Exchange.logistic]; exact (inv_lt_one_of_one_lt₀ (by linarith [exp_pos (G.node (i+1))])).le }; have h := Nat.floor_le (mul_nonneg hq0 (Nat.cast_nonneg (capacity G c P i))); have h' : (occupancy G c P i : ℝ) ≤ capacity G c P i := by { exact h.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) (capacity G c P i)]) }; exact_mod_cast h' }
private lemma occupancy_limit (G : Exchange.Mesh) {c : ℝ} (hc : 0 < c) (i : Fin G.n) : Tendsto (fun P : ℝ => (occupancy G c P i : ℝ) / boxScale c P) atTop (𝓝 (G.step * Exchange.logistic (G.node (i + 1)))) := by { simpa only [occupancy, mul_comm] using Entropy.floor_scaled (boxScale c) (fun P => capacity G c P i) (boxScale_top hc) (Exchange.step_pos G) (show 0 ≤ Exchange.logistic (G.node (i+1)) by dsimp [Exchange.logistic]; positivity) (capacity_limit G hc i) }
private lemma entropyEstimate_limit (G : Exchange.Mesh) {c : ℝ} (hc : 0 < c) : Tendsto (fun P : ℝ => entropyEstimate G c P / boxScale c P) atTop (𝓝 G.mass) := by { have h := (tendsto_finset_sum univ (fun i (_ : i ∈ (univ : Finset (Fin G.n))) => Entropy.entropy_lower_scaled (boxScale c) (fun P => capacity G c P i) (fun P => occupancy G c P i) (boxScale_top hc) (Exchange.step_pos G) (capacity_limit G hc i) (occupancy_limit G hc i))).const_mul 2; convert h using 1; { ext P; dsimp only [entropyEstimate]; rw [mul_div_assoc, sum_div] }; { dsimp only [Exchange.Mesh.mass]; rw [← Fin.sum_univ_eq_sum_range]; rfl } }
private lemma exchangeCost_limit (G : Exchange.Mesh) {c : ℝ} (hc : 0 < c) : Tendsto (fun P : ℝ => exchangeCost G c P / coreBudget P) atTop (𝓝 (G.cost / (2 * c ^ 2))) := by
  have hsum := tendsto_finset_sum univ (fun i (_ : i ∈ (univ : Finset (Fin G.n))) => (occupancy_limit G hc i).const_mul (G.node (i + 1)))
  have h := ((hsum.const_mul (2 / c ^ 2)).div coreBudget_limit (by norm_num : (2 : ℝ) ≠ 0))
  convert h.congr' (show (fun P : ℝ =>
      (2 / c ^ 2 * ∑ i : Fin G.n, G.node (i+1) *
        ((occupancy G c P i : ℝ) / boxScale c P)) / (coreBudget P / (P / log P ^ 2)))
      =ᶠ[atTop] (fun P => exchangeCost G c P / coreBudget P) from ?_) using 1
  · dsimp only [Exchange.Mesh.cost]
    rw [← Fin.sum_univ_eq_sum_range]
    apply congrArg (fun r : ℝ => 𝓝 r)
    have hs : (∑ i : Fin G.n, G.node (i+1) * (G.step * Exchange.logistic (G.node (i+1)))) = ∑ i : Fin G.n, G.step * G.node (i+1) * Exchange.logistic (G.node (i+1)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hs]
    ring
  · filter_upwards [eventually_gt_atTop (1 : ℝ),
      coreBudget_limit.eventually_const_lt (by norm_num : (0 : ℝ) < 2)] with P hP hD
    have hPpos : 0 < P := zero_lt_one.trans hP
    have hl := log_pos hP
    have hr := sqrt_pos.mpr hl
    have hDpos : 0 < coreBudget P := (div_pos_iff_of_pos_right (show 0 < P / log P ^ 2 by positivity)).mp hD
    have hr2 := sq_sqrt hl.le
    have hcoef : (2 / c ^ 2) * (P / log P ^ 2) / boxScale c P = 2 / (c * sqrt (log P)) := by
      dsimp only [boxScale]
      field_simp [hPpos.ne', hl.ne', hc.ne', hr.ne']
      ring_nf <;> rw [hr2] <;> ring
    dsimp only [exchangeCost]
    simp_rw [← mul_div_assoc]
    rw [← sum_div]
    calc
      _ = ((2 / c ^ 2) * (P / log P ^ 2) / boxScale c P) * (∑ i : Fin G.n, G.node (i+1) * (occupancy G c P i : ℝ)) / coreBudget P := by
        field_simp [hPpos.ne', hl.ne', hc.ne', hr.ne', hDpos.ne', (show boxScale c P ≠ 0 by dsimp [boxScale]; positivity)] <;> ring
      _ = _ := by rw [hcoef]
private lemma entropyEstimate_le_log_choices (G : Exchange.Mesh) (c P : ℝ) : entropyEstimate G c P ≤ log (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) := by { have hp (i : Fin G.n) : (0 : ℝ) < (capacity G c P i).choose (occupancy G c P i) := by { exact_mod_cast Nat.choose_pos (occupancy_fits G c P i) }; rw [Nat.cast_prod]; simp_rw [Nat.cast_pow]; rw [log_prod (fun i _ => (pow_pos (hp i) 2).ne')]; simp_rw [log_pow]; dsimp only [entropyEstimate, Entropy.entropyLower]; rw [mul_sum]; apply sum_le_sum; intro i _; exact mul_le_mul_of_nonneg_left (Entropy.log_choose_ge_binEntropy _ _ (occupancy_fits G c P i)) (by norm_num) }
theorem fixed_grid_exists (ε : ℝ) (hε : 0 < ε) : ∃ c : ℝ, 0 < c ∧ ∃ G : Exchange.Mesh, ∀ᶠ P : ℝ in atTop, exchangeCost G c P ≤ coreBudget P ∧ (2 * π / sqrt 3 - ε) * (P / (log P * sqrt (log P))) ≤ log (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) := by { let K : ℝ := 2 * π / sqrt 3; let c₀ : ℝ := π / (2 * sqrt 3); let η : ℝ := ε / (8 * K); let ρ : ℝ := ε * c₀ / 8; have hK : 0 < K := by { dsimp [K]; positivity }; have hc₀ : 0 < c₀ := by { dsimp [c₀]; positivity }; have hη : 0 < η := by { dsimp [η]; positivity }; have hρ : 0 < ρ := by { dsimp [ρ]; positivity }; obtain ⟨G, hcost, hmass⟩ := Exchange.exists_good_grid hη hρ; let c : ℝ := (1 + η) * c₀; have hc : 0 < c := by { dsimp [c]; positivity }; have hA : 2 * c ^ 2 = (π ^ 2 / 6) * (1 + η) ^ 2 := by { dsimp [c, c₀]; have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3); field_simp; nlinarith }; have hstrict : G.cost / (2 * c ^ 2) < 1 := by { apply (div_lt_one (by positivity : 0 < 2 * c ^ 2)).mpr; rw [hA]; have hpi : 0 < π ^ 2 / 6 := by { positivity }; have hgap : 1 + η / 2 < (1 + η) ^ 2 := by { nlinarith }; exact hcost.trans_lt (mul_lt_mul_of_pos_left hgap hpi) }; have hBc : π ^ 2 / 3 = K * c₀ := by { dsimp [K, c₀]; have hs := sq_sqrt (by norm_num : (0 : ℝ) ≤ 3); field_simp; nlinarith }; have hηK : K * η = ε / 8 := by { dsimp [η]; field_simp <;> ring }; have hcoef : K - ε / 2 < G.mass / c := by { apply (lt_div_iff₀ hc).mpr; have haux : (K - ε / 2) * (1 + η) < K - ε / 8 := by { nlinarith [mul_pos hε hη] }; have haux' := mul_lt_mul_of_pos_right haux hc₀; dsimp only [c]; rw [hBc] at hmass; dsimp only [ρ] at hmass; nlinarith }; have he : Tendsto (fun P : ℝ => entropyEstimate G c P / (P / (log P * sqrt (log P)))) atTop (𝓝 (G.mass / c)) := by { apply ((entropyEstimate_limit G hc).div_const c).congr'; filter_upwards [eventually_gt_atTop (1 : ℝ)] with P hP; dsimp only [boxScale]; field_simp [hc.ne', (log_pos hP).ne', (sqrt_pos.mpr (log_pos hP)).ne', (show P ≠ 0 by linarith)] <;> ring }; refine ⟨c, hc, G, ?_⟩; filter_upwards [(exchangeCost_limit G hc).eventually_lt_const hstrict, coreBudget_limit.eventually_const_lt (by norm_num : (0 : ℝ) < 2), he.eventually_const_lt (show K - ε < G.mass / c by linarith), eventually_gt_atTop (1 : ℝ)] with P hV hD hE hP; have hp : 0 < P := zero_lt_one.trans hP; have hl := log_pos hP; have hscale : 0 < P / (log P * sqrt (log P)) := by { positivity }; have hDpos : 0 < coreBudget P := (div_pos_iff_of_pos_right (show 0 < P / log P ^ 2 by positivity)).mp hD; constructor; { exact ((div_lt_one hDpos).mp hV).le }; { change (K - ε) * (P / (log P * sqrt (log P))) ≤ _; exact ((lt_div_iff₀ hscale).mp hE).le.trans (entropyEstimate_le_log_choices G c P) } }
private lemma choices_le_tail (G : Exchange.Mesh) {c : ℝ} (hc : 0 < c) : ∀ᶠ P : ℝ in atTop, exchangeCost G c P ≤ coreBudget P → (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) ≤ tailCount 1 (exp P) := by { have hs : Tendsto (fun P : ℝ => c * sqrt (log P)) atTop atTop := (tendsto_sqrt_atTop.comp tendsto_log_atTop).const_mul_atTop hc; have hf := (hs.const_div_atTop (-G.node G.n)).rexp; rw [exp_zero] at hf; filter_upwards [trimmed_core, hf.eventually_const_lt (by norm_num : (3 / 4 : ℝ) < 1), eventually_gt_atTop (1 : ℝ)] with P hcore hfar hP; intro hV; obtain ⟨R, hR, hcard, hsize, hbase⟩ := hcore; have hp : 0 < P := zero_lt_one.trans hP; have hl := log_pos hP; have hspos : 0 < c * sqrt (log P) := by { positivity }; have hfar' : 3 * P / 4 ≤ P * exp (-G.node G.n / (c * sqrt (log P))) := by { nlinarith }; have hthreshold : threshold 1 (exp P) < ((Nat.primesLE ⌊P⌋₊ \ R).card : ℝ) := by { rw [hsize]; have h := Nat.lt_floor_add_one (P / log P + P / log P ^ 2); simpa only [threshold, scale, log_exp, thresholdK, Nat.cast_add, Nat.cast_one, one_mul, div_div, pow_two] using h }; have hcount := Exchange.logarithmic_exchange_bound G.n P (c * sqrt (log P)) G.node R hp hspos (mesh_node_mono G) (by simp [Exchange.Mesh.node]) hfar' hR (occupancy G c P) (coreBudget P) 1 (exp P) hbase hV hthreshold (by rw [log_exp]) (exp_pos P); apply le_trans _ hcount; apply prod_le_prod'; intro i _; have hn := Nat.choose_le_choose (occupancy G c P i) (min_le_left (negativeBox G c P i).card (positiveBox G c P i).card); have hp' := Nat.choose_le_choose (occupancy G c P i) (min_le_right (negativeBox G c P i).card (positiveBox G c P i).card); simpa only [pow_two, capacity, negativeBox, positiveBox] using Nat.mul_le_mul hn hp' }
theorem lower : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in atTop, (2 * π / sqrt 3 - ε) * log x / (log (log x)) ^ (3 / 2 : ℝ) ≤ log (tailCount 1 x : ℝ) := by
  intro ε hε
  obtain ⟨c, hc, G, hgrid⟩ := fixed_grid_exists ε hε
  have hP : ∀ᶠ P : ℝ in atTop, (2 * π / sqrt 3 - ε) * (P / (log P * sqrt (log P))) ≤ log (tailCount 1 (exp P) : ℝ) := by
    filter_upwards [hgrid, choices_le_tail G hc] with P hgrid hcount
    have hchoose : 0 < (∏ i : Fin G.n, ((capacity G c P i).choose (occupancy G c P i)) ^ 2 : ℕ) := by
      exact prod_pos (fun i _ => pow_pos (Nat.choose_pos (occupancy_fits G c P i)) _)
    exact hgrid.2.trans (log_le_log (by exact_mod_cast hchoose)
      (by exact_mod_cast hcount hgrid.1))
  filter_upwards [tendsto_log_atTop.eventually hP, eventually_gt_atTop (exp 1)] with x hx hx1
  have hx0 : 0 < x := (exp_pos 1).trans hx1
  have hell : 0 < log (log x) := log_pos ((lt_log_iff_exp_lt hx0).mpr hx1)
  rw [exp_log hx0] at hx
  rw [show (log (log x)) ^ (3 / 2 : ℝ) = log (log x) * sqrt (log (log x)) by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add hell,
      rpow_one, ← sqrt_eq_rpow]]
  simpa only [mul_div_assoc] using hx
theorem result : Tendsto (fun x : ℝ => log (tailCount 1 x : ℝ) / (log x / (log (log x)) ^ (3 / 2 : ℝ))) atTop (𝓝 (2 * π / sqrt 3)) := by { rw [Metric.tendsto_nhds]; intro ε hε; have hK : 0 < 2 * π / sqrt 3 := by { positivity }; filter_upwards [lower (ε / 2) (by positivity), lower (π / sqrt 3) (by positivity), upper (ε / 2) (by positivity), eventually_gt_atTop (exp 1)] with x hlo hpositive hup hx; have hx0 : 0 < x := (exp_pos 1).trans hx; have hL : 1 < log x := (lt_log_iff_exp_lt hx0).mpr hx; have hell : 0 < log (log x) := log_pos hL; have hy : 0 < log x / (log (log x)) ^ (3 / 2 : ℝ) := div_pos (zero_lt_one.trans hL) (rpow_pos_of_pos hell _); have hn : 0 < (tailCount 1 x : ℝ) := by { by_contra h; have hz : (tailCount 1 x : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _); rw [hz, log_zero] at hpositive; have hp := mul_pos (show 0 < 2 * π / sqrt 3 - π / sqrt 3 by rw [two_mul, add_div, add_sub_cancel_right]; exact div_pos pi_pos (sqrt_pos.mpr (by norm_num))) hy; rw [mul_div_assoc] at hpositive; linarith }; have hlog := log_le_log hn hup; rw [log_exp, mul_div_assoc] at hlog; rw [mul_div_assoc] at hlo; have hhi := (div_le_iff₀ hy).mpr hlog; have hlo' := (le_div_iff₀ hy).mpr hlo; rw [Real.dist_eq, abs_lt]; constructor <;> linarith }
end D5.S3.Arith.Robin.Analytic.OmegaSecond.Entropy
