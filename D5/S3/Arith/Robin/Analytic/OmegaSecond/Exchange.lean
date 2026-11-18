/- GID: D5/S3/Arith/Robin/Analytic/OmegaSecond/Exchange
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/Analytic/OmegaSecond/Exchange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Budget-feasible equal-cardinality prime exchanges and their injective count. -/

import D5.S3.Arith.Robin.Analytic.OmegaTail.Lower
import D5.S3.Arith.Robin.PriceRecord.QuantitativePrimeAbel
import Mathlib.Data.Fintype.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Real Filter Finset
open scoped Topology BigOperators

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
def logarithmicExchangeSystem (n : ℕ) (P s : ℝ) (node : ℕ → ℝ) (R : Finset ℕ)
    (hP : 0 < P) (hs : 0 < s) (hmono : Monotone node) (hzero : node 0 = 0)
    (hfar : 3 * P / 4 ≤ P * exp (-node n / s))
    (hR : R ⊆ primeInterval (P / 2) (3 * P / 4)) : ExchangeSystem (Fin n) := by
  have hneg (i j : ℕ) (hij : i ≤ j) :
      P * exp (-node j / s) ≤ P * exp (-node i / s) := by
    apply mul_le_mul_of_nonneg_left _ hP.le
    exact exp_le_exp.mpr (div_le_div_of_nonneg_right (neg_le_neg (hmono hij)) hs.le)
  have hpos (i j : ℕ) (hij : i ≤ j) :
      P * exp (node i / s) ≤ P * exp (node j / s) := by
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
abbrev Choices (E : ExchangeSystem ι) (h : ι → ℕ) :=
  ((i : ι) → ↥((E.neg i).powersetCard (h i))) ×
    ((i : ι) → ↥((E.pos i).powersetCard (h i)))

def removed (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Finset ℕ :=
  univ.biUnion (fun i => (z.1 i).val)

def inserted (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Finset ℕ :=
  univ.biUnion (fun i => (z.2 i).val)

def support (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : Finset ℕ :=
  (E.base \ removed E h z) ∪ inserted E h z

def value (E : ExchangeSystem ι) (h : ι → ℕ) (z : Choices E h) : ℕ :=
  ∏ p ∈ support E h z, p

private lemma neg_selection (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) (i : ι) :
    (z.1 i).val ⊆ E.neg i ∧ (z.1 i).val.card = h i :=
  mem_powersetCard.mp (z.1 i).property

private lemma pos_selection (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) (i : ι) :
    (z.2 i).val ⊆ E.pos i ∧ (z.2 i).val.card = h i :=
  mem_powersetCard.mp (z.2 i).property

private lemma removed_subset (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) : removed E h z ⊆ E.base := by
  intro p hp
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
  exact E.neg_subset i ((neg_selection E h z i).1 hi)

private lemma inserted_disjoint (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) : Disjoint (inserted E h z) E.base := by
  apply disjoint_left.mpr
  intro p hp hb
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
  exact disjoint_left.mp (E.pos_base i) ((pos_selection E h z i).1 hi) hb

private lemma support_prime (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) : ∀ p ∈ support E h z, Nat.Prime p := by
  intro p hp
  rcases mem_union.mp hp with hp | hp
  · exact E.base_prime p (mem_sdiff.mp hp).1
  · obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
    exact E.pos_prime i p ((pos_selection E h z i).1 hi)

private lemma neg_pairwise (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) : Set.PairwiseDisjoint (univ : Finset ι) (fun i => (z.1 i).val) := by
  intro i _ j _ hij
  exact (E.neg_disjoint hij).mono (neg_selection E h z i).1 (neg_selection E h z j).1

private lemma pos_pairwise (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) : Set.PairwiseDisjoint (univ : Finset ι) (fun i => (z.2 i).val) := by
  intro i _ j _ hij
  exact (E.pos_disjoint hij).mono (pos_selection E h z i).1 (pos_selection E h z j).1

private lemma removed_card (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) : (removed E h z).card = ∑ i, h i := by
  rw [removed, card_biUnion (neg_pairwise E h z)]
  exact sum_congr rfl (fun i _ => (neg_selection E h z i).2)

private lemma inserted_card (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) : (inserted E h z).card = ∑ i, h i := by
  rw [inserted, card_biUnion (pos_pairwise E h z)]
  exact sum_congr rfl (fun i _ => (pos_selection E h z i).2)

private lemma support_card (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) : (support E h z).card = E.base.card := by
  have hd : Disjoint (E.base \ removed E h z) (inserted E h z) :=
    (inserted_disjoint E h z).symm.mono_left sdiff_subset
  have hc := card_le_card (removed_subset E h z)
  rw [support, card_union_of_disjoint hd, card_sdiff_of_subset (removed_subset E h z),
    removed_card, inserted_card]
  rw [removed_card] at hc
  omega

/-- Unique factorization and bin separation recover every individual choice. -/
theorem exchange_value_injective (E : ExchangeSystem ι) (h : ι → ℕ) :
    Function.Injective (value E h) := by
  intro z w he
  have hs : support E h z = support E h w :=
    prime_product_injective (support_prime E h z) (support_prime E h w) he
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
      (z.1 i).val = removed E h z ∩ E.neg i :=
        (bin_union_inter E.neg (fun j => (z.1 j).val) E.neg_disjoint
          (fun j => (neg_selection E h z j).1) i).symm
      _ = removed E h w ∩ E.neg i := by rw [hr]
      _ = (w.1 i).val := bin_union_inter E.neg (fun j => (w.1 j).val)
        E.neg_disjoint (fun j => (neg_selection E h w j).1) i
  · funext i
    apply Subtype.ext
    calc
      (z.2 i).val = inserted E h z ∩ E.pos i :=
        (bin_union_inter E.pos (fun j => (z.2 j).val) E.pos_disjoint
          (fun j => (pos_selection E h z j).1) i).symm
      _ = inserted E h w ∩ E.pos i := by rw [ha]
      _ = (w.2 i).val := bin_union_inter E.pos (fun j => (w.2 j).val)
        E.pos_disjoint (fun j => (pos_selection E h w j).1) i

/-- Equal removal and insertion preserve the number of distinct prime factors. -/
theorem omega_exchange_value (E : ExchangeSystem ι) (h : ι → ℕ)
    (z : Choices E h) :
    ArithmeticFunction.cardDistinctFactors (value E h z) = E.base.card := by
  rw [value, omega_prime_product (support_prime E h z), support_card]

/-- Independent finite choices have the product of binomial cardinalities. -/
theorem card_exchange_choices (E : ExchangeSystem ι) (h : ι → ℕ) :
    Fintype.card (Choices E h) =
      ∏ i, (E.neg i).card.choose (h i) * (E.pos i).card.choose (h i) := by
  simp only [Choices, Fintype.card_prod, Fintype.card_pi, Fintype.card_coe,
    card_powersetCard, prod_mul_distrib]

/-- Every choice satisfies the same worst-endpoint cost; no averaging is used. -/
theorem log_exchange_value_le (E : ExchangeSystem ι) (h : ι → ℕ)
    (P D s : ℝ) (t : ι → ℝ)
    (hbase : ∑ p ∈ E.base, log (p : ℝ) ≤ P - D)
    (hneg : ∀ i p, p ∈ E.neg i → log P - t i / s ≤ log (p : ℝ))
    (hpos : ∀ i p, p ∈ E.pos i → log (p : ℝ) ≤ log P + t i / s)
    (z : Choices E h) :
    log (value E h z : ℝ) ≤ P - D + (2 / s) * ∑ i, t i * (h i : ℝ) := by
  have hne : ∀ p ∈ support E h z, (p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (support_prime E h z p hp).ne_zero
  have hd : Disjoint (E.base \ removed E h z) (inserted E h z) :=
    (inserted_disjoint E h z).symm.mono_left sdiff_subset
  have hn : ∑ p ∈ removed E h z, log (p : ℝ) ≥
      ∑ i, (h i : ℝ) * (log P - t i / s) := by
    rw [removed, sum_biUnion (neg_pairwise E h z)]
    apply sum_le_sum
    intro i _
    calc
      (h i : ℝ) * (log P - t i / s) =
          ∑ _p ∈ (z.1 i).val, (log P - t i / s) := by
        simp [(neg_selection E h z i).2]
        ring
      _ ≤ ∑ p ∈ (z.1 i).val, log (p : ℝ) :=
        sum_le_sum (fun p hp => hneg i p ((neg_selection E h z i).1 hp))
  have hp : ∑ p ∈ inserted E h z, log (p : ℝ) ≤
      ∑ i, (h i : ℝ) * (log P + t i / s) := by
    rw [inserted, sum_biUnion (pos_pairwise E h z)]
    apply sum_le_sum
    intro i _
    calc
      ∑ p ∈ (z.2 i).val, log (p : ℝ) ≤
          ∑ _p ∈ (z.2 i).val, (log P + t i / s) :=
        sum_le_sum (fun p hp => hpos i p ((pos_selection E h z i).1 hp))
      _ = _ := by simp [(pos_selection E h z i).2]; ring
  have hid :
      (∑ i, (h i : ℝ) * (log P + t i / s)) -
          (∑ i, (h i : ℝ) * (log P - t i / s)) =
        (2 / s) * ∑ i, t i * (h i : ℝ) := by
    rw [← sum_sub_distrib, mul_sum]
    apply sum_congr rfl
    intro i _
    ring
  rw [value, Nat.cast_prod, log_prod hne, support, sum_union hd,
    sum_sdiff_eq_sub (removed_subset E h z)]
  linarith

/-- A feasible prime-exchange family gives a lower bound for the literal tail. -/
theorem balanced_exchange_bound (E : ExchangeSystem ι) (h : ι → ℕ)
    (P D s : ℝ) (t : ι → ℝ) (lambda x : ℝ)
    (hbase : ∑ p ∈ E.base, log (p : ℝ) ≤ P - D)
    (hneg : ∀ i p, p ∈ E.neg i → log P - t i / s ≤ log (p : ℝ))
    (hpos : ∀ i p, p ∈ E.pos i → log (p : ℝ) ≤ log P + t i / s)
    (hbudget : (2 / s) * ∑ i, t i * (h i : ℝ) ≤ D)
    (hthreshold : threshold lambda x < (E.base.card : ℝ))
    (hP : P ≤ log x) (hx : 0 < x) :
    (∏ i, (E.neg i).card.choose (h i) * (E.pos i).card.choose (h i)) ≤
      tailCount lambda x := by
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
theorem logarithmic_exchange_bound (n : ℕ) (P s : ℝ) (node : ℕ → ℝ) (R : Finset ℕ)
    (hP : 0 < P) (hs : 0 < s) (hmono : Monotone node) (hzero : node 0 = 0)
    (hfar : 3 * P / 4 ≤ P * exp (-node n / s))
    (hR : R ⊆ primeInterval (P / 2) (3 * P / 4))
    (h : Fin n → ℕ) (D lambda x : ℝ)
    (hbase : ∑ p ∈ Nat.primesLE ⌊P⌋₊ \ R, log (p : ℝ) ≤ P - D)
    (hbudget : (2 / s) * ∑ i : Fin n, node (i.val + 1) * (h i : ℝ) ≤ D)
    (hthreshold : threshold lambda x < ((Nat.primesLE ⌊P⌋₊ \ R).card : ℝ))
    (hPx : P ≤ log x) (hx : 0 < x) :
    (∏ i : Fin n,
      (primeInterval (P * exp (-node (i.val + 1) / s))
        (P * exp (-node i.val / s))).card.choose (h i) *
      (primeInterval (P * exp (node i.val / s))
        (P * exp (node (i.val + 1) / s))).card.choose (h i)) ≤ tailCount lambda x := by
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
