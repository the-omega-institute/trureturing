/- GID: D5/S3/FiniteGroups/RationalSubgroupConjugacyAttainment
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/RationalSubgroupConjugacyAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every rational strictly between zero and one is attained by an actual finite group. -/

import D5.S3.FiniteGroups.CyclicPrimePowerAction
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.Tactic

namespace D5.S3.FiniteGroups.RationalSubgroupConjugacyAttainment

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.FiniteGroups.SubgroupConjugacyRatio
open D5.S3.FiniteGroups.CyclicPrimePowerAction

private def productGroup (W V : FiniteGroup) : FiniteGroup :=
  ⟨W.Carrier × V.Carrier, inferInstance, inferInstance⟩

private theorem split_order {p q s : ℕ} (A : ActionData p q s)
    [NeZero p] [NeZero (q ^ s)] : Nat.card (SplitGroup A) = p * q ^ s := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod]
  simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

private theorem prime_coprime_above (W : FiniteGroup) {p : ℕ}
    (hp : p.Prime) (hgt : Nat.card W.Carrier < p) : (Nat.card W.Carrier).Coprime p :=
  (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt Nat.card_pos hgt)).symm

private theorem unit_counts : latticeCount Unit = 1 ∧ classCount Unit = 1 := by
  have : Subsingleton (Subgroup Unit) := by
    refine ⟨fun H J => ?_⟩
    ext x
    have hx : x = 1 := Subsingleton.elim _ _
    rw [hx]
    exact iff_of_true H.one_mem J.one_mem
  constructor <;> exact Nat.card_unique

private theorem fresh_two_primes (bound : ℕ) :
    ∃ q p : ℕ, q.Prime ∧ bound < q ∧ p.Prime ∧ q < p ∧ q ∣ p - 1 := by
  obtain ⟨q, hboundq, hq⟩ := Nat.exists_infinite_primes (bound + 1)
  obtain ⟨p, hp, hqp, hmod⟩ := Nat.exists_prime_gt_modEq_one q hq.ne_zero
  have hdiv : q ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_le).mp hmod.symm
  exact ⟨q, p, hq, by omega, hp, hqp, hdiv⟩

private theorem consecutive_ratio {t p : ℕ} (ht : 0 < t) (hp : p.Prime)
    (hp_gt_two : 2 < p) (hq : p % 2 = 1) :
    let n := t * ((p - 1) / 2)
    ((2 * n : ℚ) / (2 * n + p - 1)) = ((t : ℚ) / (t + 1)) := by
  dsimp
  have htwo : 2 ∣ p - 1 := by
    rw [Nat.dvd_iff_mod_eq_zero]
    omega
  have hhalf : 2 * ((p - 1) / 2) = p - 1 := Nat.mul_div_cancel' htwo
  have hmul : 2 * (t * ((p - 1) / 2)) = t * (p - 1) := by
    calc
      2 * (t * ((p - 1) / 2)) = t * (2 * ((p - 1) / 2)) := by ring
      _ = t * (p - 1) := by rw [hhalf]
  have hmulQ : (2 : ℚ) * (t * ((p - 1) / 2) : ℕ) = (t * (p - 1) : ℕ) := by
    exact_mod_cast hmul
  rw [hmulQ]
  have hden1 : (0 : ℚ) < (t : ℚ) + 1 := by positivity
  have hden2 : (0 : ℚ) < (t * (p - 1) : ℕ) + p - 1 := by
    norm_num [Nat.cast_mul, Nat.cast_sub hp.one_le]
    have hpq : (2 : ℚ) < p := by exact_mod_cast hp_gt_two
    nlinarith
  field_simp [ne_of_gt hden1, ne_of_gt hden2]
  norm_num [Nat.cast_mul, Nat.cast_sub hp.one_le]
  ring

private theorem consecutive_factor (W : FiniteGroup) (t : ℕ) (ht : 0 < t) :
    ∃ V : FiniteGroup, (Nat.card W.Carrier).Coprime (Nat.card V.Carrier) ∧
      0 < latticeCount V.Carrier ∧ ratio V.Carrier = (t : ℚ) / (t + 1) := by
  obtain ⟨q, p, hq, hbound, hp, hqp, hdiv⟩ :=
    fresh_two_primes (max 4 (Nat.card W.Carrier))
  have hp4 : 4 < p := lt_trans (lt_of_le_of_lt (le_max_left _ _) hbound) hqp
  have hn2 : 2 ≤ t * ((p - 1) / 2) := by
    have hh : 2 ≤ (p - 1) / 2 := by omega
    nlinarith
  let n := t * ((p - 1) / 2)
  let s := n - 1
  have hs : 0 < s := by dsimp [s, n]; omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have : NeZero (q ^ s) := ⟨pow_ne_zero s hq.ne_zero⟩
  let A := actionData p q s hp hq hdiv hs
  let V : FiniteGroup := ⟨SplitGroup A, inferInstance, inferInstance⟩
  have hcop : p.Coprime q := (Nat.coprime_primes hp hq).mpr (Nat.ne_of_gt hqp)
  have hcounts := split_counts A hs hcop
  refine ⟨V, ?_, ?_, ?_⟩
  · change (Nat.card W.Carrier).Coprime (Nat.card (SplitGroup A))
    rw [split_order A]
    exact (prime_coprime_above W hp (lt_trans
      (lt_of_le_of_lt (le_max_right _ _) hbound) hqp)).mul_right
      ((prime_coprime_above W hq (lt_of_le_of_lt (le_max_right _ _) hbound)).pow_right s)
  · change 0 < latticeCount (SplitGroup A)
    rw [hcounts.1]
    omega
  · change ratio (SplitGroup A) = _
    rw [ratio, hcounts.1, hcounts.2]
    have hsn : s + 1 = n := by dsimp [s, n]; omega
    have hmod : p % 2 = 1 := (hp.mod_two_eq_one_iff_ne_two).mpr (by omega)
    have hr := consecutive_ratio ht hp (by omega) hmod
    dsimp only at hr
    have hsQ : (s : ℚ) + 1 = (n : ℚ) := by exact_mod_cast hsn
    rw [show ((2 * s + 2 : ℕ) : ℚ) = 2 * (n : ℚ) from by
      push_cast
      linarith,
      show ((2 * s + p + 1 : ℕ) : ℚ) = 2 * (n : ℚ) + p - 1 from by
        push_cast
        linarith]
    exact hr

private theorem attain_natural (a : ℕ) (ha : 0 < a) (m : ℕ) :
    ∃ W : FiniteGroup, 0 < latticeCount W.Carrier ∧
      ratio W.Carrier = (a : ℚ) / (a + m) := by
  induction m with
  | zero =>
    let W : FiniteGroup := ⟨Unit, inferInstance, inferInstance⟩
    refine ⟨W, ?_, ?_⟩
    · exact unit_counts.1 ▸ Nat.zero_lt_one
    · change ratio Unit = _
      rw [ratio, unit_counts.1, unit_counts.2]
      simp [Nat.ne_of_gt ha]
  | succ m ih =>
    obtain ⟨W, hL, hr⟩ := ih
    obtain ⟨V, hcop, hLV, hrV⟩ := consecutive_factor W (a + m) (by omega)
    refine ⟨productGroup W V, ?_, ?_⟩
    · change 0 < latticeCount (W.Carrier × V.Carrier)
      rw [(coprime_product_counts hcop).1]
      exact Nat.mul_pos hL hLV
    · change ratio (W.Carrier × V.Carrier) = _
      rw [(coprime_product_counts hcop).2.2, hr, hrV]
      push_cast
      have ht : (a : ℚ) + m ≠ 0 := by positivity
      rw [div_mul_div_cancel₀ ht]
      congr 1
      ring

/-- Every prescribed rational in (0,1) is attained by the whole subgroup lattice
and its actual inner-conjugacy quotient of an actual finite group. -/
theorem rational_attainment :
    ∀ a b : ℤ, 1 ≤ a → a < b → ∃ W : FiniteGroup,
      b * (classCount W.Carrier : ℤ) = a * (latticeCount W.Carrier : ℤ) := by
  intro a b ha hab
  have ha0 : 0 ≤ a := by omega
  have hb0 : 0 ≤ b := by omega
  have hnat : a.toNat < b.toNat := by omega
  obtain ⟨W, hL, hr⟩ := attain_natural a.toNat (by omega) (b.toNat - a.toNat)
  have he : a.toNat + (b.toNat - a.toNat) = b.toNat := by omega
  rw [← Nat.cast_add, he] at hr
  have hLR : (latticeCount W.Carrier : ℚ) ≠ 0 := by positivity
  have hbpos : 0 < b.toNat := by omega
  have hbR : (b.toNat : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hbpos
  have hcross := (div_eq_div_iff hLR hbR).mp hr
  have hcrossZ : (classCount W.Carrier : ℤ) * b.toNat =
      (a.toNat : ℤ) * latticeCount W.Carrier := by exact_mod_cast hcross
  refine ⟨W, ?_⟩
  simpa only [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0, mul_comm] using hcrossZ

end D5.S3.FiniteGroups.RationalSubgroupConjugacyAttainment
