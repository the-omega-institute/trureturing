/- GID: D5/S3/Arith/Divisors/ErdosNicolas/Classification
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/ErdosNicolas/Classification
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/Data/Base.base_ok,D5/S3/Arith/Divisors/ErdosNicolas/Data/SmallLifts.small_ok,D5/S3/Arith/Divisors/ErdosNicolas/Data/LargeLifts.large_ok,D5/S3/Arith/Divisors/ErdosNicolas/Data/ResidueTrees.residue_tree_ok,D5/S3/Arith/Divisors/ErdosNicolas/Data/MainBox.main_box_ok,D5/S3/Arith/Divisors/ErdosNicolas/Data/Extra.extra_ok
   digest: Finite certificate domains and exact exceptional-input classification. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Cutoffs
import D5.S3.Arith.Divisors.ErdosNicolas.ResidueChains
import D5.S3.Arith.Divisors.ErdosNicolas.SmallChains
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Factorization.Basic

/-! Explicit finite domains and the complete strong-induction classification. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

theorem good_implies_claim (h : ∀ n : ℕ, 0 < n → Good n) : ErdosNicolasClaim := by
  intro n hn
  have hnE : n ∉ exceptions := by
    simp only [exceptions, mem_insert, mem_singleton] at *
    omega
  simpa only [Good, hnE, ↓reduceIte] using h n (by omega)

/-- The seven small primes, in the order used by the exponent boxes. -/
def smallPrimes : Finset ℕ := {2, 3, 5, 7, 11, 13, 17}

/-- Primes in the half-open interval `[19,N)`. -/
@[irreducible] def largePrimes (N : ℕ) : Finset ℕ := (Ico 19 N).filter Nat.Prime

private theorem mem_largePrimes {p N : ℕ} :
    p ∈ largePrimes N ↔ (19 ≤ p ∧ p < N) ∧ p.Prime := by
  simp only [largePrimes, mem_filter, mem_Ico]

/-- The part of `n` with its entire `p`-primary factor removed. -/
def primeFreePart (n p : ℕ) : ℕ := n / p ^ n.factorization p

/-- Exactly the two induction inputs in (13), for an actual prime factor. -/
def HasExceptionalInput (n : ℕ) : Prop :=
  ∃ p ∈ n.primeFactors, n / p ∈ exceptions ∨ primeFreePart n p ∈ exceptions

/-- The union in (14); repetitions of the same integer are removed. -/
def smallLifts : Finset ℕ :=
  smallPrimes.biUnion fun p =>
    (exceptions.image (p * ·)) ∪
      (exceptions.filter fun e => ¬p ∣ e).biUnion fun e =>
        (Ico 1 (firstExponent p)).image fun a => p ^ a * e

/-- The exponents in (15), including the two second powers at 19 and 23. -/
def largeLiftExponents (p : ℕ) : Finset ℕ := Icc 1 (if p < 29 then 2 else 1)

/-- Triples `(e,p,a)` in (15), before taking their integer values. -/
@[irreducible] def largeLiftTriples : Finset (ℕ × ℕ × ℕ) :=
  exceptions.biUnion fun e => (largePrimes 674).biUnion fun p =>
    (largeLiftExponents p).image fun a => (e, p, a)

/-- Value of a triple in the large exceptional-lift table. -/
def largeLiftValue (v : ℕ × ℕ × ℕ) : ℕ := v.2.1 ^ v.2.2 * v.1

/-- The prime coordinates in (21). -/
def boxPrimes : Fin 7 → ℕ := ![2, 3, 5, 7, 11, 13, 17]

/-- Tight exponent caps of the main box (21). -/
def mainCaps : Fin 7 → ℕ := ![17, 7, 3, 2, 1, 1, 1]

/-- The main box consists of exponent vectors, avoiding duplicate-value encodings. -/
def mainBox : Finset (Fin 7 → ℕ) :=
  Fintype.piFinset fun i => range (mainCaps i + 1)

/-- Integer represented by a main-box vector. -/
def mainBoxValue (v : Fin 7 → ℕ) : ℕ := ∏ i, boxPrimes i ^ v i

/-- Caps before the small-prime chain refinement; these are the tree's caps. -/
def residueCap (q : ℕ) : ℕ :=
  if q = 2 then 17 else if q = 3 then 7 else if q = 5 then 4 else
  if q = 7 then 3 else if q = 11 then 2 else if q = 13 then 2 else 1

/-- Full finite domain covered by the residue tree for maximum prime `p`.
Composite coordinates are fixed at zero, and only primes strictly below `p` occur. -/
def residueBox (p : ℕ) : Finset (Fin p → ℕ) :=
  Fintype.piFinset fun q => range ((if q.val.Prime then residueCap q.val else 0) + 1)

/-- Integer at a leaf of the unpruned residue tree. -/
def residueBoxValue (p : ℕ) (v : Fin p → ℕ) : ℕ := p * ∏ q, q.val ^ v q

/-- The six extra integers after the small-prime chain refinement. -/
def extraValues : Finset ℕ := {625, 6875, 343, 4459, 121, 169}

/-- Base cases, including both strict bounds at every exception. -/
def BaseOK : Prop := ∀ n ∈ Icc 1 5040, Good n

/-- All 146 small-lift values, retaining `Good` at the 13 exceptional values. -/
def SmallLiftsOK : Prop := ∀ n ∈ smallLifts, Good n

/-- The 1638 triples in (15); all their values are outside the exception set. -/
def LargeLiftsOK : Prop :=
  ∀ v ∈ largeLiftTriples, hHat (largeLiftValue v) < ((largeLiftValue v).divisors.card : ℚ)

/-- Conditional step certified by the whole residue tree, including directly checked leaves.
Both kernel induction inputs equal `n / p`, since the maximum prime has exponent one. -/
def ResidueTreeOK : Prop :=
  ∀ p ∈ largePrimes 107, ∀ v ∈ residueBox p,
    hHat (residueBoxValue p v / p) ≤ ((residueBoxValue p v / p).divisors.card : ℚ) →
    hHat (residueBoxValue p v) < ((residueBoxValue p v).divisors.card : ℚ)

/-- The 13824 vectors in (21), with `Good` at exception leaves. -/
def MainBoxOK : Prop := ∀ v ∈ mainBox, Good (mainBoxValue v)

/-- Six extra values; four can instead be discharged by the prime-power theorem. -/
def ExtraOK : Prop := ∀ n ∈ extraValues, Good n

/-- A good input always supplies the uniform first-layer induction bound. -/
private theorem good_uniform_bound {n : ℕ} (h : Good n) :
    hHat n ≤ (8 / 7 : ℚ) * n.divisors.card := by
  unfold Good at h
  split_ifs at h with hn
  · linarith [h.2]
  · have ht : (0 : ℚ) ≤ n.divisors.card := Nat.cast_nonneg _
    linarith

/-- Outside `E` the stronger second-layer bound is available. -/
private theorem good_nonexception_bound {n : ℕ} (h : Good n) (hn : n ∉ exceptions) :
    hHat n ≤ (n.divisors.card : ℚ) := by
  exact (by simpa only [Good, hn, ↓reduceIte] using h :
    hHat n < (n.divisors.card : ℚ)).le

/-- Failure of (13) excludes the actual two induction inputs for every prime factor. -/
private theorem nonexceptional_inputs {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (h : ¬HasExceptionalInput n) :
    n / p ∉ exceptions ∧ primeFreePart n p ∉ exceptions := by
  have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.ne'⟩
  constructor
  · intro he
    exact h ⟨p, hmem, Or.inl he⟩
  · intro he
    exact h ⟨p, hmem, Or.inr he⟩

/-- The two genuine induction inputs are positive and strictly smaller. -/
private theorem induction_inputs_lt {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) :
    0 < n / p ∧ n / p < n ∧ 0 < primeFreePart n p ∧ primeFreePart n p < n := by
  have ha := hp.factorization_pos_of_dvd hn.ne' hpn
  have hm : 0 < primeFreePart n p := Nat.ordCompl_pos p hn.ne'
  have hpow : 1 < p ^ n.factorization p := one_lt_pow₀ hp.one_lt (by omega)
  exact ⟨Nat.div_pos (Nat.le_of_dvd hn hpn) hp.pos, Nat.div_lt_self hn hp.one_lt,
    hm, Nat.div_lt_self hn hpow⟩

/-- The legal bounds supplied by strong induction, with no arbitrary-divisor exclusion. -/
private theorem induction_input_bounds {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (ih : ∀ k < n, 0 < k → Good k) (h : ¬HasExceptionalInput n) :
    hHat (primeFreePart n p) ≤ ((primeFreePart n p).divisors.card : ℚ) ∧
      hHat (n / p) ≤ ((n / p).divisors.card : ℚ) := by
  obtain ⟨hpos, hlt, hmpos, hmlt⟩ := induction_inputs_lt hn hp hpn
  obtain ⟨he, hem⟩ := nonexceptional_inputs hn hp hpn h
  exact ⟨good_nonexception_bound (ih _ hmlt hmpos) hem,
    good_nonexception_bound (ih _ hlt hpos) he⟩

private theorem prime_lt_nineteen {p : ℕ} (hp : p.Prime) (h : p < 19) :
    p ∈ smallPrimes := by
  interval_cases p <;> norm_num [smallPrimes] at *

private theorem prime_lt_677_le_673 {p : ℕ} (hp : p.Prime) (h : p < 677) :
    p ≤ 673 := by
  by_contra hh
  have hlow : 674 ≤ p := by omega
  interval_cases p <;> norm_num at hp

private theorem large_lift_exponent_mem {p a : ℕ} (hp : 19 ≤ p)
    (ha : 0 < a) (hcut : a < firstExponent p) : a ∈ largeLiftExponents p := by
  simp only [largeLiftExponents, mem_Icc]
  unfold firstExponent at hcut
  split_ifs at hcut <;> split_ifs <;> omega

/-- After first-layer pruning, (13) lands in exactly the small or large lift domain. -/
private theorem exceptional_lift_coverage {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p ∈ n.primeFactors, p < 677)
    (hexp : ∀ p ∈ n.primeFactors, n.factorization p < firstExponent p)
    (h : HasExceptionalInput n) :
    n ∈ smallLifts ∨ ∃ v ∈ largeLiftTriples, n = largeLiftValue v := by
  obtain ⟨p, hpn, he | he⟩ := h
  all_goals have hp := (Nat.mem_primeFactors.mp hpn).1
  all_goals have hpd := (Nat.mem_primeFactors.mp hpn).2.1
  · have hnval : n = p * (n / p) := (Nat.mul_div_cancel' hpd).symm
    by_cases hps : p < 19
    · left
      apply mem_biUnion.mpr
      refine ⟨p, prime_lt_nineteen hp hps, mem_union_left _ ?_⟩
      exact mem_image.mpr ⟨n / p, he, hnval.symm⟩
    · right
      refine ⟨(n / p, p, 1), ?_, ?_⟩
      · unfold largeLiftTriples
        apply mem_biUnion.mpr
        refine ⟨n / p, he, mem_biUnion.mpr ⟨p, ?_, ?_⟩⟩
        · simp only [largePrimes, mem_filter, mem_Ico]
          exact ⟨⟨by omega, by have := prime_lt_677_le_673 hp (hprime p hpn); omega⟩, hp⟩
        · apply mem_image.mpr
          refine ⟨1, ?_, rfl⟩
          unfold largeLiftExponents
          split_ifs <;> simp
      · simpa only [largeLiftValue, pow_one] using hnval
  · have hm : ¬p ∣ primeFreePart n p := Nat.not_dvd_ordCompl hp hn.ne'
    have hnval : n = p ^ n.factorization p * primeFreePart n p :=
      (Nat.ordProj_mul_ordCompl_eq_self n p).symm
    have ha : 0 < n.factorization p := hp.factorization_pos_of_dvd hn.ne' hpd
    by_cases hps : p < 19
    · left
      apply mem_biUnion.mpr
      refine ⟨p, prime_lt_nineteen hp hps, mem_union_right _ ?_⟩
      apply mem_biUnion.mpr
      refine ⟨primeFreePart n p, mem_filter.mpr ⟨he, hm⟩, ?_⟩
      exact mem_image.mpr ⟨n.factorization p, mem_Ico.mpr ⟨ha, hexp p hpn⟩,
        hnval.symm⟩
    · right
      refine ⟨(primeFreePart n p, p, n.factorization p), ?_, hnval⟩
      unfold largeLiftTriples
      apply mem_biUnion.mpr
      refine ⟨primeFreePart n p, he, mem_biUnion.mpr ⟨p, ?_, ?_⟩⟩
      · simp only [largePrimes, mem_filter, mem_Ico]
        exact ⟨⟨by omega, by have := prime_lt_677_le_673 hp (hprime p hpn); omega⟩, hp⟩
      · exact mem_image.mpr ⟨n.factorization p,
          large_lift_exponent_mem (by omega) ha (hexp p hpn), rfl⟩

/-- Exponents still available after the second-layer cutoff table. -/
def BelowSecondCutoffs (n : ℕ) : Prop :=
  ∀ p ∈ n.primeFactors, n.factorization p < secondExponent p

/-- Survival of the four small-prime chain tests, expressed as a structural condition. -/
def SmallChainSurvivor (n : ℕ) : Prop :=
  ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ), smallChainExponent p ≤ n.factorization p →
    ∀ q ∈ n.primeFactors, q = p ∨ q % p = 1 ∨ q % p = p - 1

private theorem factorization_zero_of_not_mem {n p : ℕ} (hp : p ∉ n.primeFactors) :
    n.factorization p = 0 := by
  apply Finsupp.notMem_support_iff.mp
  simpa only [Nat.support_factorization] using hp

private theorem small_factorization_bound {n : ℕ} (h : BelowSecondCutoffs n) (p : ℕ) :
    n.factorization p < secondExponent p := by
  by_cases hp : p ∈ n.primeFactors
  · exact h p hp
  · rw [factorization_zero_of_not_mem hp]
    unfold secondExponent
    split_ifs <;> omega

private theorem small_factorization_reconstruction {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p ∈ n.primeFactors, p ≤ 17) :
    n = 2 ^ n.factorization 2 * 3 ^ n.factorization 3 * 5 ^ n.factorization 5 *
      7 ^ n.factorization 7 * 11 ^ n.factorization 11 * 13 ^ n.factorization 13 *
      17 ^ n.factorization 17 := by
  have hs : n.primeFactors ⊆ smallPrimes := by
    intro p hp
    exact prime_lt_nineteen (Nat.prime_of_mem_primeFactors hp) (by
      have := hprime p hp
      omega)
  have he : (∏ p ∈ n.primeFactors, p ^ n.factorization p) =
      ∏ p ∈ smallPrimes, p ^ n.factorization p := by
    apply prod_subset hs
    intro p _ hp
    rw [factorization_zero_of_not_mem hp, pow_zero]
  rw [← Nat.prod_primeFactors_pow_factorization hn.ne'] at he
  simpa [smallPrimes, mul_assoc] using he

private theorem chain_forces_zero {n p q : ℕ} (h : SmallChainSurvivor n)
    (hp : p ∈ ({5, 7, 11, 13} : Finset ℕ)) (ha : smallChainExponent p ≤ n.factorization p)
    (hq : ¬(q = p ∨ q % p = 1 ∨ q % p = p - 1)) : n.factorization q = 0 := by
  apply factorization_zero_of_not_mem
  intro hmem
  exact hq (h p hp ha q hmem)

/-- All small-prime survivors are in (21) or are one of the six explicit extras.
This is a structural classification; the analytic tests are not assumed to be certificates. -/
private theorem small_survivor_coverage {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p ∈ n.primeFactors, p ≤ 17) (hcut : BelowSecondCutoffs n)
    (hchain : SmallChainSurvivor n) :
    (∃ v ∈ mainBox, n = mainBoxValue v) ∨ n ∈ extraValues := by
  have h2 := small_factorization_bound hcut 2
  have h3 := small_factorization_bound hcut 3
  have h5 := small_factorization_bound hcut 5
  have h7 := small_factorization_bound hcut 7
  have h11 := small_factorization_bound hcut 11
  have h13 := small_factorization_bound hcut 13
  have h17 := small_factorization_bound hcut 17
  change n.factorization 2 < 18 at h2
  change n.factorization 3 < 8 at h3
  change n.factorization 5 < 5 at h5
  change n.factorization 7 < 4 at h7
  change n.factorization 11 < 3 at h11
  change n.factorization 13 < 3 at h13
  change n.factorization 17 < 2 at h17
  have hnprod := small_factorization_reconstruction hn hprime
  by_cases he11 : 2 ≤ n.factorization 11
  · have hz (q : ℕ) (hq : q ∈ ({2, 3, 5, 7, 13, 17} : Finset ℕ)) :
        n.factorization q = 0 := by
      apply chain_forces_zero hchain (p := 11) (by simp) (by
        simpa [smallChainExponent] using he11)
      simp only [mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have he : n.factorization 11 = 2 := by omega
    right
    simp only [hz 2 (by simp), hz 3 (by simp), hz 5 (by simp), hz 7 (by simp),
      hz 13 (by simp), hz 17 (by simp), he] at hnprod
    norm_num at hnprod
    simp [extraValues, hnprod]
  by_cases he13 : 2 ≤ n.factorization 13
  · have hz (q : ℕ) (hq : q ∈ ({2, 3, 5, 7, 11, 17} : Finset ℕ)) :
        n.factorization q = 0 := by
      apply chain_forces_zero hchain (p := 13) (by simp) (by
        simpa [smallChainExponent] using he13)
      simp only [mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have he : n.factorization 13 = 2 := by omega
    right
    simp only [hz 2 (by simp), hz 3 (by simp), hz 5 (by simp), hz 7 (by simp),
      hz 11 (by simp), hz 17 (by simp), he] at hnprod
    norm_num at hnprod
    simp [extraValues, hnprod]
  by_cases he5 : 4 ≤ n.factorization 5
  · have hz (q : ℕ) (hq : q ∈ ({2, 3, 7, 13, 17} : Finset ℕ)) :
        n.factorization q = 0 := by
      apply chain_forces_zero hchain (p := 5) (by simp) (by
        simpa [smallChainExponent] using he5)
      simp only [mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have he : n.factorization 5 = 4 := by omega
    right
    simp only [hz 2 (by simp), hz 3 (by simp), hz 7 (by simp),
      hz 13 (by simp), hz 17 (by simp), he] at hnprod
    have h11' : n.factorization 11 = 0 ∨ n.factorization 11 = 1 := by omega
    rcases h11' with he | he
    all_goals
      rw [he] at hnprod
      norm_num at hnprod
      simp [extraValues, hnprod]
  by_cases he7 : 3 ≤ n.factorization 7
  · have hz (q : ℕ) (hq : q ∈ ({2, 3, 5, 11, 17} : Finset ℕ)) :
        n.factorization q = 0 := by
      apply chain_forces_zero hchain (p := 7) (by simp) (by
        simpa [smallChainExponent] using he7)
      simp only [mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl <;> norm_num
    have he : n.factorization 7 = 3 := by omega
    right
    simp only [hz 2 (by simp), hz 3 (by simp), hz 5 (by simp),
      hz 11 (by simp), hz 17 (by simp), he] at hnprod
    have h13' : n.factorization 13 = 0 ∨ n.factorization 13 = 1 := by omega
    rcases h13' with he | he
    all_goals
      rw [he] at hnprod
      norm_num at hnprod
      simp [extraValues, hnprod]
  · left
    let v : Fin 7 → ℕ := fun i => n.factorization (boxPrimes i)
    refine ⟨v, ?_, ?_⟩
    · simp only [mainBox, Fintype.mem_piFinset, mem_range]
      intro i
      fin_cases i <;> simp [v, boxPrimes, mainCaps] <;> omega
    · simpa [mainBoxValue, Fin.prod_univ_seven, v, boxPrimes, mul_assoc] using hnprod

private theorem residueCap_succ {q : ℕ} (hq : q.Prime) :
    residueCap q + 1 = secondExponent q := by
  by_cases h17 : 17 ≤ q
  · unfold residueCap secondExponent
    split_ifs <;> omega
  · have h16 : q ≤ 16 := by omega
    interval_cases q <;> norm_num at hq
    all_goals norm_num [residueCap, secondExponent]

private theorem residue_box_representation {n p : ℕ} (hn : 0 < n)
    (hp : p ∈ n.primeFactors) (hmax : ∀ q ∈ n.primeFactors, q ≤ p)
    (he : n.factorization p = 1) (hcut : BelowSecondCutoffs n) :
    ∃ v ∈ residueBox p, n = residueBoxValue p v := by
  let v : Fin p → ℕ := fun q => n.factorization q.val
  have hsubset : n.primeFactors.erase p ⊆ range p := by
    intro q hq
    obtain ⟨hne, hq⟩ := mem_erase.mp hq
    exact mem_range.mpr (lt_of_le_of_ne (hmax q hq) hne)
  have hprod : (∏ q ∈ n.primeFactors.erase p, q ^ n.factorization q) =
      ∏ q ∈ range p, q ^ n.factorization q := by
    apply prod_subset hsubset
    intro q hq hnot
    have hne : q ≠ p := by
      have hlt := mem_range.mp hq
      omega
    rw [factorization_zero_of_not_mem (by
      intro hm
      exact hnot (mem_erase.mpr ⟨hne, hm⟩)), pow_zero]
  have heq := mul_prod_erase n.primeFactors (fun q => q ^ n.factorization q) hp
  rw [he, pow_one, hprod, ← Nat.prod_primeFactors_pow_factorization hn.ne',
    Finset.prod_range] at heq
  refine ⟨v, ?_, heq.symm⟩
  simp only [residueBox, Fintype.mem_piFinset, mem_range]
  intro q
  change n.factorization q.val < (if q.val.Prime then residueCap q.val else 0) + 1
  by_cases hq : q.val.Prime
  · rw [if_pos hq]
    have h := small_factorization_bound hcut q.val
    simpa only [residueCap_succ hq] using h
  · rw [if_neg hq, Nat.factorization_eq_zero_of_not_prime _ hq]
    omega

/-- Exact finite destinations for the ordinary branch after the analytic screens. -/
private theorem ordinary_survivor_coverage {n : ℕ} (hn : 0 < n)
    (hprime : ∀ p ∈ n.primeFactors, p < 107) (hcut : BelowSecondCutoffs n)
    (hchain : SmallChainSurvivor n) :
    (∃ v ∈ mainBox, n = mainBoxValue v) ∨ n ∈ extraValues ∨
      ∃ p ∈ largePrimes 107, ∃ v ∈ residueBox p, n = residueBoxValue p v := by
  by_cases hlarge : ∃ p ∈ n.primeFactors, 19 ≤ p
  · obtain ⟨q, hq, hq19⟩ := hlarge
    have hne : n.primeFactors.Nonempty := ⟨q, hq⟩
    let p := n.primeFactors.max' hne
    have hp : p ∈ n.primeFactors := max'_mem _ _
    have hmax : ∀ q ∈ n.primeFactors, q ≤ p := fun q hq => le_max' _ q hq
    have hp19 : 19 ≤ p := hq19.trans (hmax q hq)
    have hpexp := hcut p hp
    have hppos := (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd
      hn.ne' (Nat.dvd_of_mem_primeFactors hp)
    have he : n.factorization p = 1 := by
      unfold secondExponent at hpexp
      split_ifs at hpexp <;> omega
    obtain ⟨v, hv, hnv⟩ := residue_box_representation hn hp hmax he hcut
    right
    right
    refine ⟨p, mem_largePrimes.mpr ⟨⟨hp19, hprime p hp⟩,
      Nat.prime_of_mem_primeFactors hp⟩, v, hv, hnv⟩
  · have hs : ∀ p ∈ n.primeFactors, p ≤ 17 := by
      intro p hp
      have hl : p < 19 := by
        by_contra hh
        exact hlarge ⟨p, hp, by omega⟩
      have hm := prime_lt_nineteen (Nat.prime_of_mem_primeFactors hp) hl
      simp only [smallPrimes, mem_insert, mem_singleton] at hm
      omega
    exact (small_survivor_coverage hn hs hcut hchain).imp_right Or.inl

/-- Apply the kernel criterion at the exact valuation of an actual prime factor. -/
private theorem prime_factor_induction_step {n p L : ℕ} {bA bB F : ℚ}
    (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n) (hL : 0 < L)
    (hA : hHat (primeFreePart n p) ≤ bA * (primeFreePart n p).divisors.card)
    (hB : hHat (n / p) ≤ bB * (n / p).divisors.card)
    (hF : (∑ d ∈ (primeFreePart n p).divisors, f p L (d % p)) /
      ((primeFreePart n p).divisors.card : ℚ) ≤ F)
    (hTest : KernelTest (n.factorization p) p L bA bB F) :
    hHat n < (n.divisors.card : ℚ) := by
  have ha := hp.factorization_pos_of_dvd hn.ne' hpn
  have hpm : ¬p ∣ primeFreePart n p := Nat.not_dvd_ordCompl hp hn.ne'
  have hnval : n = p ^ n.factorization p * primeFreePart n p :=
    (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have htau : (n / p).divisors.card = n.factorization p * (primeFreePart n p).divisors.card := by
    conv_lhs => rw [hnval]
    rw [prime_power_mul_div hp.pos ha]
    rw [card_divisors_prime_power_mul hp hpm]
    congr 1
    omega
  have hB' : hHat ((p ^ n.factorization p * primeFreePart n p) / p) ≤
      bB * n.factorization p * (primeFreePart n p).divisors.card := by
    rw [← hnval]
    simpa only [htau, Nat.cast_mul, mul_assoc] using hB
  have hres := kernel_criterion_residue_average hp hpm hL hA hB' hF hTest
  simpa only [← hnval] using hres

/-- The first exponent table closes every large exponent using only smaller `Good` inputs. -/
private theorem first_exponent_closes {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (ih : ∀ k < n, 0 < k → Good k) (ha : firstExponent p ≤ n.factorization p) :
    hHat n < (n.divisors.card : ℚ) := by
  obtain ⟨hpos, hlt, hmpos, hmlt⟩ := induction_inputs_lt hn hp hpn
  apply prime_factor_induction_step hn hp hpn (L := firstLength p)
    (bA := 8 / 7) (bB := 8 / 7) (F := firstResidual p)
  · unfold firstLength
    split_ifs <;> norm_num
  · exact good_uniform_bound (ih _ hmlt hmpos)
  · exact good_uniform_bound (ih _ hlt hpos)
  · exact divisor_residue_average_le hp.pos hmpos (Nat.not_dvd_ordCompl hp hn.ne')
      (first_residual_max hp).1
  · exact first_cutoff_exponent hp ha

/-- Exclusion of (13) makes the second exponent table legal. -/
private theorem second_exponent_closes {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (ih : ∀ k < n, 0 < k → Good k) (hno : ¬HasExceptionalInput n)
    (ha : secondExponent p ≤ n.factorization p) : hHat n < (n.divisors.card : ℚ) := by
  obtain ⟨hA, hB⟩ := induction_input_bounds hn hp hpn ih hno
  have hmpos : 0 < primeFreePart n p := Nat.ordCompl_pos p hn.ne'
  apply prime_factor_induction_step hn hp hpn (L := secondLength p)
    (bA := 1) (bB := 1) (F := secondResidual p)
  · unfold secondLength
    split_ifs <;> norm_num
  · simpa using hA
  · simpa using hB
  · exact divisor_residue_average_le hp.pos hmpos (Nat.not_dvd_ordCompl hp hn.ne')
      (second_residual_max hp).1
  · exact second_cutoff_exponent hp ha

/-- A smaller prime is not an endpoint residue modulo a prime at least five. -/
theorem prime_below_residue_ne_signed_one {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hp₅ : 5 ≤ p) (hqp : q < p) :
    (q : ZMod p) ≠ 1 ∧ (q : ZMod p) ≠ -1 := by
  constructor
  · intro he
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hqp, ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at hv
    have := hq.two_le
    omega
  · intro he
    have hd : p ∣ q + 1 := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      rw [he]
      ring
    have hle : p ≤ q + 1 := Nat.le_of_dvd (by omega) hd
    have heqp : q + 1 = p := by omega
    have hpodd := hp.eq_two_or_odd
    have hqodd := hq.eq_two_or_odd
    omega

/-- At the largest prime, the doubled-period chain bound supplies the residual. -/
private theorem largest_prime_induction_step {n p : ℕ} {b : ℚ} (hn : 0 < n)
    (hp : p.Prime) (hpn : p ∣ n) (hp11 : 11 ≤ p)
    (hmax : ∀ q ∈ n.primeFactors, q ≤ p)
    (hA : hHat (primeFreePart n p) ≤ b * (primeFreePart n p).divisors.card)
    (hB : hHat (n / p) ≤ b * (n / p).divisors.card)
    (hTest : KernelTest (n.factorization p) p (2 * p) b b (3 / 4)) :
    hHat n < (n.divisors.card : ℚ) := by
  by_cases hm : primeFreePart n p = 1
  · have hnval := Nat.ordProj_mul_ordCompl_eq_self n p
    change p ^ n.factorization p * primeFreePart n p = n at hnval
    rw [hm, mul_one] at hnval
    rw [← hnval]
    have hb := hHat_prime_pow_le hp (n.factorization p)
    rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]
    push_cast
    linarith only [hb]
  · obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hm
    have hpm : ¬p ∣ primeFreePart n p := Nat.not_dvd_ordCompl hp hn.ne'
    have hqn : q ∣ n := hqm.trans (Nat.ordCompl_dvd n p)
    have hqmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn.ne'⟩
    have hqp : q < p := lt_of_le_of_ne (hmax q hqmem) (by
      intro h
      subst q
      exact hpm hqm)
    have hmpos : 0 < primeFreePart n p := Nat.ordCompl_pos p hn.ne'
    have hsum := (residue_average_three_quarters hp.two_le (by omega) (by omega)).1.mpr
      ⟨q, Nat.mem_divisors.mpr ⟨hqm, hmpos.ne'⟩,
        prime_below_residue_ne_signed_one hp hq (by omega) hqp⟩
    have ht : (0 : ℚ) < (primeFreePart n p).divisors.card := by
      exact_mod_cast card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hmpos.ne'⟩
    exact prime_factor_induction_step hn hp hpn (by have := hp.pos; omega)
      hA hB ((div_le_iff₀ ht).mpr hsum.le) (by
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hTest)

/-- The uniform induction bound closes maximum primes at least 677. -/
private theorem first_largest_prime_closes {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : p ∣ n) (hmax : ∀ q ∈ n.primeFactors, q ≤ p) (hp677 : 677 ≤ p)
    (ih : ∀ k < n, 0 < k → Good k) : hHat n < (n.divisors.card : ℚ) := by
  obtain ⟨hpos, hlt, hmpos, hmlt⟩ := induction_inputs_lt hn hp hpn
  exact largest_prime_induction_step hn hp hpn (by omega) hmax
    (good_uniform_bound (ih _ hmlt hmpos)) (good_uniform_bound (ih _ hlt hpos))
    (largest_prime_test_eight_sevenths (by omega : 676 ≤ p)
      (hp.factorization_pos_of_dvd hn.ne' hpn))

/-- In the ordinary branch the improved cutoff is 107. -/
private theorem second_largest_prime_closes {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : p ∣ n) (hmax : ∀ q ∈ n.primeFactors, q ≤ p) (hp107 : 107 ≤ p)
    (ih : ∀ k < n, 0 < k → Good k) (hno : ¬HasExceptionalInput n) :
    hHat n < (n.divisors.card : ℚ) := by
  obtain ⟨hA, hB⟩ := induction_input_bounds hn hp hpn ih hno
  exact largest_prime_induction_step hn hp hpn (by omega) hmax
    (by simpa using hA) (by simpa using hB)
    (largest_prime_test_one (by omega : 105 ≤ p) (hp.factorization_pos_of_dvd hn.ne' hpn))

/-- A small-prime chain closes whenever another prime factor is not an endpoint residue. -/
private theorem small_chain_closes {n p q : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : p ∣ n)
    (hq : q.Prime) (hqn : q ∣ n) (hqp : q ≠ p)
    (hps : p ∈ ({5, 7, 11, 13} : Finset ℕ))
    (ha : smallChainExponent p ≤ n.factorization p)
    (hq1 : q % p ≠ 1) (hqm1 : q % p ≠ p - 1)
    (ih : ∀ k < n, 0 < k → Good k) (hno : ¬HasExceptionalInput n) :
    hHat n < (n.divisors.card : ℚ) := by
  obtain ⟨hA, hB⟩ := induction_input_bounds hn hp hpn ih hno
  have hpm : ¬p ∣ primeFreePart n p := Nat.not_dvd_ordCompl hp hn.ne'
  have hpq : ¬p ∣ q := fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm
  have hqm : q ∣ primeFreePart n p := Nat.dvd_ordCompl_of_dvd_not_dvd hqn hpq
  have hsum := small_chain_average hp hq hps hqm hpm hq1 hqm1
  have hmpos : 0 < primeFreePart n p := Nat.ordCompl_pos p hn.ne'
  have ht : (0 : ℚ) < (primeFreePart n p).divisors.card := by
    exact_mod_cast card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hmpos.ne'⟩
  apply prime_factor_induction_step hn hp hpn (L := smallChainLength p)
    (bA := 1) (bB := 1) (F := smallChainResidual p)
  · unfold smallChainLength
    split_ifs <;> norm_num
  · simpa using hA
  · simpa using hB
  · exact (div_le_iff₀ ht).mpr hsum
  · exact small_chain_test hps ha

private theorem outside_exceptions_of_gt {n : ℕ} (hn : 5040 < n) : n ∉ exceptions := by
  simp only [exceptions, mem_insert, mem_singleton]
  omega

/-- The finite domains close every branch surviving the analytic screens. -/
private theorem finite_survivor_good (hsmall : SmallLiftsOK) (hlarge : LargeLiftsOK)
    (htree : ResidueTreeOK) (hbox : MainBoxOK) (hextra : ExtraOK)
    {n : ℕ} (hn : 5040 < n) (ih : ∀ k < n, 0 < k → Good k)
    (hprime : ∀ p ∈ n.primeFactors, p < 677)
    (hexp : ∀ p ∈ n.primeFactors, n.factorization p < firstExponent p)
    (hordinary : ¬HasExceptionalInput n →
      (∀ p ∈ n.primeFactors, p < 107) ∧ BelowSecondCutoffs n ∧ SmallChainSurvivor n) :
    Good n := by
  have hnE := outside_exceptions_of_gt hn
  unfold LargeLiftsOK at hlarge
  by_cases he : HasExceptionalInput n
  · obtain hs | ⟨v, hv, hnv⟩ := exceptional_lift_coverage (by omega) hprime hexp he
    · exact hsmall n hs
    · have h : hHat (largeLiftValue v) < ((largeLiftValue v).divisors.card : ℚ) := hlarge v hv
      simpa only [Good, hnE, ↓reduceIte, ← hnv] using h
  · obtain ⟨hprime', hexp', hchain⟩ := hordinary he
    obtain ⟨v, hv, hnv⟩ | hs | ⟨p, hp, v, hv, hnv⟩ :=
      ordinary_survivor_coverage (by omega) hprime' hexp' hchain
    · simpa only [← hnv] using hbox v hv
    · exact hextra n hs
    · have h := htree p hp v hv
      rw [← hnv] at h
      have hpn : p ∣ n := by
        rw [hnv]
        exact dvd_mul_right _ _
      have hp' : p.Prime := (mem_largePrimes.mp hp).2
      have hB := (induction_input_bounds (by omega) hp' hpn ih he).2
      simpa only [Good, hnE, ↓reduceIte] using h hB

private theorem largest_prime_above {n q : ℕ} (hq : q ∈ n.primeFactors) :
    ∃ p ∈ n.primeFactors, q ≤ p ∧ ∀ r ∈ n.primeFactors, r ≤ p := by
  have hne : n.primeFactors.Nonempty := ⟨q, hq⟩
  exact ⟨n.primeFactors.max' hne, max'_mem _ _, le_max' _ _ hq,
    fun r hr => le_max' _ _ hr⟩

/-- Complete strong induction from six concrete finite certificate propositions.
No cutoff, residue-average inequality, or infinite induction step is a certificate premise. -/
theorem good_of_finite_certificates (hbase : BaseOK) (hsmall : SmallLiftsOK)
    (hlarge : LargeLiftsOK) (htree : ResidueTreeOK) (hbox : MainBoxOK) (hextra : ExtraOK) :
    ∀ n : ℕ, 0 < n → Good n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hb : n ≤ 5040
    · exact hbase n (mem_Icc.mpr ⟨hn, hb⟩)
    have hnlarge : 5040 < n := by omega
    have hnE := outside_exceptions_of_gt hnlarge
    by_contra hng
    have hfail : ¬hHat n < (n.divisors.card : ℚ) := by
      simpa only [Good, hnE, ↓reduceIte] using hng
    apply hng
    apply finite_survivor_good hsmall hlarge htree hbox hextra hnlarge ih
    · intro q hq
      by_contra hqbig
      obtain ⟨p, hp, hqp, hmax⟩ := largest_prime_above hq
      exact hfail (first_largest_prime_closes hn (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp) hmax (by omega) ih)
    · intro p hp
      by_contra ha
      exact hfail (first_exponent_closes hn (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp) ih (by omega))
    · intro hno
      refine ⟨?_, ?_, ?_⟩
      · intro q hq
        by_contra hqbig
        obtain ⟨p, hp, hqp, hmax⟩ := largest_prime_above hq
        exact hfail (second_largest_prime_closes hn (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp) hmax (by omega) ih hno)
      · intro p hp
        by_contra ha
        exact hfail (second_exponent_closes hn (Nat.prime_of_mem_primeFactors hp)
          (Nat.dvd_of_mem_primeFactors hp) ih hno (by omega))
      · intro p hps ha q hq
        by_contra hbad
        simp only [not_or] at hbad
        have hp : p.Prime := by
          simp only [mem_insert, mem_singleton] at hps
          rcases hps with rfl | rfl | rfl | rfl <;> norm_num
        have ha0 : 0 < smallChainExponent p := by
          unfold smallChainExponent
          split_ifs <;> norm_num
        have hpn : p ∣ n := (hp.dvd_iff_one_le_factorization hn.ne').mpr (by omega)
        exact hfail (small_chain_closes hn hp hpn (Nat.prime_of_mem_primeFactors hq)
          (Nat.dvd_of_mem_primeFactors hq) hbad.1 hps ha hbad.2.1 hbad.2.2 ih hno)

/-- The original assertion follows once the finite certificate modules are supplied. -/
theorem erdos_nicolas_of_finite_certificates (hbase : BaseOK) (hsmall : SmallLiftsOK)
    (hlarge : LargeLiftsOK) (htree : ResidueTreeOK) (hbox : MainBoxOK) (hextra : ExtraOK) :
    ErdosNicolasClaim :=
  good_implies_claim (good_of_finite_certificates hbase hsmall hlarge htree hbox hextra)

#print axioms good_uniform_bound
#print axioms good_nonexception_bound
#print axioms nonexceptional_inputs
#print axioms induction_inputs_lt
#print axioms induction_input_bounds
#print axioms exceptional_lift_coverage
#print axioms small_survivor_coverage
#print axioms ordinary_survivor_coverage
#print axioms prime_factor_induction_step
#print axioms first_exponent_closes
#print axioms second_exponent_closes
#print axioms finite_survivor_good
#print axioms largest_prime_induction_step
#print axioms first_largest_prime_closes
#print axioms second_largest_prime_closes
#print axioms small_chain_closes
#print axioms good_of_finite_certificates
#print axioms erdos_nicolas_of_finite_certificates

#print axioms good_implies_claim

end D5.S3.Arith.ErdosNicolas
