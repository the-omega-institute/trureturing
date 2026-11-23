/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/FiniteCoverage
   generality: G
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors; instance=D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Main.makowski_schinzel_of_smooth_predecessors
   digest: Exact candidate cardinality proves completeness of the labelled finite table. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.CertificateState
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Enumeration
import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Strip
import Mathlib.Data.Nat.Bitwise
import Mathlib.FieldTheory.Finite.Basic

/-! Cardinality turns inclusion of the checked table into equality of finite candidate sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

open Finset

/-- On primes, the candidate test is equivalent to a non-power-of-two predecessor. -/
theorem candidate_of_prime {q : ℕ} (hq : q.Prime)
    : candidate (q - 1) = true ↔ ¬∃ k : ℕ, q - 1 = 2 ^ k := by
  constructor
  · intro hc hpow
    have hbits := Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.mpr hpow
    have hb : isPow2 (q - 1) = true := by simp [isPow2, hbits.1, hbits.2]
    simp [candidate, hb] at hc
  · intro hpow
    have hodd : q ≠ 2 := by
      intro h
      exact hpow ⟨0, by simp [h]⟩
    have hq2 : 2 ≤ q := hq.two_le
    have hsum : q - 1 + 1 = q := by omega
    have heven : (q - 1) % 2 = 0 := Nat.even_iff.mp (hq.even_sub_one hodd)
    have hnotpow : isPow2 (q - 1) = false := by
      apply Bool.eq_false_iff.mpr
      intro hb
      have hb' : q - 1 ≠ 0 ∧ ((q - 1) &&& (q - 1 - 1)) = 0 := by
        simpa [isPow2] using hb
      exact hpow (Nat.ne_zero_and_sub_one_eq_zero_iff_isPowerOfTwo.mp hb')
    have hfermat : 2 ^ (q - 1) % q = 1 := by
      have hc : Nat.Coprime 2 q :=
        Nat.coprime_two_left.mpr (hq.odd_of_ne_two hodd)
      have hz := Nat.ModEq.pow_card_sub_one_eq_one hq hc
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < q)] using hz
    have htrial : trialPrimes.all
        (fun d => decide (q ≤ d) || q % d != 0) = true := by
      apply List.all_eq_true.mpr
      intro d hd
      have hd2 : 2 ≤ d := by
        simp only [trialPrimes, allPrimes, oddPrimes, List.mem_cons, List.not_mem_nil,
          or_false] at hd
        omega
      by_cases hqd : q ≤ d
      · simp [hqd]
      · have hmod : q % d ≠ 0 := by
          intro hz
          rcases hq.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hz) with hd1 | hdq
          · omega
          · omega
        simp [hqd, hmod]
    simp only [candidate, hsum, heven, beq_self_eq_true, hnotpow, Bool.not_false,
      hfermat, htrial, Bool.and_self]

/-- Predecessors counted by the weighted recursive smooth-number enumeration. -/
def candidatePredecessors : Finset ℕ :=
  (factoredMultiples allPrimes.toFinset bound 2).filter (fun m => candidate m = true)

/-- The recursive count is the exact number of even smooth candidate predecessors. -/
private theorem candidatePredecessors_card :
    candidatePredecessors.card = smoothSum candidateWeight allPrimes bound 2 := by
  have hp : ∀ p ∈ allPrimes, p.Prime := by
    intro p h
    simp only [allPrimes, oddPrimes, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> norm_num
  have hn : allPrimes.Nodup := by decide
  have hbound : ∀ p ∈ allPrimes, bound < 2 * p ^ 64 := by
    intro p hp'
    have hpow := Nat.pow_le_pow_left (hp p hp').two_le 64
    have hb : bound < 2 ^ 64 := by decide
    omega
  have hs := smoothSum_eq_sum candidateWeight allPrimes hp hn
    (Or.inl (by decide : 0 < 2)) (by intro _; left; decide) (Or.inr hbound)
  unfold candidatePredecessors
  rw [Finset.card_filter]
  simpa only [candidateWeight] using hs.symm

/-- Every checked table value has a predecessor in the exactly counted candidate set. -/
private theorem table_predecessor_mem {e : ℕ} (hv : validEntry e = true) :
    entryValue e - 1 ∈ candidatePredecessors := by
  cases hp : oddPrimes[entryLabel e]? with
  | none => simp [validEntry, hp] at hv
  | some p =>
    have hh : (((2 ≤ entryValue e ∧ entryValue e - 1 ≤ bound) ∧
        candidate (entryValue e - 1) = true) ∧
        isSmooth allPrimes (entryValue e - 1) = true) ∧
        (entryValue e - 1) % p = 0 := by
      simpa only [validEntry, hp, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] using hv
    have hq : 2 ≤ entryValue e := hh.1.1.1.1
    have hb : entryValue e - 1 ≤ bound := hh.1.1.1.2
    have hc : candidate (entryValue e - 1) = true := hh.1.1.2
    have hsm : isSmooth allPrimes (entryValue e - 1) = true := hh.1.2
    have hpos : 0 < entryValue e - 1 := by omega
    have h64 : entryValue e - 1 < 2 ^ 65 := by dsimp [bound] at hb; omega
    have hps : ∀ r ∈ allPrimes, r.Prime := by
      intro r hr
      simp only [allPrimes, oddPrimes, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> norm_num
    have hfuel : entryValue e - 1 = 0 ∨
        ∀ p ∈ allPrimes, ¬p ^ 65 ∣ entryValue e - 1 := by
      right
      intro p hp hd
      have hpow := Nat.pow_le_pow_left (hps p hp).two_le 65
      have hle := Nat.le_of_dvd hpos hd
      omega
    have hfact := (isSmooth_iff (fun p hp => Or.inl (hps p hp))
      (hfuel.imp_right (fun h p hp _ => h p hp))).mp hsm
    have heven : (entryValue e - 1) % 2 = 0 := by
      have hc' := hc
      simp only [candidate, Bool.and_eq_true, beq_iff_eq] at hc'
      exact hc'.1.1.1
    have hdiv : 2 ∣ entryValue e - 1 := Nat.dvd_of_mod_eq_zero heven
    refine Finset.mem_filter.mpr ⟨?_, hc⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hb⟩, hdiv, ?_⟩
    exact Nat.mem_factoredNumbers_of_dvd hfact (Nat.div_dvd_of_dvd hdiv)

/-- The labelled table contains exactly the successors of all counted predecessors. -/
private theorem table_values_eq (T : List ℕ) (hv : T.all validEntry = true)
    (hn : (T.map entryValue).Nodup)
    (hc : smoothSum candidateWeight allPrimes bound 2 ≤ T.length) :
    (T.map entryValue).toFinset = candidatePredecessors.image (· + 1) := by
  have hsub : (T.map entryValue).toFinset ⊆ candidatePredecessors.image (· + 1) := by
    intro q hq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hq)
    have hm := table_predecessor_mem (List.all_eq_true.mp hv e he)
    have hpos : 1 ≤ entryValue e - 1 :=
      (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hm).1).1).1
    exact Finset.mem_image.mpr ⟨entryValue e - 1, hm, by omega⟩
  apply Finset.eq_of_subset_of_card_le hsub
  rw [List.toFinset_card_of_nodup hn, List.length_map]
  exact (Finset.card_image_le).trans (candidatePredecessors_card.le.trans hc)

/-- The checked list contains exactly the bounded smooth successors passing the candidate test. -/
theorem prime_mem_table (T : List ℕ) (hv : T.all validEntry = true)
    (hn : (T.map entryValue).Nodup)
    (hcount : smoothSum candidateWeight allPrimes bound 2 ≤ T.length) {q : ℕ} :
    (∃ e ∈ T, entryValue e = q) ↔
      q - 1 ≤ bound ∧ candidate (q - 1) = true ∧
        q - 1 ∈ Nat.smoothNumbers 98 := by
  have hprimes : allPrimes.toFinset = Nat.primesBelow 98 := by decide
  constructor
  · rintro ⟨e, he, rfl⟩
    have hv := List.all_eq_true.mp hv e he
    cases hp : oddPrimes[entryLabel e]? with
    | none => simp [validEntry, hp] at hv
    | some p =>
      have hh : (((2 ≤ entryValue e ∧ entryValue e - 1 ≤ bound) ∧
          candidate (entryValue e - 1) = true) ∧
          isSmooth allPrimes (entryValue e - 1) = true) ∧
          (entryValue e - 1) % p = 0 := by
        simpa only [validEntry, hp, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] using hv
      refine ⟨hh.1.1.1.2, hh.1.1.2, ?_⟩
      have hm := table_predecessor_mem hv
      obtain ⟨hm', _⟩ := Finset.mem_filter.mp hm
      obtain ⟨_, hdiv, hfact⟩ := Finset.mem_filter.mp hm'
      rw [Nat.smoothNumbers_eq_factoredNumbers_primesBelow, ← hprimes]
      have htwo : 2 ∈ Nat.factoredNumbers allPrimes.toFinset := by
        rw [hprimes, ← Nat.smoothNumbers_eq_factoredNumbers_primesBelow]
        exact Nat.mem_smoothNumbers'.mpr (fun r hr hrd => by
          have : r = 2 := (Nat.prime_two.eq_one_or_self_of_dvd r hrd).resolve_left hr.ne_one
          subst r
          decide)
      simpa only [Nat.mul_div_cancel' hdiv] using Nat.mul_mem_factoredNumbers htwo hfact
  · rintro ⟨hb, hc, hsm⟩
    have hpos : 0 < q - 1 :=
      Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hsm)
    have heven : 2 ∣ q - 1 := by
      have hh := hc
      simp only [candidate, Bool.and_eq_true, beq_iff_eq] at hh
      exact Nat.dvd_of_mod_eq_zero hh.1.1.1
    have hfact : q - 1 ∈ Nat.factoredNumbers allPrimes.toFinset := by
      rw [hprimes, ← Nat.smoothNumbers_eq_factoredNumbers_primesBelow]
      exact hsm
    have hm : q - 1 ∈ candidatePredecessors := by
      refine Finset.mem_filter.mpr ⟨?_, hc⟩
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hb⟩, heven, ?_⟩
      exact Nat.mem_factoredNumbers_of_dvd hfact (Nat.div_dvd_of_dvd heven)
    have hmem : q ∈ candidatePredecessors.image (· + 1) :=
      Finset.mem_image.mpr ⟨q - 1, hm, by omega⟩
    rw [← table_values_eq T hv hn hcount] at hmem
    exact List.mem_map.mp (List.mem_toFinset.mp hmem)

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
