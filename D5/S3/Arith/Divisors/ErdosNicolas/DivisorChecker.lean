/- GID: D5/S3/Arith/Divisors/ErdosNicolas/DivisorChecker
   generality: G
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; instance=D5/S3/Arith/Divisors/ErdosNicolas/Data/Base00.chunk_checked
   digest: Trial division, factor certificates, and complete increasing divisor tables. -/

import D5.S3.Arith.Divisors.ErdosNicolas.Basic
import D5.S3.Arith.Divisors.ErdosNicolas.DivisorBlocks
import Mathlib.Data.List.Chain

/-! Prime-factor certificates provide counts without enumerating the represented integer. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

/-- Test all potential prime divisors up to the square root, using only natural arithmetic. -/
def checkPrime (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range (Nat.sqrt p + 1)).all
    (fun d => decide (d < 2) || decide (p % d ≠ 0))

/-- The bounded trial test is equivalent to primality, including zero and one. -/
theorem checkPrime_iff (p : ℕ) : checkPrime p = true ↔ p.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [checkPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, List.mem_range]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro d hd hds hdiv
    have ht := h d (by omega)
    rcases ht with ht | ht
    · omega
    · exact ht (Nat.mod_eq_zero_of_dvd hdiv)
  · rintro ⟨hp, h⟩
    refine ⟨hp, ?_⟩
    intro d hd
    by_cases hsmall : d < 2
    · exact Or.inl hsmall
    · exact Or.inr (fun hz => h d (by omega) (by omega) (Nat.dvd_of_mod_eq_zero hz))

/-- A concrete primality decision whose Boolean projection runs the small trial test. -/
def certificatePrimeDecidable (p : ℕ) : Decidable p.Prime :=
  decidable_of_iff' (checkPrime p = true) (checkPrime_iff p).symm

#print axioms checkPrime_iff

/-- Integer represented by prime and exponent pairs. -/
def factorValue : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (p, a) :: fs => p ^ a * factorValue fs

/-- Predicted divisor count of a prime factorization. -/
def factorTau : List (ℕ × ℕ) → ℕ
  | [] => 1
  | (_, a) :: fs => (a + 1) * factorTau fs

/-- Each listed prime is absent from the remaining factorization. -/
def checkFactors : List (ℕ × ℕ) → Bool
  | [] => true
  | (p, _) :: fs =>
      @decide p.Prime (certificatePrimeDecidable p) &&
        decide (¬p ∣ factorValue fs) && checkFactors fs

/-- A factor certificate proves positivity and the product formula for divisor count. -/
theorem checkFactors_sound {fs : List (ℕ × ℕ)} (h : checkFactors fs = true) :
    0 < factorValue fs ∧ (factorValue fs).divisors.card = factorTau fs := by
  induction fs with
  | nil => simp [factorValue, factorTau]
  | cons v fs ih =>
    rcases v with ⟨p, a⟩
    simp only [checkFactors, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hm, ht⟩ := ih h.2
    constructor
    · exact Nat.mul_pos (pow_pos h.1.1.pos _) hm
    · change (p ^ a * factorValue fs).divisors.card = (a + 1) * factorTau fs
      rw [card_divisors_prime_power_mul h.1.1 h.1.2, ← ht]

/-- Adjacent comparisons return only Booleans, without accumulating a chain proof. -/
def checkIncreasing : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: ds => Nat.blt a b && checkIncreasing (b :: ds)

/-- The executable adjacent comparison is exactly strict list-chain order. -/
private theorem checkIncreasing_iff (ds : List ℕ) :
    checkIncreasing ds = true ↔ ds.IsChain (· < ·) := by
  induction ds with
  | nil => simp [checkIncreasing]
  | cons a ds ih =>
    cases ds with
    | nil => simp [checkIncreasing]
    | cons b ds =>
      change ((Nat.blt a b && checkIncreasing (b :: ds)) = true) ↔ _
      simp only [Bool.and_eq_true, Nat.blt_eq, decide_eq_true_eq, ih,
        List.isChain_cons_cons]

/-- Linear adjacent-order check and linear divisibility checks, without enumerating `n`. -/
def checkDivisors (n : ℕ) (fs : List (ℕ × ℕ)) (ds : List ℕ) : Bool :=
  checkFactors fs && decide (factorValue fs = n) &&
    checkIncreasing ds &&
    ds.all (fun d => decide (0 < d ∧ d ∣ n)) &&
    decide (ds.length = factorTau fs)

/-- An increasing divisor sublist of the correct size is the entire divisor set. -/
theorem checkDivisors_sound {n : ℕ} {fs : List (ℕ × ℕ)} {ds : List ℕ}
    (h : checkDivisors n fs ds = true) :
    ds.Pairwise (· < ·) ∧ ds.toFinset = n.divisors ∧ n.divisors.card = ds.length := by
  simp only [checkDivisors, Bool.and_eq_true, decide_eq_true_eq, checkIncreasing_iff,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hf, hn⟩, hs⟩, hd⟩, hl⟩ := h
  obtain ⟨hnpos, ht⟩ := checkFactors_sound hf
  rw [hn] at hnpos ht
  have hsorted : ds.Pairwise (· < ·) := List.isChain_iff_pairwise.mp hs
  have hsub : ds.toFinset ⊆ n.divisors := by
    intro d hdmem
    exact Nat.mem_divisors.mpr ⟨(hd d (List.mem_toFinset.mp hdmem)).2, hnpos.ne'⟩
  have hcard : ds.toFinset.card = n.divisors.card := by
    rw [List.toFinset_card_of_nodup hsorted.nodup]
    exact hl.trans ht.symm
  exact ⟨hsorted, Finset.eq_of_subset_of_card_le hsub hcard.ge, ht.trans hl.symm⟩

#print axioms checkFactors_sound
#print axioms checkIncreasing_iff
#print axioms checkDivisors_sound


end D5.S3.Arith.ErdosNicolas
