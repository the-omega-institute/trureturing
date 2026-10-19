/- GID: D5/S3/Arith/Primes/MatharA073759
   generality: G
   mirror-B: D5/B/S3/Arith/Primes/MatharA073759
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Mathar's A073759 conjecture holds for every natural index at least five. -/

/-
proof_shape: prime_value, candidate_mem, candidate_upper, sub_minFac_even, result: bind-only.
Consumers: each of the four private lemmas is used by result.
escape_witness: none.
admission_basis: open-problem-resolution (#18937; Proved).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19044.
Direct frozen dependencies: none (every declaration); only pinned Mathlib is imported.
Definitions: a, A046666, A046667 and claim express the OEIS formulas quoted below.
Utility: an unbounded symbolic proof, with no finite-instance or enumeration assertion.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

namespace D5.S3.Arith.Primes.MatharA073759

/-- OEIS A073759: "Largest number < n that is neither a divisor of nor relatively prime to n,
or 0 if no such number exists." (offset 1). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Ico 1 n).filter (fun m => ¬ m ∣ n ∧ ¬ Nat.Coprime m n)).sup id

/-- OEIS A046666: "a(n) = n - (smallest prime dividing n)." (offset 2). -/
def A046666 (n : ℕ) : ℕ := n - n.minFac

/-- OEIS A046667: "a(n) = A046666(n)/2." (offset 2). -/
def A046667 (n : ℕ) : ℕ := A046666 n / 2

/-- OEIS A073759 (R. J. Mathar), conjecture: "a(n) = 2*A046667(n) if n>=5." -/
def claim : Prop := ∀ n : ℕ, 5 ≤ n → a n = 2 * A046667 n


end D5.S3.Arith.Primes.MatharA073759

namespace D5.S3.Arith.Primes.MatharA073759

private lemma prime_value {n : ℕ} (hn : n.Prime) : a n = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply Finset.sup_le
  intro k hk
  obtain ⟨hkI, _, hkn⟩ := Finset.mem_filter.mp hk
  obtain ⟨hk1, hknlt⟩ := Finset.mem_Ico.mp hkI
  exfalso
  apply hkn
  exact (hn.coprime_iff_not_dvd.mpr
    (Nat.not_dvd_of_pos_of_lt (Nat.zero_lt_of_lt hk1) hknlt)).symm

private lemma candidate_mem {n : ℕ} (hn : 5 ≤ n) (hc : ¬ n.Prime) :
    n - n.minFac ∈ (Finset.Ico 1 n).filter (fun m => ¬ m ∣ n ∧ ¬ Nat.Coprime m n) := by
  have hp := Nat.minFac_prime (by omega : n ≠ 1)
  have hp2 := hp.two_le
  have hpn := Nat.minFac_le (Nat.zero_lt_of_lt hn)
  have hd := Nat.minFac_dvd n
  have hsq := Nat.minFac_sq_le_self (Nat.zero_lt_of_lt hn) hc
  have hbig : 2 * n.minFac < n := by
    by_cases h2 : n.minFac = 2
    · omega
    have h3 : 3 ≤ n.minFac := by omega
    have hmul := Nat.mul_le_mul_left n.minFac h3
    have hmuln : n.minFac * 3 ≤ n :=
      hmul.trans (by simpa [Nat.pow_two] using hsq)
    omega
  have hsub : n.minFac < n - n.minFac := by omega
  have hgcd : Nat.gcd (n - n.minFac) n = n.minFac := by
    rw [Nat.gcd_self_sub_left hpn, Nat.gcd_eq_left hd]
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_, ?_⟩
  · intro hdiv
    have heq := Nat.gcd_eq_left hdiv
    omega
  · intro hcop
    have heq : Nat.gcd (n - n.minFac) n = 1 := hcop
    omega

private lemma candidate_upper {n k : ℕ} (hk : k < n) (hc : ¬ Nat.Coprime k n) :
    k ≤ n - n.minFac := by
  obtain ⟨r, hr, hrk, hrn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
  have hrsub : r ∣ n - k := Nat.dvd_sub hrn hrk
  have hrl : r ≤ n - k := Nat.le_of_dvd (Nat.zero_lt_sub_of_lt hk) hrsub
  have hmin : n.minFac ≤ r := Nat.minFac_le_of_dvd hr.two_le hrn
  omega

private lemma sub_minFac_even {n : ℕ} (hn : 2 ≤ n) : 2 ∣ n - n.minFac := by
  by_cases he : 2 ∣ n
  · rw [(Nat.minFac_eq_two_iff n).mpr he]
    exact Nat.dvd_sub he (dvd_refl 2)
  · have hp := Nat.minFac_prime (Ne.symm (Nat.ne_of_lt hn))
    have hp2 : n.minFac ≠ 2 := by
      intro h
      exact he ((Nat.minFac_eq_two_iff n).mp h)
    have hodd := hp.eq_two_or_odd.resolve_left hp2
    have hple := Nat.minFac_le (Nat.zero_lt_of_lt hn)
    omega

theorem result : claim := by
  intro n hn
  have hval : a n = n - n.minFac := by
    by_cases hp : n.Prime
    · rw [prime_value hp, hp.minFac_eq, Nat.sub_self]
    · apply le_antisymm
      · apply Finset.sup_le
        intro k hk
        obtain ⟨hI, _, hnc⟩ := Finset.mem_filter.mp hk
        exact candidate_upper (Finset.mem_Ico.mp hI).2 hnc
      · exact Finset.le_sup (f := id) (candidate_mem hn hp)
  rw [hval]
  exact (Nat.mul_div_cancel' (sub_minFac_even (Nat.le_of_add_left_le hn))).symm

end D5.S3.Arith.Primes.MatharA073759
