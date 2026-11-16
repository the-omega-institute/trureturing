/- GID: D5/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStripping
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/Cyclic/VerifiedPrimeFactorStripping
   mirror-E: none(waiver:general-monoid-recursion)
   anchors: [mathlib/module/Mathlib.GroupTheory.OrderOfElement]
   utility: none
   digest: Executable prime-support stripping recovers order from a positive returning multiple. -/

import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic

/-! Repeated division follows the classical order algorithm of Sutherland,
18.783 Lecture 8, Section 8.3, Algorithm 8.2. No complexity claim is made. -/

set_option autoImplicit false

namespace PrimeFactorStripping

/-- Remove a supplied factor as long as the reduced exponent still returns to one.
Zero and one are inert factors; the zero exponent is also returned unchanged. -/
def stripFactor {G : Type*} [Monoid G] [DecidableEq G] (x : G) (p m : ℕ) : ℕ :=
  if _h : 1 < p ∧ 0 < m ∧ p ∣ m ∧ x ^ (m / p) = 1 then
    stripFactor x p (m / p)
  else m
termination_by m
decreasing_by exact Nat.div_lt_self _h.2.1 _h.1

/-- Process the supplied list in order, using only power tests and natural arithmetic. -/
def stripFactors {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (P : List ℕ) (m : ℕ) : ℕ :=
  P.foldl (fun n p => stripFactor x p n) m

private theorem stripFactor_run {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (p m : ℕ) (hm : 0 < m) (hxm : x ^ m = 1) :
    let M := stripFactor x p m
    0 < M ∧ (∃ k : ℕ, m = p ^ k * M) ∧ x ^ M = 1 ∧
      (1 < p → ¬ p ∣ M / orderOf x) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    dsimp only
    by_cases hs : 1 < p ∧ 0 < m ∧ p ∣ m ∧ x ^ (m / p) = 1
    · have hlt : m / p < m := Nat.div_lt_self hm hs.1
      have hp0 : 0 < p := by omega
      have hpos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hs.2.2.1) hp0
      obtain ⟨hM, ⟨k, hk⟩, hpow, hstop⟩ := ih (m / p) hlt hpos hs.2.2.2
      rw [stripFactor, dite_eq_left hs]
      refine ⟨hM, ⟨k + 1, ?_⟩, hpow, hstop⟩
      calc
        m = p * (m / p) := (Nat.mul_div_cancel' hs.2.2.1).symm
        _ = p * (p ^ k * stripFactor x p (m / p)) := congrArg (fun n => p * n) hk
        _ = p ^ (k + 1) * stripFactor x p (m / p) := by rw [pow_succ]; ring
    · rw [stripFactor, dite_eq_right hs]
      refine ⟨hm, ⟨0, by simp⟩, hxm, ?_⟩
      intro hp hpq
      have hd : orderOf x ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hxm
      obtain ⟨k, hk⟩ := hpq
      have heq : m = p * (orderOf x * k) := by
        calc
          m = orderOf x * (m / orderOf x) := (Nat.mul_div_cancel' hd).symm
          _ = p * (orderOf x * k) := by rw [hk]; ring
      apply hs
      refine ⟨hp, hm, ⟨orderOf x * k, heq⟩, ?_⟩
      rw [heq, Nat.mul_div_right _ (by omega : 0 < p), pow_mul,
        pow_orderOf_eq_one, one_pow]

private theorem stripFactors_run {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (P : List ℕ) (m : ℕ) (hm : 0 < m) (hxm : x ^ m = 1) :
    let M := stripFactors x P m
    0 < M ∧ M ∣ m ∧ x ^ M = 1 ∧
      ∀ p ∈ P, 1 < p → ¬ p ∣ M / orderOf x := by
  induction P generalizing m with
  | nil => simp [stripFactors, hm, hxm]
  | cons p P ih =>
    obtain ⟨hn, ⟨k, hk⟩, hxn, hstop⟩ := stripFactor_run x p m hm hxm
    have hnm : stripFactor x p m ∣ m := ⟨p ^ k, by simpa only [Nat.mul_comm] using hk⟩
    obtain ⟨hM, hMn, hxM, hP⟩ := ih (stripFactor x p m) hn hxn
    dsimp only [stripFactors, List.foldl_cons]
    refine ⟨hM, hMn.trans hnm, hxM, ?_⟩
    intro q hq hq1
    rcases List.mem_cons.mp hq with rfl | hq
    · intro hqM
      apply hstop hq1
      have hquot : stripFactors x P (stripFactor x q m) / orderOf x ∣
          stripFactor x q m / orderOf x :=
        (Nat.div_dvd_div_iff_right (orderOf_dvd_iff_pow_eq_one.mpr hxM)
          (orderOf_dvd_iff_pow_eq_one.mpr hxn)).mpr hMn
      exact hqM.trans hquot
    · exact hP q hq hq1

/-- A positive returning multiple and coverage of its original prime divisors suffice.
The list may contain duplicates and arbitrary extra natural numbers. -/
theorem stripFactors_correct {G : Type*} [Monoid G] [DecidableEq G]
    (x : G) (P : List ℕ) (m : ℕ) (hm : 0 < m) (hxm : x ^ m = 1)
    (hcover : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ P) :
    let M := stripFactors x P m
    0 < M ∧ M ∣ m ∧ x ^ M = 1 ∧ M = orderOf x := by
  obtain ⟨hM, hMm, hxM, hstop⟩ := stripFactors_run x P m hm hxm
  dsimp only
  refine ⟨hM, hMm, hxM, ?_⟩
  symm
  apply orderOf_eq_of_pow_and_pow_div_prime hM hxM
  intro p hp hpM hxdiv
  have hd : orderOf x ∣ stripFactors x P m / p :=
    orderOf_dvd_iff_pow_eq_one.mpr hxdiv
  apply hstop p (hcover p hp (hpM.trans hMm)) hp.one_lt
  have hrM : orderOf x ∣ stripFactors x P m := orderOf_dvd_iff_pow_eq_one.mpr hxM
  have hmul : orderOf x * p ∣ stripFactors x P m := by
    simpa only [Nat.mul_comm] using (Nat.dvd_div_iff_mul_dvd hpM).mp hd
  exact (Nat.dvd_div_iff_mul_dvd hrM).mpr (by simpa [Nat.mul_comm] using hmul)

end PrimeFactorStripping
