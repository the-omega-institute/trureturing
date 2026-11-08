/- GID: D5/S0/Certificates/CopelandA131758PolynomialContentRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/CopelandA131758PolynomialContentRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.claim; result=D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.result; claim=D5/S0/Certificates/CopelandA131758PolynomialContentRefutation.claim
   digest: At n=8 the complete coefficient row has content 1, but the proposed count is 2. -/

/-
result: proof_shape: bind-only
escape_witness: none
admission_basis: open-problem-resolution (#23503; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
The source's finite Laguerre sum is inlined in a; no duplicate Laguerre definition is added.
The real-valued genLaguerre at order zero in
D5.S3.Quantum.QuantumChannels.FockAttenuator.FiniteFockBeamSplitterNonExtremality
is its cast correspondence; its S3 owner is not imported by this S0 module.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
The conclusion refutes the joint integer-row existence and positive-index content assertion;
it does not prove global integer-row existence or the infinite parity family.
-/

import Mathlib.Tactic.NormNum
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.NumberTheory.Divisors

namespace D5.S0.Certificates.CopelandA131758PolynomialContentRefutation

open scoped BigOperators

/-- The finite coefficient formula in OEIS A131758. -/
def a (n m : ℕ) : ℚ :=
  (-1 : ℚ) ^ n * (Nat.factorial n : ℚ) *
    ∑ k ∈ Finset.range (m + 1),
      (-1 : ℚ) ^ k * (Nat.choose (n + 1) k : ℚ) * (∑ j ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ j * (Nat.choose n j : ℚ) * (m - k + 1 : ℕ) ^ j /
          (Nat.factorial j : ℚ))

/-- The source polynomial, with coefficients given by its explicit finite formula. -/
noncomputable def P (n : ℕ) : Polynomial ℚ :=
  ∑ m ∈ Finset.range (n + 1), Polynomial.monomial m (a n m)

/-- An integer realization of the complete row, including its degree-n coefficient. -/
def IsSourceRow (n : ℕ) (row : Fin (n + 1) → ℤ) : Prop :=
  ∀ m : Fin (n + 1), (row m : ℚ) = a n m.val

/-- Nonnegative gcd of all absolute integer coefficients. -/
def rowContent {n : ℕ} (row : Fin (n + 1) → ℤ) : ℕ :=
  Finset.univ.gcd (fun m => (row m).natAbs)

/-- A038548: positive divisors at most the square root, expressed without a square root. -/
def D (n : ℕ) : ℕ :=
  (n.divisors.filter (fun d => d * d ≤ n)).card

/-- Integer rows exist, and every positive-index row has the content conjectured by Copeland. -/
def claim : Prop :=
  (∀ n : ℕ, ∃ row : Fin (n + 1) → ℤ, IsSourceRow n row) ∧
    ∀ n : ℕ, 1 ≤ n → ∀ row : Fin (n + 1) → ℤ,
      IsSourceRow n row → rowContent row = D n

end D5.S0.Certificates.CopelandA131758PolynomialContentRefutation

namespace D5.S0.Certificates.CopelandA131758PolynomialContentRefutation

theorem result : ¬ claim := by
  intro h
  obtain ⟨row, hrow⟩ := h.1 8
  have h0 : row ⟨0, by decide⟩ = 6209 := by
    have hx := hrow ⟨0, by decide⟩
    norm_num [a, Finset.sum_range_succ, Nat.choose, Nat.factorial] at hx
    exact_mod_cast hx
  have h1 : row ⟨1, by decide⟩ = -41417 := by
    have hx := hrow ⟨1, by decide⟩
    norm_num [a, Finset.sum_range_succ, Nat.choose, Nat.factorial] at hx
    exact_mod_cast hx
  have hd0 : rowContent row ∣ (row ⟨0, by decide⟩).natAbs :=
    Finset.gcd_dvd (Finset.mem_univ _)
  have hd1 : rowContent row ∣ (row ⟨1, by decide⟩).natAbs :=
    Finset.gcd_dvd (Finset.mem_univ _)
  have hc : rowContent row = 1 := by
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 6209 41417 by decide +kernel)
    · rw [h0] at hd0
      exact hd0
    · rw [h1] at hd1
      exact hd1
  have hd : D 8 = 2 := by exact Nat.two_eq_digitChar.mp rfl
  have hp := h.2 8 (by decide) row hrow
  omega


end D5.S0.Certificates.CopelandA131758PolynomialContentRefutation
