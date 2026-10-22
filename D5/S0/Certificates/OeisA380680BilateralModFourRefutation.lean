/- GID: D5/S0/Certificates/OeisA380680BilateralModFourRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/OeisA380680BilateralModFourRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/OeisA380680BilateralModFourRefutation.claim; result=D5/S0/Certificates/OeisA380680BilateralModFourRefutation.result; claim=D5/S0/Certificates/OeisA380680BilateralModFourRefutation.claim
   digest: Hanna's square-residue conjecture for OEIS A380680 fails at n = 1. -/

/-
result:
  proof_shape: bind-only; singleton-sum, coefficient, inverse and cast normalization.
  escape_witness: none
  admission_basis: open-problem-resolution (#18667; Refuted)
  Direct frozen dependencies: none.
The source definitions a and claim have proof_shape: not-applicable (definitions).
Their consumer is result. The coefficient and claim bodies are those of #18667.
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
-/

import Mathlib.RingTheory.PowerSeries.Inverse

set_option autoImplicit false

namespace D5.S0.Certificates.OeisA380680BilateralModFourRefutation

open PowerSeries

/-- The coefficient of `x^m` in `A(x) = ∑_{n ∈ ℤ} x^(n^2) (2 - x^n)^n / (1 - 2 x^n)^n`. The term `n = 0` is `1`,
and the term `-n` equals the term `n` (the entry's comment and formula (2)), so
`A(x) = 1 + 2 ∑_{n ≥ 1} x^(n^2) (2 - x^n)^n (1 - 2 x^n)^(-n)`; only `n ≤ m` contribute to `x^m`. -/
noncomputable def a (m : ℕ) : ℚ :=
  coeff m (1 + 2 * ∑ n ∈ Finset.Icc 1 m,
    (X : ℚ⟦X⟧) ^ (n ^ 2) * (2 - X ^ n) ^ n * ((1 - 2 * X ^ n) ^ n)⁻¹)

/-- A380680 ("Conjecture: for n > 0, a(n) == 2 (mod 4) iff n is a square, and a(n) is divisible by 4 when n is
nonsquare"). -/
def claim : Prop :=
  ∀ n : ℕ, 0 < n → ∃ z : ℤ, (z : ℚ) = a n ∧ ((z % 4 = 2 ↔ IsSquare n) ∧ (¬ IsSquare n → (4 : ℤ) ∣ z))

/-- The square index one has coefficient four, contradicting the required residue two. -/
theorem result : ¬ claim := by
  have ha : a 1 = 4 := by
    norm_num [a, Finset.Icc_self, PowerSeries.coeff_one_mul,
      PowerSeries.constantCoeff_inv, map_ofNat]
  intro h
  obtain ⟨z, hz, hmod, _⟩ := h 1 Nat.zero_lt_one
  have hz4 : z = 4 := Rat.intCast_inj.mp (hz.trans ha)
  have hm := hmod.mpr (IsSquare.one : IsSquare (1 : ℕ))
  norm_num [hz4] at hm

end D5.S0.Certificates.OeisA380680BilateralModFourRefutation
