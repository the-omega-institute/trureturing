/- GID: D5/S0/Certificates/SabbaPolarizationTransferRefutation
   generality: I
   mirror-B: D5/B/S0/Certificates/SabbaPolarizationTransferRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S0/Certificates/SabbaPolarizationTransferRefutation.claim; result=D5/S0/Certificates/SabbaPolarizationTransferRefutation.result; claim=D5/S0/Certificates/SabbaPolarizationTransferRefutation.claim
   digest: Refutes the conjecture of OEIS A362534 at n = 19: the numerator 215955 of the adiabatic bound g(19) differs from the denominator 43191 of f(19)/g(19). -/

/-
proof_shape: result: bind-only (evaluation of the two definitions at n = 19 by `decide` on two
  binomial coefficients, `norm_num`, and the pinned `Rat.num_div_eq_of_coprime`,
  `Rat.den_div_eq_of_coprime`)
escape_witness: null
admission_basis: open-problem-resolution (issue #10062; Refuted)
Direct frozen dependencies: none (pinned Mathlib only)
-/

import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S0.Certificates.SabbaPolarizationTransferRefutation

/-!
OEIS A362534 (Mohamed Sabba, 2023): for polarization transfer in `AX_n` spin-1/2 systems, the
symmetry-constrained bound `f(n)` and the adiabatic bound `g(n)` are
`f(n) = 2^(1-n) n binomial(n-1, n/2)` (`n` even), `2^(1-n) n binomial(n-1, (n-1)/2)` (`n` odd),
`g(n) = 2 (1 - 2^(-n) binomial(n, n/2))` (`n` even), `2 (1 - 2^(-n) binomial(n, (n-1)/2))`
(`n` odd), and the entry conjectures that the numerator of `g(n)` is the denominator of
`f(n)/g(n)`, numerators and denominators taken in lowest terms. At `n = 19`,
`g = 215955/131072` and `f/g = 92378/43191`.
-/

/-- The symmetry-constrained bound `f(n)`. -/
def f (n : ℕ) : ℚ :=
  if n % 2 = 0 then (2 : ℚ) ^ ((1 : ℤ) - n) * n * (n - 1).choose (n / 2)
  else (2 : ℚ) ^ ((1 : ℤ) - n) * n * (n - 1).choose ((n - 1) / 2)

/-- The adiabatic bound `g(n)`. -/
def g (n : ℕ) : ℚ :=
  if n % 2 = 0 then 2 * (1 - (2 : ℚ) ^ (-(n : ℤ)) * n.choose (n / 2))
  else 2 * (1 - (2 : ℚ) ^ (-(n : ℤ)) * n.choose ((n - 1) / 2))

/-- The conjecture of OEIS A362534: for every `n ≥ 1`, the numerator of `g(n)` is the
denominator of `f(n)/g(n)`, both in lowest terms. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → (g n).num = ((f n / g n).den : ℤ)

/-- At `n = 19` the numerator of `g(19)` is `215955` while the denominator of `f(19)/g(19)` is
`43191`. -/
theorem result : ¬ claim := by
  intro h
  have h19 := h 19 (by norm_num)
  have hg : g 19 = 215955 / 131072 := by
    have hc : Nat.choose 19 9 = 92378 := by decide
    simp only [g, hc]
    norm_num
  have hf : f 19 = 230945 / 65536 := by
    have hc : Nat.choose 18 9 = 48620 := by decide
    simp only [f, hc]
    norm_num
  rw [hf, hg] at h19
  have hnum : ((215955 : ℤ) / (131072 : ℤ) : ℚ).num = 215955 :=
    Rat.num_div_eq_of_coprime (by norm_num) (by decide)
  have hden : (((92378 : ℤ) / (43191 : ℤ) : ℚ).den : ℤ) = 43191 :=
    Rat.den_div_eq_of_coprime (by norm_num) (by decide)
  push_cast at hnum hden
  have hq : (230945 / 65536 : ℚ) / (215955 / 131072) = 92378 / 43191 := by norm_num
  rw [hq, hnum, hden] at h19
  norm_num at h19

#print axioms claim
#print axioms result

end D5.S0.Certificates.SabbaPolarizationTransferRefutation
