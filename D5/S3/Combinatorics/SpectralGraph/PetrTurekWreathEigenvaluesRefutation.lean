/- GID: D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.claim; result=D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.result; claim=D5/S3/Combinatorics/SpectralGraph/PetrTurekWreathEigenvaluesRefutation.claim
   digest: The wreath eigenvalues indexed by three and five coincide at fourteen and five. -/

/- Judgement form.
   admission_basis: open-problem-resolution (#19058; Refuted)
   Direct frozen dependencies: none (only pinned Mathlib imports).
   lambdaOne, lam, claim: proof_shape: not-applicable (definitions); escape_witness: none.
   lam_14_5_3: proof_shape: bind-only; escape_witness: none; consumer: result.
   lam_14_5_5: proof_shape: bind-only; escape_witness: none; consumer: result.
   result: proof_shape: bind-only; escape_witness: none.
   The public result is the designated refutation result (`basis=refutes`) and is exempt
   from four-slot escape registration (CLAUDE.md §3.9).
   The formulas are those of Petr–Turek, arXiv:2501.07269v2, Theorem 1.5, page 3.
   The claim is the coprime restriction of Question 5.5, page 16. Its negation answers
   that question negatively. The matrix-spectrum identification is not formalized here. -/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace D5.S3.Combinatorics.SpectralGraph.PetrTurekWreathEigenvaluesRefutation

open Nat

/-- Theorem 1.5: the value of `λ₁`, with `g = gcd(n,k)`. -/
def lambdaOne (n k : ℕ) : ℚ :=
  if k ∣ n then
    ((n : ℚ) ^ 2 * (n - k)!) / ((k : ℚ) ^ 2 * ((k ! : ℚ) ^ (n / k - 1)) * (n / k)!)
  else
    ((n : ℚ) * (n - k)! * k !) /
      (2 * (Nat.gcd n k : ℚ) * ((Nat.gcd n k)! : ℚ) ^ (n / Nat.gcd n k))

/-- Theorem 1.5: `λ₁` at index one, and the coprime formula for `2 ≤ l ≤ k`. -/
def lam (n k l : ℕ) : ℚ :=
  if l = 1 then lambdaOne n k
  else
    (-1 : ℚ) ^ l * (1 / 2) * l ! * k ! * (n - k - l)! * ((n : ℚ) - 2 * k - 1) * (k.choose l)
      - (1 / 2) * k ! * (n - k)!
      + l ! * ((k + 1).choose (l + 1)) *
          ∑ j ∈ Finset.range (l + 1), (-1 : ℚ) ^ (l - j) * (k - j)! * (n - k - l + j)!

/-- Question 5.5, page 16: “Are the eigenvalues λ₁, λ₂, …, λₖ from Theorem 1.5
all distinct?” Here the parameters are restricted to the coprime case. -/
def claim : Prop :=
  ∀ n k : ℕ, 0 < k → 2 * k < n → Nat.Coprime n k →
    ∀ l ∈ Finset.Icc 1 k, ∀ l' ∈ Finset.Icc 1 k, l ≠ l' → lam n k l ≠ lam n k l'

private theorem lam_14_5_3 : lam 14 5 3 = 17107200 := by
  norm_num [lam, lambdaOne, Nat.factorial, Finset.sum_range_succ, Nat.choose]

private theorem lam_14_5_5 : lam 14 5 5 = 17107200 := by
  norm_num [lam, lambdaOne, Nat.factorial, Finset.sum_range_succ, Nat.choose]

/-- The indices three and five give the same value at `(n,k) = (14,5)`. -/
theorem result : ¬ claim := by
  intro h
  have hne := h 14 5 (by norm_num) (by norm_num)
    (by norm_num [Nat.Coprime, Nat.gcd])
    3 (by norm_num) 5 (by norm_num) (by norm_num)
  exact hne (lam_14_5_3.trans lam_14_5_5.symm)

end D5.S3.Combinatorics.SpectralGraph.PetrTurekWreathEigenvaluesRefutation
