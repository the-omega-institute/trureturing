/- GID: D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation
   generality: I
   mirror-B: D5/B/S3/ArithSums/A397436GeneralSupercongruenceRefutation
   mirror-E: none(waiver:exact-kernel-refutation)
   anchors: [mathlib/module/Mathlib.RingTheory.Binomial]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.claim; result=D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.result; claim=D5/S3/ArithSums/A397436GeneralSupercongruenceRefutation.claim
   digest: The unrestricted integer-parameter supercongruence in A397436 Conjecture 3 fails at one factor and prime five. -/

import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

/-! The full signed assertion is refuted by its one-factor positive instance. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Finset

namespace D5.S3.ArithSums.A397436GeneralSupercongruenceRefutation

/-- The inclusive truncated product sum, with generalized binomials on signed integers. -/
noncomputable def U {r : ℕ} (m : Fin r → ℤ) (M n : ℕ) : ℤ :=
  ∑ k ∈ range (M * n + 1), ∏ i : Fin r, Ring.choose (m i * (n : ℤ)) k

/-- The literal same-r universal assertion of OEIS A397436, Conjecture 3. -/
def claim : Prop :=
  ∀ (r : ℕ), 0 < r → ∀ (m : Fin r → ℤ) (M : ℕ), 0 < M →
    ∀ (p : ℕ), Nat.Prime p → 5 ≤ p →
      (p : ℤ) ^ (3 * r) ∣ U m M (p ^ r) - U m M (p ^ (r - 1))

/-- One factor with m(0)=1 gives U(5)=32 and U(1)=2, whereas 125 does not divide 30. -/
theorem result : ¬ claim := by
  intro h
  have hbad := h 1 (by decide) (fun _ => 1) 1 (by decide) 5 (by decide) (by decide)
  have eval (n : ℕ) : U (fun _ : Fin 1 => (1 : ℤ)) 1 n =
      ∑ k ∈ range (n + 1), (Nat.choose n k : ℤ) := by
    simp [U, Ring.choose_natCast]
  norm_num [eval, Finset.sum_range_succ, Nat.choose] at hbad

end D5.S3.ArithSums.A397436GeneralSupercongruenceRefutation
