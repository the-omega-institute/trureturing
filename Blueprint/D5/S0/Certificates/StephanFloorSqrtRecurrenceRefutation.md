# The OEIS A104863 Floor-Square-Root Recurrence Conjecture

## Abstract

The term at n = 17 refutes the conjectured recurrence for OEIS A104863.

**Definition 1.1 (The A104863 sequence).**

$$(\operatorname{a}\left(1\right) = 10) \land \left((\operatorname{a}\left(2\right) = 30) \land (\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n + 3\right) = Nat.sqrt\left((\operatorname{a}\left(n + 2\right))^{2} + (\operatorname{a}\left(n + 1\right))^{2}\right))\right)$$

*Formalization.* `D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.a` (`✓ std3`).

*Citation.* Zak Seidov; Ralf Stephan (2005). *OEIS A104863, a(n) = floor(sqrt(a(n-1)^2 + a(n-2)^2)), a(1)=10, a(2)=30*. URL: <https://oeis.org/A104863>.

*Commentary.*

The displayed equations give a(1) = 10, a(2) = 30, and the recursive value at n+3 for every natural n. Nat.sqrt is the greatest natural number whose square does not exceed its argument. Lean makes the recursive definition total with the sentinel value a(0) = 0.

**Definition 1.2 (Stephan's recurrence conjecture).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; 17 \le n \Rightarrow \operatorname{a}\left(n\right) = \operatorname{a}\left(n - 2\right) + \operatorname{a}\left(n - 4\right) + 1)$$

*Formalization.* `D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.claim` (`✓ std3`).

*Citation.* Zak Seidov; Ralf Stephan (2005). *OEIS A104863, a(n) = floor(sqrt(a(n-1)^2 + a(n-2)^2)), a(1)=10, a(2)=30*. URL: <https://oeis.org/A104863>.

*Commentary.*

For every natural n at least 17, the conjecture equates a(n) with a(n-2) + a(n-4) + 1. Both subtractions are truncated natural subtractions, as in the Lean definition.

**Theorem 1.3 (The conjecture fails at n = 17).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a104863-floor-sqrt-recurrence-refutation` (refuted) by `D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a104863-floor-sqrt-recurrence-refutation","declaration_gid":"D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Zak Seidov; Ralf Stephan (2005). *OEIS A104863, a(n) = floor(sqrt(a(n-1)^2 + a(n-2)^2)), a(1)=10, a(2)=30*. URL: <https://oeis.org/A104863>.

*Commentary.*

At n = 17, the defining recurrence gives a(17) = 935, whereas a(15) + a(13) + 1 = 578 + 358 + 1 = 937, so the claim is false. The sign-corrected reading also fails numerically at n = 33, and the odd and even closed forms fail at m = 16 and m = 19, respectively, as detailed in the dossier.

## References

- Truth anchor: `D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.a`
- Truth anchor: `D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.claim`
- Truth anchor: `D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.result`
