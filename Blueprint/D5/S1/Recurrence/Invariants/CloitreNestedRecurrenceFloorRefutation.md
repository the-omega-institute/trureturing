# The OEIS A076502 Nested-Recurrence Floor-Offset Conjecture

## Abstract

Cloitre's floor-offset conjecture for A076502 fails at n = 1167.

**Definition 1.1 (The nested recurrence).**

$$\begin{aligned}\operatorname{a}\left(0\right) = 0\\\operatorname{a}\left(1\right) = 1\\\forall n \in \mathrm{Nat},\; \operatorname{a}\left(n + 2\right) = n + 2 - \operatorname{a}\left(\operatorname{min}\left(n + 2 - \operatorname{a}\left(\operatorname{min}\left(n + 2 - \operatorname{a}\left(n + 1\right), n + 1\right)\right), n + 1\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.a` (`✓ std3`).

*Citation.* Benoit Cloitre (2002). *OEIS A076502, a(1)=1, a(n)=n-a(n-a(n-a(n-1)))*. URL: <https://oeis.org/A076502>.

*Commentary.*

The value a(0)=0 is a sentinel outside Cloitre's offset-one sequence. The two minima keep each recursive index at most n+1. The literal recurrence below shows that both minima select their first arguments.

**Theorem 1.2 (The literal Cloitre recurrence).**

$$\forall n \in \mathrm{Nat},\; 2 \le n \Rightarrow \operatorname{a}\left(n\right) = n - \operatorname{a}\left(n - \operatorname{a}\left(n - \operatorname{a}\left(n - 1\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.a_succ` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n at least two, the bounds 1 <= a(k) <= k make the two clamped indices strictly smaller than n. Thus the total sequence obeys the nested recurrence printed for A076502.

**Theorem 1.3 (The positive cubic root).**

$$\exists! x \in \mathrm{Real}, (0 < x \land x^{3} - x^{2} + 2 \cdot x - 1 = 0)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.cubic_positiveRoot_existsUnique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The polynomial is negative at zero and positive at one. It is strictly increasing because, for x<y, twice its divided difference is x^2+y^2+(x+y-1)^2+3, which is positive.

**Definition 1.4 (Cloitre's cubic constant).**

$$c = Classical.choose\left(cubic_positiveRoot_existsUnique\right)$$

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.c` (`✓ std3`).

*Citation.* Benoit Cloitre (2002). *OEIS A076502, a(1)=1, a(n)=n-a(n-a(n-a(n-1)))*. URL: <https://oeis.org/A076502>.

*Commentary.*

This is the unique positive real root of x^3-x^2+2x-1, numerically 0.5698….

**Definition 1.5 (The bounded-error and floor-offset conjecture).**

$$claim \Leftrightarrow ((\exists M \in \mathrm{Real},\; \forall n \in \mathrm{Nat},\; 1 \le n \Rightarrow \left|(\operatorname{a}\left(n\right): \mathrm{Real}) - c \cdot (n: \mathrm{Real})\right| \le M) \land (\forall n \in \mathrm{Nat},\; 1 \le n \Rightarrow \left(\exists j \in \left\{0, 1, 2\right\},\; (\operatorname{a}\left(n\right): \mathbb{Z}) = \lfloor c \cdot (n: \mathrm{Real}) \rfloor + j\right)))$$

*Formalization.* `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.claim` (`✓ std3`).

*Citation.* Benoit Cloitre (2002). *OEIS A076502, a(1)=1, a(n)=n-a(n-a(n-a(n-1)))*. URL: <https://oeis.org/A076502>.

*Commentary.*

The assertion combines bounded real error with the requirement that every integer difference a(n)-floor(cn) belongs to {0,1,2}.

**Theorem 1.6 (The floor-offset conjecture fails).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a076502-nested-recurrence-floor-refutation` (refuted) by `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a076502-nested-recurrence-floor-refutation","declaration_gid":"D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Benoit Cloitre (2002). *OEIS A076502, a(1)=1, a(n)=n-a(n-a(n-a(n-1)))*. URL: <https://oeis.org/A076502>.

*Commentary.*

At n=1167, the recurrence gives a(1167)=664, while the cubic-root isolation gives floor(1167c)=665. Their difference is -1, outside {0,1,2}, so the second conjunct and hence the conjunction are false.

## References

- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.a`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.a_succ`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.c`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.claim`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.cubic_positiveRoot_existsUnique`
- Truth anchor: `D5/S1/Recurrence/Invariants/CloitreNestedRecurrenceFloorRefutation.result`
