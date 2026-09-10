# Non-Squashing Parity and a Paperfold Difference

## Abstract

The signed parity of distinct non-squashing partitions equals the adjacent difference of A073089.

Let B(n) be the cardinality of nonsquashingDistinctPartitions(n), the direct finite family in NonsquashingCounting. Let c(n) denote paperfoldVariant(n). All indices are natural numbers. The final equality is in the integers; B(n) mod 2 is computed in the naturals before casting. No finite cutoff is used.

**Definition 1.1 (The independent paperfold recurrence).**

$$\forall n: \mathbb{N}, \operatorname{c}\left(n\right) = \operatorname{ite}\left(n \leq 1, 0, \operatorname{ite}\left(n \bmod 4 = 0, 1, \operatorname{ite}\left(n \bmod 4 = 2, 0, \operatorname{ite}\left(n \bmod 8 = 3, 1, \operatorname{ite}\left(n \bmod 8 = 7, 0, \operatorname{ite}\left(n \bmod 16 = 5, 1, \operatorname{ite}\left(n \bmod 16 = 13, 0, \operatorname{c}\left(\left\lfloor\frac{n + 1}{2}\right\rfloor\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S1/Recurrence/Partitions/NonsquashingPaperfold.paperfoldVariant` (`✓ std3`).

*Citation.* OEIS Foundation Inc.; Alan Michael Gómez Calderón (2025). *A110037 signed non-squashing partition parity and its paperfold difference conjecture*. URL: <https://oeis.org/A110037>.

*Commentary.*

This is OEIS A073089's branch recurrence. The helper ite selects its second argument when the condition holds and its third otherwise. At indices zero and one the value is zero; zero only totalizes the source's offset-one sequence. The remaining recursive branch halves n+1 and strictly decreases n. It does not use B or the desired difference identity.

**Definition 1.2 (The eight parity conditions).**

$$\begin{aligned}\operatorname{Parity}\left(F\right) \iff\\(\forall m: \mathbb{N}, 0 < m \Rightarrow \operatorname{F}\left(2 \cdot m + 1\right) \bmod 2 = \left(\operatorname{F}\left(2 \cdot m + 0\right) \bmod 2 + 1\right) \bmod 2)\\\land (\forall m: \mathbb{N},  \operatorname{F}\left(8 \cdot m + 2\right) \bmod 2 = 1)\\\land (\forall m: \mathbb{N},  \operatorname{F}\left(8 \cdot m + 6\right) \bmod 2 = 0)\\\land (\forall m: \mathbb{N},  \operatorname{F}\left(16 \cdot m + 4\right) \bmod 2 = 0)\\\land (\forall m: \mathbb{N},  \operatorname{F}\left(16 \cdot m + 12\right) \bmod 2 = 1)\\\land (\forall m: \mathbb{N}, 0 < m \Rightarrow \operatorname{F}\left(16 \cdot m + 0\right) \bmod 2 = \operatorname{F}\left(8 \cdot m + 0\right) \bmod 2)\\\land (\forall m: \mathbb{N},  \operatorname{F}\left(32 \cdot m + 8\right) \bmod 2 = 0)\\\land (\forall m: \mathbb{N},  \operatorname{F}\left(32 \cdot m + 24\right) \bmod 2 = 1)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/Partitions/NonsquashingPaperfold.SloaneSellersParity` (`✓ std3`).

*Citation.* N. J. A. Sloane; James A. Sellers (2003). *On Non-Squashing Partitions*. DOI: [10.48550/arXiv.math/0312418](https://doi.org/10.48550/arXiv.math/0312418).

*Commentary.*

For any natural-valued sequence F, Parity(F) denotes these eight quantified conditions. Every unqualified m ranges over all natural numbers; the odd and sixteen-zero clauses require m>0. The two thirty-two clauses include m=0.

**Theorem 1.3 (The conditions hold for the direct count).**

$$\operatorname{Parity}\left(B\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/NonsquashingPaperfold.sloane_sellers_parity` (`✓ std3`). ∎

*Citation.* N. J. A. Sloane; James A. Sellers (2003). *On Non-Squashing Partitions*. DOI: [10.48550/arXiv.math/0312418](https://doi.org/10.48550/arXiv.math/0312418).

*Commentary.*

The maximum-part bijection gives the exact count recurrence. Pairing two successive even steps with the odd increment proves, by induction, B(4m+2) mod 2=(m+1) mod 2. One more even step gives B(4m) mod 2=(m+B(2m)) mod 2 for m>0. Substituting the appropriate indices yields all eight clauses, including the small boundaries.

**Theorem 1.4 (The A110037 difference conjecture).**

$$\forall n: \mathbb{N}, 2 \leq n \Rightarrow (0 - 1)^{\left\lfloor\frac{n}{2}\right\rfloor} \cdot (\operatorname{B}\left(n\right) \bmod 2) = \operatorname{c}\left(n\right) - \operatorname{c}\left(n + 1\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/Partitions/NonsquashingPaperfold.signed_nonsquashing_diff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* OEIS Foundation Inc.; Alan Michael Gómez Calderón (2025). *A110037 signed non-squashing partition parity and its paperfold difference conjecture*. URL: <https://oeis.org/A110037>.

*Acknowledgement.* N. J. A. Sloane; James A. Sellers (2003). *On Non-Squashing Partitions*. DOI: [10.48550/arXiv.math/0312418](https://doi.org/10.48550/arXiv.math/0312418).

*Commentary.*

Put f(r)=B(4r) mod 2. The parity clauses give f(2r)=f(r) for positive r, f(4s+1)=0, and f(4s+3)=1. Strong induction, using the independent paperfold branches, proves f(r)+c(4r+1)=1 for every r>0. For n congruent to zero or one modulo four this complement identity gives the difference. For the other two residues the eight-index parity clauses and the c(8s+3), c(8s+7) branches suffice. The sign is positive in the first two residues and negative in the last two. This proves the conjecture credited to Alan Michael Gómez Calderón on August 19, 2025, throughout its stated domain n>=2.

## References

- Truth anchor: `D5/S1/Recurrence/Partitions/NonsquashingPaperfold.SloaneSellersParity`
- Truth anchor: `D5/S1/Recurrence/Partitions/NonsquashingPaperfold.paperfoldVariant`
- Truth anchor: `D5/S1/Recurrence/Partitions/NonsquashingPaperfold.signed_nonsquashing_diff`
- Truth anchor: `D5/S1/Recurrence/Partitions/NonsquashingPaperfold.sloane_sellers_parity`
- Dependency: [D5/S1/Recurrence/Partitions/NonsquashingCounting](NonsquashingCounting.md)
