# Twin-Prime Averages at 6n and 12n

## Abstract

Twin-prime pairs centered at both 6n and 12n force n to be one or divisible by five.

**Definition 1.1 (Membership in A177680).**

$$\forall n \in {\mathbb N},\; IsMember\left(n\right) \Leftrightarrow (1 \le n \land \left(Prime\left(6 \cdot n - 1\right) \land \left(Prime\left(6 \cdot n + 1\right) \land \left(Prime\left(12 \cdot n - 1\right) \land Prime\left(12 \cdot n + 1\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive.IsMember` (`✓ std3`).

*Citation.* Juri-Stepan Gerasimov (2010). *OEIS A177680, Numbers n such that 6n and 12n are both the average of twin prime pairs*. URL: <https://oeis.org/A177680>.

*Commentary.*

A positive natural number n belongs to the sequence exactly when each number one below and one above 6n and 12n is prime. The minus sign denotes natural subtraction; because n is at least one, it agrees here with ordinary subtraction.

**Theorem 1.2 (Dale's divisibility conjecture).**

$$\forall n \in {\mathbb N},\; IsMember\left(n\right) \Rightarrow \left(n = 1 \lor 5 \mid n\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive.dale_a177680` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a177680-twin-prime-average-multiple-of-five` (proved) by `D5/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive.dale_a177680`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a177680-twin-prime-average-multiple-of-five","declaration_gid":"D5/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive.dale_a177680","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

Classify n by its residue modulo five. Each nonzero residue selects one of 6n-1, 6n+1, 12n-1, and 12n+1 that is divisible by five. Its primality collapses that value to five: residue one gives n=1, while residues two, three, and four are impossible. The converse is false at n=10.

## References

- Truth anchor: `D5/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive.IsMember`
- Truth anchor: `D5/S3/Arith/Congruence/DaleTwinPrimeAverageMultipleOfFive.dale_a177680`
