# The OEIS A126762 Least-Witness Exponent-Shift Conjecture

## Abstract

The printed exponent-shift conjecture for OEIS A126762 fails at n = 363.

**Definition 1.1 (The defining congruence for A126762).**

$$\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; (\operatorname{firstCongruence}\left(n, k\right)) \Leftrightarrow ((n < k \land n^{k} \bmod k = n \bmod k))$$

*Formalization.* `D5/S0/Certificates/OrdowskiLeastWitnessRefutation.firstCongruence` (`✓ std3`).

*Citation.* Thomas Ordowski (2018). *OEIS A126762, a(n) is the least k > n such that the remainder when n^k is divided by k is n*. URL: <https://oeis.org/A126762>.

*Commentary.*

For natural numbers n and k, the defining condition requires k to be strictly greater than n and the remainder of n to the power k modulo k to equal the remainder of n modulo k.

**Definition 1.2 (The proposed exponent-shift congruence).**

$$\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; (\operatorname{secondCongruence}\left(n, k\right)) \Leftrightarrow ((n < k \land n^{k - 1} \bmod k = 1 \bmod k))$$

*Formalization.* `D5/S0/Certificates/OrdowskiLeastWitnessRefutation.secondCongruence` (`✓ std3`).

*Citation.* Thomas Ordowski (2018). *OEIS A126762, a(n) is the least k > n such that the remainder when n^k is divided by k is n*. URL: <https://oeis.org/A126762>.

*Commentary.*

The proposed condition keeps k strictly greater than n, changes the exponent to k minus one, and requires remainder one modulo k.

**Definition 1.3 (Ordowski's least-witness conjecture).**

$$\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; 1 \le n \Rightarrow \left(\operatorname{IsLeast}\left(\{j \mid \operatorname{firstCongruence}\left(n, j\right)\}, k\right) \Rightarrow \operatorname{IsLeast}\left(\{j \mid \operatorname{secondCongruence}\left(n, j\right)\}, k\right)\right)$$

*Formalization.* `D5/S0/Certificates/OrdowskiLeastWitnessRefutation.claim` (`✓ std3`).

*Citation.* Thomas Ordowski (2018). *OEIS A126762, a(n) is the least k > n such that the remainder when n^k is divided by k is n*. URL: <https://oeis.org/A126762>.

*Commentary.*

For every positive n, the printed conjecture says that any k least among the witnesses of the defining condition is also least among the witnesses of the exponent-shift condition.

**Theorem 1.4 (The conjecture fails at n = 363).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S0/Certificates/OrdowskiLeastWitnessRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a126762-least-witness-exponent-shift-refutation` (refuted) by `D5/S0/Certificates/OrdowskiLeastWitnessRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a126762-least-witness-exponent-shift-refutation","declaration_gid":"D5/S0/Certificates/OrdowskiLeastWitnessRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Thomas Ordowski (2018). *OEIS A126762, a(n) is the least k > n such that the remainder when n^k is divided by k is n*. URL: <https://oeis.org/A126762>.

*Commentary.*

At n = 363, the remainders of 363 to the powers 364, 365, and 366 modulo 364, 365, and 366 are 1, 333, and 363. Thus 366 is the least witness of the defining condition.

The remainder of 363 to the power 365 modulo 366 is 123 rather than 1, so 366 is not a witness of the proposed condition. This refutes only the printed conjecture. It makes no claim about a corrected sequence or the second least witness 367.

## References

- Truth anchor: `D5/S0/Certificates/OrdowskiLeastWitnessRefutation.claim`
- Truth anchor: `D5/S0/Certificates/OrdowskiLeastWitnessRefutation.firstCongruence`
- Truth anchor: `D5/S0/Certificates/OrdowskiLeastWitnessRefutation.result`
- Truth anchor: `D5/S0/Certificates/OrdowskiLeastWitnessRefutation.secondCongruence`
