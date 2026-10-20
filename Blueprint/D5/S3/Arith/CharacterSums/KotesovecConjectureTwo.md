# Kotěšovec's second monomial-sum conjecture

## Abstract

Every biquadratefree powerful number, and each of 243, 972, 1944 and 2401, has nonzero complete monomial sums at every degree at least two.

**Definition 1.1 (The second conjecture).**

$$claimTwo = ((\forall m: \mathbb{N}, (\operatorname{InA338325}\left(m\right)) \Rightarrow (\operatorname{InA368959}\left(m\right))) \land ((\operatorname{InA368959}\left(243\right)) \land ((\operatorname{InA368959}\left(972\right)) \land ((\operatorname{InA368959}\left(1944\right)) \land (\operatorname{InA368959}\left(2401\right))))))$$

*Formalization.* `D5/S3/Arith/CharacterSums/KotesovecConjectureTwo.claimTwo` (`✓ std3`).

*Citation.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

OEIS A368959, COMMENTS: "Conjecture 2: This sequence contains all the terms from A338325, plus 243, 972, 1944, 2401, ..." The ellipsis is not an exhaustive enumeration: the proposition asserts the inclusion and the four named terms. The predicates InA338325 and InA368959 are those defined in KotesovecConjectureOne.

**Theorem 1.2 (The family and four further moduli).**

$$(\forall m: \mathbb{N}, (\operatorname{InA338325}\left(m\right)) \Rightarrow (\operatorname{InA368959}\left(m\right))) \land ((\operatorname{InA368959}\left(243\right)) \land ((\operatorname{InA368959}\left(972\right)) \land ((\operatorname{InA368959}\left(1944\right)) \land (\operatorname{InA368959}\left(2401\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/CharacterSums/KotesovecConjectureTwo.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Václav Kotěšovec (2024). *OEIS A368959: nonzero complete monomial exponential sums*. URL: <https://oeis.org/A368959>.

*Commentary.*

Nonvanishing for injective additive characters holds for prime squares, prime cubes, 243 and 2401. Chinese remaindering preserves it for coprime products. The products 972=4*243 and 1944=8*243 yield the remaining two moduli, and the standard additive character gives the exponential sums of A368959.

## References

- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureTwo.claimTwo`
- Truth anchor: `D5/S3/Arith/CharacterSums/KotesovecConjectureTwo.result`
- Dependency: [D5/S3/Arith/CharacterSums/KotesovecConjectureOne](KotesovecConjectureOne.md)
