# The Sole Prime among the Integral Eighth-Quadratic Values

## Abstract

The positive integral values of k(k+9)/8 have 17 as their only prime.

**Definition 1.1 (Integral values with positive parameter).**

$$\forall a \in \mathrm{Nat},\; (\operatorname{IsTerm}\left(a\right)) \Leftrightarrow (\exists k \in \mathrm{Nat},\; (0 < k) \land (8 \cdot a = k \cdot (k + 9)))$$

*Formalization.* `D5/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime.IsTerm` (`✓ std3`).

*Citation.* Vladimir Joseph Stephan Orlovsky; Bill McEachen (2009). *OEIS A165719, Integers of the form k*(k+9)/8*. URL: <https://oeis.org/A165719>.

*Commentary.*

A natural a is a term precisely when a positive natural k satisfies 8a=k(k+9). This equation selects the integral values without rounding.

**Theorem 1.2 (The parameter classification and the sole prime).**

$$(\forall k \in \mathrm{Nat},\; (0 < k) \Rightarrow ((8 \mid k \cdot (k + 9)) \Leftrightarrow (\exists m \in \mathrm{Nat},\; (0 < m) \land ((k + 1 = 8 \cdot m) \lor (k = 8 \cdot m))))) \land \left(((\operatorname{IsTerm}\left(17\right)) \land (\operatorname{Prime}\left(17\right))) \land (\forall a \in \mathrm{Nat},\; (\operatorname{IsTerm}\left(a\right)) \Rightarrow ((a \ne 17) \Rightarrow ((1 < a) \land (\neg \operatorname{Prime}\left(a\right)))))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a165719-eighth-quadratic-integrality-and-sole-prime` (proved) by `D5/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a165719-eighth-quadratic-integrality-and-sole-prime","declaration_gid":"D5/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Vladimir Joseph Stephan Orlovsky; Bill McEachen (2009). *OEIS A165719, Integers of the form k*(k+9)/8*. URL: <https://oeis.org/A165719>.

*Commentary.*

For every positive k, integrality is equivalent to k+1=8m or k=8m for a positive natural m. The value 17 occurs at k=8 and is prime. Every other term is greater than one and is not prime. Reduction modulo eight leaves only residues seven and zero. In the first case a=k(m+1), with both factors greater than one. In the second case a=m(8m+9); m=1 gives 17, and every larger m gives a composite value.

## References

- Truth anchor: `D5/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime.IsTerm`
- Truth anchor: `D5/S3/PrimeForms/OrlovskyEighthQuadraticSolePrime.result`
