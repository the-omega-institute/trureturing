# Zaremba Five Finite Front

## Abstract

A fuelled Euclidean checker and a kernel-decided witness table certify the sharp bound five for every denominator from two through 1024.

The quotient trace records the Euclidean quotient and recurses on the strictly smaller remainder. The Boolean checker separately tests coprimality, numerator range, and the digit bound.

**Theorem 1.1 (Euclidean checker soundness).**

$$(\forall a, q \in \mathbb{N},\ 0 < q \Rightarrow \operatorname{cfDigits}\left(a, q\right) = \operatorname{cons}\left(\frac{a}{q}, \operatorname{cfDigitsAux}\left(q, q, a \bmod q\right)\right)) \land\\{}(\forall a, q \in \mathbb{N},\ 0 < q \Rightarrow a \bmod q < q) \land\\{}(\forall A, a, q \in \mathbb{N},\ \operatorname{zarembaCheck}\left(A, a, q\right) = true \Rightarrow \operatorname{ZarembaWitness}\left(A, a, q\right)).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.cfDigits_checker_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These three clauses expose the quotient-remainder recursion, strict remainder descent, and Boolean-to-propositional soundness.

**Theorem 1.2 (Public finite Zaremba certificate).**

$$\operatorname{all}\left(\operatorname{range}\left(1025\right), (q \mapsto \operatorname{decide}\left(q < 2\right) \lor \operatorname{zarembaCheck}\left(5, \operatorname{zarembaFiveNumerator}\left(q\right), q\right))\right) = true.$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zarembaFiveCertificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This publicly addressable theorem is the named finite escape witness. Lean's kernel evaluates all 1025 rows of the witness table.

**Theorem 1.3 (Zaremba five through 1024).**

$$(\forall q \in \mathbb{N},\ 2 \leq q \Rightarrow q \leq 1024 \Rightarrow \exists a \in \mathbb{N},\ \operatorname{ZarembaWitness}\left(5, a, q\right)) \land\\{}\operatorname{ZarembaWitness}\left(5, 1, 2\right) \land\\{}(\operatorname{ZarembaWitness}\left(5, 17, 54\right) \land \forall a \in \operatorname{Fin}\left(17\right),\ \neg \operatorname{ZarembaWitness}\left(5, a, 54\right)) \land\\{}\operatorname{cfDigits}\left(17, 54\right) = [0, 3, 5, 1, 2] \land\\{}(\operatorname{cfDigits}\left(1, 6\right) = [0, 6] \land \operatorname{zarembaCheck}\left(5, 1, 6\right) = false).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zaremba_five_upto_certified` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The embedded 1025-row table is checked by Lean's kernel decision procedure. Each admissible denominator selects its table row and checker soundness converts that row into a witness.

The remaining conjuncts pin the smallest denominator, the minimal numerator at 54, two exact quotient traces, and rejection when the digit six exceeds the bound five.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.cfDigits_checker_sound`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zarembaFiveCertificate`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zaremba_five_upto_certified`
