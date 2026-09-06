# Zaremba Five Finite Front

## Abstract

A fuelled Euclidean checker and a kernel-decided witness table certify the bound five for every denominator from two through 1024.

The quotient trace records the Euclidean quotient and recurses on the strictly smaller remainder. The Boolean checker separately tests coprimality, numerator range, and the digit bound.

**Definition 1.1 (Fuelled Euclidean quotient trace).**

$$\begin{gathered}cfDigitsAux : \mathbb{N} \to \mathbb{N} \to \mathbb{N} \to \operatorname{List}\left(\mathbb{N}\right),\\{}\forall a, q \in \mathbb{N},\ \operatorname{cfDigitsAux}\left(0, a, q\right) = [],\\{}\forall fuel, a, q \in \mathbb{N},\ \operatorname{cfDigitsAux}\left(fuel + 1, a, q\right) = \operatorname{if}\left(q = 0, [], \operatorname{cons}\left(\left\lfloor\frac{a}{q}\right\rfloor, \operatorname{cfDigitsAux}\left(fuel, q, a \bmod q\right)\right)\right).\end{gathered}$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.cfDigitsAux` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The zero-fuel trace is empty. At positive fuel, a zero divisor again gives the empty trace; otherwise the next digit is the natural-number quotient and recursion continues with the divisor and remainder.

**Definition 1.2 (Continued-fraction digits).**

$$\forall a, q \in \mathbb{N},\ \operatorname{cfDigits}\left(a, q\right) = \operatorname{cfDigitsAux}\left(q + 1, a, q\right).$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.cfDigits` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The public quotient trace starts the fuelled recursion with q plus one steps.

**Definition 1.3 (Zaremba witness).**

$$\forall A, a, q \in \mathbb{N},\ \operatorname{ZarembaWitness}\left(A, a, q\right) \iff (\operatorname{Coprime}\left(a, q\right) \land (0 < a \land (a < q \land (\forall d \in \operatorname{cfDigits}\left(a, q\right),\ d \leq A)))).$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.ZarembaWitness` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A witness is coprime to the denominator, lies strictly between zero and the denominator, and has every continued-fraction digit at most A.

**Definition 1.4 (Zaremba Boolean checker).**

$$\forall A, a, q \in \mathbb{N},\ \operatorname{zarembaCheck}\left(A, a, q\right) = ((\operatorname{decide}\left(\operatorname{Coprime}\left(a, q\right)\right)) \land (\operatorname{decide}\left(0 < a\right)) \land (\operatorname{decide}\left(a < q\right)) \land (\operatorname{digitsBounded}\left(A, \operatorname{cfDigits}\left(a, q\right)\right))).$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zarembaCheck` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The checker is the Boolean conjunction of the three arithmetic tests and the bounded-digits test.

**Definition 1.5 (Explicit Zaremba-five witness table).**

$$zarembaFiveWitnessTable : \operatorname{List}\left(\mathbb{N}\right).$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zarembaFiveWitnessTable` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the explicit kernel-decided list of numerator witnesses indexed by q from zero through 1024. Its concrete Lean value has length 1025.

**Definition 1.6 (Zaremba-five numerator lookup).**

$$\forall q \in \mathbb{N},\ \operatorname{zarembaFiveNumerator}\left(q\right) = \operatorname{getD}\left(zarembaFiveWitnessTable, q, 0\right).$$

*Formalization.* `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zarembaFiveNumerator` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The numerator for q is the q-th table entry, with zero as the out-of-range default.

**Theorem 1.7 (Euclidean checker soundness).**

$$(\forall a, q \in \mathbb{N},\ 0 < q \Rightarrow \operatorname{cfDigits}\left(a, q\right) = \operatorname{cons}\left(\left\lfloor\frac{a}{q}\right\rfloor, \operatorname{cfDigitsAux}\left(q, q, a \bmod q\right)\right)) \land\\{}(\forall a, q \in \mathbb{N},\ 0 < q \Rightarrow a \bmod q < q) \land\\{}(\forall A, a, q \in \mathbb{N},\ \operatorname{zarembaCheck}\left(A, a, q\right) = true \Rightarrow \operatorname{ZarembaWitness}\left(A, a, q\right)).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.cfDigits_checker_sound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

These three clauses expose the quotient-remainder recursion, strict remainder descent, and Boolean-to-propositional soundness.

**Theorem 1.8 (Public finite Zaremba certificate).**

$$\operatorname{all}\left(\operatorname{range}\left(1025\right), (q \mapsto \operatorname{decide}\left(q < 2\right) \lor \operatorname{zarembaCheck}\left(5, \operatorname{zarembaFiveNumerator}\left(q\right), q\right))\right) = true.$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zarembaFiveCertificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

This publicly addressable theorem is the named finite escape witness. Lean's kernel evaluates all 1025 rows of the witness table.

**Theorem 1.9 (Zaremba five through 1024).**

$$(\forall q \in \mathbb{N},\ 2 \leq q \Rightarrow q \leq 1024 \Rightarrow \exists a \in \mathbb{N},\ \operatorname{ZarembaWitness}\left(5, a, q\right)) \land\\{}\operatorname{ZarembaWitness}\left(5, 1, 2\right) \land\\{}(\operatorname{ZarembaWitness}\left(5, 17, 54\right) \land \forall a \in \operatorname{Fin}\left(17\right),\ \neg \operatorname{ZarembaWitness}\left(5, \operatorname{val}\left(a\right), 54\right)) \land\\{}\operatorname{cfDigits}\left(17, 54\right) = [0, 3, 5, 1, 2] \land\\{}(\operatorname{cfDigits}\left(1, 6\right) = [0, 6] \land \operatorname{zarembaCheck}\left(5, 1, 6\right) = false).$$

*Proof.* Machine-checked in Lean as `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zaremba_five_upto_certified` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The embedded 1025-row table is checked by Lean's kernel decision procedure. Each admissible denominator selects its table row and checker soundness converts that row into a witness.

The remaining conjuncts pin the smallest denominator, the minimal numerator at 54, two exact quotient traces, and rejection when the digit six exceeds the bound five.

## References

- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.ZarembaWitness`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.cfDigits`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.cfDigitsAux`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.cfDigits_checker_sound`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zarembaCheck`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zarembaFiveCertificate`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zarembaFiveNumerator`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zarembaFiveWitnessTable`
- Truth anchor: `D5/S1/Depth/ContinuedFractions/ZarembaFiveFiniteFront.zaremba_five_upto_certified`
