# Normalization of weak shuffle products

## Abstract

Mammez's weak shuffle normalization conjecture holds for every alphabet.

Mammez, Weak stuffle algebras, Proposition 3.9 and Conjecture 3.10, defines a weak shuffle product by the displayed two-branch recursion. The source says: “Proposition [3.9] is still true for any countable alphabet.” The theorem below proves the same normalization for every alphabet; the word carrier is a finitely supported function on lists.

**Definition 1.1 (Finitely supported word coefficients).**

$$\forall X \in Type,\; \forall K \in Type,\; [Zero\left(K\right)] KX\left(X, K\right) = Finsupp\left(List\left(X\right), K\right)$$

*Formalization.* `D5/S1/Words/WeakShuffleNormalization.KX` (`✓ std3`).

*Citation.* C. Mammez (2022). *Weak stuffle algebras*. DOI: [10.24330/ieja.1060709](https://doi.org/10.24330/ieja.1060709). URL: <https://arxiv.org/abs/2003.09142>.

*Commentary.*

KX X K is the finitely supported K-valued function on List X, with the implicit Zero K instance used by the Finsupp carrier.

**Definition 1.2 (Weak shuffle recursion on words).**

$$\forall X \in Type,\; \forall K \in Type,\; [Field\left(K\right)] \forall f1 \in X \to \left(X \to K\right),\; \forall f2 \in X \to \left(X \to K\right),\; \forall u \in List\left(X\right),\; \forall v \in List\left(X\right),\; wsWord\left(f1, f2, u, v\right) = \operatorname{match} u, v \operatorname{with} \begin{aligned}| [], v \mapsto \operatorname{Finsupp.single}\left(v, 1\right)\\| u, [] \mapsto \operatorname{Finsupp.single}\left(u, 1\right)\\| \operatorname{List.cons}\left(a, u\right), \operatorname{List.cons}\left(b, v\right) \mapsto f1\left(a, b\right) \cdot \operatorname{Finsupp.mapDomain}\left(\operatorname{List.cons}\left(a\right), wsWord\left(f1, f2, u, \operatorname{List.cons}\left(b, v\right)\right)\right) + f2\left(a, b\right) \cdot \operatorname{Finsupp.mapDomain}\left(\operatorname{List.cons}\left(b\right), wsWord\left(f1, f2, \operatorname{List.cons}\left(a, u\right), v\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Words/WeakShuffleNormalization.wsWord` (`✓ std3`).

*Citation.* C. Mammez (2022). *Weak stuffle algebras*. DOI: [10.24330/ieja.1060709](https://doi.org/10.24330/ieja.1060709). URL: <https://arxiv.org/abs/2003.09142>.

*Commentary.*

The empty-word branches are singleton coefficients. For nonempty words the first coefficient prefixes the left head and recurses on the left tail, while the second coefficient prefixes the right head and recurses on the right tail.

**Definition 1.3 (Bilinear extension of the word product).**

$$\forall X \in Type,\; \forall K \in Type,\; [Field\left(K\right)] \forall f1 \in X \to \left(X \to K\right),\; \forall f2 \in X \to \left(X \to K\right),\; \forall x \in KX\left(X, K\right),\; \forall y \in KX\left(X, K\right),\; wsMul\left(f1, f2, x, y\right) = \operatorname{Finsupp.sum}\left(x, \operatorname{fun} (u: List\left(X\right)) \mapsto \operatorname{fun} (a: K) \mapsto \operatorname{Finsupp.sum}\left(y, \operatorname{fun} (v: List\left(X\right)) \mapsto \operatorname{fun} (b: K) \mapsto a \cdot b \cdot wsWord\left(f1, f2, u, v\right)\right)\right)$$

*Formalization.* `D5/S1/Words/WeakShuffleNormalization.wsMul` (`✓ std3`).

*Citation.* C. Mammez (2022). *Weak stuffle algebras*. DOI: [10.24330/ieja.1060709](https://doi.org/10.24330/ieja.1060709). URL: <https://arxiv.org/abs/2003.09142>.

*Commentary.*

wsMul sums the recursive word product over the finite supports of its two Finsupp arguments and multiplies the two coefficients.

**Definition 1.4 (Associative and commutative weak shuffle products).**

$$\forall X \in Type,\; \forall K \in Type,\; [Field\left(K\right)] \forall f1 \in X \to \left(X \to K\right),\; \forall f2 \in X \to \left(X \to K\right),\; IsWeakShuffle\left(f1, f2\right) \Leftrightarrow ((\forall x \in KX\left(X, K\right),\; \forall y \in KX\left(X, K\right),\; wsMul\left(f1, f2, x, y\right) = wsMul\left(f1, f2, y, x\right)) \land (\forall x \in KX\left(X, K\right),\; \forall y \in KX\left(X, K\right),\; \forall z \in KX\left(X, K\right),\; wsMul\left(f1, f2, wsMul\left(f1, f2, x, y\right), z\right) = wsMul\left(f1, f2, x, wsMul\left(f1, f2, y, z\right)\right)))$$

*Formalization.* `D5/S1/Words/WeakShuffleNormalization.IsWeakShuffle` (`✓ std3`).

*Citation.* C. Mammez (2022). *Weak stuffle algebras*. DOI: [10.24330/ieja.1060709](https://doi.org/10.24330/ieja.1060709). URL: <https://arxiv.org/abs/2003.09142>.

*Commentary.*

IsWeakShuffle requires commutativity and associativity of wsMul for all Finsupp inputs.

**Definition 1.5 (First normalized coefficient).**

$$\forall X \in Type,\; \forall K \in Type,\; [Field\left(K\right)] [DecidableEq\left(X\right)] \forall f1 \in X \to \left(X \to K\right),\; \forall a \in X,\; \forall b \in X,\; norm1\left(f1, a, b\right) = \operatorname{if} ((a \ne b) \land (\neg f1\left(a, b\right) \in \{0, 1\})) \operatorname{then} 1 \operatorname{else} \operatorname{if} ((a \ne b) \land (\neg f1\left(b, a\right) \in \{0, 1\})) \operatorname{then} 0 \operatorname{else} f1\left(a, b\right)$$

*Formalization.* `D5/S1/Words/WeakShuffleNormalization.norm1` (`✓ std3`).

*Citation.* C. Mammez (2022). *Weak stuffle algebras*. DOI: [10.24330/ieja.1060709](https://doi.org/10.24330/ieja.1060709). URL: <https://arxiv.org/abs/2003.09142>.

*Commentary.*

The source's first normalization bullet assigns one to an exceptional ordered pair, zero to its reverse exceptional pair, and otherwise keeps the original coefficient.

**Definition 1.6 (Second normalized coefficient).**

$$\forall X \in Type,\; \forall K \in Type,\; [Field\left(K\right)] [DecidableEq\left(X\right)] \forall f1 \in X \to \left(X \to K\right),\; \forall f2 \in X \to \left(X \to K\right),\; \forall a \in X,\; \forall b \in X,\; norm2\left(f1, f2, a, b\right) = \operatorname{if} (a = b) \operatorname{then} f2\left(a, a\right) \operatorname{else} norm1\left(f1, b, a\right)$$

*Formalization.* `D5/S1/Words/WeakShuffleNormalization.norm2` (`✓ std3`).

*Citation.* C. Mammez (2022). *Weak stuffle algebras*. DOI: [10.24330/ieja.1060709](https://doi.org/10.24330/ieja.1060709). URL: <https://arxiv.org/abs/2003.09142>.

*Commentary.*

On the diagonal norm2 keeps f2; off the diagonal it uses the reversed first normalized coefficient, exactly as in the source's bullets.

**Definition 1.7 (Mammez Conjecture 3.10).**

$$\forall K \in Type,\; [Field\left(K\right)] [CharZero\left(K\right)] \forall X \in Type,\; [DecidableEq\left(X\right)] \forall f1 \in X \to \left(X \to K\right),\; \forall f2 \in X \to \left(X \to K\right),\; (IsWeakShuffle\left(f1, f2\right)) \Rightarrow (\exists Phi \in LinearEquiv\left(K, KX\left(X, K\right), KX\left(X, K\right)\right),\; (Phi\left(\operatorname{Finsupp.single}\left([], 1\right)\right) = \operatorname{Finsupp.single}\left([], 1\right)) \land (\forall x \in KX\left(X, K\right),\; \forall y \in KX\left(X, K\right),\; Phi\left(wsMul\left(f1, f2, x, y\right)\right) = wsMul\left(norm1\left(f1\right), norm2\left(f1, f2\right), Phi\left(x\right), Phi\left(y\right)\right)))$$

*Formalization.* `D5/S1/Words/WeakShuffleNormalization.claim` (`✓ std3`).

*Citation.* C. Mammez (2022). *Weak stuffle algebras*. DOI: [10.24330/ieja.1060709](https://doi.org/10.24330/ieja.1060709). URL: <https://arxiv.org/abs/2003.09142>.

*Commentary.*

Verbatim source statement (Conjecture 3.10, printed p. 18): “Proposition [3.9] is still true for any countable alphabet.” The Lean claim quantifies over every alphabet X and expresses the algebra isomorphism as a linear equivalence fixing the empty word.

**Theorem 1.8 (Normalization for every alphabet).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/WeakShuffleNormalization.result` (`✓ std3`). ∎

*Resolves.* `Problems/mammez-2022-weak-shuffle-normalization` (proved) by `D5/S1/Words/WeakShuffleNormalization.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mammez-2022-weak-shuffle-normalization","declaration_gid":"D5/S1/Words/WeakShuffleNormalization.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* C. Mammez (2022). *Weak stuffle algebras*. DOI: [10.24330/ieja.1060709](https://doi.org/10.24330/ieja.1060709). URL: <https://arxiv.org/abs/2003.09142>.

*Commentary.*

The diagonal word rescaling has finite-support exponents. Associativity forces barriers for every exceptional pair, and the path exponent identity makes the rescaling intertwine the two products. Thus the source conjecture holds for every alphabet, including uncountable ones.

## References

- Truth anchor: `D5/S1/Words/WeakShuffleNormalization.IsWeakShuffle`
- Truth anchor: `D5/S1/Words/WeakShuffleNormalization.KX`
- Truth anchor: `D5/S1/Words/WeakShuffleNormalization.claim`
- Truth anchor: `D5/S1/Words/WeakShuffleNormalization.norm1`
- Truth anchor: `D5/S1/Words/WeakShuffleNormalization.norm2`
- Truth anchor: `D5/S1/Words/WeakShuffleNormalization.result`
- Truth anchor: `D5/S1/Words/WeakShuffleNormalization.wsMul`
- Truth anchor: `D5/S1/Words/WeakShuffleNormalization.wsWord`
