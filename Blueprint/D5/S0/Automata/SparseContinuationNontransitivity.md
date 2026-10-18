# Sparse continuation agreement need not be transitive

## Abstract

A three-word promise has nontransitive agreement on common legal continuations.

## One finite input domain

**Definition 1.1 (The three legal words).**

$$\mathit{promise} = \left\{[2, 0], [3, 1], [4, 0]\right\}$$

*Formalization.* `D5/S0/Automata/SparseContinuationNontransitivity.promise` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Use the five-element alphabet Fin 5, with a, b, x, y, z represented by 0, 1, 2, 3, 4. A word is a List, read from left to right. The displayed set is the coercion of a finite set of three actual words. It is nonempty because it contains xa. Prefixes is the existing set of words with some legal right continuation.

**Definition 1.2 (The legal output labels).**

$$\forall w \in \mathit{promise},\; \operatorname{output}\left(w\right) = \operatorname{ite}\left(\operatorname{val}\left(w\right) = [4, 0], 1, 0\right)$$

*Formalization.* `D5/S0/Automata/SparseContinuationNontransitivity.output` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The output type is Fin 2. The labels of xa and yb are zero and the label of za is one. The output function accepts only a word of the promise subtype; words outside that domain have no prescribed output.

## Compatibility on common legal suffixes

$$
\forall u \in \operatorname{Prefixes}\left(\mathit{promise}\right),\; \forall v \in \operatorname{Prefixes}\left(\mathit{promise}\right),\; \neg(\operatorname{Conflict}\left(\mathit{promise}, \mathit{output}, u, v\right)) \Leftrightarrow \left(\forall w \in \operatorname{List}\left(\operatorname{Fin}\left(5\right)\right),\; \forall h \in \operatorname{append}\left(\operatorname{val}\left(u\right), w\right) \in \mathit{promise},\; \forall k \in \operatorname{append}\left(\operatorname{val}\left(v\right), w\right) \in \mathit{promise},\; \operatorname{output}\left(\operatorname{Subtype}\left(\operatorname{append}\left(\operatorname{val}\left(u\right), w\right), h\right)\right) = \operatorname{output}\left(\operatorname{Subtype}\left(\operatorname{append}\left(\operatorname{val}\left(v\right), w\right), k\right)\right)\right)
$$

For prefixes u and v, agreement means equality of the prescribed outputs for every common legal suffix w. The membership proofs h and k make both output applications well typed. There is no requirement on a suffix legal at only one prefix. This is exactly the negation of the existing Conflict: on distinct prefixes it excludes every unequal-output continuation, and on the diagonal the two legal-word subtype values coincide. No outside-domain rejection value is added.

**Definition 1.3 (The transitivity assertion).**

$$\mathit{claim} = \left(\forall u \in \operatorname{Prefixes}\left(\mathit{promise}\right),\; \forall v \in \operatorname{Prefixes}\left(\mathit{promise}\right),\; \forall t \in \operatorname{Prefixes}\left(\mathit{promise}\right),\; \neg(\operatorname{Conflict}\left(\mathit{promise}, \mathit{output}, u, v\right)) \Rightarrow \left(\neg(\operatorname{Conflict}\left(\mathit{promise}, \mathit{output}, v, t\right)) \Rightarrow \neg(\operatorname{Conflict}\left(\mathit{promise}, \mathit{output}, u, t\right))\right)\right)$$

*Formalization.* `D5/S0/Automata/SparseContinuationNontransitivity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This assertion concerns the same three-word promise throughout. It says that two successive compatible pairs force the third pair to be compatible.

**Theorem 1.4 (Failure of transitivity).**

$$\neg(\mathit{claim})$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/SparseContinuationNontransitivity.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take the actual prefixes x, y, z. If x followed by w is legal, constructor equality in the three-word domain forces w to be the one-letter word a. For y it forces w to be b, and for z it forces w to be a. Since a and b are distinct, x and y have no common legal suffix, and neither do y and z. Both pairs therefore agree vacuously. The suffix a is legal at x and z, where the outputs are respectively zero and one, giving an actual Conflict. Transitivity applied to the first two pairs contradicts this third pair. The empty suffix is illegal at each of x, y, z, and longer or other suffixes are excluded by the same constructor equalities. This is the known construction of Proposition 3.3 in the original computational behavior representation theory, rather than a new research counterexample.

## References

- Truth anchor: `D5/S0/Automata/SparseContinuationNontransitivity.claim`
- Truth anchor: `D5/S0/Automata/SparseContinuationNontransitivity.output`
- Truth anchor: `D5/S0/Automata/SparseContinuationNontransitivity.promise`
- Truth anchor: `D5/S0/Automata/SparseContinuationNontransitivity.result`
- Dependency: [D5/S0/Automata/PromiseColoringTotalization](PromiseColoringTotalization.md)
