# Exact Kraus words and strict positivity

## Abstract

Full exact-length Kraus-word span forces strict positivity of the same actual iterate.

Fix arbitrary natural numbers d and g and a family K of g complex d by d matrices. There is no trace-preservation or unitality premise. A word of length m is indexed by a function from Fin m to Fin g. Its coordinate zero is the leftmost, latest factor; the product is K(w(0)) through K(w(m-1)). Reversing all tuple coordinates gives the convention of Ekblad Section 4 without changing the set of words. The empty product is the identity. The finite sum below ranges over every function of the indicated type.

**Definition 1.1 (Exact-length Kraus products).**

$$\forall (d:\mathbb{N}), (\forall (g:\mathbb{N}), (\forall (K:\operatorname{Fin}\left(g\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (w:\operatorname{Fin}\left(0\right) \to \operatorname{Fin}\left(g\right)), (\operatorname{word}\left(K, 0, w\right) = 1) \land \forall (m:\mathbb{N}), (\forall (w:\operatorname{Fin}\left(m + 1\right) \to \operatorname{Fin}\left(g\right)), (\operatorname{word}\left(K, m + 1, w\right) = \operatorname{apply}\left(K, \operatorname{apply}\left(w, 0\right)\right) \cdot \operatorname{word}\left(K, m, \operatorname{tail}\left(w\right)\right))))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity.word` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Owen Ekblad (2025). *A note on the quantum Wielandt inequality*. URL: <https://arxiv.org/abs/2504.21638v3>.

*Commentary.*

The two recursion clauses specify the empty word and left multiplication by the latest letter. The tail removes coordinate zero. This definition is earned by the actual iterate expansion.

**Definition 1.2 (Span at exactly one length).**

$$\forall (d:\mathbb{N}), (\forall (g:\mathbb{N}), (\forall (K:\operatorname{Fin}\left(g\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (m:\mathbb{N}), (\operatorname{wordSpan}\left(K, m\right) = \operatorname{span}\left(\mathbb{C}, \operatorname{range}\left(\operatorname{word}\left(K, m\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity.wordSpan` (`✓ std3`).

*Citation.* Owen Ekblad (2025). *A note on the quantum Wielandt inequality*. URL: <https://arxiv.org/abs/2504.21638v3>.

*Commentary.*

The scalar field is the complex numbers and the ambient space is the full matrix algebra. Words of smaller lengths are not added. This is the spanning condition in equation (4.1).

**Theorem 1.3 (Expansion of the actual iterate).**

$$\forall (d:\mathbb{N}), (\forall (g:\mathbb{N}), (\forall (K:\operatorname{Fin}\left(g\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (m:\mathbb{N}), (\forall (X:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{iterate}\left(\operatorname{ofkraus}\left(K, K\right), m, X\right) = \operatorname{sum}\left(\lambda (w:\operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(g\right)) \mapsto (\operatorname{word}\left(K, m, w\right) \cdot X \cdot \operatorname{adjoint}\left(\operatorname{word}\left(K, m, w\right)\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity.iterate_eq_word_sum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Owen Ekblad (2025). *A note on the quantum Wielandt inequality*. URL: <https://arxiv.org/abs/2504.21638v3>.

*Commentary.*

The function being iterated is precisely MatrixMap.of_kraus K K from FiniteKrausChannel, so its one-step action is the sum of K(i) X K(i)*. Induction splits an (m+1)-tuple into its first letter and tail and distributes matrix multiplication over the finite sums. The zero-length function type has one element even when g is zero.

**Theorem 1.4 (Full span implies strict positivity at the same length).**

$$\forall (d:\mathbb{N}), (\forall (g:\mathbb{N}), (\forall (K:\operatorname{Fin}\left(g\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\forall (m:\mathbb{N}), (\forall (X:\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)), (\operatorname{wordSpan}\left(K, m\right) = \operatorname{top}\left(\operatorname{Matrix}\left(\operatorname{Fin}\left(d\right), \operatorname{Fin}\left(d\right), \mathbb{C}\right)\right) \Rightarrow \left(\operatorname{PosSemidef}\left(X\right) \Rightarrow \left(\left(\neg X = 0\right) \Rightarrow \operatorname{PosDef}\left(\operatorname{iterate}\left(\operatorname{ofkraus}\left(K, K\right), m, X\right)\right)\right)\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity.iterate_posDef_of_wordSpan_eq_top` (`✓ std3`). ∎

*Citation.* Owen Ekblad (2025). *A note on the quantum Wielandt inequality*. URL: <https://arxiv.org/abs/2504.21638v3>.

*Commentary.*

For every nonzero positive semidefinite X the same m-th iterate is positive definite. Each word conjugate is positive semidefinite. If the output quadratic form at a nonzero vector v vanished, every nonnegative summand would vanish. The PSD kernel criterion then gives X L* v = 0 for each length-m word L. The matrices A satisfying X A* v = 0 form a complex submodule: scalar multiplication conjugates the scalar. Full word span puts every matrix in that submodule. Choose a nonzero coordinate v(i) and test every matrix unit E(i,b); each test forces v(i) X(a,b) = 0. Thus X = 0, a contradiction. Zero d is covered by the impossible nonzero-input premise. Zero g and zero m are retained with their actual word types and identity product. This is the known bridge underlying Wielength >= primitivity index in Ekblad Section 4. It proves no quadratic word-length bound and no quantitative bound on the gap; the global conjecture status is unverified, and the cited source explicitly notes a proposed resolution.

## References

- Truth anchor: `D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity.iterate_eq_word_sum`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity.iterate_posDef_of_wordSpan_eq_top`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity.word`
- Truth anchor: `D5/S3/Quantum/QuantumChannels/KrausWordStrictPositivity.wordSpan`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
