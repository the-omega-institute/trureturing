# Flat Phase Conjugation

## Abstract

Entrywise unit modulus reduces the diagonal of normalized phase conjugation to a conjugate sum.

**Definition 1.1 (The normalized entrywise kernel).**

$$\forall \iota,\kappa:Type,\operatorname{Fintype}(\kappa)\implies \forall H:\operatorname{Matrix}(\iota, \kappa, \mathbb{C}),\forall c:\iota\to \mathbb{C},\forall d:\kappa\to \mathbb{C}, \forall i,l:\iota, \operatorname{flatPhaseConjugation}(H, c, d, i, l)=\operatorname{card}(\kappa)^{-1}\operatorname{c}(i)\sum_{j:\kappa}\operatorname{H}(i, j)\overline{\operatorname{d}(j)}\overline{\operatorname{H}(l, j)}.$$

*Formalization.* `D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For arbitrary index types iota and kappa with Fintype kappa, the kernel is defined entrywise for a complex matrix H and complex profiles c and d. The inverse cardinality is the complex field inverse, including when kappa is empty.

**Theorem 1.2 (Unit modulus simplifies each diagonal entry).**

$$\forall \iota,\kappa:Type,\operatorname{Fintype}(\kappa)\implies \forall H:\operatorname{Matrix}(\iota, \kappa, \mathbb{C}),\forall c:\iota\to \mathbb{C},\forall d:\kappa\to \mathbb{C}, (\forall a:\iota,\forall j:\kappa,\operatorname{normSq}(\operatorname{H}(a, j))=1)\implies \forall i:\iota, \operatorname{flatPhaseConjugation}(H, c, d, i, i)=\operatorname{card}(\kappa)^{-1}\operatorname{c}(i)\sum_{j:\kappa}\overline{\operatorname{d}(j)}.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every entry of H has squared modulus one, each diagonal entry equals the inverse cardinality times c at that index times the sum of the conjugates of d.

**Theorem 1.3 (A zero-sum profile cancels a chosen diagonal entry).**

$$\forall \iota,\kappa:Type,\operatorname{Fintype}(\kappa)\implies \forall H:\operatorname{Matrix}(\iota, \kappa, \mathbb{C}),\forall c:\iota\to \mathbb{C},\forall d:\kappa\to \mathbb{C}, (\forall a:\iota,\forall j:\kappa,\operatorname{normSq}(\operatorname{H}(a, j))=1)\land (\sum_{j:\kappa}\operatorname{d}(j)=0)\implies \forall i:\iota, \operatorname{flatPhaseConjugation}(H, c, d, i, i)=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation_diagonal_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under entrywise squared modulus one for H and a zero sum for d, the diagonal entry at any supplied index i is zero.

**Theorem 1.4 (The whole diagonal vanishes pointwise).**

$$\forall \iota,\kappa:Type,\operatorname{Fintype}(\kappa)\implies \forall H:\operatorname{Matrix}(\iota, \kappa, \mathbb{C}),\forall c:\iota\to \mathbb{C},\forall d:\kappa\to \mathbb{C}, (\forall a:\iota,\forall j:\kappa,\operatorname{normSq}(\operatorname{H}(a, j))=1)\land (\sum_{j:\kappa}\operatorname{d}(j)=0)\implies \forall i:\iota, \operatorname{flatPhaseConjugation}(H, c, d, i, i)=0.$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation_zero_diagonal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same hypotheses give the universally quantified zero-diagonal statement by applying the single-entry theorem at each index.

## References

- Truth anchor: `D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation`
- Truth anchor: `D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation_diagonal`
- Truth anchor: `D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation_diagonal_zero`
- Truth anchor: `D5/S3/Quantum/Algebra/FlatPhaseConjugation.flatPhaseConjugation_zero_diagonal`
