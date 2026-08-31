# Critical-Line Oscillator Gram Matrix

## Abstract

Critical-line oscillator resolvents generate a two-row positive Pick Gram matrix.

**Definition 1.1 (Reflected oscillator feature matrix).**

Lean statement: `D5/S3/Weil/Pick/CriticalLineOscillatorGram.criticalLineOscillatorFeatureMatrix`

*Formalization.* `D5/S3/Weil/Pick/CriticalLineOscillatorGram.criticalLineOscillatorFeatureMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The two rows sample the resolvents at the reflected imaginary poles plus and minus i times the real ordinate.

**Definition 1.2 (Finite oscillator Pick matrix).**

Lean statement: `D5/S3/Weil/Pick/CriticalLineOscillatorGram.criticalLineOscillatorPickMatrix`

*Formalization.* `D5/S3/Weil/Pick/CriticalLineOscillatorGram.criticalLineOscillatorPickMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The Pick atom is defined as the conjugate-transpose Gram product of the two reflected resolvent rows. Its rank is at most two, with possible degeneracy.

**Theorem 1.3 (The oscillator Pick matrix is positive semidefinite).**

$$\forall I: \operatorname{Type}, gamma \in \mathbb{R}, nodes: I \mapsto \mathbb{C},\\{}\operatorname{Fintype}(I) \Rightarrow\\{}\operatorname{PosSemidef}(\operatorname{criticalLineOscillatorPickMatrix}(gamma, nodes)).$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/CriticalLineOscillatorGram.critical_line_oscillator_pick_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The preceding definition owns the Gram factorization.

Mathlib's conjugate-transpose Gram theorem proves positive semidefiniteness for every finite family of complex nodes, including repeated nodes and nodes at a pole under the totalized inverse convention.

## References

- Truth anchor: `D5/S3/Weil/Pick/CriticalLineOscillatorGram.criticalLineOscillatorFeatureMatrix`
- Truth anchor: `D5/S3/Weil/Pick/CriticalLineOscillatorGram.criticalLineOscillatorPickMatrix`
- Truth anchor: `D5/S3/Weil/Pick/CriticalLineOscillatorGram.critical_line_oscillator_pick_gram`
