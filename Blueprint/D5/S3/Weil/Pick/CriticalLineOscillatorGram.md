# Critical-Line Oscillator Gram Matrix

## Abstract

A reflected critical-line pole pair generates a finite rank-two positive Pick matrix.

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

Each entry is the sum of the two rank-one kernels obtained from the reflected resolvent coordinates.

**Theorem 1.3 (The oscillator Pick matrix is a positive Gram matrix).**

$$\begin{gathered}\forall I: \operatorname{Type}, \gamma \in \mathbb{R}, nodes: I \mapsto \mathbb{C},\\{}\operatorname{Fintype}(I) \Rightarrow\\{}\operatorname{criticalLineOscillatorPickMatrix}(\gamma, nodes) = \operatorname{conjTranspose}(\operatorname{criticalLineOscillatorFeatureMatrix}(\gamma, nodes)) \cdot \operatorname{criticalLineOscillatorFeatureMatrix}(\gamma, nodes) \land\\{}\operatorname{PosSemidef}(\operatorname{criticalLineOscillatorPickMatrix}(\gamma, nodes)).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/CriticalLineOscillatorGram.critical_line_oscillator_pick_gram` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Expanding the two-row matrix product gives the displayed kernel entry by entry.

Mathlib's conjugate-transpose Gram theorem then proves positive semidefiniteness for every finite family of complex nodes, including repeated nodes and nodes at a pole under the totalized inverse convention.

## References

- Truth anchor: `D5/S3/Weil/Pick/CriticalLineOscillatorGram.criticalLineOscillatorFeatureMatrix`
- Truth anchor: `D5/S3/Weil/Pick/CriticalLineOscillatorGram.criticalLineOscillatorPickMatrix`
- Truth anchor: `D5/S3/Weil/Pick/CriticalLineOscillatorGram.critical_line_oscillator_pick_gram`
