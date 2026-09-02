# Symmetric Off-Line Quartic

## Abstract

A centered quartic has full reflection and conjugation symmetry while all four zeros remain off the critical line.

**Theorem 1.1 (Full symmetry does not force critical-line localization).**

$$\forall delta, gamma \in \operatorname{Real}\left(\right),\\{}(delta \ne 0 \land gamma \ne 0) \Rightarrow\\{}\operatorname{let} centered := X - \operatorname{C}\left(\operatorname{criticalAbscissa}\left(\right)\right),\\{}\operatorname{let} P_{delta,gamma} := ((centered - \operatorname{C}\left(delta\right))^{2} + (\operatorname{C}\left(gamma\right))^{2}) \times ((centered + \operatorname{C}\left(delta\right))^{2} + (\operatorname{C}\left(gamma\right))^{2}),\\{}\operatorname{Differentiable}\left(\operatorname{Complex}\left(\right), (s \mapsto \operatorname{eval}\left(P_{delta,gamma}, s\right))\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{eval}\left(P_{delta,gamma}, s\right) = 0 \Leftrightarrow s \in \{\operatorname{criticalAbscissa}\left(\right) + delta + i \times gamma, \operatorname{criticalAbscissa}\left(\right) + delta - i \times gamma, \operatorname{criticalAbscissa}\left(\right) - delta + i \times gamma, \operatorname{criticalAbscissa}\left(\right) - delta - i \times gamma\}\right) \land \left(\operatorname{card}\left(\{\operatorname{criticalAbscissa}\left(\right) + delta + i \times gamma, \operatorname{criticalAbscissa}\left(\right) + delta - i \times gamma, \operatorname{criticalAbscissa}\left(\right) - delta + i \times gamma, \operatorname{criticalAbscissa}\left(\right) - delta - i \times gamma\}\right) = 4 \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{eval}\left(P_{delta,gamma}, 1 - s\right) = \operatorname{eval}\left(P_{delta,gamma}, s\right)\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{eval}\left(P_{delta,gamma}, \operatorname{conj}\left(s\right)\right) = \operatorname{conj}\left(\operatorname{eval}\left(P_{delta,gamma}, s\right)\right)\right) \land \left(\left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{eval}\left(P_{delta,gamma}, s\right) = 0 \Rightarrow \operatorname{Re}\left(s\right) \ne \operatorname{criticalAbscissa}\left(\right)\right) \land \left(\neg \left(\forall s \in \operatorname{Complex}\left(\right),\; \operatorname{eval}\left(P_{delta,gamma}, s\right) = 0 \Rightarrow \operatorname{Re}\left(s\right) = \operatorname{criticalAbscissa}\left(\right)\right)\right)\right)\right)\right)\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Zeros/ToySpectrum/SymmetricOffLineQuartic.symmetric_off_line_quartic_spec` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary nonzero real transverse and vertical parameters, the displayed centered quartic is complex differentiable everywhere. Its zeros are exactly the four independent sign choices, and the nonzero hypotheses make those four points distinct.

Evaluation is invariant under s mapped to one minus s and is covariant under complex conjugation. Nevertheless every zero has real part different from the critical abscissa, and an explicit root refutes universal fixed-line localization for this same polynomial.

## References

- Truth anchor: `D5/S3/Zeros/ToySpectrum/SymmetricOffLineQuartic.symmetric_off_line_quartic_spec`
