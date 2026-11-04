# Raw Three-Phase Descent Prerequisite

## Abstract

Raw three-phase balance forces marker invariance and contextual three-step readout invariance on an arbitrary unital magma.

**Definition 1.1 (The original raw balance hypotheses).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, \operatorname{RawBalance}\left(U, c\right) = (\operatorname{U}\left(1\right) = 1 \land (\forall a: M, (\forall b: M, 0 \le \operatorname{c}\left(a, b\right))) \land (\forall a: M, \operatorname{c}\left(a, a\right) = 0) \land (\forall a: M, (\forall b: M, (\forall u: M, (\forall v: M, \operatorname{c}\left(a \cdot u, b \cdot v\right) + \operatorname{c}\left(a \cdot \operatorname{U}\left(u\right), b \cdot \operatorname{U}\left(v\right)\right) + \operatorname{c}\left(a \cdot \operatorname{U}\left(\operatorname{U}\left(u\right)\right), b \cdot \operatorname{U}\left(\operatorname{U}\left(v\right)\right)\right) = 3 \cdot \operatorname{c}\left(a, b\right) + 3 \cdot \operatorname{c}\left(u, v\right))))))$$

*Formalization.* `D5/S3/Quantum/Completion/RawThreePhaseDescent.RawBalance` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

M has only a binary operation and a two-sided unit. U is an arbitrary self-map fixing the unit, and c is finite and real-valued. No associativity, commutativity, cancellation, inverse, marker homomorphism, surjectivity, periodicity, symmetry or positive-semidefinite form is assumed.

**Theorem 1.2 (The comparison has derived marker invariance).**

$$\forall M: Type, [\operatorname{MulOneClass}\left(M\right)], U: M \to M, c: M \to M \to \mathbb{R}, \operatorname{RawBalance}\left(U, c\right) \Rightarrow ((\forall u: M, (\forall v: M, \operatorname{c}\left(\operatorname{U}\left(u\right), \operatorname{U}\left(v\right)\right) = \operatorname{c}\left(u, v\right))) \land (\forall a: M, (\forall b: M, (\forall u: M, (\forall v: M, \operatorname{c}\left(a \cdot \operatorname{U}\left(\operatorname{U}\left(\operatorname{U}\left(u\right)\right)\right), b \cdot \operatorname{U}\left(\operatorname{U}\left(\operatorname{U}\left(v\right)\right)\right)\right) = \operatorname{c}\left(a \cdot u, b \cdot v\right))))) \land (\forall u: M, (\forall z: M, (\operatorname{c}\left(\operatorname{U}\left(\operatorname{U}\left(\operatorname{U}\left(u\right)\right)\right), z\right) = \operatorname{c}\left(u, z\right) \land \operatorname{c}\left(z, \operatorname{U}\left(\operatorname{U}\left(\operatorname{U}\left(u\right)\right)\right)\right) = \operatorname{c}\left(z, u\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Completion/RawThreePhaseDescent.raw_marker_readouts` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For s(n)=c(U^n u,U^n v), the raw law at the two units gives s(n+1)+s(n+2)=2s(n). Nonnegativity at every natural n rules out the growing alternating component by induction and an Archimedean contradiction. Subtracting the balance identity for (u,v) from that for (Uu,Uv) gives contextual invariance. Specializing either contextual input to the unit yields every row and column equality. Only the readings have period three; the original marker need not have period three.

This is the Section 2 prerequisite of C133 Continuation V. The anchored free-space bilinear form, both radical pairings, zero-fibre elimination, full fibre collapse and the complete Hilbert representation criterion remain open. No physical preparation, scalar control, reference or clock follows from this result.

## References

- Truth anchor: `D5/S3/Quantum/Completion/RawThreePhaseDescent.RawBalance`
- Truth anchor: `D5/S3/Quantum/Completion/RawThreePhaseDescent.raw_marker_readouts`
