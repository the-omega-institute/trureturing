# Jet Pencil Finite Expansion

## Abstract

A finite nilpotent jet pencil has an explicit determinant and inverse series.

**Theorem 1.1 (The nilpotent pencil terminates after its jet length).**

$$\forall m \in \mathbb{N}, rho \in \mathbb{C}, s \in \mathbb{C},\; \operatorname{det}\left(\operatorname{jetPencil}\left(m, rho, s\right)\right) = (s - rho)^{m} \land \left(\left(\forall k \in \mathbb{N},\; 1 \le k \Rightarrow \operatorname{trace}\left(\operatorname{nilpotentJetShift}\left(m\right)^{k}\right) = 0\right) \land \left(s \ne rho \Rightarrow \operatorname{jetPencil}\left(m, rho, s\right)^{-1} = \sum_{k=0}^{m - 1} \frac{\operatorname{nilpotentJetShift}\left(m\right)^{k}}{(s - rho)^{k + 1}}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/BlockStructure/JetPencilFiniteExpansion.jet_pencil_finite_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a natural length m, nilpotentJetShift m is the matrix with a one exactly one step below the diagonal and zero elsewhere. The reused jetPencil m rho s is (s-rho) times the identity minus this shift.

There is no global premise: the determinant and positive-power trace identities hold for every s and rho. The condition s != rho guards only the displayed inverse series, whose denominators are powers of s-rho. No positivity assumption on m is needed; at m = 0 the empty matrix identities remain valid.

Lower triangularity gives determinant (s-rho)^m. Cayley-Hamilton makes the m-th shift power zero, so the geometric inverse terminates at k = m-1. Nilpotence of every positive power and the pinned matrix trace lemma give trace zero for every k >= 1. Lean represents each matrix quotient by inverse scalar multiplication.

## References

- Truth anchor: `D5/S3/Observer/BlockStructure/JetPencilFiniteExpansion.jet_pencil_finite_expansion`
- Dependency: [D5/S3/Analytic/Adelic/JetResolventSemisimplification](../../Analytic/Adelic/JetResolventSemisimplification.md)
