# Spatial cuts and fixed-occupation shuffle phases

## Abstract

Spatial cuts and fixed-occupation shuffle phases

The sites have a linear order. The retained side is a set of sites and the traced side is its complement. An occupation label on either side specifies a finite set of occupied sites.

**Definition 1.1 (Four alternating sites).**

$$\forall \iota: \operatorname{Type}, [\operatorname{LinearOrder}(\iota)], I: \operatorname{Set}(\iota), \operatorname{Alternates}(I) \iff \exists x,y,z,w \in \iota, x<y<z<w \land ((x \in I \land y \in I^{c} \land z \in I \land w \in I^{c}) \lor (x \in I^{c} \land y \in I \land z \in I^{c} \land w \in I))$$

*Formalization.* `D5/S3/Quantum/Fermionic/SlaterCutPhase.Alternates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read four strictly increasing sites. Membership in the retained side alternates at each step, starting on either side.

**Theorem 1.2 (One side is an interval).**

$$\forall \iota: \operatorname{Type}, [\operatorname{LinearOrder}(\iota)], I: \operatorname{Set}(\iota), \neg\operatorname{Alternates}(I) \iff \operatorname{OrdConnected}(I) \lor \operatorname{OrdConnected}(I^{c})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/SlaterCutPhase.not_alternates_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cut has no four alternating sites exactly when one side is order connected. Without alternation, a hole between two retained sites forces every traced site between those endpoints. A retained site between two such traced sites would complete an alternating quadruple.

**Definition 1.3 (Cross-inversion count).**

$$\forall \iota: \operatorname{Type}, [\operatorname{LinearOrder}(\iota)], a, b: \operatorname{Finset}(\iota), \operatorname{crossCount}(a, b) = \sum_{i \in a}\sum_{j \in b}\mathbf{1}_{j<i}$$

*Formalization.* `D5/S3/Quantum/Fermionic/SlaterCutPhase.crossCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each occupied retained site the sum counts occupied traced sites to its left. These are exactly the pairs that cross when the retained sites are placed first.

**Theorem 1.4 (Characteristic polynomial of the signed marginal).**

$$\begin{aligned}\forall \iota: \operatorname{Type}, [\operatorname{LinearOrder}(\iota)], I: \operatorname{Set}(\iota), A, B: \operatorname{Type}, [\operatorname{Fintype}(A)], [\operatorname{DecidableEq}(A)], [\operatorname{Fintype}(B)],\\a: A \to \operatorname{Finset}(\iota), b: B \to \operatorname{Finset}(\iota), k: \mathbb{N}, \psi: \operatorname{Matrix}(A, B, \mathbb{C}),\\\operatorname{let} \widetilde{\psi} = (x, y) \mapsto (-1)^{\operatorname{crossCount}(a(x), b(y))} \psi(x, y) \operatorname{in}\\\neg\operatorname{Alternates}(I) \land (\forall x \in A, a(x) \subseteq I) \land (\forall y \in B, b(y) \subseteq I^{c}) \land\\(\forall x \in A, \forall y \in B, \lvert a(x) \rvert+\lvert b(y) \rvert \neq k \longrightarrow \psi(x, y)=0)\\\longrightarrow \operatorname{charpoly}(\widetilde{\psi} \widetilde{\psi}^{*}) = \operatorname{charpoly}(\psi \psi^{*})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/SlaterCutPhase.reduction_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

On the total occupation k sector, the sign depends only on the traced occupation if the retained side is an interval. It cancels in the marginal. If the traced side is an interval, the sign on that sector depends only on the retained occupation and gives a diagonal unitary conjugation. An empty side gives sign one. The two Gram matrices have identical characteristic polynomials, including all zero roots with multiplicity.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterCutPhase.Alternates`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterCutPhase.crossCount`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterCutPhase.not_alternates_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterCutPhase.reduction_charpoly`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](../Information/PartialTraceMutualInformation.md)
