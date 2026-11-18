# Spatial cuts and fixed-occupation shuffle phases

## Abstract

Spatial cuts and fixed-occupation shuffle phases

The sites have a linear order. The retained side is a set of sites and the traced side is its complement. An occupation label on either side specifies a finite set of occupied sites.

**Definition 1.1 (Four alternating sites).**

$$\operatorname{Alternates}(I) \iff \exists x,y,z,w \in \iota, x<y<z<w \land ((x \in I \land y \in I^{c} \land z \in I \land w \in I^{c}) \lor (x \in I^{c} \land y \in I \land z \in I^{c} \land w \in I))$$

*Formalization.* `D5/S3/Quantum/Fermionic/SlaterCutPhase.Alternates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Read four strictly increasing sites. Membership in the retained side alternates at each step, starting on either side.

**Theorem 1.2 (One side is an interval).**

$$\forall I \subseteq \iota, \neg\operatorname{Alternates}(I) \iff \operatorname{OrdConnected}(I) \lor \operatorname{OrdConnected}(I^{c})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/SlaterCutPhase.not_alternates_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The cut has no four alternating sites exactly when one side is order connected. A hole between two retained sites forces every traced site between those endpoints. A retained site between two such traced sites would complete an alternating quadruple.

**Definition 1.3 (Cross-inversion count).**

$$\operatorname{crossCount}(a, b) = \sum_{i \in a}\sum_{j \in b}\mathbf{1}_{j<i}$$

*Formalization.* `D5/S3/Quantum/Fermionic/SlaterCutPhase.crossCount` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each occupied retained site the sum counts occupied traced sites to its left. These are exactly the pairs that cross when the retained sites are placed first.

**Theorem 1.4 (Characteristic polynomial of the signed marginal).**

$$\begin{aligned}\neg\operatorname{Alternates}(I),\quad\forall x \in A, a(x) \subseteq I,\quad\forall y \in B, b(y) \subseteq I^{c}\\\forall x,y, \lvert a(x) \rvert+\lvert b(y) \rvert \neq k \longrightarrow \psi(x, y)=0\\\widetilde{\psi}(x, y)=(-1)^{\operatorname{crossCount}(a(x), b(y))} \psi(x, y)\\\longrightarrow \operatorname{charpoly}(\widetilde{\psi} \widetilde{\psi}^{*}) = \operatorname{charpoly}(\psi \psi^{*})\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Fermionic/SlaterCutPhase.reduction_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The row and column label types A and B are finite, and A has decidable equality. The maps a and b assign finite occupied sets to these labels. The complex amplitude matrix is supported on total occupation k, a natural number. When the retained side is an interval, the sign depends only on the traced occupation and cancels in the marginal. When the traced side is an interval, the sign depends only on the retained occupation and gives a diagonal unitary conjugation. An empty side gives sign one. The two Gram matrices thus have identical characteristic polynomials, including all zero roots with multiplicity.

## References

- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterCutPhase.Alternates`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterCutPhase.crossCount`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterCutPhase.not_alternates_iff`
- Truth anchor: `D5/S3/Quantum/Fermionic/SlaterCutPhase.reduction_charpoly`
