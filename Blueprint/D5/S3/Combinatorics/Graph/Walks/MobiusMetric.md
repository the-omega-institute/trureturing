# All-size native Mobius metrics and diameters

## Abstract

Antipodal translation reduces native shortest paths to two cyclic alternatives.

Put r=m+2 and z=(v-u).val in ZMod(2r). The native distance is min(min(z,2r-z), 1+min(Nat.dist(r,z),2r-Nat.dist(r,z))). The spanning unit-jump cycle is connected. Antipodal translation is an involutive automorphism of that cycle, and its matching extension equals the native Mobius graph.

**Theorem 1.1 (Exact cyclic-difference metric).**

$$\forall m \in \mathrm{Nat},\; \forall u \in \operatorname{ZMod}\left(\operatorname{mul}\left(2, \operatorname{add}\left(m, 2\right)\right)\right),\; \forall v \in \operatorname{ZMod}\left(\operatorname{mul}\left(2, \operatorname{add}\left(m, 2\right)\right)\right),\; \operatorname{dist}\left(\operatorname{mobius}\left(m\right), u, v\right) = \operatorname{MobiusMetricFormula}\left(m, u, v\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MobiusMetric.mobius_distance` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The notation MobiusMetricFormula denotes precisely the minimum displayed in the preceding paragraph, with r=m+2 and z=(v-u).val. The proof reuses the public cycle-distance theorem and length-preserving graph-isomorphism distance transport, then applies the involutive matching normal form.

**Theorem 1.2 (The sharp diameter at every size).**

$$\forall m \in \mathrm{Nat},\; \operatorname{diam}\left(\operatorname{mobius}\left(m\right)\right) = \operatorname{NatDiv}\left(\operatorname{add}\left(m, 3\right), 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/MobiusMetric.mobius_diameter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The metric formula bounds every distance by floor((m+3)/2). The actual cyclic vertex with value floor((m+3)/2), paired with zero, attains that bound. This proves all sizes at once, including diameters one, two and two for the first three Mobius ladders.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MobiusMetric.mobius_diameter`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/MobiusMetric.mobius_distance`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/CirculantComponents](CirculantComponents.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/InvolutiveMatchingDistance](InvolutiveMatchingDistance.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MobiusLadderSpectrum](MobiusLadderSpectrum.md)
- Dependency: [D5/S3/Combinatorics/Graph/Walks/PowerSpectrumStructure](PowerSpectrumStructure.md)
