# Sector Schmidt Encodings

## Abstract

Dependent sector coordinates and the normalized source and flat target encoding matrices.

Sector and Coord are finite types with decidable equality. The natural number d(s) is the target rank of sector s. sourceFiber(d,Coord,s) is Fin(d(s)) times Coord, while targetFiber(d,s) is Fin(d(s)). Sigma forms the dependent sum over Sector. Each such coordinate x has sector(x); a source coordinate also has residual(x) in Coord. ofNat and ofReal denote the real and complex scalar embeddings.

**Definition 1.1 (Source coordinates).**

$$\forall Sector \in FiniteType, Coord \in FiniteType, d \in \operatorname{Function}\left(Sector, \mathbb{N}\right),\; \operatorname{SourceLocal}\left(d, Coord\right) = \operatorname{Sigma}\left(Sector, \operatorname{sourceFiber}\left(d, Coord\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SectorSchmidtEncoding.SourceLocal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A source coordinate contains its sector, one target coordinate, and one residual spectral coordinate.

**Definition 1.2 (Target coordinates).**

$$\forall Sector \in FiniteType, d \in \operatorname{Function}\left(Sector, \mathbb{N}\right),\; \operatorname{TargetLocal}\left(d\right) = \operatorname{Sigma}\left(Sector, \operatorname{targetFiber}\left(d\right)\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SectorSchmidtEncoding.TargetLocal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A target coordinate contains its sector and one coordinate within the sector rank.

**Definition 1.3 (Source encoding matrix).**

$$\forall Sector \in FiniteType, Coord \in FiniteType, d \in \operatorname{Function}\left(Sector, \mathbb{N}\right),\; \forall spectrum \in \operatorname{Function}\left(Sector, \operatorname{Function}\left(Coord, \mathbb{R}\right)\right), x \in \operatorname{SourceLocal}\left(d, Coord\right), y \in \operatorname{SourceLocal}\left(d, Coord\right), s \in Sector,\; \operatorname{entry}\left(\operatorname{sourceEncoding}\left(d, spectrum\right), \operatorname{pair}\left(x, y\right), s\right) = \operatorname{ite}\left(x = y \land \operatorname{sector}\left(x\right) = s, \operatorname{ofReal}\left(\operatorname{sqrt}\left(\frac{\operatorname{apply}\left(spectrum, \operatorname{sector}\left(x\right), \operatorname{residual}\left(x\right)\right)}{\operatorname{ofNat}\left(\operatorname{apply}\left(d, \operatorname{sector}\left(x\right)\right)\right)}\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SectorSchmidtEncoding.sourceEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source matrix is diagonal across the two physical sides. In sector s each residual value is repeated d(s) times, with amplitude sqrt(spectrum(s,j)/d(s)). Positive ranks and normalized nonnegative spectra make these columns unit vectors; distinct sector columns have disjoint support.

**Definition 1.4 (Flat target encoding matrix).**

$$\forall Sector \in FiniteType, d \in \operatorname{Function}\left(Sector, \mathbb{N}\right),\; \forall x \in \operatorname{TargetLocal}\left(d\right), y \in \operatorname{TargetLocal}\left(d\right), s \in Sector,\; \operatorname{entry}\left(\operatorname{targetEncoding}\left(d\right), \operatorname{pair}\left(x, y\right), s\right) = \operatorname{ite}\left(x = y \land \operatorname{sector}\left(x\right) = s, \operatorname{ofReal}\left(\operatorname{sqrt}\left(\operatorname{inv}\left(\operatorname{ofNat}\left(\operatorname{apply}\left(d, \operatorname{sector}\left(x\right)\right)\right)\right)\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Entanglement/SectorSchmidtEncoding.targetEncoding` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The target matrix has equal amplitude sqrt(1/d(s)) on the diagonal coordinates of sector s. Positive sector ranks make its columns unit vectors with disjoint sector supports.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/SectorSchmidtEncoding.SourceLocal`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorSchmidtEncoding.TargetLocal`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorSchmidtEncoding.sourceEncoding`
- Truth anchor: `D5/S3/Quantum/Entanglement/SectorSchmidtEncoding.targetEncoding`
- Dependency: [D5/S3/Quantum/Foundation/FiniteStateChannel](../Foundation/FiniteStateChannel.md)
