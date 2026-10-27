# Charge-sector normalization refutes majorization preservation

## Abstract

Normalization inside a common charge sector can reverse a majorization order.

**Definition 1.1 (The normalized charge-sector spectrum).**

$$\forall \{n: \mathbb{N}\}, (\forall (r: \operatorname{Fin}\left(n\right) \to \mathbb{R}), (\forall (charge: \operatorname{Fin}\left(n\right) \to \mathbb{Z}), (\forall (q: \mathbb{Z}), (sectorSpectrum\left(r, charge, q\right) = \operatorname{List.mergeSort}\left(\operatorname{List.map}\left((\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (\frac{r\left(i\right)}{pushforward\left(charge, r, q\right)})), \operatorname{List.filter}\left((\lambda (i: \operatorname{Fin}\left(n\right)) \mapsto (decide\left(charge\left(i\right) = q\right))), \operatorname{List.finRange}\left(n\right)\right)\right), (\lambda (a: \mathbb{R}) \mapsto ((\lambda (b: \mathbb{R}) \mapsto (decide\left(b \le a\right)))))\right)))))$$

*Formalization.* `D5/S3/Entropy/ChargeSectorMajorizationRefutation.sectorSpectrum` (`✓ std3`).

*Citation.* Raúl Arias; Giuseppe Di Giulio; Esko Keski-Vakkuri; Erik Tonni (2023). *Probing RG flows, symmetry resolution and quench dynamics through the capacity of entanglement*. DOI: [10.1007/JHEP03(2023)175](https://doi.org/10.1007/JHEP03(2023)175). URL: <https://arxiv.org/abs/2301.02117v1>.

*Commentary.*

For a real weight vector r on Fin n and an integer charge function, sectorSpectrum selects the indices with charge q, divides each selected weight by the total weight in that sector, and sorts the resulting list in descending order. This is the normalized charge-block spectrum used in the source's charge decomposition (arXiv:2301.02117v1, lines 3550–3569).

**Definition 1.2 (Majorization preservation in every positive sector).**

$$claim = (\forall (n: \mathbb{N}), (\forall (charge: \operatorname{Fin}\left(n\right) \to \mathbb{Z}), (\forall (r: \operatorname{Fin}\left(n\right) \to \mathbb{R}), (\forall (s: \operatorname{Fin}\left(n\right) \to \mathbb{R}), ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) \le r\left(i\right))) \Rightarrow ((\sum_{i: \operatorname{Fin}\left(n\right)} (r\left(i\right)) = (1: \mathbb{R})) \Rightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), ((0: \mathbb{R}) \le s\left(i\right))) \Rightarrow ((\sum_{i: \operatorname{Fin}\left(n\right)} (s\left(i\right)) = (1: \mathbb{R})) \Rightarrow ((Majorizes\left(desc\left(r\right), desc\left(s\right)\right)) \Rightarrow (\forall (q: \mathbb{Z}), (((0: \mathbb{R}) < pushforward\left(charge, r, q\right)) \Rightarrow (((0: \mathbb{R}) < pushforward\left(charge, s, q\right)) \Rightarrow (Majorizes\left(sectorSpectrum\left(r, charge, q\right), sectorSpectrum\left(s, charge, q\right)\right))))))))))))))$$

*Formalization.* `D5/S3/Entropy/ChargeSectorMajorizationRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Raúl Arias; Giuseppe Di Giulio; Esko Keski-Vakkuri; Erik Tonni (2023). *Probing RG flows, symmetry resolution and quench dynamics through the capacity of entanglement*. DOI: [10.1007/JHEP03(2023)175](https://doi.org/10.1007/JHEP03(2023)175). URL: <https://arxiv.org/abs/2301.02117v1>.

*Commentary.*

The claim asks whether majorization of two normalized nonnegative weight vectors forces majorization of their normalized spectra in every charge sector having positive weight in both vectors. It is the finite diagonal formal reading of the question left open in Section 7 of the source (arXiv:2301.02117v1, line 4140).

**Theorem 1.3 (A four-level counterexample).**

$$\neg (claim)$$

*Proof.* Machine-checked in Lean as `D5/S3/Entropy/ChargeSectorMajorizationRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/arias-di-giulio-keski-vakkuri-tonni-2023-charge-sector-majorization` (refuted) by `D5/S3/Entropy/ChargeSectorMajorizationRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"arias-di-giulio-keski-vakkuri-tonni-2023-charge-sector-majorization","declaration_gid":"D5/S3/Entropy/ChargeSectorMajorizationRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Raúl Arias; Giuseppe Di Giulio; Esko Keski-Vakkuri; Erik Tonni (2023). *Probing RG flows, symmetry resolution and quench dynamics through the capacity of entanglement*. DOI: [10.1007/JHEP03(2023)175](https://doi.org/10.1007/JHEP03(2023)175). URL: <https://arxiv.org/abs/2301.02117v1>.

*Commentary.*

Use four levels with charge vector (0,0,1,1), r=(6/20,6/20,7/20,1/20), and s=(7/20,5/20,4/20,4/20). Each vector is nonnegative and sums to one. Their descending spectra are (7,6,6,1)/20 and (7,5,4,4)/20, so the prefix sums establish Majorizes(desc r, desc s).

In charge sector zero both total weights are 3/5. The normalized spectra are therefore (1/2,1/2) and (7/12,5/12). The first prefix inequality required for Majorizes in the proposed direction would be 1/2 ≥ 7/12, which is false. Thus the positive-sector hypotheses hold while the sector majorization conclusion fails, proving ¬claim.

## References

- Truth anchor: `D5/S3/Entropy/ChargeSectorMajorizationRefutation.claim`
- Truth anchor: `D5/S3/Entropy/ChargeSectorMajorizationRefutation.result`
- Truth anchor: `D5/S3/Entropy/ChargeSectorMajorizationRefutation.sectorSpectrum`
- Dependency: [D5/S3/Entropy/Forgetting/CapacityMonotone](Forgetting/CapacityMonotone.md)
- Dependency: [D5/S3/Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing](../Geometry/AlphaGeometry/PositiveSimplexGeometryAndMixing.md)
- Dependency: [D5/S3/Quantum/Matrix/LinDTIMajorizationRefutation](../Quantum/Matrix/LinDTIMajorizationRefutation.md)
