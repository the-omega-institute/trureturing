# LDPC bounds for monic CSS pushouts

## Abstract

Basis-preserving monic pushouts of length-two binary CSS complexes satisfy explicit row and column weight bounds.

**Definition 1.1 (Based length-two complex).**

$$\mathrm{BasedComplex} = \{dim:\operatorname{Fin}\left(3\right) \to \mathbb{N}; d2:\operatorname{Matrix}\left(\operatorname{Fin}\left(dim\left(1\right)\right), \operatorname{Fin}\left(dim\left(2\right)\right), \operatorname{ZMod}\left(2\right)\right); d1:\operatorname{Matrix}\left(\operatorname{Fin}\left(dim\left(0\right)\right), \operatorname{Fin}\left(dim\left(1\right)\right), \operatorname{ZMod}\left(2\right)\right); comp:d1 \cdot d2 = 0\}$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.BasedComplex` (`✓ std3`).

*Citation.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

A based complex has finite bases in degrees zero, one and two, two binary matrix differentials, and their composite is zero.

**Definition 1.2 (Basis matrix).**

$$\forall m \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall phi \in \operatorname{Fin}\left(m\right) \to \operatorname{Fin}\left(n\right),\; \operatorname{basisMatrix}\left(phi\right) = \lambda j \mapsto \lambda a \mapsto \operatorname{ite}\left(phi\left(a\right) = j, 1, 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.basisMatrix` (`✓ std3`).

*Citation.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

The matrix has a one in the row selected by the image of a basis element and zero elsewhere.

**Definition 1.3 (Basis-preserving chain map).**

$$\forall A \in \mathrm{BasedComplex},\; \forall C \in \mathrm{BasedComplex},\; \operatorname{BPChainMap}\left(A, C\right) = \{f:\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{Fin}\left(\operatorname{dim}\left(A\right)\left(i\right)\right) \to \operatorname{Fin}\left(\operatorname{dim}\left(C\right)\left(i\right)\right); comm2:\operatorname{d2}\left(C\right) \cdot \operatorname{basisMatrix}\left(f\left(2\right)\right) = \operatorname{basisMatrix}\left(f\left(1\right)\right) \cdot \operatorname{d2}\left(A\right); comm1:\operatorname{d1}\left(C\right) \cdot \operatorname{basisMatrix}\left(f\left(1\right)\right) = \operatorname{basisMatrix}\left(f\left(0\right)\right) \cdot \operatorname{d1}\left(A\right)\}$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.BPChainMap` (`✓ std3`).

*Citation.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

A basis-preserving chain map consists of basis functions in all three degrees whose matrices commute with both differentials.

**Definition 1.4 (Monic basis-preserving map).**

$$\forall A \in \mathrm{BasedComplex},\; \forall C \in \mathrm{BasedComplex},\; \forall phi \in \operatorname{BPChainMap}\left(A, C\right),\; \operatorname{BPChainMap.Monic}\left(phi\right) \Leftrightarrow (\forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{Injective}\left(\operatorname{mulVec}\left(\operatorname{basisMatrix}\left(\operatorname{f}\left(phi, i\right)\right)\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.Monic` (`✓ std3`).

*Citation.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

Monicity is degreewise injectivity of the induced matrix maps.

**Definition 1.5 (Pushout identification).**

$$\forall A \in \mathrm{BasedComplex},\; \forall C \in \mathrm{BasedComplex},\; \forall D \in \mathrm{BasedComplex},\; \forall phi \in \operatorname{BPChainMap}\left(A, C\right),\; \forall psi \in \operatorname{BPChainMap}\left(A, D\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; \forall x \in \operatorname{Sum}\left(\operatorname{Fin}\left(\operatorname{dim}\left(C\right)\left(i\right)\right), \operatorname{Fin}\left(\operatorname{dim}\left(D\right)\left(i\right)\right)\right),\; \forall y \in \operatorname{Sum}\left(\operatorname{Fin}\left(\operatorname{dim}\left(C\right)\left(i\right)\right), \operatorname{Fin}\left(\operatorname{dim}\left(D\right)\left(i\right)\right)\right),\; \operatorname{glue}\left(phi, psi, i\right)\left(x, y\right) \Leftrightarrow (\exists a \in \operatorname{Fin}\left(\operatorname{dim}\left(A\right)\left(i\right)\right),\; (x = \operatorname{inl}\left(\operatorname{f}\left(phi, i\right)\left(a\right)\right)) \land (y = \operatorname{inr}\left(\operatorname{f}\left(psi, i\right)\left(a\right)\right)))$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.glue` (`✓ std3`).

*Citation.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

The relation identifies the image of one apex basis element in the left foot with its image in the right foot.

**Definition 1.6 (Pushout basis).**

$$\forall A \in \mathrm{BasedComplex},\; \forall C \in \mathrm{BasedComplex},\; \forall D \in \mathrm{BasedComplex},\; \forall phi \in \operatorname{BPChainMap}\left(A, C\right),\; \forall psi \in \operatorname{BPChainMap}\left(A, D\right),\; \forall i \in \operatorname{Fin}\left(3\right),\; \operatorname{PBasis}\left(phi, psi\right)\left(i\right) = \operatorname{Quot}\left(\operatorname{glue}\left(phi, psi\right)\left(i\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.PBasis` (`✓ std3`).

*Citation.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

The pushout basis is the quotient of the disjoint union by the identification relation.

**Definition 1.7 (Degree-two block differential).**

$$\forall C \in \mathrm{BasedComplex},\; \forall D \in \mathrm{BasedComplex},\; \operatorname{sumD2}\left(C, D\right) = \operatorname{fromBlocks}\left(\operatorname{d2}\left(C\right), 0, 0, \operatorname{d2}\left(D\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.sumD2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

The direct-sum differential is the block diagonal matrix with the two input differentials.

**Definition 1.8 (Degree-one block differential).**

$$\forall C \in \mathrm{BasedComplex},\; \forall D \in \mathrm{BasedComplex},\; \operatorname{sumD1}\left(C, D\right) = \operatorname{fromBlocks}\left(\operatorname{d1}\left(C\right), 0, 0, \operatorname{d1}\left(D\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.sumD1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

The direct-sum differential is the block diagonal matrix with the two input differentials.

**Definition 1.9 (Degree-two pushout differential).**

$$\forall A \in \mathrm{BasedComplex},\; \forall C \in \mathrm{BasedComplex},\; \forall D \in \mathrm{BasedComplex},\; \forall phi \in \operatorname{BPChainMap}\left(A, C\right),\; \forall psi \in \operatorname{BPChainMap}\left(A, D\right),\; \operatorname{pushoutD2}\left(phi, psi\right) = \lambda (X:\operatorname{PBasis}\left(phi, psi, 1\right)) \mapsto \lambda (Y:\operatorname{PBasis}\left(phi, psi, 2\right)) \mapsto \operatorname{Finset.sum}\left(\operatorname{filter}\left(\lambda x \mapsto \operatorname{Quot.mk}\left(\operatorname{glue}\left(phi, psi, 1\right), x\right) = X, \operatorname{Finset.univ}\right), \lambda x \mapsto \operatorname{sumD2}\left(C, D\right)\left(x, \operatorname{Quot.out}\left(Y\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.pushoutD2` (`✓ std3`).

*Citation.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

Each output coefficient is the sum of the selected representative coefficients over its quotient class.

**Definition 1.10 (Degree-one pushout differential).**

$$\forall A \in \mathrm{BasedComplex},\; \forall C \in \mathrm{BasedComplex},\; \forall D \in \mathrm{BasedComplex},\; \forall phi \in \operatorname{BPChainMap}\left(A, C\right),\; \forall psi \in \operatorname{BPChainMap}\left(A, D\right),\; \operatorname{pushoutD1}\left(phi, psi\right) = \lambda (X:\operatorname{PBasis}\left(phi, psi, 0\right)) \mapsto \lambda (Y:\operatorname{PBasis}\left(phi, psi, 1\right)) \mapsto \operatorname{Finset.sum}\left(\operatorname{filter}\left(\lambda x \mapsto \operatorname{Quot.mk}\left(\operatorname{glue}\left(phi, psi, 0\right), x\right) = X, \operatorname{Finset.univ}\right), \lambda x \mapsto \operatorname{sumD1}\left(C, D\right)\left(x, \operatorname{Quot.out}\left(Y\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.pushoutD1` (`✓ std3`).

*Citation.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

Each output coefficient is the sum of the selected representative coefficients over its quotient class.

**Definition 1.11 (Maximum row weight).**

$$\forall I \in \operatorname{Type},\; \forall K \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{Fintype}\left(K\right)] \forall M \in \operatorname{Matrix}\left(I, K, \operatorname{ZMod}\left(2\right)\right),\; \operatorname{maxRowWeight}\left(M\right) = \operatorname{sup}\left(\operatorname{Finset.univ}, \lambda i \mapsto \operatorname{card}\left(\operatorname{filter}\left(\lambda j \mapsto M\left(i, j\right) \ne 0, \operatorname{Finset.univ}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.maxRowWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

The maximum row weight is the finite supremum of the cardinalities of nonzero row supports.

**Definition 1.12 (Maximum column weight).**

$$\forall I \in \operatorname{Type},\; \forall K \in \operatorname{Type},\; [\operatorname{Fintype}\left(I\right)] [\operatorname{Fintype}\left(K\right)] \forall M \in \operatorname{Matrix}\left(I, K, \operatorname{ZMod}\left(2\right)\right),\; \operatorname{maxColWeight}\left(M\right) = \operatorname{maxRowWeight}\left(\operatorname{transpose}\left(M\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.maxColWeight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

The maximum column weight is the maximum row weight of the transpose.

**Definition 1.13 (Uniform LDPC family).**

$$\forall d2w \in \mathbb{N} \to \operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right),\; \forall d1w \in \mathbb{N} \to \operatorname{Prod}\left(\mathbb{N}, \mathbb{N}\right),\; \operatorname{IsLDPC}\left(d2w, d1w\right) \Leftrightarrow (\exists w \in \mathbb{N},\; \forall n \in \mathbb{N},\; (\operatorname{fst}\left(d2w\left(n\right)\right) \le w) \land ((\operatorname{snd}\left(d2w\left(n\right)\right) \le w) \land ((\operatorname{fst}\left(d1w\left(n\right)\right) \le w) \land (\operatorname{snd}\left(d1w\left(n\right)\right) \le w))))$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.IsLDPC` (`✓ std3`).

*Citation.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

One natural-number bound controls both row and column weights of both differentials at every family index.

**Definition 1.14 (Degree-two weights).**

$$\forall E \in \mathrm{BasedComplex},\; \operatorname{weights2}\left(E\right) = (\operatorname{maxRowWeight}\left(\operatorname{d2}\left(E\right)\right), \operatorname{maxColWeight}\left(\operatorname{d2}\left(E\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.weights2` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

The pair records maximum row and column weights of the degree-two differential.

**Definition 1.15 (Degree-one weights).**

$$\forall E \in \mathrm{BasedComplex},\; \operatorname{weights1}\left(E\right) = (\operatorname{maxRowWeight}\left(\operatorname{d1}\left(E\right)\right), \operatorname{maxColWeight}\left(\operatorname{d1}\left(E\right)\right))$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.weights1` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

The pair records maximum row and column weights of the degree-one differential.

**Definition 1.16 (Cowtan--Burton Conjecture D.1).**

$$claim = (\forall A \in \mathbb{N} \to \mathrm{BasedComplex},\; \forall C \in \mathbb{N} \to \mathrm{BasedComplex},\; \forall D \in \mathbb{N} \to \mathrm{BasedComplex},\; \forall phi \in \left(\forall n \in \mathbb{N},\; \operatorname{BPChainMap}\left(A\left(n\right), C\left(n\right)\right)\right),\; \forall psi \in \left(\forall n \in \mathbb{N},\; \operatorname{BPChainMap}\left(A\left(n\right), D\left(n\right)\right)\right),\; (\forall n \in \mathbb{N},\; \operatorname{BPChainMap.Monic}\left(phi\left(n\right)\right)) \Rightarrow ((\forall n \in \mathbb{N},\; \operatorname{BPChainMap.Monic}\left(psi\left(n\right)\right)) \Rightarrow ((\operatorname{IsLDPC}\left(\lambda n \mapsto \operatorname{weights2}\left(A\left(n\right)\right), \lambda n \mapsto \operatorname{weights1}\left(A\left(n\right)\right)\right)) \Rightarrow ((\operatorname{IsLDPC}\left(\lambda n \mapsto \operatorname{weights2}\left(C\left(n\right)\right), \lambda n \mapsto \operatorname{weights1}\left(C\left(n\right)\right)\right)) \Rightarrow ((\operatorname{IsLDPC}\left(\lambda n \mapsto \operatorname{weights2}\left(D\left(n\right)\right), \lambda n \mapsto \operatorname{weights1}\left(D\left(n\right)\right)\right)) \Rightarrow (\operatorname{IsLDPC}\left(\lambda n \mapsto (\operatorname{maxRowWeight}\left(\operatorname{pushoutD2}\left(phi\left(n\right), psi\left(n\right)\right)\right), \operatorname{maxColWeight}\left(\operatorname{pushoutD2}\left(phi\left(n\right), psi\left(n\right)\right)\right)), \lambda n \mapsto (\operatorname{maxRowWeight}\left(\operatorname{pushoutD1}\left(phi\left(n\right), psi\left(n\right)\right)\right), \operatorname{maxColWeight}\left(\operatorname{pushoutD1}\left(phi\left(n\right), psi\left(n\right)\right)\right))\right)))))))$$

*Formalization.* `D5/S3/Quantum/Information/CssMonicPushoutLdpc.claim` (`✓ std3`).

*Citation.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

Conjecture D.1 (Appendix D, p. 18): "Let C• ←f• A• →g• D• be a basis-preserving monic span in Ch(MatF2), and let Q• be the pushout chain complex of this monic span. Further, let the monic span be a representative of a family of monic spans which are parameterised by some n ∈ ℕ, and let A•, C• and D• be the Z-type complexes of quantum LDPC codes. Then (Q•, Q•) is also LDPC." The Lean proposition expands the source objects and counts.

**Theorem 1.17 (The proved LDPC closure).**

$$\forall A \in \mathbb{N} \to \mathrm{BasedComplex},\; \forall C \in \mathbb{N} \to \mathrm{BasedComplex},\; \forall D \in \mathbb{N} \to \mathrm{BasedComplex},\; \forall phi \in \left(\forall n \in \mathbb{N},\; \operatorname{BPChainMap}\left(A\left(n\right), C\left(n\right)\right)\right),\; \forall psi \in \left(\forall n \in \mathbb{N},\; \operatorname{BPChainMap}\left(A\left(n\right), D\left(n\right)\right)\right),\; (\forall n \in \mathbb{N},\; \operatorname{BPChainMap.Monic}\left(phi\left(n\right)\right)) \Rightarrow ((\forall n \in \mathbb{N},\; \operatorname{BPChainMap.Monic}\left(psi\left(n\right)\right)) \Rightarrow ((\operatorname{IsLDPC}\left(\lambda n \mapsto \operatorname{weights2}\left(A\left(n\right)\right), \lambda n \mapsto \operatorname{weights1}\left(A\left(n\right)\right)\right)) \Rightarrow ((\operatorname{IsLDPC}\left(\lambda n \mapsto \operatorname{weights2}\left(C\left(n\right)\right), \lambda n \mapsto \operatorname{weights1}\left(C\left(n\right)\right)\right)) \Rightarrow ((\operatorname{IsLDPC}\left(\lambda n \mapsto \operatorname{weights2}\left(D\left(n\right)\right), \lambda n \mapsto \operatorname{weights1}\left(D\left(n\right)\right)\right)) \Rightarrow (\operatorname{IsLDPC}\left(\lambda n \mapsto (\operatorname{maxRowWeight}\left(\operatorname{pushoutD2}\left(phi\left(n\right), psi\left(n\right)\right)\right), \operatorname{maxColWeight}\left(\operatorname{pushoutD2}\left(phi\left(n\right), psi\left(n\right)\right)\right)), \lambda n \mapsto (\operatorname{maxRowWeight}\left(\operatorname{pushoutD1}\left(phi\left(n\right), psi\left(n\right)\right)\right), \operatorname{maxColWeight}\left(\operatorname{pushoutD1}\left(phi\left(n\right), psi\left(n\right)\right)\right))\right))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/CssMonicPushoutLdpc.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Alexander Cowtan; Simon Burton (2024). *CSS code surgery as a universal construction*. DOI: [10.22331/q-2024-05-14-1344](https://doi.org/10.22331/q-2024-05-14-1344). URL: <https://arxiv.org/abs/2301.13738v6>.

*Commentary.*

Monicity makes each quotient fibre contain at most one basis element from either foot. A column support injects into one input column, while a row support injects into the disjoint union of one row from each foot. Thus the column bound is the maximum of the two input column weights and the row bound is their sum. Applying these bounds pointwise gives the uniform family bound with constant wC + wD; no bound on the apex is required.

## References

- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.BPChainMap`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.BasedComplex`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.IsLDPC`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.Monic`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.PBasis`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.basisMatrix`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.claim`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.glue`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.maxColWeight`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.maxRowWeight`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.pushoutD1`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.pushoutD2`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.result`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.sumD1`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.sumD2`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.weights1`
- Truth anchor: `D5/S3/Quantum/Information/CssMonicPushoutLdpc.weights2`
