# A prescribed generalized inverse with no common inner product

## Abstract

The prescribed inverse of a 2-partial isometry need not admit a common inner product.

**Definition 1.1 (The alternating operator sum).**

$$\forall (H: \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)], [\operatorname{CompleteSpace}\left(H\right)], \forall (m: \mathbb{N}), (\forall (T: \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)), (\operatorname{beta}\left(m, T\right) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(m + 1\right)} (((-1: \mathbb{C}))^{m - k} \cdot (\operatorname{Nat}.\operatorname{choose}\left(m, k\right): \mathbb{C})) \cdot ((\operatorname{ContinuousLinearMap}.\operatorname{adjoint}\left(T\right))^{k} \cdot (T)^{k}))))$$

*Formalization.* `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.beta` (`✓ std3`).

*Citation.* Mohamed Amine Aouichaoui, Michał Buchała and Stephan Ramon Garcia (2026). *On m-partial isometries: spectra, weighted shifts, and similarity*. DOI: [10.48550/arXiv.2606.12865](https://doi.org/10.48550/arXiv.2606.12865). URL: <https://arxiv.org/abs/2606.12865v1>.

*Commentary.*

The operator definition preceding equation (2.1), page 2: “For T ∈ B(H) and integer m ≥ 1, define the selfadjoint operator” βₘ(T) := Σₖ₌₀ᵐ (−1)ᵐ⁻ᵏ binom(m,k) T*ᵏTᵏ. The finite sum uses Finset.range (m + 1), so its natural exponents agree with the nonnegative exponents in the paper. The adjoint is computed using the original Hilbert space structure.

**Definition 1.2 (The source operator condition).**

$$\forall (H: \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)], [\operatorname{CompleteSpace}\left(H\right)], \forall (m: \mathbb{N}), (\forall (T: \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)), ((\operatorname{IsMPartialIsometry}\left(m, T\right)) \Leftrightarrow ((1 \le m) \land (T \cdot \operatorname{beta}\left(m, T\right) = 0)))))$$

*Formalization.* `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.IsMPartialIsometry` (`✓ std3`).

*Citation.* Mohamed Amine Aouichaoui, Michał Buchała and Stephan Ramon Garcia (2026). *On m-partial isometries: spectra, weighted shifts, and similarity*. DOI: [10.48550/arXiv.2606.12865](https://doi.org/10.48550/arXiv.2606.12865). URL: <https://arxiv.org/abs/2606.12865v1>.

*Commentary.*

Section 2, page 2: “More generally, T is an m-partial isometry if T βₘ(T) = 0; it is strict if it is not an (m − 1)-partial isometry.” The order restriction m ≥ 1 is included in the predicate.

**Definition 1.3 (The fixed inverse proposed in Question 6).**

$$\forall (H: \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)], [\operatorname{CompleteSpace}\left(H\right)], \forall (T: \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)), (\operatorname{candidateInverse}\left(T\right) = (2: \mathbb{C}) \cdot \operatorname{ContinuousLinearMap}.\operatorname{adjoint}\left(T\right) - (\operatorname{ContinuousLinearMap}.\operatorname{adjoint}\left(T\right))^{2} \cdot T))$$

*Formalization.* `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.candidateInverse` (`✓ std3`).

*Citation.* Mohamed Amine Aouichaoui, Michał Buchała and Stephan Ramon Garcia (2026). *On m-partial isometries: spectra, weighted shifts, and similarity*. DOI: [10.48550/arXiv.2606.12865](https://doi.org/10.48550/arXiv.2606.12865). URL: <https://arxiv.org/abs/2606.12865v1>.

*Commentary.*

Section 6, page 17: “so S = 2T∗ − T∗²T is a generalized inverse for T and ST is the orthogonal projection onto R(T*).” Both occurrences of the adjoint use the original inner product; S stays fixed when the new form is chosen.

**Definition 1.4 (The four equations for one positive definite form).**

$$\forall (H: \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{NormedSpace}\left(\mathbb{C}, H\right)], \forall (g: \operatorname{InnerProductSpace}.\operatorname{Core}\left(\mathbb{C}, H\right)), (\forall (T: \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)), (\forall (S: \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)), ((\operatorname{penroseIn}\left(g, T, S\right)) \Leftrightarrow ((T \cdot S \cdot T = T) \land ((S \cdot T \cdot S = S) \land ((\forall (x: H), (\forall (y: H), (g.\operatorname{inner}\left((T \cdot S)\left(x\right), y\right) = g.\operatorname{inner}\left(x, (T \cdot S)\left(y\right)\right)))) \land (\forall (x: H), (\forall (y: H), (g.\operatorname{inner}\left((S \cdot T)\left(x\right), y\right) = g.\operatorname{inner}\left(x, (S \cdot T)\left(y\right)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.penroseIn` (`✓ std3`).

*Citation.* Mohamed Amine Aouichaoui, Michał Buchała and Stephan Ramon Garcia (2026). *On m-partial isometries: spectra, weighted shifts, and similarity*. DOI: [10.48550/arXiv.2606.12865](https://doi.org/10.48550/arXiv.2606.12865). URL: <https://arxiv.org/abs/2606.12865v1>.

*Commentary.*

The Moore–Penrose condition in Question 6, page 17, is expressed by TST = T, STS = S, and symmetry of TS and ST for the same positive definite complex form g. InnerProductSpace.Core supplies the form without replacing the original norm or adjoint. There is no completeness or norm equivalence condition on the new form.

**Definition 1.5 (Question 6).**

$$(claim) \Leftrightarrow (\forall (H: \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)], [\operatorname{CompleteSpace}\left(H\right)], \forall (T: \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)), ((\operatorname{IsMPartialIsometry}\left(2, T\right)) \Rightarrow (\exists (g: \operatorname{InnerProductSpace}.\operatorname{Core}\left(\mathbb{C}, H\right)), \operatorname{penroseIn}\left(g, T, \operatorname{candidateInverse}\left(T\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.claim` (`✓ std3`).

*Citation.* Mohamed Amine Aouichaoui, Michał Buchała and Stephan Ramon Garcia (2026). *On m-partial isometries: spectra, weighted shifts, and similarity*. DOI: [10.48550/arXiv.2606.12865](https://doi.org/10.48550/arXiv.2606.12865). URL: <https://arxiv.org/abs/2606.12865v1>.

*Commentary.*

Question 6, page 17: “If T is a 2-partial isometry, is 2T∗ − T∗²T the Moore–Penrose inverse of T with respect to some inner product?” H ranges over complex Hilbert spaces, T over bounded complex-linear endomorphisms, and g over positive definite complex inner products on the same vector space. The candidateInverse uses the original adjoints. All four equations use the same g.

**Theorem 1.6 (The answer to Question 6 is negative).**

$$\neg (\forall (H: \operatorname{Type}), ([\operatorname{NormedAddCommGroup}\left(H\right)], [\operatorname{InnerProductSpace}\left(\mathbb{C}, H\right)], [\operatorname{CompleteSpace}\left(H\right)], \forall (T: \operatorname{ContinuousLinearMap}\left(\mathbb{C}, H, H\right)), ((\operatorname{IsMPartialIsometry}\left(2, T\right)) \Rightarrow (\exists (g: \operatorname{InnerProductSpace}.\operatorname{Core}\left(\mathbb{C}, H\right)), \operatorname{penroseIn}\left(g, T, \operatorname{candidateInverse}\left(T\right)\right)))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/op-abg2606q6` (refuted) by `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"op-abg2606q6","declaration_gid":"D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Mohamed Amine Aouichaoui, Michał Buchała and Stephan Ramon Garcia (2026). *On m-partial isometries: spectra, weighted shifts, and similarity*. DOI: [10.48550/arXiv.2606.12865](https://doi.org/10.48550/arXiv.2606.12865). URL: <https://arxiv.org/abs/2606.12865v1>.

*Commentary.*

For r ≥ 2 take a = sqrt(2 − 1/r), b = (r − 1)/sqrt(r), and T = [[a,0],[b,0]] on EuclideanSpace ℂ (Fin 2). The relations a² + b² = r and a²r = 2r − 1 give IsMPartialIsometry 2 T. With S = candidateInverse T, ST fixes the first coordinate and kills the second. Its symmetry forces the coordinate vectors to be orthogonal for g. Symmetry of TS then forces 2ab p = ab(2 − r) q, where p and q are the squared lengths of those vectors. Positivity contradicts this equation. The proof specializes r to 25.

## References

- Truth anchor: `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.IsMPartialIsometry`
- Truth anchor: `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.beta`
- Truth anchor: `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.candidateInverse`
- Truth anchor: `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.claim`
- Truth anchor: `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.penroseIn`
- Truth anchor: `D5/S3/Quantum/MatrixAnalysis/MPartialIsometryCommonMetricInverseRefutation.result`
