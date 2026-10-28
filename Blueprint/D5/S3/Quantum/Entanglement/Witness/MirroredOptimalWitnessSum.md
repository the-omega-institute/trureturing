# Optimal witnesses with an optimal sum

## Abstract

Distinct optimal witnesses have an optimal sum and overlapping detection sets.

**Definition 1.1 (Entanglement witnesses).**

$$\forall (d : \mathbb{N}), (\forall (A : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{IsWitness}\left(A\right)) \Leftrightarrow ((\operatorname{IsHermitian}\left(A\right)) \land ((\operatorname{blockPositive}\left(A\right)) \land (\exists (\rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{IsDensity}\left(\rho\right)) \land (\operatorname{re}\left(\operatorname{trace}\left(A \cdot \rho\right)\right) < (0 : \mathbb{R}))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.IsWitness` (`✓ std3`).

*Citation.* Jiheon Seong; Anindita Bera; Beatrix C. Hiesmayr; Dariusz Chruściński; Joonwoo Bae (2026). *Mirrored entanglement witnesses for multipartite and high-dimensional quantum systems*. DOI: [10.1088/2058-9565/ae30a3](https://doi.org/10.1088/2058-9565/ae30a3). URL: <https://arxiv.org/abs/2510.06863v2>.

*Commentary.*

An entanglement witness A is a Hermitian operator on the tensor product of two d-dimensional complex spaces. It is block positive, meaning that its complex expectation is nonnegative on every product vector, and it has strictly negative real trace pairing with some density matrix ρ. IsDensity means positive semidefinite with trace one. This is the witness notion in mn_revision_clean.tex, lines 276–281, with nonnegativity on separable states expressed as block positivity.

**Definition 1.2 (The detection set).**

$$\forall (d : \mathbb{N}), (\forall (A : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), (\forall (\rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{Detects}\left(A, \rho\right)) \Leftrightarrow ((\operatorname{IsDensity}\left(\rho\right)) \land (\operatorname{re}\left(\operatorname{trace}\left(A \cdot \rho\right)\right) < (0 : \mathbb{R}))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.Detects` (`✓ std3`).

*Citation.* Jiheon Seong; Anindita Bera; Beatrix C. Hiesmayr; Dariusz Chruściński; Joonwoo Bae (2026). *Mirrored entanglement witnesses for multipartite and high-dimensional quantum systems*. DOI: [10.1088/2058-9565/ae30a3](https://doi.org/10.1088/2058-9565/ae30a3). URL: <https://arxiv.org/abs/2510.06863v2>.

*Commentary.*

Detects A ρ means that ρ is a density matrix and the real part of the trace of Aρ is strictly negative. It expresses membership in the detection set defined in mn_revision_clean.tex, lines 392–396. The predicate itself places no Hermiticity or block positivity condition on A.

**Definition 1.3 (Optimality under positive subtraction).**

$$\forall (d : \mathbb{N}), (\forall (A : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{IsOptimalWitness}\left(A\right)) \Leftrightarrow ((\operatorname{IsWitness}\left(A\right)) \land (\forall (\varepsilon : \mathbb{R}), (((0 : \mathbb{R}) < \varepsilon) \Rightarrow (\forall (P : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{PosSemidef}\left(P\right)) \Rightarrow ((P \ne (0 : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right))) \Rightarrow (\neg (\operatorname{blockPositive}\left(A - ((\operatorname{Complex.ofReal}\left(\varepsilon\right) : \mathbb{C})) \cdot (P)\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.IsOptimalWitness` (`✓ std3`).

*Citation.* Jiheon Seong; Anindita Bera; Beatrix C. Hiesmayr; Dariusz Chruściński; Joonwoo Bae (2026). *Mirrored entanglement witnesses for multipartite and high-dimensional quantum systems*. DOI: [10.1088/2058-9565/ae30a3](https://doi.org/10.1088/2058-9565/ae30a3). URL: <https://arxiv.org/abs/2510.06863v2>.

*Commentary.*

An optimal witness is an entanglement witness A for which every positive real ε and every nonzero positive semidefinite operator P make A − εP fail block positivity. The real scalar ε is explicitly included in the complex numbers before scalar multiplication. This expresses the absence of a positive subtraction improving a witness in mn_revision_clean.tex, lines 388–396.

**Definition 1.4 (Two optimal witnesses and an optimal sum).**

$$(\operatorname{claim}) \Leftrightarrow (\forall (d : \mathbb{N}), (((3 : \mathbb{N}) \le d) \Rightarrow (\exists (W : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), (\exists (M : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{IsOptimalWitness}\left(W\right)) \land ((\operatorname{IsOptimalWitness}\left(M\right)) \land ((\operatorname{IsOptimalWitness}\left(W + M\right)) \land ((\exists (\rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{Detects}\left(W, \rho\right)) \land (\neg (\operatorname{Detects}\left(M, \rho\right))))) \land ((\exists (\rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{Detects}\left(M, \rho\right)) \land (\neg (\operatorname{Detects}\left(W, \rho\right))))) \land (\exists (\rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{Detects}\left(W, \rho\right)) \land (\operatorname{Detects}\left(M, \rho\right)))))))))))))$$

*Formalization.* `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jiheon Seong; Anindita Bera; Beatrix C. Hiesmayr; Dariusz Chruściński; Joonwoo Bae (2026). *Mirrored entanglement witnesses for multipartite and high-dimensional quantum systems*. DOI: [10.1088/2058-9565/ae30a3](https://doi.org/10.1088/2058-9565/ae30a3). URL: <https://arxiv.org/abs/2510.06863v2>.

*Commentary.*

Generalized mirroring is the relation W + M = K in mn_revision_clean.tex, lines 1688–1696. The question in line 1749 asks whether W, M and K can all be optimal witnesses. The displayed assertion requires such a pair in every local dimension d at least three, together with a state detected only by W, a state detected only by M, and a state detected by both. Thus the two detection sets are incomparable and have nonempty intersection.

**Theorem 1.5 (A common spanning family gives an optimal sum).**

$$\forall (d : \mathbb{N}), (((3 : \mathbb{N}) \le d) \Rightarrow (\exists (W : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), (\exists (M : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{IsOptimalWitness}\left(W\right)) \land ((\operatorname{IsOptimalWitness}\left(M\right)) \land ((\operatorname{IsOptimalWitness}\left(W + M\right)) \land ((\exists (\rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{Detects}\left(W, \rho\right)) \land (\neg (\operatorname{Detects}\left(M, \rho\right))))) \land ((\exists (\rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{Detects}\left(M, \rho\right)) \land (\neg (\operatorname{Detects}\left(W, \rho\right))))) \land (\exists (\rho : \operatorname{Matrix}\left((\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), (\operatorname{Fin}\left(d\right) \times \operatorname{Fin}\left(d\right)), \mathbb{C}\right)), ((\operatorname{Detects}\left(W, \rho\right)) \land (\operatorname{Detects}\left(M, \rho\right))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.result` (`✓ std3`). ∎

*Resolves.* `Problems/seong-bae-2026-optimal-mirrored-witness-sum` (proved) by `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"seong-bae-2026-optimal-mirrored-witness-sum","declaration_gid":"D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jiheon Seong; Anindita Bera; Beatrix C. Hiesmayr; Dariusz Chruściński; Joonwoo Bae (2026). *Mirrored entanglement witnesses for multipartite and high-dimensional quantum systems*. DOI: [10.1088/2058-9565/ae30a3](https://doi.org/10.1088/2058-9565/ae30a3). URL: <https://arxiv.org/abs/2510.06863v2>.

*Commentary.*

For a nonzero index r in Fin d, let Aᵣ have four nonzero entries: +1 at (0r,0r) and (r0,r0), and −1 at (00,rr) and (rr,00). Let ψᵣ = (|00⟩ + |rr⟩)/√2. Swapping the two negative entries under conjugate transpose proves that Aᵣ is Hermitian. Its quadratic form at a vector v is |v(0,r)|² + |v(r,0)|² − conjugate(v(0,0))v(r,r) − conjugate(v(r,r))v(0,0). For v = x ⊗ y this equals |x(0)conjugate(y(r)) − x(r)conjugate(y(0))|², proving block positivity.

The two distinct coordinate vectors in ψᵣ are orthogonal, so the outer product ψᵣψᵣ* is positive semidefinite with trace one. The rank-one trace identity converts its trace pairing with Aᵣ to the quadratic form above. For any index s this pairing with ψₛψₛ* is −1 if r = s and zero otherwise; the computation uses that the complex image of √2 is nonzero and has square two. The maximally entangled vector Ω = d⁻¹⁄² ∑ᵢ |ii⟩ also defines a density matrix ΩΩ*. Its trace pairing with each Aᵣ is −2/d, using that the complex image of √d is nonzero and has square d.

Next the conjugate product vectors x ⊗ conjugate(x) span the whole complex tensor product. To see this, put q(x) = x ⊗ conjugate(x). Polarization gives x ⊗ conjugate(y) = (q(x + y) − q(x) − q(y) + i(q(x + iy) − q(x) − q(y)))/2. Taking x and y to be coordinate vectors therefore puts every coordinate vector |ij⟩ in the span of the q(x). Expanding an arbitrary vector in those coordinate vectors proves the spanning assertion.

For any witness A with a spanning set S of zero product vectors, suppose ε > 0, P is positive semidefinite and A − εP is block positive. At each v in S, block positivity gives 0 ≤ −ε⟨v,Pv⟩, while positive semidefiniteness gives ⟨v,Pv⟩ ≥ 0. The imaginary part is zero and the real part must vanish. The zero quadratic form criterion for a positive semidefinite matrix then gives Pv = 0. Since S spans, the linear map defined by P is zero, hence P = 0. This excludes every nonzero such P.

For each Aᵣ the product expectation vanishes at every q(x) = x ⊗ conjugate(x), since x(0)x(r) − x(r)x(0) = 0. The negative pairing −2/d with ΩΩ* makes Aᵣ a witness, and the spanning zero vectors make it optimal. For nonzero r and s, Aᵣ + Aₛ is Hermitian and block positive by addition, and its pairing with ΩΩ* is −4/d. The same spanning product vectors have zero expectation for the sum, so the sum is optimal as well.

If r and s are distinct and nonzero, ψᵣψᵣ* has pairings (−1,0) with (Aᵣ,Aₛ), and ψₛψₛ* has pairings (0,−1). They give a state in each difference of detection sets. The state ΩΩ* has pairing −2/d with both operators and lies in their intersection. Finally, for d ≥ 3 choose r = 1 and s = 2 in Fin d. These indices are nonzero and distinct. Taking W = Aᵣ and M = Aₛ proves all six conjuncts of claim.

## References

- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.Detects`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.IsOptimalWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.IsWitness`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.claim`
- Truth anchor: `D5/S3/Quantum/Entanglement/Witness/MirroredOptimalWitnessSum.result`
- Dependency: [D5/S3/Observer/Existence/EmpiricalReflexiveSeparation](../../../Observer/Existence/EmpiricalReflexiveSeparation.md)
- Dependency: [D5/S3/Quantum/Entanglement/ChoiKiemKye/ConstructionReduction](../ChoiKiemKye/ConstructionReduction.md)
- Dependency: [D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation](../WitnessKernelTraceCriteriaRefutation.md)
- Dependency: [D5/S3/Quantum/Information/SLDSpectralEnergy](../../Information/SLDSpectralEnergy.md)
- Dependency: [D5/S3/Quantum/QuantumChannels/TwoPositiveTransitionTrace](../../QuantumChannels/TwoPositiveTransitionTrace.md)
- Dependency: [D5/S3/Quantum/Reduction/FiniteEdgeProbeCorrespondence](../../Reduction/FiniteEdgeProbeCorrespondence.md)
- Dependency: [D5/S3/QuantumBounds/PeritoTsirelson](../../../QuantumBounds/PeritoTsirelson.md)
