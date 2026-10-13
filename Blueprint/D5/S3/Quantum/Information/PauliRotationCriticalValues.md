# Pauli rotations with a hypersurface of critical values

## Abstract

A product of fifteen two-qubit Pauli rotations has full derivative rank almost everywhere, while its critical values have Hausdorff dimension at least fourteen.

**Definition 1.1 (Two-qubit basis labels).**

$$\operatorname{BasisState} = \left(\operatorname{Fin}\left(2\right) \to \operatorname{Fin}\left(2\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/PauliRotationCriticalValues.BasisState` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A basis label assigns a bit to each of the two qubits. There are four labels.

**Definition 1.2 (Complex matrices on two qubits).**

$$\operatorname{Mat} = \operatorname{Matrix}\left(\operatorname{BasisState}, \operatorname{BasisState}, \mathbb{C}\right)$$

*Formalization.* `D5/S3/Quantum/Information/PauliRotationCriticalValues.Mat` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rows and columns are indexed by BasisState, so Mat is the space of four-by-four complex matrices. The matrix norm is the Frobenius norm.

**Definition 1.3 (Fifteen real rotation angles).**

$$\operatorname{Param} = \left(\operatorname{Fin}\left(15\right) \to \mathbb{R}\right)$$

*Formalization.* `D5/S3/Quantum/Information/PauliRotationCriticalValues.Param` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The fifteen coordinates are independent real angles, indexed from zero through fourteen.

**Definition 1.4 (Nonidentity two-qubit Pauli words).**

$$\operatorname{NonIdentityPauli} = \{p : \operatorname{Fin}\left(2\right) \to \operatorname{Pauli} // p \ne (\operatorname{Function.const}\left(\operatorname{Fin}\left(2\right), \operatorname{Pauli.I}\right))\}$$

*Formalization.* `D5/S3/Quantum/Information/PauliRotationCriticalValues.NonIdentityPauli` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Pauli has the four letters Pauli.I, Pauli.X, Pauli.Y and Pauli.Z. Excluding the constant identity word leaves fifteen words. Function.const(Fin 2, Pauli.I) is the function assigning Pauli.I to both qubits.

**Definition 1.5 (A Pauli rotation).**

$$\forall (p : \operatorname{NonIdentityPauli}), \forall (a : \mathbb{R}), \operatorname{rotation}\left(p, a\right) = \operatorname{SMul.smul}\left(\operatorname{Real.cos}\left(\frac{a}{2}\right), (1 : \operatorname{Mat})\right) - \operatorname{SMul.smul}\left(\operatorname{Real.sin}\left(\frac{a}{2}\right), \operatorname{SMul.smul}\left(\operatorname{Complex.I}, \operatorname{wordOp}\left(p.\operatorname{val}\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/PauliRotationCriticalValues.rotation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

wordOp takes the tensor product of the two Pauli matrices. SMul.smul is scalar multiplication: Real.cos and Real.sin act as real scalars on Mat, while Complex.I acts as a complex scalar. The typed 1 is the identity matrix. This is the rotation with generator wordOp(p.val) and angle a.

**Definition 1.6 (The ordered product of fifteen rotations).**

$$\forall (P : \operatorname{Fin}\left(15\right) \to \operatorname{NonIdentityPauli}), \forall (\alpha : \operatorname{Param}), \operatorname{circuit}\left(P, \alpha\right) = (\operatorname{List.ofFn}\left(\operatorname{fun} (j : \operatorname{Fin}\left(15\right)) \mapsto \operatorname{rotation}\left(P\left(j\right), \alpha\left(j\right)\right)\right)).\operatorname{prod}$$

*Formalization.* `D5/S3/Quantum/Information/PauliRotationCriticalValues.circuit` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

List.ofFn lists the rotations in increasing Fin 15 order, and List.prod multiplies them from left to right. Each coordinate feeds into exactly one rotation. The sequence P may repeat words.

**Definition 1.7 (Real rank of the circuit derivative).**

$$\forall (P : \operatorname{Fin}\left(15\right) \to \operatorname{NonIdentityPauli}), \forall (\alpha : \operatorname{Param}), \operatorname{derivativeRank}\left(P, \alpha\right) = \operatorname{Module.finrank}\left(\mathbb{R}, \operatorname{LinearMap.range}\left((\operatorname{fderiv}\left(\mathbb{R}, \operatorname{circuit}\left(P\right), \alpha\right)).\operatorname{toLinearMap}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/PauliRotationCriticalValues.derivativeRank` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

fderiv is the Frechet derivative over the real numbers. Its toLinearMap projection has a real vector-space range, whose Module.finrank is the rank. The domain has real dimension fifteen.

**Definition 1.8 (Parameters of deficient derivative rank).**

$$\forall (P : \operatorname{Fin}\left(15\right) \to \operatorname{NonIdentityPauli}), \operatorname{critical}\left(P\right) = \{\alpha : \operatorname{Param} \mid \operatorname{derivativeRank}\left(P, \alpha\right) < 15\}$$

*Formalization.* `D5/S3/Quantum/Information/PauliRotationCriticalValues.critical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The critical set consists of the parameters where the real derivative rank is strictly less than fifteen. Its image under circuit is the set of critical values.

**Definition 1.9 (Conjecture 3 in the two-qubit case).**

$$\operatorname{claim} \Leftrightarrow (\forall (P : \operatorname{Fin}\left(15\right) \to \operatorname{NonIdentityPauli}), (\left(\forall^{\mathrm{m}}\right)_{(\operatorname{volume} : \operatorname{Measure}\left(\operatorname{Param}\right))} (\alpha : \operatorname{Param}), \operatorname{derivativeRank}\left(P, \alpha\right) = 15) \Rightarrow \operatorname{dimH}\left((\operatorname{circuit}\left(P\right) '' \operatorname{critical}\left(P\right))\right) \le (13 : \left(\mathbb{R}_{\geq 0}\right)^{\infty}))$$

*Formalization.* `D5/S3/Quantum/Information/PauliRotationCriticalValues.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* D. Wierichs; K. Kottmann; N. Killoran (2025). *Unitary synthesis with optimal brick wall circuits*. DOI: [10.48550/arXiv.2511.16736](https://doi.org/10.48550/arXiv.2511.16736). URL: <https://arxiv.org/abs/2511.16736v1>.

*Commentary.*

Wierichs, Kottmann and Killoran, Conjecture 3, §V, p. 9: "The critical values F(C) of a PQC that has full rank almost everywhere in T^d form an at most (d−2)-dimensional subset of G." Here d = 15 and G is SU(4), represented by its complex matrices. The displayed proposition quantifies over every sequence of fifteen nonidentity two-qubit Pauli words. Its premise uses Lebesgue volume on Param, and its conclusion uses the Hausdorff dimension dimH of the actual matrix image. The measure beneath the almost-everywhere quantifier is explicit; this is Lean's notation ∀ᵐ with volume. Real angles give the periodic lift of the circuit parameters. Each Pauli-word rotation is a Clifford conjugate of a single-qubit Pauli rotation, so the ordered product is a parametrized quantum circuit with fifteen independent inputs.

**Remark 1.10 (A nonzero real-analytic function has a null zero set).**

$$
\forall (n : \mathbb{N}), \forall (f : \left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right) \to \mathbb{R}), \forall (a : \operatorname{Fin}\left(n\right) \to \mathbb{R}), (\operatorname{AnalyticOnNhd}\left(\mathbb{R}, f, \operatorname{Set.univ}\right) \land f\left(a\right) \ne 0) \Rightarrow \left(\forall^{\mathrm{m}}\right)_{(\operatorname{volume} : \operatorname{Measure}\left(\operatorname{Fin}\left(n\right) \to \mathbb{R}\right))} (x : \operatorname{Fin}\left(n\right) \to \mathbb{R}), f\left(x\right) \ne 0
$$

*Citation.* B. S. Mityagin (2015). *The zero set of a real analytic function*. DOI: [10.48550/arXiv.1512.07276](https://doi.org/10.48550/arXiv.1512.07276). URL: <https://arxiv.org/abs/1512.07276v1>.

*Commentary.*

Mityagin, Proposition 0, p. 1: the zero set of a real-analytic function that is not identically zero on a connected open real domain has Lebesgue measure zero. Here the domain is the whole finite-dimensional real coordinate space. AnalyticOnNhd supplies real analyticity everywhere, and a point a with f(a) nonzero supplies nontriviality. The conclusion says f(x) is nonzero for volume-almost every x. It holds also in dimension zero.

**Theorem 1.11 (The critical-value bound fails).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/PauliRotationCriticalValues.result` (`✓ std3`). ∎

*Resolves.* `Problems/wierichs-kottmann-killoran-2025-critical-values` (refuted) by `D5/S3/Quantum/Information/PauliRotationCriticalValues.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"wierichs-kottmann-killoran-2025-critical-values","declaration_gid":"D5/S3/Quantum/Information/PauliRotationCriticalValues.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* D. Wierichs; K. Kottmann; N. Killoran (2025). *Unitary synthesis with optimal brick wall circuits*. DOI: [10.48550/arXiv.2511.16736](https://doi.org/10.48550/arXiv.2511.16736). URL: <https://arxiv.org/abs/2511.16736v1>.

*Commentary.*

In increasing input order choose the words YY, IY, XX, ZY, ZX, IZ, XY, YZ, IX, XZ, ZI, YI, YX, XI, ZZ, where AB means the tensor product of the Pauli matrices A and B. Set inputs 5, 6, 7 and 10 to π/4 and all other inputs to zero; indices start at zero. At this parameter the derivative has rank fourteen. In invertible real coordinates its Pauli-coordinate matrix is diagonal with fourteen ones and one zero. The derivative of its determinant along a nonzero kernel direction is nonzero. This is the fold condition: the kernel is transverse to the critical hypersurface. A linear projection of the critical values contains a nonempty open subset of the fourteen-dimensional real space. Lipschitz monotonicity of dimH therefore gives Hausdorff dimension at least fourteen, contradicting the bound thirteen. AnalyticZeroSetNull.ae_ne_zero_of_analytic gives the almost-everywhere full-rank step: the determinant is real analytic and its nonzero directional derivative prevents it from vanishing identically. Mityagin, Proposition 0, p. 1, states that such a zero set on a connected open real domain has Lebesgue measure zero. Thus the same sequence has full derivative rank almost everywhere and violates the proposed critical-value dimension bound.

## References

- Truth anchor: `D5/S3/Quantum/Information/PauliRotationCriticalValues.BasisState`
- Truth anchor: `D5/S3/Quantum/Information/PauliRotationCriticalValues.Mat`
- Truth anchor: `D5/S3/Quantum/Information/PauliRotationCriticalValues.NonIdentityPauli`
- Truth anchor: `D5/S3/Quantum/Information/PauliRotationCriticalValues.Param`
- Truth anchor: `D5/S3/Quantum/Information/PauliRotationCriticalValues.circuit`
- Truth anchor: `D5/S3/Quantum/Information/PauliRotationCriticalValues.claim`
- Truth anchor: `D5/S3/Quantum/Information/PauliRotationCriticalValues.critical`
- Truth anchor: `D5/S3/Quantum/Information/PauliRotationCriticalValues.derivativeRank`
- Truth anchor: `D5/S3/Quantum/Information/PauliRotationCriticalValues.result`
- Truth anchor: `D5/S3/Quantum/Information/PauliRotationCriticalValues.rotation`
- Dependency: [D5/S3/Analytic/NullSets/AnalyticZeroSetNull](../../Analytic/NullSets/AnalyticZeroSetNull.md)
- Dependency: [D5/S3/Observer/Hankel/PositiveGramianBalancing](../../Observer/Hankel/PositiveGramianBalancing.md)
- Dependency: [D5/S3/Quantum/Measurement/StabilizerPovmMaximalEntanglementRefutation](../Measurement/StabilizerPovmMaximalEntanglementRefutation.md)
