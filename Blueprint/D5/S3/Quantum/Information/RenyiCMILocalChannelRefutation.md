# Rényi CMI local-channel monotonicity

## Abstract

Complete dephasing of A increases the Rényi conditional quantum mutual information of equation (3.18) for a faithful three-qubit state at alpha = 2.

**Definition 1.1 (Real matrix powers).**

$$\forall n \in \operatorname{Type},\; [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall X \in \operatorname{Matrix}\left(n, n, \mathbb{C}\right),\; \forall p \in \mathbb{R},\; \operatorname{mpow}\left(X, p\right) = \operatorname{cfc}\left(\operatorname{fun} (t:\mathbb{R}) \mapsto t^{p}, X\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.mpow` (`✓ std3`).

*Citation.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

Real powers use the continuous functional calculus on complex square matrices. Nonzero negative powers give generalized inverses on the support. Every matrix in the counterexample whose inverse power is used is positive definite.

**Definition 1.2 (Marginal on AE).**

$$\forall A \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall rho \in \operatorname{Matrix}\left(((A \times B) \times E), ((A \times B) \times E), \mathbb{C}\right),\; \operatorname{margAE}\left(rho\right) = \operatorname{partialTraceLeft}\left(\operatorname{Matrix.submatrix}\left(rho, \operatorname{ReorderBAE}, \operatorname{ReorderBAE}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.margAE` (`✓ std3`).

*Citation.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

The input carrier is (A times B) times E. ReorderBAE maps (b,(a,e)) to ((a,b),e), so partialTraceLeft traces B and retains AE.

**Definition 1.3 (Marginal on E).**

$$\forall A \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall rho \in \operatorname{Matrix}\left(((A \times B) \times E), ((A \times B) \times E), \mathbb{C}\right),\; \operatorname{margE}\left(rho\right) = \operatorname{partialTraceLeft}\left(rho\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.margE` (`✓ std3`).

*Citation.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

The frozen partialTraceLeft traces the whole AB factor and retains E.

**Definition 1.4 (Partial trace over A).**

$$\forall A \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall rho \in \operatorname{Matrix}\left(((A \times B) \times E), ((A \times B) \times E), \mathbb{C}\right),\; \operatorname{traceA}\left(rho\right) = \operatorname{partialTraceLeft}\left(\operatorname{Matrix.submatrix}\left(rho, \operatorname{ReorderABE}, \operatorname{ReorderABE}\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.traceA` (`✓ std3`).

*Citation.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

ReorderABE maps (a,(b,e)) to ((a,b),e). The partial trace then retains BE.

**Definition 1.5 (Identity extension of AE).**

$$\forall A \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall S \in \operatorname{Matrix}\left((A \times E), (A \times E), \mathbb{C}\right),\; \operatorname{extAE}\left(A, B, E, S\right) = \operatorname{fun} (x:((A \times B) \times E)) \mapsto \operatorname{fun} (y:((A \times B) \times E)) \mapsto \operatorname{ite}\left(\operatorname{BIndex}\left(x\right) = \operatorname{BIndex}\left(y\right), \operatorname{S}\left(\operatorname{AEIndex}\left(x\right), \operatorname{AEIndex}\left(y\right)\right), 0\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.extAE` (`✓ std3`).

*Citation.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

At indices ((a,b),e), ((aPrime,bPrime),ePrime), the entry is S((a,e),(aPrime,ePrime)) if b = bPrime and zero otherwise. BIndex and AEIndex are the corresponding coordinate projections. This is the identity extension of S on B in the input index order.

**Definition 1.6 (Identity extension of E).**

$$\forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall W \in \operatorname{Matrix}\left(E, E, \mathbb{C}\right),\; \operatorname{extE}\left(B, E, W\right) = \operatorname{Matrix.kronecker}\left(\operatorname{Identity}\left(B\right), W\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.extE` (`✓ std3`).

*Citation.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

The identity is on B; the output carrier is B times E.

**Definition 1.7 (Equation (3.18)).**

$$\forall A \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall alpha \in \mathbb{R},\; \forall rho \in \operatorname{Matrix}\left(((A \times B) \times E), ((A \times B) \times E), \mathbb{C}\right),\; \operatorname{renyiCMI}\left(alpha, rho\right) = \frac{alpha}{alpha - 1} \cdot \operatorname{Real.log}\left(\operatorname{Complex.re}\left(\operatorname{Matrix.trace}\left(\operatorname{mpow}\left(\operatorname{mpow}\left(\operatorname{extE}\left(\operatorname{margE}\left(rho\right)\right), \frac{alpha - 1}{2}\right) \cdot \operatorname{traceA}\left(\operatorname{mpow}\left(\operatorname{extAE}\left(\operatorname{margAE}\left(rho\right)\right), \frac{1 - alpha}{2}\right) \cdot \operatorname{mpow}\left(rho, alpha\right) \cdot \operatorname{mpow}\left(\operatorname{extAE}\left(\operatorname{margAE}\left(rho\right)\right), \frac{1 - alpha}{2}\right)\right) \cdot \operatorname{mpow}\left(\operatorname{extE}\left(\operatorname{margE}\left(rho\right)\right), \frac{alpha - 1}{2}\right), \frac{1}{alpha}\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.renyiCMI` (`✓ std3`).

*Citation.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

Section 3, equation (3.18), verbatim: Throughout this paper, we take our definition of Rényi conditional quantum mutual information for α ∈ (0, 1) ∪ (1, ∞) to be as follows [BSW15a, Definition 7]: The formula uses the AE and E marginals, their identity extensions, partial trace over A, real matrix powers and the real part of the final trace. The logarithm is natural.

**Definition 1.8 (A finite Kraus channel acting on A).**

$$\forall A \in \operatorname{Type},\; [\operatorname{Fintype}\left(A\right)] [\operatorname{DecidableEq}\left(A\right)] \forall B \in \operatorname{Type},\; [\operatorname{Fintype}\left(B\right)] [\operatorname{DecidableEq}\left(B\right)] \forall E \in \operatorname{Type},\; [\operatorname{Fintype}\left(E\right)] [\operatorname{DecidableEq}\left(E\right)] \forall APrime \in \operatorname{Type},\; [\operatorname{Fintype}\left(APrime\right)] [\operatorname{DecidableEq}\left(APrime\right)] \forall r \in \mathbb{N},\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(APrime, A, \mathbb{C}\right),\; \forall rho \in \operatorname{Matrix}\left(((A \times B) \times E), ((A \times B) \times E), \mathbb{C}\right),\; \operatorname{applyA}\left(K, rho\right) = \sum_{j} \operatorname{Matrix.kronecker}\left(\operatorname{Matrix.kronecker}\left(K j, \operatorname{Identity}\left(B\right)\right), \operatorname{Identity}\left(E\right)\right) \cdot rho \cdot \operatorname{conjTranspose}\left(\operatorname{Matrix.kronecker}\left(\operatorname{Matrix.kronecker}\left(K j, \operatorname{Identity}\left(B\right)\right), \operatorname{Identity}\left(E\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.applyA` (`✓ std3`).

*Citation.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

L_j = (K_j tensor 1_B) tensor 1_E. Each K_j maps A to APrime. The finite sum is a channel when sum_j K_j adjoint K_j = 1.

**Definition 1.9 (Conjecture 1).**

$$claim \Leftrightarrow (\forall dA \in \mathbb{N},\; \forall dAPrime \in \mathbb{N},\; \forall dB \in \mathbb{N},\; \forall dE \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(dE\right)), ((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(dE\right)), \mathbb{C}\right),\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dAPrime\right), \operatorname{Fin}\left(dA\right), \mathbb{C}\right),\; \forall alpha \in \mathbb{R},\; (\operatorname{Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(rho\right) = 1) \Rightarrow ((\sum_{j} \operatorname{conjTranspose}\left(K j\right) \cdot K j = 1) \Rightarrow ((((0 < alpha) \land (alpha < 1)) \lor ((1 < alpha) \land (alpha \le 2))) \Rightarrow (\operatorname{renyiCMI}\left(alpha, \operatorname{applyA}\left(K, rho\right)\right) \le \operatorname{renyiCMI}\left(alpha, rho\right))))))$$

*Formalization.* `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.claim` (`✓ std3`).

*Citation.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

Section 3, verbatim: Some results in this paper rely on the following conjecture: Conjecture 1 The Rényi conditional quantum mutual information obeys monotonicity with respect to CPTP maps on system A, i.e., for ρABE ∈ S(HABE) and α ∈ (0, 1) ∪ (1, 2], Iα(A; B|E)ρ ≥ Iα(A′; B|E)τ, where τA′BE ≡ MA→A′(ρABE) and MA→A′ is a CPTP map acting on system A alone. Section 2, verbatim: it was left as an open question to determine if the property holds for local quantum operations on the other system (with numerical evidence supporting a positive answer). Here, we assume the latter to hold. The Lean claim quantifies over all natural dimensions and finite Kraus counts, a positive semidefinite trace-one state, a complete Kraus family and the stated alpha range.

**Theorem 1.10 (A faithful state refutes local monotonicity).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/seshadreesan-berta-wilde-2015-renyi-cmi-local-channel` (refuted) by `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"seshadreesan-berta-wilde-2015-renyi-cmi-local-channel","declaration_gid":"D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

A, B and E are qubits and B is classical. The two AE blocks are M(13,8,7;13,39)/144 and M(7,8,13;39,13)/144, where M has corner entries p,q,q,s and middle diagonal entries u,v. Rational triangular conjugation certificates prove positivity and the trace is one. The Kraus matrices diagonal(1,0) and diagonal(0,1) completely dephase A. The input AE marginal is M(5,4,5;13,13)/36, whose positive square root is M(2,1,2;sqrt(13),sqrt(13))/6 and inverse square root is M(4,-2,4;6/sqrt(13),6/sqrt(13)). E is identity/2. The matrix under the last square root is diagonal(9,1,1,9)/64 before dephasing and diagonal(377,57,57,377)/2880 after it. The input square-root trace is one and the output trace is strictly greater than one. Thus the CMI goes from zero to a positive value, equivalently log((217+sqrt(21489))/360), contradicting the claim at alpha = 2.

## References

- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.applyA`
- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.extAE`
- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.extE`
- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.margAE`
- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.margE`
- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.mpow`
- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.renyiCMI`
- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.result`
- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation.traceA`
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
