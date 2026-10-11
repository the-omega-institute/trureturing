# Trace-norm CMI contraction conjecture

## Abstract

A flagged measurement in two qubit bases strictly contracts local trace distance while preserving the trace-norm conditional mutual information of a tripartite state.

**Definition 1.1 (Local trace-norm contraction ratio).**

$$\forall n \in \mathbb{N},\; \forall nPrime \in \mathbb{N},\; \forall iota \in \operatorname{Type},\; [\operatorname{Fintype}\left(iota\right)] \forall K \in iota \to \operatorname{Matrix}\left(\operatorname{Fin}\left(nPrime\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; \operatorname{localContraction}\left(K\right) = \operatorname{sSup}\left(\{r:\mathbb{R} \mid \exists rho \in \operatorname{DensityState}\left(\operatorname{Fin}\left(n\right)\right),\; \exists rhoPrime \in \operatorname{DensityState}\left(\operatorname{Fin}\left(n\right)\right),\; (\neg rho = rhoPrime) \land (r = \frac{\operatorname{traceNorm}\left(\operatorname{ofKraus}\left(K, K, \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\right)\right)\right) - \operatorname{ofKraus}\left(K, K, \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rhoPrime\right)\right)\right)\right)}{\operatorname{traceNorm}\left(\operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\right)\right) - \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rhoPrime\right)\right)\right)})\}\right)$$

*Formalization.* `D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.localContraction` (`✓ std3`).

*Citation.* Chi-Fang Chen, Kohtaro Kato and Fernando G. S. L. Brandão (2020). *Matrix Product Density Operators: when do they have a local parent Hamiltonian?*. URL: <https://arxiv.org/abs/2010.14682v3>.

*Commentary.*

Conjecture III.2, PDF p. 17: the local contraction ratio is the supremum of the trace-norm output difference divided by the trace-norm input difference. The two input DensityState values are distinct. Their underlying matrices are exposed by CStarMatrix.ofMatrix.symm. ofKraus(K,K,X) denotes FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus applied to K, K and X, namely the sum of K_i X K_i adjoint. The definition uses the repository traceNorm and the real supremum sSup.

**Definition 1.2 (Trace-norm conditional mutual information).**

$$\forall dA \in \mathbb{N},\; \forall dB \in \mathbb{N},\; \forall n \in \mathbb{N},\; \forall M \in \operatorname{Matrix}\left(((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(n\right)), ((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(n\right)), \mathbb{C}\right),\; \operatorname{let} R:(\operatorname{Fin}\left(dA\right) \times (\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(n\right))) \to ((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(n\right)) := \operatorname{fun} (p:(\operatorname{Fin}\left(dA\right) \times (\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(n\right)))) \mapsto ((\operatorname{Prod.fst}\left(p\right), \operatorname{Prod.fst}\left(\operatorname{Prod.snd}\left(p\right)\right)), \operatorname{Prod.snd}\left(\operatorname{Prod.snd}\left(p\right)\right)), \operatorname{let} S:((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(n\right)) \to (\operatorname{Fin}\left(dA\right) \times (\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(n\right))) := \operatorname{fun} (p:((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(n\right))) \mapsto (\operatorname{Prod.fst}\left(\operatorname{Prod.fst}\left(p\right)\right), (\operatorname{Prod.snd}\left(\operatorname{Prod.fst}\left(p\right)\right), \operatorname{Prod.snd}\left(p\right))), \operatorname{let} AB:\operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right) := \operatorname{partialTraceRight}\left(M\right), \operatorname{let} A:\operatorname{Matrix}\left(\operatorname{Fin}\left(dA\right), \operatorname{Fin}\left(dA\right), \mathbb{C}\right) := \operatorname{partialTraceRight}\left(AB\right), \operatorname{let} B:\operatorname{Matrix}\left(\operatorname{Fin}\left(dB\right), \operatorname{Fin}\left(dB\right), \mathbb{C}\right) := \operatorname{partialTraceLeft}\left(AB\right), \operatorname{let} BC:\operatorname{Matrix}\left((\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(n\right)), (\operatorname{Fin}\left(dB\right) \times \operatorname{Fin}\left(n\right)), \mathbb{C}\right) := \operatorname{partialTraceLeft}\left(\operatorname{Matrix.submatrix}\left(M, R, R\right)\right), \operatorname{I1}\left(M\right) = \operatorname{traceNorm}\left(M - \operatorname{Matrix.submatrix}\left(\operatorname{Matrix.kronecker}\left(A, BC\right), S, S\right)\right) - \operatorname{traceNorm}\left(AB - \operatorname{Matrix.kronecker}\left(A, B\right)\right)$$

*Formalization.* `D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.I1` (`✓ std3`).

*Citation.* Chi-Fang Chen, Kohtaro Kato and Fernando G. S. L. Brandão (2020). *Matrix Product Density Operators: when do they have a local parent Hamiltonian?*. URL: <https://arxiv.org/abs/2010.14682v3>.

*Commentary.*

Definition 2, PDF p. 14, verbatim: I_1(A:C|B) := ||rho_ABC - rho_A tensor rho_BC||_1 - ||rho_AB - rho_A tensor rho_B||_1. The input coordinates are (A times B) times C. partialTraceRight traces the right factor; partialTraceLeft traces the left factor. The maps R and S reassociate the product indices in opposite directions. AB, A, B and BC are the literal reduced matrices. The tensor product A tensor BC is reassociated back to the input coordinates before subtraction. No rank condition is imposed.

**Definition 1.3 (Chen–Kato–Brandão Conjecture III.2).**

$$claim \Leftrightarrow (\forall n \in \mathbb{N},\; \forall nPrime \in \mathbb{N},\; \forall iota \in \operatorname{Type},\; [\operatorname{Fintype}\left(iota\right)] \forall K \in iota \to \operatorname{Matrix}\left(\operatorname{Fin}\left(nPrime\right), \operatorname{Fin}\left(n\right), \mathbb{C}\right),\; (\sum_{i:iota} (\operatorname{conjTranspose}\left(K\left(i\right)\right) \cdot K\left(i\right)) = 1) \Rightarrow ((\operatorname{localContraction}\left(K\right) < 1) \Rightarrow (\exists eta \in \mathbb{R},\; (eta < 1) \land (\forall dA \in \mathbb{N},\; \forall dB \in \mathbb{N},\; \forall rho \in \operatorname{DensityState}\left(((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(n\right))\right),\; \operatorname{let} L:iota \to \operatorname{Matrix}\left(((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(nPrime\right)), ((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(n\right)), \mathbb{C}\right) := \operatorname{fun} (i:iota) \mapsto \operatorname{Matrix.kronecker}\left((1:\operatorname{Matrix}\left((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), (\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)), \mathbb{C}\right)), K\left(i\right)\right), \operatorname{I1}\left(\operatorname{ofKraus}\left(L, L, \operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\right)\right)\right)\right) \le eta \cdot \operatorname{I1}\left(\operatorname{CStarMatrix.ofMatrix.symm}\left(\operatorname{val}\left(rho\right)\right)\right)))))$$

*Formalization.* `D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.claim` (`✓ std3`).

*Citation.* Chi-Fang Chen, Kohtaro Kato and Fernando G. S. L. Brandão (2020). *Matrix Product Density Operators: when do they have a local parent Hamiltonian?*. URL: <https://arxiv.org/abs/2010.14682v3>.

*Commentary.*

Conjecture III.2, PDF p. 17, verbatim: For any channel E: C to CPrime with local contraction ratio eta_1,C < 1, there exists a global constant eta < 1 such that for any tripartite system ABC and any state rho_ABC, I_1(A:CPrime|B)_E(rho) <= eta I_1(A:C|B)_rho. All dimensions range over natural numbers. The finite Kraus family is arbitrary and its completeness equation is the channel hypothesis. L_i is the literal identity on AB kronecker K_i, and the bound applies uniformly to every DensityState on the input product carrier, including singular states.

**Theorem 1.4 (A flagged qubit measurement refutes the conjecture).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/chen-kato-brandao-2020-trace-norm-cmi-contraction` (refuted) by `D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"chen-kato-brandao-2020-trace-norm-cmi-contraction","declaration_gid":"D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Chi-Fang Chen, Kohtaro Kato and Fernando G. S. L. Brandão (2020). *Matrix Product Density Operators: when do they have a local parent Hamiltonian?*. URL: <https://arxiv.org/abs/2010.14682v3>.

*Commentary.*

Take the channel from a qubit to four classical outcomes that measures the computational basis with probability 1/2 and the plus-minus basis with probability 1/2, recording both the basis and the outcome. Its local trace-norm contraction ratio is at most 1/sqrt(2), strictly less than one. Let A and B be qubits and let the input state be the equal mixture of the Bell state phi-plus on BC flagged by A = 0 and the Bell state psi-minus on BC flagged by A = 1. The AB marginal is the identity divided by four, so the second trace-norm term vanishes both before and after the channel. The input trace-norm conditional mutual information equals one. The centered output is Hermitian and its square is the identity divided by 256; multiplying it by 16 gives a unitary whose real trace pairing with the centered output is one. Thus the output trace-norm conditional mutual information is at least one. The asserted uniform bound would force 1 <= eta for eta < 1, a contradiction.

## References

- Truth anchor: `D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.I1`
- Truth anchor: `D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.localContraction`
- Truth anchor: `D5/S3/Quantum/Information/ChenKatoBrandaoTraceNormCMIRefutation.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](../Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/Foundation/FiniteTraceDistance](../Foundation/FiniteTraceDistance.md)
- Dependency: [D5/S3/Quantum/Information/PartialTraceMutualInformation](PartialTraceMutualInformation.md)
