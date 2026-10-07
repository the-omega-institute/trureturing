# Qubit Generalized Fidelity and Failure of Data Processing

## Abstract

A fixed bit-flip qubit channel strictly increases the squared generalized Bures--Wasserstein quantity throughout an explicit interval of reference states.

**Definition 1.1 (The ordered matrix-root trace).**

$$\operatorname{fidelity}\left(R, P, Q\right) = \operatorname{tr}\left(\operatorname{sqrt}\left(\operatorname{sqrt}\left(R\right)P\operatorname{sqrt}\left(R\right)\right)R^{-1}\operatorname{sqrt}\left(\operatorname{sqrt}\left(R\right)Q\operatorname{sqrt}\left(R\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/GeneralizedFidelity.fidelity` (`✓ std3`).

*Citation.* Reza Rajaei (2026). *Generalized Fidelity and the Data Processing Inequality*. URL: <https://arxiv.org/html/2609.09753v1>.

*Commentary.*

For any finite index type n with decidable equality, R, P and Q are actual complex n by n matrices. fidelity(R,P,Q) is the trace of sqrt(sqrt(R) P sqrt(R)) R inverse sqrt(sqrt(R) Q sqrt(R)). Every root is CFC.sqrt, the positive semidefinite matrix root on positive semidefinite arguments. The source domain requires positive-definite R and permits singular positive semidefinite P,Q. The total definition does not assert the source's properties outside that domain.

**Definition 1.2 (The full real trace quantity).**

$$\operatorname{bures}\left(R, P, Q\right) = \operatorname{Re}\left(\operatorname{tr}\left(P+Q\right)\right)-2\operatorname{Re}\left(\operatorname{fidelity}\left(R, P, Q\right)\right)$$

*Formalization.* `D5/S3/Quantum/GeneralizedFidelity.bures` (`✓ std3`).

*Citation.* Reza Rajaei (2026). *Generalized Fidelity and the Data Processing Inequality*. URL: <https://arxiv.org/html/2609.09753v1>.

*Commentary.*

bures(R,P,Q) is Re tr(P+Q) minus twice Re fidelity(R,P,Q). The trace term is retained in the definition. It equals two only after establishing trace(P)=trace(Q)=1. On the source's Hermitian states the trace is real, so taking its real part gives precisely the source's squared generalized Bures--Wasserstein distance.

**Definition 1.3 (The action of an actual quantum channel).**

$$\operatorname{rawMatrix}\left(Phi, M\right) = \operatorname{ofMatrixInverse}\left(\operatorname{Phi}\left(\operatorname{ofMatrix}\left(M\right)\right)\right)$$

*Formalization.* `D5/S3/Quantum/GeneralizedFidelity.rawMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Reza Rajaei (2026). *Generalized Fidelity and the Data Processing Inequality*. URL: <https://arxiv.org/html/2609.09753v1>.

*Commentary.*

A QuantumChannel is the existing completely positive complex linear map on CStarMatrix with trace preservation. Complete positivity requires positivity at every matrix amplification. rawMatrix converts an arbitrary qubit matrix to CStarMatrix, applies the channel, and converts the value back through ofMatrix inverse. The star algebra equivalence transports matrix positivity in both directions.

**Definition 1.4 (The unrestricted qubit assertion).**

$$\forall P,Q,R,Phi,\ \operatorname{PSD}\left(P\right) \land \operatorname{PSD}\left(Q\right) \land \operatorname{tr}\left(P\right) = 1 \land \operatorname{tr}\left(Q\right) = 1 \land \operatorname{PD}\left(R\right) \land \operatorname{tr}\left(R\right) = 1 \land \operatorname{CPTP}\left(Phi\right) \land \operatorname{PD}\left(\operatorname{rawMatrix}\left(Phi, R\right)\right) \Rightarrow \operatorname{bures}\left(\operatorname{rawMatrix}\left(Phi, R\right), \operatorname{rawMatrix}\left(Phi, P\right), \operatorname{rawMatrix}\left(Phi, Q\right)\right) \le \operatorname{bures}\left(R, P, Q\right)$$

*Formalization.* `D5/S3/Quantum/GeneralizedFidelity.claim` (`✓ std3`).

*Citation.* Reza Rajaei (2026). *Generalized Fidelity and the Data Processing Inequality*. URL: <https://arxiv.org/html/2609.09753v1>.

*Commentary.*

For every actual complex two by two P,Q,R and every genuine QuantumChannel from qubits to qubits, assume P,Q positive semidefinite with trace one, R positive definite with trace one, and the transported R positive definite. The assertion is bures(Phi(R),Phi(P),Phi(Q)) <= bures(R,P,Q). No invertibility condition is imposed on P or Q. This is the residual universal qubit question explicitly retained in Rajaei's abstract and qubit discussion.

**Theorem 1.5 (A complete interval counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/GeneralizedFidelity.result` (`✓ std3`). ∎

*Resolves.* `Problems/rajaei-qubit-generalized-fidelity-dpi` (refuted) by `D5/S3/Quantum/GeneralizedFidelity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"rajaei-qubit-generalized-fidelity-dpi","declaration_gid":"D5/S3/Quantum/GeneralizedFidelity.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Reza Rajaei (2026). *Generalized Fidelity and the Data Processing Inequality*. URL: <https://arxiv.org/html/2609.09753v1>.

*Commentary.*

Let P=[[1,3],[3,9]]/10, Q=[[4,2],[2,1]]/5, R=diag(1-e,e), X=[[0,1],[1,0]] and Phi(M)=31M/32+XMX/32. For every real 0<e<=1/1000, both input states are positive semidefinite of trace one, and both reference states are positive definite of trace one. The two Kraus matrices sqrt(31/32)I and sqrt(1/32)X are normalized and give the existing genuine CPTP channel. On every complex matrix its action equals Fourier phase damping with retention 15/16. The reference output is diag((31-30e)/32,(1+30e)/32). Positive candidates whose squares are the two references and the four sandwiches identify all six actual roots by uniqueness. Expanding the ordered trace gives F_in=(2+e)/sqrt(2(4+29e-24e^2))>7/10. For S=sqrt(961+27900e-27900e^2), A=(95+450e+S)/640 and B=(1955-1350e+3S)/2560, the output is F_out=(A+B-707/1600)/(2sqrt(AB)). The bounds 31<=S<32 and S<=31+450e put A in [63/320,1/4] and B in [3/4,4/5]. The exact rectangle certificate (A+B-707/1600)^2-49AB/25<=-27/40000, with positive numerator and denominators, gives F_out<7/10. Trace-one proofs then imply B_in<3/5<B_out throughout the interval. Instantiating e=1/1000 contradicts the universal assertion. The conclusion has no term premises. It neither repeats the source's higher-dimensional counterexample nor classifies all reference bases.

## References

- Truth anchor: `D5/S3/Quantum/GeneralizedFidelity.bures`
- Truth anchor: `D5/S3/Quantum/GeneralizedFidelity.claim`
- Truth anchor: `D5/S3/Quantum/GeneralizedFidelity.fidelity`
- Truth anchor: `D5/S3/Quantum/GeneralizedFidelity.rawMatrix`
- Truth anchor: `D5/S3/Quantum/GeneralizedFidelity.result`
- Dependency: [D5/S3/Quantum/Foundation/FiniteKrausChannel](Foundation/FiniteKrausChannel.md)
- Dependency: [D5/S3/Quantum/PointerBasis](PointerBasis.md)
