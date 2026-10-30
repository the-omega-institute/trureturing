# The original low-alpha SBW assertion

## Abstract

An exact faithful state and a rectangular Kraus channel contradict the original optimized SBW A-channel inequality at alpha = 1/2.

**Definition 1.1 (The assertion on 0 < alpha < 1).**

$$claim \Leftrightarrow (\forall dA \in \mathbb{N},\; \forall dAPrime \in \mathbb{N},\; \forall dB \in \mathbb{N},\; \forall dE \in \mathbb{N},\; \forall r \in \mathbb{N},\; \forall rho \in \operatorname{Matrix}\left(((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(dE\right)), ((\operatorname{Fin}\left(dA\right) \times \operatorname{Fin}\left(dB\right)) \times \operatorname{Fin}\left(dE\right)), \mathbb{C}\right),\; \forall K \in \operatorname{Fin}\left(r\right) \to \operatorname{Matrix}\left(\operatorname{Fin}\left(dAPrime\right), \operatorname{Fin}\left(dA\right), \mathbb{C}\right),\; \forall alpha \in \mathbb{R},\; (\operatorname{Matrix.PosSemidef}\left(rho\right)) \Rightarrow ((\operatorname{Matrix.trace}\left(rho\right) = 1) \Rightarrow ((\sum_{j} \operatorname{conjTranspose}\left(\operatorname{K}\left(j\right)\right) \cdot \operatorname{K}\left(j\right) = 1) \Rightarrow (((0 < alpha) \land (alpha < 1)) \Rightarrow (\operatorname{renyiCMI}\left(alpha, \operatorname{applyA}\left(K, rho\right)\right) \le \operatorname{renyiCMI}\left(alpha, rho\right))))))$$

*Formalization.* `D5/S3/Quantum/Information/RenyiCMILowAlphaRefutation.claim` (`✓ std3`).

*Citation.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

The claim quantifies over every natural input and output dimension and finite Kraus count. A positive semidefinite trace-one input and a complete Kraus family acting only on A must satisfy renyiCMI(alpha,applyA(K,rho)) <= renyiCMI(alpha,rho) for every 0 < alpha < 1. The functional, continuous-functional-calculus powers, Kraus action and carrier ((A times B) times E) are imported unchanged from RenyiCMILocalChannelRefutation. At alpha=1/2, the counterexample below makes the output functional strictly larger than the input functional. The frozen expression is the original optimized quantity; no fixed-sigma, sandwiched replacement or log-Euclidean quantity is substituted.

**Theorem 1.2 (A half-alpha counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Information/RenyiCMILowAlphaRefutation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* K. P. Seshadreesan, M. Berta, M. M. Wilde (2015). *Rényi squashed entanglement, discord, and relative entropy differences*. DOI: [10.1088/1751-8113/48/39/395303](https://doi.org/10.1088/1751-8113/48/39/395303). URL: <https://arxiv.org/abs/1410.1443v3>.

*Commentary.*

Set t=2^(-30), with input dimensions (3,2,2) and output dimensions (2,2,2). Let H have rows (0,1) and (1,0), R0=diag(16,1)/68, R1=diag(1,16)/68 and R2=identity/4. The state is block diagonal in A and B, with E blocks (Ra+(-1)^b*t*Xa)/2, where X0=X1=H and X2=-6H. All six blocks are positive definite by their positive first diagonal entry and determinant, and the total trace is one.

The three rectangular Kraus matrices map input basis label j to output label 0 for j=0,1 and to output label 1 for j=2, and vanish on the other labels. Their adjoint products sum to identity. The actual frozen applyA sum gives output E blocks (identity/4+2*(-1)^b*t*H)/2 and (identity/4-6*(-1)^b*t*H)/2. The input AE marginal is the block sum of R0,R1,R2, the output AE marginal is identity/4 and both E marginals are identity/2.

For a positive two by two real symmetric block M with entries (a,u;u,b), d=sqrt(a*b-u^2) and g=sqrt(a+b+2*d), its positive square root is (M+d*identity)/g. The proof checks this square and positivity, then identifies it with the frozen CFC half power by square-root uniqueness. Positive fourth-root certificates similarly identify the AE quarter powers; an inverse certificate identifies the E negative quarter power. Thus the original order of the two quarter powers and the partial trace is retained.

Write x=t^2, r=sqrt(1-289*x), s=sqrt(17+8*r), p=sqrt(1-64*x), q=sqrt(1-576*x), m=sqrt((1+p)/2), n=sqrt((1+q)/2), a=5*(s^2+9)/(34*s) and b=4/s. Exact evaluation of the frozen half-alpha expression gives the input value -log(Zin) and output value -log(Zout), with Zin=(a+n)^2/4+4*x*(b-3/n)^2 and Zout=(m+n)^2/4+4*x*(1/m-3/n)^2. The matrix identities preceding these real expressions evaluate actual states and Kraus output, rather than assuming scalar values for them.

The exact comparison factors as Zout-Zin=(m-a)*(m+a+2*n)/4+4*x*(1/m-b)*(1/m+b-6/n). On 0<x<=10^(-8), the radical relations give 1-a<(5441/500)*x and 1-m>=8*x. The first summand is therefore less than (1441/500)*x. They also give 1/m-b>=1999/10000 and 1/m+b-6/n<=-41989/10000. The second summand is at most -4*(1999/10000)*(41989/10000)*x. Their sum is strictly less than -(473/1000)*x. The fixed x=2^(-60) lies in that interval. Positivity of Zout and strict monotonicity of the natural logarithm give output CMI strictly greater than input CMI, contradicting claim at alpha=1/2.

The counterexample refutes the low-alpha mathematical assertion for the original optimized functional. The alpha=2 theorem remains a separate result. The recent log-Euclidean and dual-J counterexamples concern different functionals and are not used as evidence for this theorem. No worldwide novelty or priority claim is made.

## References

- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILowAlphaRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Information/RenyiCMILowAlphaRefutation.result`
- Dependency: [D5/S3/Quantum/Information/RenyiCMILocalChannelRefutation](RenyiCMILocalChannelRefutation.md)
