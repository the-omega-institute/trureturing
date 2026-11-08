# The Hermitian pentagon quartic certificate

## Abstract

An explicit quartic sum of squares gives the sharp coefficient eight for Hermitian matrices with pentagon support.

**Theorem 1.1 (The exact trace certificate).**

$$\forall n: Type, [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A: \operatorname{Fin}\left(5\right)\to \operatorname{Matrix}\left(n, n, \mathbb{C}\right), \left((\forall i: \operatorname{Fin}\left(5\right), \operatorname{IsHermitian}\left(A(i)\right)) \land (\forall i: \operatorname{Fin}\left(5\right), A(i) \cdot A(i + 2) = 0)\right) \Rightarrow 8 \cdot \sum_{i:\operatorname{Fin}\left(5\right)} \operatorname{ReTr}\left((A(i))^{4}\right) - \operatorname{ReTr}\left((\sum_{i:\operatorname{Fin}\left(5\right)} A(i))^{4}\right) = \sum_{i:\operatorname{Fin}\left(5\right)} \operatorname{hsSq}\left(R(i) - R(i + 1)\right) + \frac{1}{2} \cdot \sum_{i:\operatorname{Fin}\left(5\right)} \operatorname{hsSq}\left(R(i) - 2 \cdot R(i + 1) + 2 \cdot R(i + 2) - R(i + 3)\right) + \frac{3}{4} \cdot \sum_{i:\operatorname{Fin}\left(5\right)} \operatorname{hsSq}\left(C(i)\right) + \frac{5}{8} \cdot \sum_{i:\operatorname{Fin}\left(5\right)} \operatorname{hsSq}\left(C(i) - C(i + 1)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PentagonQuarticTrace.pentagon_quartic_sos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nidhal Mghirbi and Seth Douglas (2026). *The Lovasz number is not alone: a continuum of Renyi points in the entanglement-assisted spectrum of graphs*. DOI: [10.48550/arXiv.2610.20775](https://doi.org/10.48550/arXiv.2610.20775). URL: <https://arxiv.org/abs/2610.20775v1>.

*Commentary.*

Let n be any finite type with decidable equality and let A(i) be arbitrary complex matrices on n, for i in Fin 5. All index additions are modulo five. Assume that every A(i) is Hermitian and A(i)A(i+2)=0. Write ReTr for the real part of the ordinary, unnormalized trace and hsSq(B)=ReTr(B adjoint B). Set F(i)=A(i+4)+A(i+1), R(i)=A(i)^2-(A(i)F(i)+F(i)A(i))/2, and C(i)=A(i)A(i+1)-A(i+1)A(i). The identity and the five aggregation identities are attributed to the supplied mathematical source pentagon-quartic-joint-source/proof.txt, SHA-256 83ef9890d59944d8f6789d3e73dff4695ab3999c76d3e9b440eed74b40812280. No positive-semidefinite hypothesis is used.

To see the coefficients, write T=sum ReTr(A(i)^4), U31=sum ReTr(A(i)^3 A(i+1)+A(i)A(i+1)^3), U22=sum ReTr(A(i)^2 A(i+1)^2), Ualt=sum ReTr(A(i)A(i+1)A(i)A(i+1)), and Ustar=sum ReTr(A(i+4)A(i)A(i+1)A(i)). Cyclic trace and the forbidden products give ReTr(S^4)=T+4U31+4U22+2Ualt+4Ustar. For the real Hilbert--Schmidt pairing, the remainder correlations at distances zero, one and two are T-2U31+U22+Ualt+Ustar, -U31+3U22/2+Ualt/2+Ustar, and Ustar/2. The commutator correlations at distances zero and one are 2U22-2Ualt and 2Ustar. The cyclic quadratic forms combine these as 7r0-10r1+3r2+2c0-5c1/4, exactly 8T-ReTr(S^4).

**Theorem 1.2 (The quartic trace bound).**

$$\forall n: Type, [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A: \operatorname{Fin}\left(5\right)\to \operatorname{Matrix}\left(n, n, \mathbb{C}\right), \left((\forall i: \operatorname{Fin}\left(5\right), \operatorname{IsHermitian}\left(A(i)\right)) \land (\forall i: \operatorname{Fin}\left(5\right), A(i) \cdot A(i + 2) = 0)\right) \Rightarrow \operatorname{ReTr}\left((\sum_{i:\operatorname{Fin}\left(5\right)} A(i))^{4}\right) \le 8 \cdot \sum_{i:\operatorname{Fin}\left(5\right)} \operatorname{ReTr}\left((A(i))^{4}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PentagonQuarticTrace.pentagon_quartic_trace_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nidhal Mghirbi and Seth Douglas (2026). *The Lovasz number is not alone: a continuum of Renyi points in the entanglement-assisted spectrum of graphs*. DOI: [10.48550/arXiv.2610.20775](https://doi.org/10.48550/arXiv.2610.20775). URL: <https://arxiv.org/abs/2610.20775v1>.

*Commentary.*

Every Hilbert--Schmidt square is nonnegative, since B adjoint B is positive semidefinite. The four coefficients 1, 1/2, 3/4 and 5/8 are positive, so the certificate gives the dimension-independent inequality. The empty finite type is included. No rank restriction, projection reduction, real-entry assumption, invertibility or simultaneous diagonalization is used.

The supplied analytic positive Schatten duality argument at the conjugate exponents 4 and 4/3 converts this bound into sum Tr((P(i) X P(i))^(4/3)) <= 2 Tr(X^(4/3)) for X positive semidefinite and projections with P(i)P(i+2)=0. The primary source arXiv:2610.20775v1, Section 3.1, equation (11), uses the graph normalization 1/theta_alpha=sup min_i Z_(1-alpha). With this normalization, substituting X=sigma^(3/4) gives theta_(1/4)(C5)=5/2. The primary Proposition 3.3(ii) and flat witness then give the plateau [1/4,2]. These Schatten and graph consequences are analytic only here; this module proves the integer quartic matrix statements. This is the quartic consequence; higher-degree analytic plateau improvements are outside this module. The full curve remains open, and no literature priority is asserted.

**Theorem 1.3 (Every smaller coefficient fails).**

$$\forall c: \mathbb{R}, c < 8 \Rightarrow \exists A: \operatorname{Fin}\left(5\right)\to \operatorname{Matrix}\left(\operatorname{Fin}\left(1\right), \operatorname{Fin}\left(1\right), \mathbb{C}\right), \left((\forall i: \operatorname{Fin}\left(5\right), \operatorname{IsHermitian}\left(A(i)\right)) \land (\forall i: \operatorname{Fin}\left(5\right), A(i) \cdot A(i + 2) = 0)\right) \land c \cdot \sum_{i:\operatorname{Fin}\left(5\right)} \operatorname{ReTr}\left((A(i))^{4}\right) < \operatorname{ReTr}\left((\sum_{i:\operatorname{Fin}\left(5\right)} A(i))^{4}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PentagonQuarticTrace.constant_eight_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nidhal Mghirbi and Seth Douglas (2026). *The Lovasz number is not alone: a continuum of Renyi points in the entanglement-assisted spectrum of graphs*. DOI: [10.48550/arXiv.2610.20775](https://doi.org/10.48550/arXiv.2610.20775). URL: <https://arxiv.org/abs/2610.20775v1>.

*Commentary.*

For every real c<8, the strict reverse inequality occurs already on the one-dimensional complex space. Take A(0)=A(1)=1 and all other A(i)=0. The five support relations and Hermiticity hold, sum ReTr(A(i)^4)=2, and ReTr((sum A(i))^4)=16. Thus c times the former is strictly less than the latter. This proves optimality of eight for the same universal Hermitian inequality.

An additional analytic equality example uses the five diagonal projections onto span(e(i),e(i+1)) in dimension five. Their sum is 2I, T=10 and Tr(S^4)=80; all R(i) and C(i) vanish. The one-dimensional witness in the displayed theorem suffices to establish sharpness.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/PentagonQuarticTrace.constant_eight_sharp`
- Truth anchor: `D5/S3/Quantum/Matrix/PentagonQuarticTrace.pentagon_quartic_sos`
- Truth anchor: `D5/S3/Quantum/Matrix/PentagonQuarticTrace.pentagon_quartic_trace_le`
