# The complex PSD pentagon fifth moment

## Abstract

Seven explicit rational PSD-weighted squares give the sharp fifth-moment coefficient sixteen on the pentagon.

**Theorem 1.1 (The exact seven-square identity).**

$$\forall n: Type, [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A: \operatorname{Fin}\left(5\right)\to \operatorname{Matrix}\left(n, n, \mathbb{C}\right), \left((\forall i: \operatorname{Fin}\left(5\right), \operatorname{IsHermitian}\left(A(i)\right)) \land (\forall i: \operatorname{Fin}\left(5\right), A(i) \cdot A(i + 2) = 0)\right) \Rightarrow 16 \cdot \sum_{i:\operatorname{Fin}\left(5\right)} \operatorname{ReTr}\left((A(i))^{5}\right) - \operatorname{ReTr}\left((\sum_{i:\operatorname{Fin}\left(5\right)} A(i))^{5}\right) = \sum_{i:\operatorname{Fin}\left(5\right)} \sum_{k:\operatorname{Fin}\left(7\right)} w(k) \cdot \operatorname{weightedSquare}\left(A(i), \operatorname{B}\left(i, k\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PentagonQuinticTrace.pentagon_quintic_sos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nidhal Mghirbi and Seth Douglas (2026). *The Lovasz number is not alone: a continuum of Renyi points in the entanglement-assisted spectrum of graphs*. DOI: [10.48550/arXiv.2610.20775](https://doi.org/10.48550/arXiv.2610.20775). URL: <https://arxiv.org/abs/2610.20775v1>.

*Commentary.*

Let n be any finite type with decidable equality and A(i) complex matrices on n indexed by Fin 5. Index additions are modulo five. For this identity assume Hermiticity and A(i)A(i+2)=0. ReTr denotes the real part of the ordinary trace and weightedSquare(a,B)=ReTr(B adjoint a B). Put L=A(i-1)A(i-2), M=A(i+1)A(i+2), Dminus=A(i-1)^2-A(i-1)A(i), Dplus=A(i+1)^2-A(i+1)A(i), Fminus=A(i-1)^2-A(i)A(i-1), Fplus=A(i+1)^2-A(i)A(i+1), H=A(i)^2-A(i-1)^2-A(i+1)^2. The ordered even vector is E=(L+M,Dminus+Dplus,Fminus+Fplus,H) and the odd vector is O=(L-M,Dminus-Dplus,Fminus-Fplus). The identity is attributed to the supplied mathematical source pentagon-quintic-joint-source/proof.txt, SHA-256 9ecd6884c7788722176850d88a786d0306243f9373e333ed25ff6b557faf101a.

The seven B entries are E0-E1+7E2/8+3E3/2, E1+E2/6+7E3/6, E2+316E3/325, E3, O0-O1/3+O2/6, O1-O2/2, O2. Their weights w are 2,3,325/96,4181/1300,3,2/3,1/4. Sixteen separately proved Gram entries and five bounded first-factor expansions establish the exact ordered trace identity. The two oriented five-cycle words occur with their actual order. Cyclicity preserves each orientation; adjoint reversal conjugates the complex trace, and a separate lemma identifies their real parts. No complex trace is assumed to equal its reverse, and no cycle term is assigned a sign.

**Theorem 1.2 (The universal PSD bound).**

$$\forall n: Type, [\operatorname{Fintype}\left(n\right)] [\operatorname{DecidableEq}\left(n\right)] \forall A: \operatorname{Fin}\left(5\right)\to \operatorname{Matrix}\left(n, n, \mathbb{C}\right), \left((\forall i: \operatorname{Fin}\left(5\right), \operatorname{PosSemidef}\left(A(i)\right)) \land (\forall i: \operatorname{Fin}\left(5\right), A(i) \cdot A(i + 2) = 0)\right) \Rightarrow \operatorname{ReTr}\left((\sum_{i:\operatorname{Fin}\left(5\right)} A(i))^{5}\right) \le 16 \cdot \sum_{i:\operatorname{Fin}\left(5\right)} \operatorname{ReTr}\left((A(i))^{5}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PentagonQuinticTrace.pentagon_quintic_trace_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nidhal Mghirbi and Seth Douglas (2026). *The Lovasz number is not alone: a continuum of Renyi points in the entanglement-assisted spectrum of graphs*. DOI: [10.48550/arXiv.2610.20775](https://doi.org/10.48550/arXiv.2610.20775). URL: <https://arxiv.org/abs/2610.20775v1>.

*Commentary.*

Assume every A(i) is positive semidefinite and A(i)A(i+2)=0. PSD congruence gives B adjoint A(i) B positive semidefinite for every complex B. Its real trace is nonnegative. All seven rational weights are strictly positive, so the exact identity proves the inequality in every finite dimension, including the empty dimension. Singular and zero matrices are included. Positivity is used here; no corresponding Hermitian fifth-moment inequality is asserted. There is no reality, commutativity, rank, repeated-spectrum or invertibility restriction.

The analytical positive Schatten duality uses p=5/4 and q=5. For projections P(i) with P(i)P(i+2)=0 and X positive semidefinite, let Y(i)=P(i)XP(i) and L=sum Tr(Y(i)^(5/4)). For L>0 set C(i)=Y(i)^(1/4)/L^(1/5). These are PSD, supported in P(i), and sum Tr(C(i)^5)=1. Holder and the fifth-moment inequality give L^(4/5)<=16^(1/5) Tr(X^(5/4))^(4/5), hence L<=2 Tr(X^(5/4)); the zero case is immediate. In the primary projection formula, X=sigma^(4/5) gives min_i Z_(4/5)<=2/5 and theta_(1/5)(C5)>=5/2. The flat faithful witness sigma=I/5 attains equality, and primary monotonicity supplies [1/5,2]. These fractional-power, duality and graph statements are analytical here. The stronger analytical sixth-degree plateau [1/6,2] is outside this Lean module. The full curve remains open and no literature priority is certified. The primary definitions, original [1/2,2] plateau and umbrella with optimized centers are attributed to Mghirbi and Douglas, arXiv:2610.20775v1; see Library/Entropy/mghirbi2026renyi.md.

**Theorem 1.3 (The constant sixteen is sharp).**

$$\forall c: \mathbb{R}, c < 16 \Rightarrow \exists A: \operatorname{Fin}\left(5\right)\to \operatorname{Matrix}\left(\operatorname{Fin}\left(1\right), \operatorname{Fin}\left(1\right), \mathbb{C}\right), \left((\forall i: \operatorname{Fin}\left(5\right), \operatorname{PosSemidef}\left(A(i)\right)) \land (\forall i: \operatorname{Fin}\left(5\right), A(i) \cdot A(i + 2) = 0)\right) \land c \cdot \sum_{i:\operatorname{Fin}\left(5\right)} \operatorname{ReTr}\left((A(i))^{5}\right) < \operatorname{ReTr}\left((\sum_{i:\operatorname{Fin}\left(5\right)} A(i))^{5}\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Matrix/PentagonQuinticTrace.constant_sixteen_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Nidhal Mghirbi and Seth Douglas (2026). *The Lovasz number is not alone: a continuum of Renyi points in the entanglement-assisted spectrum of graphs*. DOI: [10.48550/arXiv.2610.20775](https://doi.org/10.48550/arXiv.2610.20775). URL: <https://arxiv.org/abs/2610.20775v1>.

*Commentary.*

For every real c<16 choose scalar complex PSD matrices A(0)=A(1)=1 and A(2)=A(3)=A(4)=0. All five support relations hold, sum ReTr(A(i)^5)=2 and ReTr((sum A(i))^5)=32. Thus the bound with c fails already in dimension one, for the same PSD domain.

The additional analytical flat example consists of five diagonal projections onto span(e(i),e(i+1)) in dimension five. Its sum is 2I, total fifth moment is 10 and the sum's fifth moment is 160. The scalar example already proves the formal optimality statement; the full flat projection and fractional-power consequences are outside its compiled scope.

## References

- Truth anchor: `D5/S3/Quantum/Matrix/PentagonQuinticTrace.constant_sixteen_sharp`
- Truth anchor: `D5/S3/Quantum/Matrix/PentagonQuinticTrace.pentagon_quintic_sos`
- Truth anchor: `D5/S3/Quantum/Matrix/PentagonQuinticTrace.pentagon_quintic_trace_le`
- Dependency: [D5/S3/Quantum/Matrix/PentagonQuarticTrace](PentagonQuarticTrace.md)
