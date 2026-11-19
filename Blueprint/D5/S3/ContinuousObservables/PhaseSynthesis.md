# Polynomial phases and signed circle factorization

## Abstract

Exact polynomial QSP synthesis factors continuous matrix completions on the full signed phase circle.

Let d be Polynomial.natDegree, let P* be the polynomial obtained by conjugating every coefficient, and let par(P,k) mean that every coefficient of parity opposite to k vanishes. Natural subtraction k−1 is truncated. Set e(φ)=exp(iφ), and define step(φ;(R,S))=(e(φ)[XR+(X²−1)S],e(−φ)[XS+R]). Multiplication by e(φ) here means multiplication by its constant polynomial. The pair q(φ₀,Φ)=qspPolyW(φ₀,Φ) is the left fold of this step over the real list Φ, starting from (e(φ₀),0). The initial phase is separate from the list.

**Theorem 1.1 (Every admissible pair has exactly k signal steps).**

$$\forall (k: \mathbb{N}), \forall (P: \mathbb{C}[X]), \forall (Q: \mathbb{C}[X]), ((\operatorname{d}(P) \leq k) \land (\operatorname{d}(Q) \leq k-1) \land ((k = 0) \Rightarrow Q = 0) \land (\operatorname{par}(P, k)) \land (\operatorname{par}(Q, k-1)) \land (P\operatorname{conj}(P)+(1-(X)^{2})Q\operatorname{conj}(Q) = 1)) \Rightarrow \exists (phi0: \mathbb{R}), \exists (Phi: \operatorname{List}(\mathbb{R})), (\operatorname{length}(Phi) = k) \land (\operatorname{q}(phi0, Phi) = \operatorname{pair}(P, Q))$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/PhaseSynthesis.exists_phases` (`✓ std3`). ∎

*Citation.* Andras Gilyen, Yuan Su, Guang Hao Low, Nathan Wiebe (2019). *Quantum singular value transformation and beyond: exponential improvements for quantum matrix arithmetics*. DOI: [10.1145/3313276.3316366](https://doi.org/10.1145/3313276.3316366). URL: <https://arxiv.org/abs/1806.01838v1>.

*Commentary.*

The identity is an equality in C[X]. One initial real phase and one real list work for the whole polynomial pair. The conclusion includes length exactly k, rather than a degree-dependent upper bound. When k=0, Q=0 is explicit and P can be any unimodular constant.

The induction lowers the budget k, including when the actual top coefficients vanish. At k=n+1, the coefficient of X^(2n+2) in the norm identity gives p_(n+1) times its conjugate equal to q_n times its conjugate. If q_n=0, both coefficients vanish and φ=0 works. Otherwise p_(n+1)/q_n has modulus one; a half argument supplies e(−φ)p_(n+1)=e(φ)q_n.

Define the inverse pair R=e(−φ)XP+e(φ)(1−X²)Q and S=e(φ)XQ−e(−φ)P. The forward step returns (P,Q) and the norm identity is preserved. The chosen phase kills the highest coefficient of each component, while opposite parity kills the next coefficient. Thus d(R)≤n and d(S)≤n−1, with S=0 at n=0. The recursive phase list is extended on the right by φ. This is the original degree-lowering proof, including its zero-top-coefficient branch.

For T=AddCircle(1), z=windingPhase(t), x=Re(z) and y=Im(z), write A₂=C(T,Matrix(ZMod 2,ZMod 2,C)). The native signal W is phaseCompletion(X,0,1), so W(t)=[[x,iy],[iy,x]]. Let D(φ) be the constant diagonal field diag(e(φ),e(−φ)). The field product V(φ₀,Φ)=phaseProduct(φ₀,Φ) is the left fold U↦U·W·D(φ) starting from D(φ₀). It therefore equals D(φ₀) followed in list order by the factors W·D(φ).

**Theorem 1.2 (The same sum-of-squares factors give the entire matrix field).**

$$\forall (k: \mathbb{N}), \forall (p: \mathbb{R}[X]), ((\operatorname{d}(p) \leq k) \land (\operatorname{par}(\operatorname{c}(p), k)) \land (\forall (x: I), (\operatorname{p}(x))^{2} \leq 1)) \Rightarrow \exists (B: \mathbb{R}[X]), \exists (C: \mathbb{R}[X]), \exists (U: A_{2}), \exists (phi0: \mathbb{R}), \exists (Phi: \operatorname{List}(\mathbb{R})), ((1-(p)^{2} = (B)^{2}+(1-(X)^{2})(C)^{2}) \land (\operatorname{d}(B) \leq k) \land (\operatorname{d}(C) \leq k-1) \land ((k = 0) \Rightarrow C = 0) \land (\operatorname{par}(\operatorname{c}(B), k)) \land (\operatorname{par}(\operatorname{c}(C), k-1))) \land (U = \operatorname{F}(p, B, C)) \land (\operatorname{star}(U)U = 1) \land (U\operatorname{star}(U) = 1) \land (\forall (t: T), \operatorname{det}(\operatorname{U}(t)) = 1) \land (\forall (t: T), \operatorname{Re}(\operatorname{entry}(\operatorname{U}(t), 0, 0)) = \operatorname{p}(\operatorname{Re}(\operatorname{z}(t)))) \land (\operatorname{length}(Phi) = k) \land (\operatorname{q}(phi0, Phi) = \operatorname{pair}(\operatorname{c}(p)+i\operatorname{c}(B), \operatorname{c}(C))) \land (\operatorname{V}(phi0, Phi) = U)$$

*Proof.* Machine-checked in Lean as `D5/S3/ContinuousObservables/PhaseSynthesis.exists_phase_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Here c is coefficientwise complexification from R[X] to C[X], I=[−1,1], and F(p,B,C)=phaseCompletion(p,B,C). Its four entries at t are p(x)+iB(x), iyC(x), iyC(x), p(x)−iB(x). The witnesses B,C and U are obtained once from exists_phase_unitary_completion; all scalar bounds, parities, the k=0 endpoint, both star products, determinant and real readout are retained for those same witnesses.

Set P=c(p)+i·c(B), Q=c(C). Their polynomial norm identity is the complexification of 1−p²=B²+(1−X²)C². The exact pair theorem yields φ₀,Φ. At any real x,y satisfying x²+y²=1, form E(P,Q)=[[P(x),iyQ(x)],[iyQ*(x),P*(x)]]. Direct multiplication gives E(R,S)·W·D(φ)=E(step(φ;(R,S))). Induction on the list identifies the native product with E(q(φ₀,Φ)). Since real polynomial coefficients are fixed by conjugation, E(P,Q)=F(p,B,C). Equality of all four entries gives equality in A₂.

The signed coordinate y is essential: x²+y²=1 holds on the entire winding circle, and no step replaces y by its absolute value or by a nonnegative square root. Polynomial evaluation and the coordinate functions are continuous; the constant diagonal fields and their finite products are continuous as elements of the existing observable algebra. For p=X, the factors B=0,C=1 give the signal itself, realized by initial phase zero and the one-element list [0]. The theorem includes constant and lower-degree inputs through the exact budget induction.

This is an existence theorem for phase lists and a full signed-circle field factorization. It does not assert an effective root algorithm, numerical stability, a query-complexity theorem, block encoding, physical realization, full QSVT or a reflection-convention equivalence.

Copyright (c) 2026 shosonoda. All rights reserved. The polynomial synthesis proof is reused from auto-res/lean-qsvt, commit 42c4b9149d5957db497e4226bc02da92d10f7a3c, QSVT/QSP/Existence.lean through exists_phases, with its consumed helpers from QSP/PolyW.lean, QSP/Poly.lean and Polynomial/Parity.lean. Apache-2.0 is preserved in docs/reports/licenses/auto-res-lean-qsvt-LICENSE.txt. Namespaces, imports and visibility are adapted to the receiver's existing SOS definitions. The source bodies implement Gilyen–Su–Low–Wiebe, arXiv:1806.01838v1, Theorem 3, equations (4)–(8), printed pages 8–9. The continuous signed-circle application combines that established result with the interval SOS theorem and carries no originality claim for either theorem.

## References

- Truth anchor: `D5/S3/ContinuousObservables/PhaseSynthesis.exists_phase_factorization`
- Truth anchor: `D5/S3/ContinuousObservables/PhaseSynthesis.exists_phases`
- Dependency: [D5/S3/ContinuousObservables/IntervalSOSCompletion](IntervalSOSCompletion.md)
