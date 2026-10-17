# Full Positive Cell Finite Transfer

## Abstract

Full nonnegative coefficients admit finite actual Mobius transport with the complete integer mean and pole-centered prefix.

All logarithms are natural. The block is N<=m<2*N, with natural N>=3. The coefficients b are arbitrary nonnegative real numbers on this entire block. There is no zeroth- or first-moment cancellation. The response and variation are the original OriginalResidualFiniteTransfer definitions. The constant response, the same actual Mobius coefficient in its linear and floor pieces, every prime-power index and both jumps of the zero extension are retained.

**Definition 1.1 (The full mass).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.totalMass`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.totalMass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N and real sequence b, A(N,b)=sum(N<=m<2*N,b(m)).

**Definition 1.2 (The full first moment).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.firstMoment`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.firstMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,b, B(N,b)=sum(N<=m<2*N,m*b(m)). For nonnegative b, 0<=B<=2*N*A.

**Definition 1.3 (The positive fractional kernel).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.fracPair`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.fracPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N,d and b, Q(N,b,d)=sum(N<=m<2*N,b(m)*(m mod d)/d). Mathlib's Int.fract_div_natCast_eq_div_natCast_mod identifies this remainder quotient with the literal fractional part of the real quotient m/d.

**Definition 1.4 (The full logarithmic kernel).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.logPair`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.logPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,b,d, K(N,b,d)=log(N/d)*Q(N,b,d). At positive N, K(N,b,N)=0; integer remainders also give K(N,b,1)=0.

**Definition 1.5 (Consecutive full-kernel difference).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.logDifference`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.logDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,b,k, D(N,b,k)=K(N,b,k)-K(N,b,k+1).

**Definition 1.6 (Weighted full-kernel variation).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.weightedVariation`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.weightedVariation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,h,b, W(N,h,b)=sum(h<=k<N,k*abs(D(N,b,k))).

**Definition 1.7 (The unchanged full response pairing).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.pairing`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.pairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,b, E(N,b)=sum(N<=m<2*N,b(m)*response(N,m)). The original affine-and-floor response is used directly.

**Definition 1.8 (Positive high-prefix replacement).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.replacement`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.replacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,q,b,F, Z(N,q,b,F)=sum(q+1<=k<N,(F(k)+2)*D(N,b,k))/log N. The sign is positive. The literal +2 telescopes to 2*K(N,b,q+1)/log N.

**Definition 1.9 (The exact pole-centered low prefix).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.polePrefix`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.polePrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural q put h=q+1. R(q)=sum(1<=d<=q,mu(d)*log(h/d))+2*log h, with the actual Mobius function and inclusive finite cutoff.

**Definition 1.10 (The exact reciprocal low prefix).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.reciprocalPrefix`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.reciprocalPrefix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural N,q, U(N,q)=sum(1<=d<=q,mu(d)*log(N/d)/d).

**Definition 1.11 (The entire nonzero-mean correction).**

Lean statement: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.meanCorrection`

*Formalization.* `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.meanCorrection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,q,b, put h=q+1, u=log(N/h), L=log N. C(N,q,b)=A(N,b)/(2*L)*(R(q)-U(N,q)+(M(q)+2)*u/h). M(q) is the unchanged actual inclusive Mobius prefix.

**Theorem 1.12 (Finite full-positive transfer).**

$$\forall N,q\in \mathbb{N},\forall b,F\in \mathbb{R}^{\mathbb{N}},\forall e,c\in \mathbb{R},3\le N\land q\le N-2\land 0\le e\land 0\le c\land (\forall m\in \mathbb{N},N\le m< 2\cdot N\Rightarrow 0\le \operatorname{b}\left(m\right))\land (\forall k\in \mathbb{N},(q+1)\le k< N\Rightarrow \lvert \operatorname{F}\left(k\right)-\operatorname{M}\left(k\right)\rvert \le e\cdot k+c)\Rightarrow \lvert \operatorname{E}\left(N, b\right)-\operatorname{Z}\left(N, q, b, F\right)-\operatorname{C}\left(N, q, b\right)\rvert \le \frac{e+\frac{c}{(q+1)}}{\operatorname{log}\left(N\right)}\cdot N\cdot \operatorname{A}\left(N, b\right)\cdot (1+2\cdot \operatorname{log}\left(\frac{N}{(q+1)}\right)^{2}+2\cdot \operatorname{log}\left(\frac{N}{(q+1)}\right)\cdot (1+\operatorname{log}\left(\frac{2\cdot N}{(q+1)}\right)))+(q+1)\cdot (\frac{3\cdot q}{2}+2)\cdot \operatorname{V}\left(N, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.originalFullCell_finite_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural N>=3 and q<=N-2, arbitrary real sequences b,F and real e,c>=0, assume b(m)>=0 on N<=m<2*N and abs(F(k)-M(k))<=e*k+c on h=q+1<=k<N. Set u=log(N/h), v=log(2*N/h), L=log N and V=variation(N,b). Then abs(E-Z-C)<=((e+c/h)/L)*N*A*(1+2*u^2+2*u*(1+v))+h*(3*q/2+2)*V.

Natural division and finite exchange give E=A+sum(mu(d)*K(d))/L. The public ActualOddMobiusFinitePairing.prefix_abel supplies its positive Abel form. K(N)=0 retains the exact terminal boundary. In the full kernel, Q(k)-Q(k+1)=B/(k*(k+1))-sum(b(m)*(floor(m/k)-floor(m/(k+1)))). The three product-difference costs are 2*N*A*u^2, 2*N*A*u*(1+v) and N*A. The original weighted_floor_bound, reciprocal_log_step and weighted_log_step supply the finite count and logarithmic estimates.

Let S(d)=sum(b(m)*centered(d,m)). The exact integer mean gives Q(d)=A*(d-1)/(2*d)+S(d). The original-owner centered_pair_variation_bound gives abs(S(d))<=d*V with both jumps and no moment hypotheses. Writing P=sum(1<=k<=q,M(k)*D(k)), the exact low identity is A+(P-2*K(h))/L=C+[sum(1<=d<=q,mu(d)*log(N/d)*S(d))-(M(q)+2)*u*S(h)]/L. The truncated pole payment is literally -2*K(h)/L. The centered remainder costs at most h*(3*q/2+2)*V, using sum(1<=d<=q,d)=q*(q+1)/2 and abs(M(q)+2)<=q+2.

The remaining high error is exactly sum(h<=k<N,(M(k)-F(k))*D(k))/L. The shared original-owner prefix_error_bound bounds it by ((e+c/h)/L)*W. At q=0, R=U=M(0)=0, h=1 and u=L, so C=A exactly. At q=N-2 the high range contains only k=N-1. Zero coefficients, variation or error constants require no division by them. Full residues, a signed infinite account, strict Robin above 5040 and RH remain open.

**Theorem 1.13 (Sharp finite full-positive transfer).**

$$\forall N,q\in \mathbb{N},\forall b,F\in \mathbb{R}^{\mathbb{N}},\forall e,c\in \mathbb{R},3\le N\land q\le N-2\land 0\le e\land 0\le c\land (\forall m\in \mathbb{N},N\le m< 2\cdot N\Rightarrow 0\le \operatorname{b}\left(m\right))\land (\forall k\in \mathbb{N},(q+1)\le k< N\Rightarrow \lvert \operatorname{F}\left(k\right)-\operatorname{M}\left(k\right)\rvert \le e\cdot k+c)\Rightarrow \lvert \operatorname{E}\left(N, b\right)-\operatorname{Z}\left(N, q, b, F\right)-\operatorname{C}\left(N, q, b\right)\rvert \le \frac{e+\frac{c}{(q+1)}}{\operatorname{log}\left(N\right)}\cdot N\cdot \operatorname{A}\left(N, b\right)\cdot (1+2\cdot \operatorname{log}\left(\frac{N}{(q+1)}\right)^{2}+2\cdot \operatorname{log}\left(\frac{N}{(q+1)}\right)\cdot (1+\operatorname{log}\left(\frac{2\cdot N}{(q+1)}\right)))+\operatorname{B}\left(N, q, b\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.originalFullCell_finite_transfer_sharp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under exactly the same full-positive hypotheses, define B(N,q,b)=0 if q=0, and B(N,q,b)=h*(3*q/2+2)*V/16 otherwise, h=q+1. The sharp bound is abs(E-Z-C)<=((e+c/h)/L)*N*A*(1+2*u^2+2*u*(1+v))+B. The complete block, nonnegative b, e,c>=0, actual F prefix-error hypothesis and full range 0<=q<=N-2 are unchanged.

The original-owner centered_pair_variation_sharp_bound supplies abs(S(d))<=d*V/16. Shared private centered-log and low-error sums consume this estimate with V/16, using all actual Mobius indices and the literal +2. At q=0 the low error is exactly zero because centered(1,m)=0; the mean remains C(N,0,b)=A(N,b) for N>1. Neither the high error nor the mean is discarded. Both public transfers call the same exact decomposition and final error assembly, retaining PLUS replacement, the literal -2*K(h)/L, the full first moment and the high nonnegativity requirement. No sign is assumed for Abel differences.

For actual partial cells take b(m)=log(N)*omega(a,b,m), N<=a<=b<=2*N. OriginalResidualPartialCellWeights supplies nonnegativity, A=log(N)*(g(a)-g(b)) and V<=2*log(N)*activationDensity(a) through its original private mass and variation proofs. These are applications of the finite theorem, with no vanishing first moment. The primitive estimate also covers N=1; the logarithmic transfer keeps N>=3. Signed MAIN, strict Robin above 5040, cofinal/global transport and RH remain open.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.firstMoment`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.fracPair`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.logDifference`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.logPair`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.meanCorrection`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.originalFullCell_finite_transfer`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.originalFullCell_finite_transfer_sharp`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.pairing`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.polePrefix`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.reciprocalPrefix`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.replacement`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.totalMass`
- Truth anchor: `D5/S3/Arith/Robin/OriginalFullCellFiniteTransfer.weightedVariation`
- Dependency: [D5/S3/Arith/Robin/OriginalResidualFiniteTransfer](OriginalResidualFiniteTransfer.md)
