# Finite Transfer of the Original Mobius Floor Residual

## Abstract

The unchanged finite Mobius floor response admits an explicit residual transfer with both moments, weighted floor variation and exact prefix payments.

All sequences are real-valued on the natural numbers. All logarithms are natural. Fix natural N>=3 and 0<=q<=N-2, put h=q+1 and L=log N. The integer block is N<=m<2N. Empty sums are zero. The arithmetic function mu is Mathlib's actual Mobius function at every index, without a prime-only restriction or any modification at prime powers. M(k) is the existing full inclusive prefix sum of mu(d) for 1<=d<=k.

The source-bound audit for log_bounds remains declared_unresolved under IE-C050/source.unsafe_or_external (Nat.add). The missing source-reconstruction binding certificate is tracked at https://github.com/the-omega-institute/trureturing/issues/17873. This is an unfinished audit, not a failure of the compiled inequality or evidence of a judge defect. The other new helper audits and full-positive transfer audit are validated.

**Definition 1.1 (Absolute block mass).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.mass`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.mass` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N and real sequence a, A=mass(N,a)=sum(N<=m<2N,abs(a(m))).

**Definition 1.2 (First absolute moment on the original block).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.firstAbsoluteMoment`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.firstAbsoluteMoment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N and real sequence a, B=firstAbsoluteMoment(N,a)=sum(N<=m<2N,m*abs(a(m))). The actual integer index remains inside the sum.

**Definition 1.3 (Variation of the zero extension).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.variation`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.variation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N and a, V=variation(N,a)=abs(a(N))+sum(N<=m<2N-1,abs(a(m+1)-a(m)))+abs(a(2N-1)). For N>=1 this is precisely the variation of a on the block extended by zero outside it. Both jumps remain.

**Definition 1.4 (The actual integer floors).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.floorPair`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.floorPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N,d and sequence a, H(d)=floorPair(N,a,d)=sum(N<=m<2N,a(m)*floor(m/d)). The formal definition uses natural division; for d>=1 it is exactly the floor of the nonnegative real quotient.

**Definition 1.5 (Logarithmic floor pairing).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.logPair`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.logPair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N,d and sequence a, G(d)=logPair(N,a,d)=log(N/d)*H(d).

**Definition 1.6 (The complete consecutive difference).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.logDifference`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.logDifference` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N,k and a, J(k)=logDifference(N,a,k)=G(k)-G(k+1).

**Definition 1.7 (Denominator-weighted variation).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weightedVariation`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weightedVariation` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,h,a, W=weightedVariation(N,h,a)=sum(h<=k<N,k*abs(J(k))).

**Definition 1.8 (Unchanged logarithmic Mobius coefficients).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.coefficient`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.coefficient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every natural N,d, alpha(d)=coefficient(N,d)=mu(d)*log(N/d)/log N. The coefficient at d=1 is retained, and the logarithmic weight at d=N is zero.

**Definition 1.9 (The original affine and floor response).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.response`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.response` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,m, response(N,m)=1+C*m-sum(1<=d<=N,alpha(d)*floor(m/d)), where C=sum(1<=d<=N,alpha(d)/d). Both the constant and the full linear coefficient are included in this definition.

**Definition 1.10 (Pairing with the original response).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.residual`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.residual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,a, E=residual(N,a)=sum(N<=m<2N,a(m)*response(N,m)).

**Definition 1.11 (High-prefix replacement with the literal constant).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.replacement`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.replacement` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every N,q,a,F, Z=replacement(N,q,a,F)=-sum(q+1<=k<N,(F(k)+2)*J(k))/log N. The +2 pays a literal -2 in a supplied spectral prefix and is not absorbed into an endpoint.

**Definition 1.12 (The nonzero integer mean).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered`

*Formalization.* `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For all natural d,m, centered(d,m)=(m mod d)/d-(d-1)/(2*d). For d>=1 the subtracted mean is the exact average on integer residues, including residue zero.

**Theorem 1.13 (The original quotient decomposition).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered_floor`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered_floor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural d>0 and m, floor(m/d)=m/d-centered(d,m)-(d-1)/(2*d), where the quotient on the left is natural division and the other quotient is real.

**Theorem 1.14 (Nonnegative complete variation).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.variation_nonneg`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.variation_nonneg` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural N and arbitrary real sequence a, variation(N,a)>=0, including both endpoint absolute values and the entire interior difference sum.

**Theorem 1.15 (Centered pairing with both jumps).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered_pair_variation_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered_pair_variation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural N,d with N>0 and d>0 and every real sequence a, abs(sum(N<=m<2N,a(m)*centered(d,m)))<=d*variation(N,a). No moment condition is needed. The same periodic primitive and summation-by-parts proof supply the two-moment floor bound and the full positive mean remainder.

**Theorem 1.16 (Sharp centered pairing with both jumps).**

$$\forall N,d\in \mathbb{N},\forall a\in \mathbb{R}^{\mathbb{N}},0< N\land 0< d\Rightarrow \lvert \operatorname{S}\left(N, d, a\right)\rvert \le \frac{d}{16}\cdot \operatorname{V}\left(N, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered_pair_variation_sharp_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every positive natural N,d and arbitrary real sequence a, let S(N,d,a)=sum(N<=m<2*N,a(m)*centered(d,m)). Then abs(S)<=d*V/16, where V=variation(N,a) includes both zero-extension jumps. No sign or moment hypothesis is imposed, including at N=1.

For the original private primitive P=r*(r-d)/(2*d), r=m mod d, 0<=r<=d and (2*r-d)^2>=0 give -d/8<=P<=0. Hence Q=P+d/16 satisfies abs(Q)<=d/16. The unchanged primitive_step supplies the wrap. Q is not the zero-based prefix: Q(0)=d/16. Before taking absolute values, sum(a(m+1)-a(m))=a(2*N-1)-a(N) cancels the shift exactly. Both coarse and sharp bounds use one private finite by-parts assembly, with boundary terms a(2*N-1)*Q(2*N)-a(N)*Q(N). The new range inference is consumed by the sharper full-positive transfer. This finite estimate does not settle signed infinite transport or RH.

**Theorem 1.17 (Reciprocal logarithmic step).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.reciprocal_log_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.reciprocal_log_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k>0, 1/(k+1)<=log(k+1)-log(k).

**Theorem 1.18 (Partial floor count with its negative endpoint).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weighted_floor_prefix_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weighted_floor_prefix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural h,j,m with 0<h<=j<m, sum(h<=k<=j,k*(floor(m/k)-floor(m/(k+1))))<=m*(1+log(j/h))-j. The terminal floor(m/(j+1)) is at least one. Its negative contribution -j is retained for the later joint cancellation.

**Theorem 1.19 (Weighted original floor count).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weighted_floor_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weighted_floor_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural N,h,m with 0<h<N and m<2*N, sum(h<=k<N,k*(floor(m/k)-floor(m/(k+1))))<=2*N*(1+log(2*N/h)). The proof keeps the exact terminal floor before taking its upper bound.

**Theorem 1.20 (Logarithms on the finite divisor range).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.log_bounds`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.log_bounds` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural N,d with 0<d<=N, 0<=log(N/d)<=log(N).

**Theorem 1.21 (Weighted logarithmic step).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weighted_log_step`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weighted_log_step` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k>0, k*(log(k+1)-log(k))<=1.

**Theorem 1.22 (Joint first-moment high variation).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weightedVariation_firstMoment_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weightedVariation_firstMoment_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural N,h with 0<h<=N and arbitrary real a on the original block, assume only sum(N<=m<2N,m*a(m))=0. No zeroth moment is required. Put u=log(N/h) and B=firstAbsoluteMoment(N,a). Then the unchanged weightedVariation(N,h,a)<=B*(u+u*u/2). At h=N both sides vanish. The first moment rewrites the floor pair as a negative remainder pair. For delta(k)=log(k+1)-log(k), triangular finite summation keeps the negative endpoint -j*mass(N,a) until it cancels the entire mass(N,a)*sum(k*delta(k)) payment in the product difference. Finally sum(delta(k)*log(k/h))<=u*u/2 follows by telescoping squares. The existing finite transfer consumes this bound and recovers its old public allowance from B<=2*N*mass(N,a); no residual sign follows.

**Theorem 1.23 (Absolute actual Mobius prefix).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.prefix_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.prefix_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural q, abs(M(q))<=q, with every original Mobius index retained.

**Theorem 1.24 (Exact finite integer sum).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.sum_indices`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.sum_indices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural q, sum(1<=d<=q,d)=q*(q+1)/2 as a real identity.

**Theorem 1.25 (Shared error for an arbitrary finite difference).**

Lean statement: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.prefix_error_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.prefix_error_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For natural N,h with h>0, arbitrary real arrays D,F and real e,c with c>=0, if abs(F(k)-M(k))<=e*k+c for h<=k<N, then abs(sum(h<=k<N,(F(k)-M(k))*D(k)))<=(e+c/h)*sum(h<=k<N,k*abs(D(k))). The statement needs no sign condition on D or vanishing moments.

**Theorem 1.26 (The finite two-moment transfer).**

$$\forall N,q\in \mathbb{N},\forall a,F\in \mathbb{R}^{\mathbb{N}},\forall e,c\in \mathbb{R},3\le N\land q\le N-2\land 0\le e\land 0\le c\land \sum_{m= N}^{2\cdot N-1} \operatorname{a}\left(m\right) = 0\land \sum_{m= N}^{2\cdot N-1} m\cdot \operatorname{a}\left(m\right) = 0\land (\forall k\in \mathbb{N},(q+1)\le k< N\Rightarrow \lvert \operatorname{F}\left(k\right)-\operatorname{M}\left(k\right)\rvert \le e\cdot k+c)\Rightarrow \lvert \operatorname{E}\left(N, a\right)-\operatorname{Z}\left(N, q, a, F\right)\rvert \le \frac{e+\frac{c}{(q+1)}}{\operatorname{log}\left(N\right)}\cdot N\cdot \operatorname{A}\left(N, a\right)\cdot (1+2\cdot \operatorname{log}\left(\frac{N}{(q+1)}\right)\cdot (1+\operatorname{log}\left(\frac{2\cdot N}{(q+1)}\right)))+(q+1)\cdot (\frac{3\cdot q}{2}+2)\cdot \operatorname{V}\left(N, a\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.originalResidual_finite_transfer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let N,q be natural with N>=3 and q<=N-2. Let a,F be arbitrary real sequences, and let e,c be real with e>=0 and c>=0. Assume sum(N<=m<2N,a(m))=0 and sum(N<=m<2N,m*a(m))=0 exactly. At every integer h<=k<N assume abs(F(k)-M(k))<=e*k+c. There is no condition on F below h. Then abs(E-Z) is at most ((e+c/h)/L)*N*A*(1+2*log(N/h)*(1+log(2N/h)))+h*(3*q/2+2)*V.

For d>=1 the centered sawtooth is phi(d,m)=(m mod d)/d-(d-1)/(2*d). Its periodic primitive is P(d,m)=r*(r-d)/(2*d), r=m mod d. The difference P(d,m+1)-P(d,m) equals phi(d,m), including a wrap to residue zero. Since abs(P(d,m))<=d/2, every centered prefix starting at any natural integer is bounded by d. Mathlib's finite summation by parts then gives abs(H(d))<=d*V. The same two moments give H(d)=-sum(a(m)*phi(d,m)); the pointwise sawtooth bound also gives abs(H(d))<=A.

At d=1 the floor is m and the first moment cancels it. At d=N all block floors are exactly one and the zeroth moment cancels them. Thus H(1)=H(N)=G(1)=G(N)=0. Expanding the original response cancels its constant by the zeroth moment and its linear term by the first moment, giving E=-sum(mu(d)*G(d))/L. ActualOddMobiusFinitePairing.prefix_abel supplies the full exact identity E=-sum(1<=k<N,M(k)*J(k))/L.

Actual weighted floor drops satisfy the exact identity sum(h<=k<N,k*(floor(m/k)-floor(m/(k+1))))=h*floor(m/h)+sum(h<=k<N-1,floor(m/(k+1)))-(N-1)*floor(m/N). The terminal floor is nonnegative. The inequalities floor(m/j)<=m/j and 1/(k+1)<=log(k+1)-log k telescope to an upper bound m*(1+log(N/h)), which is at most 2*N*(1+log(2*N/h)) on the original block. Expanding the product difference J(k) and using k*(log(k+1)-log k)<=1 therefore proves W<=N*A*(1+2*log(N/h)*(1+log(2*N/h))).

The exact low prefix is Pq=sum(1<=k<=q,M(k)*J(k))=sum(1<=d<=q,mu(d)*G(d))-M(q)*G(h). Its bound is abs(Pq)/L<=(3/2)*q*(q+1)*V. Telescoping the entire high range gives sum(h<=k<N,J(k))=G(h), so the constant payment is exactly 2*G(h)/L and is bounded in absolute value by 2*h*V. The remaining error is sum(h<=k<N,(F(k)-M(k))*J(k))/L, bounded by ((e+c/h)/L)*W using c>=0. Their sum gives the displayed bound.

The case q=0 has empty low prefix; the case q=N-2 has one high term. Zero e,c,A or V require no special division by these quantities. This theorem is finite and proves no signed spectral inequality. The actual partial-cell integral and Gram projection, analytic residue suppliers, original construction, infinite account, strict Robin above 5040 and RH remain separate obligations.

## References

- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered_floor`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered_pair_variation_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.centered_pair_variation_sharp_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.coefficient`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.firstAbsoluteMoment`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.floorPair`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.logDifference`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.logPair`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.log_bounds`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.mass`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.originalResidual_finite_transfer`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.prefix_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.prefix_error_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.reciprocal_log_step`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.replacement`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.residual`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.response`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.sum_indices`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.variation`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.variation_nonneg`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weightedVariation`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weightedVariation_firstMoment_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weighted_floor_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weighted_floor_prefix_bound`
- Truth anchor: `D5/S3/Arith/Robin/OriginalResidualFiniteTransfer.weighted_log_step`
- Dependency: [D5/S3/Arith/Robin/ActualOddMobiusFinitePairing](ActualOddMobiusFinitePairing.md)
