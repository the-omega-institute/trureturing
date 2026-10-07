# Neutral Tents and the Square-Root Response Obstruction

## Abstract

Two exact zero moments and bounded increments do not give a uniform square-root response bound.

Fix phi to be the positive golden ratio and q=phi^(-2). The kernel k is precisely BinetPositiveResponse.response(q,hq), where hq proves q>0. Thus k is the Dirichlet inverse of the literal Binet logarithmic coefficient applied to the arithmetic logarithm. It is not a free kernel or an assumed response law.

For positive integer m, use u(m)=1/(m(m+1)) and v(m)=log(m)/m-log(m+1)/(m+1). Let K(J) be the sum of k(d) over 1<=d<=J, and let T(f,N) be the sum of k(d)f(floor(N/d)) over 1<=d<=N. All sequences are real-valued and indexed by natural numbers.

Write S(f) for the set of |f(m)|/sqrt(m) at positive integer m. The predicate I(f) below requires f(0)=0, summability of both positive-index moment series, both exact zero moments, nonemptiness and upper boundedness of S(f), sup S(f)<=1, the pointwise envelope |f(m)|<=sqrt(m) for every natural m, and |f(m)-f(m-1)|<=1 for every m>=1. It has no finite-support restriction.

$\operatorname{I}\left(f\right)\iff (\operatorname{f}\left(0\right)=0\land \operatorname{Summable}\left(m\mapsto\operatorname{f}\left(m+1\right)\operatorname{u}\left(m+1\right)\right)\land \operatorname{Summable}\left(m\mapsto\operatorname{f}\left(m+1\right)\operatorname{v}\left(m+1\right)\right)\land \sum_{m\ge1}\operatorname{f}\left(m\right)\operatorname{u}\left(m\right)=0\land \sum_{m\ge1}\operatorname{f}\left(m\right)\operatorname{v}\left(m\right)=0\land \operatorname{Nonempty}\left(\operatorname{S}\left(f\right)\right)\land \operatorname{BddAbove}\left(\operatorname{S}\left(f\right)\right)\land \operatorname{sup}\left(\operatorname{S}\left(f\right)\right)\le1\land (\forall m\in\mathbb{N}, \lvert\operatorname{f}\left(m\right)\rvert\le\sqrt{m})\land (\forall m\ge1, \lvert\operatorname{f}\left(m\right)-\operatorname{f}\left(m-1\right)\rvert\le1))$

The final quantifier uses O(f), the original zero value, two zero moment identities, bounded unit supremum norm, and unit adjacent increments. This class has no finite-support restriction. Every constructed member of I also belongs to O.

$\operatorname{O}\left(f\right)\iff (\operatorname{f}\left(0\right)=0\land \sum_{m\ge1}\operatorname{f}\left(m\right)\operatorname{u}\left(m\right)=0\land \sum_{m\ge1}\operatorname{f}\left(m\right)\operatorname{v}\left(m\right)=0\land \operatorname{Nonempty}\left(\operatorname{S}\left(f\right)\right)\land \operatorname{BddAbove}\left(\operatorname{S}\left(f\right)\right)\land \operatorname{sup}\left(\operatorname{S}\left(f\right)\right)\le1\land (\forall m\ge1, \lvert\operatorname{f}\left(m\right)-\operatorname{f}\left(m-1\right)\rvert\le1))$

**Theorem 1.1 (The actual response is unbounded on the entire neutral input class).**

$$(\exists F: \mathbb{N}\to\mathbb{N}\to\mathbb{R}, \forall J\in\mathbb{N}, 2\le J\Rightarrow (\operatorname{Finite}\left(\operatorname{support}\left(\operatorname{F}\left(J\right)\right)\right)\land \operatorname{I}\left(\operatorname{F}\left(J\right)\right)\land \frac{\operatorname{K}\left(J\right)}{16\sqrt{J}}\le\frac{\operatorname{T}\left(\operatorname{F}\left(J\right), 64J^{3}\right)}{\sqrt{64J^{3}}}))\land \lim_{J\to\infty}\frac{\operatorname{K}\left(J\right)}{16\sqrt{J}}=\infty\land \neg(\exists C\in\mathbb{R}, \forall f:\mathbb{N}\to\mathbb{R}, \operatorname{O}\left(f\right)\Rightarrow \forall N\in\mathbb{N}, 1\le N\Rightarrow \frac{\lvert\operatorname{T}\left(f, N\right)\rvert}{\sqrt{N}}\le C)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/NeutralTentResponseObstruction.neutral_tent_response_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There is one family F, with f_J=F(J), whose members have finite support and satisfy every condition in I simultaneously for every J>=2, including J=2. At the same integer cutoff N_J=64J^3, the signed response divided by sqrt(N_J) is at least K(J)/(16sqrt(J)). This lower bound tends to positive infinity as J tends to infinity through the integers.

For each 2<=j<=J put m_j=floor(N_J/j) and R_j=floor(sqrt(m_j)/8). Three literal max/absolute-value tents, centered at m_j-2R_j, m_j and m_j+2R_j, are combined with coefficients (-alpha_j,1,-eta_j)/2. The ratio v(m)/u(m) is strictly increasing: its adjacent difference is (m+1)log((m+1)^2/(m(m+2)))>0. Ordered positive weighted averages therefore give the two exact compensating coefficients, with 0<alpha_j<1 and 0<eta_j<2.

Each pulse has both exact zero moments, center value R_j/2, the square-root envelope and unit increments. An adjacent pair can meet the nonzero support of at most one individual tent; the same property holds between different j blocks. This checks the zero seams as well as the interior slopes. All supports lie in the finite interval from 1 to N_J, so the finite moment cancellations are also the exact infinite sums.

The endpoint quotient identities are floor(N_J/(m_j-3R_j+1))=j and floor(N_J/(m_j+3R_j))=j-1. Consequently only d=j samples the j-th pulse, at its center; d=1, d=J+1 and all other divisor indices contribute zero to that pulse. The exact response is one half of the sum of k(j)R_j over 2<=j<=J. Since R_j>=J and k(1)=0, this is at least J K(J)/2. The identity sqrt(N_J)=8J sqrt(J) gives the original 1/16 constant.

The actual Binet contract supplies a positive constant c with k(j)>=c log(j). Thus K(J)>=(J-1)c log(2) for J>=2, and K(J)/(16sqrt(J)) is at least c log(2)sqrt(J)/32. A uniform constant for every member of O and every positive cutoff would contradict this divergence. The finite-support family is used to refute a bound on the entire original class O, rather than defining that class.

The inputs change with J. They are not the actual arithmetic partial sums H, and no fixed finite-support input is asserted to have a divergent normalized response. The obstruction proves no improvement to a Robin estimate or the Riemann hypothesis.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/NeutralTentResponseObstruction.neutral_tent_response_obstruction`
- Dependency: [D5/S3/Arith/FibonacciAtomic/BinetPositiveResponse](BinetPositiveResponse.md)
