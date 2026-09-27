# The A398542 fixed-bottom polynomial theorem

## Abstract

Rational polynomial witnesses for every actual fixed-bottom completion count.

The target is the exact fixed-bottom conjecture in OEIS A398542 revision 18, August 30, 2026. Perm(m) denotes permutations of Fin(m), translated to the source's 1,...,m by adding one. Avoid132(b) means not Contains(pattern132,b). Every series below is a formal series over Q; no analytic convergence is assumed. The Library note bounds the prior-source comparison and makes no worldwide-priority claim.

**Definition 1.1 (The series of actual cardinalities).**

Lean statement: `D5/S1/Words/Patterns/A398542Polynomial.intervalSeries`

*Formalization.* `D5/S1/Words/Patterns/A398542Polynomial.intervalSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every b in Perm(m) and l,h in N, intervalSeries(b,l,h) is the element of Q[[X]] whose coefficient of X^k, for every k in N, is the rational cast of intervalCount(b,l,h,k). These are cardinalities of actual restricted source permutations.

**Definition 1.2 (The pinned Catalan series over Q).**

Lean statement: `D5/S1/Words/Patterns/A398542Polynomial.catalanQ`

*Formalization.* `D5/S1/Words/Patterns/A398542Polynomial.catalanQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

catalanQ is Mathlib's catalanSeries over N mapped coefficientwise to Q by the natural-number cast ring homomorphism. Write C for this series. The proof uses its existing identity C^2*X+1=C.

**Definition 1.3 (The inverse of the constant-one series).**

Lean statement: `D5/S1/Words/Patterns/A398542Polynomial.centralSeries`

*Formalization.* `D5/S1/Words/Patterns/A398542Polynomial.centralSeries` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

centralSeries, written T, is invOfUnit(1-2X*catalanQ,1). The specified unit is the rational unit one. The constant coefficient of 1-2XC is one; the live proofs discharge this condition before applying the inverse identity. No field structure on Q[[X]] is assumed.

**Theorem 1.4 (The exact interval equation and singleton series).**

Lean statement: `D5/S1/Words/Patterns/A398542Polynomial.actual_series`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/A398542Polynomial.actual_series` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m and every b in Perm(m) avoiding 132, let F(l,h)=intervalSeries(b,l,h). For all l<=h<=m, F(l,h)=1+X*sum over g in [l,h] of F(l,g)*F(g,min(h,dead(b,g)-1)). In addition, for every g<=m, F(g,g)=catalanQ. The equation comes from the actual cardinal convolution; strong coefficient induction identifies the singleton solution uniformly from the actual recurrence.

**Theorem 1.5 (The guarded inverse-power polynomial).**

Lean statement: `D5/S1/Words/Patterns/A398542Polynomial.guarded_polynomial`

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/A398542Polynomial.guarded_polynomial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every m, b in Perm(m) avoiding 132, and natural l<h<=m satisfying h<dead(b,l), there exists A in Q[X] with A.natDegree<=2*(h-l)-2 and intervalSeries(b,l,h)=T*A.eval2(PowerSeries.C,T). Here T=centralSeries. A uniform induction on the interval width separates both endpoint terms, uses smaller guarded children, and treats singleton right children by the Catalan identity. The guard is strict and no monotonicity of dead is used.

**Theorem 1.6 (The entire fixed-bottom conjecture).**

$$\forall m\in\mathbb{N}, 1\le m\Rightarrow \forall b\in\operatorname{Perm}\left(m\right), \operatorname{Avoid132}\left(b\right)\Rightarrow \exists p,q\in\mathbb{Q}[X], \operatorname{natDegree}\left(p\right)\le m-1\land \operatorname{natDegree}\left(q\right)\le m-2\land (m=1\Rightarrow q=0)\land \forall k\in\mathbb{N}, \operatorname{d}\left(b, k\right)=\operatorname{p}\left(k\right)\cdot\operatorname{Nat.choose}\left(2\cdot k, k\right)+\operatorname{q}\left(k\right)\cdot4^{k}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/A398542Polynomial.result` (`✓ std3`). ∎

*Resolves.* `Problems/oeis-a398542-fixed-bottom-polynomial` (proved) by `D5/S1/Words/Patterns/A398542Polynomial.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oeis-a398542-fixed-bottom-polynomial","declaration_gid":"D5/S1/Words/Patterns/A398542Polynomial.result","resolution_kind":"proved"} -->

*Citation.* Charles Cornell Norton (2026). *OEIS A398542: fixed-bottom polynomial conjecture*. URL: <https://oeis.org/A398542>.

*Commentary.*

For every natural m>=1 and every b in Perm(m) avoiding 132, there exist rational polynomials p and q, chosen before k, with p.natDegree<=m-1 and q.natDegree<=m-2 and with q=0 when m=1, such that the displayed identity holds for every natural k, including zero. In the formula d(b,k) is Nat.card of the actual subtype of permutations w in Perm(m+k) whose list of values below m equals the list of b's values, which avoid 1324, and whose upper-value subsequence, read in position order and reduced by m, avoids 213. Thus the value cut is fixed, empty upper cells are allowed, and the actual recurrence gives d(b,0)=1. Nat.choose(2*k,k) is exactly Nat.centralBinom k in Lean. The natural subtractions in the degree bounds truncate at zero; the separate m=1 condition gives the source's negative-degree convention q=0. For m>=2 these are the ordinary degree upper bounds, also allowing zero polynomials. The proof applies guarded_polynomial to [0,m], whose guard follows from dead(b,0)=m+2. It uses the pinned binomial-series and Pochhammer identities directly to extract odd and even powers, including all nonzero denominator obligations. This settles the quoted fixed-bottom assertion alone. It does not enumerate unrestricted 1324 avoiders, compute the full L-gridding generating function, or settle A398446. Worldwide priority remains unclaimed.

## References

- Truth anchor: `D5/S1/Words/Patterns/A398542Polynomial.actual_series`
- Truth anchor: `D5/S1/Words/Patterns/A398542Polynomial.catalanQ`
- Truth anchor: `D5/S1/Words/Patterns/A398542Polynomial.centralSeries`
- Truth anchor: `D5/S1/Words/Patterns/A398542Polynomial.guarded_polynomial`
- Truth anchor: `D5/S1/Words/Patterns/A398542Polynomial.intervalSeries`
- Truth anchor: `D5/S1/Words/Patterns/A398542Polynomial.result`
- Dependency: [D5/S1/Words/Patterns/A398542MinimumRecurrence](A398542MinimumRecurrence.md)
