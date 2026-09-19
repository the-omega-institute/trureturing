# A Uniform Bound for Antidiagonal Grid Traffic

## Abstract

A uniform strict binomial-ratio bound for antidiagonal grid obstructions at every n at least 496.

Gil, Liang, Odetola and Weiner consider north-east lattice paths from (0,0) to (n,n) avoiding an obstruction B. Their Conjecture 7.4 concerns the points of maximum traffic when B lies on x+y=n. The arithmetic theorem below establishes a stronger sufficient strict inequality. The grid and path-count statements used to obtain the ordinary grid conclusion are published literature inputs; they are not Lean-verified in this module.

**Definition 1.1 (The rational traffic ratio).**

Lean statement: `D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound.claim`

*Formalization.* `D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Juan Gil, Zhenni Liang, Ayodeji Odetola, Michael Weiner (2026). *Points of maximal traffic on a grid with obstruction*. URL: <https://arxiv.org/abs/2609.01562>.

*Commentary.*

Let n and a be natural numbers with n at least 496, a at least one, and 2a<n. Binomial coefficients are natural numbers, and the divisions in the following ratio take place in the rational numbers:$\operatorname{R}\left(n, a\right) = \frac{\frac{n \cdot \left(n - 2 \cdot a + 1\right)}{n - a} \cdot \operatorname{choose}\left(n, a\right) \cdot \operatorname{choose}\left(n - 2, a - 1\right)}{\operatorname{choose}\left(2 \cdot n - 2, n - 1\right)}$

The proposition claim says R(n,a)<1 for every such pair, without an upper bound on n. In particular it includes a=1 and the odd near-central pair (n,a)=(497,248). The condition 2a<n uses no truncated division by two. All subtractions occurring in binomial indices and denominators are nonnegative on this domain, and both denominators are positive.

**Theorem 1.2 (The uniform strict inequality).**

$$\forall n \in \mathbb{N}, a \in \mathbb{N},\; \left(496 \le n \land \left(1 \le a \land 2 \cdot a < n\right)\right) \Rightarrow \frac{\frac{n \cdot \left(n - 2 \cdot a + 1\right)}{n - a} \cdot \operatorname{choose}\left(n, a\right) \cdot \operatorname{choose}\left(n - 2, a - 1\right)}{\operatorname{choose}\left(2 \cdot n - 2, n - 1\right)} < 1$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Juan Gil, Zhenni Liang, Ayodeji Odetola, Michael Weiner (2026). *Points of maximal traffic on a grid with obstruction*. URL: <https://arxiv.org/abs/2609.01562>.

*Commentary.*

Put k=n-2a and write T(n,k)=R(n,(n-k)/2) on the domain k>=1, n>=k+2 and n congruent to k modulo two. The identity choose(n-2,a-1)=a(n-a)choose(n,a)/(n(n-1)) gives$\operatorname{T}\left(n, k\right) = \frac{\left(n - k\right) \cdot \left(k + 1\right)}{2 \cdot \left(n - 1\right)} \cdot \frac{\operatorname{choose}\left(n, \frac{n - k}{2}\right)^{2}}{\operatorname{choose}\left(2 \cdot n - 2, n - 1\right)}$

First fix n. Lowering a by one increases k by two, and the quotient of successive T values is (n-k)(n-k-2)(k+3)/((n+k+2)^2(k+1)). Its numerator minus denominator is -2F(n,k), where F(n,k)=2k^2 n+7kn+k-n^2+5n+2. For n>=496 and 1<=k<=14, F(n,k)<=-n^2+495n+16<0. Thus every small-gap value is bounded above by a value in the same row with k>=15. The move is always legal: these small gaps force a>=2. Repetition terminates because a decreases. Parity gives k>=16 in even rows; odd rows can retain k=15.

Next fix k>=3 and let n vary with the same parity. The exact quotient is$\frac{\operatorname{T}\left(n + 2, k\right)}{\operatorname{T}\left(n, k\right)} = \frac{4 \cdot n \cdot \left(n - 1\right) \cdot \left(n + 1\right)^{2} \cdot \left(n + 2\right)^{2}}{\left(n - k\right) \cdot \left(n - k + 2\right) \cdot \left(2 \cdot n - 1\right) \cdot \left(2 \cdot n + 1\right) \cdot \left(n + k + 2\right)^{2}}$

Let Delta(n,k) be the numerator minus denominator of this quotient, and put x=n-k>0. Dividing Delta(k+x,k) by x^5 gives -4 plus five positive coefficients times 1/x, 1/x^2, ..., 1/x^5. The coefficients are positive for k>=3, as their expansions in k-3 have positive coefficients. Hence this expression decreases with x. For e=0 or 1, direct polynomial factorization gives Delta(N-2,k)>0 and Delta(N,k)<0 at N=2k(k+1)-e. Taking e to be the parity of k, the same-parity sequence therefore increases up to N and decreases after N. In particular, T(n,k)<=T(N,k) for every admissible n.

It remains to bound these infinitely many peaks. For positive m, the pinned Stirling successive-difference estimate is log(s_m)-log(s_(m+1))<=1/(12m(m+1)), with s_m tending to sqrt(pi). Consequently log(s_m)-1/(12m) is increasing to log(sqrt(pi)). This supplies the upper logarithmic factorial remainder 1/(12m); the Stirling lower bound supplies the denominator estimates. These established Stirling results are used inside the peak argument.

For 0<=x<1, set h(x)=(1-x)log(1-x)+(1+x)log(1+x). The logarithmic series lower bound gives h'(x)=log((1+x)/(1-x))>=2x. Since h(0)=0, one obtains h(x)>=x^2. Apply this with x=k/n, and combine the upper estimates for n! and (n-1)! with the lower estimates for a!, (n-a)! and (2n-2)!. Cancellation in the logarithm of T gives the weak bound T(n,k)<=B(n,k), where$\operatorname{B}\left(n, k\right) = \frac{4 \cdot n \cdot \left(k + 1\right)}{\left(n + k\right) \cdot \operatorname{sqrt}\left(\pi \cdot \left(n - 1\right)\right)} \cdot \operatorname{exp}\left(\frac{1}{6 \cdot n} - \frac{k^{2}}{n} + \frac{1}{6 \cdot \left(n - 1\right)}\right)$

Each parity envelope B(2k(k+1)-e,k) decreases for real k>=3. The two remainder terms decrease because 2k(k+1)-e increases. The logarithmic derivative of the remaining factor for e=0 is -(4k^3+20k^2+28k+11)/(2(k+1)^2(2k+3)(2k^2+2k-1)), which is negative. For e=1 it is -P(k)/(2(k+1)(k^2+k-1)(2k^2+2k-1)^2(2k^2+3k-1)), where P(k)=8k^7+48k^6+80k^5+12k^4-52k^3-3k^2+20k-5. Expanding P in k-2 gives positive coefficients, so this derivative is also negative throughout the required interval.

At the even base (N,k)=(544,16), it suffices to prove 5345344/665175 < pi exp(832961/886176). At the odd base (N,k)=(611,17), it suffices to prove 60478002/7517945 < pi exp(352173/372710). Both follow by rational arithmetic from pi>157/50 and the positive exponential Taylor sums through degrees six and four, respectively. Monotonicity now bounds every even peak with k>=16 and every odd peak with k>=17 strictly below one. This is the uniform peak estimate used by the theorem.

The remaining odd gap k=15 has its peak at N=479. Thus its sequence decreases over all odd n>=497. The exact local certificate 241 choose(497,241)^2 < 31 choose(992,496) gives T(497,15)=R(497,241)<1. Together with the low-gap ascent and the uniform large-gap estimate, this bounds every original R(n,a) strictly below one. Casting between the rational and real expressions preserves the inequality.

To recover the ordinary grid conclusion, use Section 6 of arXiv:2609.01562v1. For n>=9 it reduces the maximum to six corner-adjacent points except for obstructions in {(1,2),(2,1),(n-1,n-2),(n-2,n-1)}. Their coordinate sums are 3 or 2n-3, neither of which equals n when n>=496. For an interior obstruction B=(a,n-a) with 2a<n, Proposition 7.1 pairs opposite candidates and identifies (1,0) as the larger boundary competitor. Proposition 7.2 gives f_B(1,0)-f_B(1,1)=D(n)(R(n,a)-1), with D(n)=choose(2n-2,n-1)/n>0. The strict arithmetic bound defeats that competitor, so both (1,1) and (n-1,n-1) attain the maximum.

Equation (2.1), using coordinate interchange, covers the interior half 2a>n. At the even central obstruction 2a=n, Theorem 5.1 applies because n>=496 implies n>=5; its two cases give the two near-corner maximizers. At a=0 or a=n, Lemma 2.2(ii) and (iii) both apply and give the same conclusion. This accounts for every antidiagonal obstruction in the published conjecture. These grid reductions remain literature inputs, not Lean grid/path theorems here. Only the sufficient implication from R<1 is used; no converse or assertion excluding other tied maximizers is made.

## References

- Truth anchor: `D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound.claim`
- Truth anchor: `D5/S3/Arith/FactorialRatio/GridAntidiagonalTrafficBound.result`
