# Squarefree Integers in the Thirty-Wheel

## Abstract

Universal count and first-moment bounds for squarefree integers coprime to thirty.

For each natural X, good(X) is exactly the finite set of integers d in [7,X] such that gcd(d,30)=1 and d is squarefree. Write K=Nat.sqrt(X), the integer square root. All arithmetic in the following inequalities takes place in the rationals; subtraction is signed, including at X=0.

**Theorem 1.1 (Count and total weight at every cutoff).**

$$\forall X \in \mathrm{Nat},\; \frac{170 \cdot X - 168 \cdot \operatorname{NatSqrt}\left(X\right) - 1083}{675} \le \operatorname{card}\left(\operatorname{good}\left(X\right)\right) \land \frac{85 \cdot X^{2} - 192 \cdot X \cdot \operatorname{NatSqrt}\left(X\right) - 402 \cdot X - 675}{675} \le \sum_{d \in \operatorname{good}\left(X\right)} d$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Mertens/ThirtyWheelSquarefree.count_weight_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let U(Y) count the positive integers at most Y coprime to thirty and let J(Y) be their sum. Write Y=30m+r with 0<=r<30, and let u(r),s(r) be the count and sum of the members of {1,7,11,13,17,19,23,29} at most r. Exact block summation gives U(Y)=8m+u(r) and J(Y)=120m^2+30m*u(r)+s(r). The thirty residue cases give -10<=15u(r)-4r<=14, 15s(r)-2r^2+10r>=0 and 2r^2+16r-15s(r)>=0. Consequently (4Y-10)/15<=U(Y)<=(4Y+14)/15 and (2Y^2-10Y)/15<=J(Y)<=(2Y^2+16Y)/15.

Every integer at least seven coprime to thirty has a representation b+30t with b in {7,11,13,17,19,23,29,31} and t natural. For a>0, 1/(a+30)^2 <= 1/(30a)-1/(30(a+30)). Finite telescoping bounds each progression by 1/b^2+1/(b+30)^2+1/(30(b+30)). The sum of these eight rational quantities is strictly less than 1/18. Thus the finite sum of 1/k^2 over 7<=k<=K coprime to thirty is less than 1/18 for every K, including K=0.

Mathlib's Nat.squarefree_iff_prime_squarefree supplies a prime-square divisor of each nonsquarefree positive integer d. If d is coprime to thirty, this prime is also coprime to thirty and is at least seven. Its square dividing d<=X implies that the prime is at most K. Enlarge the primes to all k in [7,K] coprime to thirty. The unit multiples of k^2 are exactly k^2*t for unit t<=X/(k^2). The same nonnegative finite union bound therefore bounds the discarded count B by the sum of U(X/(k^2)), and the discarded weight E by the sum of k^2*J(X/(k^2)). Natural quotients are used.

For X>=1, the number of these k is U(K)-1<=(4K-1)/15. The wheel bounds, quotient inequalities and reciprocal telescope give B<=2X/135+56K/225-14/225 and E<=X^2/135+64XK/225-16X/225. Removing exactly the bad units and the unit 1 gives U(X)=1+card(good(X))+B and J(X)=1+sum(good(X))+E. Combining these identities proves both bounds. At X=0 the good set is empty and both rational lower bounds are negative. The empty index sets for K<7 and the first square divisor 49 require no additional premise.

These finite arithmetic estimates do not construct Mobius octets or their bounded-variation consumer. They assert no global residual sign, signed MAIN, Robin inequality for every n>5040, or RH.

## References

- Truth anchor: `D5/S3/Weil/Mertens/ThirtyWheelSquarefree.count_weight_lower_bound`
