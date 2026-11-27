# Uniform noisy interval recovery

## Abstract

Uniform stability for complete inclusive interval observations of monotone real tuples.

**Theorem 1.1 (A constant depending only on the length).**

$$\forall n: Nat, 3 \le n \Rightarrow \exists C: Real, 0 \le C \land \forall a: \operatorname{Fin}\left(n\right) \to Real, \forall b: \operatorname{Fin}\left(n\right) \to Real, \operatorname{Nonnegative}\left(a\right) \Rightarrow \left(\operatorname{Nonnegative}\left(b\right) \Rightarrow \left(\operatorname{Monotone}\left(a\right) \Rightarrow \left(\operatorname{Monotone}\left(b\right) \Rightarrow \forall epsilon: Real, 0 \le epsilon \Rightarrow \forall pi: \operatorname{Perm}\left(\operatorname{O}\left(n\right)\right), \left(\forall p: \operatorname{O}\left(n\right), \lvert\operatorname{S}\left(a, p\right) - \operatorname{S}\left(b, \operatorname{apply}\left(pi, p\right)\right)\rvert \le epsilon\right) \Rightarrow \forall i: \operatorname{Fin}\left(n\right), \lvert\operatorname{apply}\left(a, i\right) - \operatorname{apply}\left(b, i\right)\rvert \le C \cdot epsilon\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/IntervalReconstruction/MonotoneIntervalStability.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For n≥3, O(n) is the finite set of endpoint pairs (i,j) with 0≤i<j<n. For a tuple a:Fin(n)→Real, S(a,(i,j)) is the sum of a(r) over every i≤r≤j, including both endpoints. It is exactly Omega.MonotoneIntervalReconstruction.intervalSum applied to the tuple extended by zero outside Fin(n); no outside value occurs in these sums. Nonnegative(a) means every coordinate is nonnegative, and Monotone(a) means a(i)≤a(j) whenever i≤j. Perm(O(n)) consists of all bijections of the actual endpoint occurrences. Equal interval sums remain distinct occurrences. Singletons are omitted.

Fix a permutation π. On the vector space of pairs (a,b), impose the homogeneous linear inequalities expressing nonnegativity and monotonicity of both tuples, together with both signs of every linear difference S(a,p)−S(b,π(p)). Their common cone therefore consists exactly of monotone nonnegative pairs with exact matched observations. A noisy pair violates every defining inequality by at most ε. The homogeneous Hoffman bound supplies a point (a′,b′) of this cone whose displacement, measured by each coordinate-difference functional (x,y)↦x(i)−y(i), is at most C(π)ε.

The occurrence bijection gives equality of the actual observation multisets for a′ and b′, with all multiplicities. The existing exact reconstruction theorem gives a′=b′. Consequently the same bound controls |a(i)−b(i)|. There are finitely many permutations of O(n). Choose the nonnegative constant C as the sum of their constants C(π); it dominates every one of them and is chosen before a, b, ε and π. This proves the displayed statement for all n≥3.

Hoffman's homogeneous error bound follows from Tucker's alternative. A nonnegative linear relation among the defining functionals identifies the functionals that must vanish on the cone. A linear pseudo-inverse projects onto their common kernel with displacement controlled by the inequality residuals. The remaining functionals admit a common strictly positive direction in that kernel; moving along it by a multiple of ε satisfies all the inequalities. This produces the required C(π) without a separation assumption on the interval sums. Hoffman's classical source is On approximate solutions of systems of linear inequalities, Journal of Research of the National Bureau of Standards 49 (1952), 263–265. Tucker's Dual systems of homogeneous linear relations appears in Linear Inequalities and Related Systems, Annals of Mathematics Studies 38 (1956).

All-zero tuples, repeated coordinates, tied sums and zero noise are included. No strictness, separation, integrality, magnitude bound, genericity or compatibility of matched endpoints is assumed. The result asserts existence of a finite real constant; it supplies no optimal constant, efficient reconstruction algorithm or solution of general Turnpike.

## References

- Truth anchor: `D5/S3/Combinatorics/IntervalReconstruction/MonotoneIntervalStability.result`
