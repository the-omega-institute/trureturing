# Sharp quadratic loads on stars

## Abstract

The star has explicit optimal quadratic shares and an explicit maximizing probability vector. Its value also bounds every finite graph from below through its maximum degree.

For an integer m at least one, let H(m) be the simple star on Option(Fin(m)), with centre none and leaves some(i). Write s for the positive square root of m and t for 1/(1+s). The allocation a(m)(b,c) is t when b is the centre and 1-t otherwise. These formulas also bound the irrelevant nonedge coordinates. The probability vector mu(m) assigns t to the centre and 1/(s(1+s)) to every leaf. The function Phi(m) sums p(b)p(c)/(p(b)+p(c)) once over each unordered edge. Real division assigns zero when both coordinates vanish. The simplex contains every nonnegative vector of total mass one, including vectors with zero coordinates.

$\mathrm{q}\left(m\right) = \frac{m}{\left(1 + \mathrm{sqrt}\left(m\right)\right)^{2}}$

**Theorem 1.1 (Every graph contains the maximum-degree obstruction).**

$$\forall V \in \mathrm{Type},\; [\mathrm{Fintype}\left(V\right)] [\mathrm{Nonempty}\left(V\right)] \forall G \in \mathrm{SimpleGraph}\left(V\right),\; [\mathrm{DecidableRel}\left(\mathrm{Adj}\left(G\right)\right)] 1 \le \mathrm{maxDegree}\left(G\right) \Rightarrow \frac{\mathrm{maxDegree}\left(G\right)}{\left(1 + \mathrm{sqrt}\left(\mathrm{maxDegree}\left(G\right)\right)\right)^{2}} \le \mathrm{kappa}\left(G\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadraticLoad/StarExtrema.maximum_degree_lower_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take an actual minimum allocation and a vertex b of maximum degree D. Set s equal to the square root of D and t equal to 1/(1+s). For each neighbour c, the complementary shares x and 1-x satisfy s*x*x+(1-x)*(1-x) at least s*t: their difference is (1+s)(x-t)^2. Summing gives D*s*t at most s times the load at b plus the sum of the loads at its neighbours. The latter is at most (s+D) times kappa. Cancellation gives D/(1+s)^2 at most kappa. Additional edges among the neighbours only add nonnegative squares to their loads; neither connectivity nor regularity is required.

**Theorem 1.2 (Both attained extrema on every star).**

$$\forall m \in \mathrm{Nat},\; 1 \le m \Rightarrow \left(\mathrm{Feasible}\left(\mathrm{H}\left(m\right), \mathrm{a}\left(m\right)\right) \land \left(\left(\forall b \in \mathrm{Option}\left(\mathrm{Fin}\left(m\right)\right),\; \mathrm{load}\left(\mathrm{H}\left(m\right), \mathrm{a}\left(m\right), b\right) = \mathrm{q}\left(m\right)\right) \land \left(\mathrm{kappa}\left(\mathrm{H}\left(m\right)\right) = \mathrm{q}\left(m\right) \land \left(\mathrm{mu}\left(m\right) \in \mathrm{stdSimplex}\left(\mathrm{Real}, \mathrm{Option}\left(\mathrm{Fin}\left(m\right)\right)\right) \land \left(\mathrm{Phi}\left(m, \mathrm{mu}\left(m\right)\right) = \mathrm{q}\left(m\right) \land \left(\left(\forall p \in \mathrm{Option}\left(\mathrm{Fin}\left(m\right)\right) \to \mathrm{Real},\; p \in \mathrm{stdSimplex}\left(\mathrm{Real}, \mathrm{Option}\left(\mathrm{Fin}\left(m\right)\right)\right) \Rightarrow \mathrm{Phi}\left(m, p\right) \le \mathrm{q}\left(m\right)\right) \land \left(\left(m = 1 \Rightarrow \mathrm{kappa}\left(\mathrm{H}\left(m\right)\right) = \frac{1}{4}\right) \land \left(m = 2 \Rightarrow \mathrm{kappa}\left(\mathrm{H}\left(m\right)\right) = 2 \cdot \left(3 - 2 \cdot \mathrm{sqrt}\left(2\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/QuadraticLoad/StarExtrema.star_extrema` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The centre load is m*t*t, and each leaf load is (1-t)^2=m*t*t. This allocation gives the upper bound, while the maximum-degree estimate gives the reverse bound. The displayed measure has mass one and gives t*t on every edge. For any nonnegative competing masses x and y, xy/(x+y) is at most x*t*t+y*(1-t)^2. When x+y is positive, clearing the denominator leaves the square (x*t-y*(1-t))^2; at x=y=0 both sides vanish. Summing over the m edges bounds every competing probability vector by q(m). Thus both extrema are attained on their full carriers. For m=1 the value is one quarter; for m=2 it is 2(3-2*sqrt(2)). These conclusions alone do not establish growth or legal-word bounds.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticLoad/StarExtrema.maximum_degree_lower_bound`
- Truth anchor: `D5/S3/Combinatorics/Graph/QuadraticLoad/StarExtrema.star_extrema`
- Dependency: [D5/S3/Combinatorics/Graph/QuadraticEdgeLoad](../QuadraticEdgeLoad.md)
