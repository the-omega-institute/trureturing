# A single deferred occurrence controls both native coordinates

## Abstract

Uniform physical joint orders for equal short gaps and one long gap

**Theorem 1.1 (The unbounded physical construction).**

Lean statement: `D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/Uniform.actualSource_uniform_one_long_joint`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/Uniform.actualSource_uniform_one_long_joint` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every a>=2, p>=1 and d>=a, set E=geom(a,p) and k=d+a(p-1). The theorem proves OriginalOrder(k,E,sigma) and OriginalOrder(k+1,2E,earWord(k,sigma,cut)) for the explicit physicalWord sigma. Each predicate contains the once-only physical Fin-label inventory, its own zero total and the closed strip bound for every natural take-prefix, including empty and saturated takes. The hypotheses contain no feasibility certificate, finite bound, coprimality, primitivity or distinct-value condition.

When d=a or d=a+1, sigma is the ascending physical word. For d>=a+2, put t=d-a-1. Its exact natural labels are [0,t) followed by [t+1,k-a), then t, then [k-a,k). The intervals can be empty. The fresh physical last label is inserted at cut a-1 when d=a and at cut k-1 otherwise. The one-negative case p=1 is included: the empty middle returns t to its original ascending position. The inventory proof partitions literal labels; no sorting or identification of equal source values is used.

The mechanism is the dyadic group action x maps to 2x on the odd cyclic modulus. Grouping a actions yields x maps to R*x, R=2^a. The old source value f and same-phase nonnegative charge c determine the enlarged value g=2f-c at each retained physical occurrence. The fresh value is E. The native digit_data and charge_sum supply this coupling and its total charge E; actualSource and centered uniqueness supply the source interpretation.

Write D=2^d, A_j=geom(a,j+1), and P_j=A_j+D*R^j*geom(a,p-1-j). A positive packet has old values 2^u*P_j and enlarged values 2^u*(2P_j-A_j), both positive. With q=2^(a-1), the old peak drift is R^j*(R-D)/2 and the valley drift is R^j*(R-D). Their nonpositive signs propagate the initial peak bound and final valley bound through arbitrarily many packets. The general descending-packet proof also includes every partial positive packet. The last positive packet is excluded from the middle charge estimate, which is exactly A=geom(a,p-1). This exclusion is essential for the lower bound in the enlarged coordinate.

For d>a put l=2^(d-a-1), M=R^(p-1), B=2^(k-1), T=q*A+1. If d=a+1, the first peak is B-1 and the last middle valley is M. If d>=a+2, deferring label t subtracts l*E: the first peak becomes B-E-l and the final middle valley is (2l-1)M-l*E, at least A+1. Thus the middle lies in A<=F<=B-1 and has 0<=C<=A, so its same-word enlarged height 2F-C lies in [0,2B-1]. Returning t and the final positive packet increases both coordinates to the legal endpoint (B-T,2B-E-T). Fresh then raises the second coordinate to 2B-T, and the last old negative returns both totals to zero.

On d=a the literal ascending blocks have sharp old height E*(2^(a-1)-1). The fresh occurrence after the initial positive run and total charge bound keep every enlarged prefix legal. For p=1, the old positives have charge zero, reach B-1, and fresh reaches the enlarged upper boundary 2B-1 before the final negative. These are separate proofs of the degenerate and exactly periodic boundaries. The result strengthens the arbitrary-number equal-short-gap component; the general physical joint-order problem and unrelated lifts remain outside its scope. No literature novelty, official acceptance or broad-goal completion is asserted.

## References

- Truth anchor: `D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/Uniform.actualSource_uniform_one_long_joint`
- Dependency: [D5/S3/Combinatorics/Circle/EqualShortGapsOneLong/Arithmetic](Arithmetic.md)
