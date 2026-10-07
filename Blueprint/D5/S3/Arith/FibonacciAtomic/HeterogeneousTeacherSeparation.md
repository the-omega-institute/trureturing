# Sharp Heterogeneous Whole-Window Teacher Separation

## Abstract

Every independent heterogeneous whole-window law with all five symbol masses at least rho separates different increasing priority teachers by the same sharp squared-distance constant, attained within the common-law subclass.

Window is the five-symbol alphabet 000,100,010,101,001 in low-to-high bit order. Its first and last bits are the low and high endpoints. Input(n) contains all words of n whole windows, including every zero window. Positions in Fin(n) start at zero. Roles(n) is the existing type of triples p<q<r. No global seam condition is imposed.

Laws(n) is Fin(n) to Window to the real numbers. Admissible(rho,mu) requires each of the five masses mu(i,a) to be at least rho and each position's total mass to equal one. The input mass is the product of mu(i,w(i)) over all positions. Positions are independent; their laws need not agree. Within one window, the joint high-and-low mass is mu(i,101), rather than the product of the two endpoint marginals.

classValue(t,w) is the real value of the existing priority teacher: it returns 1 when high(w(p)) and low(w(q)) both hold, otherwise 2 when high(w(q)) and low(w(r)) both hold, and 0 otherwise. distance(mu,t,u) is the sum over all complete words of the product input mass times the squared class-value difference. gamma(rho) is 8 times rho squared times (1 minus 2 times rho).

Product expectation productExpectation(mu,f) sums the actual product input mass times f. The functions highIndicator and lowIndicator are the real zero-one endpoint indicators, highMarginal and lowMarginal are their marginal means, and firstGate(t,w)=highIndicator(w(p)) lowIndicator(w(q)) is the first gate. The product formulas for two, three and four positions apply at distinct positions; product_expectation_linear_combination distributes three-term linear combinations. The endpoint and joint means, binary indicators, class formula, marginal interval and Bernoulli discrepancy estimate give the same identities for every actual heterogeneous law.

**Theorem 1.1 (Separation of different first pairs).**

$$\forall \left(n: \mathbb{N}\right), \forall \left(rho: \mathbb{R}\right), \forall \left(mu: \operatorname{Laws}\left(n\right)\right), \forall \left(t: \operatorname{Roles}\left(n\right)\right), \forall \left(u: \operatorname{Roles}\left(n\right)\right), \left(0 < rho \land rho \le \frac{1}{8} \land \operatorname{Admissible}\left(rho, mu\right) \land \left(\operatorname{p}\left(t\right) \neq \operatorname{p}\left(u\right) \lor \operatorname{q}\left(t\right) \neq \operatorname{q}\left(u\right)\right)\right) \implies \left(\operatorname{gamma}\left(rho\right) \le \operatorname{productExpectation}\left(mu, \left(w \mapsto \left(\operatorname{firstGate}\left(t, w\right) - \operatorname{firstGate}\left(u, w\right)\right)^{2}\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation.first_gate_discrepancy_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A shared first position, a shared second position, a crossed position, and disjoint first pairs exhaust the overlaps. The same window joint mass is preserved in the crossed case. In all four cases the squared discrepancy of the binary first gates is at least gamma.

**Theorem 1.2 (A uniform lower bound and an attaining law).**

$$\forall \left(n: \mathbb{N}\right), \forall \left(rho: \mathbb{R}\right), \left(4 \le n \land 0 < rho \land rho \le \frac{1}{8}\right) \implies \left(\left(\forall \left(mu: \operatorname{Laws}\left(n\right)\right), \left(\operatorname{Admissible}\left(rho, mu\right)\right) \implies \left(\forall \left(t: \operatorname{Roles}\left(n\right)\right), \forall \left(u: \operatorname{Roles}\left(n\right)\right), \left(t \neq u\right) \implies \left(\operatorname{gamma}\left(rho\right) \le \operatorname{distance}\left(mu, t, u\right)\right)\right)\right) \land \left(\operatorname{Admissible}\left(rho, \left(i \mapsto \operatorname{extremal}\left(rho\right)\right)\right) \land \exists \left(t: \operatorname{Roles}\left(n\right)\right), \exists \left(u: \operatorname{Roles}\left(n\right)\right), t \neq u \land \operatorname{distance}\left(\left(i \mapsto \operatorname{extremal}\left(rho\right)\right), t, u\right) = \operatorname{gamma}\left(rho\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Finite product factorization integrates every unselected coordinate using its total mass one. These product identities and the Bernoulli discrepancy s+t-2st are standard probability algebra. Both endpoint marginals lie between 2 rho and 1 minus 3 rho. The bilinear discrepancy is minimized at the lower-lower corner on this rectangle.

The uniform estimate treats shared first positions, shared second positions, a crossed middle position, and disjoint first pairs. The crossed case retains the same middle window's low-only, high-only, and joint endpoint masses simultaneously. A first-gate disagreement forces a squared class difference of one, regardless of the third positions. For identical first pairs and different third positions, restricting the middle window to 001 gives a sufficient bound: the first gate vanishes, the second gate is open to either third low bit, and the squared difference is four times their discrepancy.

The public equality clause fixes the admissible common law mu(i,a)=extremal(rho)(a), with masses ((1-3 rho)/2, rho, (1-3 rho)/2, rho, rho) in alphabet order. The triples (0,n-2,n-1) and (1,n-2,n-1) share the last two positions. Their squared class difference equals their first-gate discrepancy, whose expectation is exactly gamma(rho). All five masses satisfy the required lower bound. The universal lower bound and attained equality identify the infimum over all admissible heterogeneous laws and distinct triples. No label channel or sampling guarantee is asserted.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation.first_gate_discrepancy_lower`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/HeterogeneousTeacherSeparation.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap](GarbledPosteriorRootGap.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/LegalPriorityTeacher](LegalPriorityTeacher.md)
