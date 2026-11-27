# Containment rank bounds for arbitrary real realizations

## Abstract

The whole multiplicity block of every actually realized distance obeys the containment rank bounds.

The containment-based rank bounds are due to Elder, Marçais and Kingsford, WABI 2026, Lemma 14 and Appendix A.3, DOI 10.4230/LIPIcs.WABI.2026.20 (CC BY 4.0). The corresponding arXiv:2603.18283v1 statement is Lemma 13. Rank in the source is any occurrence index in the expanded decreasing distance multiset. Applying both endpoints of a used equal-value block gives the two bounds here.

All indices below are zero-based. Interval(n) is the subtype of pairs (i,j) in Fin(n) with i<j. For e=(i,j), set L(n,e)=(i.val+1)*(n-j.val) and U(n,e)=choose(n,2)-choose(j.val-i.val+1,2)+1, with natural subtraction. Set A(mu,q)=1+sum over r<q of mu(r) and B(mu,q)=sum over r<=q of mu(r). Delta(x,e)=x(j)-x(i). These definitions specify every abbreviation in the closed displayed formula.

**Theorem 1.1 (Whole used blocks and original mask soundness).**

$$\forall \left(n: \operatorname{Nat}\right), \left(\forall \left(d: \operatorname{Nat}\right), \left(\forall \left(y: \operatorname{Fin}\left(d\right) \to \operatorname{Real}\right), \left(\forall \left(mu: \operatorname{Fin}\left(d\right) \to \operatorname{Nat}\right), \left(\forall \left(x: \operatorname{Fin}\left(n\right) \to \operatorname{Real}\right), \left(\forall \left(e: \operatorname{Interval}\left(n\right)\right), \left(\forall \left(q: \operatorname{Fin}\left(d\right)\right), \left(\left(\operatorname{StrictAnti}\left(y\right)\right) \Rightarrow \left(\left(\operatorname{Realizes}\left(y, mu, x\right)\right) \Rightarrow \left(\left(\operatorname{Delta}\left(x, e\right) = y\left(q\right)\right) \Rightarrow \left(\left(\operatorname{L}\left(n, e\right) \le \operatorname{A}\left(mu, q\right)\right) \land \left(\left(\operatorname{B}\left(mu, q\right) \le \operatorname{U}\left(n, e\right)\right) \land \left(\operatorname{RankAllowed}\left(mu, e, q\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Turnpike/ContainmentRankBounds.containment_rank_bounds` (`✓ std3`). ∎

*Citation.* C. S. Elder, Guillaume Marçais, Carl Kingsford (2026). *Turnpike with Uncertain Measurements: Triangle-Equality Integer Programming with a Deterministic Recovery Guarantee*. DOI: [10.4230/LIPIcs.WABI.2026.20](https://doi.org/10.4230/LIPIcs.WABI.2026.20). URL: <https://drops.dagstuhl.de/storage/00lipics/lipics-vol390-wabi2026/html/LIPIcs.WABI.2026.20/LIPIcs.WABI.2026.20.html>.

*Commentary.*

Realizes(y,mu,x) is the existing predicate: x is strictly increasing; every interval difference equals some label y(q); and the cardinality of each entire interval fiber equals mu(q). The theorem assumes only this predicate, StrictAnti(y), and the displayed used-label equality. It quantifies over all natural n and d, all real y and x and all natural mu. There is no Admissible premise, n>=3 premise, positivity premise on every label, or positivity premise on every multiplicity. Unused bins may have zero multiplicity and negative values compatible with strict decrease. A used bin has positive multiplicity because its fiber is inhabited.

The original RankAllowed(mu,e,q) is the intersection condition L(n,e)<=B(mu,q) and A(mu,q)<=U(n,e). The theorem proves the stronger whole-block inequalities L(n,e)<=A(mu,q) and B(mu,q)<=U(n,e), then derives the unchanged intersection predicate from positivity of the used multiplicity.

For each interval the proof chooses its unique label using Realizes and injectivity of strictly decreasing y. The existing Finset.sum_card_fiberwise_eq_card_filter identifies cumulative multiplicities with counts of intervals whose labels lie in the corresponding index range, including empty fibers. A proper superinterval has strictly larger real difference; a proper subinterval has strictly smaller real difference, by strict increase of x. The target interval itself supplies the one exceptional occurrence in each direction.

The superinterval family is put in bijection with Iic(i) times Ici(j). The subinterval family is put in bijection with ordered pairs from Icc(i,j). Fin.card_Iic, Fin.card_Ici, Fin.card_Icc, Finset.card_product and Finset.card_product_filter_lt supply their generic cardinalities. The partition of all intervals into labels <=q and >q and the existing Fintype.card_product_filter_lt give the upper endpoint after natural arithmetic. These cardinality identities connect geometric interval containment through real differences and unique labels to the multiplicity histogram.

The generality includes two-point rulers and arbitrary translations and positive scalings of a realization. Labels with zero multiplicity do not affect the cumulative counts. For a two-point ruler with one used label and an unused negative label, both containment endpoints equal one. No LP integrality, completeness of pruning, or sufficiency of local marginals follows from this result.

## References

- Truth anchor: `D5/S3/Combinatorics/Turnpike/ContainmentRankBounds.containment_rank_bounds`
