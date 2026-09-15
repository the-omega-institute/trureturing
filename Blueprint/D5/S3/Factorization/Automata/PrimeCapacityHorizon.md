# Prime Capacity and Observation Horizon

## Abstract

The entire finite-continuation profile is exactly the clipped remaining-capacity vector.

Fix a finite register-index type I and capacities a(i). A live state r gives the remaining amount 0<=r(i)<=a(i). An actual continuation word is a List(I); it fits precisely when count_i(word)<=r(i) for every register. With distinct prime labels p_i and current product d=product(p_i^(a_i-r_i)), unique factorization identifies this condition with d*value(word) dividing N=product(p_i^a_i). The Lean theorem below is over the exact word-count capacity semantics; the integer divisor DFAO is owned by GuardedPrimeProduct.

Capacity(a) is the finite product of Fin(a_i+1), Profile(a,H) is the product of Fin(min(a_i,H)+1), and clipState maps remaining capacities coordinatewise to their minima with H. Both carriers explicitly include an Option none reject state. allowed(none,w) is false; allowed(some r,w) is the count guard. The empty continuation is included.

**Theorem 1.1 (Exact kernel, attainable profiles and cardinality for every horizon).**

$$\forall I: Type, (\operatorname{DecidableEq}(I) \land \operatorname{Fintype}(I)) \Rightarrow \forall a: I \to \mathbb{N}, \forall H \in \mathbb{N}, \operatorname{Surjective}(\operatorname{clipState}(a, H)) \land (\forall s, t: \operatorname{Option}(\operatorname{Capacity}(a)), (\forall w: \operatorname{List}(I), \operatorname{length}(w) \leq H \Rightarrow (\operatorname{allowed}(a, s, w) \iff \operatorname{allowed}(a, t, w))) \iff \operatorname{clipState}(a, H, s) = \operatorname{clipState}(a, H, t)) \land \operatorname{card}(\operatorname{Option}(\operatorname{Profile}(a, H))) = 1 + \prod_{i \in I} (\operatorname{min}(\operatorname{a}(i), H) + 1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Automata/PrimeCapacityHorizon.finite_horizon_state_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The theorem proves that clipState is onto the stated finite carrier and that two states have the same signature if and only if every actual word of total length at most H has the same admissibility from both. Thus the displayed cardinality is the number of complete observation profiles, not an assumed encoding size or a sample count.

For sufficiency, each letter count is at most the whole word length, so clipping a remaining amount at H cannot alter admissibility. For necessity, repeat one letter min(r_i,H) times; transferring admissibility to the other state bounds its remaining amount. Doing this in both directions gives equality of clipped coordinates. Every profile is attained by choosing those same finite coordinates as the original remaining amounts. Rejection is separated from each live state by the empty word.

For capacities (4,2,1,1), the complete profile counts at horizons 0,1,2,3,4 are 2,17,37,49,61. At horizon four all states are separated. This does not claim that a fixed-H summary remains closed under a new input. Remaining amounts H and H+1 can agree now and differ after one consumption. It is a bounded-horizon observer quotient, not silently an exact autonomous state model.

## References

- Truth anchor: `D5/S3/Factorization/Automata/PrimeCapacityHorizon.finite_horizon_state_classification`
