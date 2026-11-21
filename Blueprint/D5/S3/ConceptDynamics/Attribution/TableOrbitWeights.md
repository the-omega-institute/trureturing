# The orbit program for finite equivariant probability kernels

## Abstract

Orbit mass variables for invariant probability tables and their event constraints.

**Theorem 1.1 (Invariant event masses are exactly the linear combinations of orbit frequencies).**

$$\forall G, T, I, A:I \to \operatorname{Finset}\left(T\right), m:I \to \mathbb{R}, (\exists p:T \to \mathbb{R}, \operatorname{Law}\left(p\right)) \iff (\exists z:Q \to \mathbb{R}, \operatorname{Feasible}\left(z\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.invariant_event_masses_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a group acting on a finite type T, and let I be any index type. The three types may belong to independent universes. For each i in I take a finite subset A(i) of T and a real prescribed mass m(i). Write Q for the type of G-orbits in T. The frequency of an event C in an orbit o is the cardinality of their intersection divided by the cardinality of o.

$\operatorname{Law}\left(p\right)$ means that p is nonnegative on T, sums to one on T, satisfies p(g acting on t) = p(t) for every g and t, and sums to m(i) over A(i) for every i in I. $\operatorname{Feasible}\left(z\right)$ means that z is nonnegative on Q, sums to one on Q, and for every i in I the sum over all orbits o of z(o) times the frequency of A(i) in o equals m(i).

To obtain z from p, sum p over each orbit. To obtain p from z, divide each orbit total by the orbit cardinality and assign the result to every point in that orbit.

**Theorem 1.2 (The orbit program attains the maximum invariant mass of the target event).**

$$\forall G, T, I, A:I \to \operatorname{Finset}\left(T\right), m:I \to \mathbb{R}, B:\operatorname{Finset}\left(T\right), (\exists p:T \to \mathbb{R}, \operatorname{Law}\left(p\right)) \Rightarrow \exists z:Q \to \mathbb{R}, \operatorname{Feasible}\left(z\right) \land (\forall w:Q \to \mathbb{R}, \operatorname{Feasible}\left(w\right) \Rightarrow \operatorname{Score}\left(w\right) \le \operatorname{Score}\left(z\right)) \land (\forall a:\mathbb{R}, (\exists p:T \to \mathbb{R}, \operatorname{Law}\left(p\right) \land \operatorname{TargetMass}\left(p\right)=a) \iff (\exists w:Q \to \mathbb{R}, \operatorname{Feasible}\left(w\right) \land \operatorname{Score}\left(w\right)=a))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.maximal_invariant_event_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G act on a finite type T and let I be arbitrary, with independent universes as in the event equivalence. Fix finite subsets A(i) of T and real masses m(i) for every i in I. Fix a finite target subset B of T. Assume there is a single real function p on T satisfying Law(p) for all the events A(i).

For any real function w on Q, Score(w) is the sum over orbits o of w(o) times the frequency of B in o. TargetMass(p) is the sum of p over B. Law and Feasible have the same meaning as in the event equivalence. The maximizing z is feasible, and each real a is realized as TargetMass by some law if and only if it is realized as Score by some feasible vector.

The feasible orbit vectors form a nonempty closed subset of the compact box with coordinates in the unit interval. Continuity gives attainment. Adjoining the target event to the indexed family gives the equality of attainable values while keeping all the original event constraints on the same law.

**Theorem 1.3 (An arbitrary subgroup's fixed seed mass is the attained orbit program optimum).**

$$\forall G, X, Y, H:\operatorname{Subgroup}\left(G\right), P:X \times Y \to \mathbb{R}, \operatorname{CovariantProbabilityKernel}\left(P\right) \Rightarrow \exists z:Q \to \mathbb{R}, \operatorname{Feasible}\left(z\right) \land (\forall w:Q \to \mathbb{R}, \operatorname{Feasible}\left(w\right) \Rightarrow \operatorname{Score}\left(w\right) \le \operatorname{Score}\left(z\right)) \land \operatorname{UniversalBound}\left(z\right) \land \operatorname{PositiveAttainment}\left(z\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.maximal_table_fixed_mass` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let G be a group acting on a nonempty finite input type X in universe v and a finite output type Y in universe w. Assume decidable equality on Y and a finite enumeration of the function type from X to Y. Fix any subgroup H of G and a real function P on X times Y. Its entries are nonnegative, its rows sum to one, and P(g acting on x, g acting on y) = P(x,y) for every g, x and y.

The G-action on a table t sends it under g to the table that takes x to g acting on t evaluated at the inverse translate of x. Let Q be its orbit type. For each cell (x,y), take the event of tables with t(x) = y. Feasible(z) means that z is nonnegative on Q, sums to one there, and for every x and y the sum of z(o) times the cell frequency in o over all o equals P(x,y). Score(z) sums z(o) times the H-fixed-table frequency in o over all o.

UniversalBound(z) means that for every finite seed type U in any universe s with a G-action, every real weight function a on U, and every readout f from X times U to Y, the following implication holds. If a is nonnegative and G-invariant, f is pointwise G-equivariant, and for every x and y the sum of a over seeds with f(x,u) = y equals P(x,y), then the sum of a over seeds fixed by all of H is at most Score(z).

PositiveAttainment(z) means that there exists a finite seed type U in the maximum of v and w, a G-action on U, a real weight function a on U, and a readout f from X times U to Y. The weights are strictly positive, sum to one and are G-invariant. The readout is pointwise G-equivariant, its weighted marginals equal P at every cell, and the total weight of H-fixed seeds equals Score(z).

Pushing seeds to their tables preserves the row marginals and can increase the fixed mass. Each positive-weight table can also serve as a seed with evaluation as the readout. For the universal bound, summing the marginal equations at any one input already shows that the weights sum to one. Weight invariance makes the table law constant on orbits and readout equivariance transports fixed seeds into fixed tables.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.invariant_event_masses_iff`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.maximal_invariant_event_mass`
- Truth anchor: `D5/S3/ConceptDynamics/Attribution/TableOrbitWeights.maximal_table_fixed_mass`
- Dependency: [D5/S3/ConceptDynamics/Attribution/NormalSubgroupFixedMass](NormalSubgroupFixedMass.md)
