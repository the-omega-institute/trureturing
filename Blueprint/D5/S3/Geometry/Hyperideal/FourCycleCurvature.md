# From local angle envelopes to all global curvature faces

## Abstract

The actual occurrence-counted curvature has a uniform inward margin on an explicit global four-cycle box.

T is an arbitrary finite type of tetrahedra. E is an arbitrary global-edge type with decidable equality. An incidence s has edge:T -> Fin(6) -> E and low:E -> Bool. In the local order (12,13,14,34,24,23), slots 0 and 3 are high and the other four are low. FourCycle(s) requires this equality at every local slot, degree eight for every low global label, and degree at least twelve for every high label. Degree is the actual cardinality of the fibre of edge, including repeated labels.

For each local target, frame is an explicit permutation induced by a tetrahedral vertex relabeling. Its zeroth coordinate is the target; for a low target its slots 0,1,3,4 are low. All frame coordinates read the SAME global vector x:E -> Real. C(s,x,o) is the previous exact six-variable cosine after this relabeling. The angle is arccos(C), and K(s,x,e) is 2pi minus the sum over all occurrences o with source e.

Set m=card(T x Fin(6)), t=pi/(m+2), c=cos(t), and delta(T)=min(1/8,(1-c)/(2+c)). The lower vector L(s) has value 5/4 at low labels and 1+delta at high labels. U(s) has value 2 at low labels and 8/5 at high labels. Box(s,x) means L(s)(e)<=x(e)<=U(s)(e) for all e. The size-independent eta is min(pi, min(2pi-8arccos(293/400), min(8arccos(1577/2236)-2pi,12arccos(37/43)-2pi))).

**Theorem 1.1 (An explicit nonempty box with signed margin on every face).**

$$\forall T \in Type, E \in Type, s \in Incidence\left(T, E\right),\; \left(Fintype\left(T\right) \land \left(DecidableEq\left(E\right) \land FourCycle\left(s\right)\right)\right) \Rightarrow \left(0 < delta\left(T\right) \land \left(delta\left(T\right) \le \frac{1}{8} \land \left(0 < eta \land \left(Box\left(s, L\left(s\right)\right) \land \left(\forall x \in E \to Real,\; Box\left(s, x\right) \Rightarrow \left(\left(\forall o \in Product\left(T, Fin\left(6\right)\right),\; -1 < C\left(s, x, o\right) \land C\left(s, x, o\right) < 1\right) \land \left(\forall e \in E,\; \left(x\left(e\right) = L\left(s\right)\left(e\right) \Rightarrow eta \le K\left(s, x, e\right)\right) \land \left(x\left(e\right) = U\left(s\right)\left(e\right) \Rightarrow K\left(s, x, e\right) \le -eta\right)\right)\right)\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/FourCycleCurvature.fourcycle_curvature_box` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The derivative-based local theorem is consumed directly. The proof checks the actual finite frame permutations, proves the trigonometric gaps from exact square-root comparisons, and constructs delta rather than assuming an unspecified sufficiently small number. It proves cos(t)<2(1-delta)/(2+delta), so on a high lower face each angle is below t. There are at most m occurrences at any edge; hence the angle sum is below pi and its curvature exceeds pi.

On low lower and upper faces the exact cardinality is eight. The corresponding arccos bounds are summed over the actual fibre. On a high upper face the cardinality is at least twelve and all arccos values are nonnegative. These give the three fixed gaps in eta. The same proof shows -1<C(s,x,o)<1 throughout the box, and the lower vector itself witnesses nonemptiness. No solution or face sign is assumed.

This is a real incidence-system theorem. The formal statement does not certify that the incidence system is a manifold, prove the hyperbolic realization of each angle formula, or invoke an unproved Brouwer or co-volume existence axiom. Those geometric identifications and the ordinary variational existence step remain separate.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/FourCycleCurvature.fourcycle_curvature_box`
- Dependency: [D5/S3/Geometry/Hyperideal/FourCycleEnvelopes](FourCycleEnvelopes.md)
