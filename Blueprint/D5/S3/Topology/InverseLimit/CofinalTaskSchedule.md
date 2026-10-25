# Cofinal syntactic task schedule

## Abstract

Fixed cofinal ordinal reservations with domain checks and a legal fallback.

Label is the literal set of ordinals below omegaOne from SignedProperLimit. Task is the disjoint sum (Label times Label) plus (Label times Label times Label times Nat). The first summand reserves ordinary pairs, and the second reserves delayed tuples. Labels below omega are allowed in the syntax and rejected when their execution domains fail. reservation is a single fixed equivalence Label to Task times Label. Its definition contains no born spaces, clopens, points or measures, and requires no continuum hypothesis.

**Theorem 1.1 (Unbounded reservation fibers).**

$$\forall task \in Task,\; \forall base \in Label,\; \exists a \in Label,\; \operatorname{Lt}\left(base, a\right) \land \operatorname{fst}\left(\operatorname{reservation}\left(a\right)\right) = task$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/CofinalTaskSchedule.exists_reservation_above` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every task and every proper ordinal base, some later stage decodes to that task. Finite cardinal products and sums give the equivalence. A bounded inverse fiber would inject uncountable Label into the countable segment below the successor of its bound, a contradiction.

**Theorem 1.2 (Every executed target is legal).**

$$\forall a \in Label,\; \operatorname{Le}\left(omega, \operatorname{val}\left(a\right)\right) \Rightarrow \left(\forall delayed \in Label \to \left(Label \to \left(Label \to \left(Nat \to Prop\right)\right)\right),\; \operatorname{OrdinaryValid}\left(a, \operatorname{fst}\left(\operatorname{execute}\left(a, delayed\right)\right), \operatorname{snd}\left(\operatorname{execute}\left(a, delayed\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/CofinalTaskSchedule.execute_valid` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

OrdinaryValid(a,r,d) means omega<=r, r<=a and d<=a. DelayedValid(a,theta,s,t) means omega<=theta and theta,s,t<a. execute inspects the first component of reservation(a). A valid ordinary pair is returned literally. A delayed tuple returns (theta,t) only when DelayedValid and the supplied semantic predicate both hold. Every rejected case returns the literal pair (omega,0). For a>=omega this pair is legal. The semantic predicate can refer to already born data; classical branching makes no recognition-algorithm claim.

**Theorem 1.3 (Cofinal ordinary execution).**

$$\forall r \in Label,\; \forall d \in Label,\; \forall base \in Label,\; \operatorname{Le}\left(omega, \operatorname{val}\left(r\right)\right) \Rightarrow \left(\forall delayed \in Label \to \left(Label \to \left(Label \to \left(Nat \to Prop\right)\right)\right),\; \exists a \in Label,\; \operatorname{Lt}\left(base, a\right) \land \left(\operatorname{OrdinaryValid}\left(a, r, d\right) \land \left(\operatorname{fst}\left(\operatorname{reservation}\left(a\right)\right) = \operatorname{inl}\left(\operatorname{pair}\left(r, d\right)\right) \land \operatorname{execute}\left(a, delayed\right) = \operatorname{pair}\left(r, d\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/CofinalTaskSchedule.ordinary_cofinal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every r>=omega, d and base, and every delayed predicate, a later stage reserves the ordinary pair and executes exactly (r,d). Choose its reservation beyond the maximum of base,r,d. Equality r=a or d=a is accepted by the execution rule, without asserting any old convergence law there.

**Theorem 1.4 (Cofinal valid delayed execution).**

$$\forall theta \in Label,\; \forall s \in Label,\; \forall t \in Label,\; \forall base \in Label,\; \forall k \in Nat,\; \operatorname{Le}\left(omega, \operatorname{val}\left(theta\right)\right) \Rightarrow \left(\forall delayed \in Label \to \left(Label \to \left(Label \to \left(Nat \to Prop\right)\right)\right),\; \operatorname{delayed}\left(theta, s, t, k\right) \Rightarrow \left(\exists a \in Label,\; \operatorname{Lt}\left(base, a\right) \land \left(\operatorname{DelayedValid}\left(a, theta, s, t\right) \land \left(\operatorname{fst}\left(\operatorname{reservation}\left(a\right)\right) = \operatorname{inr}\left(\operatorname{tuple}\left(theta, s, t, k\right)\right) \land \operatorname{execute}\left(a, delayed\right) = \operatorname{pair}\left(theta, t\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Topology/InverseLimit/CofinalTaskSchedule.delayed_cofinal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If theta>=omega and the semantic predicate holds for a tuple, every base has a later reservation strictly beyond theta,s,t, executing exactly (theta,t). The semantic predicate in this statement is fixed; applying it to a history requires proving that its already born data persist. This schedule constructs no successor carrier, signed enumeration, coherent history or signed A-G law.

## References

- Truth anchor: `D5/S3/Topology/InverseLimit/CofinalTaskSchedule.delayed_cofinal`
- Truth anchor: `D5/S3/Topology/InverseLimit/CofinalTaskSchedule.execute_valid`
- Truth anchor: `D5/S3/Topology/InverseLimit/CofinalTaskSchedule.exists_reservation_above`
- Truth anchor: `D5/S3/Topology/InverseLimit/CofinalTaskSchedule.ordinary_cofinal`
- Dependency: [D5/S3/Topology/InverseLimit/SignedProperLimit](SignedProperLimit.md)
