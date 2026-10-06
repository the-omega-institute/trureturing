# Integer Potentials on Nondeterministic Runs

## Abstract

Backward and forward path induction turn edge inequalities into bounds for every accepted input.

**Definition 1.1 (Integer charge of a run).**

$$\forall A \in \operatorname{Type},\; \forall S \in \operatorname{Type},\; \forall M \in \operatorname{NFA}\left(A, S\right),\; \forall charge \in S \to A \to S \to \mathbb{Z},\; \left(\forall s \in S,\; \operatorname{pathCharge}\left(charge, \operatorname{nil}\left(s\right)\right) = 0\right) \land \left(\forall q \in S,\; \forall s \in S,\; \forall t \in S,\; \forall a \in A,\; \forall xs \in \operatorname{List}\left(A\right),\; \forall h \in q \in \operatorname{step}\left(M, s, a\right),\; \forall p \in \operatorname{Path}\left(M, q, t, xs\right),\; \operatorname{pathCharge}\left(charge, \operatorname{cons}\left(q, s, t, a, xs, h, p\right)\right) = charge\left(s, a, q\right) + \operatorname{pathCharge}\left(charge, p\right)\right)$$

*Formalization.* `D5/S1/Words/Palindromes/PeriodDoubling/AutomatonPotential.pathCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Charge is defined on the existing NFA.Path proof object. The empty run has charge zero, and a cons run adds the first edge charge to the tail charge. The equations retain every carrier and all constructor arguments.

**Theorem 1.2 (Total potentials control every accepting run).**

$$\forall A \in \operatorname{Type},\; \forall S \in \operatorname{Type},\; \forall M \in \operatorname{NFA}\left(A, S\right),\; \forall charge \in S \to A \to S \to \mathbb{Z},\; \forall potential \in S \to \mathbb{Z},\; \forall offset \in S \to \mathbb{Z},\; \forall B \in \mathbb{Z},\; \left(\left(\left(\forall s \in S,\; s \in \operatorname{start}\left(M\right) \Rightarrow 0 \le potential\left(s\right)\right) \land \left(\forall s \in S,\; \forall q \in S,\; \forall a \in A,\; q \in \operatorname{step}\left(M, s, a\right) \Rightarrow potential\left(s\right) + charge\left(s, a, q\right) \le potential\left(q\right)\right)\right) \land \left(\forall t \in S,\; t \in \operatorname{accept}\left(M\right) \Rightarrow potential\left(t\right) + offset\left(t\right) \le B\right)\right) \Rightarrow \left(\forall s \in S,\; \forall t \in S,\; \forall xs \in \operatorname{List}\left(A\right),\; \left(s \in \operatorname{start}\left(M\right) \land t \in \operatorname{accept}\left(M\right)\right) \Rightarrow \left(\forall p \in \operatorname{Path}\left(M, s, t, xs\right),\; \operatorname{pathCharge}\left(charge, p\right) + offset\left(t\right) \le B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/AutomatonPotential.accepted_path_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Start potentials are nonnegative. Each transition dominates its predecessor potential plus the edge charge. Accepted states have a bounded potential plus terminal offset. Induction on the actual run proves the bound at arbitrary length.

**Theorem 1.3 (Partial potentials control every accepting run).**

$$\forall A \in \operatorname{Type},\; \forall S \in \operatorname{Type},\; \forall M \in \operatorname{NFA}\left(A, S\right),\; \forall charge \in S \to A \to S \to \mathbb{Z},\; \forall potential \in S \to \operatorname{Option}\left(\mathbb{Z}\right),\; \forall offset \in S \to \mathbb{Z},\; \forall B \in \mathbb{Z},\; \left(\left(\left(\forall s \in S,\; s \in \operatorname{start}\left(M\right) \Rightarrow \left(\forall V \in \mathbb{Z},\; potential\left(s\right) = \operatorname{some}\left(V\right) \Rightarrow 0 \le V\right)\right) \land \left(\forall s \in S,\; \forall q \in S,\; \forall a \in A,\; q \in \operatorname{step}\left(M, s, a\right) \Rightarrow \left(\forall W \in \mathbb{Z},\; potential\left(q\right) = \operatorname{some}\left(W\right) \Rightarrow \left(\exists V \in \mathbb{Z},\; potential\left(s\right) = \operatorname{some}\left(V\right) \land V + charge\left(s, a, q\right) \le W\right)\right)\right)\right) \land \left(\forall t \in S,\; t \in \operatorname{accept}\left(M\right) \Rightarrow \left(\exists W \in \mathbb{Z},\; potential\left(t\right) = \operatorname{some}\left(W\right) \land W + offset\left(t\right) \le B\right)\right)\right) \Rightarrow \left(\forall s \in S,\; \forall t \in S,\; \forall xs \in \operatorname{List}\left(A\right),\; \left(s \in \operatorname{start}\left(M\right) \land t \in \operatorname{accept}\left(M\right)\right) \Rightarrow \left(\forall p \in \operatorname{Path}\left(M, s, t, xs\right),\; \operatorname{pathCharge}\left(charge, p\right) + offset\left(t\right) \le B\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/AutomatonPotential.accepted_path_bound_partial` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A present potential at a successor propagates backwards to a present predecessor with the edge inequality. Every accepted state has a present bounded potential. Backwards path induction reaches the source and bounds the entire charge.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/AutomatonPotential.accepted_path_bound`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/AutomatonPotential.accepted_path_bound_partial`
- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/AutomatonPotential.pathCharge`
