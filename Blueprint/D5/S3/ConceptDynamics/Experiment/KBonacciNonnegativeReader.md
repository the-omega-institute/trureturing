# Nonnegative Fixed Readers and the One-Preparation Obstruction

## Abstract

Every globally correct, pointwise terminating deterministic actual-window protocol with an unknown nonnegative nonzero fixed reader needs at least two preparations in the worst case in dimension two.

**Theorem 1.1 (Unrestricted actual-history preparation lower bound).**

$$(\forall b \in Window, \exists p,t\in Fin(2), lead(b)=p\land A(b)=E(p,t))\land (\forall p \in Fin(2), (\forall t \in Fin(2), \exists b\in Window, A(b)=E(p,t)))\land (\forall w \in C, 0< D(w))\land (\forall \pi \in Proto, (\forall w \in C, N(\pi,w)=P(\pi,w)+W(\pi,w)))\land (\forall \pi \in Proto, Correct(\pi)\implies \neg(\forall w \in C, P(\pi,w)\le 1))\land (\forall \pi \in Proto, Correct(\pi)\implies 2\le B(\pi))\land 2\le V\land V\neq 1\land \neg(\exists \pi\in Proto, Correct(\pi)\land (\forall w \in C, P(\pi,w)\le 1\land W(\pi,w)\le 2\land N(\pi,w)\le 3))$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Experiment/KBonacciNonnegativeReader.complete_source_8_2` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

C denotes all worlds consisting of a strictly positive real two-vector c and a nonnegative real two-vector ell whose coordinate sum is positive. Both vectors and the location of any zero reader coordinate are unknown. The target is the original outer product c ell-transpose. Every preparation supplies exactly the same c within that world, with ell fixed across all successive runs. D is the exact initial scalar ell dot c.

A window b is a literal Boolean word of length three accepted from state zero by the original live-tail automaton. This is internal exclusion of two consecutive ones, rather than a requirement that every current tail survive. A(b) is its actual live evaluation matrix. For p and t in Fin 2, E(p,t) has entry one at (i,s) exactly when i=t and s+p<2. The first two conjuncts give the leading-endpoint correspondence for every actual legal window and actual realization of all four endpoint pairs.

Proto contains arbitrary deterministic full-history choice, stopping and matrix-output functions. Each recorded event retains its literal action, the preceding action list and its exact real read. The redundant prefix is checked against the actual history. A window requires a previously prepared object. A preparation discards the old object; a window acts only on the current one. There is no operation for returning to an old object, copying, resetting it, observing internally or obtaining a free read.

Every preparation immediately incurs its initial read, even in an empty run. Every complete window immediately incurs one read, including a killed object, a zero state and each repeated zero response. P, W and N count preparations, windows and paid reads in the actual terminal history. The protocol supplies a finite actual terminal execution separately on every world. No common fuel, window or read bound, continuity, measurability or computability hypothesis is imposed. Correct means that every actual terminal output equals the original outer product.

B(pi) is the supremum over C of the natural preparation count, embedded in the extended nonnegative reals. V is the infimum of B over all correct protocols in Proto. These complete-order operations allow positive infinity, and the empty correct-protocol class has infimum infinity. The displayed conjunction includes the positive paid initial read, the exact accounting identity, impossibility of one preparation everywhere, both extended-order lower bounds, failure of V=1 and failure of the same-protocol simultaneous budgets P<=1, W<=2, N<=3.

For the collision, stop before preparation or immediately after an initial read equal to one cannot separate the source's unequal target pairs. Otherwise the actual first word is selected from that same history. For leading endpoint one, use initial objects (1,1) and (1,2) with reader (1,0). For leading endpoint zero, use (1/4,3/4) and (3/4,1/4) with reader (1,1). In each case the initial reads agree, the reader is identical, and the selected actual window makes the objects identical, while their original outer products differ. Both trailing endpoints are included, including a zero first-window read.

The one-preparation assumption excludes every later preparation. Induction on the actual finite remaining history shows equal objects and equal fixed-reader responses after each selected window, including every zero state. The existing conditional execution-transfer theorem then replays that same terminal history on the second world. Execution monotonicity identifies its terminal output without a uniform termination assumption. Unequal targets contradict correctness.

This is the k=2 obstruction to extending the universal sharp resource law from strictly positive readers to all nonnegative nonzero readers. It excludes the preparation equality and the simultaneous same-protocol bounds. It establishes no exact optimal preparation, window or total read count on the enlarged domain, and does not separately refute a window-count or total-read infimum equality. The strictly positive reader results retain their original assumptions. The contract uses exact noiseless real reads and granted same-source preparations; no physical construction, noise tolerance or finite-precision claim follows.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Experiment/KBonacciNonnegativeReader.complete_source_8_2`
- Dependency: [D5/S1/Words/AdmissibleWords/KBonacciActualEndpointOperators](../../../S1/Words/AdmissibleWords/KBonacciActualEndpointOperators.md)
- Dependency: [D5/S3/ConceptDynamics/Experiment/PassivePolicyNormalization](PassivePolicyNormalization.md)
