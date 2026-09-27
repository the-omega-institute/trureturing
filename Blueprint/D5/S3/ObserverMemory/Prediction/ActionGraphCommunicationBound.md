# Action Graph Communication Bound

## Abstract

Cumulative cost on a finite deterministic action graph is bounded exactly when every closed action word has zero cost.

**Definition 1.1 (Finite action words determine terminal states).**

$$\begin{gathered}\forall Q, \mathcal{F}, T: \mathcal{F} \to \left(Q \to Q\right),\\{}\forall m\in Q, \operatorname{runWord}(T, [], m) = m,\\{}\forall f\in \mathcal{F}, \forall u\in \operatorname{List}(\mathcal{F}), \operatorname{runWord}(T, \operatorname{cons}(f, u), m) = \operatorname{runWord}(T, u, \operatorname{T}(f, m)).\end{gathered}$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.runWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Starting at m, the empty word leaves the state unchanged. Executing a word whose first action is f first applies the deterministic transition T_f and then executes the remaining word.

**Definition 1.2 (Finite-word communication is the sum of step costs).**

$$\begin{gathered}\forall Q, \mathcal{F}, T: \mathcal{F} \to \left(Q \to Q\right), w: Q \to \left(\mathcal{F} \to \mathbb{N}\right),\\{}\forall m\in Q, \operatorname{Comm}(T, w, m, []) = 0,\\{}\forall f\in \mathcal{F}, \forall u\in \operatorname{List}(\mathcal{F}), \operatorname{Comm}(T, w, m, \operatorname{cons}(f, u)) = \operatorname{w}(m, f) + \operatorname{Comm}(T, w, \operatorname{T}(f, m), u).\end{gathered}$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.Comm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The empty word costs zero. A nonempty word pays the cost of its first labelled edge and then pays the cost of the remaining execution from the successor state.

**Definition 1.3 (Infinite-word communication is a prefix supremum).**

$$\forall Q, \mathcal{F}, T: \mathcal{F} \to \left(Q \to Q\right), w: Q \to \left(\mathcal{F} \to \mathbb{N}\right),\\\forall m\in Q, \forall \omega: \mathbb{N} \to \mathcal{F},\\\operatorname{InfiniteComm}(T, w, m, \omega) = \operatorname{sup}_{n\ge0} \operatorname{Comm}(T, w, m, \operatorname{prefix}(\omega, n)) \in \operatorname{ENat}.$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.InfiniteComm` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The total cost of an infinite action word is the supremum in the extended natural numbers of the costs of all its finite prefixes.

**Definition 1.4 (The finite supremum of edge costs).**

$$\forall Q, \mathcal{F}, [\operatorname{Fintype} Q], [\operatorname{Fintype} \mathcal{F}], w: Q \to \left(\mathcal{F} \to \mathbb{N}\right),\\\operatorname{maxEdgeCost}(w) = \operatorname{sup}_{m\in Q, f\in \mathcal{F}} \operatorname{w}(m, f).$$

*Formalization.* `D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.maxEdgeCost` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For finite state and action carriers, W_max is the finite supremum of all labelled-edge costs; its value is zero if either carrier is empty.

**Theorem 1.5 (Cumulative communication criterion).**

$$\begin{gathered}\forall Q, \mathcal{F}: \operatorname{Type}, [\operatorname{Fintype} Q], [\operatorname{Nonempty} Q],\\{}[\operatorname{Fintype} \mathcal{F}], [\operatorname{Nonempty} \mathcal{F}], I: \operatorname{Set}(Q),\\T: \mathcal{F} \to \left(Q \to Q\right), w: Q \to \left(\mathcal{F} \to \mathbb{N}\right),\\\forall m\in Q, \exists m_{0}\in I, \exists p\in \operatorname{List}(\mathcal{F}), \operatorname{runWord}(T, p, m_{0}) = m,\\W_{max} = \operatorname{maxEdgeCost}(w),\\a: \forall m_{0}\in I, \forall \omega: \mathbb{N} \to \mathcal{F}, \operatorname{InfiniteComm}(T, w, m_{0}, \omega) \neq \infty,\\b: \exists B\in \mathbb{N}, \forall m_{0}\in I, \forall u\in \operatorname{List}(\mathcal{F}), \operatorname{Comm}(T, w, m_{0}, u) \leq B,\\c: \forall m\in Q, \forall v\in \operatorname{List}(\mathcal{F}), v \neq [] \land \operatorname{runWord}(T, v, m) = m \Rightarrow \operatorname{Comm}(T, w, m, v) = 0,\\\operatorname{List.TFAE}([a, b, c]) \land\\(c \Rightarrow \forall m_{0}\in I, \forall u\in \operatorname{List}(\mathcal{F}), \operatorname{Comm}(T, w, m_{0}, u) \leq (\operatorname{card}(Q) - 1) W_{max}).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.cumulative_communication_criterion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let Q and the action alphabet be finite and nonempty. Let I be a set of initial states, and assume every state is reached from I by some finite action word; since the state type is nonempty, I is then nonempty. Then finite total cost for every infinite execution, one common bound for all finite executions from I, and zero cost for every nonempty closed action word are equivalent.

If the cycle condition holds, remove a closed segment whenever an execution repeats a state. The segment has zero cost and its deletion preserves the state from which the suffix runs. Iteration leaves a path with no repeated state, hence at most card(Q)-1 edges, and each edge costs at most W_max.

Conversely, a reachable positive-cost cycle can be repeated after a prefix leading to it. Determinism returns to the same state after each copy, so its prefix costs are unbounded. A common finite-word bound directly bounds every infinite-word prefix supremum.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.Comm`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.InfiniteComm`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.cumulative_communication_criterion`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/ActionGraphCommunicationBound.maxEdgeCost`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.runWord`
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](ControlledBehaviorUniversality.md)
