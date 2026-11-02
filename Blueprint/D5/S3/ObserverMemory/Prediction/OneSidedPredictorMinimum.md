# Sharp one-sided predictive memory

## Abstract

Sharp one-sided predictive memory.

**Theorem 1.1 (Sharp one-sided predictive memory).**

$$\forall x \in \mathbb{R},\; \forall e \in \mathbb{R},\; \forall p \in \mathbb{N} \to \mathbb{R},\; \forall N \in \mathbb{N},\; \left(0 < x \land \left(x \le 1 \land \left(0 \le e \land \left(2 \cdot e < x \land \left(\left(\forall n \in \mathbb{N},\; 0 \le p\left(n\right)\right) \land \left(\left(\forall n \in \mathbb{N},\; p\left(n\right) \le x\right) \land \left(\mathrm{Antitone}\left(p\right) \land \left(\mathrm{Tendsto}\left(p, \mathrm{atTop}, \mathrm{nhds}\left(0\right)\right) \land \left(\forall n \in \mathbb{N},\; p\left(n\right) \le 2 \cdot e \Leftrightarrow N \le n\right)\right)\right)\right)\right)\right)\right)\right)\right) \Rightarrow \left(\left(\exists M \in \mathrm{Predictor}\left(\mathrm{Sum}\left(\mathrm{Fin}\left(N + 1\right), \mathrm{Unit}\right)\right),\; \mathrm{Correct}\left(M, x, p, e\right)\right) \land \left(\mathrm{card}\left(\mathrm{Sum}\left(\mathrm{Fin}\left(N + 1\right), \mathrm{Unit}\right)\right) = N + 2 \land \left(\forall S \in \mathrm{Type},\; \forall inst \in \mathrm{Fintype}\left(S\right),\; \forall M \in \mathrm{Predictor}\left(S\right),\; \mathrm{Correct}\left(M, x, p, e\right) \Rightarrow N + 2 \le \mathrm{card}\left(S\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/OneSidedPredictorMinimum.sharp_predictor_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A predictor has one fixed initial state, a total update receiving one Boolean outcome, and an output in the closed interval from zero to one. Its reached state is the left-to-right runWord fold. Every persistent counter, program phase and parse state belongs to this carrier; no time or source-state argument is supplied.

Let x lie in (0,1], let epsilon be nonnegative with 2 epsilon < x, and let p be a nonnegative decreasing sequence bounded above by x and tending to zero. The history law is x once a false outcome has occurred, and otherwise p evaluated at the history length. Correctness requires absolute next-outcome error at most epsilon for every finite Boolean history, including the empty history.

Suppose N is the first nonstrict threshold: p(n) <= 2 epsilon if and only if N <= n. There is a correct predictor on Fin(N+1) + Unit, whose cardinality is N+2, and every correct predictor on any finite carrier has at least N+2 states.

The Fin states store the all-one depth up to N. The last one saturates and outputs p(N)/2; the Unit state records that a zero has occurred and outputs x. The saturation error is at most p(N)/2. This includes N=0 and exact threshold equality.

If two distinct all-one depths reach the same state, deterministic continuation repeats the earlier state along an unbounded arithmetic progression. Taking the limit of its error inequality forces the earlier p value to be at most 2 epsilon. Thus the first N+1 all-one states are distinct. A zero-history state cannot equal any of them: a common all-one suffix would require one output to approximate both x and a sequence tending to zero.

This theorem concerns a specified history law. Applying it to a retained quantum instrument requires deriving that law from the actual branches. It counts persistent states; output installation precision and computation time are separate resources.

**Theorem 1.2 (Exact prediction needs infinitely many states).**

$$\forall x \in \mathbb{R},\; \forall p \in \mathbb{N} \to \mathbb{R},\; \left(\left(\forall n \in \mathbb{N},\; 0 < p\left(n\right)\right) \land \mathrm{Tendsto}\left(p, \mathrm{atTop}, \mathrm{nhds}\left(0\right)\right)\right) \Rightarrow \left(\forall S \in \mathrm{Type},\; \forall inst \in \mathrm{Fintype}\left(S\right),\; \forall M \in \mathrm{Predictor}\left(S\right),\; \neg \mathrm{Correct}\left(M, x, p, 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/OneSidedPredictorMinimum.exact_prediction_impossible` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If every p(n) is strictly positive and p tends to zero, every finite carrier fails exact all-history prediction, for any reset output x. Pigeonhole gives a repeated all-one state; its deterministic recurrence and the limit force the earlier strictly positive p value to be zero.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/OneSidedPredictorMinimum.exact_prediction_impossible`
- Truth anchor: `D5/S3/ObserverMemory/Prediction/OneSidedPredictorMinimum.sharp_predictor_minimum`
- Dependency: [D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality](ControlledBehaviorUniversality.md)
