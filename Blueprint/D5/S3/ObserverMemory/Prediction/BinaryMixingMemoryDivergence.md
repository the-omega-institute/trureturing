# Binary mixing and necessary observer memory

## Abstract

A fixed bound on deterministic observer states fails below the static error floor throughout a sufficiently small positive mixing interval.

The hidden state and report alphabets are binary. A chronological word starts from the uniform hidden prior. The old hidden bit emits its report before the bit flips. For report zero, set a=p and c=1-p; for report one, set a=1-p and c=p. The transfer of an unnormalized column is

$(x,y) \mapsto ((1-r)ax+rcy,rax+(1-r)cy)$

Let v(p,r,w) be the successive transfer of the initial column (1/2,1/2) along w, with the first coordinate corresponding to hidden zero. Let Z(p,r,w) be the sum of its coordinates. The next-zero prediction is the ratio of the mass of w followed by zero to the mass of w:

$f(p,r,w) = \frac{Z(p,r,w0)}{Z(p,r,w)}$

An observer has a finite state set S, an initial state s0, two fixed updates T0 and T1, and an arbitrary real readout t. Its state s(w) is obtained by applying the report-labelled updates chronologically; s(empty)=s0 and s(wb)=Tb(s(w)). All evolving memory is in S. In particular, readouts in the probability interval are included.

**Theorem 1.1 (A uniform obstruction to bounded observer memory).**

$$\forall p,\varepsilon\in \mathbb{R}, \forall N\in \mathbb{N},\ (0 < p < \frac{1}{2} \land 0 < \varepsilon < \frac{1}{2}-p) \Rightarrow \exists \delta\in \mathbb{R},\ 0 < \delta \land \forall r\in \mathbb{R},\ (0 < r \land r < \min(\delta,\frac{1}{2})) \Rightarrow \forall S, [\operatorname{Fintype} S],\ \forall s_{0}\in S, \forall T_{0},T_{1}: S \to S,\ \forall t: S \to \mathbb{R},\ \operatorname{card}(S) \leq N \Rightarrow \exists w\in \{0,1\}^{*},\ 0 < Z(p,r,w) \land \varepsilon < \lvert t(s(w))-f(p,r,w)\rvert$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/BinaryMixingMemoryDivergence.small_mixing_observer_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The interval depends only on p, the error tolerance and N. The observer may be chosen anew at every mixing rate, and its readout may contain arbitrary exact real constants. Nevertheless, some positive-probability finite history has error strictly above the tolerance. The assertion includes all finite history lengths.

At zero mixing, the hidden likelihoods along a block of n zeros and k ones are p^n(1-p)^k/2 and (1-p)^n p^k/2. Choose an integer m so that the two histories with net evidence of opposite signs have a prediction gap greater than twice the tolerance. For every positive period l, the histories are n zeros followed by n+ml ones, and n+2ml zeros followed by n+ml ones.

Every fixed-word mass is polynomial in the mixing rate, and the denominator is positive at zero. Prediction gaps are therefore continuous there. There are finitely many possible n and l below the state bound, so one positive interval preserves all their strict gaps. The finite-orbit period bound makes the two zero prefixes reach the same state for one such pair. Appending their common one suffix preserves this equality. A single real readout cannot approximate both predictions within the stated tolerance.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/BinaryMixingMemoryDivergence.small_mixing_observer_obstruction`
- Dependency: [D5/S3/ObserverMemory/Prediction/FiniteOrbitPeriodBound](FiniteOrbitPeriodBound.md)
