# A shared threshold for real occupancy means

## Abstract

A single threshold realizes all parity-dependent pair extremes of a legal path.

**Theorem 1.1 (Simultaneous pair extremes on a finite path).**

Lean statement: `D5/S1/Words/AdmissibleWords/FIBThresholdPairExtrema.threshold_pair_extrema`

*Proof.* Machine-checked in Lean as `D5/S1/Words/AdmissibleWords/FIBThresholdPairExtrema.threshold_pair_extrema` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Richard P. Stanley (1986). *Two Poset Polytopes*. DOI: [10.1007/BF02187680](https://doi.org/10.1007/BF02187680). URL: <https://math.mit.edu/~rstan/pubs/pubfiles/66.pdf>.

*Acknowledgement.* Giovanni Puccetti and Ruodu Wang (2015). *Extremal Dependence Concepts*. DOI: [10.1214/15-STS525](https://doi.org/10.1214/15-STS525). URL: <https://arxiv.org/abs/1512.03232v3>.

*Commentary.*

For any finite path and any real occupancy profile p in the path stable-set polytope, there is a binary word for each real threshold u. Every word is legal, and the word is empty outside the open unit interval. Each occupied-site event is measurable and has Lebesgue mass p_i. For every pair i,j, the joint occupied mass is min(p_i,p_j) if the two positions have the same parity, and max(0,p_i+p_j-1) otherwise.

Use the interval (0,p_i) at even zero-based positions and (1-p_i,1) at odd positions. Adjacent positions have opposite parity and their two intervals are disjoint because the adjacent occupancies sum to at most one. Same-parity intervals are nested. An opposite-parity pair intersects in an interval of length given by the positive part of its occupancy sum minus one. The event formulas hold for one and the same word map, including zero and unit occupancies.

The order-polytope construction supplies the threshold geometry, and the classical Frechet bounds identify the two extremal pair values. Alternating the interval endpoints enforces the path constraint.

## References

- Truth anchor: `D5/S1/Words/AdmissibleWords/FIBThresholdPairExtrema.threshold_pair_extrema`
- Dependency: [D5/S1/Words/AdmissibleWords/AdmissibleCount](AdmissibleCount.md)
