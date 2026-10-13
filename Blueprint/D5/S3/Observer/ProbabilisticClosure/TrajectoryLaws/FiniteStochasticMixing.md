# Finite primitive stochastic convergence

## Abstract

Finite primitive stochastic convergence

RowStochastic(P) means nonnegative real entries and every row summing to one; IsPrimitive(P) is Mathlib's actual positive-power predicate. powers(P) is n ↦ P^n, constantRows(mu) is (i,j) ↦ mu(j), sum is over the finite state type, and eval is function evaluation. The topology in Tendsto is the finite product topology. Thus the matrix limit entails convergence of every entry to the corresponding stationary coordinate.

**Theorem 1.1 (Convergence to the unique stationary probability row).**

$$\forall S:Type, ([\operatorname{Fintype}(S)][\operatorname{DecidableEq}(S)][\operatorname{Nonempty}(S)]\forall P:\operatorname{Matrix}(S, S, \mathbb{R}), (\operatorname{RowStochastic}(P)\land \operatorname{IsPrimitive}(P)\implies \exists \mu:S\to \mathbb{R}, (\forall j:S, (0\leq \operatorname{eval}(\mu, j))\land \operatorname{sum}(\mu)=1\land \operatorname{vecMul}(\mu, P)=\mu\land \forall v:S\to \mathbb{R}, ((\forall j:S, (0\leq \operatorname{eval}(v, j))\land \operatorname{sum}(v)=1\land \operatorname{vecMul}(v, P)=v)\implies v=\mu)\land \operatorname{Tendsto}(\operatorname{powers}(P), \operatorname{atTop}(), \operatorname{nhds}(\operatorname{constantRows}(\mu))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing.primitive_convergence` (`✓ std3`). ∎

*Citation.* Shangtong Zhang (2025). *Stochastic matrices and geometric mixing in rl-theory-in-lean*. URL: <https://github.com/ShangtongZhang/rl-theory-in-lean/blob/fec0b5d1a03e90479945286532f89e4f22cfcd1e/RLTheory/Data/Matrix/Stochastic.lean>.

*Commentary.*

The stationary probability row exists, is nonnegative and normalized, satisfies mu*P=mu, is unique among normalized nonnegative stationary rows, and attracts every row of P^n. Nonempty is essential only for this probability-row conclusion. On an empty state type the unique matrix is zero and the power sequence is constant; no normalized row is asserted.

The source-preserving supplier uses eventual positivity, Doeblin minorization, l1 contraction on the simplex, uniqueness of a contracting fixed point, and the original geometric estimate C*rho^n for 0<rho<1. Its stationary existence step calls the original repository cesaro_stochastic, pair_cluster, stochastic_limit and cesaro_fixed declarations in NativePaidHistoryCommonRowLimits and selects a row of the stochastic fixed cluster. The return-arithmetic step calls Nat.exists_mem_closure_of_ge and Nat.setGcd machinery. No duplicate stationary, extended-gcd or Frobenius proof is retained.

The primitive bridge proves the supplier's actual return_times predicate, {n | 1<=n and 0<(P^n)(i,i)}: a positive power k and row stochasticity give positive powers k and k+1; their gcd is one. These two real return lengths witness the retained FiniteGCDOne predicate at each state. Positivity of a matrix power is not replaced by an assumed aperiodicity premise.

For the alternating two-state chain, the positive return lengths are exactly the positive multiples of two. Restricting its actual square to the phase containing the first state gives a stochastic primitive block to which this supplier applies. General closed-class decomposition, cyclic labels, first-entry phase probabilities, reducible-chain limits and arithmetic denominator bounds require further results. Phase indexing here is mathematical analysis and establishes no runtime clock or resource waiver.

## References

- Truth anchor: `D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteStochasticMixing.primitive_convergence`
- Dependency: [D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativePaidHistoryCommonRowLimits](NativePaidHistoryCommonRowLimits.md)
