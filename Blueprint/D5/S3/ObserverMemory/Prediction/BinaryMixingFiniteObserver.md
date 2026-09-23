# Finite observers for positive binary mixing

## Abstract

Every positive binary mixing rate admits a finite deterministic observer with arbitrarily small uniform next-report prediction error.

Fix emission and mixing parameters p and r strictly between zero and one half. The hidden prior is (1/2,1/2). The old hidden bit emits before it flips: report zero has emission weights p and 1-p on hidden zero and hidden one, and report one exchanges these weights. The flip probability is r. Chronological words include the empty word.

Write v(w) for the resulting unnormalized hidden column, Z(w) for the sum of its two coordinates, and f(w)=Z(w0)/Z(w) for the next-zero prediction. These are the transfer, wordVector, wordMass and prediction of the binary mixing process. Both coordinates stay positive. The mass of the empty word is one, and Z(w0)+Z(w1)=Z(w), so the ratios are actual normalized conditional probabilities for every finite history.

An observer consists of a finite set S, an initial state s0, fixed updates T0 and T1, and a fixed real readout t. Write s(w) for its chronological run, starting at s(empty)=s0 and satisfying s(wb)=Tb(s(w)). The initial state makes S nonempty, and all evolving memory resides in S.

**Theorem 1.1 (Uniform finite-state approximation).**

$$\forall p,r,\varepsilon\in \mathbb{R},\ (0 < p < \frac{1}{2} \land 0 < r < \frac{1}{2} \land 0 < \varepsilon) \Rightarrow \ (\forall w\in \{0,1\}^{*}, 0 < Z(w)) \land \ \exists S, [\operatorname{Fintype} S], \exists s_{0}\in S,\ \exists T_{0},T_{1}: S \to S, \exists t: S \to \mathbb{R},\ (\forall z\in S, 0 \leq t(z) \leq 1) \land \ \forall w\in \{0,1\}^{*}, \lvert t(s(w))-f(w)\rvert \leq \varepsilon$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/Prediction/BinaryMixingFiniteObserver.finite_suffix_observer_exists` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The state set, updates and readout may depend on p, r and the positive error allowance, but the same tables serve every finite history. No lower bound on history probability is imposed. This is mathematical existence with exact real tables.

Use the log odds of the two positive hidden masses. Emission adds the logarithm of the ratio of its weights; mixing then applies G(x)=log(r+(1-r)exp(x))-log(1-r+r exp(x)). Its derivative is positive and at most eta=1-2r. Indeed, the derivative denominator minus exp(x) is r(1-r)(exp(x)-1)^2. Also, the absolute value of G is bounded by B=log((1-r)/r). A common word of length k therefore contracts differences of log odds by eta^k.

The normalized hidden-one mass is the sigmoid of its log odds. The sigmoid derivative is at most one quarter, and the next-zero prediction is p plus (1-2p) times this hidden-one mass. Consequently, discarding a prefix before a shared suffix of length k changes the prediction by at most C eta^k, where C=(1-2p)B/4.

Choose k so that this geometric bound is within the error allowance. Take S to be all Boolean lists of length at most k, start at the empty list, and update by appending the report and retaining the last k symbols. The readout at a stored list is its exact prediction from the fixed prior. Induction identifies the run state with the last k reports, or with the whole history during startup. Empty and short histories are predicted exactly; longer histories satisfy the geometric bound. Startup length is part of the finite state, including the one-state case k=0.

## References

- Truth anchor: `D5/S3/ObserverMemory/Prediction/BinaryMixingFiniteObserver.finite_suffix_observer_exists`
- Dependency: [D5/S3/ObserverMemory/Prediction/BinaryMixingMemoryDivergence](BinaryMixingMemoryDivergence.md)
