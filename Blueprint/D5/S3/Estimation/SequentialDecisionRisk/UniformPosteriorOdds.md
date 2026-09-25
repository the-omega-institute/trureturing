# Uniform Posterior Log Odds

## Abstract

A balanced auxiliary Bernoulli array gives a uniform finite approximation to actual posterior log odds.

**Theorem 1.1 (Universal finite posterior log-odds bound).**

$$\begin{gathered}\exists C>0, \exists V0>0,\\{}\forall M,q,s:Nat, r:Real, e:Experiment, o:\operatorname{Obs}(M, s, e), t:Real,\\{}1\leq q<M \land 0<r<1 \land \operatorname{compensation}(M, q, r)<1 \land 0<t \land U=q \land V0\leq V \Rightarrow\\{}\forall i:\operatorname{Fin}(M), 0<\operatorname{inclusion}(q, r, e, o, i)<1 \land \operatorname{abs}(\operatorname{log}(\frac{\operatorname{inclusion}(q, r, e, o, i)}{1-\operatorname{inclusion}(q, r, e, o, i)})-(\operatorname{score}(q, r, e, o, i)-\operatorname{log}(B0)+\operatorname{log}(t)))\leq\frac{C}{V}\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/UniformPosteriorOdds.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

There are universal positive real constants C and V0, chosen before every model parameter, observation, tilt and coordinate. Both constants may be taken to be four. Let M, q and s be natural numbers with 1<=q<M, let 0<r<1, and assume the compensation a=rq/(M-q) is less than one. The experiment e is either the compensated independent-pair experiment or the compensated consecutive-path experiment, and o is any complete observation of that experiment.

For any positive real t, put B0=(M-q)/q and p(i)=t w(i)/(B0+t w(i)), where w(i) is the actual positive likelihood weight. Write U for the sum of p(i) and V for the sum of p(i)(1-p(i)). If U=q and V>=V0, every actual posterior inclusion probability pi(i) is strictly between zero and one. Its log odds differ from score(i)-log(B0)+log(t) in absolute value by at most C/V, simultaneously for all coordinates.

The coefficient estimate uses arbitrary positive Bernoulli odds. If their sum mean lies between consecutive integers k and k+1 and their sum variance is W>=2, the logarithm of the ratio of the corresponding adjacent elementary symmetric coefficients has absolute value at most 2/W. Multiply every odds by the ratio of those coefficients. The new coefficients are equal. Coefficient deletion, the first-moment identity and Newton's inequality place the new mean between k and k+1. The rational change in the mean bounds the odds multiplier and its logarithm in terms of W.

For a deleted coordinate, the mean is q-p(i) and the variance is V-p(i)(1-p(i)), at least V-1/4. The auxiliary coefficient estimate therefore applies. The common tilt cancels in every fixed-cardinality support probability; the actual Bayes formula identifies the posterior odds with the tilted single-coordinate odds times the deleted coefficient ratio. Taking logarithms gives the stated bound without a union bound over coordinates.

This is a deterministic finite statement conditional on the realized observation and the displayed mean and variance conditions. It does not assert their probability under the actual data law, a sparse-cardinality asymptotic, or a risk expansion.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/UniformPosteriorOdds.result`
- Dependency: [D5/S3/Analytic/RealRootedCoefficientNewton](../../Analytic/RealRootedCoefficientNewton.md)
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionBayes](FiniteSupportSelectionBayes.md)
