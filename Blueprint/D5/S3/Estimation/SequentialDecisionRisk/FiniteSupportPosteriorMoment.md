# Finite posterior exponential moments

## Abstract

Exponential moments of the actual finite fixed-support posterior.

**Theorem 1.1 (The two finite moment bounds).**

$$\begin{gathered}\forall M,q,s:Nat, r:Real, e:Experiment, o:\operatorname{Obs}(M, s, e), I:\operatorname{Finset}(\operatorname{Fin}(M)), t:Real,\\{}1\leq q<M \land 0<r<1 \land \operatorname{compensation}(M, q, r)<1 \land 0\leq t \Rightarrow\\{}\sum_{{S:\operatorname{Support}(M, q)}}{\operatorname{posterior}(r, e, o, S) \operatorname{exp}(t \operatorname{card}(\operatorname{inter}(I, S)))}\leq\prod_{{i\in I}}{1+(\operatorname{exp}(t)-1) \operatorname{inclusion}(q, r, e, o, i)}\leq\operatorname{exp}((\operatorname{exp}(t)-1) \sum_{{i\in I}}{\operatorname{inclusion}(q, r, e, o, i)})\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportPosteriorMoment.finite_support_posterior_moment` (`✓ std3`). ∎

*Citation.* Julius Borcea; Petter Brändén; Thomas M. Liggett (2009). *Negative dependence and the geometry of polynomials*. DOI: [10.1090/S0894-0347-08-00618-8](https://doi.org/10.1090/S0894-0347-08-00618-8). URL: <https://arxiv.org/abs/0707.2340v2>.

*Commentary.*

Let M, q and s be natural numbers with 1<=q<M, let 0<r<1, and suppose the compensation rq/(M-q) is less than one. Its nonnegativity follows from these conditions. The experiment e is either the compensated independent-pair experiment or the consecutive-path experiment. Fix any complete observation o, any subset I of Fin M, and any real t>=0.

The support S has exactly q elements. The functions posterior and inclusion are those of FiniteSupportSelectionBayes, with the same r, experiment and complete observation throughout. The expectation here is the finite sum against that actual posterior. Its positive likelihood weights identify it with the normalized product-weight q-slice. An independent tie priority may choose I after conditioning; the bound applies to every resulting fixed I and does not allow selection using the hidden support.

Write e_k(U) for the sum of weight products over k-element subsets of U, including e_0(U)=1 and e_k(U)=0 when k exceeds the size of U. For distinct coordinates i and j, expansion over their membership and Newton's coefficient inequality give e_n(U)e_(n-2)(U without i,j)<=e_(n-1)(U without i)e_(n-1)(U without j). Every feasible forced-success condition leaves a positive product-weight slice on the remaining labels. Thus adding another forced success decreases every remaining inclusion probability. Induction on the number of required labels gives a joint inclusion probability at most the product of the original marginals.

Expanding the finite product with x=exp(t)-1>=0 turns the moment into a sum of nonnegative coefficients times joint inclusion probabilities. Apply the joint bound term by term and factor the resulting sum. Applying 1+y<=exp(y) to every factor gives the second bound. Empty I and t=0 give equality. Oversized required-label sets have zero inclusion mass; no conditional law is obtained by dividing by that zero mass.

The finite product-weight moment inequality is a classical consequence of negative dependence. This formulation applies it to the existing actual posterior and does not assert an asymptotic process limit, an unknown-direction posterior, an entropy bound or originality.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportPosteriorMoment.finite_support_posterior_moment`
- Dependency: [D5/S3/Analytic/RealRootedCoefficientNewton](../../Analytic/RealRootedCoefficientNewton.md)
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionBayes](FiniteSupportSelectionBayes.md)
