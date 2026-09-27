# Finite Support Selection Bayes Rules

## Abstract

Finite Support Selection Bayes Rules.

**Theorem 1.1 (Finite Support Selection Bayes Rules).**

$$\forall M, q, s: Nat, r: Real, e: Experiment, 1\leq q<M \land 0<r<1 \land 0\leq\operatorname{compensation}(M, q, r)<1 \Rightarrow \operatorname{BayesCertificate}(M, q, s, r, e)$$

*Proof.* Machine-checked in Lean as `D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionBayes.finite_support_bayes` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The vertices are two copies of Fin M. A support S is a subset of the first copy with cardinality q, fixed for the whole observation. Write n = 2M and a = rq/(M-q). The source-row coefficient is r on S, -a on the other first-copy vertices, and zero on the second copy. The target sign is +1 on the first copy and -1 on the second. The transition probability is (1+b(S,x) chi(y))/n.

For every natural sample count s, the pair experiment consists of s independent ordered pairs, each with its own uniform start. The path experiment has exactly one uniform start and s consecutive transitions. Their complete observation probabilities are respectively the product of P(S,x,y)/n over pairs and the product of transitions divided by n. The compensated transition has all row and column sums equal to one, and both complete observation laws are strictly positive and stochastic.

For each first-copy coordinate i, let N(i,+) and N(i,-) count departures from i whose targets have sign +1 and -1. Set w(i)=((1+r)/(1-a))^N(i,+) ((1-r)/(1+a))^N(i,-), and W(i)=N(i,+) log((1+r)/(1-a))+N(i,-) log((1-r)/(1+a)). Then w(i)>0 and w(i)=exp(W(i)). The observation probability is its uniform reference mass times C times the product of w(i) over i in S. Here C is the product of 1-a chi(y) over edges starting in the first copy and is independent of S.

The uniform fixed-cardinality prior gives posterior mass proportional to the product of the selected weights. Its normalizer Z is the sum of these products over all q-element supports and is positive. For distinct i and j, the inclusion-probability difference is (w(i)-w(j)) times the sum of products over all (q-1)-element subsets excluding i and j, divided by Z. This coefficient is strictly positive, so inclusion probabilities and weights have exactly the same weak ordering.

The decision rule is uniform over q-element subsets whose selected weights dominate every omitted weight. There is a cutoff t with H={i:t<w(i)} and E={i:w(i)=t}, satisfying |H|<q<=|H|+|E|. Its mass at T is the reciprocal of binomial(|E|,q-|H|) when H is contained in T and T is contained in H union E, and zero otherwise. This is a stochastic kernel, including at sample count zero.

The rule minimizes uniform-prior expected normalized Hamming loss |T symmetric-difference S|/(2q) among all randomized rules with exactly q outputs. Extending it by zero to every other subset also gives a stochastic kernel and minimizes exact-recovery loss, zero for T=S and one otherwise, among all randomized rules with arbitrary-subset actions.

## References

- Truth anchor: `D5/S3/Estimation/SequentialDecisionRisk/FiniteSupportSelectionBayes.finite_support_bayes`
- Dependency: [D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer](FiniteDeficiencyRiskTransfer.md)
