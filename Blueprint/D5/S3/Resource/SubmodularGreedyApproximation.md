# Cardinality greedy approximation for monotone submodular objectives

## Abstract

Cardinality greedy approximation for monotone submodular objectives.

**Definition 1.1 (Marginal gain).**

$$\forall Alpha \in Type,\; \forall f \in \operatorname{Finset}\left(Alpha\right) \to \mathbb{R},\; \forall S \in \operatorname{Finset}\left(Alpha\right),\; \forall x \in Alpha,\; \operatorname{marginal}\left(f, S, x\right) = (\operatorname{f}\left(\operatorname{insert}\left(x, S\right)\right)-\operatorname{f}\left(S\right))$$

*Formalization.* `D5/S3/Resource/SubmodularGreedyApproximation.marginal` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The marginal is the change in a finite-set objective after inserting one element.

**Definition 1.2 (Submodularity).**

$$\forall Alpha \in Type,\; \forall f \in \operatorname{Finset}\left(Alpha\right) \to \mathbb{R},\; (\operatorname{Submodular}\left(f\right)) \Leftrightarrow (\forall A \in \operatorname{Finset}\left(Alpha\right),\; \forall B \in \operatorname{Finset}\left(Alpha\right),\; (\operatorname{f}\left(A\right)+\operatorname{f}\left(B\right)) \ge (\operatorname{f}\left(A \cup B\right)+\operatorname{f}\left(\operatorname{inter}\left(A, B\right)\right)))$$

*Formalization.* `D5/S3/Resource/SubmodularGreedyApproximation.Submodular` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Submodularity is expressed by the union/intersection inequality.

**Definition 1.3 (Monotonicity).**

$$\forall Alpha \in Type,\; \forall f \in \operatorname{Finset}\left(Alpha\right) \to \mathbb{R},\; (\operatorname{Monotone}\left(f\right)) \Leftrightarrow (\forall A \in \operatorname{Finset}\left(Alpha\right),\; \forall B \in \operatorname{Finset}\left(Alpha\right),\; (A \subseteq B) \Rightarrow (\operatorname{f}\left(A\right) \le \operatorname{f}\left(B\right)))$$

*Formalization.* `D5/S3/Resource/SubmodularGreedyApproximation.Monotone` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Monotonicity is inclusion monotonicity of the finite-set objective.

**Theorem 1.4 (Diminishing returns).**

$$\forall Alpha \in Type,\; \forall f \in \operatorname{Finset}\left(Alpha\right) \to \mathbb{R},\; \forall hf \in \operatorname{Submodular}\left(f\right),\; \forall A \in \operatorname{Finset}\left(Alpha\right),\; \forall B \in \operatorname{Finset}\left(Alpha\right),\; \forall x \in Alpha,\; (A \subseteq B) \Rightarrow ((\neg x \in B) \Rightarrow (\operatorname{marginal}\left(f, B, x\right) \le \operatorname{marginal}\left(f, A, x\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SubmodularGreedyApproximation.marginal_antitone` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For nested base sets, a new element has no larger marginal at the larger base.

**Theorem 1.5 (Union gain bound).**

$$\forall Alpha \in Type,\; \forall f \in \operatorname{Finset}\left(Alpha\right) \to \mathbb{R},\; \forall hf \in \operatorname{Submodular}\left(f\right),\; \forall A \in \operatorname{Finset}\left(Alpha\right),\; \forall B \in \operatorname{Finset}\left(Alpha\right),\; (\operatorname{f}\left(A \cup B\right)-\operatorname{f}\left(A\right)) \le \sum_{x \in B} \operatorname{marginal}\left(f, A, x\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SubmodularGreedyApproximation.marginal_sum_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The gain of adjoining a finite set is bounded by the sum of its original-base marginals.

**Theorem 1.6 (One greedy step).**

$$\forall Alpha \in Type,\; \forall f \in \operatorname{Finset}\left(Alpha\right) \to \mathbb{R},\; \forall hfmono \in \operatorname{Monotone}\left(f\right),\; \forall hfsub \in \operatorname{Submodular}\left(f\right),\; \forall k \in \mathbb{N},\; \forall O \in \operatorname{Finset}\left(Alpha\right),\; \forall S \in \operatorname{Finset}\left(Alpha\right),\; \forall e \in Alpha,\; (O.card \le k) \Rightarrow ((\forall x \in Alpha,\; (\neg x \in S) \Rightarrow (\operatorname{marginal}\left(f, S, x\right) \le \operatorname{marginal}\left(f, S, e\right))) \Rightarrow ((\operatorname{f}\left(O\right)-\operatorname{f}\left(S\right)) \le ((k: \mathbb{R})\cdot\operatorname{marginal}\left(f, S, e\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SubmodularGreedyApproximation.greedy_step_gap` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A maximum available marginal captures at least the average remaining gain of a comparison set.

**Theorem 1.7 (Nemhauser–Wolsey–Fisher cardinality-greedy bound).**

$$\forall Alpha \in Type,\; \forall f \in \operatorname{Finset}\left(Alpha\right) \to \mathbb{R},\; \forall k \in \mathbb{N},\; \forall O \in \operatorname{Finset}\left(Alpha\right),\; \forall S \in \mathbb{N} \to \operatorname{Finset}\left(Alpha\right),\; \forall e \in \mathbb{N} \to Alpha,\; (\operatorname{f}\left(\emptyset\right) = 0) \Rightarrow ((\operatorname{Monotone}\left(f\right)) \Rightarrow ((\operatorname{Submodular}\left(f\right)) \Rightarrow ((k > 0) \Rightarrow ((O.card \le k) \Rightarrow ((S\left(0\right) = \emptyset) \Rightarrow ((\forall i \in \mathbb{N},\; (i < k) \Rightarrow (S\left((i+1)\right) = \operatorname{insert}\left(e\left(i\right), S\left(i\right)\right))) \Rightarrow ((\forall i \in \mathbb{N},\; (i < k) \Rightarrow (\forall x \in Alpha,\; (\neg x \in S\left(i\right)) \Rightarrow (\operatorname{marginal}\left(f, S\left(i\right), x\right) \le \operatorname{marginal}\left(f, S\left(i\right), e\left(i\right)\right)))) \Rightarrow (\operatorname{f}\left(S\left(k\right)\right) \ge ((1-\operatorname{RealExp}\left(-1\right))\cdot\operatorname{f}\left(O\right))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Resource/SubmodularGreedyApproximation.cardinality_greedy_one_sub_exp` (`✓ std3`). ∎

*Citation.* G. L. Nemhauser; L. A. Wolsey; M. L. Fisher (1978). *An Analysis of Approximations for Maximizing Submodular Set Functions—I*. DOI: [10.1007/BF01588971](https://doi.org/10.1007/BF01588971).

*Commentary.*

The proof iterates the one-step gap with ratio 1-1/k and uses (1-1/k)^k ≤ exp(-1). The statement is valid for any ground type with decidable equality because all comparison and greedy sets are finite. It does not assert a weighted-cost, curvature-dependent, or non-monotone extension.

## References

- Truth anchor: `D5/S3/Resource/SubmodularGreedyApproximation.Monotone`
- Truth anchor: `D5/S3/Resource/SubmodularGreedyApproximation.Submodular`
- Truth anchor: `D5/S3/Resource/SubmodularGreedyApproximation.cardinality_greedy_one_sub_exp`
- Truth anchor: `D5/S3/Resource/SubmodularGreedyApproximation.greedy_step_gap`
- Truth anchor: `D5/S3/Resource/SubmodularGreedyApproximation.marginal`
- Truth anchor: `D5/S3/Resource/SubmodularGreedyApproximation.marginal_antitone`
- Truth anchor: `D5/S3/Resource/SubmodularGreedyApproximation.marginal_sum_bound`
