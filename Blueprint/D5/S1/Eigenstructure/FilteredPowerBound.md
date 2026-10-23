# Filtered Operator Power Bound

## Abstract

Finite lowering depth gives a truncated binomial bound for powers of noncommuting operators.

**Theorem 1.1 (A contraction and a lowering map).**

$$\forall K : Type, [\operatorname{NontriviallyNormedField}\left(K\right)],\ \forall E : Type, [\operatorname{NormedAddCommGroup}\left(E\right)], [\operatorname{NormedSpace}\left(K, E\right)],\ \forall A, B \in \operatorname{ContinuousLinearEnd}\left(K, E\right),\ \forall F : \mathbb{N} \to \operatorname{Submodule}\left(K, E\right), \forall h, k \in \mathbb{N},\ F(0) = \operatorname{zeroSubmodule}\left(K, E\right) \land F(h) = \operatorname{wholeSubmodule}\left(K, E\right) \land\ (\forall j \in \mathbb{N}, j < h \Rightarrow \forall x \in F(j+1), A(x) \in F(j+1) \land B(x) \in F(j)) \land \lvert \lvert A \rvert \rvert \le 1 \Rightarrow\ \lvert \lvert (A+B)^{k} \rvert \rvert \le \sum_{l \in \operatorname{range}\left(h\right)} \operatorname{choose}\left(k, l\right) \cdot \lvert \lvert B \rvert \rvert^{l}$$

*Proof.* Machine-checked in Lean as `D5/S1/Eigenstructure/FilteredPowerBound.norm_add_pow_le_sum_choose` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let K be a nontrivially normed field and E a normed K-vector space. The operators A and B are bounded linear endomorphisms, with the operator norm. Let F be a sequence of submodules with F(0) zero and F(h) equal to E. For every j below h, A preserves F(j+1) and B maps it into F(j). The estimate holds for every natural exponent k if the norm of A is at most one. Neither commutativity, finite dimension nor completeness is needed.

The proof bounds the norm of the kth power applied to a vector in each F(j), simultaneously by induction on k. Splitting the next application into the A and B terms leaves the first vector at the same level and lowers the second by one. The triangle inequality, the operator norm bounds and Pascal's recurrence give the truncated sum. The zero level contains only zero, so the recursion terminates without any assumption that mixed words vanish.

An increasing filtration is a special case; nesting is not needed once the two mapping conditions hold. Height zero is also allowed and forces the space to be trivial. For positive height, binomial coefficients vanish above k, so the displayed sum equals the sum through min(k,h-1). For fixed h it is a polynomial bound in k of degree at most h-1. Application to a physical generation process requires separately identifying its operators, norm and lowering filtration.

## References

- Truth anchor: `D5/S1/Eigenstructure/FilteredPowerBound.norm_add_pow_le_sum_choose`
