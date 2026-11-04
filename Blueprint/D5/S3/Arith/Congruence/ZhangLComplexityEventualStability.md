# Eventual stability of l-complexity

## Abstract

Every positive-multiple orbit reaches permanent linear l-complexity growth.

Expressions have one leaf value l and internal operations addition and multiplication. For l > 1, an expression with s leaves has value at most l raised to s. Multiplying an expression by one additional leaf increases its size by one. Consequently the l-complexity of l^m * n minus m is a nonincreasing positive integer sequence. The antitone chain condition makes this sequence eventually constant. The lower bound permits cancellation of natural subtraction and gives permanent linear growth from a suitable point in every orbit. This is the discrete-defect stabilization method used by Altman and Zelinsky for ordinary integer complexity; the expression bound here applies to every natural l > 1.

**Definition 1.1 (Natural expression value).**

$$\forall l \in \operatorname{Nat},\; (\operatorname{value}\left(l, \operatorname{Expr}.\operatorname{x}\right) = l) \land ((\forall e \in \operatorname{Expr},\; \forall f \in \operatorname{Expr},\; \operatorname{value}\left(l, \operatorname{Expr}.\operatorname{add}\left(e, f\right)\right) = \operatorname{value}\left(l, e\right)+\operatorname{value}\left(l, f\right)) \land (\forall e \in \operatorname{Expr},\; \forall f \in \operatorname{Expr},\; \operatorname{value}\left(l, \operatorname{Expr}.\operatorname{mul}\left(e, f\right)\right) = \operatorname{value}\left(l, e\right)\cdot \operatorname{value}\left(l, f\right)))$$

*Formalization.* `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.value` (`✓ std3`).

*Citation.* Pengcheng Zhang (2024). *The 2-complexity of even positive integers*. DOI: [10.48550/arXiv.2411.19364](https://doi.org/10.48550/arXiv.2411.19364). URL: <https://arxiv.org/abs/2411.19364v1>.

*Commentary.*

An expression is evaluated in Nat by assigning l to each leaf and using addition and multiplication at the corresponding internal nodes. Expr denotes KumarPengTranModularComplexity.Expr.

**Definition 1.2 (Natural l-complexity).**

$$\forall l \in \operatorname{Nat},\; \forall n \in \operatorname{Nat},\; \operatorname{complexity}\left(l, n\right) = \operatorname{sInf}\left(\{k:\operatorname{Nat}\mid \exists e \in \operatorname{Expr},\; (\operatorname{Expr}.\operatorname{leaves}\left(e\right) = k) \land (\operatorname{value}\left(l, e\right) = n)\}\right)$$

*Formalization.* `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.complexity` (`✓ std3`).

*Citation.* Pengcheng Zhang (2024). *The 2-complexity of even positive integers*. DOI: [10.48550/arXiv.2411.19364](https://doi.org/10.48550/arXiv.2411.19364). URL: <https://arxiv.org/abs/2411.19364v1>.

*Commentary.*

Page 2: “Given a positive integer n ∈ lZ⁺, define the l-complexity of n, denoted as ‖n‖_l, as the minimal number of l’s that are needed to express n in terms of l using only addition and multiplication (and parentheses).” Complexity is the natural sInf of attainable leaf counts. Expr.leaves counts the leaves; value l e evaluates e in Nat. For a positive multiple of l, the set of leaf counts is nonempty.

**Definition 1.3 (Numbers with permanent linear growth).**

$$\forall l \in \operatorname{Nat},\; \operatorname{A}\left(l\right) = \{n:\operatorname{Nat}\mid (0 < n) \land ((l \mid n) \land (\forall m \in \operatorname{Nat},\; \operatorname{complexity}\left(l, l^{m}\cdot n\right) = m+\operatorname{complexity}\left(l, n\right)))\}$$

*Formalization.* `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.A` (`✓ std3`).

*Citation.* Pengcheng Zhang (2024). *The 2-complexity of even positive integers*. DOI: [10.48550/arXiv.2411.19364](https://doi.org/10.48550/arXiv.2411.19364). URL: <https://arxiv.org/abs/2411.19364v1>.

*Commentary.*

Question 3, page 10: “Let l > 1 and define A_l := {n ∈ lZ⁺ : ‖l^m · n‖_l = m + ‖n‖_l for all m ≥ 0}.” In Nat, membership in lZ⁺ means 0 < n and l ∣ n. The variable m ranges over all natural numbers, including zero. Page 2: “Given a positive integer n ∈ lZ⁺, define the l-complexity of n, denoted as ‖n‖_l, as the minimal number of l’s that are needed to express n in terms of l using only addition and multiplication (and parentheses).” The value function is structural recursion on Expr, with leaf l and operations Nat.add and Nat.mul. The complexity function is the natural sInf of the attainable leaf counts. Expr denotes KumarPengTranModularComplexity.Expr; Expr.leaves counts the leaves.

**Definition 1.4 (Every orbit reaches A).**

$$(\operatorname{claim}) \Leftrightarrow (\forall l \in \operatorname{Nat},\; (1 < l) \Rightarrow (\forall n \in \operatorname{Nat},\; (0 < n) \Rightarrow ((l \mid n) \Rightarrow (\exists m0 \in \operatorname{Nat},\; l^{m0}\cdot n\in \operatorname{A}\left(l\right)))))$$

*Formalization.* `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.claim` (`✓ std3`).

*Citation.* Pengcheng Zhang (2024). *The 2-complexity of even positive integers*. DOI: [10.48550/arXiv.2411.19364](https://doi.org/10.48550/arXiv.2411.19364). URL: <https://arxiv.org/abs/2411.19364v1>.

*Commentary.*

Question 3, page 10: “Can one say anything about the set A_l? For example, is it true that for every n ∈ lZ⁺, there exists m₀ ≥ 0 such that l^{m₀} · n ∈ A_l?” Together with the preceding sentence “Let l > 1 and define A_l := {n ∈ lZ⁺ : ‖l^m · n‖_l = m + ‖n‖_l for all m ≥ 0}.” The variables l, n and m0 are natural numbers; m0 denotes the source's m₀. Positivity and divisibility express n ∈ lZ⁺. This proposition is the every-orbit assertion in Question 3.

**Theorem 1.5 (Eventual stability on every positive-multiple orbit).**

$$\forall l \in \operatorname{Nat},\; (1 < l) \Rightarrow (\forall n \in \operatorname{Nat},\; (0 < n) \Rightarrow ((l \mid n) \Rightarrow (\exists m0 \in \operatorname{Nat},\; l^{m0}\cdot n\in \operatorname{A}\left(l\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.result` (`✓ std3`). ∎

*Resolves.* `Problems/zhang-2024-l-complexity-question-3` (proved) by `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"zhang-2024-l-complexity-question-3","declaration_gid":"D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Pengcheng Zhang (2024). *The 2-complexity of even positive integers*. DOI: [10.48550/arXiv.2411.19364](https://doi.org/10.48550/arXiv.2411.19364). URL: <https://arxiv.org/abs/2411.19364v1>.

*Commentary.*

Every positive multiple n of every natural l > 1 has a translate l^m0 * n in A l. The exponential bound on expression values gives l-complexity of l^m * n at least m + 1. The one-leaf extension makes the corresponding natural defect nonincreasing. After the defect becomes constant, cancellation yields the equality required by A. No bound on the first such m0 or complete description of A l is asserted.

## References

- Truth anchor: `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.A`
- Truth anchor: `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.claim`
- Truth anchor: `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.complexity`
- Truth anchor: `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.result`
- Truth anchor: `D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.value`
- Dependency: [D5/S3/Arith/Congruence/KumarPengTranModularComplexity](KumarPengTranModularComplexity.md)
