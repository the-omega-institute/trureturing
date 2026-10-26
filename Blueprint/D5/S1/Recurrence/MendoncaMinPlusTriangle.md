# Mendonça's Min-Plus Configuration Triangle

## Abstract

Strict decrease of the min-plus configuration counts from depth three onward.

**Definition 1.1 (The two root operators).**

$$\begin{aligned}Op : Type\\\operatorname{Op}.\operatorname{plus} : Op\\\operatorname{Op}.\operatorname{min} : Op\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/MendoncaMinPlusTriangle.Op` (`✓ std3`).

*Citation.* J. R. G. Mendonça (2026). *OEIS A400584 and The min-plus configuration triangle: Technical note supporting OEIS A400584*. URL: <https://oeis.org/A400584>.

*Commentary.*

Irregular triangle read by rows: T(n,k) is the number of labelings of the internal vertices of the complete plane binary tree of depth n by + or min, with every leaf equal to 1, that evaluate to k at the root (n >= 1, 1 <= k <= 2^n). (OEIS A400584, NAME, revision 28; unpaginated.) Op has exactly two constructors, Op.plus and Op.min, for addition and minimum.

**Definition 1.2 (Ordered complete trees).**

$$\begin{aligned}LabeledTree : \mathrm{Nat} \to Type\\\operatorname{LabeledTree}.\operatorname{leaf} : LabeledTree\left(0\right)\\\forall n \in \mathrm{Nat}, op \in Op, left \in LabeledTree\left(n\right), right \in LabeledTree\left(n\right),\; \operatorname{LabeledTree}.\operatorname{node}\left(op, left, right\right) : LabeledTree\left(n + 1\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/MendoncaMinPlusTriangle.LabeledTree` (`✓ std3`).

*Citation.* J. R. G. Mendonça (2026). *OEIS A400584 and The min-plus configuration triangle: Technical note supporting OEIS A400584*. URL: <https://oeis.org/A400584>.

*Commentary.*

The tree has 2^n leaves and 2^n - 1 internal vertices. Each internal vertex applies its operator to the values of its two children. Left and right positions are distinguished; labelings related by exchanges of children are counted separately. (OEIS A400584, first COMMENT, revision 28; unpaginated.) LabeledTree n records all internal labels at depth n. Its leaf has depth zero; LabeledTree.node has an operator and two ordered subtrees of equal depth. Thus exchanging unequal subtrees changes the counted labeling.

**Definition 1.3 (Root evaluation).**

$$\begin{aligned}value\left(\operatorname{LabeledTree}.\operatorname{leaf}\right) = 1\\\forall n \in \mathrm{Nat}, left \in LabeledTree\left(n\right), right \in LabeledTree\left(n\right),\; value\left(\operatorname{LabeledTree}.\operatorname{node}\left(\operatorname{Op}.\operatorname{plus}, left, right\right)\right) = value\left(left\right) + value\left(right\right)\\\forall n \in \mathrm{Nat}, left \in LabeledTree\left(n\right), right \in LabeledTree\left(n\right),\; value\left(\operatorname{LabeledTree}.\operatorname{node}\left(\operatorname{Op}.\operatorname{min}, left, right\right)\right) = min\left(value\left(left\right), value\left(right\right)\right)\end{aligned}$$

*Formalization.* `D5/S1/Recurrence/MendoncaMinPlusTriangle.value` (`✓ std3`).

*Citation.* J. R. G. Mendonça (2026). *OEIS A400584 and The min-plus configuration triangle: Technical note supporting OEIS A400584*. URL: <https://oeis.org/A400584>.

*Commentary.*

Irregular triangle read by rows: T(n,k) is the number of labelings of the internal vertices of the complete plane binary tree of depth n by + or min, with every leaf equal to 1, that evaluate to k at the root (n >= 1, 1 <= k <= 2^n). The tree has 2^n leaves and 2^n - 1 internal vertices. Each internal vertex applies its operator to the values of its two children. Left and right positions are distinguished; labelings related by exchanges of children are counted separately. (OEIS A400584, NAME and first COMMENT, revision 28; unpaginated.) The natural-valued recursion starts at one and applies the root operator.

**Definition 1.4 (The configuration count).**

$$\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; T\left(n, k\right) = \operatorname{Nat}.\operatorname{card}\left(\{t : LabeledTree\left(n\right) // value\left(t\right) = k\}\right)$$

*Formalization.* `D5/S1/Recurrence/MendoncaMinPlusTriangle.T` (`✓ std3`).

*Citation.* J. R. G. Mendonça (2026). *OEIS A400584 and The min-plus configuration triangle: Technical note supporting OEIS A400584*. URL: <https://oeis.org/A400584>.

*Commentary.*

Irregular triangle read by rows: T(n,k) is the number of labelings of the internal vertices of the complete plane binary tree of depth n by + or min, with every leaf equal to 1, that evaluate to k at the root (n >= 1, 1 <= k <= 2^n). (OEIS A400584, NAME, revision 28; unpaginated.) Nat.card counts the finite subtype of labeled trees with the specified root value; natural depth zero extends the same tree definition to a single leaf.

**Definition 1.5 (Strict-monotonicity conjecture).**

$$claim \Leftrightarrow (\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; (3 \le n) \Rightarrow ((1 \le k) \Rightarrow ((k < 2^{n}) \Rightarrow (T\left(n, k + 1\right) < T\left(n, k\right)))))$$

*Formalization.* `D5/S1/Recurrence/MendoncaMinPlusTriangle.claim` (`✓ std3`).

*Citation.* J. R. G. Mendonça (2026). *OEIS A400584 and The min-plus configuration triangle: Technical note supporting OEIS A400584*. URL: <https://oeis.org/A400584>.

*Commentary.*

Auffinger and Cable report unpublished work of Albert Chen proving that the root-value probabilities decrease with k, independently discovered by Tam Cheetham-West. Here monotonicity must be understood in the weak sense, since the first two rows contain ties. Conjecture: T(n,k) > T(n,k+1) for n >= 3 and 1 <= k < 2^n. This strict-monotonicity conjecture has been verified by exact computation for 3 <= n <= 12, but is not proved in general. (OEIS A400584, fourth COMMENT, revision 28; unpaginated.) Both indices are natural numbers. The inequalities retain every depth at least three and each adjacent pair of columns from one through two to the depth.

**Theorem 1.6 (Strict decrease at every depth from three).**

$$\forall n \in \mathrm{Nat}, k \in \mathrm{Nat},\; (3 \le n) \Rightarrow ((1 \le k) \Rightarrow ((k < 2^{n}) \Rightarrow (T\left(n, k + 1\right) < T\left(n, k\right))))$$

*Proof.* Machine-checked in Lean as `D5/S1/Recurrence/MendoncaMinPlusTriangle.result` (`✓ std3`). ∎

*Resolves.* `Problems/mendonca-oeis-a400584-strict-monotonicity` (proved) by `D5/S1/Recurrence/MendoncaMinPlusTriangle.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"mendonca-oeis-a400584-strict-monotonicity","declaration_gid":"D5/S1/Recurrence/MendoncaMinPlusTriangle.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. R. G. Mendonça (2026). *OEIS A400584 and The min-plus configuration triangle: Technical note supporting OEIS A400584*. URL: <https://oeis.org/A400584>.

*Commentary.*

For every natural depth n at least three and column k with 1 ≤ k < 2^n, T n (k+1) is strictly less than T n k. Splitting a labeled tree into its root operator and ordered subtrees gives the min-plus counting recurrence. Its adjacent differences decompose into nonnegative products. A product is strictly positive below, at, and above the old support endpoint. Consequently the transform preserves strict decrease for positive strictly decreasing integer inputs of finite support length at least two. The row at depth three starts the induction. The source's support and recurrence retain their meanings; the strict conclusion strengthens weak decrease.

## References

- Truth anchor: `D5/S1/Recurrence/MendoncaMinPlusTriangle.LabeledTree`
- Truth anchor: `D5/S1/Recurrence/MendoncaMinPlusTriangle.Op`
- Truth anchor: `D5/S1/Recurrence/MendoncaMinPlusTriangle.T`
- Truth anchor: `D5/S1/Recurrence/MendoncaMinPlusTriangle.claim`
- Truth anchor: `D5/S1/Recurrence/MendoncaMinPlusTriangle.result`
- Truth anchor: `D5/S1/Recurrence/MendoncaMinPlusTriangle.value`
