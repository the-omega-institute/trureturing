# Callan's weighted Dyck paths

## Abstract

The weighted Dyck-path sum satisfies the A002067 convolution, through a polynomial model for arbitrary up/down words.

**Definition 1.1 (The source sequence).**

$$\forall a: \mathbb{N} \to \mathbb{N}, \operatorname{IsSourceSequence}\left(a\right) = \left((a\left(0\right) = 1) \land (\forall n: \mathbb{N}, a\left(n + 1\right) = \sum_{k \in \operatorname{Finset.range}\left(n + 1\right)} \operatorname{Nat.choose}\left(2 \cdot (n + 1), 2 \cdot k\right) \cdot a\left(k\right) \cdot a\left(n - k\right))\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.IsSourceSequence` (`✓ std3`).

*Citation.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

OEIS A002067, NAME (unnumbered entry, no page number): "a(n) = Sum_{k=0..n-1} binomial(2*n,2*k)*a(k)*a(n-k-1)." The offset and source program set a(0)=1. The source index n >= 1 is written as n+1; k runs from 0 to n.

**Definition 1.2 (Prefix height).**

$$\forall p: \operatorname{DyckWord}, \forall j: \mathbb{N}, \operatorname{prefixHeight}\left(p, j\right) = \operatorname{List.count}\left(\operatorname{DyckStep.U}, \operatorname{List.take}\left(j, \operatorname{DyckWord.toList}\left(p\right)\right)\right) - \operatorname{List.count}\left(\operatorname{DyckStep.D}, \operatorname{List.take}\left(j, \operatorname{DyckWord.toList}\left(p\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.prefixHeight` (`✓ std3`).

*Citation.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

The natural height is the number of U steps minus the number of D steps in the first j steps. Natural-number subtraction is truncated at zero; the Dyck prefix inequalities ensure that no truncation changes a path height.

**Definition 1.3 (Weight of one path).**

$$\forall p: \operatorname{DyckWord}, \operatorname{pathWeight}\left(p\right) = \prod_{j \in \operatorname{Finset.filter}\left((fun j: \mathbb{N} \mapsto \operatorname{List.getD}\left(\operatorname{DyckWord.toList}\left(p\right), j, \operatorname{DyckStep.D}\right) = \operatorname{DyckStep.U}), \operatorname{Finset.range}\left(\operatorname{List.length}\left(\operatorname{DyckWord.toList}\left(p\right)\right)\right)\right)} (j + 1) \cdot \operatorname{prefixHeight}\left(p, j + 1\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.pathWeight` (`✓ std3`).

*Citation.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

OEIS A002067, Callan COMMENTS (unnumbered entry, no page number): "a(n) is the total weight of Dyck n-paths with weight defined as follows. Given a Dyck path, for each upstep, record its position in the path and the height of its upper endpoint; then multiply together all of these positions and heights. For example, the Dyck 4-path P = UUDUUDDD has upsteps in positions 1,2,4,5 ending at heights 1,2,2,3 respectively, and hence weight(P) = 480. (In fact the positions determine the heights because, for the k-th upstep, position + height = 2k.)" Positions are one-based; the index j in the formula is zero-based, so position and upper height are j+1 and prefixHeight(p,j+1).

**Definition 1.4 (Total path weight).**

$$\forall n: \mathbb{N}, \operatorname{weightedDyckSum}\left(n\right) = \sum_{p: \{p: \operatorname{DyckWord} \mid \operatorname{DyckWord.semilength}\left(p\right) = n\}} \operatorname{pathWeight}\left(\operatorname{val}\left(p\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.weightedDyckSum` (`✓ std3`).

*Citation.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

The sum ranges over every Mathlib DyckWord of semilength n. It includes the empty word at n = 0. The value of the product over its empty set of upsteps is one.

**Definition 1.5 (Derivative polynomials).**

$$\begin{aligned}\operatorname{walkPoly}: \mathbb{N} \to \operatorname{Polynomial}\left(\mathbb{N}\right)\\\operatorname{walkPoly}\left(0\right) = 1\\\forall n: \mathbb{N}, \operatorname{walkPoly}\left(n + 1\right) = \operatorname{Polynomial.derivative}\left(\operatorname{walkPoly}\left(n\right)\right) + \operatorname{Polynomial.C}\left(n + 1\right) \cdot \operatorname{Polynomial.X} \cdot \operatorname{walkPoly}\left(n\right)\end{aligned}$$

*Formalization.* `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.walkPoly` (`✓ std3`).

*Citation.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

Dominici, arXiv:math/0607230v2, Section 3: P_{n+1}(x)=P'_{n}(x)+(n+1)xP_n(x), with P_0(x)=1. The coefficient ring here is the natural numbers. Polynomial differentiation counts the choices of a closing step; multiplication by (n+1)X adds an opening step at position n+1.

**Theorem 1.6 (Uniqueness of the recurrence).**

$$\forall a: \mathbb{N} \to \mathbb{N}, \forall b: \mathbb{N} \to \mathbb{N}, (\operatorname{IsSourceSequence}\left(a\right)) \Rightarrow ((\operatorname{IsSourceSequence}\left(b\right)) \Rightarrow (a = b))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.source_unique` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

Strong induction identifies any two solutions: both indices k and n-k in the recurrence for n+1 are smaller than n+1.

**Theorem 1.7 (Returning coefficients solve the recurrence).**

$$\operatorname{IsSourceSequence}\left((fun n: \mathbb{N} \mapsto \operatorname{Polynomial.eval}\left(0, \operatorname{walkPoly}\left(2 \cdot n\right)\right))\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.poly_is_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

A derivative convolution follows from Pascal's identity by induction. Coefficients of the wrong parity vanish, so evaluation at zero in even degree gives exactly the source recurrence.

**Theorem 1.8 (The weighted Dyck identity).**

$$\forall a: \mathbb{N} \to \mathbb{N}, (\operatorname{IsSourceSequence}\left(a\right)) \Rightarrow (\forall n: \mathbb{N}, a\left(n\right) = \operatorname{weightedDyckSum}\left(n\right))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.source_eq_dyck` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* David Callan (2017). *Two conjectures in OEIS A002067: hafnians and weighted Dyck paths*. URL: <https://oeis.org/A002067>.

*Commentary.*

For every length, summing the polynomial contributions of all up/down words gives walkPoly. A word contributes zero if a prefix is negative; otherwise it contributes its step weight times X raised to its final height. Evaluation at zero selects returning paths. A factorial crossing invariant equates products of upstep upper heights and downstep starting heights.

## References

- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.IsSourceSequence`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.pathWeight`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.poly_is_source`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.prefixHeight`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.source_eq_dyck`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.source_unique`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.walkPoly`
- Truth anchor: `D5/S3/Combinatorics/PerfectMatchings/CallanA002067Dyck.weightedDyckSum`
- Dependency: [D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality](../../../S0/Computability/Coding/DepthBudgetIidGreedyOptimality.md)
- Dependency: [D5/S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment](../../../S1/Recurrence/Invariants/SchroederPeakAlternatingQuadraticMoment.md)
- Dependency: [D5/S3/Combinatorics/NarayanaStrip/CiglerStripExpansionDefs](../NarayanaStrip/CiglerStripExpansionDefs.md)
