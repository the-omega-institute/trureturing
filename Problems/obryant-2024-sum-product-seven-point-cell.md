---
slug: obryant-2024-sum-product-seven-point-cell
bibkey: obryant2024visualizing
doi: 10.48550/arXiv.2411.08139
url: https://arxiv.org/abs/2411.08139v2
triage: theorem
motivation_gids:
  - D5/S3/Arith/SumProductSevenPointCell.result
---

# O'Bryant's seven-point positive-real sum-product cell

## Problem

Kevin O'Bryant, *Visualizing the Sum-Product Conjecture*,
arXiv:2411.08139v2, §5.2:

> We believe that (23, 13) is not in SPP_{R+}(7).

For a domain X, the spectrum is

$$
\operatorname{SPP}_X(n)
 = \{(|A+A|,|AA|): A\subseteq X,\ |A|=n\}.
$$

Here R+ denotes the strictly positive reals, and A+A and AA denote the
pointwise sumset and product set. The exact assertion is that every finite
set A of positive reals with seven elements satisfies

$$
\neg\bigl(|A+A|=23\ \land\ |AA|=13\bigr).
$$

The Lean `claim` retains these quantifiers and hypotheses. Its theorem
`result : claim` follows from the stronger statement

$$
|AA|=13\quad\Longrightarrow\quad |A+A|\geq24.
$$

## Motivation

The least possible product cardinality is 2|A|−1. At equality, positivity
forces a geometric progression, so a specific corner of the sum-product
spectrum becomes a problem about collisions between sums of powers of one
real parameter. The bound excludes the proposed cell and identifies the
sharp minimum of the sum cardinality along this product-minimal boundary.

## Gap

Tier 1, externally stated in arXiv:2411.08139v2 §5.2 and preregistered in
issue #14745. The supplied literature scope lists the integer small-set
papers arXiv:2307.06874 and arXiv:2601.21828, the asymptotic paper
arXiv:2605.28781, and `ErdosProblems/52.lean` in formal-conjectures, which
states the main sum-product conjecture. These references do not themselves
supply a proof of this seven-element positive-real cell exclusion.
The claimed absence of a subsequent settlement within that scope is
`ASSUMED-UNVERIFIED` here: the literature information was supplied with the
task and was not independently browsed.

## Route

For B={b₀<⋯<bₘ₋₁} of positive reals, the chain

$$
b_0^2<b_0b_1<\cdots<b_0b_{m-1}<b_1b_{m-1}<\cdots<b_{m-1}^2
$$

has 2m−1 distinct products. Equality forces a geometric progression.
Every increasing path in the ordered product grid from (0,0) to
(m−1,m−1) has 2m−1 vertices. At equality each path enumerates the full
product set in increasing order. Compare the path that first follows row
zero with the path that changes to row one at column j−1. The entries at
position j give b₀bⱼ=b₁bⱼ₋₁. Induction yields bⱼ=b₀(b₁/b₀)ʲ. Thus the
seven-element case reduces to A={b,br,…,br⁶}, with b>0 and r>1.

There are 28 unordered index pairs. Two different pairs with equal sums
can be oriented as i<k≤l<j. Dividing by rⁱ produces

$$
1+r^d=r^a+r^b,\qquad1\leq a\leq b<d\leq6.
$$

If a+b≤d, then
1+rᵈ−rᵃ−rᵇ≥(rᵃ−1)(rᵇ−1)>0. Hence a+b>d.
The thirteen possible triples have the following exact factorizations,
where 1+Xᵈ−Xᵃ−Xᵇ=(X−1)EHⱼ.

| d | a | b | j | E |
| --- | --- | --- | --- | --- |
| 3 | 2 | 2 | 1 | 1 |
| 4 | 2 | 3 | 2 | 1 |
| 4 | 3 | 3 | 3 | 1 |
| 5 | 2 | 4 | 4 | 1 |
| 5 | 3 | 3 | 5 | 1 |
| 5 | 3 | 4 | 6 | X+1 |
| 5 | 4 | 4 | 7 | 1 |
| 6 | 2 | 5 | 8 | 1 |
| 6 | 3 | 4 | 9 | 1 |
| 6 | 3 | 5 | 2 | X²+1 |
| 6 | 4 | 4 | 10 | X+1 |
| 6 | 4 | 5 | 11 | 1 |
| 6 | 5 | 5 | 12 | 1 |

The factors are

$$
\begin{aligned}
H_1&=X^2-X-1,&H_2&=X^3-X-1,\\
H_3&=X^3-X^2-X-1,&H_4&=X^4-X-1,\\
H_5&=X^4+X^3-X^2-X-1,&H_6&=X^3-X^2-1,\\
H_7&=X^4-X^3-X^2-X-1,&H_8&=X^5-X-1,\\
H_9&=X^5+X^4-X^2-X-1,&H_{10}&=X^4-X^2-1,\\
H_{11}&=X^5-X^3-X^2-X-1,&H_{12}&=X^5-X^4-X^3-X^2-X-1.
\end{aligned}
$$

The omitted factors E are positive for r>1. Distinct Hⱼ cannot vanish at
the same positive real. Polynomial Bézout identities certify this
separation in the formal proof. The following independent rational data
also separates their positive roots: k is the largest negative-coefficient
degree, and u=100^(deg Hⱼ)Hⱼ(L/100),
v=100^(deg Hⱼ)Hⱼ((L+1)/100).

| j | k | L | u | v |
| --- | --- | --- | --- | --- |
| 1 | 1 | 161 | −179 | 44 |
| 2 | 1 | 132 | −20032 | 22637 |
| 3 | 2 | 183 | −50413 | 3904 |
| 4 | 1 | 122 | −466544 | 5886641 |
| 5 | 2 | 117 | −6339979 | 940976 |
| 6 | 2 | 146 | −19464 | 15623 |
| 7 | 3 | 192 | −9474304 | 3092301 |
| 8 | 1 | 116 | −596583424 | 224480357 |
| 9 | 2 | 112 | −385389568 | 660087893 |
| 10 | 2 | 127 | −1145359 | 4595456 |
| 11 | 3 | 153 | −683634007 | 978453024 |
| 12 | 4 | 196 | −1635610624 | 1132702657 |

Every positive-coefficient degree exceeds k, so Hⱼ(x)/xᵏ is strictly
increasing for x>0. The rational signs place its root in
(L/100,(L+1)/100); these twelve intervals are disjoint.

For a fixed root, discard the outer index pairs (i,i+d) associated with
its rows. Their counts are respectively
(4,4,3,2,2,2,2,1,1,1,1,1). At most four pairs are discarded. Every remaining
pair sum is distinct, because a collision would have required one of the
discarded outer pairs. At least 28−4=24 sums remain. Positive scaling
preserves both sum and product cardinalities.

## Falsifier

The conclusion would fail if minimum product cardinality did not force a
geometric progression, if an unordered-pair collision escaped the thirteen
triples, if two distinct factors had a common positive root, or if more
than four outer index pairs had to be removed for one factor. The proof
must retain strict positivity, seven distinct elements, and the exact
product cardinality thirteen throughout these reductions.

## Evidence

The designated closed statement is
`D5/S3/Arith/SumProductSevenPointCell.result : claim`.
The stronger statement is
`D5/S3/Arith/SumProductSevenPointCell.stronger_result`.
The formal argument uses ordered positive-real products, exact polynomial
identities, root separation, and an injective restriction of the finite
pair-sum map. The rational sign table above was independently recomputed
by integer evaluation
Σᵢ cᵢLⁱ100^(deg H−i); its 24 entries agree with the supplied proof.
These arithmetic readouts support the alternative root-isolation argument;
the retained Lean route uses polynomial separation identities.

## Triage

- [proved: D5/S3/Arith/SumProductSevenPointCell.stronger_result]
  For seven positive reals, |AA|=13 implies |A+A|≥24. Consequently
  (23,13) is absent from the positive-real spectrum.
- [computed: exact polynomial reduction of the 28 unordered pair sums
  modulo X²−X−1 and X³−X−1]
  The bound is sharp for geometric progressions with ratio the golden
  ratio φ=(1+√5)/2 and the plastic number, the real root greater than one
  of X³−X−1, approximately 1.3247. Both reductions give 24 distinct sum
  residues. The positive geometric progressions have thirteen products.
  These sharpness instances are not separate retained Lean theorems.
- [computed: exact polynomial reduction modulo H₁,…,H₁₂, together with
  the supplied collision classification]
  The corresponding sum residue counts are
  (24,24,25,26,26,26,26,27,27,27,27,27). The supplied calculation identifies
  {24,25,26,27,28} as the full range of sum cardinalities on seven-term
  geometric progressions with ratio greater than one; generic ratios give
  28. This full-range statement is not separately kernel-checked here.
- [open] Determine the remaining cells of SPP_{R+}(7). The minimum-product
  boundary does not classify sets with larger product cardinality.
- [open] The paper's proposed union formula for n≥7 remains a separate
  question. This exclusion does not establish that formula.

## ASSUMED-UNVERIFIED

The source quotation, latest-version designation, and literature scope
are supplied by the task. No independent network verification of
arXiv:2411.08139v2, arXiv:2307.06874, arXiv:2601.21828,
arXiv:2605.28781, or formal-conjectures `ErdosProblems/52.lean` was performed.
The literature scope is not an exhaustive priority determination.
The full geometric-progression range is attributed to the supplied
classification and computations rather than an additional Lean theorem.
