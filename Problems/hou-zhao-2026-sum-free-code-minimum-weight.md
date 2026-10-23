---
slug: hou-zhao-2026-sum-free-code-minimum-weight
bibkey: hou2026sumfreedom
doi: 10.48550/arXiv.2609.31489
url: https://arxiv.org/abs/2609.31489v1
triage: theorem
motivation_gids:
  - D5/S3/Arith/SumFreeCodeMinimumWeightRefutation.result
---

# Hou–Zhao: minimum-weight independence of sum-free codes

## Problem

Xiang-dong Hou and Shujun Zhao, *Further Results on Sum-Freedom of Binary
and q-ary Functions*, arXiv:2609.31489v1 (2026-09-25), printed p.14,
immediately after Theorem 4.6:

> There are some open questions. In Theorem 4.1, the dimension and minimum
> weight of the code C(f) are determined and they are independent of f as long
> as f is APN, i.e., 2nd order sum-free. Do we have the same conclusion for
> the code C_s(f) in Theorems 4.5 and 4.6, where f is an sth order sum-free
> function? If the dimension k and the minimum weight d of C_s(f) depend on
> the sum-free function f, what are the ranges for k and d? Likely, these
> questions will lead the investigation of sum-free functions to new directions.

The component considered here is minimum-weight independence alone.
For every finite field K of cardinality q, every n ≥ 2, every
1 ≤ s ≤ n−1 and every f,g:K^n→K^n whose vector sums on **every** affine
s-plane are nonzero, assert d(C_s(f)) = d(C_s(g)). There is no additional
planarity, permutation, non-degeneracy, rank or equal-dimension hypothesis.

The original definition (1.1) uses affine subspaces. A basis of the direction
subspace parametrizes such a subspace bijectively by K^s; independence of
the directions prevents repetitions. `SumFree` uses exactly these sums.
Definitions (4.2) and (4.7) make C_s(h) the kernel of the evaluations of
all reduced monomials of total degree at most s(q−1)−1, together with all
n coordinate rows of h. Each exponent is less than q. These monomials
span the source Reed–Muller space, so redundant rows leave the kernel unchanged.
All q^n points, including zero, are present.

`claim : Prop` retains the full universal assertion over small finite-field
carriers. Every finite field has a small isomorphic carrier. Hamming weight
counts nonzero entries; `minimumWeight` takes the infimum over **nonzero**
kernel words in the extended naturals. The zero code has minimum infinity.
This convention adds no premise and is irrelevant to the displayed nonzero codes.
The conclusion is literally `result : ¬ claim`.

The separate dimension result, issue14810 and PR14846, neither proves nor
refutes this minimum-weight component. The present result does not classify
the complete ranges of k and d and does not contradict Theorem 4.6's bounds.

## Motivation

Function-independent parameters in the binary APN case need not persist
under the weaker general sum-free hypothesis. An admissible pair with
different **attained** minima isolates the distance question from dimension.

## Gap

Tier 1: this is an explicit concluding question in a recent published arXiv
source. The literal minimum-weight settlement is suspected-novel within
the bounded readings; worldwide priority is unverified.
The prospective formal commitment is
[issue15094](https://github.com/the-omega-institute/trureturing/issues/15094),
posted 2026-10-10 before Lean probing.
The admission basis is `open-problem-resolution`, under the explicit
final-result exception. There is one new result, with essential definitions;
no standalone classical distance theorem is supplied.

The bounded readings are Hou–Zhao v1; Carlet–Ding–Yuan 2005;
Wu–Yang–Feng arXiv:2306.06422v2; Heering–Kaspers–Taranchuk
arXiv:2605.22958v1; Ebeling–Hou–Rydell–Zhao arXiv:2410.10426v2;
and arXiv:2609.22394v2. The binary non-degenerate result requires
2 ≤ r ≤ n−2 and does not cover the ternary n=2,s=1 pair.
The earlier q-ary sum-freedom paper has no located code-distance answer.
The accepted 2026-10-10 refresh found only v1, no literal answer in seven
recent arXiv search entries, and only the dimension issue/PR in the public
identifier search. These are bounded findings, not worldwide absence.
Unread citation coverage, some final journal versions and Carlet's
WAIFI/ePrint full text remain limits. Unavailable authenticated code searches
and challenged indices are not counted as nonhits.

## Route

Take K=F_3,n=2,s=1 and

$$F(x,y)=(x^2-y^2,2xy),\qquad G(x,y)=(x^2,y^2).$$

On a line a+tv, with v nonzero, the sum of either homogeneous quadratic
map Q is −Q(v). Both Q(v) are nonzero, so both source antecedents hold.
The original Reed–Muller rows specialize to 1,x,y. The remaining rows
are respectively x²−y²,2xy and x²,y².

For each five-row matrix C, explicit matrices E,P,S satisfy

$$I=EP+SC.$$

Thus every kernel word w is E(Pw). The four free coordinates range over
all 81 possibilities. Exact Lean reduction of these possibilities excludes
every nonzero F word of weight less than 5 and every nonzero G word of
weight less than 4. This is a universal exclusion, not a check of only
successful examples. The existing kernel-compression theorem is reused
at its original declaration, as are G, its sum-freedom and its right inverse.

In point order (0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2),
the words

$$w_F=(0,0,1,0,0,1,1,1,2),\qquad
w_G=(1,2,0,2,1,0,0,0,0)$$

have weights 5 and 4. Their original parity syndromes vanish. These actual
attaining words, together with the lower exclusions, establish the two minima.

The F distance-five fact is classical: Claude Carlet, Cunsheng Ding and
Jin Yuan, *Linear Codes From Perfect Nonlinear Mappings and Their Secret
Sharing Schemes*, IEEE TIT 51(6), 2005, 2089–2102,
DOI10.1109/TIT.2005.847722, equation (7), Theorem 7, printed p.2092.
That theorem concerns the **extended** trace-evaluation code and explicitly
allows m≥2. At (p,m,h)=(3,2,1) its dual has distance 5.
In F_3[t]/(t²+1), squaring z=x+yt has coordinates F, and
Tr((r+st)(u+vt))=2(ru−sv). The trace pairings and constants span exactly
1,x,y,F_1,F_2, identifying the dual with the original kernel.
G is not planar: its derivative in direction (1,0) is (2x+1,0).
The classical theorem does not state minimum-weight independence for all
sum-free maps. Its application is credited here; it is not a new theorem
or an assumed Lean premise. Necessary finite checks remain inside `result`.

## Falsifier

The refutation fails if a source antecedent is false, if the generic code
does not specialize to the original ternary parity map, if a reconstruction
identity is wrong, if a smaller nonzero kernel weight survives, or if either
attaining word fails its original syndrome. None may be replaced by an
assumed premise or a restricted universal assertion.

## Evidence

The closed theorem `D5/S3/Arith/SumFreeCodeMinimumWeightRefutation.result`
compiles with Lean 4.33.0. The current inspector verifies that the compiled
claim has literal type `Prop` and the result has literal type `Not claim`,
without free term or universe parameters. The axiom closure is exactly
`propext`, `Classical.choice`, `Quot.sound`; there is no `sorry`, new axiom
or native evaluation. The proof shape is bind-only: existing suppliers,
logical binding and exact finite reduction. Its admission basis is the
named external open-problem resolution, not an escape-witness claim.
The generic source parity map is identified locally with the existing
ternary parity map, and the sum-free antecedents specialize to the existing
ternary predicate. Universal lower exclusions and actual attaining words
prove minimum values 5 and 4 inside the single result.

The original supplier's visibility conversion retains all twenty included
frozen declaration identities and the module statement identity
`sha256:d08863231c3c8321cdc44120cd6099e66a6cfafde0f77425f653cf5aac12d131`.
There is no copied or forwarding declaration. The Scribe resolution marker
records the literal negation as a refutation of the minimum-weight component.

The existing independent ordinary enumeration covers all 3^9 words for
each original matrix and agrees with minima 5 and 4; it is corroboration,
not Lean evidence.

## Triage

### What the settlement shows

The original F and G kernels have different attained minima although both
maps satisfy every affine-line sum-free condition. The counterexample does
not contradict Theorem 4.6's bounds. The separate dimension result remains
distinct from the minimum-weight component.

- [refuted: D5/S3/Arith/SumFreeCodeMinimumWeightRefutation.result]
  The literal full-source minimum-weight independence component is false.
- [literature-attested] F's distance five is covered by CDY2005 Theorem7.
- [open] The complete ranges of k and d and other fixed-parameter regimes
  are not settled by this counterexample.

## ASSUMED-UNVERIFIED

Priority outside the bounded corpus, unread final versions and complete
forward-citation coverage remain unverified. No global novelty claim follows.
