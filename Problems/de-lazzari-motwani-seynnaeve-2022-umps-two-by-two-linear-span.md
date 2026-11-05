---
slug: de-lazzari-motwani-seynnaeve-2022-umps-two-by-two-linear-span
bibkey: delazzarimotwaniseynnaeve2022umpsspan
doi: 10.3842/SIGMA.2022.099
url: https://arxiv.org/abs/2204.10363v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.result
---

# The exact linear-span dimension of binary bond-two uniform matrix product states

## Problem

C. De Lazzari, H. J. Motwani and T. Seynnaeve, *The Linear Span of Uniform Matrix Product States*, SIGMA 18 (2022), 099, DOI 10.3842/SIGMA.2022.099; arXiv:2204.10363v3, Section 3.2, PDF page 9 (`sigma22-099.tex`, lines 540–547):

> **Conjecture 3.8 (Corollary of Conjecture 3.7).**
>
> $\dim \langle \mathrm{uMPS}(2,2,d)\rangle = \begin{cases}\frac{1}{192}\big(d^4-4d^2+192d+192\big) & \text{for }d\text{ even,}\\ \frac{1}{192}\big(d^4-10d^2+192d+201\big) & \text{for }d\text{ odd.}\end{cases}$

For two complex $2\times2$ matrices $X,Y$, let $A_0=X$, $A_1=Y$, and let the tensor $\phi_d(X,Y)$ have coefficient $\operatorname{tr}(A_{i_1}\cdots A_{i_d})$ at the binary word $(i_1,\ldots,i_d)$. The source defines $\mathrm{uMPS}(2,2,d)$ as the closure of the image of $\phi_d$ (the parametrization and following paragraph; TeX lines 215–225). Its linear span is taken over $\mathbb C$.

Issue [#23810](https://github.com/the-omega-institute/trureturing/issues/23810) fixes the reading for every positive integer $d$. The Lean `claim` uses `UniformMPSExpectedDimensionRefutation.uMPS 2 2 d`, the image of this ordered trace parametrization, and asserts the displayed equality after casting the natural-number dimension to $\mathbb Q$. The image/closure bridge is explained below. This reading of Conjecture 3.8 is proved.

## Motivation

The source studies which linear equations vanish on uniform matrix product states, before addressing their higher-degree defining equations. For bond and physical dimension two, the exact span dimension counts the independent trace coordinates at each length and determines how many linear equations are needed in the full tensor ambient space. It also separates the total-dimension question from the stronger character and weight-space questions. The source and its definitions are recorded in [the literature note](../Library/Geometry/delazzarimotwaniseynnaeve2022umpsspan.md).

## Gap

The bounded literature check before any Lean is recorded in #23810:

- The source states Conjecture 3.8 and presents it as a consequence of the weight-space Conjecture 3.7; Table 1 gives computed total dimensions for lengths $8$ through $20$.
- T. Seynnaeve, *Matrix product states, geometry, and invariant theory*, arXiv:2212.13806v2 (2023 version), TeX lines 460–466, asks for a symmetric-group decomposition formula and states: “In particular, it would solve Conjectures 3.7 and 3.8 in” the De Lazzari–Motwani–Seynnaeve paper. That passage does not supply a settlement.
- The orchestrator reports searches of the authors' arXiv listings, the 40 most recent abstract-search results for uniform matrix product states, web results, and repository issues and PRs, with no settlement found. The repository's expected-variety-dimension refutation concerns a different conjecture.
- The doctoral thesis and citing-work checks were incomplete: the thesis was inaccessible, and the citation services returned rate-limit errors.

`not-found-in-searched-scope`.

## Route

Write $T_d$ for the complex span of the functions $(X,Y)\mapsto\operatorname{tr}(A_{i_1}\cdots A_{i_d})$ over binary words of length $d$. In `UniformMPSTwoByTwoTraceWords`, the five invariants are $s=\operatorname{tr}X$, $t=\operatorname{tr}Y$, $u=\det X$, $v=\det Y$, $w=\operatorname{tr}(XY)$, with weights $1,1,2,2,2$. Let $R_k$ be the span of their monomials of weighted degree $k$, with $R_k=0$ for negative integer $k$, and put $C=XY-YX$ and $\delta=w^2-stw+s^2v+t^2u-4uv$.

1. **Tensor/coordinate bridge.** For every $d\in\mathbb N$, the main module's `evaluation_bridge` identifies the dimension of the tensor span with $\dim T_d$. A linear functional on the finite tensor-coordinate space is sent to its evaluation on $\phi_d(X,Y)$; the range is $T_d$ and the kernel is the annihilator of the tensor span. Rank-nullity and the annihilator dimension formula give the equality.
2. **Commutator construction.** For every pair of complex $2\times2$ matrices, `commutator_operations` gives $XC+CX=sC$, $YC+CY=tC$, $XCX=uC$, $YCY=vC$, and $XYC+CYX=wC$; `commutator_square` gives $C^2=\delta I$. For every exponent vector $e\in\mathbb N^5$, `invariant_multiple` constructs a constant-coefficient word combination supported on words of length $\deg(e)+2$ whose value at every pair is $s^{e_0}t^{e_1}u^{e_2}v^{e_3}w^{e_4}C$. Taking the trace after multiplication by $C$ yields twice $\delta$ times that monomial. Since $2\ne0$ in $\mathbb C$, `delta_monomial_mem` places $\delta$ times the monomial in $T_{\deg(e)+4}$.
3. **Upper bound and independence.** For every $d\in\mathbb N$, `coordinates_upper` puts $T_d$ inside the sum of the span of $\operatorname{tr}(X^aY^{d-a})$, $0\le a\le d$, and $\delta R_{d-4}$. The invariant-realization lemma `invariants_attained` requires exactly $s^2\ne4u$ for the proposed five invariant values. The resulting `invariant_polynomial_injective` is unconditional: evaluation on all matrix pairs is injective on the polynomial ring in the five invariants. For every $d\in\mathbb N$, `normal_independent` and `normal_span` establish independence and spanning of the ordered traces together with $\delta$ times the weighted monomials of degree $d-4$. Independence uses $X=xI$, $Y=I$ for every $x\in\mathbb C$ to separate the ordered traces, and polynomial injectivity to separate the remaining monomials.
4. **Dimension and count.** For every $d\in\mathbb N$, `coordinate_dimension` gives $\dim T_d=d+1+\#E_d$, where $E_d$ consists of five nonnegative exponents satisfying $e_0+e_1+2e_2+2e_3+2e_4+4=d$. The Lean `extraIndex d` additionally bounds each exponent by $d$; the main module's `index_unbounded`, for every $d\in\mathbb N$, removes these redundant bounds. For every $k\in\mathbb N$, `compositions_card` counts five exponents of ordinary sum $k$ by $\binom{k+4}{4}$; `odd_equiv` identifies $E_{2k+5}$ with two copies of those compositions, and `even_equiv` identifies $E_{2k+6}$ with the disjoint union of the compositions of $k+1$ and $k$. `small_count` requires $d<4$ and gives zero extra indices; `count_four` gives one at $d=4$. `monomial_count_even` and `monomial_count_odd`, each for every $k\in\mathbb N$, combine these cases. Finally `normal_count`, with $d\in\mathbb N$ and $1\le d$, adds $d+1$ and obtains the two rational expressions in `claim`; `result` applies the bridge and `coordinate_dimension`.

## Falsifier

A dimension formula for a different tensor set would not answer the source conjecture. Here `traceWord` is the trace of the ordered product, and `uMPS` is its range; no normalization, injectivity, invertibility, or noncommutativity condition restricts the two input matrices. The only length hypothesis of `claim` is $1\le d$.

The source takes a closure, whereas the Lean definition takes the image. Let $S$ be the complex linear span of that image. In a finite-dimensional complex vector space, $S$ is Zariski closed because it is the common zero set of linear forms. It therefore contains the source's closure, so the span of that closure is contained in $S$; the reverse inclusion follows because the image is contained in its closure. This elementary identification, including the tensor-basis identification with functions on binary words, is not a closure theorem stated by `result`.

The discriminant restriction in `invariants_attained` is used to establish polynomial injectivity, not to restrict the tensors in `claim`. Likewise, $\delta$ is a nonzero polynomial, but can vanish at a particular matrix pair; the proof does not divide by its value at that pair. A statement about Krull dimension of the variety, or only about finitely many lengths, would not meet this settlement's criterion.

## Evidence

The canonical source is `D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.lean`.

- **Proof.** It defines `claim` and proves `result : claim`; the compiled types agree with the positive-length dimension statement above.
- **Reuse.** It uses the ordered trace parametrization and image from `UniformMPSExpectedDimensionRefutation`, and `UniformMPSTwoByTwoTraceWords.coordinate_dimension` for the trace-coordinate span.
- **Axioms.** `#print axioms` on `result` reports only `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/TensorNetworks/UniformMPSTwoByTwoLinearSpan.lean.json`.

Declaration statements:

- `result`: `sha256:efb69fb47d7d2bb25abbbc3e4b96fb87b7ec5c79aad1f44eb723d7b2791c98a7`;
- `claim`: `sha256:53251a790f94fbd4e7da1cf9dc3ed53a3b70b6880539bafca3ed51dece6edd63`.

## Triage

Tier 1 conjecture of a 2022 paper retained as a target in the later Seynnaeve survey, preregistered in issue #23810 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural length $d\ge1$, the complex linear span of the image `uMPS 2 2 d` of the ordered trace parametrization has dimension $(d^4-4d^2+192d+192)/192$ for even $d$, and $(d^4-10d^2+192d+201)/192$ for odd $d$, with the dimension equality read in $\mathbb Q$.

**Computed, not formalized** (orchestrator, recorded in #23810): exact finite-field ranks of sampled trace tensors at small lengths, consistent with the dimension proved by `result`.

**Argued, not formalized.**

- *Decisive mechanism and sharpness.* The basis in `normal_independent` and `normal_span`, each valid for every $d\in\mathbb N$, separates the $d+1$ ordered traces from the commutator contribution. The five invariants have weights $1,1,2,2,2$, and the commutator contribution starts four degrees later. Consequently their monomial count has generating series $z^4/((1-z)^2(1-z^2)^3)$: each exponent contributes its geometric series, and the shift contributes $z^4$. Adding the series for $d+1$ and omitting length zero gives $\sum_{d\ge1}D(d)z^d=(1-z)^{-2}-1+z^4/((1-z)^2(1-z^2)^3)$, where $D(d)$ is the dimension in `claim`. This explains the quartic growth and the parity dependence; the matching independent family makes the upper dimension count exact. The generating-series identity is not stated by `result`.
- *Linear equations.* With the image/closure identification above, the space of linear equations vanishing on the source variety has dimension $2^d-D(d)$ for every $d\ge1$: it is the annihilator of a $D(d)$-dimensional subspace of the $2^d$-dimensional tensor space. This counts equations without giving a tensor-coordinate generating set or any higher-degree ideal generators.
- *Effect on the source and nearby questions.* Conjecture 3.8 is established without assuming Conjecture 3.7. The source's Theorem 4.8 remains an upper bound; its comparison with a conjectured leading term can instead be made with the exact dimension. The weight-space formulas of Conjecture 3.7 and the associated representation decompositions do not follow from the total dimension alone and are not settled by `result`. Neither are the higher-degree equations discussed in Section 3.3, the symmetric-group decomposition requested in Seynnaeve's arXiv:2212.13806v2, other bond or physical dimensions, or length zero. These questions are outside the positive-length total-dimension statement.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty or priority. The source's conjecture, definitions, Table 1, and relevant dependency passages, and Seynnaeve's cited survey passage were checked directly. The author-list, abstract-search, web-search and repository-search conclusions are attributed to the orchestrator's record in #23810 and were not independently reproduced. The thesis remains unread; whether it contains a settlement is unverified. The unavailable citing-work lists prevent a complete citation check.

The finite-field rank computations and the two Table 1 evaluations are attributed to the orchestrator and were not independently rerun; they supply no evidence for untested lengths beyond their stated range. The image/closure and tensor-basis identifications, generating-series interpretation, linear-equation count, and statements in “Argued, not formalized” are not additional formal conclusions of `result`. No extension to the neighbouring questions listed above is claimed.
