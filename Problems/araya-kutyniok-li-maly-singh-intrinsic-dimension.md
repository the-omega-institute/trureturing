---
slug: araya-kutyniok-li-maly-singh-intrinsic-dimension
bibkey: arayakutynioklimalysingh2026intrinsic
doi: 10.48550/arXiv.2610.39674
url: https://arxiv.org/abs/2610.39674v1
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.result
---

# The exact deep-linear intrinsic-dimension prediction fails

## Problem

Araya, Kutyniok, Li, Maly and Singh, *Formalizing the Intrinsic Dimension of Objective Landscapes by a Generalized Notion of Co-dimension*, arXiv:2610.39674v1, Section 4.1, after Proposition 21 in the source TeX, predict:

> As we will see in Section 7, numerical experiments suggest that $d_{\mathsf{int}}(\Theta)=D$ in the deep linear case independently of the width and depth of the network.

The assertion concerns every positive depth $L$, every positive architecture $m_0=D,m_1,\ldots,m_L$, and every nonzero target $u\in\mathbb R^D$. Equation (20) specifies the bias-free polynomial fiber

$$\Theta=\{(W_1,\ldots,W_L,a):W_1^\top\cdots W_L^\top a=u\}.$$

Equation (3) takes the least integer dimension whose random affine plane intersects this fiber with probability one. The source's equivalent generator uses independent standard Gaussian columns and offset. The translate by $g$ equals the translate by its orthogonal projection onto the perpendicular complement of the column span. The full-dimensional plane is the entire ambient space. The copied bias-coordinate paragraph after equation (20) conflicts with its displayed tuple; the displayed tuple, network formula and source Theorem 19 determine the bias-free encoding. PDF theorem numbering differs: the matching theorem is numbered 17 in the PDF.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Independent Gaussian columns and offset | `sampleLaw` | Product of finite independent `stdGaussian` laws and an independent offset; includes dimension zero. |
| Random affine plane, entire space at $d=p$ | `affinePlane` | The two branches preserve the source generator and full-dimensional convention. |
| Equation (3), probability-one infimum | `intrinsicDimension` | ENat infimum over natural $0\le d\le p$; empty infimum is infinity. |
| Bias-free tuple $(W_1,\ldots,W_L,a)$ | Coordinate type in `weight` | Sigma of matrix-entry indices plus the output-coordinate indices; no duplicate coordinate aliases. |
| Ordered network product | `weightProduct`, `realization` | Identity at zero; successor left multiplication; transpose applied to output coordinates. |
| Equation (20), vector equality | `solutionSet` | Exactly the polynomial fiber of `realization` at $u$. |
| Positive depth and every positive width | `claim` | $1\le L$ and $1\le m_l$ for every $l\le L$; unused tail values are inert. |
| Nonzero target and equality to input dimension | `claim` | Every nonzero $u$; right-hand side is $m_0$ in ENat. |
| Refutation of the full universal assertion | `result` | Literal type is the negation of the closed `claim`; no added hypotheses. |

## Motivation

Local manifold codimension does not determine the global probability-one affine-intersection threshold. The scalar one-layer fiber $wa=1$ admits an open collection of affine lines that miss it. This distinction tests the exact quantifier in the source prediction independently of a finite training success rate.

## Gap

The named settlement is preregistered in [#26399](https://github.com/the-omega-institute/trureturing/issues/26399). The literature screen recorded there found no matching settlement in the accessed scope. Its source-record citation counts, bounded author/full-text searches and public formal-settlement searches do not certify exhaustive coverage. Overall literature completeness and priority are `ASSUMED-UNVERIFIED`.

## Route

Set $L=D=m_1=1$ and $u=1$. The fiber is $wa=1$. A zero-dimensional sample with $g_wg_a<1$ misses it. For a line $g+tv$, intersection requires

$$At^2+Bt+C=0,\qquad A=v_wv_a,\quad B=g_wv_a+v_wg_a,\quad C=g_wg_a-1.$$

The region $A<0$ and $B^2-4AC<0$ is open and contains $v=(1,-1)$, $g=0$, where the discriminant is $-4$. The reused Mathlib no-real-root theorem `quadratic_ne_zero_of_discrim_ne_sq` excludes intersection. Gaussian full support and independence give positive measure to each nonempty open miss event. Therefore neither $d=0$ nor $d=1$ qualifies in the infimum. Every qualifying natural dimension is at least two, so the infimum is at least two and contradicts the asserted value one.

## Falsifier

A different random-plane law, omission of dimension zero, a changed order of matrix products, an empty witness fiber, or a nonnegative discriminant throughout the proposed miss region would invalidate this argument. The source-specific definitions preserve the generator, dimension-zero and full-dimensional cases and ordered fiber. The concrete fiber is inhabited at $(w,a)=(1,1)$; the open line-miss region contains $(v,g)=((1,-1),0)$.

## Evidence

`D5/S3/QuadraticForms/DeepLinearIntrinsicDimensionRefutation.result` is the settling kernel-checked negation of `claim`. The module's public surface consists of eight definitions and this one theorem. Its generality is `G`; admission is `open-problem-resolution (#26399; Refuted)`; utility is `kind=certified-instance` with `basis=refutes` targeting `claim`. Every theorem is classified `bind-only`, with the private helpers used by the settling proof. No escape-witness admission is claimed. The source acknowledgement is [the Library note](../Library/QuadraticForms/arayakutynioklimalysingh2026intrinsic.md).

The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

Experiment entry: [araya-kutyniok-li-maly-singh-2026-deep-linear-intrinsic-dimension](https://github.com/the-omega-institute/trureturing-experiments/tree/5fb8908a2eb5c3ec8cde5ca7ce1ebb9dd54fdacf/docs/reports/araya-kutyniok-li-maly-singh-2026-deep-linear-intrinsic-dimension), pinned to commit `5fb8908a2eb5c3ec8cde5ca7ce1ebb9dd54fdacf`. The exact `check.py` has SHA-256 `d28c887336061a38b9074c014b1662f0933a6f33f14ee20b966bb2dda43925a4`. Executing its identical bytes with `python3 /Users/auric/.op-scratch/op/akls2610dint/stageb/experiment-check.py` exits 0 with `ALL_CHECKS_OK`. The tested scope is 36 integer population-MSE networks with $D=1,\ldots,3$, $M=1,\ldots,4$, $L=1,\ldots,3$, a symbolic residual at $D=3$, 24 signatures at $D=1,\ldots,4$, $M=1,\ldots,6$, 216 rational translated-plane maxima for $d=0,\ldots,M$, square completion, strict rational margins, and scalar dimension counts for $M=1,\ldots,29$. No program or dataset is embedded here.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Result and boundary |
| --- | --- | --- |
| Exact probability-one equality | Proved; kernel-checked `result` | The universal exact-value prediction is false under the binding source model. The scalar lower bound $d_{\mathsf{int}}\ge2$ is established by the local `hl` step of `result` and the infimum argument in Route; it is not a separately exported theorem. |
| Positive-measure line-miss region | Proved; proof in prose in Route, using the kernel-checked private `miss_one_open`, `miss_one_nonempty`, `miss_one_disjoint`, `hit_one_lt_one` | Negative discriminant excludes all real intersection parameters on a nonempty open Gaussian event. This is a global affine-intersection obstruction. No separate manifold-dimension theorem is delivered. |
| Exact random model, including zero dimension | Proved; source-definition correspondence and the product-law argument in Route | `sampleLaw` is exactly independent standard Gaussian columns and offset. `hit_zero_lt_one` handles the empty column family, and `hit_one_lt_one` uses the same law. The separate Haar/Gaussian equivalence is source-attested, not a new kernel theorem. |
| Exact checker | Computed; immutable experiment entry in Evidence, exit 0 and the recorded SHA-256 | The 36 networks, 24 signatures, 216 translated-plane maxima, square completion, rational margins and scalar counts through $M=29$ are finite checks. They do not replace the probability proof or establish an unbounded family in Lean. |
| Compatibility with source bounds and other results | Computed for the numbers; proved in prose for compatibility | At $D=M=L=1$, the stated Theorem 19 bounds evaluate to $D=1$ and $M+D=2$ (`python3 -c 'D=M=1; print(D, M+D)'`, exit 0). Hence the source interval $[1,2]$ is compatible with the proved lower bound two. The affine-subspace proposition and finite numerical training traces are not refuted by the exact-value negation. |
| Wider exact values | Open | The general-width $M+1$ lower bound, complete scalar-width equality family, $D>1$ exact values and deeper-network exact values are not formalized here. |
| Quantitative and downstream conclusions | Open | Miss probabilities for the paper's actual initialization and teacher, finite-tolerance thresholds and revised downstream generalization conclusions are not settled. |

The source's established geometric bounds and affine-subspace proposition address different statements from its exact equality prediction. Finite optimized-loss traces test success below a tolerance, rather than probability-one exact intersection. The refutation gives no replacement quantitative estimate for the source's actual initialization, teacher or downstream generalization analysis.

### Literature status

The preregistration's accessed screen includes the source, Li–Farkhoor–Liu–Yosinski arXiv:1804.08838, and the localized positive-semidefinite quadratic scope of Cheng et al. arXiv:2608.12597. Neither neighboring result supplies the indefinite bilinear probability-one threshold. OpenAlex and Semantic Scholar citation enumeration had rate-limit gaps; later-author and full-text searches were bounded; the CoPEER snapshot predates the source and the Machina data has an older generated timestamp. AFTD, Zenodo and repository searches found no matching settlement within their recorded scopes. The inaccessible journal articles and challenged general-web searches in #26399 do not count as verified absence. Completeness remains `ASSUMED-UNVERIFIED`.

## ASSUMED-UNVERIFIED

Worldwide priority, exhaustive citation coverage, any inaccessible later settlement, and an independent formal proof of the source's Haar/Gaussian equivalence are unverified. The source's equivalent Gaussian generator is the binding model. The computations concern only their stated finite ranges. No claim is made about the actual Figure 3 miss probability, finite-tolerance training threshold, all widths or all depths.
