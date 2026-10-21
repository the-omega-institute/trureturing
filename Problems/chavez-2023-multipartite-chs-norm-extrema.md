---
slug: chavez-2023-multipartite-chs-norm-extrema
bibkey: chavez2023extremalpolynomialnorms
doi: 10.48550/arXiv.2311.04689
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/MultipartiteCHS/Result.result
url: https://arxiv.org/abs/2311.04689v3
---

# Complete homogeneous symmetric norms of complete multipartite graphs

## Problem

Chávez et al., *Extremal polynomial norms of graphs*, arXiv:2311.04689v3, Section 8, Problem 3: “Can one find the extrema of the CHS norms over other families of graphs such as regular, unicyclic and complete multipartite graphs?”

For a complete $r$-partite graph with positive part sizes $a_1,\ldots,a_r$ and total order $n$, the cited article defines, for even $d=2m$, the CHS norm by

$$\|G\|_{2m}=h_{2m}(\lambda_1,\ldots,\lambda_n)^{1/(2m)},$$

where the $\lambda_i$ are the adjacency eigenvalues. This dossier settles the complete multipartite branch only. The regular and unicyclic branches remain open.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Complete multipartite graph | `Vtx a` and `adj a` | Literal vertices and adjacency matrix for the part sizes. |
| Complete homogeneous symmetric polynomial | `chs` | Evaluation of `MvPolynomial.hsymm` at the real adjacency eigenvalues. |
| Even-degree norm | `chsNorm` | Real power with exponent `1 / d`, specialized to `d = 2 * m`. |
| Minimum part multiset | `minParts r n` | One part of size `n-r+1` and `r-1` singleton parts. |
| Maximum part multiset | `balancedParts r n` | Parts differ by at most one, with the prescribed quotient and remainder. |
| Unique extrema | `claim` and `Result.result` | Both inequalities and both equality classifications up to permutation. |

## Motivation

The settling declaration is `D5/S3/Combinatorics/Graph/MultipartiteCHS/Result.result`. The existing library note `D5/L/GraphInvariants/chavez2023extremalpolynomialnorms` is reused for the cited article and its CHS definitions. The result addresses the complete multipartite family named in Section 8, Problem 3; it does not address regular or unicyclic graphs.

## Gap

The complete multipartite branch is settled for every fixed number of parts, every admissible order, and every positive even degree. The regular and unicyclic branches, and closed expressions for the two extremal values beyond the reciprocal recurrence, remain open.

## Route

The determinant identity for the complete multipartite adjacency pencil is

$$\det(I-tA)=1-\sum_{j\ge 2}(j-1)e_j(a)t^j,$$

where $e_j(a)$ is the elementary symmetric function of the part sizes. The reciprocal generating series gives the recurrence

$$H_0=1,\qquad H_d=\sum_{j=2}^{d}(j-1)e_j(a)H_{d-j}.$$

Every coefficient is a polynomial with nonnegative coefficients in the elementary symmetric functions with index at least two. The elementary symmetric functions are Schur-concave in the part sizes. A two-part transfer preserves the sum and changes the product of the selected parts, so balancing strictly increases the coefficients and unbalancing strictly decreases them. The strict quadratic contribution and positivity of the even coefficients give strictness at every positive even degree. The real power with positive exponent preserves the inequalities and their equality cases.

The proof route was derived with the assistance of the ChatGPT Pro model.

## Falsifier

A positive complete $r$-partite part-size vector of total $n$ for which the CHS $2m$-norm lies below the concentrated vector, above the balanced vector, or attains either endpoint without the stated part multiset would contradict `Result.result`.

## Evidence

`D5/S3/Combinatorics/Graph/MultipartiteCHS/Result.result` proves the complete multipartite statement in the Lean kernel. The determinant-to-recurrence bridge is `Spectral.chs_eq_recH`; the strict recurrence extrema are `Extremal.recH_extremal`; positivity is `Recurrence.recH_two_mul_pos`. The accepted axiom closure of the main result is contained in `{propext, Classical.choice, Quot.sound}`.

The literature checks recorded for this problem covered the arXiv API for “CHS norm” and “complete homogeneous symmetric” with graph, the repository's D5, Problems and Library entries for CHS and complete multipartite graphs, and repository pull-request and issue text for “CHS” and “CHS norm”. The follow-up article on connected bipartite CHS extrema was also read. No answer for the complete multipartite family was found in that scope. Citation indexes were not exhaustively checked; this is not a priority certification.

## Triage

- **PROVED (formalized).** For $r\ge2$, $n\ge r$, and $m\ge1$, over complete $r$-partite graphs with positive part sizes summing to $n$, the CHS $2m$-norm has the unique minimum at part sizes $\{n-r+1,1,\ldots,1\}$ and the unique maximum at the balanced partition, up to permutation of parts.
- **PROVED (formalized).** The determinant identity is $\det(I-tA)=1-\sum_{j\ge2}(j-1)e_jt^j$; its reciprocal coefficient recurrence, strict coefficient comparison, and two-part transfer monotonicity are proved.
- **COMPUTED.** Exact rational arithmetic from adjacency-power traces tested every $2\le r\le n\le9$ and $m\le4$, giving 348 comparisons with the stated extremal classification.
- **OPEN.** The regular and unicyclic branches of Problem 3 remain open.
- **OPEN.** Exact closed forms of the extremal values beyond the recurrence remain open.

### What the settlement shows

- **PROVED, kernel-checked.** The fixed-part-count complete multipartite branch of Problem 3 is settled with strict uniqueness at both endpoints.
- **Explanatory mechanism.** Every CHS coefficient is a polynomial with nonnegative coefficients in the elementary symmetric functions $e_j$ for $j\ge2$. Those functions are Schur-concave in the part sizes, and strictness comes from the $e_2^m$ term.
- **COMPUTED.** The finite exact comparisons support the same endpoint classification through $n=9$ and degree parameter $m=4$; they are numerical checks and are not part of the formal proof.
- **Source dependence.** The conclusion concerns complete multipartite graphs with a fixed number of parts and does not settle the regular or unicyclic families named in Problem 3.
- **OPEN.** Closed forms for the extremal recurrence values and the other two graph families remain outside this result.

## ASSUMED-UNVERIFIED

Literature completeness, priority and exhaustive coverage of subsequent papers are unverified. The cited article, the bounded literature checks above and the existing library note are the available literature evidence.
