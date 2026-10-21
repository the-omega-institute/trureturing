---
slug: chavez-2023-regular-chs-norm-extrema
bibkey: chavez2023extremalpolynomialnorms
doi: 10.48550/arXiv.2311.04689
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/RegularCHS/Result.result
url: https://arxiv.org/abs/2311.04689v3
---

# Complete homogeneous symmetric norms of regular graphs

## Problem

Chávez et al., *Extremal polynomial norms of graphs*, arXiv:2311.04689v3, Section 8, Problem 3: “Can one find the extrema of the CHS norms over other families of graphs such as regular, unicyclic and complete multipartite graphs?”

For even degree $d=2m\ge2$, Theorem 1.4 defines

$$\|G\|_{2m}=h_{2m}(\lambda_1,\ldots,\lambda_n)^{1/(2m)},$$

where $\lambda_1,\ldots,\lambda_n$ are the real adjacency eigenvalues. Among connected regular simple graphs of order $n\ge3$, the cycle $C_n$ attains the minimum and the complete graph $K_n$ attains the maximum:

$$\|C_n\|_{2m}\le\|G\|_{2m}\le\|K_n\|_{2m}.$$

Here connected means that every two vertices are joined by a walk. In fact the lower coefficient bound $h_{2m}(C_n)\le h_{2m}(G)$ holds for every $r$-regular simple graph of order $n\ge3$ with $r\ge2$, without connectedness. This dossier concerns the regular family. The unicyclic branch is not addressed; the complete multipartite branch is settled separately.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Simple graph of order n | `SimpleGraph (Fin n)` | Literal finite simple graph. |
| Adjacency eigenvalues and complete homogeneous polynomial | `Defs.chs` | `MvPolynomial.hsymm` evaluated at the real Hermitian adjacency eigenvalues. |
| Positive even-degree norm | `Defs.chsNorm`, `2 * m`, `1 ≤ m` | Real power with exponent one divided by the degree. |
| Connected regular family | `G.Connected` and `∃ r, G.IsRegularOfDegree r` | Usual graph connectedness; no isolated-vertex convention is substituted. |
| Every n at least three | `3 ≤ n` in `Defs.claim` | Excludes the smaller orders. |
| Minimum and maximum with attainment | `Result.result : Defs.claim` | Both inequalities and connected regular endpoint graphs. |
| Lower bound without connectedness | Private `Result.chs_cycle_le_regular` | Every regular degree at least two, at every even coefficient degree. |

## Motivation

The settling declaration is `D5/S3/Combinatorics/Graph/RegularCHS/Result.result`. The existing library note `D5/L/GraphInvariants/chavez2023extremalpolynomialnorms` identifies the source article and CHS definitions. The two endpoint graphs belong to the connected regular family for every admissible order.

## Gap

The regular branch is settled for every order at least three and every positive even degree. The unicyclic branch and extremizers within a fixed degree class $r\ge3$ remain open here. No uniqueness classification is asserted.

## Route

Write $H_d(G)=h_d(\lambda(G))$ and $W_k(G)=\operatorname{tr}(A_G^k)$, the number of rooted closed walks of length $k$. The Newton recurrence is

$$(d+1)H_{d+1}(G)=\sum_{k=0}^{d}W_{k+1}(G)H_{d-k}(G).$$

Its nonnegative terms imply nonnegativity of all adjacency CHS coefficients and monotonicity under domination of closed-walk counts. The complete graph dominates every graph on the same vertex set.

For the comparison sequence, $b_0(n,r)=1$ and

$$2m\,b_m(n,r)=r(n+2m-2)b_{m-1}(n,r).$$

Minimum degree at least $r$ gives $W_{2j}(G)\ge nr^j$, hence $H_{2m}(G)\ge b_m(n,r)$. For $r\ge4$, monotonicity in $r$ and the cycle spectral estimate yield

$$H_{2m}(C_n)\le b_m(n,4)\le b_m(n,r)\le H_{2m}(G).$$

The cycle estimate uses trace zero, adjacency eigenvalues of absolute value at most two, and nonnegative even coefficients of finite products of real linear reciprocal factors. A differential identity gives the comparison recurrence for its even coefficients.

For cubic graphs, the even closed-walk moments dominate those of the cycle by the second and fourth moments and log convexity; the odd cycle moments vanish because the order of a cubic graph is even. For two-regular graphs, decomposition into cycles and the Catalan-substituted determinant give coefficientwise domination of the single cycle by the component product. These degree-dependent comparisons give exactly the moment or coefficient bounds needed; no closed-walk domination is asserted for every degree at least four. Connectedness and the degree-sum formula exclude regular degrees zero and one for orders at least three. Monotonicity of the real power transfers the coefficient bounds to norms.

The proof route was derived with the assistance of the ChatGPT Pro model.

## Falsifier

A connected regular simple graph of order $n\ge3$ and a positive integer $m$ whose CHS $2m$-norm lies below the cycle or above the complete graph would contradict `Result.result`. A graph of regular degree at least two with a smaller even coefficient would contradict `Result.chs_cycle_le_regular`. The conclusion does not identify equality cases beyond the two stated endpoint graphs.

## Evidence

`D5/S3/Combinatorics/Graph/RegularCHS/Result.result` proves the literal full claim. The closed-walk comparison is `Newton.chs_le_of_closedWalks_le`; the upper bound is `Newton.chs_le_top`. The high-degree lower bounds use `Cubic.closedWalks_ge_of_minDegree`, `Newton.chs_ge_bseq`, `Newton.bseq_mono`, and `CycleBound.chs_cycle_le_bseq`. The other branches use `Cubic.closedWalks_cubic_ge_cycle` and `TwoRegular.chs_cycle_le_twoRegular`. The main result uses only `propext`, `Classical.choice`, and `Quot.sound`.

Searches covered the arXiv query “CHS norm”, the repository's D5 and Problems entries and pull-request text for CHS and regular-graph CHS, the source article, and Bouthat–Chávez–Sheng, arXiv:2606.17356. The latter treats connected bipartite extrema, matching norms, and a closed-walk Cauchy–Schwarz bound with equality for regular graphs. No answer for the regular family was found in that scope. Citation indexes were not exhaustively checked; this is not a priority certification.

## Triage

- **PROVED (formalized).** For every $n\ge3$ and $m\ge1$, connected regular simple graphs satisfy the two-sided CHS $2m$-norm bound, attained by $C_n$ and $K_n$.
- **PROVED (formalized).** Every $r$-regular simple graph of order $n\ge3$ with $r\ge2$ satisfies $h_{2m}(G)\ge h_{2m}(C_n)$, including disconnected graphs.
- **PROVED (formalized).** Closed-walk domination implies domination of every adjacency CHS coefficient. The comparison sequence $b_m(n,r)$ gives the high-degree lower bound, and $H_{2m}(C_n)\le b_m(n,4)$.
- **PROVED (formalized).** Cubic closed-walk domination and two-regular cycle domination establish the two lower-degree branches.
- **COMPUTED (exact rational arithmetic, outside the Lean development).** There were 864 comparisons for random regular graphs with $4\le n\le12$ and $m\le6$, all satisfying the two coefficient bounds. These are numerical checks and not part of the formal proof.
- **OPEN.** The unicyclic branch of Problem 3 and extremizers within a fixed degree class $r\ge3$.

### What the settlement shows

- **PROVED (formalized).** The regular family has the cycle and complete graph as attained extrema in every positive even CHS degree.
- **PROVED (formalized mechanism).** CHS coefficients are monotone in closed-walk counts by the Newton recurrence with nonnegative terms. The cycle comparisons needed for regular degree at least two follow from degree-dependent walk lower bounds, cubic walk domination, two-regular component factorization, and the cycle spectral bound.
- **COMPUTED.** The 864 finite exact comparisons agree with these bounds; they are independent of the kernel proof.
- **OPEN.** The unicyclic family and the classification of extrema when the regular degree is fixed at least three.

## ASSUMED-UNVERIFIED

Literature completeness, priority and exhaustive coverage of subsequent papers are unverified. The cited article, the bounded literature checks above and the existing library note are the literature evidence. The finite exact computations are not part of the formal proof. Four-slot registration is a separate assessment; no validated registration for `Result.result` is asserted here.
