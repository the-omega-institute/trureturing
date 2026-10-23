---
bibkey: sainmannapaul2024local
authors: D. Sain; J. Manna; K. Paul
year: 2024
title: "On local preservation of orthogonality and its application to isometries"
doi: null
url: https://arxiv.org/abs/2407.08900v1
claim: "The open question at the end of Section 2 asks for the minimal K-sets in real finite-dimensional sup-norm spaces and their K-number; Proposition 2.1 and Remark 2.20 give the bounds n ≤ κ(ℓ∞ⁿ) ≤ 2^(n−1)."
strata_touched:
  - D5/S3/Analytic/BanachGeometry/LinfKNumber
license: citation-only
triage: anchor
---

## Locator

Author text: <https://arxiv.org/abs/2407.08900v1>.
D. Sain, J. Manna, K. Paul, *On local preservation of orthogonality and its application to isometries*, arXiv:2407.08900v1, *Linear Algebra and its Applications* (2024), Definitions 1 and 3 and the Open Question at the end of §2.

## K-sets and the K-number

Definition 1 states verbatim:

> Definition 1. Let X be a Banach space. A set A ⊂ S_X is said to be a Koldobsky-set, for the sake of brevity, a K-set, if any operator T ∈ L(X) that preserves Birkhoff-James orthogonality at each point of A, is necessarily a scalar multiple of an isometry.

Preservation at $x$ means that for every $y$, $x\perp_B y\Rightarrow Tx\perp_B Ty$.

Definition 3 states verbatim:

> Definition 3. Let X be a Banach space having a finite K-set. Then the K-number of X is defined by min{|A| : A is a K-set of X}. We denote the K-number of X by κ(X).

The end of §2 asks verbatim:

> Open Question: Characterize the minimal K-sets in ℓ^n_∞ and hence find κ(ℓ^n_∞).

Here minimal means minimal under inclusion, whereas the K-number minimizes cardinality. Remark 2.20(ii) exhibits both the two-point set $\{(1,1),(1,-1)\}$ and the three-point set $\{(1,1),(1,0),(0,1)\}$ as minimal K-sets in $\ell_\infty^2$.

## Known bounds and neighboring questions

For real polyhedral spaces, Proposition 2.1 gives the dimension lower bound. Remark 2.20 states that the extreme points of the closed unit ball form a K-set, yielding

$$
n\le\kappa(\ell_\infty^n)\le2^{n-1}.
$$

Theorem 2.22 determines $\kappa(\ell_1^n)=n$. The follow-ups arXiv:2501.02714, arXiv:2501.10719, arXiv:2504.11161, and arXiv:2511.20345 do not determine $\kappa(\ell_\infty^n)$. The extreme-point K-set theorem in arXiv:2504.11161 applies to every finite-dimensional space; its Remark 2.15 shows that $n$ linearly independent points need not suffice in $\ell_2^3$. The final question of arXiv:2511.20345 is:

> Open Question: In an n-dimensional polyhedral Banach space, does the preservation of Birkhoff-James orthogonality by a bounded linear operator at any n linearly independent extreme points necessarily imply that the operator is a scalar multiple of an isometry?

## Repository-derived result

For real $\ell_\infty^n$ with $n\ge2$, the companion Lean theorem characterizes K-sets contained in the extreme points of the closed unit ball by full linear span. It constructs an $n$-element K-set and proves that every finite K-set has at least $n$ elements. Thus $\kappa(\ell_\infty^n)=n$. Among extreme-point sets, the inclusion-minimal K-sets are exactly the bases contained in $\{\pm1\}^n$; this also answers the final question of arXiv:2511.20345 positively for these spaces. The classification of minimal K-sets containing non-extreme points remains open.

## ASSUMED-UNVERIFIED

Coverage is limited to the cited arXiv versions; journal-version equivalence and later unindexed resolutions are unverified. The general polyhedral-space assertion is refuted by the real Banach plane in [the separate primary-source note](mannamandalpaulsain2025improvement.md); the positive sup-norm theorem has its original scope.

PDF page numbers for Definitions 1 and 3 and the end-of-§2 Open Question are unverified; the locators above identify the numbered definitions and section.
