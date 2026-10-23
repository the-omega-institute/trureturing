---
slug: sain-manna-paul-2024-linf-k-number
bibkey: sainmannapaul2024local
doi: null
url: https://arxiv.org/abs/2407.08900v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/BanachGeometry/LinfKNumber.result
---

# The K-number and extreme-point K-sets of real finite-dimensional sup-norm spaces

## Problem

D. Sain, J. Manna, K. Paul, *On local preservation of orthogonality and its application to isometries*, arXiv:2407.08900v1, *Linear Algebra and its Applications* (2024), states:

> Definition 1. Let X be a Banach space. A set A ⊂ S_X is said to be a Koldobsky-set, for the sake of brevity, a K-set, if any operator T ∈ L(X) that preserves Birkhoff-James orthogonality at each point of A, is necessarily a scalar multiple of an isometry.

> Definition 3. Let X be a Banach space having a finite K-set. Then the K-number of X is defined by min{|A| : A is a K-set of X}. We denote the K-number of X by κ(X).

The Open Question at the end of §2 is:

> Open Question: Characterize the minimal K-sets in ℓ^n_∞ and hence find κ(ℓ^n_∞).

The spaces are real, and minimality is under inclusion. The result determines the K-number for $n\ge2$ and characterizes the minimal K-sets consisting of extreme points; it leaves the classification involving non-extreme points open.

## Motivation

Local preservation of Birkhoff–James orthogonality can force a global scalar isometry. Determining the smallest test sets distinguishes the number of points needed from their geometry. The extreme-point characterization also gives a positive answer for $\ell_\infty^n$ to the final question of arXiv:2511.20345 about $n$ linearly independent extreme points in a polyhedral Banach space.

## Gap

Proposition 2.1 and Remark 2.20 of arXiv:2407.08900v1 give
$n\le\kappa(\ell_\infty^n)\le2^{n-1}$; Remark 2.20 makes the full extreme-point set a K-set. Theorem 2.22 proves $\kappa(\ell_1^n)=n$.

The follow-ups arXiv:2501.02714, 2501.10719, 2504.11161, and 2511.20345 leave $\kappa(\ell_\infty^n)$ undetermined. The finite-dimensional extreme-point theorem of 2504.11161 does not determine the smallest K-set, and its Remark 2.15 shows that arbitrary $n$ linearly independent points need not suffice in $\ell_2^3$. The final question of 2511.20345 asks whether $n$ linearly independent extreme points suffice in every $n$-dimensional polyhedral space. These statements do not provide the spanning characterization for the sup norm.

## Route

The Lean carrier is `Fin n → ℝ` with its sup norm. The definition `BJOrth x y` means

$$
\forall t\in\mathbb R,\quad \|x\|\le\|x+ty\|.
$$

`PreservesBJAt T x` means that for every $y$, $x\perp_B y\Rightarrow Tx\perp_B Ty$. `IsScalarMulIsometry T` means that there is $c\ge0$ such that $\|Ty\|=c\|y\|$ for every $y$; it includes the zero operator. On this finite-dimensional carrier all linear maps are bounded, so the quantification over `LinearMap` matches $L(X)$. A nonzero norm-scaling linear endomorphism is a scalar multiple of a linear isometry.

The private lemma `extreme_iff` identifies the extreme points of the closed unit ball with vectors having $|u_i|=1$ for every coordinate. At such a vector $u$, a zero coordinate of $y$ implies $u\perp_B y$ (`vertex_zero_BJ`). For a nonzero preserving image, a kernel vector would let a coordinate of $u+sz$ vanish while its image remains the same nonzero vector. This proves injectivity (`preserving_injective`). The active-coordinate criterion `active_not_BJ` then proves that every coordinate of $Tu$ has absolute value $\|Tu\|$ (`image_vertex`).

Write $S=T^{-1}$ and $v=Tu/\|Tu\|$. The inverse satisfies $u_i S_{ij}v_j\ge0$ (`inverse_sign`, with the unnormalized $Tu$ in its statement). Two nonzero entries in a column force every $u\in A$ into one fixed hyperplane $u_i=\pm u_k$. This contradicts full span (`column_sparse`). Invertibility turns the disjoint column supports into a permutation (`inverse_monomial`), and the image of one vertex fixes a common absolute value for its nonzero entries (`spanning_KSet`). Consequently $T$ scales the norm. The case where $T$ vanishes on all of $A$ gives $T=0$ by spanning.

Conversely, if $A$ has proper span, a nonzero linear functional $f$ annihilating its span defines the rank-one map $Ty=f(y)e_0$. It preserves orthogonality at all points of $A$ because it annihilates them, but cannot scale the norm when $n\ge2$ (`KSet_spans`). The dimension bound gives `KSet_card`.

Finally, `vertex_basis` constructs $n$ vertices: the all-ones vector and, for each coordinate other than coordinate zero, the vector with only that coordinate changed to $-1$. Their differences recover those coordinate vectors, and the all-ones vector recovers the remaining one. Their full span and the sufficiency theorem give an $n$-element K-set.

## Falsifier

For $n\ge2$, the formal claim would fail if an extreme-point set had full span but admitted a locally orthogonality-preserving operator that did not scale the norm; if an extreme-point K-set had proper span; if no $n$-element K-set existed; or if a finite K-set had fewer than $n$ points. The theorem proves all three claim clauses, ruling out these alternatives. It does not assert that every inclusion-minimal K-set has cardinality $n$.

## Evidence

The public declarations in `D5/S3/Analytic/BanachGeometry/LinfKNumber.lean` are `BJOrth`, `PreservesBJAt`, `IsScalarMulIsometry`, `IsKSet`, `claim`, `active_not_BJ`, and `result`. The remaining supporting lemmas are private. The exposed `active_not_BJ` strict-descent criterion is used by `image_vertex`, `inverse_sign`, and `PolyhedralBJRefutation.product_of_bj`; its statement and proof remain in the original Linf owner. The theorem `D5.S3.Analytic.BanachGeometry.LinfKNumber.result` has type `claim`.

For every $n\ge2$, `claim` is the conjunction of: the equivalence between `IsKSet A` and full span for any set $A$ contained in the extreme points of the closed unit ball; the existence of an $n$-element finite K-set; and the lower bound $n\le|A|$ for every finite K-set, without an extreme-point restriction on that lower bound.

The axiom closure is $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$, with no `sorry` or additional axiom. There is no separate definition of $\kappa$, inclusion-minimality theorem, or transport theorem in the module: the first two are consequences of the three claim clauses and finite-dimensional basis theory; transport remains unformalized.

## Triage

### What the settlement shows

1. **Proved (Lean) — extreme-point characterization.** For $n\ge2$ and $A\subseteq\operatorname{Ext}(B_{\ell_\infty^n})$, $A$ is a K-set if and only if it spans $\mathbb R^n$. This is the first clause of `claim`.

2. **Proved (Lean cardinality clauses) — $\kappa(\ell_\infty^n)=n$ for $n\ge2$.** An $n$-element K-set exists, and every finite K-set has at least $n$ elements. Infinite sets have no cardinality below the finite number $n$, so the three claim clauses give $\kappa=n$ under Definition 3; $\kappa$ is not a separate Lean definition. For $n=1$, every linear endomorphism scales the norm, so the empty set is a K-set and $\kappa(\ell_\infty^1)=0$ under Definition 3. This is why the claim is stated for $n\ge2$.

3. **Proved (consequence of the Lean characterization) — minimal extreme-point K-sets.** The inclusion-minimal spanning subsets of the finite vertex set $\{\pm1\}^n$ are precisely its bases, hence precisely its linearly independent $n$-subsets. Removing an element from a basis destroys span, and a spanning set that is not a basis contains a proper spanning subset. This consequence is not separately named in Lean.

4. **Proved (consequence of the Lean characterization) — the sup-norm case of the final question of 2511.20345.** Any $n$ linearly independent extreme points in $\ell_\infty^n$ span, so preservation at them forces a scalar isometry. The all-polyhedral assertion is not proved.

5. **Proved (mechanism in Lean, with an explanatory identity) — inverse signs and column sparsity.** `inverse_sign` proves $u_i S_{ij}(Tu)_j\ge0$; normalization gives $u_i S_{ij}v_j\ge0$. Since $Sv=u/\|Tu\|$, summing the nonnegative terms gives $\sum_j|S_{ij}|=1/\|Tu\|$ for every row. This row-sum identity is reasoning from the sign statement, not a separately proved Lean step. The formal proof instead establishes column sparsity and then fixes the common modulus in `spanning_KSet`. `column_sparse` proves that two nonzero entries in one column would impose $u_i=\pm u_k$ on all of $A$; full span excludes this. Linear independence of $n$ test vertices supplies that span.

6. **Open (transfer, not formalized) — isometric copies.** Conjugating by a linear isometric equivalence is the expected transport route for any space linearly isometric to $\ell_\infty^n$. The orthogonality, operator, and K-set transport statements are not formalized in this module.

7. **Refuted — the universal polyhedral assertion.** The separate [polyhedral extreme-test dossier](manna-mandal-paul-sain-2025-polyhedral-extreme-tests.md) gives the native real-plane counterexample to the final question of arXiv:2511.20345. This sup-norm module retains its positive conclusion. The consecutive-vertex results of Theorem 2.16 of 2407.08900 concern the regular case. The K-number of other polyhedral spaces is not determined here.

8. **Open — minimal K-sets involving non-extreme points.** Remark 2.20(ii) gives the inclusion-minimal K-set $\{(1,1),(1,0),(0,1)\}$ in $\ell_\infty^2$, of size three despite $\kappa(\ell_\infty^2)=2$. The classification of all such minimal K-sets remains open.

## ASSUMED-UNVERIFIED

Coverage is limited to the cited arXiv versions; journal-version equivalence and later unindexed resolutions are unverified.

PDF page numbers for Definitions 1 and 3 and the end-of-§2 Open Question are unverified; the quotations use definition and section locators.

The row-sum identity and the minimal-basis and final-question consequences are mathematical deductions from the formal statements, not additional named Lean theorems. Isometric transport remains unformalized in this module. The separate polyhedral refutation has its own source and claim.
