---
slug: rajchel-gasiorowski-zyczkowski-2018-strongly-complementary-permutations
bibkey: rajchelgasiorowskizyczkowski2018robust
doi: 10.1007/s11786-018-0384-y
url: https://arxiv.org/abs/1804.10715v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.result
---

# The maximum number of pairwise strongly complementary permutation matrices

## Problem

G. Rajchel, A. Gąsiorowski and K. Życzkowski, *Robust Hadamard matrices, unistochastic rays in Birkhoff polytope and equi-entangled bases in composite spaces*, Mathematics in Computer Science 12, 473–490 (2018), arXiv:1804.10715v2, Section 4, ask about sets of $n\times n$ permutation matrices whose distinct members are pairwise strongly complementary. The v2 source `unisto9.tex`, lines 686–690, states:

> Due to the definition of strong complementarity each pair of matrices has non-zero entries in different places, so that $k \leq n$. We are not able to determine how the maximal number $k$ of such matrices depends on the dimension $n$, nor whether the bistochastic matrices belonging to the interior of this polytope are unistochastic.

Definitions 4.1 and 4.3 (`unisto9.tex`, lines 606–612 and 623–627) specify the relations:

- Permutation matrices $P,Q$ are complementary if, for every $i,j,h,k$, the equalities $P_{ij}=P_{hk}=Q_{ik}=1$ imply $Q_{hj}=1$.
- They are strongly complementary if they are complementary and, for every $i,j$, $P_{ij}=1$ implies $Q_{ij}=0$.

The definitions and source locators are recorded in [the literature note](../Library/FiniteGroups/rajchelgasiorowskizyczkowski2018robust.md).

Issue [#23851](https://github.com/the-omega-institute/trureturing/issues/23851) fixes the cardinality clause: for every natural $n\ge1$, the maximum is $k(n)=2^{v_2(n)}$, where $v_2(n)$ is the exponent of two in $n$. This identity answers the cardinality question. The question about unistochasticity is separate.

## Motivation

The paper uses strongly complementary permutations to build subsets of the Birkhoff polytope around its flat matrix $W_n$. Its Section 4 triangle lemma assumes the existence of a robust Hadamard matrix of order $n$ and strong complementarity of $P,Q$, and concludes that $\Delta(P,Q,W_n)$ is unistochastic. The ensuing discussion considers larger pairwise strongly complementary families. Determining their maximum size identifies exactly how many permutation vertices such a family can supply, independently of the analytic question about the polytope's interior.

## Gap

The bounded literature check recorded in #23851 reports:

- The question occurs in arXiv v1 and v2; the v2 source contains the wording quoted above.
- The downloaded sources of nine Semantic Scholar citing works, arXiv:1812.09083, 2003.12184, 2101.11288, 2306.00532, 2307.06998, 2312.00497, 2404.18847, 2405.05785 and 2608.21185, and the thesis arXiv:2204.13008 contain no occurrence of the phrase “strongly complementary”.
- Additional reported screens of arXiv:0708.4051 and 2310.03436, and targeted arXiv and Semantic Scholar queries, found no determination of the maximum.
- Repository searches for “1804.10715”, “strongly complementary” and “robust Hadamard” found no prior work on this question; #16299 concerns a different question of arXiv:2101.11288.

`not-found-in-searched-scope`.

## Route

1. **Relative permutations.** For any type $\alpha$ with decidable equality and permutations $\sigma,\tau$ of $\alpha$, `complementary_iff` identifies complementarity of their natural-valued permutation matrices with involutivity of $\sigma^{-1}\tau$. Under the same hypotheses, `strong_iff` identifies strong complementarity with involutivity together with the condition that $\sigma^{-1}\tau$ has no fixed point. For any further permutation $\rho$ of $\alpha$, `row_relabelling` shows that replacing $\sigma,\tau$ by $\sigma\rho^{-1},\tau\rho^{-1}$ preserves strong complementarity.
2. **Normalization and the generated group.** For a nonempty finite set $s$ of permutations of $\mathrm{Fin}\,n$ whose distinct members have strongly complementary matrices, `normalize_family` produces a family $t$ of the same size, with the same pairwise property and containing the identity. For a finite family $t$ with that pairwise property and the identity as a member, `normalized_involutions` proves that each member squares to the identity and distinct members commute. The reused `YangBaxterAutomatonPeriod.isPGroup_closure_of_commuting_involutions`, for a subset of a group whose elements commute with one another and each square to the identity, makes its generated subgroup a $2$-group.
3. **An orbit bounds the family.** For any finite set $t$ of permutations of $\mathrm{Fin}\,n$ with the pairwise strong-complementarity property and any $x\in\mathrm{Fin}\,n$, `orbit_evaluation_bound` gives $|t|\le|Gx|$, where $G$ is its generated subgroup: coinciding evaluations would give a fixed point of a relative permutation. For $n\ge1$ and any subgroup $G$ of the permutation group of $\mathrm{Fin}\,n$ satisfying `IsPGroup 2 G`, `least_orbit_divisor` supplies an orbit of size $2^a$ with $2^a\mid n$. Its proof chooses the least orbit exponent; that orbit size divides every orbit size and hence their sum $n$. Consequently `permutation_family_upper`, for $n\ge1$ and any finite permutation family with the pairwise property, gives $|t|\le2^{v_2(n)}$, including the empty family.
4. **Attainment by translations.** For natural $n,a,m$ with $m>0$ and a bijection $e:\mathrm{Fin}\,n\simeq(\mathrm{Fin}\,a\to\mathbb Z/2)\times\mathrm{Fin}\,m$, `elementary_translation_family` constructs $2^a$ permutations with pairwise strongly complementary matrices. They translate the first coordinate by every vector $v$. For distinct $u,v$, the relative permutation translates by $v-u$, which squares to the identity and has no fixed point. For $n\ge1$, `matrix_family_lower` uses the positive odd decomposition $n=2^{v_2(n)}m$ from `DivisorNimGrundy.valuation_decomposition` and constructs an attaining matrix family.
5. **The supremum is a maximum.** For $n\ge1$, a finite set of natural-valued $n\times n$ matrices all satisfying `IsPermutationMatrix`, and pairwise `IsStronglyComplementary` on distinct members, `matrix_family_upper` bounds its cardinality by $2^{v_2(n)}$. The witness of `matrix_family_lower` places $2^{v_2(n)}$ in the set of attained cardinalities, making that set nonempty. Thus that set is bounded above, and `result` applies `csSup_le` and `le_csSup` with these hypotheses to identify its natural-number supremum with the attained value.

## Falsifier

A settlement would miss the source question if it used a weaker entry condition, omitted disjoint support, or bounded a supremum without establishing the conditions needed to use it. The module uses the four-index condition of Definition 4.1 and the additional support condition of Definition 4.3 verbatim as predicates on natural-valued matrices. Its families additionally require every matrix to be the matrix of a permutation, with the convention $P_{ij}=1$ exactly when $\sigma(i)=j$. Families are finite sets, so repeated matrices cannot inflate their cardinality. The upper bound and attaining construction discharge boundedness and nonemptiness for the supremum.

The conclusion includes $n=1$: a singleton family satisfies the pairwise condition, which concerns distinct members. The statement of `claim` excludes $n=0$.

## Evidence

The canonical source is `D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.lean`.

- **Proof.** It proves `result : claim`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.

Frozen state: `Golden/Frozen/state/D5/S3/Combinatorics/Permutation/StronglyComplementaryPermutationMaximum.lean.json`.

Declaration statements:

- `result`: `sha256:4ed3e2c7e07b136366af1a8ef2c31345a20d6bfdbd3f88a3dc00a7f1b4feb316`;
- `claim`: `sha256:ceb1bc6deb688a5d911a3d05c674e618929edd5a2ee293bc0eb2e242fe9896a4`.

## Triage

Tier 1 question of a 2018 paper, preregistered in issue #23851 before any Lean.
`theorem`; resolution `proved`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** for every natural $n\ge1$, the supremum in $\mathbb N$ of the cardinalities of finite sets of $n\times n$ permutation matrices whose distinct members are pairwise strongly complementary equals $2^{v_2(n)}$.

**Computed, not formalized:** none.

**Argued, not formalized.**

- *Sharpness and the odd factor.* For $n=2^a m$ with $m$ positive odd, the identity gives $k(n)=2^a$, so $n/k(n)=m$. Thus the support-packing bound $k(n)\le n$ is attained exactly when $n$ is a power of two; for odd positive $n$, the maximum is one. Extra odd factors enlarge the underlying set without increasing the maximum family size.
- *Extremizers in power-of-two dimensions.* Let $n=2^a$, and let $T$ be a finite family of $n$ permutations of $\mathrm{Fin}\,n$ containing the identity and having pairwise strongly complementary matrices. By `normalized_involutions` with precisely these membership and pairwise hypotheses, its generators commute and square to the identity. Hence their generated group $G$ is abelian and satisfies $g^2=1$ for every $g\in G$: every word is a product of commuting generators, and squaring cancels the two copies of each generator. For every $x\in\mathrm{Fin}\,n$, `orbit_evaluation_bound` for this finite pairwise family gives $n=|T|\le|Gx|\le n$, so $G$ is transitive. If $g\in G$ fixes $x$, commutativity gives $g(hx)=h(gx)=hx$ for every $h\in G$, so transitivity makes $g$ the identity permutation. The action is therefore regular, $|G|=n$, and $T\subseteq G$ with equal sizes gives $T=G$. An abelian group satisfying $g^2=1$ for every $g$ is a vector space over $\mathbb F_2$ under its group law; choosing a basis and a point identifies this regular action with the full translation family on $\mathbb F_2^a$. This classification argument is not a declaration of the module. Classification of extremal families when $n$ has an odd factor greater than one remains open here.
- *Relabelling the carrier.* For any finite nonempty set $X$, choose a bijection $e:X\simeq\mathrm{Fin}\,|X|$. Transport a matrix by $P'_{ij}=P_{e^{-1}(i),e^{-1}(j)}$. The four-index and support conditions are unchanged because all indices are universally quantified, and a permutation witness transports by conjugation with $e$. This transport is invertible and preserves finite-family cardinalities, so the same maximum applies to permutation matrices indexed by $X$. This transport argument has no separate Lean declaration in the module.
- *Effect on the paper.* The Section 4 polytope discussion can use the sharp family size $2^{v_2(n)}$ in every positive dimension. Its triangle and two-face unistochasticity assertions retain their robust-Hadamard setting and their source proofs. The cardinality settlement supplies no unitary realization of interior points and does not settle the paper's robust-Hadamard or equi-entangled-basis results. The third question in its concluding list (`unisto9.tex`, lines 971–972) remains open here:

> Is the convex hull of all mutually strong complementary permutation matrices of a fixed order $n$ and the flat matrix $W_n$ unistochastic?

## ASSUMED-UNVERIFIED

The literature check is bounded and does not establish exhaustive worldwide novelty or priority. The reported v1 reading, nine citing-source screens, thesis screen, additional two-paper screens, external queries and repository-search readings in #23851 are not independently reproduced. Absence of the phrase “strongly complementary” does not exclude an equivalent result under different terminology.

The arithmetic consequences, extremizer classification and carrier-transport arguments under “Argued, not formalized” have no separate Lean declarations in this module. Extremizer classification beyond the power-of-two case and the source's unistochasticity questions remain open here. Robust-Hadamard existence, the triangle and two-face assertions, full-interior unistochasticity and the equi-entangled-basis constructions are not formalized by this settlement. The case $n=0$ is outside `claim`.
