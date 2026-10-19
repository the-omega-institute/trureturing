---
slug: das-2026-whole-cyclic-sgb-extension-refutation
bibkey: das2026sgbcyclic
doi: 10.48550/arXiv.2602.07587
url: https://arxiv.org/abs/2602.07587v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation.result
---

# The whole finite-cyclic SGB extension

## Problem

Das–Erfanian–Nath, *Certain topological indices and spectral properties of SGB-graphs of finite
cyclic groups*, arXiv:2602.07587v1, closes Section 5 with an unlabelled invitation to extend
its preceding complete list to any cyclic group. The source's ambient groups are finite.
The list was established there for orders $p^n,pq,p^2q,p^2q^2$, with distinct primes $p,q$
and $n\geq1$; those families are known source results.

For every finite cyclic group $G$, including order one, let $B(G)$ have vertex type
$(G\times G)\sqcup\operatorname{Subgroup}(G)$. All ordered and repeated pairs, the identity pair,
and all subgroups including the trivial one remain present. Cross adjacency is exactly
$\langle a,b\rangle=H$; same-part vertices are never adjacent.

The whole extension asserts the conjunction of these ten clauses:

1. The adjacency spectrum is not integral.
2. The Laplacian spectrum is integral.
3. The signless Laplacian spectrum is integral.
4. The common-neighbour spectrum is integral.
5. $E(B(G))<|V(B(G))|$.
6. $E(B(G))\leq E(K_{|V(B(G))|})$.
7. $LE(B(G))\leq LE(K_{|V(B(G))|})$.
8. $LE^+(B(G))\leq LE^+(K_{|V(B(G))|})$.
9. $E_{CN}(B(G))\leq E_{CN}(K_{|V(B(G))|})$.
10. $E(B(G))\leq LE(B(G))$.

Here $A$ is literal adjacency, $D$ is diagonal degree, $L=D-A$, $Q=D+A$, and $CN$ counts
common neighbours off the diagonal and is zero on it. Spectra are actual symmetric-matrix
spectra with algebraic multiplicity. Integral means every real eigenvalue is the real image
of an integer. Energies sum absolute eigenvalues; only $LE,LE^+$ subtract the whole graph's
$2m/N$. Each benchmark uses its respective energy of an actual same-carrier complete graph.
Thus no separate formula or indexing transport is assumed for a benchmark.

## Motivation

`SubgroupGenerating.CyclicExtensionRefutation.result` proves the negation of this entire
universal. Its counterexample is the order-one cyclic group. The failure concerns the
unrestricted finite statement, not the known source families and not a nontrivial variant.

## Gap

The prospective registration is issue [#17151](https://github.com/the-omega-institute/trureturing/issues/17151).
The source is a Tier 1 published extension question from 2026. The supplied independent
qualification checked the complete original and found no established exact prior resolution
in the bounded indexes: zero indexed citing records, 20 visible MathDB cards and 50 of 55
related-arXiv records. Five unreturned records and sign-in-only code-search contents remain
unverified. These readings establish neither worldwide absence nor publication priority.

Canonical atom lookup for the source identifier returned no matching atom. Repository public
and private declaration searches found no exact SGB supplier. The Sombor-energy refutation is
an engineering precedent for symmetric spectral calculations, not a supplier for this question.

## Route

The source graph is defined directly on arbitrary finite group carriers, so it requires no
identification with a divisors-only model or a labelled cyclic representative. For the order-one
group, an explicit equivalence carries the entire typed vertex union to `Fin 2`. Both inverse
laws are proved. Reindexing its actual adjacency matrix gives $\begin{pmatrix}0&1\\1&0\end{pmatrix}$.
Its characteristic polynomial is $(X-1)(X+1)$. The Hermitian spectral theorem identifies its
root multiset with the actual adjacency eigenvalue multiset, including both multiplicities.
Both roots are integers. Specializing the whole claim to this cyclic group contradicts clause 1.
The other nine conjuncts remain in the claim; proving their truth is unnecessary to negate it.

## Falsifier

An incorrect source domain, generated-subgroup relation, inverse law, matrix reindexing,
characteristic polynomial or spectral multiplicity would invalidate the proposed counterexample.
An extension explicitly restricted to nontrivial cyclic groups is a different statement and
is not refuted by the order-one example.

## Evidence

The canonical mathematical source is
`D5/S3/Combinatorics/Graph/SubgroupGenerating/CyclicExtensionRefutation.lean`, with its matching
Blueprint Scribe. `claim` has literal type `Prop`; `result` has literal type `Not claim`.
The source graph, matrices, spectra, integrality and energies are definitions used by that claim.
The private symmetry lemma supplies the spectrum definition; all four matrices are Hermitian.
There is only one public theorem, the designated utility refutation result.

Exact pinned Mathlib suppliers include `SimpleGraph.adjMatrix`, `SimpleGraph.degMatrix`,
`SimpleGraph.lapMatrix`, `SimpleGraph.isHermitian_adjMatrix`, `SimpleGraph.isHermitian_degMatrix`,
`SimpleGraph.isHermitian_lapMatrix`, `Matrix.IsHermitian.add`,
`Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`, `Matrix.charpoly_reindex`,
`Matrix.charpoly_fin_two`, `Matrix.det_fin_two`, `Polynomial.roots_mul`,
`Polynomial.roots_X_sub_C`, `Fintype.ofInjective`, `SetLike.coe_injective`, and
`isCyclic_of_subsingleton`. Their source pin is Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. They are applied directly.

The designated result is `proof_shape: bind-only`, `escape_witness: none`, with
`admission_basis: open-problem-resolution (#17151; Refuted)`. The private symmetry helper is
bind-only and is consumed by `graphSpectrum` and the result's characteristic-root bridge.
The designated result has the current utility-refutation author Reg exemption; no other public
theorem or lemma creates an author Reg target. No Reg certificate is asserted.

## Triage

**Kernel conclusion:** the whole unrestricted finite-cyclic universal is false, because its
first conjunct fails at the order-one group. This is one question. It does not refute the
source's established nontrivial families or identify the authors' unstated intentions.

**NONFORMAL boundary analysis:** the independently qualified scientific data reports that the
complete bundle holds for every nontrivial finite cyclic group. This is fallible same-question
boundary evidence, not an additional Lean theorem or a separate resolved problem.
Its structural parameters are $s_H$, the number of ordered pairs generating $H$,
$S=\sum_H s_H=|G|^2$, $t=|\operatorname{Subgroup}(G)|$, and $N=S+t$.
Cyclicity gives $s_H\geq1$, and the graph is the disjoint union of stars $K_{1,s_H}$.
The source's star spectra give

$$
E=2\sum_H\sqrt{s_H}\leq N,\qquad
LE=LE^+=\frac{2(S^2+t^2)}{S+t},\qquad E_{CN}=2(S-t).
$$

The center is $2S/(S+t)$ for the whole union. Since $S\geq t\geq1$, it lies in $[1,2)$.
The same analysis gives

$$
LE-N=\frac{(S-t)^2}{S+t},\qquad
2(N-1)-LE=\frac{4St-2S-2t}{S+t}\geq0,
\qquad E_{CN}\leq2(N-1)(N-2).
$$

For a prime divisor $p$ of a nontrivial cyclic group's order, its order-$p$ subgroup has
$s_H=p^2-1>1$, with $(p-1)^2<p^2-1<p^2$. Its adjacency eigenvalues are nonintegral and
$2\sqrt{s_H}<s_H+1$, giving strict hypoenergeticity. L, Q and CN star eigenvalues are integers.
These observations explain the reported nontrivial boundary while keeping its formal status
separate from the unconditional refutation.

**NONFORMAL order-one values:** the qualification reports $B(C_1)=K_2$, adjacency spectrum
$\{1,-1\}$, L and Q spectra $\{0,2\}$, CN spectrum $\{0,0\}$, average degree one, and energies
$E=LE=LE^+=2$, $E_{CN}=0$. Thus strict hypoenergeticity also fails, while all four benchmarks
are attained and $E\leq LE$ is equality. The Lean refutation uses adjacency integrality only;
these extra values are not additional formal claims.

## ASSUMED-UNVERIFIED

Worldwide prior-resolution absence, publication priority, private author intent, the nontrivial
classification as a Lean theorem, and the extra order-one energy calculations as Lean theorems
are not established here. Scribe emission, frozen binding, full admission, independent source
comparison and later delivery checks are separate obligations.
