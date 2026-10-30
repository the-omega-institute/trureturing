---
slug: hemmer-straub-westrem-2025-weighted-ev-character-average
bibkey: hemmerstraubwestrem2025riordan
doi: 10.37236/14401
url: https://arxiv.org/abs/2509.02796v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.result
---

# The Hemmer–Straub–Westrem weighted Ev character average

## Problem

Hemmer, Straub and Westrem, *New identities in the character table of symmetric groups involving Riordan numbers*, arXiv:2509.02796v1, Conjecture 6.1, equation (6.1), PDF page 12, asks whether, for every integer $n\geq1$,

$$
\sum_{\lambda\vdash n}\frac{L_\lambda}{z_\lambda}
=\sum_{\lambda\vdash n}\frac{R_\lambda}{z_\lambda}
=\begin{cases}
\displaystyle\binom{n/2+2}{2},&n\text{ even},\\
0,&n\text{ odd},
\end{cases}
$$

where the outer sums range over all partitions of $n$ and

$$
\begin{aligned}
z_\lambda&=\prod_{j=1}^{n}j^{m_j}m_j!,
&m_j&=\#\{i:\lambda_i=j\},\\
L_\lambda&=\sum_{\rho\in\operatorname{Ev}(\lambda)}
  \sum_{\mu\in\mathcal R_3(2n)}(-1)^{\ell(\rho)}\chi^\mu_\rho,
&R_\lambda&=\sum_{\rho\in\operatorname{Ev}(\lambda)}\chi^{(n,n)}_\rho.
\end{aligned}
$$

Each occurrence of a positive part $a$ independently contributes either $(2a)$ or $(a,a)$ to $\operatorname{Ev}(\lambda)$; reordering produces cycle partitions, and coincident outcomes retain multiplicity. The set $\mathcal R_3(2n)$ consists of partitions of $2n$ with at most three rows, every row even. The symbol $\chi^\mu_\rho$ means the ordinary complex irreducible character of the symmetric group on $2n$ letters, labeled by $\mu$, evaluated at cycle type $\rho$. The journal version retains the assertion as Conjecture 17, equation (6.1). Preregistration: [#21960](https://github.com/the-omega-institute/trureturing/issues/21960).

## Motivation

The frozen `D5/S3/Combinatorics/Partitions/HemmerStraubWestrem.result` supplies the pointwise equality in its Frobenius coefficient model. The source's weighted question additionally asks for the explicit value of the common average at every positive size. The existing `D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyC2.zPartition` supplies the multiplicity product defining $z_\lambda$; no second centralizer factor is needed.

## Gap

The source event requires ordinary irreducible characters. The existing `frobChar` is defined as a coefficient of a Vandermonde times a product of power sums. Its identification with the ordinary character is explicitly outside the frozen sibling theorem. The source's Lemma 3.1 and Stanley's Corollary 7.17.4 attest the classical identification, but a citation is not a Lean proof of that identification.

The missing formal interface must supply the partition-labeled ordinary irreducible representation of $\Sigma_m$ and prove that its trace character at every permutation with full cycle partition $\rho$ equals the complex cast of `frobChar` for the padded row triple. Here $m=2n$, the shape is either a member of $\mathcal R_3(2n)$ or $(n,n)$, and the cycle partition ranges over every occurrence of `evTypes lam.parts.toList`. The bridge must include fixed points in the full cycle partition, agree with the source's partition labeling, and apply uniformly in $n$. Pinned Mathlib provides `Representation.character`, conjugacy invariance and irreducible-character orthogonality; no matching partition-indexed family or Frobenius bridge was found in the repository and pinned-library searches described in Evidence.

Independently, no Lean proof of the universal weighted closed-form evaluation is supplied. Proving that evaluation only for `frobChar` would leave the ordinary-character bridge unresolved; treating the bridge as a hypothesis would give a conditional statement rather than settle this problem.

## Route

The intended dependency order is the ordinary-character bridge, the existing pointwise and rectangular coefficient identities, the weighted partition aggregation, and exact coefficient extraction. The private `ev_right`, `right_coefficient` and `triProd` belong to the original sibling owner; any needed reuse must expose those declarations there rather than reprove them under new names.

For a partition with $r$ parts, the sibling's polynomial reduction gives the coefficient expression

$$
2^r\left([X^n]-[X^{n+1}]\right)
\prod_{a\in\lambda}(1+X^a+X^{2a}).
$$

The preregistered aggregation route asks for a coefficientwise proof, over $\mathbb Q[z,z^{-1}][[t]]$, of

$$
\sum_{n\geq0}t^n\sum_{\lambda\vdash n}
\frac{2^{\ell(\lambda)}}{z_\lambda}
\prod_{a\in\lambda}(z^a+1+z^{-a})
=\frac{1}{(1-t)^2(1-tz)^2(1-t/z)^2},
$$

followed by extraction of $\operatorname{CT}_z(1-z)$ times this series, with proposed result $(1-t^2)^{-3}$. Its coefficient at degree $n$ must then be proved to equal the even/odd formula in Problem. The $n=0$ term is bookkeeping for this route; it does not change the source's quantifier $n\geq1$. These series steps are proof obligations, not a replacement for the published character event or a claimed Lean result.

## Falsifier

A positive integer $n$ at which either ordinary-character weighted sum differs from the displayed value refutes the source assertion. A finite range of agreement does not prove it. Failure to construct the ordinary-character bridge is a formalization obstruction, not a counterexample to the classical Frobenius formula or to this conjecture.

## Evidence

A current transient Lean `example` checks the first weighted equality for every natural $n\geq1$, using the exact existing `zPartition` reciprocal in $\mathbb Q$, all `Nat.Partition n`, all occurrences of `evTypes`, the existing `R3`, and the existing integer `frobChar` values cast to $\mathbb Q$. Its proof applies `Finset.sum_congr` and rewrites each summand using the frozen `result`; it does not check the closed form or an ordinary-character statement. The transient check adds no retained mathematical declaration.

The same compiler invocation checks positivity of `zPartition` by the original `zExponent_pos` and prints the axiom closures of the reused `result`, `zPartition` and `zExponent_pos`. Each closure is contained in `{propext, Classical.choice, Quot.sound}`. These closure checks do not discharge the missing character interpretation.

Repository searches include public and private declarations for `Specht`, `specht`, the Frobenius character formula and irreducible-character names. Searches across pinned Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` include `Specht`, `Young` symmetrizers, `Frobenius` with `character` or `Schur`, `Schur` functions, and `Murnaghan`; inspection of `RepresentationTheory/Character.lean` confirms the generic trace-character API. No usable partition-indexed ordinary-character bridge was found in that scope. This is a bounded search result, not a proof that no external Lean implementation exists.

The finite experiments and literature screen in #21960 are prior evidence reported by their authors; they were not rerun here and do not establish universal Lean evidence.

## Triage

This is the preregistered external named open-problem route, with potential admission basis `open-problem-resolution` only upon a complete source-faithful proof. The compiled first equality is bind-only reuse and supplies no new escape witness or standalone retained theorem. The weighted closed form and ordinary-character bridge remain unresolved. No new public D5 theorem, Scribe resolution claim, freeze, or completed escape registration is asserted. The sibling's unfinished audit [#18551](https://github.com/the-omega-institute/trureturing/issues/18551) remains separate.

The next mathematical interface question is whether an admissible partition-indexed ordinary symmetric-group representation family and its exact Frobenius coefficient formula can be supplied in Lean. A proof of the generating-series evaluation alone cannot answer that question.

## ASSUMED-UNVERIFIED

Literature completeness remains `ASSUMED-UNVERIFIED` with the scope and inaccessible sources disclosed in #21960. The classical representation-theoretic identification is cited literature and has no compiled bridge here. The weighted generating-series calculation and its universal coefficient extraction have not been compiled. No resolution of Conjecture 6.1 or its negation is claimed.
