---
slug: laneve-2024-qsp-collapse-conjecture-refutation
bibkey: laneve2024multivariateqsp
doi: 10.22331/q-2025-02-20-1641
url: https://arxiv.org/abs/2407.20823v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.result
---

# A three-level QSP segment that collapses without a common monomial factor

## Problem

L. Laneve and S. Wolf, *On multivariate polynomials achievable with quantum signal processing*,
arXiv:2407.20823v2 (Quantum 9, 1641 (2025)), Conjecture 8: if a Protocol C segment
$A_m\tilde W\cdots A_1\tilde W$ ($\tilde W=\operatorname{diag}(1,a,b)$, $A_k\in SU(3)$) maps a polynomial
state of effective dimension $\le2$ to one of effective dimension $\le2$ while every intermediate
state has effective dimension $>2$, then the segment acts as $a^kb^h\cdot U$ on some pair of
subspaces $H\to H'$ of dimension $d\ge2$. The verbatim statements are in
[the literature note](../Library/QuantumBounds/laneve2024multivariateqsp.md).

Issue [#14369](https://github.com/the-omega-institute/trureturing/issues/14369) reads the
conclusion permissively — any linear isometry $U:H\to H'$ and any $k,h\in\mathbb N$ — so that its
refutation covers the printed form.

## Motivation

The paper states that Conjecture 8 is the final step it could not prove towards Conjecture 7:
two-dimensional outputs of three-level multivariate QSP would then be reachable by two-level QSP,
since a segment acting as $a^kb^h\cdot U$ can be replaced by one that never leaves two dimensions.

## Gap

The authors' own example $(1,a,b)\mapsto(1,ab,ab)$ acts as $ab\cdot\mathrm{id}$ on a two-dimensional
subspace and fits the conjecture. Issue #14369 records the literature check before any Lean: no later
work settles Conjecture 7 or 8; `not-found-in-searched-scope`.

## Route

$m=2$, $A_1$ and $A_2$ the two cyclic permutations of the basis, $\gamma'=(3,4,12a)/13$:
$\gamma_1=(12ab,3,4a)/13$ has effective dimension 3, $\gamma=(3a,4ab,12ab)/13$ and $\gamma'$ have
effective dimension 2, and the segment is $T=\operatorname{diag}(a,ab,b)$. At $(a,b)=(1,1)$ the
conclusion forces $U=\mathrm{id}_H$; at $(i,-1)$ it forces $\operatorname{diag}(i,-i,-1)$ to act as a scalar
on $H$, so $\dim H\le1$.

## Falsifier

The refutation concerns Conjecture 8 as printed. It does not address Conjecture 7: the output
$(3a,4ab,12ab)/13$ may still be reachable by two-level QSP through another protocol.

## Evidence

The canonical source is `D5/S3/Quantum/Algebra/MultivariateQSPCollapseRefutation.lean`, with public
`claim` and `result : ¬ claim`. The axiom closure of `result` is exactly `propext`,
`Classical.choice` and `Quot.sound`; there is no `sorry`, `native_decide` or new axiom.
The module statement is `sha256:f574441ecafeed6f2e6064857346f2f8fa2b72c36188667de8c4912e447486f0`,
the `result` statement `sha256:3857e9bd93ab7e36a288e7abb485c451cee11d2c9849049ca152f850a3884479` and the
`claim` statement `sha256:0eeede7668a3b4ba3318959d58b6a966d1b6ec3e60cabca39ccd8118b34e4aef`. The Freeze
event is `sha256:0ce5bfcc61680c92b2df8857ed877dc5b26002c791d828920c20f969e8fc760a`; it has no
project-level prerequisite (the module imports Mathlib only).

## Triage

Tier 1 auxiliary conjecture of a 2024 paper (kept in the Quantum version), preregistered in issue
#14369 before any Lean. `theorem`; resolution `refuted`.

| declaration | proof_shape | escape_witness | admission_basis |
| --- | --- | --- | --- |
| result | content | scalar_subspace_dimension | open-problem-resolution |

The private theorem `scalar_subspace_dimension` carries the content: a diagonal matrix with pairwise
distinct entries acts as a scalar only on subspaces of dimension at most one. It is not a Mathlib
statement and lies on the live proof of `result`. The remaining private theorems (`coefficient_span`,
`initial_normalized`, `stages`, `transfer_diagonal`, `initial_dimension`, `middle_dimension`,
`final_dimension`, `distinct_diagonal`) are bind-only instantiations and normalizations, each used on
the proof of `result`. The settlement is
admitted as an external open-problem resolution.

Utility is `kind=certified-instance; basis=refutes` (the claim and its refutation). There is no
digestion atom.

### What the refutation shows

**Proved by `result`:** Conjecture 8 fails for a two-step segment whose processing operators are
permutation matrices.

**Argued, not formalized.**

- *Mechanism.* The output returns to effective dimension 2 because two output coordinates acquire
  the same monomial $ab$ from different sources: one from the operator factor $ab$ acting on the
  constant coefficient, the other from the operator factor $b$ acting on the coefficient that
  already carries $a$. A collision of monomials in the state does not require a common monomial
  factor of the operator on any fixed subspace, which is the step the conjecture assumes.
- *Conjecture 7.* The output is $\gamma=a\cdot(3,4b,12b)/13$; the example shows only that this
  segment does not have the structure Conjecture 8 asserts, not that $\gamma$ is unreachable by
  two-level QSP. It removes the proposed route to Conjecture 7 without refuting Conjecture 7.

**Open.** Conjecture 7 is not determined here, nor is Conjecture 8 restricted to segments whose
input state does not depend on $a,b$ (the setting of the authors' own example).

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty, priority, or
the absence of an independent proof.
