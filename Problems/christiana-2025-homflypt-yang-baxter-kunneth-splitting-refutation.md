---
slug: christiana-2025-homflypt-yang-baxter-kunneth-splitting-refutation
bibkey: christiana2025homflypt
doi: null
url: https://arxiv.org/abs/2502.20659v1
triage: theorem
motivation_gids:
  - D5/S3/HomologicalAlgebra/HomflyptYangBaxterKunnethSplittingRefutation.result
---

# The HOMFLYPT Yang–Baxter Künneth subcomplex need not split

## Problem

Christiana, Clingenpeel, Guo, Oh, Przytycki, Wang and Yun,
*Low Dimensional Homology of the Yang-Baxter Operators Yielding the HOMFLYPT Polynomial*,
arXiv:2502.20659v1, §5.1, Conjecture 5.6:

> The short exact sequence of chain complexes
> $0 \to C_\bullet^{(m,A,B)} \to C_\bullet^m \to C_n^m/C_\bullet^{(m,A,B)} \to 0,$
> splits. Thus homology $H_n(C_\bullet^m)$ splits.

Definition 5.4 includes every cutoff from zero to the word length. The
hypotheses are $A\cup B=X_{(m)}$ and every letter of $A$ at least every
letter of $B$. Splitting means a chain-map retraction of the inclusion.

## Motivation

The frozen result named above refutes this universal splitting assertion
with the strictly ordered, disjoint two-letter decomposition $A=\{2\}$,
$B=\{1\}$. A degreewise module splitting alone does not supply the
homology consequence asserted in the conjecture.

## Gap

Issue #11622 preregisters the exact statement, witness and literature
screen before Lean implementation. Its screen covers the source and
arXiv:2607.28626 and 2505.03465; no settlement is identified in that scope.
The source TeX retains the displayed splitting conjecture. Repository and
pinned-Mathlib searches identify no HOMFLYPT chain-retraction refutation;
generic braided-category Yang–Baxter identities do not settle it.

## Route

Use the paper's normalized operator over $\mathbb Z[t]$, with $t=y^2$,
and both traveller face maps with deletion at the respective wall. The
boundary uses the paper's one-based alternating signs. The block submodule
is the existing Finsupp.supported constructor on the Definition 5.4 words;
Finsupp.supported_eq_span_single identifies its basis-vector span.

For $m=2$, every degree-five block generator $2^i1^{5-i}$ has zero boundary.
The chain

$$c=t(t+1)11112+(t^3+t^2+t+1)11121+t11212-t12112+t^3 12211+t^2 12221$$

has boundary $q(2221-2111)$ with $q=t^3(t^2-1)$. This is a nonzero
member of the degree-four block submodule. Retraction fixes this boundary,
while the chain-map equation makes it zero, a contradiction.

## Falsifier

A different crossing convention, coefficient specialization, or omission
of a permitted cutoff would change the source statement. Here the
witness boundary uses the interior cutoffs three and one, while the
vanishing argument includes every degree-five cutoff. The coefficient
of $t^5$ in $q=t^5-t^3$ is one in Polynomial ℤ.

## Evidence

The module proves result : ¬ claim with a kernel-checked proof. Its local
facts hd, hu, hv, he, hqe, hz, hfixed and hcoeff establish the boundary,
block membership, degree-five vanishing and the contradiction. There are
no separately exported companion theorems and no native_decide.

## Triage

Tier 1: an explicitly stated conjecture in a published arXiv paper,
preregistered in #11622. Admission basis: open-problem-resolution
(#11622; Refuted). Judgement form: bind-only; the proof consists of finite
boundary normalization and the linear-retraction contradiction. Utility:
certified-instance, refutes the module's claim.

### What the settlement shows

**Proved in this module:** the ordered two-letter subcomplex has no chain
retraction. The obstruction is a nonzero ambient boundary inside the
block submodule, whereas the degree-five block differential is zero. The
witness uses a strict, disjoint decomposition, so imposing either of
those additional conditions does not restore the universal conjecture.

**Proved in this module:** in this witness, the entire degree-five block
submodule has zero boundary; both degree-four words in the obstruction
belong to the block submodule. These are the finite-degree facts needed
for the contradiction, without a homology calculation in other degrees.

**Open here:** a classification of ordered decompositions admitting chain
retractions, arbitrary-degree block vanishing, coefficient-specialized
splittings, and the neighbouring splitting assertions after Conjecture
5.6. The present argument does not refute Proposition 5.5 or determine all
abstract homology-group decompositions. Any deduction requiring the
universal chain splitting of Conjecture 5.6 lacks that premise; the
paper's other computations and splitting results require their own
hypotheses and are not adjudicated here.

## ASSUMED-UNVERIFIED

The preregistration's literature screen is bounded. Journal acceptance
and a complete citation census are unverified here; no global priority
claim follows from the screen. Identification with the paper depends on
the displayed source-clause correspondence and face convention; the
Lean kernel verifies the encoded statement, not that correspondence.
