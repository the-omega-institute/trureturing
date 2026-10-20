---
slug: coulter-do-2025-conjecture-5-8
bibkey: coulter2025weingarten
doi: 10.48550/arXiv.2506.04002
url: https://arxiv.org/abs/2506.04002v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Combinatorics/DeformedJucysMurphyNoncommutation.J
---

# Coulter–Do Conjecture 5.8

## Problem

Xavier Coulter and Norman Do, arXiv:2506.04002v1, Conjecture 5.8
(`con:b-laplace`, original TeX lines 2144–2149):

> For all $\lambda \vdash k$,
> $\mathrm{ch}^{(b)}((\mathcal J_1+\cdots+\mathcal J_k)\cdot\mathbf p_\lambda)
> =D(b)\cdot\mathrm{ch}^{(b)}(\mathbf p_\lambda)$.

The original source uses the macros `\J` and `\p` for the two symbols above.
Here every positive integer k and every partition lambda of k is in scope,
the scalar field is C(b), and b is an indeterminate. The class vector has
coefficient one at precisely the matchings of coset type lambda. Membership
of the operator image in the class-constant space is part of the assertion,
since the characteristic map has that space as its domain. Explicitly,
one coefficient function c on all partitions of k must satisfy both

1. `S_X(indicator lambda)(p) = c(ct(p))` for every actual matching p;
2. `sum_mu (c(mu)/A_mu) p_mu = D_X((A_lambda)^(-1) p_lambda)`.

The normalization is literally
`A_mu=(1+b)^(number of parts of mu) product_r r^(m_r(mu)) m_r(mu)!`.
The differential operator acts on C(b)[p_1,p_2,...], with all positive
derivative indices and the original ordered cut and join sums.

## Motivation

The sum of the original deformed Jucys–Murphy operators is defined without
any commutation assumption. Its identification with the Laplace–Beltrami
operator can survive the failure of Conjecture 5.4(a). The frozen `J`
definition is reused; its old noncommutation settlement does not settle 5.8.

## Gap

[Issue #17676](https://github.com/the-omega-institute/trureturing/issues/17676)
preregistered this exact full assertion, tier 1, and the
`open-problem-resolution` basis before a probe or Lean implementation.
The issue records the original k<=5 checks and the already implied
lambda=(1^k) family, neither of which is claimed as new progress here.
Its dated literature screen is retained in the corresponding Library note.
No exhaustive or newly refreshed priority search is claimed.

## Route

The candidate uses the original partner maps, actual transposition action
and output-matching charges. Alternating-walk coverage establishes the
maximum-anchored charge rule. Complete edge components include doubled
edges. Counted cuts and joins give `Row.native_row` and `Row.native_C1`.
The literal infinite-variable differential operator yields an occurrence
coefficient equal to that same `Row.rowCoefficient`. The diagonal pairing
proves balance with the exact normalization, giving
`Occurrence.same_coefficient_C2`. Finally `Occurrence.conjecture58` chooses
that one coefficient function; actual matching realization for every
partition proves uniqueness. No commutation or Jack-eigenbasis hypothesis
occurs. Complete singleton-inclusive coset type and the live orbit-to-edge
coordinates remain. The full rotation-orbit multiset is a consequence of
the reused frozen two-orbit split, recorded in the Components narrative.

## Falsifier

The interpretation would fail if the native row used input charges instead
of output charges, omitted singleton components, restricted k or partition
shape, replaced the native action by a proxy, changed the normalization,
truncated the derivative operator without a support argument, or used
different coefficients in C1 and C2. The completed bounded source assessment
found none of those failures. That assessment is evidence for independent
review, not a replacement for admission or native validation.

## Evidence

The sole proposed resolution-claim host is
`D5/S3/Combinatorics/PerfectMatchings/DeformedJucysMurphyOccurrence.conjecture58`.
Its existing statement asserts a unique common coefficient for every k>=1
and every partition. The prepared Scribe claim uses `ResolutionKind.Proved`
on that declaration without a new theorem or wrapper. The inherited reports
identify its statement as
`sha256:18b51862c7c66c2fff8550fa0874cb7030245fe52c0233095397487c53af9350`
and its type as
`sha256:b900be3b075ebd53386c4f4b1b82a3e44914572ed267ba00ff45b140d5e2225f`.
These stable statement identities refer to the existing theorem, whose full
source span is preserved. Current report and emission status is stated below;
historical reports do not certify edited source bytes.

## Triage

`theorem`: the full original-domain candidate is prepared under
`admission_basis: open-problem-resolution`, preregistration #17676.
This is not a statement that freeze, deposit, final review, CI or merge
has occurred. Only the final existing gates can establish those events.

- Candidate theorem: the original C1 and normalized C2 share one coefficient,
  with actual matching realization. The complete source assessment supports
  its fidelity within its stated bounded scope.
- Reused structural consequence: the product-rotation orbit multiset is twice
  the complete coset-type multiset, including fixed orbits of size one.
  Frozen `InvolutionOrbitSplit.component_split` and `component_orbit_classes`
  give the two nonempty sheets, exchanged by the identity matching. Each
  sheet has one endpoint of each identity edge, so a component with r edges
  gives two full orbits of size r. This is readable source correspondence
  rather than a separately delivered new endpoint.
- Mathematical interpretation: this argument uses the sum alone, and does
  not restore pairwise commutation or an order-independent evaluation of
  general symmetric polynomials in the individual operators.
- Open: further ordered consequences concerning Conjecture 5.7(b) and a
  simultaneous eigenbasis. They are not resolved problems in this claim.

### Scoped source and reader assessment (2026-10-19)

The live surface retains the original all-positive-k/all-partition result,
the same coefficient in C1 and C2, the actual infinite polynomial operator,
the exact normalization and every-partition matching realization. Four
unconsumed, unfrozen public companions were retired together with their
proved orphan helper closure: 22 theorems (10 public, 12 private) and one
private coordinate equivalence. Their complete old proofs remain in the
immutable pre-repair candidate archive. No new consumer or theorem alias was
introduced. The six required full source spans remain byte-identical.

The mixed-weight finite derivative formula and positive-part z-product remain
mathematical source correspondences. Positive weighted degree bounds the
nonzero derivative indices of each monomial; linearity handles the finite
monomial support. Variable i represents p_(i+1), and its exponent is exactly
the multiplicity of part i+1. Reindexing the finite product gives the original
part powers and factorials. Native detailed balance follows by the existing
literal coefficient equality and algebraic balance; C2 uses the normalized
algebraic expansion directly. These facts need no standalone wrapper.

Affected D5 and Reg scoped reports completed on 2026-10-19 against
the reviewed reduced source before the canonical header corrections, with
native exit 0, direct wait return 0 and separate
native stdout/stderr EOF receipts. The D5 report contains 13 modules and 633
declaration rows; its SHA256 is
`62c7b49d41125d2de0c75589472ef3daa1f20391ab0650d156441c46270737c8`.
The Reg report contains 53 modules and 2249 declaration rows; its SHA256 is
`2a03258af20bf9014746875d065b486f057bc87a50d4fcfdf91dcacaeb76ac4a`.
Every included declaration has only standard axioms. All six protected
statement/type identities are unchanged. These counts include generated
and dependency declarations; the nine candidate D5 source files contain
167 explicit theorems, of which 78 are public and 89 private.

The scoped Scribe reader consumed all seven sources successfully (native
exit 0, direct wait return 0 and both native EOF receipts). Four affected
pages changed; the other three remained current. Exactly one typed claim
remains on the existing `Occurrence.conjecture58`. Successful scoped
emission establishes the reader bindings at that source revision. This
scoped assessment did not settle frozen-host claim validation or canonical
delivery gates. Historical evidence remains bound to its original bytes;
subsequent canonical receipts govern admission, freezing, full reports and
gates without extending these scoped receipts to changed source hashes.

The Row header anchors the reachable Mathlib Finpartition module. The Walk
and Charge headers anchor Mathlib.GroupTheory.Perm.Cycle.Basic, reached through
their existing InvolutionOrbitSplit import closure and used for their
rotation-orbit and SameCycle arguments. The Walk and Charge helpers point to
the existing Row Blueprint, which explains the alternating walk, component
maximum and output charges. These header corrections change no proof, type
or mathematical source body.

## ASSUMED-UNVERIFIED

The literature screen is dated 2026-10-16 and is not exhaustive. Two Reg
records remain `declared_unresolved`, with null certificates; 76 of the current
78 public theorem addresses remain unassessed, and none is declared validated.
Before this correction the surface was 2 unresolved plus 86 unassessed; the
original history was 2 plus 93. Retirement changes the live surface, not the
historical audit outcomes. The retained Reg mirrors and existing #17676
linked-issue disclosure do not certify those audits. The all-78-target disclosure
is https://github.com/the-omega-institute/trureturing/issues/17676#issuecomment-6258362749.
Its source hashes identify the reviewed pre-header-correction revision; the
canonical delivery records map the three header-only hash changes while
preserving all target names, owners, theorem bodies and audit statuses.
Canonical receipts must independently establish claim-host freezing, exact
frozen-host claim validation, deposit, the current full raw report and full
gates. This dossier does not substitute for them. Independent final review,
exact-head CI, merge and first-dev validation remain required.
