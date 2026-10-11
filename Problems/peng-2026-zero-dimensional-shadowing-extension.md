---
slug: peng-2026-zero-dimensional-shadowing-extension
bibkey: peng2026shadowing
doi: null
url: https://arxiv.org/abs/2606.14435v3
triage: wall
motivation_gids:
  - D5/S1/Dynamics/Shadowing/MittagLefflerInverseLimit.shadowing_inverse_limit_of_mittag_leffler
---

# Zero-dimensional shadowing extensions

## Problem

Peng's Question 5.1 asks whether every compact Hausdorff shadowing system
(X,f) is a continuous onto equivariant factor of a compact zero-dimensional
shadowing system (Y,g). Time is natural, including zero. Neither f nor g is
assumed invertible or onto; no metrizability or countable-weight condition
is imposed. Empty X has the solution Y empty. The general nonempty question
is unresolved here.

## Motivation

The reusable background bridge is preservation of finite-cover shadowing
by an arbitrary-directed compact Hausdorff Mittag-Leffler inverse limit.
It does not choose the symbolic stages or provide their bonding maps.

## Gap

A sufficient symbolic construction still requires all of the following:

1. Finite graphs at every finite observation scope, with edge-preserving
   deletion maps satisfying identities and every composition exactly.
2. Complete-path lifting for every target infinite path and every finite
   prefix, or genuinely proved ML stabilization of complete-path images.
   Vertex or edge surjectivity alone is insufficient.
3. Nonempty closed decoding cells, nested under every deletion, refining
   every finite open cover of X at some stage.
4. Actual graph-of-f witnesses for every stage edge, or a proved buffered
   closed-graph replacement implying sound limit decoding.
5. Complete coding of each actual orbit of each x in X at every stage.

Separate face lifts need not share one tracing orbit, and independently
constructed refinements need not commute around deletion squares. A
one-face refinement therefore does not settle the all-face construction.
A join-tree gluing theorem also requires its actual running-intersection
hypotheses and cannot be applied to cyclic proper-face scopes.

## Source feasibility criterion

For a once-fixed finite-face stage, suppose the vertical source relations
R_G are closed and symmetric. For a column v define its closed source cell
C(v) as the intersection of all constraints (v^G,x) in R_G. For a live finite
word w=v_0...v_m, meaning a prefix of an entire old stage path, define

$$
K(w)=\bigcap_{i=0}^{m}f^{-i}C(v_i).
$$

Every old whole array has one common constrained source orbit if and only
if K(w) is nonempty for every live finite word. The reverse implication
uses nested compact source sets for the same prescribed whole array. The
maximal source-array incidence is then compact and forward invariant; its
projection onto the entire stage is exactly this common-orbit condition.
These are ordinary mathematical reductions, not additional Lean theorems.

Arbitrarily fine proper-superface lifts of the same frozen old array force
this condition: shadow each lifted top row and take one compact subnet of
the source tracing points. Closedness preserves every old constraint in
the limit. For infinite coordinate indexing, monotone cofinal controls
provide the required proper-superface tail. Open relations give only their
closures under this argument, so closing a relation changes the target and
requires a separate construction choice.

The remaining existence obligation is to choose the controls and finite
alphabets globally, before any context or word is supplied, so that every
stage's live finite word has nonempty K(w). Source compactness does not
supply these finite feasibility facts. A failed word blocks every
sufficiently fine whole lift of arrays having that prefix, but does not
refute the existential question for other global choices.

A proposed finite visible/hidden graph can be checked against its entire
old path target using reachable hidden subsets. With N live visible and M
live hidden vertices, failure has a live prefix of length at most
N 2^M+1. This checks a fixed candidate; it does not prove a successful
candidate exists. Closed multivalued source itinerary images need not be
sofic even when the source has shadowing, so exact source-image pruning
cannot be assumed to terminate in a finite graph.

## Route

If this coherent family is constructed, compactness supplies its inverse
limit and the same-orbit coding fibers. Nested arbitrarily small cells give
unique decoding, edge soundness gives equivariance, the closed graph gives
continuity, and same-orbit fibers give surjectivity. The inverse-limit
shadowing theorem then supplies shadowing of Y. None of the missing
construction clauses is supplied by treating it as a hypothesis and calling
the original question solved.

## Falsifier

A coherent all-face construction would answer the question positively. A
scheme-specific lifting failure does not answer it negatively; a negative
answer requires a compact Hausdorff shadowing system admitting no such
extension by any construction.

## Evidence

The inspected primary source is Peng arXiv:2606.14435v3, Question 5.1 on
printed p.21. The independent source capsule also verifies the exact
Mittag-Leffler quantifiers of Definition 1.10. The self-contained inverse-limit
proof is in the cited Lean module; it does not assume that eventual-image
restrictions inherit shadowing.

## Triage

This is an unresolved construction question outside the metric case. The
Mittag-Leffler shadowing bridge is known-background infrastructure, not an
original question settlement.

## ASSUMED-UNVERIFIED

No worldwide open-status conclusion is inferred from a bounded search. The
final Good–Meddaugh journal Theorem 8, pp.722-723, supplies the attributed
Mittag-Leffler preservation result, including nonsurjective bonds. Its Lean
formalization and subsequent freezing are separate from the still missing
coherent symbolic construction in this problem dossier.
