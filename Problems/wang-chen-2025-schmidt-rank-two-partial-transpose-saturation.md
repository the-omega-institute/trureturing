---
slug: wang-chen-2025-schmidt-rank-two-partial-transpose-saturation
bibkey: wangchen2025partialtranspose
doi: 10.1142/S1230161226500071
url: https://arxiv.org/abs/2508.18644v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Classification.result
---

# Schmidt-rank-two partial-transpose saturation

## Problem

N. Wang, L. Chen, *Equality condition for a matrix inequality by partial
transpose*, arXiv:2508.18644v1, Section VI, ask:

> An open problem arising from this paper is to find out the condition saturating the inequality for Schmidt-rank-two matrices with any dimensions.

Theorem 6 states
rank(sum Rj transpose tensor Sj) <= K rank(sum Rj tensor Sj).
For two linearly independent complex rectangular coefficient pairs A and
B, put X=A1 tensor B1+A2 tensor B2 and transpose the A factors to obtain
XGamma. Let h and v be the horizontal and vertical concatenation ranks.
The complete target is

$$
\operatorname{rank}X^\Gamma=2\operatorname{rank}X
\quad\Longleftrightarrow\quad
(v_A=2h_A\land v_B=2h_B)\ \lor\
(h_A=2v_A\land h_B=2v_B).
$$

## Motivation

The criterion is intrinsic to the coefficient pairs, uses only four
ordinary matrix ranks, and includes every finite rectangular dimension.
Independence of both pairs expresses Schmidt rank exactly two. Empty or
zero-dimensional factors are allowed in the sufficient direction.

## Gap

Issue #30687 supplies the preregistration, exact quotation and target.
The sufficient direction alone does not settle the question. The
converse needs a complete simultaneous decomposition of an arbitrary
matrix pair, followed by an exact defect calculation on every pair of
summands. A hypothesis asserting the desired decomposition would not
discharge this gap.

## Route

The sufficient direction uses independent output control directly.
If v(B)=2h(B), the map x to (B1 x,B2 x) surjects onto H(B) squared,
where H(B)=image B1+image B2. Pure tensor preimages then show
image X=H(A) tensor H(B). Consequently rank X=h(A)h(B), while
rank XGamma=v(A)h(B). Transposition gives the other orientation.

For the converse the proof selects a shortest polynomial
kernel chain. A separating functional for the image of its boundary
map gives dual chain coordinates; the resulting simultaneous projectors
split off a right singular summand. Applying the construction to the
dual pair gives left summands. The remaining square regular pair is
equivalent to its transpose. Reversing actual Jordan chains constructs
the required nondegenerate pairing.

For positive singular indices r,s, equal orientations have ranks rs and
rs+min(r,s); opposite orientations have these ranks in reverse order.
Zero defect forces r=s=1 and agreement of orientations across all
nonzero summands. The finite recursive expansion uses the actual commuting projections,
so these local formulas add for both tensor ranks and both concatenation
ranks. Equality of the sum of nonnegative defects forces equality for
every summand. A nonzero regular leaf would have positive tensor rank
against the independent other coefficient pair, which contradicts
saturation. The remaining positive singular indices are one with a
common orientation.

## Falsifier

The terminal theorem quantifies over all four natural dimensions using
finite natural index types, and assumes only independence of each
coefficient pair. It must
use ordinary complex matrix rank and the literal first-factor partial
transpose. It must prove both implications of the displayed criterion,
without assuming a normal form, a decomposition certificate, the rank
inequality, or the classification itself. No additional dimension or
regularity hypothesis is part of the target.

## Evidence

The terminal Lean theorem is
`D5.S3.Quantum.Entanglement.PartialTransposeSaturation.result`, in
`D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Classification.lean`.
It proves the full displayed equivalence, with no decomposition,
regularity or rank-bound premise. The scoped compilation exited zero;
its report digest is
`4be001e595e8d1b44159fff37b87ae1f54bb7e382ef5ad9fd2bea5166076e5a5`.
The theorem statement identity is
`sha256:1e7d93b77d2b00324381ebd60b3101bae934284779264f027106ef2a6e32fd4e`.
Every declaration in that scope uses only `Classical.choice`,
`Quot.sound` and `propext`. The sufficient direction also includes
empty dimensions and dependent coefficient pairs.

The joint scoped verification of the mathematical endpoint and its registration
sources exited zero (67 modules, 3578 declarations), with digest
`4fed6c3389f52fb8a69cdcc2a0841f753d2897f8c939cbe492e1286a01d8a39f`.
The terminal result has a validated source-equivalence registration.
Of 37 registration attempts, 32 are `declared_validated`; five chain-splitting
registrations remain `declared_unresolved` under `source.coordinate_dependency`,
`source.absent_occurrence`, or `source.params`. The constructive theorem
`two_sided_reduction` has no faithful observation template for its opaque
inductive conclusion. These auxiliary gaps are associated with issue #30687;
they are not missing mathematical premises or proofs. The outer delta command
could not consume the scoped report: it requires the full-report schema.

## Triage

The proof mechanism is matrix-pair decomposition, preservation
of rank by the regular part, and strictly positive defect for all
nonstandard singular blocks. The constructive splitting is an internal
proof step; classical Kronecker matrix-pencil theory is its precedent.
Extensions to Schmidt rank K at least three and a complete
classification of rank(X)=rank(XGamma) are outside the conclusion.

## ASSUMED-UNVERIFIED

The supplied bibliographic data, source quotation and issue description
have not been retrieved from the network in this task. The six-step
paper proof was read and independently checked; the formal proof then
constructs its own finite block expansion rather than assuming the
classical normal form. No exhaustive priority search is claimed.
