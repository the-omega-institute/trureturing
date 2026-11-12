---
slug: delgado-suer-yesil-2026-symmetrization-surjectivity
bibkey: delgadosueryesil2026symmetrization
doi: null
url: https://arxiv.org/abs/2611.14268v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Partitions/FerrersRowCoordinates
---

# Surjectivity of original-row symmetrization

## Problem

Delgado, Suer and Yesil, *A Symmetrization for Almost Symmetric Numerical
Semigroups*, arXiv:2611.14268v1, Section 5, ask:

> A natural question is whether Φ is surjective, that is, whether every symmetric numerical set arises as the symmetrization of some almost symmetric numerical semigroup.

Section 2 works with proper numerical sets: cofinite subsets of the
nonnegative integers containing zero and different from the whole set.
Write G(U) for the complete nonempty finite gap set, F(U) for its maximum,
g(U) for its cardinality, and PF(U) for its pseudo-Frobenius numbers. A gap f
is pseudo-Frobenius when f+s belongs to U for every positive s belonging to
U. An almost symmetric numerical semigroup is closed under addition and
satisfies 2g(U)=F(U)+|PF(U)|. A symmetric numerical set satisfies
a∈U if and only if F(U)−a∉U for every integer 0≤a≤F(U); additive closure is
not required of the target.

The map in Theorem 4.2 simultaneously deletes exactly the rows originally
labelled by PF(U) other than F(U), preserves every retained row length, and
inverts the resulting boundary. Pseudo-Frobenius numbers are computed in
the original source, never recomputed after deletion. Thus the event is
literally every proper symmetric target T having some proper almost
symmetric semigroup source S with Φ(S)=T. There is no bound on source size,
Frobenius number, genus, type or multiplicity.

## Motivation

The paper's symmetrization sends almost symmetric semigroups to symmetric
numerical sets and need not produce semigroups. Surjectivity asks whether
that construction reaches the whole stated target class. The existing
`FerrersRowCoordinates` module supplies related row/column-coordinate
vocabulary; it is a motivation link, not an imported premise or a reduction
to a fixed rectangle. The present carrier allows every nonempty finite gap
set excluding zero.

## Gap

The final paragraph of Section 5 explicitly poses surjectivity and the
problem of characterizing the image. The source's finite Frobenius tables
do not decide the unrestricted event. The obstruction below excludes one
target uniformly over every possible source and does not characterize the
full image. No claim of literature priority or exhaustive forward-citation
search is made.

## Route

For an original row r, let l(r) count source members below r, and let R be
any retained subfamily of the original gap set. The complete boundary count
and its partition into retained and deleted gaps give

$$
l(r)+|\{q\in G(U):q<r\}|=r,
$$

$$
r-|\{q\in G(U)\setminus R:q<r\}|
=l(r)+|\{q\in R:q<r\}|\qquad(r\in R).
$$

The right side is the inverse-boundary gap label after deleting the other
up steps. Equal row lengths are retained with their original order and
multiplicity. The private lemmas `original_boundary_label` and
`deletion_is_inverse_boundary` establish this bridge for arbitrary U and R.

For every proper numerical semigroup U, a length-one row survives:

1. If no positive source member is at most F(U), the Frobenius row survives
   and its only preceding right step is zero.
2. Otherwise let M be the greatest positive member at most F(U). Then
   M<F(U). Put r=F(U)−M. Additive closure shows that r is a gap, since
   r+M=F(U). The same positive member M shows that r is not
   pseudo-Frobenius, so its original row survives. A positive source member
   a<r would make M+a a source member strictly between M and F(U), which
   contradicts maximality. Thus this row also has length one.

The first retained row has positive length because zero is a member. Its
length is at most that of the surviving length-one row, so its length is
one. With no preceding retained up steps, its inverse-boundary label is
one. Consequently `phi_omits_one` excludes 1 from Φ(U) for every proper
numerical semigroup U, without an almost-symmetry assumption.

Take T={0,1}∪{n∈ℕ:n≥4}, with complete gap set {2,3}. Its Frobenius number
is 3 and its complementary pairs are {0,3} and {1,2}, so it is symmetric.
It contains 1. Applying any alleged surjective preimage to this target
contradicts `phi_omits_one`. This is the proof of `result : ¬ claim`.

## Falsifier

Source correspondence would fail if the carrier bounded any source
parameter, required target additive closure, recomputed pseudo-Frobenius
numbers, retained old labels without their deletion shift, or assumed the
length-one obstruction. The carrier, definitions and inverse-boundary
bridge preserve all these distinctions. Both proof cases are needed;
there is no enumeration of possible preimages. The example is not a
semigroup because 1+1=2 is a gap, which is permitted by the source target
class.

## Evidence

The mathematical source is
`D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.lean`.
Its `claim` has the literal type `Prop`, with the complete universal-target
and existential-source event; `result` has the literal type `Not claim`.
The proof uses the uniform theorem `phi_omits_one` and the explicit target
with gaps {2,3}.

The mirrored Reg source is
`Reg/D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiRefutation.lean`.
Its dependent-family registration retains the full `NumericalSet` source
and `Set ℕ` output, the semigroup antecedent, an exact equivalence bridge,
an enrolled readout, intervention/sensitivity and observational dependence.
The continuation is unknown. The terminal `result` alone has the designated
refutation exemption. Registration does not replace canonical admission or
establish correspondence to the external prose.

The owning Blueprint Scribe attributes the paper's definitions and question
to the Library note and acknowledges that source separately for the
repository-derived obstruction and refutation. Primary locators are
Section 2, Section 4 Theorem 4.2, and the final paragraph of Section 5 at
https://arxiv.org/html/2611.14268v1. The construction follows the mathematical
row deletion, not an executable interpretation of the extracted Algorithm
1 punctuation.

## Triage

This is an unrestricted analytic refutation of the stated surjectivity
event. Its admissibility basis is the external open-problem-resolution
exception, not a new general image-classification theorem. The auxiliary
binding lemmas are consumed by the content proof; the retained-row
construction and uniform omission invariant carry the argument. No
corresponding theory volume is present, so the applicable first-freeze
route is `deposit-uncovered` after independent prefreeze review. A typed
resolution claim belongs to the terminal theorem's Scribe node only after
that theorem becomes a current frozen member.

## ASSUMED-UNVERIFIED

The paper's output-symmetry theorem is not assumed on the Lean proof path
and is not formally verified here. The full image characterization and
literature priority remain outside this result. Later versions and forward
citations have not been exhaustively checked. Compilation and the typed
audit do not prove natural-language source correspondence, independent
review approval, first-freeze admission, required CI success or delivery
into dev.
