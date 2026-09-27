---
slug: nikandish-subspace-orthogonality-clique
bibkey: nikandish2026orthogonality
doi: 10.48550/arXiv.2609.22769
url: https://arxiv.org/abs/2609.22769v1
triage: theorem
motivation_gids:
  - D5/S3/Fourier/CharacterSelection/BinaryCharacterCodeDuality.standardCoordinatePairing
---

# Nikandish Problem 4.2

## Problem

Section 4 of the cited source asks: "Determine the exact value of
omega(O_n*) for general n." For every integer `n >= 1`, the vertices
are all nonzero linear subspaces of `F_2^n`. Distinct vertices are adjacent
when every vector in one is orthogonal to every vector in the other under
the standard symmetric, nonalternating dot form.

## Motivation

The frozen standard coordinate pairing supplies the exact ambient form.
The target concerns the whole subspace lattice, including degenerate
subspaces with nonzero intersections, and cannot be replaced by a graph
on lines or nondegenerate subspaces.

## Gap

The source gives lower constructions and low-dimensional information,
but its general clique number is posed as Problem 4.2. Its Lemma 3.2
counting argument incorrectly gives three nonzero subspaces of `F_2^2`;
the correct count is four. That argument is not a premise of the consumer.

## Route

The exact consumer `D5/S3/Combinatorics/Orthogonality/NikandishClique.result`
states, for every `n >= 1`,

    (orthogonalityGraph n).cliqueNum = max n (nonzeroSubspaceCount (n/2) + n%2).

Here `nonzeroSubspaceCount r` is `Nat.card` of all nonzero submodules of
`Fin r -> ZMod 2`. The sum `R` of the radicals of clique members is
totally isotropic. Quotient images in `R-perp/R` have nondegenerate
restrictions and form an indexed independent family. Members contained
in `R` contribute at most `N(dim R)`, and the others at most `n-2 dim R`.
The increment `N(r+1) >= N(r)+2` for `r >= 1` reduces the upper bound to
the two endpoints. Coordinate lines and the full nonzero lattice of the
duplicate-coordinate isotropic space attain them; in odd dimensions the
perpendicular space supplies one extra vertex. The source already gives
this latter construction when `n = 7`.

## Falsifier

A clique larger than both endpoints, or failure of restriction separation
for a nonzero quotient image, would invalidate the proposed formula or
route. Anisotropic-vector selection is not a valid substitute: a
nondegenerate alternating restriction over `F_2` need not contain any
anisotropic vector. The proof uses arbitrary test vectors instead.

## Evidence

The primary Definition 2.3 and Problem 4.2 were read in the versioned HTML.
The native Lean consumer proves the unrestricted formula by the radical,
quotient, lattice, and extremal arguments described in the source note.
The cardinality target was included in preregistration issue 9458.
The Gaussian-binomial counting bridge is outside this statement and is
not asserted. The ring-graph corollary is not a separate delivered theorem.

## Triage

`theorem`; Tier 1, a named question in a September 2026 paper, preregistered
in issue 9458 before probes. Prospective admission basis is
`open-problem-resolution`. The single public theorem has `proof_shape: content`:
the arbitrary-clique radical-family estimate and its extremal completion
are on the live proof path, rather than an instance of an existing clique
formula. Utility is `none`, since this is symbolic for every dimension,
not a bounded enumeration, checker, numeric reduction, or certified instance.
Definitions describe the source object and independent lattice count;
there are no separately delivered classical helper theorems.

## ASSUMED-UNVERIFIED

Prior-proof absence is bounded by the searches documented in the Library
note and the attributed independent intake; worldwide novelty is not
certified. Admission, independent delivery review, Freeze, CI, and merge
are separate from the Lean statement and remain caller-owned. The typed
Scribe resolution claim must bind this exact result after Freeze; a
pre-Freeze document without that claim is not the final publication.
