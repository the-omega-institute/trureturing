---
slug: pronko-2025-fredkin-xi-hamiltonian-commutation
bibkey: pronko2025fredkin
doi: 10.1088/1751-8121/ae1644
url: https://doi.org/10.1088/1751-8121/ae1644
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.result
---

# Pronko's commutation of the Dyck-class operator Ξ with the periodic Fredkin Hamiltonian

## Problem

Pronko reads spin words as lattice paths in section 2.2, printed p. 4:

> A Dyck path of length `N` starts at `(x,y)=(a,0)` and ends at `(x,y)=(b,N)`,
> at each step `Δx = 1` and `Δy = ±1`, with the condition that at least once the
> path hits the `x`-axis, i.e., `min y = 0` along the path. … we will call all
> such paths as belonging to the equivalence class `C_{a,b}(N)`.

A letter `↑` is a step up and a letter `↓` a step down. Section 4.1, printed
pp. 9-10, defines for even `N`

> `Ξ = Σ_{k=0}^{N/2} (−1)^k Σ_{ℓ₁ℓ₂…ℓ_N ∈ C_{k,k}(N)} n_1^{ℓ₁} n_2^{ℓ₂} ⋯ n_N^{ℓ_N}`, (4.1)

with `n^{ℓ}` the spin-up and spin-down projections, and states on printed
p. 10:

> It commutes with the Hamiltonian and anti-commutes with the cyclic shift
> operator: `[Ξ, H] = 0`, `C Ξ C⁻¹ = −Ξ`. The first relation may require a proof
> though we find it satisfied in all checks; the second one is obvious from (4.1).

`H` is the periodic Fredkin Hamiltonian (2.3) with density (2.2),
`F_{j,j+1,j+2} = n↑_j Π_{j+1,j+2} + Π_{j,j+1} n↓_{j+2}`, sites modulo `N`.

Issue #9996 fixes the readings: (i) `ℓ ∈ C_{a,b}(N)` when the path started at
height `a` stays at height `≥ 0`, touches `0`, and ends at `b`; (ii) the
projections and `H` are those of the frozen module
`D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation`; (iii) `N` is even
and `N ≥ 3`; (iv) only the first relation `[Ξ, H] = 0` is settled.

## Motivation

The frozen declaration `D5/S3/Quantum/Dynamics/PronkoFredkinXiCommutes.result`
proves `[Ξ, H] = 0` for every even `N ≥ 3`. The paper uses this relation, with
`C Ξ C⁻¹ = −Ξ`, to explain the double degeneracy it observes numerically in the
`S^z = 0` sector of the spectrum.

## Gap

Issue #9996 preregisters this printed, explicitly unproven relation and its
literature check. Crossref reports one citing work; Semantic Scholar lists
exactly one, arXiv:2509.04838, whose text does not discuss `Ξ` or the spectral
doubling. MathDB has entries for Conjectures 1-4 of the paper
(`/p/369467`-`/p/369470`) and none for this relation.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent proof.

## Route

`Ξ` is diagonal. A word is balanced when it has as many up letters as down
letters; a balanced word lies in exactly one class `C_{a,a}(N)`, with
`a = −min_{0 ≤ i ≤ N} s_i` for the prefix heights `s_i`, and `Ξ` takes the
value `(−1)^a` there; `Ξ` vanishes on unbalanced words. The off-diagonal part of
`F_{j,j+1,j+2}` exchanges the letters at `j + 1, j + 2` when the letter at `j`
is up, or at `j, j + 1` when the letter at `j + 2` is down, indices modulo `N`.
An exchange keeps the number of up letters. An exchange that does not wrap
changes one prefix height by two, and the control letter forces the smaller
value to occur at another index, so `a` is unchanged. An exchange of the last
and the first letter moves every interior height by the same amount, and the
control letter forces an interior height `≤ 0` in both words, so `a` changes by
zero or two. Hence `Ξ` commutes with every density and with `H`. The argument
uses only `N ≥ 3`; for odd `N` there are no balanced words.

## Falsifier

A refutation would be an even `N ≥ 3` and two basis words joined by a nonzero
off-diagonal entry of `H` whose depths `a` have different parities. The
depth-parity invariance proved for every periodic Fredkin exchange rules this
out.

## Evidence

`H` was built term by term from (2.2) and (2.3), and `Ξ` from (4.1) by class
membership, for `N = 2, 4, …, 12`. For `N = 4..12` the largest entry of
`[Ξ, H]` is zero and no nonzero off-diagonal entry of `H` joins balanced words of
different depth parity. For `N = 2` the three-site terms overlap and
`max|[Ξ, H]| = 2`; that case is outside the statement. The Lean proof has only
the standard axiom closure `propext`, `Classical.choice`, and `Quot.sound`.
These finite checks support the reading but do not establish the universal
theorem.

## Triage

A printed relation stated as needing proof in Pronko, *Journal of Physics A:
Mathematical and Theoretical* 58 (2025) 445204, section 4.1, preregistered in
issue #9996. Resolution: `proved`.

The public surface is exactly `pathHeight`, `inClass`, `Xi`, `claim`, and
`result`. This is a uniform theorem, not bounded enumeration, checker
infrastructure, numeric reduction, or a certified finite instance, so
`utility: none` applies. The relation `C Ξ C⁻¹ = −Ξ` and the spectral doubling
are not asserted.

## ASSUMED-UNVERIFIED

OpenAlex was rate limited and is `ASSUMED-UNVERIFIED`. The bounded literature
check does not establish exhaustive worldwide novelty, priority, or the absence
of an independent proof. The Lean kernel does not authenticate the external
PDF, its printed pagination, the literature-check coverage, or publication
history. The finite checks for small `N` do not establish the universal
theorem.
