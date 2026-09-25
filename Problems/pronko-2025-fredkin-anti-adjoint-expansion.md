---
slug: pronko-2025-fredkin-anti-adjoint-expansion
bibkey: pronko2025fredkin
doi: 10.1088/1751-8121/ae1644
url: https://doi.org/10.1088/1751-8121/ae1644
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.result
---

# Pronko's anti-adjoint expansion conjecture for the periodic Fredkin chain

## Problem

Pronko fixes the one-site Pauli matrices in section 2.1, printed p. 3:

> The basis in End(ℂ²) is provided by the Pauli matrices
> `σ⁺ = [[0, 1], [0, 0]], σ⁻ = [[0, 0], [1, 0]], σᶻ = [[1, 0], [0, −1]]`.

Equation (2.1), printed p. 3, normalizes the total spin operators:

> `S^± = Σ_{j=1}^N σ_j^±`, `S^z = ½ Σ_{j=1}^N σ_j^z`.

Theorem 2, equation (3.1), printed pp. 6-7, defines

> `Σ^± = Σ_{r₁,...,r_N ∈ {−1,0,1}, r₁+⋯+r_N = ±1} σ₁^{r₁} ⋯ σ_N^{r_N}`,
> where `σ_i^0 = 1` and `σ_i^{±1} = σ_i^±`.

Conjecture 2, printed p. 7, is:

> For the operators Σ^± there exists the representation
> `Σ^± = Σ_{k=1}^{⌈N/2⌉} γ_k (ãd S^± ãd S^∓)^{k−1} S^±`,
> where γ_k are some coefficients and ãd denotes the anti-adjoint action,
> `(ãd a) b ≡ {a, b} = ab + ba`.

The paper gives `Σ^± = −¼ S^± + ⅛ {S^±, {S^∓, S^±}}` for `N = 3` and the
coefficients for `N ≤ 10` in Table 1, printed p. 8.

Issue #9982 fixes the readings: (i) `Σ^±` is (3.1) literally; (ii) `S^±` has
the (2.1) normalization; (iii) `(ãd S^± ãd S^∓)^{k−1} S^±` is the map
`X ↦ {S^±, {S^∓, X}}` iterated `k − 1` times on `S^±`; (iv) one family of
complex coefficients serves both signs; (v) every natural number `N`.

## Motivation

The frozen declaration
`D5/S3/Quantum/Dynamics/PronkoFredkinAntiAdjointExpansion.result` proves
Conjecture 2 for every `N`, with one coefficient family for both signs. The
operators `Σ^±` commute with the periodic Fredkin Hamiltonian (Theorem 2 of the
paper), while the total spin operators do not; the theorem expresses the
nonlocal symmetry generators as explicit finite expressions in `S^±`.

## Gap

Issue #9982 preregisters this published conjecture and its literature check.
Crossref reports `is-referenced-by-count = 1`; Semantic Scholar lists exactly
one citing work, arXiv:2509.04838, whose text states once that the nonlocal
conserved charges "are linear combinations of the total spin operator `S^±`",
citing the paper, without a proof or the coefficients. MathDB `/p/369468`
has status `open` with zero solutions. The conclusion of the paper suggests the
technique of Zhou and Fu (Quantum Inf. Process. 10 (2011) 379-394); that
paper's text is not publicly readable and is `ASSUMED-UNVERIFIED`.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent proof.

## Route

For spin words `y, x` let `b` count sites with `(y_i, x_i) = (↑, ↓)` and `c`
count sites with `(↓, ↑)`. Let `Z_r(y, x) = [b = r + 1 ∧ c = r]` and
`E_s(y, x) = [b = c = s]`. Summing single-site flips gives

- `{S⁻, Z_r} = 2(r + 1) E_{r+1} + (N − 2r) E_r`,
- `{S⁺, E_s} = 2(s + 1) Z_s + (N − 2s + 1) Z_{s−1}`,

where the counts of sites with equal letters add up to `N − b − c`. Hence the
map `A X = {S⁺, {S⁻, X}}` acts on the patterns by the three-term recurrence

`A Z_r = 4(r + 1)(r + 2) Z_{r+1} + 2(r + 1)(2N − 4r − 1) Z_r + (N − 2r)(N − 2r + 1) Z_{r−1}`.

Since `E_0` is the identity, the case `s = 0` gives `S⁺ = Z_0`. The leading
coefficient is nonzero, so by induction each `Z_r` lies in the span of
`S⁺, A S⁺, …, A^r S⁺`. Reading (3.1) entrywise — every Kronecker factor is `0`
or `1`, and at each site pair exactly one exponent gives `1` — yields
`Σ⁺(y, x) = [b − c = 1]`;
as `b + c ≤ N`, `Σ⁺ = Σ_{r < ⌈N/2⌉} Z_r` lies in the span of the first
`⌈N/2⌉` iterates. Transposition maps `σ⁺` to `σ⁻`, `Σ⁺` to `Σ⁻` and each
raising iterate to the matching lowering iterate, so the same coefficients
serve `Σ⁻`.

## Falsifier

A refutation would be an `N` for which `Σ⁺` is not a complex linear
combination of `S⁺, A S⁺, …, A^{⌈N/2⌉−1} S⁺`, or for which no single
coefficient family gives both signs. The three-term recurrence with nonzero
leading coefficient rules this out for every `N`.

## Evidence

The literal Kronecker matrices of (3.1) and (2.1) were built for `N = 1..8`.
The three-term recurrence holds exactly for every `r ≤ (N − 1)/2`,
`S⁺ = Z_0`, `Σ⁺ = Σ_r Z_r`, `{S⁺, {S⁻, Σ⁺}} = N(N + 1) Σ⁺` and
`Σ⁻ = (Σ⁺)ᵀ`. Solving the tridiagonal model exactly over the rationals
reproduces all forty entries of Table 1 for `N = 3..10`, for example
`N = 10`: `63/128, −641/5120, 509/61440, −7/36864, 1/737280`. A least-squares
solve against the literal matrices for `N = 3..7` agrees with Table 1 with
residual at most `8.2e−13`, and the same coefficients reproduce `Σ⁻` for
`N = 1..8`. The Lean proof has only the standard axiom closure `propext`,
`Classical.choice`, and `Quot.sound`. These finite checks support the reading
but do not establish the universal theorem.

## Triage

First-tier external named open problem: Pronko, *Journal of Physics A:
Mathematical and Theoretical* 58 (2025) 445204, Conjecture 2, preregistered in
issue #9982. Resolution: `proved`.

The public surface is exactly `antiAd`, `totalPlus`, `totalMinus`, `claim`,
and `result`. This is a uniform symbolic theorem, not bounded enumeration,
checker infrastructure, numeric reduction, or a certified finite instance, so
`utility: none` applies. Conjecture 1 is settled separately; Conjectures 3 and
4 of the paper are not asserted.

## ASSUMED-UNVERIFIED

The content of Zhou and Fu (2011) is `ASSUMED-UNVERIFIED` because its text and
abstract were not publicly readable. OpenAlex was rate limited and is
`ASSUMED-UNVERIFIED`. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent proof.
The Lean kernel does not authenticate the external PDF, its printed pagination,
the literature-check coverage, or publication history. The finite checks for
small `N` do not establish the universal theorem.
