---
slug: pronko-2025-fredkin-noncyclic-annihilation
bibkey: pronko2025fredkin
doi: 10.1088/1751-8121/ae1644
url: https://doi.org/10.1088/1751-8121/ae1644
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.result
---

# Pronko's non-cyclic Fredkin eigenstate annihilation conjecture

## Problem

Pronko fixes the one-site basis in section 2.1, printed p. 3:

> We denote basis vectors in ℂ² by
> `|↑⟩ = (1, 0)ᵀ, |↓⟩ = (0, 1)ᵀ`.
>
> The basis in End(ℂ²) is provided by the Pauli matrices
> `σ⁺ = [[0, 1], [0, 0]], σ⁻ = [[0, 0], [1, 0]], σᶻ = [[1, 0], [0, −1]]`.
>
> We will also use projectors onto the spin-up and spin-down states:
> `n↑ = ½(1 + σᶻ), n↓ = ½(1 − σᶻ)`.

The same page defines the adjacent exchange and antisymmetrizer:

> Consider two adjacent copies of ℂ², say, the jth and (j + 1)th. Important
> objects are the permutation operator `P_{j,j+1}`, which exchanges these copies,
> and the projector `Π_{j,j+1}` onto the spin-0 state, which is essentially the
> antisymmetrizer,
> `Π_{j,j+1} = ½(1 − P_{j,j+1})`.

It then prints the Hamiltonian density and periodic Hamiltonian:

> `F_{j,j+1,j+2} = n↑_j Π_{j+1,j+2} + Π_{j,j+1} n↓_{j+2}`. (2.2)
>
> The periodic boundary conditions mean that the Hamiltonian is the cyclic sum,
> `H = Σ_{j=1}^{N} F_{j,j+1,j+2}`. (2.3)
>
> where identification of sites by modulus N is assumed.

Across printed pp. 3-4 the source gives the ordered product and its action:

> The operator `C = P_{1,2} ⋯ P_{N−2,N−1} P_{N−1,N}` is the cyclic shift
> operator C, acting on sites as `i ↦ i + 1`.

Theorem 2, equation (3.1), printed pp. 6-7, states:

> The operators
> `Σ^± = Σ_{r₁,...,r_N ∈ {−1,0,1}, r₁+⋯+r_N = ±1}
> σ₁^{r₁} ⋯ σ_N^{r_N}`, (3.1)
> where `σ_i^0 = 1` and `σ_i^{±1} = σ_i^±`.

Conjecture 1, printed p. 7, is:

> The operators Σ^± annihilate all non-cyclic invariant (C ≠ 1)
> eigenstates of the Hamiltonian.

Issue #9359 fixes four readings: (i) an eigenstate is a nonzero `H`-eigenvector
that is also a `C`-eigenvector; (ii) non-cyclic means its `C`-eigenvalue `c` is
not one; (iii) (3.1) is represented literally, with `Fin 3` values `0,1,2`
encoding exponents `-1,0,1`; and (iv) sites are modulo `N`, `N >= 3`, over
complex scalars.

## Motivation

The frozen declaration
`D5/S3/Quantum/Dynamics/PronkoFredkinNonCyclicAnnihilation.result` proves
Conjecture 1 for every `N >= 3`. It retains the simultaneous Hamiltonian
eigenvector hypothesis but proves the stronger fact used by the conjecture:
every `C`-eigenvector with eigenvalue different from one is annihilated by both
operators.

## Gap

Issue #9359 preregisters this published conjecture and its literature check.
Crossref reports `is-referenced-by-count = 1`. OpenAlex records `W4415449412`
with `cited_by_count = 1` and `W4415233546` with `cited_by_count = 0`. The only
citing work found, arXiv:2509.04838v2, does not mention Conjecture 1.
arXiv:2608.17548 proves a different Pronko conjecture. MathDB problem `/p/369467`
lists zero solutions. Semantic Scholar returned HTTP 429 and is
`ASSUMED-UNVERIFIED`.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent proof.

## Route

The exact entry description is
`Sigma M ε y x = [weight y − weight x = ε]`: at each `(y,x)`, at most
one Kronecker monomial of (3.1) has a nonzero value, and it lies in the
constrained sum exactly when the displayed weight difference equals `ε`;
otherwise no term of (3.1) contributes.
Weight is invariant under every site swap, so
`Sigma M epsilon * P M j = Sigma M epsilon`. Folding this identity over the
printed ordered product gives the organizing absorption identity
`Sigma M epsilon * C M = Sigma M epsilon`. Thus
`Sigma psi = Sigma C psi = c * Sigma psi`; since `c != 1`,
`(c - 1) * Sigma psi = 0` forces `Sigma psi = 0`. The proof uses no property of
`H`.

Under CLAUDE.md section 3.2, `result` has `proof_shape: bind-only` and
`escape_witness: none`, with `admission_basis: open-problem-resolution` under
issue #9359. After the local `have` chain is inlined, every step is an
instantiation of a pinned Mathlib declaration or a finite normalization of the
module's own tables: `Finset.prod_ite_zero`, `Finset.sum_sub_distrib`,
`Equiv.sum_comp`, `PEquiv.mul_toMatrix_toPEquiv`, list induction on `List.prod`,
`Matrix.mulVec_mulVec`, `Matrix.mulVec_smul`, `smul_eq_zero`, and `sub_eq_zero`.
The absorption identity is the organizing intermediate fact, not an escape
witness. The direct frozen dependency is
`D5/S3/Quantum/FiniteDimensional.qubitZ` with statement_id
`sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c`,
carried through `nUp` and `nDown`.

## Falsifier

A refutation would be an `N >= 3` and a nonzero simultaneous `H`/`C`
eigenvector with `C`-eigenvalue `c != 1` that is not annihilated by `Sigma+` or
`Sigma-`. The absorption identity (E),
`Sigma M epsilon * C M = Sigma M epsilon`, rules this out for every
`C`-eigenvector with eigenvalue different from one.

## Evidence

The orchestrator built integer matrices directly from (3.1) by Kronecker
products for `N = 2..6` and `epsilon = +/-1`. Entrywise, at each `(y,x)` at
most one monomial is nonzero; it lies in (3.1) exactly when
`weight(y) - weight(x) = epsilon`, and otherwise no term contributes. Both
`Sigma^epsilon C = Sigma^epsilon` and `C Sigma^epsilon = Sigma^epsilon` hold in
every checked case.

The printed matrices, projectors, (2.2), (2.3), the ordered `C` product, (3.1),
and Conjecture 1 were checked against rendered printed pp. 3, 6, and 7; the
shift characterization continues onto printed p. 4. The Lean proof has only
the standard axiom closure `propext`, `Classical.choice`, and `Quot.sound`.
These finite checks support the reading and route but do not establish the
universal theorem.

## Triage

First-tier external named open problem: Pronko, *Journal of Physics A:
Mathematical and Theoretical* 58 (2025) 445204, Conjecture 1, preregistered in
issue #9359. Resolution: `proved`.

| proof_shape | escape_witness | direct frozen dependencies | admission_basis |
| --- | --- | --- | --- |
| bind-only | none | D5/S3/Quantum/FiniteDimensional.qubitZ | open-problem-resolution |

The public surface is exactly `sigmaPlus`, `sigmaMinus`, `nUp`, `nDown`,
`tensor`, `site`, `P`, `Pi`, `F`, `H`, `C`, `sigmaPow`, `Sigma`, `claim`, and
`result`; `spinStep` and `weight` are private data definitions. This is a
uniform symbolic theorem, not bounded enumeration, checker infrastructure,
numeric reduction, or a certified finite instance, so `utility: none` applies.
Conjecture 2, equations (3.3)/(3.4), ground-state claims, and the Motzkin
analogue are not asserted.

## ASSUMED-UNVERIFIED

Semantic Scholar is `ASSUMED-UNVERIFIED` because it returned HTTP 429. The
bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent proof. The Lean kernel does not
authenticate the external PDF, its printed pagination, the literature-search
coverage, or publication history. The finite checks through `N = 6` do not
establish the universal theorem.
