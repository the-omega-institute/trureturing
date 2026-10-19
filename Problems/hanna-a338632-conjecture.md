---
slug: hanna-a338632-conjecture
bibkey: hanna2026a338632
doi: null
url: https://oeis.org/A338632
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/HannaA338632
---

# Hanna's OEIS A338632 congruence

## Problem

Paul D. Hanna's OEIS A338632, revision 13, states:

> G.f. A(x) satisfies: 1 = A(x) - x/(A(x) - 3*x/(A(x) - 5*x/(A(x) - 7*x/(A(x) - 9*x/(A(x) - ...))))), a continued fraction relation.

Its formula line is:

> a(n) = 2 (mod 4) for n > 1 (conjecture).

The offset is zero. The source note is `Library/RecurrenceComposition/hanna2026a338632.md`.

### Statement echo

| Source clause | Formal counterpart | Scope |
| --- | --- | --- |
| The displayed continued fraction | `tail` uses the literal rational-series finite truncations, ending at $A$ | The numerator at level $j$ is $(2j+1)x$. |
| The equation equals one | `IsGF` | For each coefficient index, every sufficiently deep truncation has that coefficient equal to the constant series one. |
| The generating series exists | The first conjunct of `claim`, proved by `result` | This makes the universal coefficient assertion nonvacuous. |
| $a(n)$, offset zero | The degree-$n$ coefficient of any rational series satisfying `IsGF` | The source convention is unchanged. |
| $n>1$ | $2\le n$ for natural $n$ | The two ranges coincide. |
| $a(n)=2\pmod4$ | An integer representative $m$ of that rational coefficient with $m\bmod4=2$ | Integrality at the stated indices is part of the conclusion. |

The quantification over all series satisfying the relation and explicit existence are stronger than selecting one unnamed generating series; they do not weaken the source. The private `gf_unique` identifies every such series with the constructed solution.

## Motivation

This is a first-tier externally stated OEIS conjecture, preregistered in [#18983](https://github.com/the-omega-institute/trureturing/issues/18983). The settling declaration is `D5/S1/Recurrence/Invariants/HannaA338632.result`, with admission basis `open-problem-resolution (#18983; Proved)`.

## Gap

The bounded literature screen recorded in #18983 read the OEIS internal entry, where the modulo-four assertion is labelled conjectural and no proof is cited. The search used A338632, proof, congruence, Hanna and the continued-fraction title words, checked the repository and issues, and checked `epoch-research/LeanOpenProblems-results` metadata. No settlement was found in that scope. MathDB access was unavailable. Search completeness is `ASSUMED-UNVERIFIED`.

## Route

The proof constructs finite tails over a commutative ring with unit constant coefficient. Agreement through a finite coefficient range is preserved by normalized inversion; multiplying by $x$ gains one coefficient. The existing `Agree`, `agree_inv`, `agree_shift`, `map_inverse` and `inverse_one` declarations of `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare` supply these operations and are used in the compiled proof.

The private `ft_stable` proves depth stabilization. The diagonal approximation `sol`, its fixed-point identity `sol_fixed`, and `fixed_unique` construct and identify the normalized solution. `gf_sol` and `gf_unique` connect this construction to the literal rational-series predicate `IsGF`. The used ring-map identity `map_sol` transfers the integer solution both to the rationals and to $\mathbb Z/4\mathbb Z$.

Modulo four, the odd numerators have period two. The private `ft_period`, `lt_period` and `reduced_quad` give the quadratic
$A^2-(1+3x)A+2x=0$ for the reduced solution. The series
$B=(1+x^2)/(1-x)$ satisfies the same quadratic by `closed_quad`.
The factorization
$(A-B)(A+B-1-3x)=0$
has a unit second factor because its constant coefficient is one. `reduced_closed` therefore identifies $A=B$. The coefficient identity `closed_coeff` and the integral lift give the congruence in `result`.

## Falsifier

The statement would fail if no rational series satisfied `IsGF`, or if a series satisfying it had a coefficient at an index $n\ge2$ without an integer representative congruent to two modulo four. The universal theorem excludes both possibilities within the stated formal interpretation. A numerical truncation alone cannot settle that universal assertion.

## Evidence

- Lean: `D5/S1/Recurrence/Invariants/HannaA338632.lean`, public theorem `D5.S1.Recurrence.Invariants.HannaA338632.result`.
- Scribe: `Blueprint/D5/S1/Recurrence/Invariants/HannaA338632.scribe.cs`; the result node displays the full claim and carries one `OpenProblemResolutionClaim` of kind `Proved`.
- Existing owner: `D5/S1/Recurrence/Residue/ContinuedFractionOddSquare.lean`, with unchanged statements and proofs of the five published declarations.
- The public declarations' axiom closures are contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
- Escape audit unfinished: [#19167](https://github.com/the-omega-institute/trureturing/issues/19167), covering `result`, the published definition `Agree`, `agree_inv`, `agree_shift`, `map_inverse` and `inverse_one`. No target is claimed `declared_validated`.

### Experiment

[Exact rational finite-truncation check](https://github.com/the-omega-institute/trureturing-experiments/tree/f1e11ce70fdf5e6e3f6b949b8ed06eb052d0c89f/docs/reports/oeis-a338632-hanna-continued-fraction-mod4).

Command: `git -C /Users/auric/trureturing-experiments show f1e11ce70fdf5e6e3f6b949b8ed06eb052d0c89f:docs/reports/oeis-a338632-hanna-continued-fraction-mod4/check.py | python3 -`.
Exit code: 0. Script SHA-256: `d3a679f5d845890887da25e41cb4ceae7fffe3a0609e2f8687c2633ff38bbb43`.

The check computes integral coefficients through degree 40, agrees with the 19 listed OEIS coefficients, and verifies the defining relation through degree 40. It verifies $a(n)\equiv2\pmod4$ for $2\le n\le40$ and $A\equiv(1+x^2)/(1-x)\pmod4$ through degree 40. It also computes $A^2\equiv A+x\pmod3$ through degree 40. These are finite computed readings; the universal modulo-four conclusion comes from the Lean theorem.

## Triage

`theorem`: the named modulo-four conjecture is proved. The three target items have the following evidence kinds.

| Item | Status | Evidence |
| --- | --- | --- |
| Settlement, including existence and an integer representative congruent to two for every $n\ge2$ | Proved in Lean | `result`; uniqueness is the private used theorem `gf_unique`. |
| Period-two mechanism, quadratic and normalized rational root modulo four | Proved in Lean | Private used theorems `ft_period`, `lt_period`, `reduced_quad`, `closed_quad`, `reduced_closed` and `closed_coeff`. |
| Modulo-three relation through degree 40 | Computed | The pinned experiment, exit 0 and SHA-256 above; degrees 0 through 40 only. |
| Uniform modulo-three relation and the entry's A191107/A186776 residue classifications | Open | No theorem for these statements is delivered. |
| Literature completeness | ASSUMED-UNVERIFIED | The bounded literature reading in #18983. |

### What the settlement shows

The decisive mechanism is that period two modulo four converts the continued fraction into a quadratic whose normalized root is rational. The coefficient conclusion holds for every index at least two, with no resource or truncation bound. The solution construction and uniqueness arguments operate over commutative rings; the literal public continued-fraction predicate is over rational power series. No universal modulus other than four is asserted here. The pinned exact computation gives coefficients one at degrees zero and one, so the asserted residue two does not extend to those two indices; this endpoint reading is computed, not a separately stated Lean theorem.

The modulo-three computation supports the separate relation $A^2=A+x$ only in its tested range. The source's A191107 and A186776 classifications, and uniform algebraic reductions at other odd moduli, remain open in this delivery. None of those conjectures is used as a hypothesis of the proved modulo-four result. No dependent source theorem is claimed to become settled by this resolution.

## ASSUMED-UNVERIFIED

Literature completeness and publication priority are not established by the bounded search. Interpreting the informal continued fraction by coefficientwise limits of the specified finite truncations is the explicit convention of #18983. No analytic convergence or alternate continued-fraction convention is asserted. The escape-audit evidence named in #19167 is unfinished and is independent of the kernel-checked mathematical result.
