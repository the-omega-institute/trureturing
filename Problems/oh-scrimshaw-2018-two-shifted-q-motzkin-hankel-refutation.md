---
slug: oh-scrimshaw-2018-two-shifted-q-motzkin-hankel-refutation
bibkey: oh2018identities
doi: 10.48550/arXiv.1805.00113
url: https://arxiv.org/abs/1805.00113v1
triage: theorem
motivation_gids:
  - D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.result
---

# Oh and Scrimshaw's two-shifted q-Motzkin Hankel conjecture

## Problem

Oh and Scrimshaw consider Cigler's `q`-Motzkin numbers

> M̃†_{n+1}(q) = M̃†_n(q) + Σ_{k=0}^{n−1} q^{k+1} M̃†_k(q) M̃†_{n−k−1}(q),
> M̃†_0(q) = 1,

and state, based on numerical computations, the first conjecture labelled
`conj:factored_motzkin_2shifted` in their appendix on other `q`-determinants:

> Define f_n(q) := Σ_{1 ≤ k ≤ n, k ≢ 1 mod 3} q^k if n ≡ 0 mod 3, and
> (q+1)(Σ_{k=0}^{⌊n/3⌋} q^{3k}) otherwise. Then we have
> (det[M̃†_{i+j+2}(q)]_{i,j=0}^{n−1})_{n=1}^∞ = (q^{c_n} f_n(q))_{n=1}^∞
> for some c_n ∈ ℤ_{≥0}.

Issue #10046 fixes the readings: the polynomials and the determinant live in
`ℤ[q]`; "for some `c_n`" means that for each `n ≥ 1` some natural number
`c_n` makes the polynomial identity hold; the second conjecture carrying the
same label, on the three-shifted determinants, is not addressed.

## Motivation

The frozen declaration
`D5/S0/Certificates/OhScrimshawQMotzkinHankelRefutation.result` proves that
the conjecture is false as printed: at `n = 3` no power of `q` times `f_3`
equals the determinant. The formal statement makes no claim about a corrected
summation range.

## Gap

Issue #10046 preregisters the published conjecture and its literature check.
MathDB `/p/339076` has status `open` with zero solutions. Semantic Scholar
lists four citing papers, on fluctuations of Young diagrams for symplectic
groups, branching formulae for classical groups, promotion for fans of Dyck
paths, and skew Howe duality; none concerns `q`-Motzkin Hankel determinants.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent refutation.

## Route

Evaluation at `q = 1` is a ring homomorphism `ℤ[q] → ℤ`, so it commutes with
the determinant and, by strong induction, with the recursion. At `q = 1` the
recursion is the first-return recursion of the Motzkin numbers, giving
`1, 1, 2, 4, 9, 21, 51`, and the determinant becomes

`det[[2, 4, 9], [4, 9, 21], [9, 21, 51]] = 36 − 60 + 27 = 3`.

On the printed side `f_3(q) = q^2 + q^3`, so `1^c f_3(1) = 2` for every `c`.

## Falsifier

The refutation would fail if some reading of the printed `f_3` evaluated to
`3` at `q = 1`; the printed range `1 ≤ k ≤ 3` with `k ≢ 1 (mod 3)` contains
only `k = 2, 3`.

## Evidence

Exact computation in `ℤ[q]`, with the determinant expanded over column
subsets, gives `det = q^{11}(1 + q^2 + q^3)` at `n = 3`. For `n = 1, …, 12`
the printed statement holds for `n ≢ 0 (mod 3)` and fails for
`n = 3, 6, 9, 12`, where the determinant at `q = 1` is `3, 5, 7, 9` against
`f_n(1) = 2, 4, 6, 8`. Extending the first range to `0 ≤ k ≤ n` makes every
case `n ≤ 12` hold, with `c_n = 0, 4, 11, 26, 51, 85, 133, 197, 276, 375,
496, 638`. In Lean, the same definitions give the determinant `2` at `q = 1`
for `n = 1, 2` and `f_1(1) = f_2(1) = 2`, where the printed statement holds.
The Lean proof has only the standard axiom closure `propext`,
`Classical.choice`, and `Quot.sound`.

## Triage

Tier 1 external named conjecture, preregistered in issue #10046 before the
probe. The result has `proof_shape: bind-only`, `escape_witness: null`, and
`admission_basis: open-problem-resolution`. Its computational use is a
`certified-instance` with `basis=refutes`: the result negates the closed
claim. Resolution: `refuted`, as printed. The statement with the corrected
range, the three-shifted conjecture and the positivity conjecture are outside
its scope.

## ASSUMED-UNVERIFIED

Whether the journal version, Discrete Math. 342(9) (2019) 2493–2541, keeps
the appendix and the printed range was not checked. The corrected range is
supported only for `n ≤ 12` and is not claimed. The bounded literature check
does not establish exhaustive worldwide novelty, priority, or the absence of
an independent refutation. The Lean kernel does not authenticate the external
source or its version history.
