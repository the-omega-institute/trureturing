---
slug: luschny-a323206
bibkey: luschny2019a323206
doi: null
url: https://oeis.org/A323206
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Invariants/LuschnyA323206Parity.result
---

# Luschny's A323206 parity conjecture

## Problem

Peter Luschny's OEIS A323206, revision 52, gives the NAME:

> A(n, k) = hypergeometric([-k, k+1], [-k-1], n), square array read by ascending antidiagonals for n,k >= 0.

Its COMMENTS conjecture is:

> Conjecture: A(n, k) is odd if and only if n is even or (n is odd and k + 2 = 2^j for some j > 0).

The source is [OEIS A323206](https://oeis.org/A323206), with the locator and
statements in `Library/RecurrenceComposition/luschny2019a323206.md`.
There is no source DOI or arXiv identifier. The binding finite interpretation is

$$
A(n,k)=\sum_{j=0}^{k}\frac{(-k)_j(k+1)_j}{(-k-1)_j\,j!}n^j,
\qquad (a)_0=1,\quad(a)_j=\prod_{t=0}^{j-1}(a+t).
$$

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| All nonnegative $n,k$ | Natural arguments of `A` and universal binders of `claim` | Zero is included. |
| Terminating hypergeometric array | `A`, using `ordinaryHypergeometricCoefficient` on $-k,k+1,-k-1$ and degrees $0\le j\le k$ | Literal finite convention in #22903. |
| “is odd” | Integer witness $a$, its rational image equal to $A(n,k)$, and `Odd a` | Integrality is a conclusion, not a hypothesis. |
| “if and only if” | The equivalence in `claim` | Both directions. |
| “n is even or (n is odd and …)” | `Even n` or the conjunction with `Odd n` | Same alternatives and grouping. |
| “k + 2 = 2^j for some j > 0” | Natural exponent $e$, $0<e$, $k+2=2^e$ | Only the bound variable is renamed. |

Empty products and zero powers, including $0^0$, equal one. For
$0\le t<j\le k$, the lower factor $-k-1+t$ is nonzero; the factorial is
nonzero. No infinite hypergeometric evaluation at a pole is used.

## Motivation

The target is the entire published two-parameter classification, preregistered
in [#22903](https://github.com/the-omega-institute/trureturing/issues/22903).
`D5/S1/Recurrence/Invariants/LuschnyA323206Parity.result` proves its literal
`claim`. Its admission basis is `open-problem-resolution (#22903; Proved)`;
its proof shape is bind-only and its utility is none. All auxiliary theorems
are private steps used by the settling proof. No independent content witness
is asserted.

## Gap

The bounded literature screen recorded in #22903 found no settlement in the
inspected material. It includes the OEIS entry and related arrays, arXiv
identifier and subject searches, published Abate–Whitt TeX, selected weighted
Catalan papers, Zenodo metadata and citation metadata. The generalized Catalan
and ballot identities and ordinary Catalan parity are established ingredients.
Completeness is ASSUMED-UNVERIFIED: linked 1992/1993 full texts were not obtained,
citation services limited the returned sets, and uninspected paper bodies
remain outside the screen. This is no claim of first-publication priority.

## Route

Write the degree-$j$ coefficient as the integer ballot expression

$$
b(k,0)=1,\qquad
b(k,j)=\binom{k+j}{j}-\binom{k+j}{j-1}\quad(1\le j\le k).
$$

Here $b$ is explanatory notation, not another Lean definition. The private
`coeff_eq` proves this identity from Pochhammer and binomial identities.
The private integer polynomial `z` has these coefficients, and `z_cast_eq_A`
proves that its rational image is the literal source array.

Two hockey-stick sums and the central-binomial Catalan identity yield

$$
\sum_{j=0}^{k}b(k,j)
=\binom{2k+1}{k+1}-\binom{2k+1}{k+2}=C_{k+1}.
$$

The private `row_sum_catalan_q` checks this identity. Reduction modulo two
sends even arguments to the constant coefficient and odd arguments to this
row sum. The imported
`D5.S1.Recurrence.Invariants.CatalanCompositionSquareParity.binary_catalan`
is used in `catalan_mod_two_iff`, through its shifted `catalanSeries` and
Mathlib coefficient rewrites, to obtain $C_{k+1}\equiv1\pmod2$ exactly when
$k+2=2^e$. Since $k+2\ge2$, $e>0$ follows. The existing owner supplies the
binary support theorem; this module does not claim a new Catalan parity result.

## Falsifier

A pair $n,k\in\mathbb N$ for which the finite sum has no integer value,
or whose integer value fails either direction of the stated parity
equivalence, contradicts `claim`. A finite search cannot establish the
universal result. Different moduli or hypergeometric parameters are outside
this claim.

## Evidence

The Lean module is `D5/S1/Recurrence/Invariants/LuschnyA323206Parity.lean`;
its public theorem is `result : claim`. The Scribe displays the full expanded
claim and carries one `OpenProblemResolutionClaim` with resolution Proved.
The frozen state is
`Golden/Frozen/state/D5/S1/Recurrence/Invariants/LuschnyA323206Parity.lean.json`.
The axiom closure of every public declaration is contained in
{propext, Classical.choice, Quot.sound}.

Escape registration for the sole public theorem `result` is unfinished:
[#23031](https://github.com/the-omega-institute/trureturing/issues/23031).
The missing evidence is a compiled adapter for the nested universal
integer-witness conjunction, with its faithful realization/readout bridge
and whole-family variation and sensitivity. No `declared_validated`
registration is claimed.

### Exact experiment

The [experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ef93c7c67a217d1b030a8f84de42c2274805ab9d/docs/reports/luschny-a323206-parity)
is pinned to commit `ef93c7c67a217d1b030a8f84de42c2274805ab9d`.
Its program is `docs/reports/luschny-a323206-parity/check.py`, SHA-256
`c723f2b596d81056e4dcfa7c273919a4a38936b451ad6f6bae34c156e9be5626`.
Command: `git -C /Users/auric/trureturing-experiments show ef93c7c67a217d1b030a8f84de42c2274805ab9d:docs/reports/luschny-a323206-parity/check.py | python3 -`
(with pipefail); exit 0, `ALL_CHECKS_OK`.
It checks 72 source examples ($0\le n\le8$, $0\le k\le7$), 5151 coefficients
($0\le j\le k\le100$), 101 row sums ($0\le k\le100$), and 2121 parity pairs
($0\le n\le20$, $0\le k\le100$). The row sums also agree with independent
Catalan convolution. These are exact finite computations, not a universal
proof.

## Triage

| Target item | Status and evidence kind | Evidence |
| --- | --- | --- |
| Hypergeometric-to-ballot integer coefficient bridge and integral witness $z$ | Proved; kernel-checked | Private `coeff_eq` and `z_cast_eq_A`, used by public `result`. |
| Even/odd evaluation split modulo 2 | Proved; kernel-checked | Private `sum_eval_even`, `sum_eval_odd` and `odd_z_iff`, used by `result`. |
| Ballot row sum is $C_{k+1}$; positive binary exponent support is $k+2=2^e$, $e>0$ | Proved; kernel-checked | Private `row_sum_catalan_q` and `catalan_mod_two_iff`, the latter applying the imported `binary_catalan`; both used by `result`. |
| Exact checker: 72 source examples, 5151 coefficients, 101 row sums, 2121 parity pairs | Computed | The pinned exact experiment above, exit 0, `ALL_CHECKS_OK`, at exactly the stated finite ranges. |
| Other moduli/parameters; completeness of the external literature screen | Open | No extension is asserted; the literature-access limits are listed in Gap and ASSUMED-UNVERIFIED. |

### What the settlement shows

Proved in this module: the decisive mechanism is the integer-coefficient
bridge followed by the two evaluations in characteristic two. Even inputs
see coefficient one; odd inputs see $C_{k+1}$. The result is uniform for all
natural $n,k$, including their zero boundaries. The positive exponent is
forced by $k+2\ge2$, not an extra assumption on $k$.

Proved in this module: the even/odd evaluations use the integral coefficient
bridge and the coefficient sum. No analytic convergence hypothesis is used,
and no restriction on the size of either index is introduced. A separate
general theorem for arbitrary integer polynomials is an open formalization
candidate; it is not an additional public declaration in this settlement.

Open: replacing modulus two or changing the hypergeometric parameters
requires new coefficient and residue analyses. No uniform extension is
claimed from the finite experiment. The inspected source states no theorem
conditional on this conjecture, so no downstream source theorem is assigned
a changed status.

## ASSUMED-UNVERIFIED

Completeness and priority of the external literature search remain
ASSUMED-UNVERIFIED, with the precise unread sources and query limits recorded
in #22903. The formal statement follows the finite reading fixed there;
no analytic infinite-series assertion or other-modulus generalization is
included. Escape audit #23031 remains unfinished and is independent of the
kernel-checked settlement.
