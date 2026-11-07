---
slug: rowland-sistos-barron-2025-rank-sequences
bibkey: rowlandsistosbarron2025powers
doi: 10.48550/arXiv.2501.14643
url: https://arxiv.org/abs/2501.14643v1
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/RowlandSistosBarronRankSequences
---

# Infinitely many rank sequences of initial rank three

## Problem

Eric Rowland and Jesús Sistos Barrón, *Complexity of powers of a
constant-recursive sequence*, arXiv:2501.14643v1, Section 1, page 2:

> We say that a sequence of integers is a rank sequence if it arises as
> (rank s(n)^M)_{M≥1} for some constant-recursive integer sequence s(n)_{n≥0}.
> For each r ≥ 1, we conjecture that there are only finitely many rank sequences
> associated with sequences s(n)_{n≥0} of rank r, and we are interested in
> enumerating them.

Section 2 defines a constant-recursive sequence by a recurrence with constant
coefficients, nonzero constant coefficient, and validity for all sufficiently
large indices. Its rank is the least recurrence order. The binding conventions
are those of [#19942](https://github.com/the-omega-institute/trureturing/issues/19942):
integer sequences, rational coefficients, tail recurrences, and equality at
every positive exponent rather than eventual equality.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Integer sequence indexed by nonnegative integers | `s : ℕ → ℤ` | All indices |
| A constant-coefficient recurrence on a tail, with nonzero constant coefficient | `HasRecurrence s r` | `LinearRecurrence ℚ`, order `r`, coefficient condition and tail `N` |
| Constant-recursive | `IsConstantRecursive s` | Existence of an order |
| Minimal recurrence size | `rank s` | Natural infimum of admissible orders |
| Positive powers | `rankSequence s` | Domain `ℕ+`; integer pointwise powers |
| Finitely many rank sequences for each initial rank at least one | `claim` | All positive initial ranks and all qualifying integer sequences |
| Refutation | `result` | Negation of the entire claim |

Order zero expresses an eventually zero sequence; the positive initial-rank
restriction is retained. Rational coefficients are the preregistered field;
field-independence is not an additional Lean theorem in this module.

## Motivation

The conjecture asks whether the initial recurrence order controls the number of
possible entire rank sequences. Parameter-dependent cancellations distinguish
infinitely many such sequences even when the initial rank is three.

## Gap

The source separates general rank sequences, determined by roots and their
product relations, from particular rank sequences affected by coefficient
cancellation. The unrestricted Section 1 conjecture includes both. The
settlement addresses that unrestricted assertion; it does not classify the
general rank sequences.

## Route

For natural $p\ge3$, put $s_p(n)=p8^n-4^n-2^n$ and
$F_p(X)=1+X-pX^2$. The distinct nonzero exponential bases imply
$\operatorname{rank}(s_p)=3$. Expansion gives
$s_p(n)^M=(-1)^M\sum_j [X^j]F_p(X)^M\,(2^{M+j})^n$, so its rank is the
number of nonzero coefficients of $F_p^M$.

For fixed $M$ and $0\le j\le2M$, the coefficient is a polynomial in $p$.
At $p=-1$ it is positive, so that polynomial is nonzero and has finitely many
natural roots. Consequently, all but finitely many $p$ have rank $2M+1$ at
exponent $M$. On the other hand,
$[X^2]F_p^M=M(M-1)/2-pM$ vanishes at $M=2p+1$, where the rank is at most
$2M$. For any rank sequence in this family, choose a parameter $p$ realizing
it. Every other parameter realizing the same sequence lies in the finite
exceptional set for $M=2p+1$. Thus each fibre is finite. Finitely many rank
sequences would give finitely many parameters, contradicting unbounded primes.

For each finite bound $L$, the union of exceptional parameter sets for
$1\le M\le L$ is finite. Choose $p\ge3$ outside that union. Then $R_p(M)=2M+1$
through $L$, while cancellation occurs at $2p+1$. This proves in prose that the
first cancellation is unbounded across the family, without identifying its
exact exponent for each parameter.

## Falsifier

The universal finiteness assertion is refuted by the infinite rank-three
family. A finite list of distinct examples alone would not refute it. The
symbolic finite-exception and finite-fibre arguments supply the unbounded
conclusion without asserting that different parameters always give different
rank sequences or that $2p+1$ is the first cancellation.

## Evidence

The source note is
`Library/Eigenstructure/rowlandsistosbarron2025powers.md`.
The canonical module is
`D5/S1/Recurrence/RowlandSistosBarronRankSequences.lean`, with the corresponding
Blueprint Scribe. The only public theorem is
`D5.S1.Recurrence.RowlandSistosBarronRankSequences.result`.
Its axiom closure is contained in $\{\mathtt{propext},\mathtt{Classical.choice},\mathtt{Quot.sound}\}$.
The module has generality `I`, `utility: none`, and admission basis
`open-problem-resolution (#19942; Refuted)`. There is no atom or coverage step.

The public result is a symbolic refutation with no finite certificate and no
utility-refutation exemption. Its four-slot escape registration is unfinished:
[#20338](https://github.com/the-omega-institute/trureturing/issues/20338).
No `declared_validated` registration is claimed. A faithful quantified-finiteness
readout, reconstruction bridge and whole-family sensitivity evidence are absent.

### Exact experiment

The immutable experiment directory is
[trureturing-experiments at ec0476c9a5059125ae488f65fef099ec30b5c335](https://github.com/the-omega-institute/trureturing-experiments/tree/ec0476c9a5059125ae488f65fef099ec30b5c335/docs/reports/rowland-sistos-barron-2025-rank-sequences).
The script is `check.py`, SHA-256
`544161d3a2d4295dfa4e074ec2f4bb89a5891980d4ca579b7bc5cc1f0955fdb6`.
The verified pinned script was executed with
`git -C ../trureturing-experiments show ec0476c9a5059125ae488f65fef099ec30b5c335:docs/reports/rowland-sistos-barron-2025-rank-sequences/check.py | /opt/homebrew/bin/python3 -` (with `pipefail`),
exit 0, with `ALL_CHECKS True`.

The tested scope is: recurrence and positivity at $0\le n<40$ and
Berlekamp–Massey order on 20 terms for $p\in\{3,5,7,11,29\}$; support versus
Berlekamp–Massey order for $(p,M)\in\{(3,6),(3,7),(5,4),(5,11),(7,15),(11,7)\}$;
$1\le M\le2p+2$ for $p\in\{3,5,7,11\}$ and all ten pairwise comparisons in the prime
chain $3,11,29,61,127$, at exponent $2p+1$ for the smaller prime.
In particular $R_3(7)=13$ and $R_{11}(7)=15$.
These are finite exact computations, independent of the unbounded Lean proof.

## Triage

Tier 2 published conjecture; settlement **Refuted**. The preregistration is
[#19942](https://github.com/the-omega-institute/trureturing/issues/19942).
The source and literature checks recorded there identify arXiv v1 and no
journal version in the recorded Crossref title search. Literature-screen
completeness is `ASSUMED-UNVERIFIED`; priority is `repo-prior-exposed`.

### What the settlement shows

| Target item | Status and evidence |
| --- | --- |
| Unrestricted fixed-rank finiteness | **Proved, kernel-checked:** `result` negates `claim`; its argument specializes the alleged finite set to initial rank three. |
| Fixed rank-three family | **Proved, kernel-checked:** private `family_rank_three` gives rank three and constant-recursiveness for every natural $p\ge3$, and is used by `result`. |
| Finite exceptions at each fixed exponent | **Proved, kernel-checked:** private `RSBPoly.finite_bad_parameter`, using `RSBPoly.trinomial_pos` and `RSBPoly.A_ne_zero`, gives finiteness of parameters with a zero coefficient in degrees $0$ through $2M$; private `power_full_rank` gives rank $2M+1$ outside this set. |
| A designated later cancellation for every parameter | **Proved, kernel-checked:** private `RSBPoly.low_coeffs` and `RSBPoly.cancellation` give vanishing at $M=2p+1$; private `power_cancellation_rank` gives the rank bound $2M$. |
| Finite fibres force infinitely many rank sequences | **Proved, kernel-checked:** private `finite_rank_sequence_fibre` gives each fibre's finiteness; `result` uses finite union and unbounded primes to contradict the finite rank-three set. |
| Finiteness restricted to general rank sequences | **Open:** no classification or finiteness proof is supplied for the source's general subclass. |
| Conjecture 5.3: eventual polynomial or pseudo-polynomial behaviour | **Open:** the proof distinguishes entire rank functions and supplies no eventual-behaviour theorem. |
| Arbitrarily delayed first cancellation | **Proved in prose:** the finite-union argument in Route gives a parameter with full support through every prescribed finite exponent bound, together with a later certified cancellation. No separate Lean declaration states this consequence. |
| Exact first cancellation for each $p$ | **Open:** $2p+1$ is a certified cancellation, not a claimed first one. The experiment computes first cancellations only in its stated finite prefixes. |
| Exact checker and comparison values | **Computed:** the pinned experiment entry above, exit 0 and stated SHA-256, gives `ALL_CHECKS True`, $R_3(7)=13$ and $R_{11}(7)=15$. |
| Consequences for the source's other results | **Open boundary / source reading:** this refutation concerns Section 1's unrestricted finiteness claim. The source's general-rank classifications and Conjecture 5.3 are not refuted by it; no other theorem is asserted to change. |

The failure mechanism is coefficient cancellation depending on a free parameter
while the initial exponential support remains fixed. The nearest surviving
question is finiteness within general rank sequences. The symbolic proof does
not give an exact fibre classification or pairwise injectivity of the parameter
map.

## ASSUMED-UNVERIFIED

Completeness of the literature search and absence of an earlier published
settlement remain `ASSUMED-UNVERIFIED`. The source's field-independence
interpretation is recorded in #19942 and is not separately formalized here.
The experiment's finite scope supplies no uniform conclusion beyond its tested
parameters; uniform results are exactly those supported by the named Lean
lemmas. Four-slot escape registration remains unfinished at #20338.
