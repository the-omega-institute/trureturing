---
slug: fiebig-mbirika-spilker-even-descent-dichotomy
bibkey: fiebigmbirikaspilker2025lucas
doi: null
url: https://arxiv.org/abs/2408.14632v2
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/LucasEvenDescent
---

# The even-parameter descent dichotomy for Lucas sequences

## Problem

Conjecture 5.2 of arXiv:2408.14632v2, as printed:

> Set `U_n := U_n(p, q)`, and let `m >= 1` and `n` in `Z`. Assume that both `p` and `m` are even.
> If `U_{2n} = 0 (mod m)` and `U_{2n+1} = q^n (mod m)`, then exactly one of the following two
> conclusions occur: (i) `U_n = 0 (mod m)`, or (ii) `U_n = m/2 (mod m)` where `n = c * e_U(m)/2`,
> where `c` is some odd integer and `e_U(m)` is the entry point of `m` in `(U_n)`.

The paper adds a second sentence: "Can we give conditions for when Conclusion (i) versus
Conclusion (ii) occurs?"

## Motivation

The doubling hypotheses are the standard entry into descent arguments for Lucas sequences, and the
even-parameter case is the one the paper's own Convention 3.20 excludes from its main development.
A dichotomy with an explicit index characterisation is what lets the descent be iterated.

## Gap

The conjecture asserts an exclusive disjunction, so neither conclusion may be derived on its own:
a proof has to produce both the disjunction and the exclusivity. The paper states it from
Mathematica data and does not prove it.

## Route

Work in the unit group with the companion matrix `M = !![p, -q; 1, 0]`, whose integer powers carry
`U` and `V` as entries and trace. The doubling hypotheses say `M^{2n}` is a scalar, and the Cassini
identity relates `U_n`, `U_{n+1}` and `q^n`. The load-bearing arithmetic identity is
`2 A B^2 = B * (2A(B - p'A)) + A * (2A(p'B - qA)) + 2 q A^3`, which yields `2 A q^n = 0` and hence
`2 U_n = 0` in `ZMod m`. The zero set of `U` is an additive subgroup of `Z`, so the entry point is
its generator and the index characterisation in conclusion (ii) follows.

## Falsifier

Even `p`, even `m`, and an index `n` satisfying both doubling hypotheses for which neither
conclusion holds, or for which both hold, would refute it.

## Evidence

- Module: `D5/S1/Recurrence/LucasEvenDescent.lean`, frozen.
- Theorem: `conjecture_five_two`, stating the conclusion as `Xor` of the two alternatives, with
  conclusion (ii) carried as `U_n = m/2` together with `Even (entryPoint)` and an odd `c` with
  `n = c * (entryPoint / 2)`.
- Supporting public results in the same module: `two_mul_lucas_eq_zero`,
  `lucas_eq_zero_iff_entry_dvd`, `entry_point_spec`, `lucas_even_descent`.
- The hypothesis `Int.gcd q m = 1` is carried explicitly. It is not printed inside the sentence of
  Conjecture 5.2; it comes from the paper's own Convention governing that subsection.

## Triage

`theorem`. The printed dichotomy is settled, and because conclusion (ii) is stated with its index
characterisation, the `Xor` also answers the paper's follow-up sentence: conclusion (ii) occurs
exactly when the entry point is even and the index is an odd multiple of half of it, and
conclusion (i) occurs otherwise. That reading of the follow-up sentence is the orchestrator's, not
the paper's own phrasing.

**Settled beyond what the conjecture asks.** The conjecture assumes `p` even, and
`conjecture_five_two` keeps that hypothesis so that its statement is the printed one. The
supporting theorem `lucas_even_descent` in the same module proves the same dichotomy with **no
parity hypothesis on `p` at all**, over `p : ZMod m` and any unit `q`, its docstring saying so
explicitly. So the frozen result covers odd `p` as well; only the headline declaration is
restricted, and only for fidelity to the printed sentence.

The evenness of `m` is likewise less of a restriction than it looks. The two-torsion input
`two_mul_lucas_eq_zero` is stated over **any** commutative ring and carries no hypothesis on `m`
at all; over `ZMod m` with `m` odd, `2` is a unit, so it forces conclusion (i) outright. That last
step is a one-line consequence rather than a separate frozen declaration, so the registry records
it as a consequence and not as a proved node.

Not settled here: the behaviour when the coprimality hypothesis fails.

## ASSUMED-UNVERIFIED

The identification of the printed `m/2` with the repository's `((m / 2 : N) : ZMod m)` is a
reading of the paper's notation. The coprimality hypothesis was located in the paper's Convention
rather than in the sentence of the conjecture, which is an orchestrator reading of the paper's
scoping. First-publication priority is not established, and no forum search was performed. The
citation graph of the source paper was read on 2026-09-12 through one aggregator and contained a
single citing work, which does not address this conjecture; that is one retrieval on one day
through one index, not a survey.
