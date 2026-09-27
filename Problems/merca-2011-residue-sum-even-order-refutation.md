---
slug: merca-2011-residue-sum-even-order-refutation
bibkey: merca2011sums
doi: null
url: https://cs.uwaterloo.ca/journals/JIS/VOL14/Merca/merca3.pdf
triage: theorem
motivation_gids:
  - D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.result
---

# Merca's even-order residue-sum conjecture refutation

## Problem

Merca, Journal of Integer Sequences 14 (2011), Article 11.9.1, defines the
remainder operation on printed page 2:

> When m is integer and n is a positive integer the quotient of m divided by n is
> ⌊m/n⌋ and the value m mod n = m − n⌊m/n⌋ is the remainder (or residue) of
> the division.

Section 3.2 on printed page 17 defines the multiplicative order:

> For every positive integer m and every integer a relatively prime to m, we denote
> by ord_m(a) the multiplicative order of a modulo m, i.e., the smallest positive
> integer n such that a^n ≡ 1 (mod m), namely
> ord_m(a) = min {n ∈ N∗ | a^n ≡ 1 (mod m)}

Section 4 on printed page 23 states the conjecture:

> **Conjecture 1.** Let a and m be relatively prime positive integers. If a−1 and m
> are relatively prime and ord_m(a) is even then
> Σ_{i=1}^{ord_m(a)} (a^i mod m) = m · ord_m(a) / 2.

The formal `claim` retains both positivity conditions, both coprimality
conditions, even multiplicative order, the inclusive index range from 1 through
the order, and the least non-negative remainder operation. Its equality doubles
both printed sides to express the exact integer statement in natural numbers.

| Printed expression | Formal expression |
| --- | --- |
| positive integers `a`, `m` | `0 < a`, `0 < m` with `a m : ℕ` |
| `a` and `m` relatively prime | `Nat.Coprime a m` |
| `a−1` and `m` relatively prime | `Nat.Coprime (a - 1) m` |
| `ord_m(a)` | Mathlib's `orderOf (a : ZMod m)` |
| `ord_m(a)` is even | `Even (orderOf (a : ZMod m))` |
| `Σ_{i=1}^{ord_m(a)} (a^i mod m)` | `residueSum m a` over inclusive `Finset.Icc 1 (orderOf (a : ZMod m))` |
| `sum = m · ord_m(a) / 2` | `2 * residueSum m a = m * orderOf (a : ZMod m)` |

## Motivation

The witness is `(a, m) = (2, 15)`. Both coprimality conditions hold,
`ord_15(2) = 4`, and the residues are `2, 4, 8, 1`, whose sum is `15`.
The printed right side is `15 * 4 / 2 = 30`, so the conjectured equality fails.

Exact enumeration for `m < 80` and representatives `0 < a < m` found 761 pairs
satisfying both coprimality conditions and having even order. Among them, 94 fail
Conjecture 1, and every failing modulus in that bounded enumeration is composite.
This is a finite observation, not a theorem about prime moduli. The paper's
Conjecture 2, which assumes prime `m`, is a separate problem and is not asserted
here.

## Gap

Issue #9191 preregistered the literal published statement, counterexample, and
literature check before the proof. The Journal of Integer Sequences paper is the
published source and has no arXiv version. The arXiv API queries
`all:"Inequalities and Identities Involving Sums of Integer Functions"` and
`au:Merca AND all:"multiplicative order"` each returned zero matches.

MathDB searches for `Merca sums of integer functions conjecture`,
`sum of a^i mod m multiplicative order even`,
`residues of powers modulo m sum order`, and `Merca 11.9.1` found no entry for
this conjecture. The checked repository and open-pull-request scope likewise
contained no prior settlement. These bounded searches do not establish
exhaustive publication absence or publication priority.

## Route

The formalisation encodes `ord_m(a)` as Mathlib's
`orderOf (a : ZMod m)`. At `(a, m) = (2, 15)`, the equality
`orderOf (2 : ZMod 15) = 4` follows from the fourth power being one and the
smaller positive exponents being non-one. Evaluation then gives
`residueSum 15 2 = 15`. Instantiating the universal claim at this pair would
force `2 * 15 = 15 * 4`, namely `30 = 60`, a contradiction.

## Falsifier

The refutation would fail if the encoded order were not the least positive
exponent, if `%` did not denote the least non-negative remainder, if the sum
omitted or added an endpoint, if either source coprimality condition failed at
`(2, 15)`, or if the two sides were equal there. The formal definitions and
kernel-checked instance retain each of these links.

## Evidence

- Lean theorem:
  `D5/S0/Certificates/MercaResidueSumEvenOrderRefutation.result`.
- Freeze event:
  `sha256:8d2a32178a09b7ab7ed57d7c0136d7bc46a6e6cb90209c51c2624cc8829fd1b0`.
- Module statement identity:
  `sha256:53f89b140fcab9a43b269447e4bec0289d57b2a40da2fbf78496109af399b87e`.
- Result declaration identity:
  `sha256:0cc98c5f52b867debaeaa9cf379f4deb2b10bb05e7dd3463df709caeb84b541e`.
- The Freeze event has no project-level frozen prerequisites; the sole import is
  pinned Mathlib's `Mathlib.GroupTheory.OrderOfElement` module.
- The axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.
- PDF text extracted with layout preservation and split on form feeds places the
  quoted passages on printed pages 2, 17, and 23, respectively.
- The three Lean fidelity examples check the `(2, 15)` order and sum, the full
  `(2, 15)` hypothesis bundle, and the positive control `(3, 7)`, where the order
  is `6`, the residue sum is `21`, and the conjectured equality holds.
- Exact enumeration over representatives `0 < a < m` with `m < 80` gives 761
  qualifying pairs and 94 failures; every failing modulus in this range is
  composite.

## Triage

`theorem`; first-tier external named conjecture, preregistered in issue #9191.
The public theorem has `proof_shape: bind-only`: it instantiates the printed
universal statement at `(2, 15)` and closes the concrete order and residue sum
by kernel evaluation. Its `escape_witness` is `none`, and its
`admission_basis` is `open-problem-resolution`. Its computational use is a
`certified-instance` with a typed `refutes` edge from `result` to `claim`.
There is no atom and no digestion coverage edge.

## ASSUMED-UNVERIFIED

Literature completeness is `ASSUMED-UNVERIFIED`: the bounded searches cannot
exclude every prior resolution or establish publication priority. The search
seat's OEIS and Crossref readings and its rate-limited Semantic Scholar reading
remain seat-self-reported. Source-to-Lean fidelity and proof-shape classification
remain semantic review judgments; the Lean kernel checks the formal statement
and proof, not their equivalence to the cited prose.
