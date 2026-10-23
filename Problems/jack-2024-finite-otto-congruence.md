---
slug: jack-2024-finite-otto-congruence
bibkey: jack2026conjugacy
doi: 10.1007/s00233-026-10614-w
url: https://arxiv.org/abs/2411.16284
triage: theorem
motivation_gids:
  - D5/S3/FiniteGroups/FiniteOttoCongruence.result
---

# Finite Otto congruence quotients are cancellative

## Problem

Trevor Jack, *Answering Five Open Problems Involving Semigroup Conjugacy*,
arXiv:2411.16284v1, Section 9, Problem 9.4, p. 14; Semigroup Forum 112
(2026), 450–466, DOI 10.1007/s00233-026-10614-w:

> Is there a finite semigroup for which ∼o is a congruence and S/∼o is not cancelative?

The answer is negative. Section 2, p. 2 defines the relation by:

> ∀a, b ∈ S (a ∼o b ⇔ ag = gb and bh = ha for some g, h ∈ S).

Both witnesses lie in $S$; no identity is adjoined.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| finite semigroup | `claim` quantifies over `S : Type` with `Semigroup S` and `Finite S` | arbitrary finite carrier, with no chosen enumeration |
| Otto conjugacy | `Otto` | exactly the two existential witness equations in Section 2 |
| is a congruence | `OttoIsCongruence` | multiplication compatibility; `otto_refl`, `otto_symm`, `otto_trans` prove equivalence |
| quotient is cancelative | `QuotientCancelative` | both representative cancellation implications |
| no such finite semigroup | `result : claim` | universal negative answer; empty carriers satisfy the cancellation statement vacuously |

## Motivation

The source's Problem Four constructs an infinite semigroup with an Otto
congruence and a noncancellative quotient. Problem 9.4 asks whether finiteness
can be retained. Finite idempotent powers prevent that failure.

## Gap

The external named question is preregistered in
[#17635](https://github.com/the-omega-institute/trureturing/issues/17635).
The source explicitly asks the question. No answer was found in the inspected
literature and repository scope described below; completeness of that screen
is `ASSUMED-UNVERIFIED`.

## Route

The module is `D5/S3/FiniteGroups/FiniteOttoCongruence.lean`, with one public
settling theorem, `D5.S3.FiniteGroups.FiniteOttoCongruence.result`. The four
public definitions are the literal conventions of #17635. Its private
helpers are consumed by the cancellation proof. Their classification and
that of `result` is `proof_shape: bind-only`; the module's admission basis is
`open-problem-resolution (#17635; Proved)`. Its utility is `none`: the proof
is structural over arbitrary finite semigroups and contains no enumeration
or fixed numerical certificate.

The frozen `D5.S0.Certificates.Algebra.BergmanQuestion15Refutation.positivePower`
supplies the positive product $a^{k+1}$ at index $k$. Mathlib's
`exists_idempotent_in_compact_subsemigroup` supplies an idempotent in the
finite subsemigroup of positive powers, using the discrete topology.
`SemiconjBy.mul_left` composes the witness equations in `otto_trans`.

## Falsifier

A finite associative multiplication table with multiplication-compatible
Otto conjugacy and a failure of either representative cancellation law would
contradict `result` under its stated definitions. This criterion uses the
original two-witness relation, without replacing it by a certificate or by a
relation on a monoid with an adjoined identity.

## Evidence

The kernel-checked settling declaration is
`D5.S3.FiniteGroups.FiniteOttoCongruence.result`. Its axiom closure is contained
in `{propext, Classical.choice, Quot.sound}`. The Blueprint displays the full
universal implication and both cancellation laws.

The only public theorem is an escape-audit target. Its four-slot registration
is unfinished: [#17715](https://github.com/the-omega-institute/trureturing/issues/17715)
names the missing source reconstruction, exact occurrence bridge,
whole-family variation/sensitivity and actual observational-dependence
evidence. No successful Reg mirror or `declared_validated` status is claimed.

### Experiment

The independent finite enumeration is in
[trureturing-experiments at commit 1ea0f434ab3c6f8b8803a90a4b0b73c27fe24977](https://github.com/the-omega-institute/trureturing-experiments/tree/1ea0f434ab3c6f8b8803a90a4b0b73c27fe24977/docs/reports/jack-2024-finite-otto-congruence).
The program is `docs/reports/jack-2024-finite-otto-congruence/check.py`;
run `python3 check.py` in that directory. Exit code: 0; result: `ALL_OK`.
SHA-256: `62c4082d7c5952937d8663b016643759922a7715cbd8fbb16e9542023f62c5df`.
The tested scope is every labelled semigroup of orders 1, 2, 3 and 4:

| Order | Associative tables | Otto congruences | Quotient check |
| --- | ---: | ---: | --- |
| 1 | 1 | 1 | abelian group |
| 2 | 8 | 8 | abelian group |
| 3 | 113 | 113 | abelian group |
| 4 | 3492 | 3468 | abelian group |

These counts are computed, not Lean enumeration theorems. The structural
cancellation theorem applies to every finite order independently of this
experiment.

## Triage

### What the settlement shows

- **Mechanism — kernel-checked.** `exists_idempotent_power` gives an index
  $k\geq2$ with $a^{k+1}$ idempotent. Writing $n=k+1$, `otto_stable_power`
  gives $a\sim_o a^{n+1}$, and `otto_idempotents` relates every two
  idempotents. Under multiplication compatibility,
  `idempotent_class_identity` makes their common class a two-sided identity,
  `inverse_class` gives $[a^{n-1}]$ as an inverse representative, and
  `otto_mul_swap` gives $ab\sim_o ba$. These private declarations are on
  `result`'s proof path; their statements express the class laws on
  representatives.
- **Strength — kernel-checked cancellation.** `quotient_cancelative` and
  `result` prove both left and right cancellation for every finite semigroup,
  including the empty case vacuously. **Finite abelian group — proved in
  prose for nonempty $S$.** The quotient is finite as the image of $S$.
  Choose an element to obtain an idempotent power. The preceding identity,
  inverse and swap laws descend to its congruence classes, giving a finite
  abelian group. The module does not construct a Lean `CommGroup` instance.
  **Converse — proved in prose.** In an abelian group the equation $ag=gb$
  becomes $ag=bg$ and cancellation gives $a=b$; equality conversely has
  witnesses $a,a$. Thus Otto conjugacy is equality, and every finite abelian
  group occurs as its own quotient. No nonemptiness is claimed for the
  empty carrier.
- **Consequence — proved in prose from `result`.** The noncancellative
  quotient of the source's infinite Problem Four example cannot be realized
  by a finite semigroup. The source's infinite construction remains valid;
  no other source theorem is changed by this finite obstruction. Finiteness
  is essential: the source's infinite example violates the conclusion.
- **Classification — open.** Characterize the finite semigroups whose Otto
  conjugacy is multiplication compatible. The experiment computes that
  3468 of the 3492 labelled order-four semigroups have this property. It is
  not a classification at arbitrary order.
- **Experiment — computed.** The pinned experiment in Evidence exhausts
  labelled semigroups of orders 1–4 and checks the quotient's commutativity,
  identity, inverses and cancellation whenever Otto conjugacy is a
  congruence. The command, exit code, script SHA-256 and exact counts are
  stated there. No enumeration claim beyond order 4 is made.
- **Literature — open completeness (`ASSUMED-UNVERIFIED`); source reading.** The arXiv v1
  source was read. The source and the inspected screen do not give an
  answer to Problem 9.4. The Semigroup Forum version of record, Liu–Wang,
  Communications in Algebra 53 (2025), 375–389, and Clifford–Cummings–Teymouri
  (2011) remain unread in full. The probe's reported screen also inspected
  arXiv:2301.04252v3, 2605.00041, 2101.00324v2, 1503.00915v2 and 2503.02148;
  no answer was identified in that scope. This is not an exhaustive novelty
  certificate.

## ASSUMED-UNVERIFIED

Literature completeness and external priority remain unverified because the
journal version's final question section and the other full texts named in
Triage have not been read. The source fidelity and kernel-checked negative
answer do not establish worldwide priority. The four-slot escape audit is
unfinished under #17715. The general classification in Triage remains open.
