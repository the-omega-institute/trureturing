---
slug: rule-163
bibkey: hofmann2025rule163
doi: null
url: https://oeis.org/A392003
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence
---

# Rule 163 even subsequence and OEIS conjectures

## Problem

OEIS A392003 records Hofmann's formula

```text
a(n) = (7*2^n - 9 + 5*(-1)^n) / 6.
Conjecture: a(2*n) = A266753(n).
```

OEIS A266753 records the Rule 163 single-seed cellular automaton and the conjectures

```text
a(n) = 5*a(n-1)-4*a(n-2) for n>2.
G.f.: (1-x+2*x^2) / ((1-x)*(1-4*x)).
Empirical a(n) = (7*4^n - 4)/6 for n>1.
a(n) = 4*a(n-1) + 2, n>1.
```

The source conventions are documented in the Library note
[`hofmann2025rule163`](../Library/StatisticalMechanics/hofmann2025rule163.md) and preregistration [#22909](https://github.com/the-omega-institute/trureturing/issues/22909).

### Statement echo

The settling declaration is `D5.S3.StatisticalMechanics.CellularAutomata.Rule163EvenSubsequence.result : claim`. Its five conjuncts state, respectively: $B(2n)=A(n)$ for $n\ge1$; $(A(n):\mathbb Q)=(7\cdot4^n-4)/6$ for $n>1$; $A(n)=4A(n-1)+2$ for $n>1$; $(A(n):\mathbb Z)=5(A(n-1):\mathbb Z)-4(A(n-2):\mathbb Z)$ for $n>2$; and the formal power-series identity
$\operatorname{PowerSeries.mk}(n\mapsto(A(n):\mathbb Z))(1-X)(1-4X)=1-X+2X^2$.

## Motivation

The claim combines the complete even-subsequence identity with the closed form, the first and second recurrences, and the generating-function identity for the source sequence. The formalization keeps the integer-lattice evolution, nonquiescent exterior, finite binary window and coefficient carriers literal.

## Gap

The source entries present these assertions as conjectures or empirical formulas. The bounded literature screen recorded in #22909 found no settling reference. Its completeness is `ASSUMED-UNVERIFIED`; the screen does not establish global absence or priority.

## Route

The proof uses the existing integer-lattice `row` owner and defines Wolfram rule 163, the finite-window binary sequence $A$, and the rational sequence $B$. A Boolean table and an induction establish that every positive-time row has all-one exterior and central word $100(10)^{n-1}$. The binary encoding therefore obeys $A(n+1)=4A(n)+2$. Induction gives $6A(n)+4=7\cdot4^n$, including $n=1$; substitution gives the even-subsequence identity. Eliminating the constant term gives the second-order recurrence. Coefficient comparison, with $A(0)=1$, $A(1)=4$ and the second-order recurrence from degree three onward, proves the formal power-series identity.

## Falsifier

A counterexample to the all-integer row invariant, to the stated finite-window orientation, or to any quantified conjunct would falsify the claim. The exceptional values are part of the statement: $A(1)=4$ while $4A(0)+2=6$, and $A(2)=18$ while $5A(1)-4A(0)=16$; these explain the published ranges and the $2X^2$ correction.

## Evidence

The kernel-checked result is `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.result`, frozen in `Golden/Frozen/state/D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.lean.json`. The public result has axiom closure contained in `{propext, Classical.choice, Quot.sound}`.

The independent finite experiment is in `the-omega-institute/trureturing-experiments` at commit `543c6e1f3bdaa0d1c2325175c9d5b689c58135db`, path `docs/reports/rule-163-even-subsequence/check.py`, sha256 `393f5bf922e569fae046125a37dc1b5024d157013b8000f3b8de69008065df82`. The command `python3 docs/reports/rule-163-even-subsequence/check.py` exits 0 and checks the published prefixes and the evolution through time 300; it is corroborating finite evidence, not the unbounded proof.

The four-slot escape audit for `D5/S3/StatisticalMechanics/CellularAutomata/Rule163EvenSubsequence.result` remains unfinished under [issue #27131](https://github.com/the-omega-institute/trureturing/issues/27131). No `declared_validated` status is asserted without the required CI `current` reading.

## Triage

### What the settlement shows

- **Proved — complete row invariant.** The nonquiescent exterior is all 1 at time 1 and remains all 1; the interior word is $100(10)^{n-1}$ for every positive time. Evidence: the live induction through `row_word` in `result`.
- **Proved — affine encoding step.** Appending the bits $10$ multiplies the binary encoding by 4 and adds 2 for every transition from a positive-time row. Evidence: `D5.S3.StatisticalMechanics.CellularAutomata.Rule163EvenSubsequence.result`, whose live proof uses `A_succ`.
- **Proved — extended closed form.** $(A(n):\mathbb Q)=(7\cdot4^n-4)/6$ holds already at $n=1$, extending the source's $n>1$ range. Evidence: `result`, whose live proof uses `A_closed`.
- **Computed — exceptional initial recurrences.** Exact integer evaluation gives $A(1)=4\ne4A(0)+2=6$ and $A(2)=18\ne5A(1)-4A(0)=16$. Evidence: `check.py`, command `python3 docs/reports/rule-163-even-subsequence/check.py`, exit 0, script sha256 `393f5bf922e569fae046125a37dc1b5024d157013b8000f3b8de69008065df82`; its tested scope is the finite evolution and published prefixes through time 300. No uniform extension beyond that computation is claimed for these exact numerical checks.
- **Open — neighbouring questions.** Yurramendi's additional binary-as-decimal identities, A266752 base-10 formulas and arbitrary initial configurations are outside the five-clause claim and have no settling declaration here.

The result changes the status of all five selected source assertions from conjectural or empirical to proved under the literal conventions above. It does not settle the neighbouring questions listed as open.

## ASSUMED-UNVERIFIED

Literature completeness, global absence of prior proof and publication priority remain `ASSUMED-UNVERIFIED`. The finite experiment does not replace the quantified Lean proof. The escape audit remains unfinished under issue #27131 until its required CI `current` DTR reading is available.
