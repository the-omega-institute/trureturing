---
slug: oudra-a248186-cubic-floor
bibkey: oudra2023a248186
doi: null
url: https://oeis.org/A248186/internal
triage: theorem
motivation_gids:
  - D5/S3/ArithSums/OudraA248186CubicFloor.result
---

# Oudra's A248186 cubic floor formula

## Problem

OEIS A248186 asks for the least positive $k$ such that
$1/18-\sum_{h=1}^{k}1/(h(h+1)(h+2)(h+3))<1/n^3$ and conjectures
$a(n)=\lfloor r n+r^2/n-1\rfloor$ for $n>2$, where $r=3^{-1/3}$.
The source convention uses natural indices, real summands, strict comparison, and
the integer floor after real subtraction. The delivered claim retains existence of
the source sequence at every positive index and the formula for every such sequence.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Least positive threshold index from the reciprocal-product sum | `D5.S3.ArithSums.OudraA248186CubicFloor.residual` and `IsSourceSequence` | The finite sum, positive index condition, real arithmetic, and strict inequality are literal. |
| $r=3^{-1/3}$ | `D5.S3.ArithSums.OudraA248186CubicFloor.r` | The real base and exponent are literal. |
| Formula for every $n>2$ | `claim` and `result` | The existential sequence clause and all quantifiers are retained. |

## Motivation

The settling declaration is `D5/S3/ArithSums/OudraA248186CubicFloor.result` and
has admission basis `open-problem-resolution (#24012; Proved)`. This is an external
named problem with no atom, so the chain form is deposit-uncovered. The public result
is the designated open-problem settlement; the auxiliary declarations are private.
The source is recorded in `Library/Asymptotics/oudra2023a248186.md`.

## Gap

The preregistration's bounded literature screen found no proof or counterexample for
the A248186 formula. Literature-screen completeness is `ASSUMED-UNVERIFIED`; the
screen does not establish absence of an unindexed or later source.

## Route

The reciprocal-product summand telescopes, giving
$\operatorname{residual}(k)=1/[3(k+1)(k+2)(k+3)]$. Set
$b=rn+r^2/n$. The identity $r^3=1/3$ gives
$3(b^3-b)=n^3+1/(3n^3)$. For $n>2$ this value lies strictly between
$n^3$ and $n^3+1$. The polynomial $q(x)=3(x^3-x)$ is strictly increasing
for $x\ge1$, and its integer values at consecutive floor points bracket the
threshold. The least admissible index is therefore $\lfloor b\rfloor-1$,
which is the displayed floor after subtracting one. The cases $n=1,2$ have
least index one.

## Falsifier

An $n>2$ for which the least positive admissible index differs from the displayed
floor would refute the claim. A failure of the telescoping identity or either strict
floor bracket would be a concrete proof obligation failure. Finite data alone does
not refute or prove the universal statement.

## Evidence

The kernel-checked settling theorem is
`D5.S3.ArithSums.OudraA248186CubicFloor.result`. Its axiom closure is contained
in `{propext, Classical.choice, Quot.sound}`. The Scribe result node displays the
complete claim and carries the single `OpenProblemResolutionClaim(Proved)` for this
dossier. The module has `generality: I` and `utility: none`.

The escape audit is unfinished under
[issue #24748](https://github.com/the-omega-institute/trureturing/issues/24748).
No `declared_validated` registration is asserted without the required CI `current`
reading.

### Experiment

The independent checker is in
[trureturing-experiments](https://github.com/the-omega-institute/trureturing-experiments/tree/4093bd7a859a5be8bec8c9615ef3150c9e427071/docs/reports/oudra-a248186),
commit `4093bd7a859a5be8bec8c9615ef3150c9e427071`.
The command is `python3 check.py`; exit code 0; script SHA-256 is
`eda2a4d6a3054c01f38b36fd5c1fe4b4e058ef0a7a94f72f2b45ce5c7364e4d1`.
It reproduces the finite source data and checks all 9,998 cases
$3\le n\le10000$, ending `ALL_CHECKS_OK`. This supports the argument and is not
the universal proof.

## Triage

| Target item | Status | Evidence |
| --- | --- | --- |
| The reciprocal-product sum telescopes to $1/[3(k+1)(k+2)(k+3)]$. | Proved | Kernel-checked `residual_formula` in the delivered module. |
| The explicit $b=rn+r^2/n$ has cubic-image overshoot strictly between $n^3$ and $n^3+1$ for $n>2$; integer floor bracketing gives the least index. | Proved | Kernel-checked `q_overshoot`, `candidate_data`, and `candidate_isleast`. |
| The independent checker reproduces finite data and all 9,998 cases $3\le n\le10000$; output ends `ALL_CHECKS_OK`. | Computed | The experiment entry above, command `python3 check.py`, exit 0, and the pinned script SHA-256. |
| Extensions to A248187/A248188 and other reciprocal products are outside this theorem. | Open | No declaration or computation in this delivery addresses those extensions. |

### What the settlement shows

The decisive mechanism is the telescoping identity followed by the cubic overshoot
and integer floor bracket. The argument is uniform for every natural $n$ in the
claim, with no finite cutoff. It settles the exact A248186 formula and does not
settle A248187, A248188, or other reciprocal products. Results that relied on the
A248186 conjecture may now use this exact formula within the stated conventions.

## ASSUMED-UNVERIFIED

Literature completeness beyond the bounded screen, including blocked endpoints and
unindexed sources, remains `ASSUMED-UNVERIFIED`. The finite checker is supporting
computation and does not replace the kernel proof. The escape audit remains
unfinished under issue #24748.
