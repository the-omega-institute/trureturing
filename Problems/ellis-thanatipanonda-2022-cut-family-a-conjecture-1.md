---
slug: ellis-thanatipanonda-2022-cut-family-a-conjecture-1
bibkey: ellis2022cutfamilya
doi: 10.1016/j.dam.2022.08.027
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.result
url: https://arxiv.org/abs/2203.02457v1
---

## Problem

Paul Ellis and Thotsaporn Aek Thanatipanonda, *The Arithmetic-Periodicity
of cut for C = {1, 2c}*, arXiv:2203.02457v1, Section 7, page 18;
Discrete Applied Mathematics 322 (2022), 391–403,
DOI 10.1016/j.dam.2022.08.027:

> Let X to be a non-empty set of even numbers, each of which is at least 4. Let Y to be a non-empty set of odd numbers, each of which is at least 5. Let x = 2c and y be the smallest elements of X and Y, respectively.

> Family A: C = {1, 3} ∪ X, or C = {1, 3} ∪ X ∪ Y.

> The nim-sequence for all games of cut in this family are all precisely (0, 1)^c (+2).

This is Conjecture 1. Preregistration:
[#19674](https://github.com/the-omega-institute/trureturing/issues/19674).
The settling theorem is
`D5.S0.Certificates.Games.EllisThanatipanondaCutFamilyA.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| A move cuts a pile into $d+1$ positive parts, $d\in C$ | `G`: `Fin (d + 1)` option, positivity and exact sum | All legal options occur |
| Nim-sum of the part values; mex of option values | `G`: `List.ofFn`, right fold of natural xor, existing `mex` | The guard only ensures well-founded recursion and is inactive for Family A options |
| Nonempty even $X$, all elements at least $4$ | First two hypotheses of `claim` | Arbitrary natural sets, including infinite sets |
| No extra odd cuts, or nonempty odd $Y$ with elements at least $5$; its least element $y$ | Disjunction in `claim` | $Y=\varnothing$ gives the first alternative; nonempty natural $Y$ has a least member, which the conclusion does not use |
| Smallest even cut $2c$ | $2c=\operatorname{sInf}X$ | Nonempty natural sets have a least member; $c\ge2$ follows |
| Sequence $(0,1)^c(+2)$, beginning at $n=1$ | Conclusion of `claim`, proved by `result` | $G_C(n)=2\lfloor(n-1)/(2c)\rfloor+((n-1)\bmod2)$ for every $n\ge1$ |

The natural subtraction, integer quotient and remainder are the literal
binding conventions. The recursion also defines values outside Family A;
`guard_value` and `G_equation` identify its legal-option recursion on the
positive cut-sets used in the proof. No assertion about an invalid zero
cut is needed.

## Motivation

The frozen settling node proves the entire Family A statement, rather
than a finite initial segment. Its only direct D5 owner is
`D5.S0.Certificates.Games.AbukuEnforceNimberDomination.mex`.
This supplies the set-valued minimum-excluded definition; that owner's
game theorem is not on this module's dependency path.

## Gap

Four-slot escape registration of the public theorem `result` is unfinished:
[#19690](https://github.com/the-omega-institute/trureturing/issues/19690).
No Reg mirror or validated registration is supplied. A faithful dependent
source reconstruction and enrolled readout for the quantified cut-sets,
minimum, parity constraints and positive pile sizes, together with the
required intervention and sensitivity evidence, remain missing.

Literature completeness is `ASSUMED-UNVERIFIED`. The base case
$C=\{1,3,2c\}$ is prior art; no claim of a new method for that case or of
exhaustive priority is made. The source's other cut families and questions
are outside this settlement.

## Route

Put $b=2c$ and $F(n)=2\lfloor(n-1)/b\rfloor+((n-1)\bmod2)$.
Strong induction on $n$ replaces each part value by $F$.
For an odd cut the number of parts is even. Their xor has low bit
$n\bmod2$, whereas $F(n)$ has low bit $(n-1)\bmod2$.
For an even cut the number of parts exceeds $b$. Positivity of the parts
forces the sum of their quotient terms below $\lfloor(n-1)/b\rfloor$.
The natural xor bound by the sum then forces the option value below $F(n)$.
Thus no legal option has the proposed value.

Every smaller value is reached with one of three cuts, $1$, $3$ or $b$.
The constructed lists are two parts, four parts containing an equal pair,
or a leading part followed by $b$ equal parts. Equal pairs cancel under
xor. The private `reachability` theorem proves that these choices cover
every value below $F(n)$; `exclusion` excludes $F(n)$. The private
`nim_formula` combines both facts with `G_equation` and `csInf_eq_iff`.
`result` verifies the cut hypotheses from the literal Family A definition.

## Falsifier

A Family A cut-set and positive pile size with a different nim-value
would contradict `result` under the stated definitions and axiom closure.
A different legal-option convention would require a separate fidelity
argument. A previously published full-family solution would change the
literature assessment, rather than the kernel-checked conclusion.

## Evidence

The compiled module has the public definitions `G`, `claim` and the public
theorem `result`. The axiom closure of every public declaration is
contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The Blueprint displays the full defining expressions and the expanded
settling proposition with one Proved resolution claim.

### Finite experiment

[Experiment entry](https://github.com/the-omega-institute/trureturing-experiments/tree/b1c81d4a510e0c66b51d53548b9b3ee913d48194/docs/reports/ellis-thanatipanonda-2022-cut-family-a-conjecture-1)
at commit `b1c81d4a510e0c66b51d53548b9b3ee913d48194`.
Commands executed on the exact script bytes extracted from that commit:
`python3 /Users/auric/.sshx/1456a70f5c9412afd6705c56/attempt-1/experiments/check.py`
and `python3 /Users/auric/.sshx/1456a70f5c9412afd6705c56/attempt-1/experiments/check_moves.py`;
both exit 0 and report `RESULT PASS`.
SHA-256 of `check.py`:
`93d02c9162321fde0c53382c9de665a7e2ab5a8889e86ec9e1963038feee4509`.
SHA-256 of `check_moves.py`:
`598556e64bb396ab74f315463d84944600944fc982e6bae8c9e80aaa91ed076e`.

Computed scope: brute-force option enumeration for 24 fixed-seed random
Family A cut-sets, $c\in\{2,3,4,5\}$, with and without $Y$, and
$1\le n\le26$; every value agrees with $F(n)$. The explicit-move check
covers $b\in\{4,6,8,10,12\}$ and $1\le n\le400$: positive parts,
correct sums, legal cuts, and values covering $[0,F(n))$ without $F(n)$.
These computations are finite checks; `result` supplies the universal claim.

## Triage

### What the settlement shows

- **Mathematics — proved, kernel-checked.** `result` proves Conjecture 1
  for both Family A alternatives with the fixed conventions and every
  positive pile size.
- **Stronger compiled form — proved, kernel-checked.** The private
  `nim_formula` requires only $c>0$, $1,3,2c\in C$, and
  $\forall d\in C,\ d\bmod2=1\lor2c\le d$. It asserts the same formula
  at every positive pile size. In particular no finiteness assumption is
  needed, and the proof allows arbitrary odd cuts alongside those three
  required cuts. This is an internal proof statement, not an additional
  public theorem.
- **Mechanism — proved, kernel-checked.** `odd_exclusion` excludes the proposed
  value when the number of parts is even. `quotient_budget` bounds the
  sum of quotient terms, and `large_exclusion` bounds the option value
  strictly below the proposed value when the number of parts exceeds
  $2c$, using `xor_le_add` and `xs_le_sum`. `reachability`
  uses the explicit `option_one`, `option_three` and `option_even`
  constructions. `exclusion` combines the two exclusion cases.
- **Finite checks — computed.** The experiment entry above supplies the
  exact scopes, commands, exit codes and hashes for the 24 cut-sets and
  the explicit moves through pile size 400. No wider computational scope
  is asserted.
- **Novelty — literature reading; completeness open.** Dailly–Duchêne–
  Larsson–Paris, *Partition games*, arXiv:1803.02621v3, Proposition 8,
  DOI 10.1016/j.dam.2020.05.032, states the base case
  $C=\{1,3,2c\}$; it is not on this module's dependency path. The full
  family is the present settlement. The literature screen in #19674
  covers the arXiv and journal author copies, Semantic Scholar, OpenAlex
  and the later-author works named there; exhaustive coverage remains
  `ASSUMED-UNVERIFIED`.
- **Tracked tree — computed inventory.** The delivery is on branch
  `lane/math/op-et2203`; its mathematical module, Scribe, emitted
  Markdown, Library note, dossier and canonical state record form the
  publication unit. `git status --porcelain` and the branch inventory
  are the evidence for its final committed state.
- **Extension boundaries — open.** Necessity of each of the three
  required cuts, sharpness outside the stated cut restriction, and the
  source's other cut families are not asserted by `result`. Conjecture 1
  can now be used as a theorem with its stated Family A hypotheses;
  no theorem about another source question or conditional dependency is
  included in this module.
- **Consequences for other source problems — literature reading with an
  open premise.** Section 7 states that proving arithmetic periodicity
  for Families A and B would imply Conjecture 1 of DDLP. `result` supplies
  the Family A formula. Family B, including the source's Conjecture 2,
  is outside this result, so the combined DDLP conclusion is not claimed.
  Conjecture 3 for Family C and the Family D game are also outside it.

## ASSUMED-UNVERIFIED

The source and literature checks are those recorded in #19674.
Citation coverage outside the named services is incomplete and not every
later-author proof was independently read. No exhaustive novelty claim
is made. The unfinished escape audit is disclosed in #19690 and is
separate from the verified Lean proof.
