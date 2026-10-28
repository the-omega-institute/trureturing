---
slug: manabe-2024-restricted-amalgamation-nim-conjecture-1
bibkey: manabe2024restrictedamalgamation
doi: 10.48550/arXiv.2411.14488
triage: theorem
motivation_gids:
  - D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim.result
url: https://arxiv.org/abs/2411.14488v1
---

## Problem

Hikaru Manabe, *An Amalgamation Nim with Restriction*,
arXiv:2411.14488v1, Section 3, Conjecture 1, page 14:

> For n ∈ Z≥0, we have the following (i) and (ii). (i) If the Grundy number of a position (x, y, z) is 2n, then x ⊕ y ⊕ z = 2n or x ⊕ y ⊕ z = 2n + 1. (ii) If the Grundy number of a position (x, y, z) is 2n + 1, then x ⊕ y ⊕ z = 2n or x ⊕ y ⊕ z = 2n + 1.

The game is Definitions 4–5: strictly reduce any one of three natural
pile sizes, or merge two piles each at least two, allowing both placements
of the sum and zero. Preregistration:
[#19861](https://github.com/the-omega-institute/trureturing/issues/19861).

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Three nonnegative pile sizes | Natural arguments of `move`, `grundy` and `claim` | Zero is included |
| Definition 5 sets (1)–(3) | First three alternatives of `move` | All strict reductions |
| Definition 5 sets (4)–(6) | Last three alternatives of `move` | Both piles at least two; both placements |
| Grundy value is mex of option values | `grundy`, with the existing `AbukuEnforceNimberDomination.mex` | Private `move_decreases` and `grundy_eq` remove the well-founded guard on options |
| Both even and odd implications, for every natural n | Two conjuncts of `claim`, proved by `result` | Neither implication is dropped |
| Termination measure in the binding conventions | `size`: stone total plus number of nonempty piles | An implementation measure, not an extra game hypothesis |

The four public definitions preserve the binding expressions in #19861.
The measure and recursion guard add no hypothesis to the universal result.

## Motivation

The public theorem
`D5.S0.Certificates.Games.ManabeRestrictedAmalgamationNim.result`
settles both parts of Conjecture 1 for every position. Its mathematical
proof establishes an exact value, not a finite approximation.
The imported `D5.S0.Certificates.Games.AbukuEnforceNimberDomination.mex`
supplies the minimum-excluded definition; that owner's game theorem is
not on this module's dependency path.

## Gap

Four-slot escape registration of the sole public theorem `result` is
unfinished: [#20798](https://github.com/the-omega-institute/trureturing/issues/20798).
No Reg registration is delivered. The quantified conjunction of guarded
disjunctions needs a lawful enrolled readout, exact source reconstruction,
source selection, intervention/sensitivity and observational-dependence
evidence. This gap does not weaken the Lean theorem.

## Route

Write $a=x/2$, $b=y/2$, $c=z/2$ using natural quotients, and put
$h=a\mathbin{\mathrm{xor}}b\mathbin{\mathrm{xor}}c$ and
$p=(x\bmod2)\mathbin{\mathrm{xor}}(y\bmod2)\mathbin{\mathrm{xor}}(z\bmod2)$.
Let $B$ mean that some pair of $a,b,c$ is positive and bitwise disjoint;
let $E$ mean that all three are positive and pairwise bitwise disjoint.
Put $\delta=1$ exactly when $B\land\neg E$, and otherwise $\delta=0$.
The private `exact_formula` proves
$g(x,y,z)=2h+(p\mathbin{\mathrm{xor}}\delta)$.

The private `merger_low_bit` shows that a legal merger preserving the
high XOR reverses the corrected low bit. `exclusion` rules out the
proposed value at every option; `lower_blocks` and `last_value` provide
every smaller value. Strong induction on `size` and mex then give
`grundy_formula`, `exact_formula` and `result`.

## Falsifier

A position violating either implication of `claim` would refute the
settlement. The stronger formula also predicts every Grundy value under
the stated six-option relation. The finite computation below tests these
predictions independently; the universal result is kernel-checked Lean.

## Evidence

The source module and Blueprint Scribe have the same owning path under
`D5/S0/Certificates/Games/ManabeRestrictedAmalgamationNim`.
`result` proves the expanded `claim`. The axiom closure of every public
declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

### Finite experiment

[Experiment entry](https://github.com/the-omega-institute/trureturing-experiments/tree/ffbf16ab17fc78fc53ff70b7bd8850aade42a8d4/docs/reports/manabe-2024-restricted-amalgamation-nim-conjecture-1)
at commit `ffbf16ab17fc78fc53ff70b7bd8850aade42a8d4`, script `check.py`.
Command:
`python3 /Users/auric/.sshx/7d2cc64fd2186d0cad557293/attempt-1/experiment.py`,
exit 0. Script SHA-256:
`9fe9d0293073584a03f7249591ae254519e12932685709745b6a2d2f5dab30c4`.
For all 68,921 positions with $0\le x,y,z\le40$, there are zero mismatches
for Conjecture 1, the exact formula, and equality of the zero set with
Definition 6's P-set. Computed examples are $g(0,2,4)=7$ with XOR $6$,
$g(2,2,0)=0$, and $g(2,4,6)=1$ with XOR $0$.

## Triage

### What the settlement shows

- **Settlement — proved, kernel-checked:** `result` proves both clauses
  of Conjecture 1 under the exact binding conventions, at all natural
  pile sizes.
- **Stronger result — proved, kernel-checked:** private `exact_formula`
  proves $g=2h+(p\mathbin{\mathrm{xor}}\delta)$ universally. Private
  `xor_half` identifies $h=(x\mathbin{\mathrm{xor}}y\mathbin{\mathrm{xor}}z)/2$;
  `low_value_lt` bounds the corrected low bit by two.
- **Mechanism — proved, kernel-checked:** `merger_low_bit` states that
  every legal merger retaining the high XOR reverses the corrected low
  bit. `merger_exclusion` and `even_merge_target` use that fact.
- **Adjacent zero-set characterization — proved in prose from the exact
  formula:** both summands are nonnegative and the low bit is below two,
  so $g=0$ is equivalent to $h=0$ and $p=\delta$. No additional public
  theorem asserts this characterization.
- **Definition 6 comparison — computed:** equality with the paper's
  complete P-set is checked only on $0\le x,y,z\le40$ by the experiment
  above. A separate universal Lean equivalence with Definition 6 is open.
- **Sharpness — computed:** $g(0,2,4)=7\ne6$ and $g(2,4,6)=1\ne0$
  show that replacing the adjacent-pair conclusion by exact equality
  with ordinary XOR fails. These values are in the stated finite run.
- **Other source results — literature reading:** Theorem 2 states the
  P-position set independently of Conjecture 1. The settlement supplies
  the conjectured adjacent-pair Grundy property; the source's full
  Definition 6 equivalence is not separately proved by this module.
- **Open frontier — open:** four or more piles and unrestricted
  amalgamation Nim. The proof's three-pile correction is not asserted
  for those games.
- **Novelty — literature reading; completeness ASSUMED-UNVERIFIED:**
  the source history and the literature screen in #19861 and the search
  evidence cover the named sources only. No exhaustive publication-priority
  claim is made.

## ASSUMED-UNVERIFIED

The arXiv history lists v1. The CGTC V abstract retains a conjecture.
Seven later-author papers were keyword-screened, not audited for implicit
general theorems: 2501.15786, 2504.18606, 2510.03088, 2601.18715,
2603.10414, 2605.14321 and 2609.05358. Citation-service coverage and unread
references leave literature completeness ASSUMED-UNVERIFIED; no
zero-citation claim is made. The unfinished escape audit is #20798.
