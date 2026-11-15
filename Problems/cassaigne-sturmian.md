---
slug: cassaigne-sturmian
bibkey: cassaigne2008extremal
doi: 10.1051/ita:2008003
url: https://www.numdam.org/item/10.1051/ita:2008003.pdf
triage: theorem
motivation_gids:
  - D5/S1/Words/Complexity/CassaigneSturmianCharacterization.result
---

# Equality of asymptotic word invariants does not characterize Sturmian words

## Problem

Julien Cassaigne, *On extremal properties of the Fibonacci word*, RAIRO
42(4), 701–715, printed p. 707, Open problem 2, asks:
“How can this equality be explained? Does it characterize Sturmian words?”
The equality is $\operatorname{ind}^*(u)=\rho^*(u)$.
The characterization question is interpreted as the implication for every
infinite binary word. The source's explanation question is outside this claim.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Infinite word over the binary alphabet $\{a,b\}$ | `claim` quantifies over every `Nat → Bool` | `true` represents $a$; indices start at zero. |
| Factor language $L_n(u)$ | `CassaigneRecurrenceTransport.factorLanguage` | Existence of a starting index and its `List.ofFn` block, including length zero. Finite containment is a bounded starting index with pointwise `getD` equality. |
| Exponent is length divided by least positive period | `HasPeriod`, `per`, `exponent` | Positive periods use the quantified bounded `getD` equality; every finite word has one. |
| Asymptotic index over tails of factor lengths | `indexAt`, `indStar` | The extended nonnegative-real tail infimum and supremum preserve infinity. |
| Recurrence function in $\mathbb N\cup\{+\infty\}$ | `HasRecurrenceBound`, `recurrenceCandidates`, `recurrenceFunction` | Finite candidates are embedded in `ENat`; no finite bound gives top. |
| Recurrence quotient is the limsup of $R_u(n)/n$ | `recurrenceRatio`, `rhoStar` | Top is preserved in `ENNReal`; the value at zero does not alter a tail. |
| Irrational slope in $[0,1]$, some intercept, and either floor or ceiling coding | `floorCoding`, `ceilCoding`, `IsSturmian` | Both source codings and every conjunction are retained. |
| Equality implies Sturmianity for every binary word | `CassaigneSturmianCharacterization.claim` | No recurrence or finiteness hypothesis is added. |
| Negative answer | `CassaigneSturmianCharacterization.result` | The literal type is the negation of the closed claim. |

## Motivation

The settling module has `generality: I`, utility
`kind=certified-instance; basis=refutes`, and admission basis
`open-problem-resolution (#23441; Refuted)`.
The characterization fails even on words with finite recurrence bounds at
every factor length and a finite common asymptotic invariant.

## Gap

The literature screen recorded in #23441 found no settlement in its inspected
scope: the source paper, the relevant citing-work screen, arXiv, OpenAlex,
Zenodo, MathOverflow, the repository and public Lean settlement indexes.
Masáková–Pelantová, arXiv:0809.0603v2, addresses a stronger finite-scale
condition involving infinitely many factors, rather than equality of these
limsup invariants. Literature-search completeness is `ASSUMED-UNVERIFIED`.

## Route

Put $v_k(n)=f(\lfloor n/k\rfloor)$, where $f$ is the existing golden word,
and $\varphi=(1+\sqrt5)/2$. Transitions in $v_k$ synchronize modulo $k$.
Aligned periods decode to periods of $f$ after a bounded loss at the endpoints;
a nonaligned period can have only a bounded overlap. Recurrence bounds
transport in both directions. Vanishing endpoint errors then preserve the
two normalized invariants. Fibonacci return gaps and long repetitions give
$\operatorname{ind}^*(f)=\rho^*(f)=2+\varphi$.
For $k\ge2$, $v_k$ contains both constant binary bigrams; no irrational
mechanical coding in the source can contain both.

## Falsifier

The kernel-checked `result` uses $k=2$ and refutes the implication by the
word `replicated 2 goldenWord`. Its invariants equal the same finite value,
yet `vk_not_sturmian` excludes the required mechanical representation.

## Evidence

The settling declaration is
`D5.S1.Words.Complexity.CassaigneSturmianCharacterization.result`.
The Scribe displays the complete negated quantified claim and acknowledges
[the source](../Library/Automata/cassaigne2008extremal.md).
The public result is the designated refutation result (`basis=refutes`) and
is exempt from four-slot escape registration (CLAUDE.md §3.9).
The escape audit for the supporting public theorems and published owners is
unfinished under [#26320](https://github.com/the-omega-institute/trureturing/issues/26320).
No completed registration is claimed for those targets.

### Experiments

[Published finite checker](https://github.com/the-omega-institute/trureturing-experiments/tree/55be271d998dc376d192e3076471a7f71b99ea8f/docs/reports/cassaigne-open-problem-2),
`check.py`, SHA-256
`be7346cfc6cd482ee6c75474953a6c40b48d70691eb3264beafc11d542350e00`.
Command: `python3 /tmp/op-cassaigne08/check.py`; exit 0,
`ALL_CHECKS_OK`. The script was read from that immutable revision.
It checks the 2584-letter Fibonacci prefix, $(aba)^3$ at position 5,
all four bigrams for $k=2,\ldots,6$, and the finite-prefix factor counts
$p_{v_k}(n)=n+2k-1$ for $2k+1\le n\le69$. Repetition samples have lengths
$2k+1$, 20 and 40.

The finite checker supplies no asymptotic proof.

## Triage

1. **Proved, kernel-checked:** for every $k\ge2$, the exact common invariant
   is $2+\varphi$ and the replicated word is not Sturmian.
   Evidence: private `CassaigneSturmianCharacterization.nominated_invariant_values`
   and public `CassaigneRecurrenceTransport.vk_not_sturmian`.
2. **Proved, kernel-checked:** every positive uniform replication preserves
   the extended-real recurrence limsup (`rhoStar_replicated`);
   golden replication preserves the asymptotic index (`golden_indStar_replicated`).
3. **Proved in prose from the named kernel-checked bounds:** every nominated word has a finite recurrence bound
   at each length. For $k\ge2$ and length $n$, set $m=\lfloor n/k\rfloor+2$.
   Set $q=m+5$; `Nat.le_fib_self` gives $m+1\le F_{q+1}$. Private `CassaigneGoldenRecurrence.golden_recurrence_bound_fib`
   gives a source bound $M=m+F_{q+2}$.
   Private `CassaigneRecurrenceTransport.recurrence_bound_replicated` gives
   the finite bound $kM+2k$ for $v_k$ at length $n$.
   Adding only finite recurrence bounds therefore does not rescue the implication.
4. **Computed:** the published finite checker passes on exactly the scope
   in Experiments. These observations are not used as asymptotic proofs.
5. **Open:** other finite-scale Sturmian characterizations and a
   classification of all equality cases are not settled here.
6. **Open:** an exact finite recurrence-function formula is not supplied.
   The private Fibonacci upper bound `golden_recurrence_bound_fib` is
   kernel-checked and has the asymptotic precision used by `golden_rhoStar_eq_sharp`.

### What the settlement shows

The failure mechanism is loss of the binary mechanical-word structure under
letter replication while both limsup invariants remain unchanged.
The two equalities survive every positive replication of the golden word;
non-Sturmianity holds for every replication factor at least two.
The family also has finite recurrence bounds, by the derivation from the bounds above.
The forward equality for Sturmian words is not refuted, nor is the separate
finite-scale characterization of Masáková–Pelantová. No other theorem of
the source is negated by this counterexample. Consequences requiring the
false converse retain only their conditional status; an exhaustive list of
such consequences is unverified.

## ASSUMED-UNVERIFIED

Worldwide literature completeness and a classification of all equality
cases are unverified.
Four-slot escape audits remain unfinished under #26320.
The finite-prefix complexity formula is computed only on the stated ranges;
no uniform complexity theorem is claimed here.
