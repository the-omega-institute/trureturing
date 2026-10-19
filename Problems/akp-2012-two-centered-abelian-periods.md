---
slug: akp-2012-two-centered-abelian-periods
bibkey: avgustinovich2012critical
doi: 10.1051/ita/2011121
triage: theorem
motivation_gids:
  - D5/S1/Words/TwoCenteredAbelianPeriods.result
url: https://www.numdam.org/item/ITA_2012__46_1_3_0/
---

# Two centered abelian period lengths

## Problem

Avgustinovich, Karhumäki and Puzynina, *On abelian versions of critical factorization theorem*, RAIRO–ITA 46(1), Open problem 6.2, ask:

> Let k be an integer. Does there exist a non-periodic word w and integers l₁, l₂, such that w contains a central abelian 2k-power of length l₁ or l₂ at every position?

The answer is negative for every $k\geq1$, every finite alphabet and every pair of block lengths. The public theorem is `D5.S1.Words.TwoCenteredAbelianPeriods.result`.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Biinfinite word over a finite alphabet | $w:\mathbb Z\to\mathrm{Fin}(r)$, every natural $r$ | Alphabet labels are immaterial. |
| Position between $w_i$ and $w_{i+1}$ | Integer cut $i$ | The first block starts at $i-lk+1$. |
| Central abelian $2k$-power with period length $l$ | `CentralAbelianPower w k l i` | All $2k$ consecutive length-$l$ blocks have the same letter counts; $l>0$. |
| Two lengths, one available at every position | The disjunction inside the universal integer-position hypothesis of `claim` | Both lengths are fixed globally. |
| No non-periodic example | `result : claim` concludes `Periodic w` | A positive natural ordinary period is produced. |
| Positive exponent | $1\leq k$ | Nonempty centered powers; no assertion about $k=0$. |
| Natural lengths may equal zero | Positivity is part of each central-power predicate | A zero length never satisfies that predicate, so only the other length remains. |

## Motivation

The source states that one centered period length forces periodicity and constructs a non-periodic word using three lengths in Theorem 3.2. This settlement fills the two-length case. Its settling GID is `D5/S1/Words/TwoCenteredAbelianPeriods.result`.

## Gap

The theorem settles the stated universal rigidity question. The completeness of the prior-settlement literature screen remains `ASSUMED-UNVERIFIED`; no worldwide priority claim follows.

## Route

Fix a letter and form its signed cumulative count $C$. Set $F(n)=C(n+p)-C(n)$ and $G(n)=C(n+q)-C(n)$. The centered-square alternative makes the product of the two second differences zero. An exact identity then expresses the increment of a bounded integer flux as the negative square of the mixed difference $F(n+q)-F(n)$. The flux is antitone and constant on both tails. On each tail it is a bounded coboundary; constant drift must vanish. Both tail values, and hence the flux and mixed difference everywhere, are zero. The common-multiple window increment then has constant first difference, recovering letterwise periodicity and finally word periodicity.

The module uses the frozen `AbelianBorderQuestionDefs.letterCount`, Mathlib `fwdDiff`, `Pi.single` and `birkhoffSum`. The proof is classified bind-only under the named-open-problem exception; no escape witness is claimed. Its admission basis is `open-problem-resolution (#17818; Proved)` and its utility is `none`.

## Falsifier

A non-periodic biinfinite word over a finite alphabet with two globally fixed centered abelian period lengths at every cut and $k\geq1$ would contradict `result`. One-sided powers, three allowed lengths, or a position-dependent unbounded set of lengths do not satisfy this theorem's hypothesis.

## Evidence

`D5/S1/Words/TwoCenteredAbelianPeriods.lean` proves `result` from the literal `claim`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. Its Blueprint expands the complete proposition.

The escape audit of `result` is unfinished: [#19073](https://github.com/the-omega-institute/trureturing/issues/19073). No validated four-slot registration is claimed.

The finite diagnostic is published in [the experiments repository at commit 80038634f2c0f440ee08fd49471857125507a9e2](https://github.com/the-omega-institute/trureturing-experiments/tree/80038634f2c0f440ee08fd49471857125507a9e2/docs/reports/avgustinovich-karhumaki-puzynina-2012-two-centered-abelian-periods). Command: `python3 -I /Users/auric/trureturing-experiments/docs/reports/avgustinovich-karhumaki-puzynina-2012-two-centered-abelian-periods/check.py`; exit 0, `ALL_OK`; script SHA-256 `a91796fa13defe4035c84f000d61f74b1d576b4de9b74b70db5fd9632b9edc7b`. The directory is an external input and can be relocated without changing the program. This diagnostic is not used in the proof.

## Triage

- **Mathematics — kernel-checked.** `result` proves the full negative answer. The consumed private declarations `central_square`, `energy_identity`, `finite_defects`, `no_defects` and `periodic_increment` supply the reduction, identity, rigidity and reconstruction. The public surface is the three necessary definitions and `result`.
- **Literature — open completeness boundary.** No prior answer was identified in the recorded source, Fici–Puzynina arXiv:2207.09937v2 and full Huova–Karhumäki–Saarela–Saari chapter screen. The additional citing-paper and author-publication coverage is `ASSUMED-UNVERIFIED`. Related one-sided Sturmian results and the unrestricted bounded centered-square problem have different hypotheses.
- **Prior disclosure — open priority boundary.** `repo-prior-exposed`; this record asserts the formal result, not independent discovery.
- **Scope.** The independent mathematical check and implementation use codex-cli without delegated research seats. Producer, publication and worktree-state accounting belongs to the PR provenance and runner result rather than mathematical evidence.
- **Checker — computed.** For the binary alphabet, every $1\leq p<q\leq6$, and for the ternary alphabet, every $1\leq p<q\leq3$, the valid-window shift graph has only unbranched cyclic strongly connected components, each with word period $\operatorname{lcm}(p,q)$, and no path joins two cyclic components. The negative control permits lengths $1,\ldots,8$ on the binary alphabet: 52,666 valid windows, 69 cyclic components, and the rigidity test fails as required. The command, exit code and script identity are in Evidence. No uniform theorem is inferred from this finite check.

### What the settlement shows

- **Kernel-checked:** `result` makes the two-length centered condition sufficient for ordinary periodicity at every positive exponent. The reduction to two middle blocks explains why the exponent does not change the conclusion.
- **Kernel-checked private consequence:** `squares_lcm_period` gives $\operatorname{lcm}(p,q)$ as a period when the centered-square alternative holds. When $p,q>0$, `result` uses its positive least common multiple as the ordinary period. A zero length cannot occur in a valid central power and leaves the single positive length. No minimal-period or sharp period-length claim is made.
- **Proved in prose from the source plus the settlement:** the threshold for the number of available centered period lengths is two versus three. The settlement excludes one or two, while source Theorem 3.2 supplies a non-periodic example with three. This threshold is not a new Lean theorem in the module.
- **Explanatory mechanism:** bounded antitone integer flux and its two tail coboundaries turn a pointwise alternative into a global mixed-difference identity. The exact private identity and its use are part of the compiled proof chain; this description is not an additional public theorem.
- **Open:** a minimal-period classification, extensions to infinite alphabets or weakened positionwise hypotheses, and corresponding higher-dimensional rigidity statements. They are outside `claim`.
- **Source dependence:** source Theorem 3.2 and the one-sided Sturmian constructions remain compatible with the answer, since their hypotheses differ. No source theorem is asserted to depend on an affirmative answer to Open problem 6.2.

## ASSUMED-UNVERIFIED

Completeness of the literature and priority screen is unverified. The source and named survey/chapter are a bounded screen; additional citing papers, author publications and all subsequent literature have not been exhaustively checked. The convention at $k=0$ is outside the theorem's $k\geq1$ scope. The unfinished escape-registration evidence is tracked in #19073.
