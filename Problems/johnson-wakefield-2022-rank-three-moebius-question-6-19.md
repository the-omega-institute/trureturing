---
slug: johnson-wakefield-2022-rank-three-moebius-question-6-19
bibkey: johnsonwakefield2024incidencenearring
doi: 10.26493/1855-3974.2894.b07
url: https://arxiv.org/abs/2204.07158v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.result
---

# Johnson–Wakefield Question 6.19: nonvanishing in rank three

## Problem

John Johnson and Max Wakefield, *A non-associative incidence near-ring with a generalized Möbius function*, Ars Mathematica Contemporanea 24, #P2.03, Question 6.19, ask:

> Is there a rank 3 non-modular connected matroid $M$ such that $\mathcal M(M,-1)=0$?

The answer for finite matroids is negative. The precise source definitions and finite-carrier conventions are fixed by [#19762](https://github.com/the-omega-institute/trureturing/issues/19762). The Library source is `Library/FiniteGeometry/johnsonwakefield2024incidencenearring.md`.

### Statement echo

| Source clause | Lean counterpart | Scope |
| --- | --- | --- |
| Lattice of flats $L(M)$, ordered by inclusion | `Flats M`, the subtype of `Matroid.IsFlat` | Literal binding convention |
| Rank and top rank | `rk M F`, `M.eRank` | Extended rank converted to a natural number; finite carrier |
| Definition 5.1, $x\le a\le y\le b\le z$, with diagonal value one and all other flag values zero | `IsJFunction` | The rectangle equation, rather than the product formula, defines the public predicate |
| Definition 6.2, the partial-flag sum with exponent $3r(M)-r(x)-r(y)-r(z)$ | `MoebiusPoly` | All sums are finite; exponent subtraction is in $\mathbb N$ |
| Rank three, connected, nonmodular | `claim` hypotheses `M.eRank = 3`, `Connected M`, and `¬ Modular M` | Connectedness is retained literally |
| No such vanishing example | `result : claim` | Every solution of the defining rectangle equation has nonzero evaluation |
| Finite matroid setting | `Finite α` with `M : Matroid α` | No infinite-carrier assertion |

## Motivation

The evaluation has the exact incidence interpretation
$\mathcal M(M,-1)=2(b-v)$, where $v$ counts rank-one flats and $b$ counts rank-two flats. The frozen settling declaration is `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.result`. Its admission basis is `open-problem-resolution (#19762; Proved)`; its proof shape is bind-only, using consumed private adapters to pinned Mathlib. This settlement does not claim an independent escape witness.

## Gap

The source's Theorem 6.16 proves modular-to-zero. Its Remark 6.18 supplies a connected nonmodular rank-four vanishing example, so the converse fails without a rank restriction. Question 6.19 isolates the rank-three possibility. The delivery establishes nonvanishing there. It supplies no classification in arbitrary rank and no new public converse theorem.

## Route

The namespace below is `D5.S3.Combinatorics.Matroids.JohnsonWakefieldRankThreeMoebius`.

The private `mu_isJ` supplies the product of ordinary Möbius values as an actual solution of the rectangle equation; `j_eq_mu_product` gives uniqueness on partial flags. The latter uses `IncidenceAlgebra.moebius_inversion_top` and `IncidenceAlgebra.moebius_inversion_bot`. Summing by the middle element and separating the four rank layers gives `Graded.rank_three_mu_evaluation`; `moebius_eval_neg_one` transfers the identity to the lattice of matroid flats.

The private `nonmodular_disjoint_lines` extracts two rank-two flats whose intersection has rank zero. The private `nonmodular_more_lines` applies `Configuration.HasLines.card_le`, `Configuration.HasLines.hasPoints` and `Configuration.HasPoints.existsUnique_point`: equality of point and line counts would force the two lines to have a common rank-one flat. Thus $b>v$. The settling `result` combines the evaluation identity with that strict cardinality inequality over $\mathbb Z$.

## Falsifier

A finite rank-three matroid satisfying the stated nonmodularity and rectangle-equation hypotheses with zero polynomial evaluation would contradict `result`. A rank-four example, a function not satisfying Definition 5.1, or an intersection containing loops but no rank-one flat does not meet these conditions.

## Evidence

The Lean source is `D5/S3/Combinatorics/Matroids/JohnsonWakefieldRankThreeMoebius.lean`, with its matching Blueprint Scribe. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The supplemental experiment is [the pinned experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/12e29eb676f5e4845bb9b417bebfd9bfa514bd7a/docs/reports/johnson-wakefield-2022-rank-three-moebius-question-6-19), file `check.py`, SHA-256 `d564a17d21dca597c2d1d13a9df5892798299334821f5e1da24b8ec674b6f894`. Its immutable Git bytes were extracted to scratch storage and run with `/opt/homebrew/bin/python3 /Users/auric/.sshx/293b8d2d377551ec779b4cb1/attempt-1/check-experiment.py`, exit 0, `RESULT PASS`. It checks the defining rectangle recursion against the product of Möbius values, the two source factorizations, and nine rank-three examples: $U_{3,4}$, $U_{3,5}$, $U_{3,6}$, Fano, non-Fano, a five-point near-pencil, the triangle $P_7$ configuration, two disjoint lines, and $AG(2,3)$. It is supplemental finite computation.

The escape audit of the public theorem `result` is unfinished under [#21453](https://github.com/the-omega-institute/trureturing/issues/21453). No Reg mirror or validated four-slot registration is asserted. Missing evidence is a faithful original-telescope realization, exact statement/readout bridge, whole-family variation and sensitivity, and actual observational dependence.

## Triage

### What the settlement shows

- **Negative answer — proved, kernel-checked:** `result` proves nonvanishing for every finite connected nonmodular rank-three matroid and every `IsJFunction`. No additional public theorem is delivered.
- **Unused assumption — proved in prose from the checked proof:** the connectedness argument is introduced and discarded in `result`; neither `moebius_eval_neg_one` nor `nonmodular_more_lines` assumes connectedness. Their displayed statements and the same final integer inference establish the conclusion without connectedness. No separately named strengthening theorem is claimed.
- **Mechanism and Question 6.21 in rank three — proved, kernel-checked:** the private `moebius_eval_neg_one` states $\mathcal M(M,-1)=2(b-v)$. Thus half the evaluation is the excess of lines over points. This interpretation is a consequence of the identity, not an additional named public theorem.
- **Quantitative bound — proved in prose:** `nonmodular_more_lines` gives integers $b>v$, hence $b-v\ge1$. Substitution into `moebius_eval_neg_one` gives $\mathcal M(M,-1)\ge2$. The lower bound has no separately named Lean theorem here.
- **Disjoint-line convention — proved, kernel-checked:** `nonmodular_disjoint_lines` gives rank-zero intersection. This means no common rank-one flat. The intersection can contain loops; set-theoretic emptiness is not asserted.
- **Nonvacuity — proved, kernel-checked:** `mu_isJ` provides the product-of-Möbius-values solution, and `j_eq_mu_product` identifies every solution on flags. The universal quantification over solutions is not vacuous.
- **Finite checker — computed:** the pinned experiment above checks exactly the nine named rank-three examples and the source factorizations for $U_{3,4}$ and rank-four $M^*(K_{3,3})$. It reports $2(b-v)$ equal to the evaluation in all nine examples, with zero precisely for the modular examples. No uniform theorem is inferred from these tests.
- **Higher rank — computed boundary:** the same pinned experiment verifies the source factorization of the rank-four nonmodular $M^*(K_{3,3})$, including its factor $t+1$. That example prevents extending this nonvanishing assertion to all ranks. Its matroid identification and nonmodularity are from source Remark 6.18; the example is not formalized here.
- **Question 6.20 in rank three — open classification boundary:** no complete classification theorem identifying the modular rank-three cases as projective planes and near-pencils, including $B_3$, is delivered.
- **Rank-three zero criterion — proved in prose using the source:** the checked nonmodular-to-nonzero argument, which does not use connectedness, gives zero-to-modular by contraposition. Source Theorem 6.16 gives modular-to-zero. Together these imply zero if and only if modular for finite rank-three matroids; the converse direction is literature input, not a Lean theorem of this delivery.
- **Arbitrary rank and the converse — open delivery boundary:** no arbitrary-rank classification for Question 6.20 is claimed. The modular-to-zero theorem remains source Theorem 6.16; no additional named Lean converse is delivered. The new result resolves Question 6.19 and adds no premise to that source theorem or to the source's rank-four counterexample.
- **Literature — literature reading, completeness ASSUMED-UNVERIFIED:** #19762 records the orchestrator's reading of the published source with Question 6.19 intact, the screen of arXiv:2305.02874v2 and arXiv:2508.04789v1, and the bounded index/repository searches. Those readings do not establish exhaustive absence of prior art.

## ASSUMED-UNVERIFIED

Literature completeness and priority remain ASSUMED-UNVERIFIED. The source's arbitrary-rank classification question, the full rank-three equality classification, and the rank-four example have no kernel-checked statements in this delivery. Escape registration remains unfinished under #21453. The finite experiment does not certify a uniform result beyond its stated scope.
