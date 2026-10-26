---
slug: oeis-a379764-hanna-theta-mod-four
bibkey: hanna2026a379764
doi: null
url: https://oeis.org/A379764
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.result
---

# Hanna's A379764 theta-four coefficient conjectures

## Problem

Paul D. Hanna's [OEIS A379764](https://oeis.org/A379764) states:

> G.f. A(x) satisfies Sum_{n=-oo..+oo} (4^n*A(x)^n - 4*A(x))^(n+1) = 2*theta_4(x) = 2*Sum_{n=-oo..+oo} (-x)^(n^2).

> Conjecture: for n > 0, a(n) is odd iff n is a square.

> Conjecture: for n > 0, a(n) == (-1)^(n-1) (mod 4) iff n is a square, otherwise a(n) is divisible by 4 if n is nonsquare.

The statement source and binding formal conventions are in [#18830](https://github.com/the-omega-institute/trureturing/issues/18830). The normalization is $A(0)=0$ and $a(1)=1$. Integer powers of the summand are taken in rational Laurent series. The bilateral equation means equality at coefficient $N$ for every symmetric window $[-K,K]$ with $N+1\le K$; no analytic convergence assertion is made.

### Statement echo

All names below belong to `D5.S1.Recurrence.Bilateral.HannaThetaFourModFour`.

| Source or binding convention | Lean counterpart | Fidelity |
| --- | --- | --- |
| The sum defining $\theta_4$ | `theta4` | Its coefficient at $N$ sums $(-1)^N$ at the integer roots of $j^2=N$ in $[-N,N]$. |
| The Laurent summand with integer index | `term` | The source expression is retained literally after `HahnSeries.ofPowerSeries` embeds $A$. |
| Normalization and every coefficient window | `IsGF` | Both normalization equalities and all $N,K$ with $N+1\le K$ are required. |
| Every positive index; odd coefficient iff square | `claim`, `result` | Every normalized rational solution has an integer coefficient witness and the odd-square biconditional. |
| Signed residue iff square; divisibility otherwise | `claim`, `result` | The same coefficient witness satisfies the second biconditional and nonsquare divisibility. |
| Existence of the normalized series | First conjunct of `claim` | This strengthens the source convention by ruling out a vacuous universal assertion. |
| Rational-to-integer coefficient correspondence | Integer witness in `claim` | This proves integrality at every positive coefficient; it adds no hypothesis. |

## Motivation

This is an externally stated OEIS conjecture (tier 1). The single settling declaration is `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.result`; it carries the dossier's sole `OpenProblemResolutionClaim`, with resolution `Proved`. The delivery uses `deposit-uncovered`, without an atom or coverage step.

## Gap

The literature screen in #18830 records the OEIS entry, the research seat's reading of its 18 revisions and the related A378582 and A002448 entries, repository and issue searches, and the named formal-conjecture indexes. No proof of these congruences was found in that searched scope. This is a scope-limited literature result, with completeness `ASSUMED-UNVERIFIED`.

The mathematical task is to connect the literal Laurent summands to an integral coefficient recursion and to identify every normalized rational solution with its integral solution.

## Route

Write $A=XF$ and define the signed square source by $s_k=(-1)^k$ when $k+1$ is a square, and $s_k=0$ otherwise. The private `positive_factor` and `negative_factor` identities normalize the positive and negative Laurent summands. Their exponents increase with the index; `pair_order` and `tail_window` justify each finite coefficient window.

The identities `window_eq`, `theta_identity` and `gf_iff` reduce the equation to $F=s+4T(F)$, where $T$ is the integral series built from the normalized summand pairs. `step_agree` states that agreement below degree $d$ improves to agreement below degree $d+1$. The private diagonal construction `solution` satisfies this equation by `solution_fixed`. The generic frozen `PowerSeriesNormalizedContraction.exists_unique_fixed`, applied in `fixed_unique`, supplies uniqueness; `gf_unique` identifies every normalized rational solution with the rational image of the integer construction. `solution_mod_four` and `arithmetic` give the two square biconditionals and nonsquare divisibility in `result`.

The definitions `theta4`, `term`, `IsGF` and `claim` are literal matches to the binding conventions. Proofs use existing owners through private consumed adapters. There are no supporting modules or owner publications.

## Falsifier

A normalized rational solution with a positive coefficient that is nonintegral, an odd coefficient at a nonsquare, an even coefficient at a square, a wrong signed square residue, or a nonsquare coefficient not divisible by four would contradict `result`. The theorem supplies a normalized solution, so an empty solution class cannot account for the result.

## Evidence

- Source note: `Library/RecurrenceComposition/hanna2026a379764.md`.
- Lean owner: `D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.lean`.
- Public theorem: `D5.S1.Recurrence.Bilateral.HannaThetaFourModFour.result`.
- Blueprint: `Blueprint/D5/S1/Recurrence/Bilateral/HannaThetaFourModFour.md`.
- `admission_basis: open-problem-resolution (#18830; Proved)`; `generality: I`; `utility: none`.
- Public-theorem classification after expansion: `result` has `proof_shape: bind-only`, `escape_witness: none`. Admission is the external named problem's settlement. The declarations are unbounded series identities and coefficient arguments, rather than finite numerical certificates.
- The escape audit for `D5.S1.Recurrence.Bilateral.HannaThetaFourModFour.result` is unfinished: [#19879](https://github.com/the-omega-institute/trureturing/issues/19879). No validated four-slot registration is asserted. The missing evidence is a faithful reconstruction and realization bridge for the existence-plus-universal-coefficient proposition, an enrolled readout, actual-positive law, whole-family variation, slot sensitivity and observational dependence.

### Experiment

[Exact arithmetic checker and source data](https://github.com/the-omega-institute/trureturing-experiments/tree/9dfe5bdc210cac281a148e7180239ddb21b0b34b/docs/reports/oeis-hanna-parity-family-research), commit `9dfe5bdc210cac281a148e7180239ddb21b0b34b`. Command: `python3 check.py` in that directory; exit 0. Script SHA-256: `ec87bb1637d6a946d4e5fb43f078bc623ce327257ef53b9305c05c564ca154b5`. For A379764, the first 12 terms match the saved source data, the coefficients through degree 40 are integral, and both conjectures hold for $1\le n\le40$. These are computed finite readings; the universal conclusion is supplied by `result`.

## Triage

| Lane target item | Status | Evidence |
| --- | --- | --- |
| Settlement for the exact binding claim | Proved | Kernel-checked `D5.S1.Recurrence.Bilateral.HannaThetaFourModFour.result`: existence and all positive-index coefficient clauses. |
| The supplied mother-series route is realized directly by normalized positive/negative summands; no separate $\Phi$ generalization or new task is needed | Proved for the stated route | Kernel-checked private `term_pos`, `term_neg`, `window_eq` and `gf_iff` implement the summand identities and reduction. This states the route used for this settlement, without asserting a new general $\Phi$ theorem. |
| Finite arithmetic check | Computed | The pinned experiment above checks the first 12 terms and the exact scope $1\le n\le40$. |
| Literature completeness | Open: `ASSUMED-UNVERIFIED` | The bounded screen recorded in #18830; no exhaustive priority claim. |

### What the settlement shows

**Proved (kernel-checked):** `result` gives a normalized rational solution and proves integrality, odd-square parity, the signed square-residue biconditional, and nonsquare divisibility for every normalized solution and every positive index. The decisive mechanism is the factor four in $F=s+4T(F)$: its nonlinear correction vanishes modulo four. `solution_mod_four`, consumed by `result`, states that coefficient congruence for the integer construction.

**Proved (kernel-checked auxiliary):** `gf_unique` proves uniqueness of the normalized rational solution. No analytic convergence, arbitrary scaling parameter, or other OEIS generating equation is included in this statement.

**Proved in prose from the definitions:** the positive-index restriction cannot be extended unchanged to zero: normalization gives $a(0)=0$, which is even, whereas zero is a square. The defining generating equation and its normalization remain necessary hypotheses of the universal coefficient assertion.

Both conjectures in A379764 are settled under the coefficientwise interpretation above. The related mother-series entry A378582 supplies context; no additional claim about its other questions follows here. No separate $\Phi$ generalization or additional task is proposed.

## ASSUMED-UNVERIFIED

Literature-screen completeness, first-publication priority, and identification of the OEIS informal infinite sum with the stated coefficientwise finite-window convention are not Lean-kernel conclusions. The literature screen distinguishes the orchestrator's direct checks from research-seat reports in #18830. The finite experiment is supporting arithmetic evidence, not a proof of the universal theorem. The four-slot escape audit remains unfinished as specified in #19879.
