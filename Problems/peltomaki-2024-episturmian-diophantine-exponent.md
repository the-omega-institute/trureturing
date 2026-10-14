---
slug: peltomaki-2024-episturmian-diophantine-exponent
bibkey: peltomaki2024episturmian
doi: 10.1016/j.ejc.2024.103942
url: https://arxiv.org/abs/2103.08351v3
triage: theorem
motivation_gids:
  - D5/S1/Words/Episturmian/DiophantineExponentCriterion.result
---

# Diophantine exponents of aperiodic episturmian words

## Problem

J. Peltomäki, *Initial nonrepetitive complexity of regular episturmian words and their Diophantine exponents*, European Journal of Combinatorics 118 (2024), 103942, DOI 10.1016/j.ejc.2024.103942, arXiv:2103.08351v3, Section 8, Conjecture 8.4:

> Let $\mathbf t$ be an aperiodic episturmian word. Then $\mathrm{dio}(\mathbf t)<\infty$ if and only if $\mathbf t$ has bounded partial quotients.

The source proves the regular case in Theorem 6.6. The unrestricted statement is the target of [#15858](https://github.com/the-omega-institute/trureturing/issues/15858).

### Statement echo

| Source clause | Formal counterpart |
| --- | --- |
| A finite alphabet | Every natural $d$, with letters in `Fin d` |
| A directive word $\Delta$ | Every stream $\mathbb N\to\mathrm{Fin}\,d$ |
| An episturmian word with directive $\Delta$ | `Lang t = Lang (cDelta Delta)` |
| Aperiodic | The literal negation of an eventually periodic natural tail, expanded in `claim` |
| Bounded partial quotients | `BoundedPQ Delta`, a uniform bound on the distance to the next different directive letter |
| Finite Diophantine exponent | `dio t < ⊤` |
| If and only if | Both implications of `DiophantineExponentCriterion.result` |

Finite factors use the frozen operator `AbelianBorderQuestionDefs.factor` at start zero. Its value is the literal list of the first $n$ letters. Directive prepending uses Mathlib's `Stream'.cons`, and finite powers use `Powers.wordPower`. No alphabet size, regularity, intercept or recurrence hypothesis is added.

The source's run convention and `BoundedPQ` agree: if every maximal run has length at most $K$, the next different letter occurs within $K+1$ positions; conversely a witness $B$ bounds each run by $B-1$. An eventually constant directive has neither property. This is a finite run-length argument, proved in prose.

## Motivation

The kernel-checked settling declaration is `D5.S1.Words.Episturmian.DiophantineExponentCriterion.result`. Literal palindromic closure constructs the standard word. Morphic decomposition, uniformly located powers and period desubstitution connect its factor language to the exponent of every word with that language.

The supporting literature is [Droubay–Justin–Pirillo](../Library/Rewriting/droubayjustinpirello2001episturmian.md), [Justin–Pirillo](../Library/Rewriting/justinpirillo2002episturmian.md), and [Peltomäki](../Library/Words/peltomaki2024episturmian.md). The classical closure and morphism results are literature-attested; the unrestricted finite-window transfer supplies the settlement's additional information.

## Gap

An arbitrarily large power occurring somewhere does not suffice for an arbitrarily long prefix with a large normalized ratio: the distance to the occurrence contributes to the denominator. A uniform window at every position controls this distance and transfers through equality of factor languages.

A directive tail that is eventually constant has no next separator. `powerChunk_exists` groups a fixed number of equal letters in this case, and `powerChunks_cover` constructs an unbounded chain of chunks. The argument therefore includes the infinite final periodic tail.

## Route

`central_Justin` supplies the palindromic-prefix morphism identity. The image lengths satisfy `mu_length_triangle`, and `mu_length_at_run_start` bounds every separator image by $2q$, where $q$ is the image length of the run's letter. `cDelta_constant_run_cover` and `powerChunks_cover` construct the periodic run cover.

`uniform_finite_window` uses $M\ge2$, $a\ge M(M+3)$ and $q>0$. At every position it gives a prefix $UV^e$ with $|V|=q$, $|U|\le(M+2)q$, $Mq\le |UV^e|\le H=(a+M+2)q$, and $|UV^e|/(|U|+|V|)\ge M$. `uniform_window_transfer` transports this prefix to every word with the same factor language. `not_boundedPQ_dio_top` yields an infinite Diophantine exponent for unbounded runs; `dio_finite_implies_boundedPQ` gives the first implication.

For bounded runs, `extendedMu_period_lift` desubstitutes a period through the iterated morphism. Central buffers and `boundedPQ_image_scale` control the first image scale above the period. `cDelta_periodic_factor_bound` bounds the length of a period-$p$ factor by $[1+2(d+2)(B+2)]p$. `boundedPQ_boundedPowers` supplies a uniform power bound, `boundedPowers_of_language_eq` transfers it, and `dio_finite_of_bounded_powers` gives the other implication.

## Falsifier

A violation of either implication under the literal source definitions would contradict `result`. A counterexample to the uniform window would violate one of the explicitly quantified length, period, distance or ratio clauses of `uniform_finite_window`.

The stronger auxiliary assertion that all fractional powers have exponent at most the maximal directive run plus two is false. It is not a premise of the settling theorem. The quantitative supplier is $1+2(d+2)(B+2)$.

## Evidence

The module escape witnesses are `MorphicDecomposition.central_Justin` and `BoundedPowers.extendedMu_period_lift`. Both lie on the derivation of `DiophantineExponentCriterion.result`.

The three modules and their Scribes are under `D5/S1/Words/Episturmian/` and `Blueprint/D5/S1/Words/Episturmian/`. The settling declaration proves the displayed claim. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The escape audit is unfinished: [#16158](https://github.com/the-omega-institute/trureturing/issues/16158) identifies the public theorem targets and the missing source-family realization, exact source reconstruction, variation, sensitivity and observational-dependence evidence. No successful four-slot registration is asserted.

Experiment: [the fixed finite-window check](https://github.com/the-omega-institute/trureturing-experiments/tree/b4f2004f1a39385d63d8fec694456054bc68fddc/docs/reports/peltomaki-2024-episturmian-diophantine-exponent). Command: `python3 check.py`; exit 0. Script SHA-256: `6d392ca44fcf662cf4e362031fade4288dabf63390cccc30e01b319b81e988cf`. It tests 60 random directives over 2–4 letters, $M\in\{2,3\}$, with an inserted run of length $M(M+3)$, at 593,077 positions; the first $3H$ positions and up to 3000 later sampled positions are selected, subject to the finite-word cutoff. There are zero failures. The executable permits $|U|\le(M+3)q$ and does not constrain the chosen power's total length by $H$; these readings test that relaxed finite search, while the exact $H$ and $(M+2)q$ bounds are supplied by the kernel-checked theorem.

## Triage

### What the settlement shows

- **Proved, kernel-checked:** long directive runs provide uniformly dense high fractional powers at every position, with the exact $H=(a+M+2)q$ window and normalized ratio at least $M$ (`MorphicDecomposition.uniform_finite_window`). The bound transfers independently of the intercept (`BoundedPowers.uniform_window_transfer`), and unbounded partial quotients force `dio = ⊤` (`BoundedPowers.not_boundedPQ_dio_top`).
- **Proved, kernel-checked:** bounded runs bound all powers by period desubstitution (`BoundedPowers.extendedMu_period_lift`, `BoundedPowers.boundedPQ_boundedPowers`). The bound used is $1+2(d+2)(B+2)$; no optimality is claimed.
- **Proved in prose:** the maximal-run-plus-two bound is false for the finite directive $(ab)^3$. Its central word is `abaababaabaababaababaabaababaaba`, obtained by the consecutive closures `a`, `aba`, `abaaba`, `abaababaaba`, `abaababaabaababaaba`, and the displayed final word. The factor at zero-based position 8 of length 16 is `abaababaababaaba`; its period-5 decomposition is given below. These literal finite equalities establish the counterexample directly rather than relying on an unpublished experiment program.
- **Computed:** the published experiment has 593,077 tested positions and zero failures, with the exact tested scope and script identity in Evidence. It does not establish a uniform statement beyond this scope.
- **Open:** Nguyen's question whether $\mathrm{Rdio}(\mathbf a)=\infty$ for every aperiodic episturmian word (arXiv:2608.20191v2, Section 9) is not settled by these declarations. The exact critical exponent for bounded partial quotients also remains open here.

For the finite counterexample, the displayed factor is $({\tt abaab})^3{\tt a}$, of length $16$, with period $5$. Its exponent is $16/5>3$, whereas every run in $(ab)^3$ has length one. It occurs in the sixth central word, which is a prefix of any infinite directive continuation. Thus it disproves the proposed bound without contradicting boundedness of the exponent. The finite derivation is the evidence kind for this item; the published experiment entry concerns the separate window test.

Both directional declarations use equality of factor languages without an aperiodicity hypothesis. Their conjunction therefore proves, in prose from those declarations, the same equivalence for every word with the indicated standard-word language. The public settling claim retains the source's aperiodicity clause. Peltomäki's regular-case theorem remains valid. Consequences that require precisely the unrestricted equivalence can use `result`; statements requiring an exact exponent or a repetition exponent receive no such conclusion from this settlement.

## ASSUMED-UNVERIFIED

The preregistration's literature screen found no settlement in its stated source and citing-work scope. Full texts of the two software-testing papers with DOIs 10.1109/ICSTW60967.2024.00036 and 10.1016/j.scico.2025.103412 were not verified; this limitation does not assert that no other publication exists. No model-family diversity is claimed. Four-slot escape registration remains unfinished under #16158. Neither the finite experiment nor the failure of normalization-only bypass attempts proves an exhaustive absence of alternative proofs.
