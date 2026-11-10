---
slug: mwafise-a401496-labeled-riordan-complements
bibkey: mwafise2026a401496
doi: null
url: https://oeis.org/A401496
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Riordan/LabeledComplementCount.result
---

## Problem

Prove Arnauld Mesinga Mwafise's five FORMULA conjectures in OEIS A401496, revision 9, with the labeled Riordan graph definition in A401493, revision 10. The preregistration is [#26688](https://github.com/the-omega-institute/trureturing/issues/26688). Let $a(n)$ count distinct graphs on the fixed labels $1,\ldots,n$ for which the graph and its complement admit the stated binary power-series representation. Neither presentations nor isomorphism classes are counted.

### Statement echo

The representation has arbitrary $g,f\in\mathbb F_2[[t]]$ with $f(0)=0$; no properness assumption is imposed. Vertex $i:\operatorname{Fin}(n)$ represents label $i+1$. The lower adjacency coefficient is $[t^{i-2}]gf^{j-1}$ in source labels.

| Source clause | Lean counterpart | Domain and interpretation |
| --- | --- | --- |
| Initial values and two-step recurrence | `LabeledComplementAlgebra.claim`, settled by `LabeledComplementCount.result` | $a(1)=1$, $a(2)=2$; $a(n)=8a(n-2)-4$ for $n\ge3$, with integer subtraction. |
| Difference and finite sum | The corresponding two conjuncts of `claim` | $a(n+1)-a(n)=2^{\lfloor3(n-1)/2\rfloor}$ and $a(n)=1+\sum_{k=0}^{n-2}2^{\lfloor3k/2\rfloor}$ for $n\ge1$. |
| A113836 | The A113836 conjunct of `claim` | $n\ge2$; its finite sum uses the zero-based positive nonmultiples of three $i+\lfloor i/2\rfloor+1$. |
| Even and odd formulas | The two rational-valued conjuncts of `claim` | $(10\cdot8^{k-1}+4)/7$ for $a(2k)$, $k\ge1$; $(3\cdot8^k+4)/7$ for $a(2k+1)$, $k\ge0$. |
| Ordinary generating function | The final conjunct of `claim` | Equality in $\mathbb Q[[x]]$ with $x(1-2x)(1+3x)/((1-x)(1-8x^2))$. |

The source prints `108^(k-1)` and `38^k`. This settlement uses the preregistered multiplication reading $10\cdot8^{k-1}$ and $3\cdot8^k$. Author confirmation of that typography is unverified. The literal integer-base reading gives $a(3)=6$ and $a(4)=16$, whereas exhaustive graph enumeration gives $4$ and $12$. No literal-reading refutation is claimed.

## Motivation

The settling declaration is `D5/S3/Combinatorics/Riordan/LabeledComplementCount.result`, with admission basis `open-problem-resolution (#26688; Proved)`, generality `G`, and utility `none`. It states the full five-formula conjunction. Cheon–Jung–Kitaev–Mojallal, arXiv:1710.04604v2, Section 5, Problem 3, is context: its unlabeled question is outside this settlement.

## Gap

Finite agreement alone does not determine the all-order count. The structural issue is to classify distinct graphs while eliminating repeated power-series presentations and preserving the same labels under complementation.

## Route

In the finite quotient $\mathbb F_2[t]/(t^{N+1})$, orient a complementary pair by the edge between its first two vertices. On the unit side, write $r=H+g$ and the displacement as $\delta$. The all-column complement condition is equivalent to $r\delta^2=0$ together with the first-column parameter equation. A first nonzero coefficient of $r$ determines its order $k$. The attainable second-parameter image is the exact tail beginning at $k+\lceil(N+1-k)/2\rceil$. The zero case and these tails give normal forms; bijections and finite cardinalities give the count, from which the five formulas follow.

The algebra and classification declarations have admission basis `escape-witness`; their mathematical mechanisms are `image_square_annihilator` and `graph_complement_factor_criterion`, respectively. The result uses these through its counting bijection.

## Falsifier

A fixed-label graph outside the stated normal forms, a normal form whose complement lacks a Riordan presentation, or a duplicate graph from two distinct normal forms would invalidate the classification. A coefficient disagreement with any conjunct of the full `claim` would invalidate the corresponding formula. The disclosed integer-base typography is excluded from the proved interpretation.

## Evidence

The Lean sources are `D5/S3/Combinatorics/Riordan/LabeledComplementAlgebra.lean`, `LabeledComplementClassification.lean` and `LabeledComplementCount.lean`; their Blueprint Scribes display the statements and definitions. The source note is `Library/FiniteGeometry/mwafise2026a401496.md`.

The escape audit is unfinished: [#27284](https://github.com/the-omega-institute/trureturing/issues/27284). No four-slot registration is claimed validated by this dossier.

### Independent finite computation

[Experiment directory at commit 6e0dcc3ec6a0faa2f159aa2a6ed5b344e582ec91](https://github.com/the-omega-institute/trureturing-experiments/tree/6e0dcc3ec6a0faa2f159aa2a6ed5b344e582ec91/docs/reports/oeis-a401496-labeled-riordan-complements).

The immutable `check.py` was executed with Python 3.14 from that repository, using `git show 6e0dcc3ec6a0faa2f159aa2a6ed5b344e582ec91:docs/reports/oeis-a401496-labeled-riordan-complements/check.py` as the program supplied to `python3 -c`. Exit code: 0. Script SHA-256: `08f6714491038e8d6b038ea184394482763333f7cffd3826a65a6dd76307544e`. Final check: `ALL_CHECKS_OK`.

Complete enumeration of presentations and deduplication of fixed-label graphs for $n=1,\ldots,10$ gives $1,2,4,12,28,92,220,732,1756,5852$. The canonical graph sets equal the exhaustive unit-side sets at these orders. The recurrence, difference, sum, A113836, multiplication-reading parity formulas and generating-function coefficients agree through index $200$. This computation proves no uniform extension beyond its tested ranges.

## Triage

### What the settlement shows

| Item | Status and evidence kind | Evidence and scope |
| --- | --- | --- |
| Finite quotient criterion and exact attainable second-parameter image | Proved; kernel-checked declarations | `LabeledComplementClassification.graph_complement_criterion` gives the quotient criterion; `LabeledComplementAlgebra.image_square_annihilator` and `LabeledComplementClassification.graph_complement_factor_criterion` give the exact coefficient tail, for all their stated finite truncations. |
| Abstract all-column unit-parameter criterion | Proved; kernel-checked declaration | `LabeledComplementAlgebra.unit_parameter_criterion`, over every commutative ring of characteristic two, with both unit hypotheses. |
| Normal forms and all-order labeled count, including every bound formula | Proved; kernel-checked declaration | `LabeledComplementCount.result` gives all conjuncts of `claim`; its private counting bijection supplies the finite normal-form enumeration. |
| Independent exhaustive graph enumeration and formula diagnostics | Computed | The experiment above gives the ten counts for $n=1,\ldots,10$, checks formulas through $200$, exits 0 and ends `ALL_CHECKS_OK`; the immutable program and SHA-256 are specified there. |
| Unlabeled complements and other characteristics | Open | Neither the unlabeled classification/counts in contextual Problem 3 nor other-characteristic extensions are asserted by the delivered declarations. |

The decisive structure is the square-annihilator condition together with the exact image tail. The abstract all-column criterion extends to arbitrary characteristic-two commutative rings under its unit hypotheses; the binary tail enumeration uses the coefficients of $\mathbb F_2$ and is not asserted for general rings. The five OEIS expressions are settled together under the disclosed reading. The contextual paper's separate unlabeled problem remains open; no dependent result of that paper is claimed proved here.

### Literature status

The bounded literature screen in #26688 found no all-order settlement in the inspected OEIS history, ten accessible citing works, the listed title/author searches and arXiv material. Three publisher full texts and the journal wording were not inspected; citation-service rate limits restricted the search. This is a bounded literature reading, not a claim that no prior proof exists.

## ASSUMED-UNVERIFIED

Literature-screen completeness; the three inaccessible publisher full texts; equivalence of the context paper's journal wording to arXiv v2; and author confirmation of the parity-line typography remain `ASSUMED-UNVERIFIED`. Finite computations do not establish the all-order theorem. Unfinished escape registration is tracked in #27284 and supplies no mathematical proof.
