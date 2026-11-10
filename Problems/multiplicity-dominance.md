---
slug: multiplicity-dominance
bibkey: petrovscott2026clone
doi: 10.1017/fms.2025.10165
url: https://arxiv.org/abs/2412.21126v2
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.result
---

# Fibonacci multiplicity dominance: Petrov–Scott Conjecture 8.22

## Problem

Leonid Petrov and Jeanne Scott, *Random Fibonacci words via clone Schur functions*, arXiv:2412.21126v2, Conjecture 8.22, p. 47; Forum of Mathematics, Sigma 14 (2026), e15, DOI 10.1017/fms.2025.10165:

> The matrix 𝐍ₙ is upper triangular. Furthermore, if Nᵤ,ᵥ is nonzero then u ⪰ v and ℎ(u)=ℎ(v), where ℎ(w) denotes the total hike, i.e., the number of 2’s appearing in a Fibonacci word w.

The preregistration is [#22953](https://github.com/the-omega-institute/trureturing/issues/22953). The binding interpretation retains the printed Definition 8.12, including its odd-length weight defect. The theorem concerns the literal matrix restricted to pairs of words of common weight. It does not certify the separate weight-preserving correction or Figure 8.

### Statement echo

| Source clause | Lean counterpart | Fidelity |
| --- | --- | --- |
| Words over $\{1,2\}$ of weight $n\ge1$ | `YF`, universal binders of `claim` | Arbitrary natural weight and list length; no finite cutoff. |
| Total hike is the number of twos | `hike` | `List.count 2`. |
| Ribbon inverse, Definition 8.10 | `Fib` | Initial/final row offsets one, interior offsets two, and the one-row case are retained. |
| Literal auxiliary compositions, Definition 8.12 | `splitA`, `splitB` | One-based indices shift to zero-based list indices; the printed sum in `splitB` has exactly $p$ terms. |
| Arcs, noncrossing, active endpoints and predecessor rank | `Arc`, `IsNoncrossing`, `Gamma`, `gamma` | Source labels $1,\ldots,n$ shift to `Fin n`; every strict and weak inequality is preserved. |
| Equation (8.1), Definition 8.16, Corollary 8.20 | `ell`, `g`, `peak`, `z`, `multiplicity` | Finite partition count; precisely the optional final zero is removed. |
| Definition 8.21 matrix | `matrixEntry` | A matching `Composition n` is chosen when one exists, otherwise the entry is zero. |
| Upper triangularity in the descending lexicographic order of Figure 8 | First conjunct of `claim` and `result` | Opposite lexicographic direction forces a zero entry. |
| Nonzero support implies every common prefix inequality and equal hike | `Dominates`, second conjunct of `claim` and `result` | All common nonempty prefixes; both conclusions are present. |

Every public definition has its complete body in the Blueprint. No additional hypothesis occurs in the public settling statement. Private proof carriers do not replace the binding public expressions. `endWord` applies the frozen `D5.S1.Words.UnaryGapWords.gap` owner with its parameters.

## Motivation

The result gives an unbounded structural restriction on the literal partition-count matrix, independent of finite enumeration or an explicit formula for its nonzero multiplicities. The settling declaration is `D5.S3.Combinatorics.YoungFibonacci.PetrovScottMultiplicityDominance.result`.

## Gap

The weight-preserving correction of `splitB`, the corresponding Figure 8 matrix in Lean, an explicit multiplicity formula (Problem 8.23), and a converse characterizing the support from dominance remain open in this delivery. A proof about the literal fixed-weight matrix does not settle these separate statements.

## Route

Equal lengths of the two split compositions give equal numbers of twos. For positive composition parts, each trailing run in the first split word is at least the corresponding run in the second. The private `endWord_count_mono` proves by induction that increasing those runs reduces the number of twos in every reversed prefix, with arbitrary initial runs. `split_dominates` combines this with equal weight and hike to obtain equal lengths and the forward-prefix inequalities. `dominates_no_reverse_lex` excludes the opposite lexicographic direction at the first different letter. `result` applies these consequences to nonzero matrix support.

## Falsifier

A common-weight supported pair violating a prefix inequality, hike equality or the stated lexicographic direction would contradict the settling claim. A pair whose literal split words have different weights is outside the matrix's common-weight domain and is not such a counterexample. For example, the pinned computation gives $A(1,1,1,1,1)=(1,2,2)$ and $B(1,1,1,1,1)=(1,2,1)$, of weights five and four.

## Evidence

`result` proves `claim` in `D5/S3/Combinatorics/YoungFibonacci/PetrovScottMultiplicityDominance.lean`. Its admission basis is `open-problem-resolution (#22953; Proved)`, generality is `G`, and utility is `none`. The axiom closure of every public declaration is contained in $\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$. The source note is `Library/RecurrenceComposition/petrovscott2026clone.md`.

The escape audit of `D5.S3.Combinatorics.YoungFibonacci.PetrovScottMultiplicityDominance.result` is unfinished: [#25184](https://github.com/the-omega-institute/trureturing/issues/25184). No Reg registration is delivered. Missing evidence is a lawful whole-family realization and reconstruction of the complete compound statement, with compiled observational dependence, variation and sensitivity proofs; a pointwise inequality projection alone omits other conjuncts.

The supplemental [experiment directory](https://github.com/the-omega-institute/trureturing-experiments/tree/ed45e66b1305174ab2b1a2d2d5642495ac8f2817/docs/reports/fibonacci-multiplicity-dominance) contains `check.py` at immutable revision `ed45e66b1305174ab2b1a2d2d5642495ac8f2817`. Program SHA-256: `eac5364d98a2a8cef5d32c666b515bd31ca27483df4b7309651be306f4848db6`. Command: `python3 /Users/auric/.sshx/dc41e1c4f6ac75238dec2a79/attempt-1/check.py` on the bytes extracted from that revision; exit 0, `ALL_CHECKS_OK`. The program is not a premise of the Lean proof.

## Triage

| Item | Status and evidence kind | Scope |
| --- | --- | --- |
| The bridge applies to every positive composition whose literal split words have common weight, without any assumption on multiplicity. | Proved; kernel-checked private `split_dominates`. | Every `Composition n` whose two split words satisfy `YF n`; no multiplicity hypothesis. |
| Monotonicity of reversed-prefix counts under coordinatewise enlargement of trailing runs, allowing arbitrary initial runs. | Proved; kernel-checked private `endWord_count_mono`. | Arbitrary lists related by `List.Forall₂`, arbitrary initial runs and prefix lengths. |
| Equal hike and equal YF weight imply equal word lengths; dominance excludes the opposite descending lex direction. | Proved in prose for length equality: apply kernel-checked private `yf_sum_formula` to both words, substitute their common weight and hike, and cancel the common hike. Lexicographic exclusion is kernel-checked private `dominates_no_reverse_lex`. | The identity is $\operatorname{sum}(w)=\operatorname{length}(w)+\operatorname{hike}(w)$ for binary words; the lexicographic lemma assumes binary words, equal length and dominance. |
| Exact source-fidelity checks and all 16,383 weight-preserving and 8,569 literal same-weight composition pairs through weight 14. | Computed; pinned `check.py`, command, exit 0 and SHA-256 in Evidence. | Weights $1\le n\le14$ for support checks; Catalan totals and surjectivity for $1\le n\le9$; all 64 Figure 8 entries only under the separate weight-preserving interpretation. `ALL_CHECKS_OK`. |
| Separate Lean theorem for the weight-preserving correction of `splitB` / Figure 8. | Open. | Binding definitions are unchanged; no such theorem is delivered. |

### What the settlement shows

The decisive mechanism is monotonicity of reversed-prefix counts under enlargement of trailing runs. It proves the dominance bridge for all positive compositions with common-weight split words, including ones whose multiplicity vanishes. Initial runs need no comparison. Equal weight supplies the common length used to convert to forward prefixes; the printed odd-length split can leave that domain. These are the scopes of `endWord_count_mono` and `split_dominates`, rather than a claim about a corrected matrix.

The first differing letter then turns prefix dominance into upper triangularity in the source's descending lexicographic order. The settling theorem supplies the structural assertion of Conjecture 8.22 under the binding literal interpretation. No further source result depending on the corrected matrix or on a multiplicity formula is certified here. The explicit formula and support converse remain open.

## ASSUMED-UNVERIFIED

Completeness of the source and literature screen in #22953 is ASSUMED-UNVERIFIED. The screen distinguishes Okada's clone Kostka nonvanishing theorem from these moment multiplicities and found no settlement of Conjecture 8.22 in its inspected scope. It does not establish publication priority or exhaust uncatalogued manuscripts. The corrected matrix, Figure 8 in Lean, and additional probabilistic consequences are not formally verified by this delivery.
