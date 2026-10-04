---
slug: lau-2026-synchronous-doily-one-tenth
bibkey: lau2026doily
doi: 10.48550/arXiv.2603.20748
url: https://arxiv.org/abs/2603.20748v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.result
---

# The one-tenth synchronous doily value

## Problem

Tony Lau, *Beyond the Magic Square Game: Widening the Gap for Two Bell States*, arXiv:2603.20748v2, §5, asks whether a value below 31/35 occurs for some p < 1/7 and identifies the one-tenth candidate: if the asymmetric strategy bound in Lemma 4.3 can be strengthened to twelve synchronous wins out of fifteen, then the 1/10-synchronous doily game has classical value 22/25. The settled statement is

`classicalValue (1/10) = 22/25`,

where `classicalValue` is the supremum over all deterministic pairs of functions from the fifteen equations to Boolean triples, the nonsynchronous distribution is uniform over the 90 ordered intersecting pairs, and the synchronous distribution is uniform over the fifteen diagonal pairs. The referee predicate uses the fifteen equations in Table 3, their stated right-hand sides, parity validity, and equality of every shared variable.

## Motivation

The source leaves the 1/10 value as an explicit exhaustive-check question and records 22/25 as the candidate value. The formal result answers that named question and gives a kernel-checked certificate for the finite game described by Table 3 and Definition 4.1.

## Gap

The source's conditional Lemma 4.3 improvement was not itself the target. The formal statement instead quantifies over all deterministic answers, including parity-invalid triples, and proves the value directly. The bounded literature search recorded in issue #12753 found no later proof or refutation of this value in the searched arXiv, INSPIRE, Semantic Scholar, MathDB, and repository surfaces; this is `not-found-in-searched-scope`, not a claim of exhaustive coverage.

## Route

The lower bound uses the explicit strategy returning 000 on equations 0 through 11 and 100 on equations 12 through 14 for both players. It satisfies every parity, wins all fifteen diagonal questions, and loses twelve of the 90 ordered intersecting questions, giving 22/25.

For the upper bound, replacing a parity-invalid answer by a parity-valid answer preserves every previously won question. For parity-valid strategies, the ten displayed 3-by-3 grids each have odd total parity and force one directed loss in each orientation. Every ordered intersecting pair occurs in two grids, so the nonsynchronous loss count is at least 10. If the two players disagree on at most two equations, the minority-event count and the local loss table force at least 12 nonsynchronous losses. With `L` the nonsynchronous losses and `r` the Hamming distance between the two equation-answer functions, finite counting gives `300 * (1 - winProb (1/10) A B) = 3 * L + 2 * r`; the two cases imply `3 * L + 2 * r ≥ 36`.

## Falsifier

A deterministic pair with winning probability greater than 22/25 would refute the upper bound. A failure of the explicit 000/100 strategy to win 78 ordered pairs would refute the lower bound. The Lean theorem `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.result` proves both bounds and their equality.

## Evidence

- Lean module: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.lean`.
- Public result: `D5/S3/Quantum/Entanglement/SynchronousDoilyClassicalValue.result`.
- The kernel axiom closure is `propext`, `Classical.choice`, and `Quot.sound`.
- The direct finite computation in the proof establishes 90 ordered intersecting pairs, 78 wins for the explicit strategy, and 15 diagonal wins. The proof's content bounds are the ten-grid loss bound and the at-most-two-disagreements bound.
- The independent exhaustive computation cited by issue #12753 reports `V(0)=8/9`, `V(1/20)=79/90`, `V(1/16)=7/8`, `V(1/12)=79/90`, `V(1/10)=22/25`, and `V(1/7)=31/35`; these values are computed evidence for neighbouring parameters, not additional Lean conclusions here.

## Triage

The named 1/10 question is **proved** by the Lean result. The ten-grid mechanism and the disagreement case split are the decisive mathematical content. The listed values of the full finite value function and the crossing of the `(L,r)=(10,5)` and `(12,0)` strategy lines at `p=1/16` are **computed** by exhaustive search; a formal theorem about the minimum over p remains **open**. The perfect quantum value for every p is **proved in the source's strategy** but is not a declaration of this module. Higher-dimensional generalisations in the source remain **open**.

### What the settlement shows

**Proved in this module:** the result proves the source's candidate value without assuming the conditional improvement to Lemma 4.3. Every grid forces one loss in each orientation, giving `L ≥ 10`; at most two synchronous disagreements force `L ≥ 12`. Every deterministic strategy therefore has loss at least 3/25 in the 1/10 mixture, and the explicit strategy attains the bound. Parity repair extends the upper bound to all parity-invalid deterministic answers. The sharp conclusion is the named 1/10 instance; the paper's results at other parameters require no revision.

**Computed, orchestrator-reported in #12753:** compiling `/tmp/op-doily/doily.c` with `cc -O3 -o /tmp/op-doily/doily /tmp/op-doily/doily.c` and running `/tmp/op-doily/doily WN WS` for `(WN,WS)=(1,0),(19,6),(5,2),(11,6),(3,2),(1,1)` gives respectively `V(0)=8/9`, `V(1/20)=79/90`, `V(1/16)=7/8`, `V(1/12)=79/90`, `V(1/10)=22/25`, and `V(1/7)=31/35`. The full value function is the maximum of the deterministic strategy lines. The reported optimal lines `(L,r)=(10,5)` and `(12,0)` cross at `p=1/16`, with the reported unique minimum `7/8` and classical–entangled gap `1/8 > 4/35`. These are computational findings; a formal proof of the full value function and unique minimum is an open follow-up candidate.

**Proved in the source:** the paper's perfect quantum strategy retains value 1 for every p. Combined with the module's exact classical value it gives gap 3/25 at p=1/10. This quantum strategy is a literature result, not a Lean declaration of this module.

**Open:** the author's higher-dimensional generalisations and a kernel-checked full parameter-value theorem. The settlement does not assert the proposed uniform strengthening of Lemma 4.3.

## ASSUMED-UNVERIFIED

The literature search is bounded to the sources and queries recorded in issue #12753. No assertion of worldwide priority or exhaustive absence is made. The neighbouring p-values, the global minimum over p, and higher-dimensional generalisations are not covered by the Lean theorem and remain open or computed as marked above.
