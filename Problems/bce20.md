---
slug: bce20
bibkey: barrett2022laplacianspread
doi: 10.48550/arXiv.2206.15410
url: https://arxiv.org/abs/2206.15410v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.result
---

## Problem

Barrett–Cameron–Evans–Hall–Kempton, *On the Laplacian spread of digraphs*, arXiv:2206.15410v1, Conjecture 20, page 16: “The bound on the Laplacian spread of digraphs given in (5) can be reduced to a linear function in $n$ with a slope of $1$.” Section 6 specifies unweighted digraphs. Preregistration: [#21874](https://github.com/the-omega-institute/trureturing/issues/21874).

### Statement echo

`claim` asserts that some real constant $C$ bounds the spread by $n+C$ for every $n\ge2$ and every loopless `Digraph (Fin n)`. Its outgoing-degree Laplacian, real Euclidean constrained quadratic-value set, infimum, supremum and spread are the literal shared source definitions. Opposite arcs are allowed; balance is not a hypothesis. `result` proves the literal negation of this uniform existential assertion.

## Motivation

The settling declaration is `D5.S3.Combinatorics.SpectralGraph.BarrettLaplacianSpreadSlopeRefutation.result`. It excludes every fixed intercept in a slope-one upper bound for all loopless unweighted digraphs, rather than just excluding the bound at one order.

## Gap

A finite excess above the order does not alone exclude an arbitrary intercept. The proof amplifies a five-vertex excess by independent-cluster blowups, so the excess is unbounded.

## Route

For the source Figure 3 graph, zero-sum integer vectors have Rayleigh values $3408/679$ and $0$. Replacing each vertex by an independent cluster of size $m$ produces a loopless unweighted graph of order $5m$. Lifted vectors give spread at least $3408m/679$, and therefore excess at least $13m/679$ over the order. The Archimedean property chooses $m$ large enough to defeat any proposed real intercept.

## Falsifier

A real constant bounding every such graph by its order plus that constant would contradict `result`. This refutation says nothing about restrictions to balanced or polygonal digraphs.

## Evidence

The Lean source is `D5/S3/Combinatorics/SpectralGraph/BarrettLaplacianSpreadSlopeRefutation.lean`, with its matching Scribe. Its proof shape is `bind-only` and its admission basis is `open-problem-resolution (#21874; Refuted)`. The four-slot escape audit of `quadraticValues_isCompact`, `rayleigh_mem` and `result` is unfinished under [#22040](https://github.com/the-omega-institute/trureturing/issues/22040). The module uses `utility: none`, so no designated utility-refutation audit exemption is claimed.

The exact experiment is [bcehk-laplspread at commit 2189938c4555f35b12767dce2ac078784f928114](https://github.com/the-omega-institute/trureturing-experiments/tree/2189938c4555f35b12767dce2ac078784f928114/docs/reports/bcehk-laplspread). Command: `python3 /Users/auric/trureturing-experiments/docs/reports/bcehk-laplspread/check.py`; exit 0. Script SHA-256: `c37f6d846b9c1342f26d3284250e053c90313946f9f50d636cb8483fff3d6366`. Python 3 with SymPy 1.14.0 verifies exact arithmetic and polynomial root isolation; all checks pass.

## Triage

| Item | Status and evidence |
| --- | --- |
| No universal slope-one spread bound with a fixed real intercept | Proved in Lean: `BarrettLaplacianSpreadSlopeRefutation.result`. |
| Figure 3 base certificates and arbitrary positive independent-cluster blowups | Proved in Lean: private `base_x`, `base_y`, `lifted_energy`, and `blowup_spread`; the latter gives the lower bound $3408m/679$, not an exact value for the entire spread. |
| Finite checks of the base and cluster lifts | Computed by the experiment in Evidence: base Rayleigh values $3408/679$ and $0$, and the exact lifted values for $m=1,\ldots,8$. Figure 3's spread is enclosed in $(5.0345,5.0355)$; no exact spread equality to the lower certificate is claimed. |
| Best general asymptotic slope, balanced and polygonal restrictions | Open here; this family does not settle them. |

### What the settlement shows

The failure mechanism is a general digraph with spread exceeding its order together with a blowup operation that scales both the order and the certified Rayleigh difference. A five-vertex witness thus obstructs every intercept. The preserved assertion is the source's general upper bound $5(n-1)/2$; no contradiction to it is asserted. Bounds restricted to balanced or polygonal digraphs are separate statements. The companion proof of Conjecture 14 establishes a balanced unweighted lower-gap assertion, rather than a general upper bound.

## ASSUMED-UNVERIFIED

Literature completeness is ASSUMED-UNVERIFIED. The source screen in #21874 found no settlement in its searched scope. The journal full text, complete citing-work inventory, latest Li–Ji corrigendum, Gregory–Hershkowitz–Kirkland nonprincipal-spectrum implications, and Cameron–Graillat text remain unverified. No exhaustive priority claim is made. Four-slot escape registration remains unfinished under #22040.
