---
slug: finch-unimodular-zerofree-six
bibkey: finch2026smallinverses
doi: 10.48550/arXiv.2605.03691
url: https://arxiv.org/abs/2605.03691v4
triage: theorem
motivation_gids:
  - D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.result
---

# Refutation of Finch's order-six zerofree conjecture

## Problem

Steven Finch, *Small Matrices with Small Inverses: Unimodular Zerofree Cases*, arXiv:2605.03691v4, Section 5, Conjecture 4, asks whether any $6\times6$ integer matrix can be unimodular and zerofree with both entrywise absolute maxima equal to $3$. The source defines unimodular by determinant a unit, zerofree by nonzero entries in the matrix and its inverse, and the two maxima as the maximum absolute entries of the matrix and inverse. The formal claim quantifies over every integer matrix of order six with these four properties.

## Motivation

Conjecture 4 asserts nonexistence of a small order-six example. A certified counterexample separates that assertion from the source's orbit-classification and neighboring questions. The source's signed row and column permutations preserve all predicates used here, so quantifying over all matrices captures the stated existence question without choosing a canonical representative.

## Gap

The literature screen recorded in preregistration issue #25882 found no settlement in the inspected sources. The source is attested by arXiv version 4; no journal version was identified in the screened records. Citation discovery was rate-limited or unavailable on some services, and broad web results were unusable. Literature completeness and publication priority are therefore `ASSUMED-UNVERIFIED`.

The source's later discussion does not provide a theorem settling Conjecture 4. The repository proof uses standard Mathlib inverse and determinant-unit implications together with an explicit finite matrix; those standard interfaces do not themselves settle the source conjecture.

## Route

Let $A$ be the integer matrix with rows
$(3,2,2,2,2,2)$, $(2,3,2,2,2,2)$, $(2,2,3,2,2,2)$,
$(2,2,2,1,2,2)$, $(2,2,2,2,1,2)$, and $(2,2,2,2,2,1)$.
Let $B$ have rows
$(-1,-2,-2,2,2,2)$, $(-2,-1,-2,2,2,2)$, $(-2,-2,-1,2,2,2)$,
$(2,2,2,-3,-2,-2)$, $(2,2,2,-2,-3,-2)$, and $(2,2,2,-2,-2,-3)$.
The kernel-checked `witness_mul` establishes $AB=I$. Mathlib's right-inverse theorem identifies $B$ with $A^{-1}$, and its determinant-unit theorem establishes unimodularity. Every entry of both matrices is nonzero, and finite evaluation gives both maxima equal to $3$. The settling declaration has type `result : ¬ claim`.

## Falsifier

A matrix satisfying the four hypotheses and the conclusion of the source claim would contradict the displayed refutation. In particular, any alleged proof that every such order-six matrix is absent would contradict the kernel-checked witness. The result addresses the single order-six nonexistence assertion; it does not assert a classification of all orbits.

## Evidence

The frozen settling declaration is `D5/S3/QuadraticForms/FinchBalancedZerofreeRefutation.result`. Its axiom closure is contained in `{propext, Classical.choice, Quot.sound}`. The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).

The independent exact-arithmetic checker is in `the-omega-institute/trureturing-experiments`, commit `e7dc91fabb9838f81fc0f1efce16280247300b94`, at `docs/reports/finch-unimodular-zerofree-six/check.py`. The script content has SHA-256 `74a048acaefd7a7dfb3f311adbba2e45e98c6586c2f33d152c88b6628ca84bb4`. The recorded command is `python3 docs/reports/finch-unimodular-zerofree-six/check.py`; it exits `0` and ends with `ALL_CHECKS_OK`. The computation checks $AB=BA=I$, determinant $-1$, the displayed inverse, entry conditions, finite family checks, and boundary controls. It is finite supporting evidence; the Lean theorem supplies the refutation.

## Triage

| target item | status | evidence |
| --- | --- | --- |
| The displayed $A$ and $B$ multiply to the identity; $B$ is the Mathlib nonsingular inverse of $A$. | proved | Kernel-checked `witness_mul`, `result`, and the Mathlib inverse application in the settling module. |
| $A$ is unimodular, both $A$ and $B$ have no zero entries, and both maxima equal $3$. | proved | The determinant-unit, entrywise, and finite maximum branches of `result`. |
| Finch C4 is false. | proved | The frozen declaration `result : \neg claim`. |
| The pinned checker independently confirms the products, determinant, inverse, entry conditions, finite family checks, and boundary controls. | computed | `python3 docs/reports/finch-unimodular-zerofree-six/check.py`, exit `0`, script SHA-256 above, tested scope recorded in `output.txt` at the pinned experiment commit. |
| The symbolic balanced-sign family for every even dimension and $k\geq2$, exhaustive order-six orbit classification, and neighboring odd-dimensional or $\alpha=\beta=2$ conjectures remain unsettled here. | open | The delivered theorem is the fixed order-six instance; no declaration or computation in this delivery establishes a uniform family, exhaustive orbit classification, or neighboring-dimensional result. |

### What the settlement shows

The failure mechanism is an explicit balanced order-six witness whose integral inverse has the same maximum absolute entry. The nearest surviving questions are the all-even-dimensional balanced-sign family, complete order-six orbit counts, the $\alpha=\beta=2$ case, and odd-dimensional nonexistence; each remains open at the stated scope. The source's subsequent results do not acquire a false premise from this refutation because no proved result there is conditional on Conjecture 4.

## ASSUMED-UNVERIFIED

The source and literature screen are bounded to the inspected arXiv, citation, repository, and web surfaces. Rate limits and blocked or unusable search endpoints leave completeness of discovery and any priority claim `ASSUMED-UNVERIFIED`. No claim is made about a journal publication, exhaustive orbit classification, or the least counterexample.
