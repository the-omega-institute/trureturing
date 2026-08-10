---
bibkey: rice1953classes
authors: Henry Gordon Rice
year: 1953
title: Classes of recursively enumerable sets and their decision problems
doi: 10.1090/S0002-9947-1953-0053041-6
claim: No nontrivial class of partial recursive functions has a recursive index-decision procedure.
strata_touched:
  - D5/S0/Computability/ClosureUndecidable
license: citation-only
triage: anchor
---

# Classes of Recursively Enumerable Sets and Their Decision Problems

Henry Gordon Rice's paper proves that every nontrivial property of the
partial recursive functions is undecidable at the level of indices: if a
class of partial recursive functions is neither empty nor exhaustive, then
no recursive procedure decides, from an index, whether the indexed function
belongs to the class. The proof is the diagonal construction on indices —
the same construction, run through the recursion-theoretic fixed point,
that the repository's module wraps.

The deposited statement is the same-layer closure-reading form: a closure
predicate on codes that respects behavior (codes of equal evaluation are
equi-closed) and is nontrivial admits no total computable reading. This is
Rice's theorem specialized to the ledger vocabulary; the pinned Mathlib
carries the statement as `ComputablePred.rice₂`, an equivalence between
decidability of a behavior-respecting code predicate and its triviality,
proved from `Nat.Partrec.Code.fixed_point₂`.

## Search log

- 2026-08-11: Pinned Mathlib checkout searched first (`rice` in
  `Mathlib/Computability/Halting.lean`); `ComputablePred.rice` and
  `ComputablePred.rice₂` exist upstream, so the deposit is a declared thin
  wrapper plus a nontriviality-witness instantiation. Transactions of the
  American Mathematical Society 74, pages 358-366; the DOI recorded here is
  the AMS article locator. No online metadata query was run in the
  restricted implementation worker.

## Locator

- DOI: https://doi.org/10.1090/S0002-9947-1953-0053041-6
