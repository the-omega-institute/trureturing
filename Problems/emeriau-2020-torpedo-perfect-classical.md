---
slug: emeriau-2020-torpedo-perfect-classical
bibkey: emeriau2020torpedo
doi: 10.1103/PRXQuantum.3.020307
url: https://arxiv.org/abs/2007.15643v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/TorpedoGamePerfectClassical.result
---

# A perfect classical strategy for the Torpedo Game

## Problem

P.-E. Emeriau, M. Howard and S. Mansfield (arXiv:2007.15643, quant-ph; PRX
Quantum 3, 020307 (2022)) introduce the dimension-`d` Torpedo Game: Alice
receives `x, z ∈ Z_d` and sends one dit; Bob is asked
`q ∈ {∞, 0, …, d − 1}` and must answer `a ≠ x` for `q = ∞` and `a ≠ qx − z`
otherwise. They find the classical values `3/4` and `11/12` for `d = 2, 3`,
perfect classical strategies for `5 ≤ d ≤ 23`, and state

> Conjecture: θ^C_{d≥5} = 1.

Issue #11350 fixes the reading: classical strategies use finite shared
randomness with stochastic encodings and decodings, and `θ^C_d = 1` means that
`1` is the greatest classical winning probability.

## Motivation

The quantum Torpedo Game is won perfectly for `d ≥ 3` by a qudit strategy
built from stabilizer states, while `d = 2, 3` show a classical–quantum gap. The
conjecture says the gap disappears classically from `d = 5` on. The frozen
declaration `D5/S3/Quantum/Information/TorpedoGamePerfectClassical.result`
proves it for every `d ≥ 5`.

## Gap

Issue #11350 preregisters the reading, the construction and the literature
check. The published text and the 2022 thesis of P.-E. Emeriau state the
conjecture as open. INSPIRE lists 32 citing records; the arXiv full texts
that mention the game (2210.00397, 2408.00436, 2608.05092) do not treat
`d ≥ 4`.

These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search, priority, or the absence of an
independent answer.

## Route

1. A deterministic strategy is a colouring `E` of the `d × d` grid with `d`
   colours and a decoding `D`; it is perfect iff `D(E(x, z), q)` differs from
   the forbidden label for every `(x, z, q)`.
2. For `d ≥ 6` rows are paired: row `2i` gives columns `0, 1` to one class and
   the rest to the other; row `2i + 1` gives columns `0, 2` to the second class
   and the rest to the first. For odd `d` the last three rows `r, r + 1, r + 2`
   carry three classes with parts `{−1, −2, −3}`, `{0, 1, 3}` and `{0, 2, 3}`.
3. For each class and question, Bob answers an explicit value that no point of
   the class has as its label: the labels `qx − z` of a row part missing
   columns `F` miss exactly `qx − F`, and the chosen value in that gap avoids
   the labels of the other part once `d ≥ 6` separates the small constants.
4. For `d = 5` the paper's Fig. 9 colouring with a tabulated decoding is
   checked directly. Every winning probability is at most `1`, and the perfect
   deterministic strategy attains it.

## Falsifier

The answer would change if Alice's message had fewer than `d` values, or if
Bob had to name the label `qx − z` instead of avoiding it.

## Evidence

The explicit strategy wins on every `(x, z, q)` for even `d = 4, …, 80` and odd
`d = 7, …, 79` (issue #11350); replacing the set `{0, 2}` by `{0, 1}` in the
odd rows loses at `d = 4, 6, 7, 9`.

The canonical source is
`D5/S3/Quantum/Information/TorpedoGamePerfectClassical.lean`. Its public
declarations are `label`, `winProb`, `classicalValues`, `claim` and `result`;
probability vectors are Mathlib's `stdSimplex`. The frozen module state has statement identity
`sha256:b9e7d80f1bbc3d11a4562ce11b59881582442c6292bbb8b061ece75fe5e1ebcc`.
The result declaration has statement identity
`sha256:6897018875bf5ea3f08829209af2b7fb44f5007bbec610e933746eceefba0ed7`.
The Freeze event is
`sha256:5aeb8da915f4c8c7200f43d800e89f966e1998260f017f2c1a31240ad1e8a167`
and has no project-level frozen prerequisites. The proof uses only the standard
axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

Tier 1 external named conjecture, preregistered in issue #11350 before any
Lean. `theorem`; resolution `proved`. The public theorem has
`proof_shape: content`: the colouring, the decoding and the class-by-class gap
argument are proved in the module. Its escape witness is form (1), and its
admission basis is `open-problem-resolution`. Utility `none`: the statement
holds for every `d ≥ 5`; the `d = 5` table is one case of the proof.

## ASSUMED-UNVERIFIED

The bounded literature check does not establish exhaustive worldwide novelty,
priority, or the absence of an independent answer. The Lean kernel does not
authenticate the external source or its version history.
