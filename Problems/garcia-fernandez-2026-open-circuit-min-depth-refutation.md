---
slug: garcia-fernandez-2026-open-circuit-min-depth-refutation
bibkey: garciafernandez2026openqc
doi: 10.48550/arXiv.2607.02093
url: https://arxiv.org/abs/2607.02093v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.result
---

# The minimum depth of open integrable circuits

## Problem

García Fernández, Paletta and Retore (arXiv:2607.02093v1) build open-boundary
integrable quantum circuits for every set of sites carrying the inhomogeneity
`-κ` and group them by the number `κ₋` of such sites. They conjecture:

> **Conjecture 1** For odd $N$ and $0<\kappa_-\le \frac{N-1}{2}$, the minimum
> depth is given by $d=\frac{1}{2}(N+3)-\kappa_-.$
>
> **Conjecture 2** For even $N$ and $0<\kappa_-\le \frac{N}{2}$, the minimum
> depth is given by $d=\frac{1}{2}(N+4)-\kappa_-.$

Issue #10379 fixes the readings: the circuits are those of the paper's
Theorems 1 and 2, with `U_{j,j+1}` on the sites `j, j + 1`, `K₁^R` on site 1
and `K̃^L_N` on site `N`, and the rightmost factor of the operator product
acting first; the depth is the least number of layers into which the gates can
be placed so that any two gates sharing a site keep their time order; the
minimum is taken over all sets of `κ₋` sites among `1, …, N`.

## Motivation

These circuits are the Floquet evolutions of Yang–Baxter integrable open spin
chains, and the minimum depth selects the shallowest circuit in each
spectral-equivalence class. The frozen declaration
`D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.result` shows
that both conjectured formulas fail.

## Gap

Issue #10379 preregisters the counterexamples before any formalization. The
arXiv API lists only v1 (2026-07-02), and Semantic Scholar lists no citing
paper (2026-09-27). The paper reports an exhaustive check of all positions for
odd `N = 3, …, 9`, where the conjecture holds, and studies of even `N` up to
10. These readings are `not-found-in-searched-scope`; they do not establish an
exhaustive worldwide literature search or priority.

## Route

1. For `N = 8` and the `-κ` sites `{3, 6}` (`n⃗ = (6, 3)`), Theorem 1 gives
   `U₆₇U₃₄K₁U₁₂U₂₃U₄₅U₅₆U₇₈K̃₈`. In time order the gates `K̃₈, U₇₈, U₅₆, U₄₅,
   U₂₃, U₁₂, K₁, U₃₄, U₆₇` take the layers `0, 1, 0, 1, 0, 1, 2, 2, 2`, and
   every two gates sharing a site keep their order. So the minimum depth for
   `κ₋ = 2` is at most 3, while Conjecture 2 gives `(8 + 4)/2 − 2 = 4`.
2. For `N = 11` and `{4, 8}` (`n⃗ = (8, 4)`), the gates `K̃₁₁, U₁₀,₁₁, U₉,₁₀,
   U₇₈, U₆₇, U₅₆, U₃₄, U₂₃, U₁₂, K₁, U₄₅, U₈₉` take the layers
   `0, 1, 2, 0, 1, 2, 0, 1, 2, 3, 3, 3`, so the minimum depth for `κ₋ = 2` is at
   most 4, while Conjecture 1 gives `(11 + 3)/2 − 2 = 5`.

## Falsifier

A reading of the circuits or of the depth under which these layerings are
invalid would undo the refutation; the kernel checks both layerings against
the definitions.

## Evidence

An independent computation of the least layer of each gate reproduces every
depth the paper prints for its figures (for `N = 5` the configurations
`(4, 2)`, `(5, 2)`, `(2, 1)` have depths 2, 3, 4; for `κ₋ = 0` the staircase
has depth `N + 1`; the `N = 9` appendix configurations have depths 2, 3, 4, 5,
10). For `2 ≤ N ≤ 12` the conjectured formulas fail exactly at `N = 8`
(`κ₋ = 2`), `N = 10` (`κ₋ = 2, 3`), `N = 11` (`κ₋ = 2, 3`) and `N = 12`
(`κ₋ = 2, 3, 4`), each time by one.

The canonical source is
`D5/S3/Quantum/Dynamics/OpenIntegrableCircuitDepthRefutation.lean`. Its public
declarations are `Gate`, `Gate.sites`, `circuit`, `RunsIn`, `depth`,
`minDepth`, `conjectureOne`, `conjectureTwo`, `claim`, and `result`. The
frozen module state has statement identity
`sha256:390c62f30a9dba597753aa85dfe27970c19da88c66e780fc68f1f7e4e5afcc0c`.
The result declaration has statement identity
`sha256:b1c8dacfe9dee0a619737280bea242475857aab92cf8d0067cd2876485ba33d8`.
The Freeze event is
`sha256:062e9c74fd037ee3a45d1c733e0d8b0c2d445c7ddad2be550486f7e6d9257bc9`
and has no project-level frozen prerequisites. The proof uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`,
`native_decide`, or new axiom.

## Triage

`theorem`; resolution `refuted`, for both conjectures as read in #10379. The
public theorem has `proof_shape: bind-only`: it instantiates the definitions
with two explicit layer maps checked by `decide`. `admission_basis:
open-problem-resolution` under preregistration issue #10379; utility
`kind=certified-instance; basis=refutes` with typed `claim` and `result`. There
is no atom and no digestion coverage edge.

## ASSUMED-UNVERIFIED

The depth is read as the least number of layers under commutation of gates on
disjoint sites, the only commutation the paper uses; the authors' Mathematica
notebook was not opened. The bounded literature check does not establish
exhaustive worldwide novelty, priority, or the absence of an independent
refutation.
