# Seed residual barrier and approximate-quartet exclusion

This directory delivers the previously unpushed approximate-quartet bundle. The complete replay and all ten corruption tests were executed again on 2026-09-06. It preserves the concurrent `SublevelRowEnclosure` and robust-gap audit work. No saved PASS is consumed by the driver.

## Precise computational claim

Set `b=(-3+4i)/5`, `e=(-2+i sqrt(21))/5`. Let H0 have blocks `J3+(b-1)I3`, `J3+(e-1)I3`, `J3+(conj(e)-1)I3`, and `-J3-(conj(b)-1)I3`, in the order of the existing C++ seed.

Every dephased unit-entry vector with all first-five seed residuals `abs(normSq((H0* u)_a)-6) <= 2^-18` lies in the union of sixty signed-Cayley tubes of radius `2^-14`. Here `H0*` denotes the adjoint.

For normalized phase vectors, the exact interval audit gives squared overlap greater than `99/100` for any two points of the same tube, and greater than `1/100000000` on every one of 1656 forbidden tube pairs. The allowed supergraph has a six-label canonical block and a disjoint bipartite remainder. Allowed edges need not actually be zero.

For any actual order-six complex Hadamard H satisfying

```math
\sigma=\max_a\sum_j|H_{ja}-H_{0,ja}|\le6\cdot2^{-24},
```

this excludes a quartet with fixed edge `(I,H/sqrt(6))`. No X-family, symmetry, target-root regularity, or exact target-root count is assumed. The neighborhood is small.

## Quantitative statement and normalization

For unit-entry matrices U,V set

```math
D_H(U)=\sum_{a,i}(|(H^\dagger U)_{ai}|^2-6)^2,
\quad O(U)=\frac1{36}\sum_{i<j}|(U^\dagger U)_{ij}|^2,
```

```math
B(U,V)=\sum_{i,j}(|(U^\dagger V)_{ij}|^2/36-1/6)^2.
```

The certificate implies

```math
D_H(U)+D_H(V)+O(U)+O(V)+B(U,V)\ge2^{-38}.
```

The columns remain exactly coordinate-flat. The cross term is degree eight jointly in U,V; no global degree-four SOS claim is made. An obsolete `2^-46` display and a missing factor six in the old handoff README have been corrected to match the actual constants and replay.

## Soundness argument

1. The signed Cayley charts `s(1+it)/(1-it)`, `s in {-1,1}`, `t in [-1,1]`, cover the unit circle, including seams. Their 32 products cover all five dephased phases.
2. For a sublevel point, the enclosure is `m-C f0(m)+(I-C J(X))(X-m)+C[-epsilon,epsilon]^5`. The last term is essential. The Jacobian argument uses a segment average or rowwise scalar mean values, not one simultaneous vector mean-value point.
3. Residual pruning, this inflated enclosure, and subdivision preserve all sublevel points. Chart changes `t -> -1/t` require a certified nonzero denominator. Every unresolved resource-limited run fails closed.
4. Whole-tube interval geometry bounds independent vectors in the same or different tubes. Root existence and uniqueness are unnecessary for this graph consumer. The inherited seed loader still performs its stronger preflight.
5. If the target residual is at most tau <= 1/4 and the column displacement is at most sigma, the seed residual is at most `tau+sigma(5+sigma)`. With tau=`2^-19` and sigma=`6*2^-24`, this is `260046857/70368744177664 < 2^-18`.
6. If total energy were below tau squared, every column would enter a tube and every internal normalized squared overlap would be below `tau^2 < 1/100000000`. Tube labels would be distinct and form a six-clique, hence be exactly the canonical labels.
7. Both frames would share a tube, forcing a cross overlap above `99/100`. Its deviation from `1/6` already contributes more than tau squared, a contradiction.

## Replay

```bash
python3 scripts/research/check_real_x_ambient_exclusion.py \
  docs/develop/certificates/real_x_supergraph_patch/input.json \
  --output /tmp/mub_ambient_barrier --jobs 4
python3 scripts/research/test_real_x_ambient_exclusion.py \
  docs/develop/certificates/real_x_supergraph_patch/input.json \
  /tmp/mub_ambient_barrier --output /tmp/mub_ambient_barrier/negative_tests.json
```

The C++17 implementation reuses the concurrent sublevel extension, Git blob `aadd53bfcd9a32af059026dd1ebc999580bdf522`, unchanged. Floating point only proposes rational preconditioners; acceptance uses outward dyadic and Fraction arithmetic. The replay completes all 32 charts, visits 5,990,990 boxes, and has no pending or unresolved boxes.

`verification.json` is a compact projection of the freshly executed report. The driver emits full per-chart files on every run. Reported counts and hashes are diagnostics, not proofs. All ten corruption tests were rejected again.

## Formal boundary

The existing `HadamardResidualBarrier.lean` now includes approximate columnwise transfer. The existing `CompleteRootSupergraphExclusion.lean` includes a set-valued whole-tube consumer. Both retain prior declarations and have Scribe projections.

There was no local Lean/lake or Scribe compiler. The sources are logically reviewed, not reported as elaborated. Interval-expression soundness, actual residual derivatives, complete finite-tree reflection, and numerical instantiation into the final energy theorem remain kernel obligations. This is a computational proof with an explicit analytic interpretation, not full Lean admission.

The single-compilation specification is not bypassed: continuous tubes are not a finite Arena equivalent to all solutions. No sampled catalog, positive information gain, AnalysisDisposition, seal, or release is asserted. All other agents' commits and their independent verification paths are preserved.
