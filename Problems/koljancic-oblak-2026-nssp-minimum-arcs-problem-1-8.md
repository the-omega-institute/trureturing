---
slug: koljancic-oblak-2026-nssp-minimum-arcs-problem-1-8
bibkey: koljancicoblak2026nssp
doi: 10.13001/ela.2026.10523
url: https://arxiv.org/abs/2604.21552v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.result
---

# The minimum number of arcs requiring nSSP

## Problem

Sara Koljančić and Polona Oblak, *Combinatorial aspects of the nonsymmetric
strong spectral property for graphs*, Problem 1.8, printed page 759:

> Is the minimum number of arcs in a directed graph G on n vertices that requires the nSSP equal to 2n−1?

The source and preregistration are linked from
[issue #25108](https://github.com/the-omega-institute/trureturing/issues/25108).
The [Library note](../Library/Eigenstructure/koljancicoblak2026nssp.md)
records source versions, attribution and licensing. The endpoint-looped double
path is the source's Theorem 5.5 and Remark 2.10(1), not a new upper construction.

| Source clause | Exact Lean meaning |
| --- | --- |
| n vertices | Fin n, for every natural n with 1 ≤ n |
| Directed graph, loops allowed | Finset (Fin n × Fin n); each ordered pair appears at most once |
| Exact matrix support | A i j ≠ 0 if and only if (i,j) belongs to E |
| nSSP | Every real X with A i j * X i j = 0 and A * X.transpose − X.transpose * A = 0 is zero |
| Requires nSSP | Every real A of that exact support has nSSP |
| Minimum equals 2n−1 | All requiring E have at least 2n−1 arcs, and at the same n some requiring E has exactly 2n−1 arcs |

These definitions occur in
`D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs`.
`MinimumArcs` is the entire two-clause assertion; `result` states it directly.
There is no additional identity-Hadamard, trace, sign, connectivity, symmetry,
eigenvalue, genericity or finite-order restriction in that assertion.

## Motivation

The assertion determines the sharp support-size threshold for universal real
nSSP at every positive order. Its upper construction is prior art; the
settlement joins that construction to the universal lower bound.

## Gap

The question concerns every exact real weighting, rather than the existence
of one matrix with nSSP. A lower bound assuming connectivity alone would
leave a gap: connectivity must follow from the universal requirement.

## Route

The lower-bound argument embeds an n-dimensional real space in the centralizer,
using the classical polynomial-module structure theorem. The support readout
F ↦ (A_ij F_ji) is injective by nSSP and lies in the directed incidence kernel.
A requiring support must be connected: a component without a loop gives a
diagonal obstruction, and two looped parts can be weighted to share eigenvalue
one, giving an off-block outer-product obstruction. Connected incidence has
rank at least n−1, so the arc count is at least 2n−1. The source's endpoint
path supplies equality for all arbitrary nonzero real weights.

## Falsifier

A counterexample to the lower clause would be a positive order n and a
requiring support with fewer than 2n−1 arcs. A counterexample to the upper
clause would be an exact real weighting of the endpoint-looped double path
and a nonzero real X satisfying both original obstruction conditions.
The settling theorem excludes both throughout the stated domain.

## Evidence

The settling declaration is
`D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.result`.
Its definitions, full statement and proof mechanism are exposed in the
[Blueprint](../Blueprint/D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.md).
The [source note](../Library/Eigenstructure/koljancicoblak2026nssp.md)
binds the journal and arXiv versions and their attribution. The immutable
[preregistration](https://github.com/the-omega-institute/trureturing/issues/25108#issuecomment-6553617852)
selects the entire all-positive-order event.

## Triage

**Proved:** Problem 1.8, by
`D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.result`.
The endpoint upper construction remains attributed to Theorem 5.5 and
Remark 2.10(1), rather than counted as a separate resolution.

### What the settlement shows

The decisive lower-bound mechanism is the injection of the centralizer into
the signed incidence kernel, proved by
`D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.nssp_centralizer_cycle_bound`.
It gives n plus the incidence rank as a lower bound on the number of arcs.
The additional structural result
`D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.requires_connected`
derives connectivity from universal nSSP, using a loop in every component
and shared-eigenvalue block obstructions. The connected rank estimate in
`D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.nssp_arc_bound_of_connected`
then yields 2n−1. Sharpness at the same n is proved by
`D5/S3/Combinatorics/SpectralGraph/KoljancicOblakMinimumArcs.endpoint_attainment`.
All these statements retain arbitrary real nonzero arc weights; no sign,
symmetry or genericity assumption is needed. The positive-order boundary
includes n=1 with its single loop.

The source's Problem 1.6 asks for a classification of loop assignments on
double paths into requiring, allowing but not requiring, and not allowing
nSSP. The endpoint singleton assignment supplies an already known requiring
case; the sharp minimum does not classify all equality cases or other loop
assignments. That full classification remains open here. Question 5.11
asks whether every nonempty loop assignment on an even-order double path
allows nSSP. It remains open here: allowing one weighting and requiring
every weighting have different quantifiers. No other source theorem is
refuted or replaced by this settlement, and no consequence for sign-pattern
minimum questions is asserted.

## ASSUMED-UNVERIFIED

The bounded literature qualification in #25108 does not establish exhaustive
nonresolution or worldwide priority outside its inspected sources.

Eight public-theorem escape audits remain unfinished under the explicit
[issue disclosure](https://github.com/the-omega-institute/trureturing/issues/25108#issuecomment-6555443606):

- `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.endpoint_requires`
- `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.requires_connected`
- `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.endpoint_attainment`
- `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.requires_level_has_loop`
- `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.loop_support_eigenvalue_one`
- `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.nssp_arc_bound_of_connected`
- `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.nssp_centralizer_cycle_bound`
- `D5.S3.Combinatorics.SpectralGraph.KoljancicOblakMinimumArcs.result`

Their typed dependent-family proofs are retained in the Reg mirror, but
decodable Contract registrations and current lawful source-selection and
binding evidence remain missing. The attempted `Connected.registration`
decoder returned `contract.discovery:rigid_universes` (raw exit 2, nested
exit 1); the aborted batch did not check the other seven targets. No
`declared_validated` registration is claimed. These audit obligations do
not strengthen or weaken the mathematical theorem.
