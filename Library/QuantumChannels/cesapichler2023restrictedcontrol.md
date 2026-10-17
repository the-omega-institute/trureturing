---
bibkey: cesapichler2023restrictedcontrol
authors: Francesco Cesa; Hannes Pichler
year: 2023
title: "Universal Quantum Computation in Globally Driven Rydberg Atom Arrays"
doi: 10.1103/PhysRevLett.131.170601
url: https://arxiv.org/abs/2305.19220
claim: "Established universal computation with global species-selective drives, used to delimit native single-phase-address claims."
strata_touched: []
license: citation-only
triage: anchor
---

## Checked primary source and architectural contrast

The publisher identifies Physical Review Letters 131, 170601 (2023). The accessible primary arXiv text describes universal computation without individual addressing or dynamic atomic rearrangement, using a dual-species static arrangement, species-selective global drives and blockade constraints. It provides circuit-dependent and universal-arrangement constructions; the latter has quadratic atom-number overhead. Its scheme and costs are not reproduced or benchmarked here.

The project's [single-reference continuation](../../docs/develop/theory/FIB_LEGAL_GATES_SINGLE_REFERENCE_AND_CERTIFIED_READOUT.md) retains independently addressed phase-zero controls at all native sites, adds a second quadrature at one selected data site, and compiles on an alternating-data/zero-separator encoding. Removing most phase-capable addresses is a different task from eliminating individual addressing entirely. The new model-specific theorem must not be described as the first universal reduced-control architecture, or as outperforming the Cesa-Pichler construction.

The controlled-Y/SWAP algebra and routing principle are standard. The continuation supplies their exact no11 pulse realization, explicit distance-dependent costs, and their application to the project's newly specified five-mode certification PVM.

## Real-computation boundary

T. Rudolph and L. Grover, *A 2 rebit gate universal for quantum computing*, [arXiv:quant-ph/0210187](https://arxiv.org/abs/quant-ph/0210187), establishes efficient quantum computation with real amplitudes even though arbitrary complex unitaries are not implemented on the unchanged encoding. Its primary abstract was checked for this distinction; the construction was not imported into the native compiler.

Accordingly the continuation's zero-versus-one phase-address lower bound retains its standard complex encoding, initial computational words and unchanged gate-action target. It does not establish that every real or antiunitary-constrained device has less computational power. Additional phase-reference states or a rebit encoding alter the task.

## Calibration and sequential testing

G. Warttmann, F. Meinert, H. P. Buechler and S. Weber, *Suppressing crosstalk for Rydberg quantum gates*, Quantum 10, 2045 (24 March 2026), DOI 10.22331/q-2026-03-24-2045, gives current primary context for explicit treatment of local-addressing errors. No physical error value, implementation or suppression protocol is imported here. The continuation instead states its uniform operator-norm or total-variation calibration bounds as assumptions and derives the consequences.

S. R. Howard, A. Ramdas, J. McAuliffe and J. Sekhon, *Time-uniform Chernoff bounds via nonnegative supermartingales*, arXiv:1808.03204, supplies established sequential-test methodology already used by dev C-121. The new score correction uses the elementary range-four total-variation expectation bound, with the native measurement effects, actual settings, conditional source hypothesis and all rounds retained.

No exhaustive novelty audit, QPU implementation or Lean compilation is claimed.

## Verified locator

- DOI: https://doi.org/10.1103/PhysRevLett.131.170601
- URL: https://arxiv.org/abs/2305.19220

## Remaining formalization scope

The full all-length native-control theorem, monomial and clean-work interfaces, routing bounds, complete five-state effects and conditional calibrated sequential test remain written mathematical results. Admissible Lean/Scribe formalization must preserve their complete telescopes and original control, encoding, history and calibration hypotheses. The finite compiler programs and their results remain in the [experiments source](https://github.com/the-omega-institute/trureturing-experiments/tree/a6a32d7ee751b959b70c9b74fe73a994dad59946/docs/reports/gate-shor-integration); finite residuals do not certify the universal statements.
