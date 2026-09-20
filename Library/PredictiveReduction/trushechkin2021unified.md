---
bibkey: trushechkin2021unified
authors: Anton Trushechkin
year: 2021
title: Unified Gorini-Kossakowski-Lindblad-Sudarshan quantum master equation beyond the secular approximation
doi: 10.1103/PhysRevA.103.062226
url: https://arxiv.org/abs/2103.12042v3
claim: Near-degenerate Bohr-frequency clusters require an explicit time-scale and weak-coupling treatment rather than identification with exact degeneracy.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Near-degenerate quantum frequencies

## Source and locator

Physical Review A 103, 062226 (2021), arXiv:2103.12042v3. Parsed text and the PDF page containing Section III were checked. Equation (8) splits Bohr frequencies into cluster centers and corrections at the weak-coupling scale; the surrounding construction states the system-bath assumptions and derives a GKLS form.

## Scope in the repository

The source motivates tracking frequency difference together with time and error scales. It does not justify treating every numerically close pair as an exact resonance. It also does not turn the closed classical Gaussian optimization in Section 14 into a dissipative quantum-channel result.

The source assumes a bath and a specified weak-coupling limit. The repository's canonical surrogate has no bath and is explicitly a finite-horizon approximation. Positivity, detailed balance and thermodynamic conclusions from the source are not imported after removing those assumptions.

No new resolution of the paper's master-equation problem is claimed; this is attribution to an existing result. No source experiment or full independent proof audit was performed.
