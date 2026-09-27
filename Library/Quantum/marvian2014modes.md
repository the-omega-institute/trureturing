---
bibkey: marvian2014modes
authors: Iman Marvian; Robert W. Spekkens
year: 2014
title: 'Modes of asymmetry: the application of harmonic analysis to symmetric quantum dynamics and quantum reference frames'
doi: 10.1103/PhysRevA.90.062110
url: https://arxiv.org/abs/1312.0680v2
claim: Time-translation covariant quantum maps preserve frequency modes; the mode-selection rule is an independent constraint on coherent thermal recovery.
strata_touched:
  - D5/S3/Quantum/Dynamics/HamiltonianEffectCompletionGenerator
license: citation-only
triage: anchor
---

# Frequency modes and thermal recovery

## Source scope

Physical Review A 90, 062110 (2014), author manuscript v2. Section II,
equations (2.7)-(2.10), describes decomposition into symmetry modes and their
preservation by symmetric processing. The rule concerns a specified symmetry
representation on both the input and output; matching a stationary reference
state alone does not imply this covariance.

## Use in the computational-behavior volume

Sections 56-58 impose covariance on the same CPTP channel that restores two
conditional Gibbs states. The resulting off-diagonal block obeys
`H0 X - X H1 = omega X`. The frequency rule is prior art. The volume separately
optimizes its trace over the thermally calibrated positive block, using
noncommuting spectral projections, and treats finite-time covariance error.

For the two-label problem, each exact output energy has at most one partner at
a fixed gap, so independent polar contractions assemble into one feasible map.
That argument does not establish simultaneous saturation for three or more
labels. Near-equal numerical gaps do not establish exact matching. The
existing Lean commutator-orbit declaration supplies a dynamics interface; it
does not prove the paper-level optimization or diamond-norm formulas.

The bibliography and the Section II mode formulas are the source basis. This
note contains an original citation-only summary, without reproducing the
article or claiming a thermal-operation implementation.
