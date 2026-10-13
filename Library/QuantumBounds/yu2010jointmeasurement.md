---
bibkey: yu2010jointmeasurement
authors: Sixia Yu; Nai-le Liu; Li Li; C. H. Oh
year: 2010
title: "Joint measurement of two unsharp observables of a qubit"
doi: 10.1103/PhysRevA.81.062116
url: https://arxiv.org/abs/0805.1538
claim: "Equation (5) defines the squared-bias square-root function used in the necessary and sufficient joint-measurability criterion."
strata_touched:
  - D5/S3/Quantum/Measurement/OrderedRootCoordinates
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.1103/PhysRevA.81.062116

Source: https://arxiv.org/abs/0805.1538

# Joint measurement of two unsharp observables of a qubit

Equation (5), PDF p. 2, defines

$$F_x=\frac{\sqrt{(1+x)^2-m^2}+\sqrt{(1-x)^2-m^2}}2.$$

Here $m$ is the length of the Bloch vector and $x$ is the bias. The condition
$|x|+m\le1$ describes a two-outcome qubit observable. Theorem 1 gives the
necessary and sufficient condition for joint measurability. Its strict violation,
restricted to the parameter bodies of both observables, is the incompatible set
in the probability calculation.

The Lean function `hYu` replaces $m$ by the norm of a vector in
`EuclideanSpace ℝ (Fin 3)` and retains the squares on both $1+x$ and $1-x$.
