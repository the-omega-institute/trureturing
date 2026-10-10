---
bibkey: tabiaappleby2013qutrit
authors: Gelo Noel M. Tabia; D. M. Appleby
year: 2013
title: "Exploring the geometry of qutrit state space using symmetric informationally complete probabilities"
doi: 10.1103/PhysRevA.88.012131
url: https://arxiv.org/abs/1304.8075v2
claim: "Every Weyl-Heisenberg SIC in d=3 is obtained by an extended Clifford (anti)unitary from a SIC with fiducial vector (0, 1, -e^{2it})/sqrt(2), t in [0, pi/6], and distinct t in that range give distinct extended Clifford orbits."
strata_touched:
  - D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation
license: citation-only
triage: anchor
---

# Tabia and Appleby, the continuous family of qutrit SIC fiducials

G. N. M. Tabia and D. M. Appleby, *Exploring the geometry of qutrit state space using symmetric
informationally complete probabilities*, Phys. Rev. A 88, 012131 (2013); arXiv:1304.8075v2
(quant-ph).

## Verified locator

DOI: 10.1103/PhysRevA.88.012131 (Crossref: Physical Review A, volume 88, article 012131, issued
2013-07-31).
Preprint: https://arxiv.org/abs/1304.8075v2. The arXiv abstract page lists versions v1 and v2;
the TeX source `qutritGeom.tex` of the v2 e-print supplies the statements below.

## Source statements

Section II, "Properties of Weyl-Heisenberg qutrit SICs", after the clock and shift matrices of $d=3$:

> Every Weyl-Heisenberg SIC in $d=3$ can be obtained by acting with an (extended) Clifford
> (anti)unitary on a SIC with fiducial vector
> $\ket{\psi_t} = \frac{1}{\sqrt{2}}(0, 1, -e^{2it})^{\mathsf T}$, $t \in [0, \frac{\pi}{6}]$.
> Fiducials corresponding to distinct values of $t$ in the range $[0, \frac{\pi}{6}]$ generate
> distinct orbits of the extended Clifford group.

The paper attributes the orbit classification to Appleby (2005): three types of orbits contain
$\ket{\psi_t}$, the infinitely many generic ones for $t \in (0, \frac{\pi}{6})$ and two exceptional
ones at the endpoints. The abstract states that the infinitely many qutrit SICs fall into eight SIC
families corresponding to independent orbits of the extended Clifford group.

## Use in this repository

`D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation` uses the vectors
$\psi_z = (0, 1, -z)/\sqrt2$, $|z| = 1$. For $z = e^{2it}$ with $t \in [0, \pi/6]$ they are the
fiducials quoted above. The module proves the SIC overlap condition for every unit $z$ directly
(`qutritFiducial_isSIC`), so it does not rely on the paper for the remaining values of $z$; only
the family itself is attributed to this source.
