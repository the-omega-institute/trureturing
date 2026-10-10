---
bibkey: erewgoldstein2025magic
authors: Muhammad Erew and Moshe Goldstein
year: 2025
title: 'Extremizing Measures of Magic on Pure States by Clifford-stabilizer States'
doi: 10.48550/arXiv.2512.19657
url: https://arxiv.org/abs/2512.19657v2
claim: The ququint state and Wigner convention are taken from the paper; the constrained direction analysis is left open there. Conjecture 1 asserts that every SIC-POVM fiducial state is a Clifford-stabilizer state (uniquely stabilized by a subgroup of the finite eigenphase-extended Clifford group).
strata_touched:
  - D5/S3/Quantum/Magic/QuquintWignerCriticalGeometry
  - D5/S3/Quantum/Magic/ErewGoldsteinSICStabilizerRefutation
license: citation-only
triage: anchor
---

# Ququint Critical Geometry

## Verified locator

DOI 10.48550/arXiv.2512.19657, https://arxiv.org/abs/2512.19657v2 and
https://arxiv.org/html/2512.19657v2. Appendix E, equation (E.3a), gives
the state (1,1,zeta^3,1,zeta^2)/sqrt(5). Equation (2.16) gives the
phase-point convention after renaming the paper's (p,q) to (q,p).
Section 4.4.2, after (4.55), leaves the mana behavior for the constrained
variations to the reader; the last row of Table 2 is undetermined.

The saved full text and abstract were read in the preceding implementation
attempt and inspected again for this continuation. PR #5657 records the
independent source check. The current Lean development certifies the exact
geometry and vanishing first variation. QuquintStrictDecrease proves the
exact normalized change and strict mana decrease along every nonzero
direction in the specified constrained tangent family. This is a local
repository result, not a claim that the source paper contains that proof.

This lane does not claim a general solution of mana extremisation, other
dimensions, other critical points, that Claim C is the authors' verbatim
conjecture, or global novelty beyond the recorded search.

## Conjecture 1 and its definitions

From the v2 TeX source `main.tex`, for a single qudit of prime dimension $d$ with
$X\ket j=\ket{j+1}$ and $Z\ket j=\omega^j\ket j$:

- Pauli group: "$\mP_{1,d} = \Big\{ (-1)^x \zeta^k X^a Z^b \; \mid \; a,b,k \in \mathbb{Z}_d \ , \ x \in \mathbb{Z}_2 \Big\}$, where $\zeta = e^{\pi i/d}$".
- Clifford operations: "unitary transformations $ C \in \mathrm{U}(\mH) $ that map the generalized Pauli group onto itself under conjugation".
- Eigenphase-extended group: "$\mC'_{N,d} = \Bigl\{ \lambda C \; \big| \; C \in \tilde{\mC}_{N,d}, \lambda \in \Lambda(\tilde{\mC}_{N,d}) \Bigr\}$, where $\Lambda(\tilde{\mC}_{N,d})$ denotes the set of all eigenvalues of all elements in $\tilde{\mC}_{N,d}$", with $\tilde{\mC}_{N,d}$ the Clifford unitaries of determinant one.
- Clifford-stabilizer state: "A \emph{Clifford-stabilizer state} is a normalized pure state whose density operator is the projector onto a Clifford-stabilized subspace. Equivalently, it is the unique normalized state (up to an overall global phase) that spans a one-dimensional Clifford-stabilized space."
- SIC fiducial: "a normalized state $\ket{\psi} \in \mH_{1,d}$ such that $\left| \braket{\psi | T_{\boldsymbol{\chi}} | \psi} \right| = \frac{1}{\sqrt{d+1}}$ $\forall\, \boldsymbol{\chi} \in \mathbb{V}_{1,d} \setminus \{0\}$".
- Conjecture 1 (Stabilizer nature of SIC fiducials): "Every SIC-POVM fiducial state is a Clifford-stabilizer state."
