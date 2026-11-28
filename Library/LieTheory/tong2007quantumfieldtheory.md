---
bibkey: tong2007quantumfieldtheory
authors: David Tong
year: 2007
title: Quantum Field Theory
doi: null
url: https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf
claim: Chiral Dirac matrices satisfy the Clifford relation, their Weyl blocks represent the Lorentz double cover, and charge conjugation exchanges the two chiralities.
strata_touched:
  - D5/S3/Geometry/Lorentz/SL2CLorentzCover4D
  - D5/S3/Geometry/Lorentz/DiracCliffordSpinors4D
license: citation-only
triage: anchor
---

# Weyl spinors and Lorentz transformations

## Verified locator

Tong's Cambridge Part III notes, §4.4, equations (4.57)–(4.61),
describe two-component Weyl spinors, the Pauli matrices for rotations
and boosts, and the identification of the Lorentz double cover as
$\mathrm{SL}(2,\mathbb C)$.
[Lecture notes](https://www.damtp.cam.ac.uk/user/tong/qft/qft.pdf)

Equations (4.13) and (4.16) give the Clifford relation and chiral gamma
matrices. Section 4.3 derives the Dirac adjoint and bilinear transformations.
Equations (4.67)–(4.70) give the chirality projections. Section 4.5 gives
Majorana reality and its exchange of the two Weyl components.
[Chapter 4](https://www.damtp.cam.ac.uk/user/tong/qft/four.pdf)

## Formal correspondence

The formalization uses time-positive metric convention and represents a
four-vector by its Hermitian Pauli matrix. The determinant-one
conjugation action defines a real matrix with exact fibers $\{A,-A\}$.
Euler rotations and an axial boost construct its preimage for every
proper orthochronous Lorentz matrix. Spinor outer products intertwine
this action with matrix multiplication on spinors. The Möbius identity
uses the affine chart with nonzero second spinor coordinate at both ends.

For the bispinor action $S(A)=\operatorname{diag}(A,(A^\dagger)^{-1})$,
the two off-diagonal blocks of the slash matrix are the Hermitian Pauli
matrix and its adjugate. This identifies slash conjugation with the same
real Lorentz matrix as in the two-component cover. Inverse conjugation of
the upper-index gamma family uses columns of the inverse Lorentz matrix.
Lowering the gamma index with the time-positive metric gives the row form
$S(A)^{-1}\gamma_\mu S(A)=\sum_\nu\Lambda(A)^\mu{}_{\nu}\gamma_\nu$.
The vector and axial bilinears with lowered gamma matrices obey that row
transformation.

In the Weyl basis $\gamma_5=\operatorname{diag}(-I_2,I_2)$ and
$C=i\gamma^2\gamma^0$. The matrix acting on the conjugated spinor is
$C\gamma^0=i\gamma^2$, the convention used for the antilinear map in
Section 4.5. Its involution commutes with the bispinor action and exchanges
the two chirality projections.
