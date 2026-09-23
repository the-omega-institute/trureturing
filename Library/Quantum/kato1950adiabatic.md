---
bibkey: kato1950adiabatic
authors: Tosio Kato
year: 1950
title: On the Adiabatic Theorem of Quantum Mechanics
doi: 10.1143/JPSJ.5.435
strata_touched:
  - D5/S3/Quantum/Transport/MatrixUnitGenerator
license: citation-only
triage: anchor
---

# Projector transport and the complete logical algebra

Journal of the Physical Society of Japan 5(6), 435-439 (1950).
Primary publication metadata:
https://www.jstage.jst.go.jp/browse/jpsj/5/6/_contents/-char/ja
DOI: https://doi.org/10.1143/JPSJ.5.435

Kato's adiabatic work is the classical source for projector-based adiabatic
transport. In the finite skew-adjoint convention, the projector generator is
[Pdot,P]. The present module gives a self-contained algebraic construction for
a moving full system of logical matrix units:

    K = (1/d) sum_ij D_ij F_ji - P Pdot,
    P = sum_i F_ii,  Pdot = sum_i D_ii.

The differentiated matrix-unit and adjoint laws imply K* = -K and
[K,F_ij] = D_ij. For d=1 this reduces to the projector mechanism. For d>1 a
constant support can still contain a moving logical algebra, so transporting
P alone cannot determine every logical operation.

The real-path adapter derives the tangent laws from actual entrywise
HasDerivAt hypotheses. The general full-matrix-unit averaging formula is not
attributed as a theorem of Kato's paper. No new universal adiabatic estimate,
Dyson-series convergence, parameter-bundle trivialization, or physical control
cost theorem is claimed by the algebraic declarations.
