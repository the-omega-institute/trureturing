---
bibkey: nigamphillips2007pyramids
authors: Nilima Nigam and Joel Phillips
year: 2007
title: Higher-order finite elements on pyramids
doi: 10.48550/arXiv.math/0610206
url: https://arxiv.org/abs/math/0610206v3
claim: "The reference pyramid has nonnegative coordinates with x,y at most 1-z; equations (2.3) and (6.1) give a projective map and first-order rational shape functions."
strata_touched:
  - D5/S1/Words/AdmissibleWords/PathStableSetPolytope
license: citation-only
triage: anchor
---

# Reference pyramid and the scope of rational shape functions

The primary text consumed here is the fixed author version
[arXiv:math/0610206v3](https://arxiv.org/pdf/math/0610206v3),
with the title above. Equation (1.2), PDF p. 2, defines

$$
\Omega=\{(x,y,z):x,y,z\ge0,\ x\le1-z,\ y\le1-z\}.
$$

Theorem 1.1, PDF p. 3, excludes purely polynomial high-order
$H^1(\Omega)$-conforming finite elements satisfying the compatibility
property specified in the paper. The proof uses a rational function
with polynomial face traces and derives a contradiction from a proposed
polynomial representation. This is a statement about that finite-element
model and compatibility requirement, not a claim that all functions on
a pyramid must be rational or that arbitrary vertex data determine them.

The [determinant sequel](../../docs/develop/theory/AURIC_FIB_ATOM_PYRAMID_DETERMINANT_AND_NATIVE_GUARD_CONTINUATION.md)
uses this reference domain and the explicit projective shape-function bridge.
Equation (2.3), PDF p. 3, maps infinite-pyramid coordinates $(u,v,h)$ to
$(u/(1+h),v/(1+h),h/(1+h))$. Section 6.1, equation (6.1),
PDF p. 26, prints the five pullbacks

$$
(\widetilde\pi_1,\widetilde\pi_2,\widetilde\pi_3,\widetilde\pi_4,\widetilde\pi_5)
=\frac{((u-1)(v-1),u(v-1),(u-1)v,uv,h)}{1+h}.
$$

The volume keeps these printed signs explicit: its nonnegative weights
in order $(0,2,5,25,3)$ are
$(\widetilde\pi_1,-\widetilde\pi_2,-\widetilde\pi_3,\widetilde\pi_4,\widetilde\pi_5)$.
The elementary substitution $r=1/(1+h)$ supplies that correspondence.
The paper attributes its first-order input to Gradinaru and Hiptmair;
this note does not assign discovery priority to either this volume or
the higher-order construction.

The continuous apex extension,
coordinate Lebesgue integral coefficients $1/16$ and $1/12$, and interior
bubble calculation have their own elementary proofs in the volume.
Those exact coefficients are not attributed to this source. No Appendix
Table 2, journal-version title equivalence, approximation estimate or
native FIB response theorem is consumed from this v3 text.
