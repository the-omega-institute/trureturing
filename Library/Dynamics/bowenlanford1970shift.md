---
bibkey: bowenlanford1970shift
authors: Rufus Bowen and Oscar E. Lanford III
year: 1970
title: Zeta functions of restrictions of the shift transformation
doi: null
url: https://people.math.harvard.edu/~knill/history/lanford/papers/BowenLanford.pdf
claim: Finite forbidden-word shifts have periodic-point counts given by traces of a finite transition matrix and dynamical zeta equal to its inverse characteristic determinant.
strata_touched: []
license: citation-only
triage: anchor
---

# Zeta functions of restrictions of the shift transformation

The primary scan, printed pp.43–45, defines the two-sided shift, its
periodic-point zeta and the transition matrix for a finite forbidden-word
set. Section 2, Lemmas 1–2 and Theorem 1, gives

$$
N_m=\operatorname{tr}(T^m),\qquad
\exp\left(\sum_{m\ge1}\frac{N_mz^m}{m}\right)
=\prod_j(1-\lambda_jz)^{-1}=\det(I-zT)^{-1},
$$

where eigenvalues are counted with multiplicity. The local power series
has its own convergence domain; rational continuation outside that domain
is not a convergent sum of periodic configurations.

The example on printed pp.44–45 forbids `00` and uses
$T=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$.
Exchanging the two symbols gives the forbidden-`11` matrix
$Q=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$.
Both have characteristic polynomial $X^2-X-1$ and
$\det(I-zT)=1-z-z^2$. The scan's final example denominator on p.45
prints $1-z+z^2$, which conflicts with its displayed matrix and
eigenvalues. The general theorem and the determinant calculation supply
the minus sign; the conflicting printed example formula is not used.

The result is consumed inside the labelled-seam to periodic-point bridge
in §5 of [the seams continuation](../../docs/develop/theory/AURIC_FIB_SEAMS_CYCLES_ARITHMETIC_BOUNDARY_RECONSTRUCTION.md).
The matrix-periodic configurations belong to a specified transition graph,
not automatically to the original ordered substitution tree. The paper
does not supply a physical cycle, a Riemann zeta identification or RH.
