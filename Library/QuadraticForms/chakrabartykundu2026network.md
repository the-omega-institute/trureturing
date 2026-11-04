---
bibkey: chakrabartykundu2026network
authors: Sudip Chakrabarty and Amit Kundu
year: 2026
title: Network nonlocality with tripartite entangled sources
doi: 10.48550/arXiv.2610.35838
url: https://arxiv.org/abs/2610.35838v1
claim: Proposition 1 expresses the squared Bell-state-measurement network optimum through orthogonal-direction quadratic optimization over two complete orthonormal frames and all four central-observable indices; the W-state paragraph gives the lower bound sqrt(13)/3 and reports no larger numerical value.
strata_touched:
  - D5/S3/Quantum/MeasurementGeometry/WStateBellMeasurementOptimum
license: citation-only
triage: anchor
---

# W-state Bell-state-measurement optimum

## Verified locator

DOI: 10.48550/arXiv.2610.35838

Source: https://arxiv.org/abs/2610.35838v1

Proposition 1 is on PDF page 4. The W-state paragraph and the table caption
are on PDF page 5. Appendix B, beginning on PDF page 11, proves the
variational formula of Proposition 1.

## Source statement

The W-state paragraph states:

> For the $W$ state, $\boldsymbol\tau_{33}=-\hat{\boldsymbol z}$ and $\boldsymbol\tau_{13}=\tfrac23\hat{\boldsymbol x}$ are orthogonal, which gives $\mathcal N_c\ge\sqrt{13}/3\approx1.202$. The numerical optimization over frames finds no larger value.

The table caption states:

> For $\mathcal N_c(W)$ the value $\sqrt{13}/3$ is a proven lower bound, and the numerics find no larger value.

On PDF page 4 the observable sentence is:

> We write $A_i=\boldsymbol e_i\cdot\boldsymbol\sigma$ and $C_j=\boldsymbol f_j\cdot\boldsymbol\sigma$, and set $A_0=C_0=\mathbb I$.

The correlation-vector equation on that page is
$\boldsymbol\tau_{\mu\nu}=(\operatorname{Tr}[\rho A_\mu\otimes\sigma_k\otimes C_\nu])_{k=1,2,3}$.
The next paragraph states:

> The network value therefore depends on how much of $\boldsymbol\tau_{\mu\nu}$ and $\boldsymbol\tau_{\mu'\nu'}$ two perpendicular directions can capture. For two vectors $\boldsymbol\tau,\boldsymbol\tau'$ this is

and defines
$\Lambda(\boldsymbol\tau,\boldsymbol\tau')=\max_{\boldsymbol n\perp\boldsymbol n'}[(\boldsymbol\tau\cdot\boldsymbol n)^2+(\boldsymbol\tau'\cdot\boldsymbol n')^2]$.
Proposition 1 states:

> For two copies of a three-qubit state $\rho$, Bell-state measurements at the central nodes and projective measurements at the end nodes, the largest value of $\sqrt{|I|}+\sqrt{|J|}$ is $\mathcal N_c(\rho)$, with

$\mathcal N_c(\rho)^2=\max_{\{\boldsymbol e_i\},\{\boldsymbol f_j\}}\max_{\mu\nu,\mu'\nu'}\Lambda(\boldsymbol\tau_{\mu\nu},\boldsymbol\tau_{\mu'\nu'})$.

> The maxima run over the frames of the two central nodes and over the indices $\mu,\nu,\mu',\nu'\in\{0,1,2,3\}$.

## Mathematical scope

The associated Lean statement uses the literal normalized W ket on
$(\mathrm{Fin}\,2\times\mathrm{Fin}\,2)\times\mathrm{Fin}\,2$, its
rank-one density matrix, and the displayed variational supremum. The
conclusion is the exact value $\sqrt{13}/3$ for this Bell-measurement
class, including zero and repeated central indices. The larger
product-projective measurement class and noisy states are separate
questions.

The decisive identity is
$9\|T(a,c)\|^2=(2a_0c_0+2a_1c_1-a_2c_2)^2+4a_2^2+4c_2^2$
for unit vectors $a,c$. Parseval identities for complete orthonormal
frames bound every index pair; the standard frame attains $13/9$ before
taking the square root. This is a repository derivation of the upper
bound, rather than an attribution of that upper bound to the source.

## Evidence boundary

The preregistration is issue
[23251](https://github.com/the-omega-institute/trureturing/issues/23251).
It identifies the exact experiment in
`the-omega-institute/trureturing-experiments`, report commit
`3e3d376e925060a7fa7e3a299ae6e2f7b98edfa0`, path
`docs/reports/wbsm-2610/`, integrated branch tip
`5ec051dd6edc3b3bafa06423169bd4da1c5d382d`, checker SHA-256
`aac9922feda7ca6dc2a991f15dcfce11a266be5d9b4df051a9c92d89ddb317a2`,
reported exit code 0 and final line `ALL_CHECKS_OK`. Those finite checks
are supplementary evidence and do not establish the universal optimum.
The literature screen in that issue is `ASSUMED-UNVERIFIED` for
completeness.
