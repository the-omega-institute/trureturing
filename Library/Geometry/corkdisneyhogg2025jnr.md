---
bibkey: corkdisneyhogg2025jnr
authors: Josh Cork and Linden Disney-Hogg
year: 2025
title: Locations of JNR skyrmions
doi: 10.1007/s11040-025-09513-3
url: https://arxiv.org/abs/2505.00075v2
claim: Remark 13 conjectures strict positivity of the JNR triple sum (18) without the balance condition (15).
strata_touched: []
license: citation-only
triage: anchor
---

# Locations of JNR skyrmions

## Verified locator

DOI: 10.1007/s11040-025-09513-3

Source: https://arxiv.org/abs/2505.00075v2

## Source statements

Appendix A, Remark 13, PDF page 20 (printed page 19):

> The above proof shows that this is positive so long as Σᵢ (λᵢ²/|yᵢ|²) yᵢ = 0, however we conjecture that the sum in (18) is positive for any choice of yᵢ ∈ ℝ³∖{aᵢ}.

> We have a proof of this for N = 2, for N = 3 with equal weights, and when the yᵢ are on a single sphere, but a general proof without any constraint on the yᵢ appears to be a hard combinatorial problem.

Equation (3) defines “ρ(μ) = Σ_{i=0}^N λᵢ² / |x − aᵢ + μ|²”.
At μ = 0, with yᵢ = aᵢ − x, this is ρ(0) = Σᵢ λᵢ² / |yᵢ|².
The quaternion norm becomes the Euclidean norm for the pure imaginary poles and point.
Equation (18) is

$$
S=\frac{1}{\rho(0)}\sum_{i,j,k=0}^{N}
\frac{\lambda_i^2\lambda_j^2\lambda_k^2
\langle y_j-y_i,y_j-y_k\rangle}
{(\lVert y_i\rVert^2+\mu^2)(\lVert y_j\rVert^2+\mu^2)
\lVert y_j\rVert^2\lVert y_k\rVert^2}.
$$

## Encoding and scope

`D5/S3/Analytic/JNRRemarkThirteenPositivity` uses `Fin (N + 1)` for the poles,
`EuclideanSpace ℝ (Fin 3)` for their carrier, positive λᵢ and μ, injective poles,
and x distinct from every pole, with N ≥ 1. The source's displayed exclusion
is interpreted as x ≠ aᵢ, hence yᵢ ≠ 0, as specified in issue #19039.

The repository proof factors the two outer sums and completes a square at the
β-weighted barycentre. It concerns expression (18); it asserts no equality with
the source's earlier double sum away from condition (15), and no physical
realization. The source's other theorems retain their own hypotheses.

## Experiment and literature boundary

The exact and numerical comparison of (18) and the two square forms is in
`the-omega-institute/trureturing-experiments`,
`docs/reports/cork-disney-hogg-2025-jnr-remark13-positivity/`, commit
`7259d8d6c51ea9b5c1a72bc731e94dc9681817a9`.
The `check.py` SHA-256 is
`34bc783540f3264fc197e71a603340b23ad130f02f3d9595355bd26e83c299c9`;
`python3 check.py` exits 0 with `RESULT PASS 0`.

Issue #19039 records the literature screen, including the correction
DOI `10.1007/s11040-026-09577-9`. Literature completeness is
`ASSUMED-UNVERIFIED`: Google Scholar, Semantic Scholar and native MathDB were
not fully accessible in that screen. The SOS derivation was supplied by the
search seat recorded there; the Lean proof does not claim independent discovery.
