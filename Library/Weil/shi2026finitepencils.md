---
bibkey: shi2026finitepencils
authors: Yaoming Shi
year: 2026
title: Construction of Finite Hilbert–Pólya Matrices from Weil's Explicit Formula
doi: null
url: https://arxiv.org/abs/2609.04908v1
claim: A finite Hermitian definite quotient pencil has real spectrum under a simple least eigenvalue and a positive compressed metric; transfer to the full arithmetic spectrum still requires uniform relative perturbation estimates.
strata_touched: []
license: citation-only
triage: anchor
---

# Finite Weil pencils and their relative-transfer boundary

The primary source is [Shi, arXiv:2609.04908v1](https://arxiv.org/html/2609.04908v1),
submitted 4 September 2026. The source identifies its manuscript as
Version 12. Theorem 4.1 and the relative-transfer discussion in Sections
1.4--1.5 and 4.8--4.9 were inspected. This note does not independently
verify the full preprint, its numerical experiments or its proofs.

## What the finite construction supplies

For the arithmetic matrix $\mathbf S_{N,L}$ the source subtracts its
least eigenvalue $\epsilon_{N,L}$ to form
$\mathbf W_{N,L}=\mathbf S_{N,L}-\epsilon_{N,L}I$.
It uses the fixed contrast space
$\mathcal V_{N,L}^0=\ker\boldsymbol\delta_{N,L}^{\mathsf T}$,
where $\boldsymbol\delta_{N,L}$ represents evaluation at zero in the
chosen Fourier coordinates. Thus coefficient sum zero is this
evaluation constraint; it is not the theta model's $\nu$-mean constraint.
An orthonormal basis matrix $\mathbf C_{N,L}$ gives the metric and
differentiation form

$$
\mathbf G_{N,L}=\mathbf C_{N,L}^*\mathbf W_{N,L}\mathbf C_{N,L},
\qquad
\mathbf K_{N,L}=\mathbf C_{N,L}^*\mathbf W_{N,L}
\mathbf D_{L,N}\mathbf C_{N,L}.
$$

Theorem 4.1 assumes a simple $\epsilon_{N,L}$ and
$\mathbf G_{N,L}\succ0$. It obtains a Hermitian definite pencil
$\mathbf K y=\mu\mathbf G y$, a self-adjoint realization in that
metric and real generalized eigenvalues. Its scale invariance and
contrast construction are existing source results to reuse, rather
than a new project method. Shifting by the least eigenvalue does not
prove that the unshifted arithmetic form is nonnegative.

Section 4.8 also defines an unshifted pencil using
$\mathbf G^{\rm un}=\mathbf C^*\mathbf S\mathbf C$ and
$\mathbf K^{\rm un}=\mathbf C^*\mathbf S\mathbf D\mathbf C$.
Its definite-pencil conclusion requires
$\mathbf G^{\rm un}\succ0$. It does not supply unconditional
all-scale positivity of that metric. The section states that relating
the shifted and unshifted low-energy limits needs relative estimates
in the unshifted metric.

## Reconstruction and the estimate still required

Section 1.4 describes an exact finite zero-side reconstruction from
$N$ supplied distinct positive real ordinates. It identifies the
resulting pencil spectrum with their signed ordinates. This theorem
does not obtain those ordinates from unproved full arithmetic
convergence, or exclude off-line zeros.

Sections 1.5 and 4.9 leave a whole-pencil relative perturbation theorem
and uniform control of the compressed metric as the transfer problem.
The positive zero-tail decomposition used in Section 4.9 assumes RH.
Numerical agreement at selected parameters is not that transfer
estimate. The paper explicitly claims no proof of RH.

The [original theta variance metric](https://github.com/the-omega-institute/trureturing-experiments/blob/main/docs/reports/theta-mixed-matrix/weighted-window-metric.md)
is another concrete relative-estimate target. Its ground, measure,
odd derivative space and metric $B_L$ are independently fixed by the
original form. No parameter map identifying Shi's contrast metric or
least-eigenvalue shift with that $B_L$ is supplied here. Consequently
the source gives neither the theta endpoint $c=1/2$ nor a cofinal
sequence $c\uparrow1/2$, RH, full Robin or Lean certification.

The inspected versioned HTML has SHA-256
`eb82b35d55876f598ee91b816878900c5db18c5ee5db7bc34ba8d651ef83ecb0`.
Only a bibliographic reference and scope summary are retained; no
third-party program or source proof is copied.
