---
bibkey: hiairuskai2016contraction
authors: Fumio Hiai; Mary Beth Ruskai
year: 2016
title: "Contraction coefficients for noisy quantum channels"
doi: 10.1063/1.4936215
url: https://arxiv.org/abs/1508.03551v1
claim: "Conjecture 6.3. Equality holds in (45c) through (45e) above."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/HiaiRuskaiRiemannianContraction
license: citation-only
triage: anchor
---

# Exact Riemannian contraction coefficients of a qubit CQ channel

Journal of Mathematical Physics 57, 015211 (2016).

The arXiv v1 PDF, p. 19, states:

> Although the bounds in the above theorem are sufficient to disprove two conjectures as remarked below, we believe that they are optimal, i.e.,

> Conjecture 6.3. Equality holds in (45c) through (45e) above.

Theorem 6.2, p. 19, gives the three lower bounds

$$
\eta_{\widehat{\mathrm{WY}}}^{\mathrm{Riem}}(\Phi_{\alpha,\tau})
\geq\frac{\alpha^2(1+\sqrt{1-\tau^2})}{2(1-\tau^2)},\qquad
\eta_{x^{-1/2}}^{\mathrm{Riem}}(\Phi_{\alpha,\tau})
\geq\frac{\alpha^2}{\sqrt{1-\tau^2}},\qquad
\eta_{\mathrm{BKM}}^{\mathrm{Riem}}(\Phi_{\alpha,\tau})
\geq\frac{\alpha^2}{2\tau}\log\frac{1+\tau}{1-\tau}.
$$

The corresponding kernels are respectively
$(1+\sqrt{x})^2/(4x)$, $1/\sqrt{x}$, and $\log(x)/(x-1)$.
The BKM kernel takes its continuous value $1$ at $x=1$.
The parameters satisfy $\alpha\geq0$, $0<|\tau|<1$, and
$\alpha^2+\tau^2\leq1$, including $\alpha=0$ and either sign of $\tau$.

On p. 19 the source states:

> The next theorem treats a family of trace-preserving maps Φ_{α,τ} : M_2 → M_2 with two real parameters α,τ determined by t = (0,0,τ)^t and T = diag(α,0,0); more explicitly,

The channel formula is

$$\Phi_{\alpha,\tau}(w_0I+\mathbf w\cdot\boldsymbol\sigma)
=w_0I+\alpha w_1\sigma_1+\tau w_0\sigma_3.$$

Section 2.4, p. 7, states:

> Given a function κ ∈ K we define, for any A ∈ P_d, a linear map Ω_A^κ : M_d → M_d by

and gives

$$\Omega_A^\kappa(X)\equiv R_A^{-1}\kappa(L_AR_A^{-1})X,$$

> For each κ ∈ K the contraction coefficient of a CPT map Φ with respect to the monotone metric M^κ induced by κ is defined by

$$\eta_\kappa^{\mathrm{Riem}}(\Phi)\equiv
\sup_{\rho\in\mathcal D_d}\sup_{A\in\mathcal H_d^0,\,A\ne0}
\frac{\langle\Phi(A),\Omega_{\Phi(\rho)}^\kappa(\Phi(A))\rangle}
{\langle A,\Omega_\rho^\kappa(A)\rangle}.$$

> Associated with κ ∈ K a Riemannian metric M^κ on the Riemannian manifold D_d is defined by

$$M_\rho^\kappa(A,B)\equiv\langle A,\Omega_\rho^\kappa(B)\rangle,\qquad A,B\in\mathcal H_d^0,\ \rho\in\mathcal D_d.$$

Here $\mathcal D_2$ consists of positive definite trace-one complex matrices,
$\mathcal H_2^0$ consists of traceless Hermitian matrices, and
$\langle A,B\rangle=\operatorname{Tr}(A^*B)$.
In an orthonormal eigenbasis with eigenvalues $\lambda_i$,
the operator acts by
$(\Omega_\rho^\kappa(X))_{ij}
=\kappa(\lambda_i/\lambda_j)X_{ij}/\lambda_j$.
The Lean definition implements this spectral functional calculus, and uses
the real part of the trace for the metric; the trace has zero imaginary part.
Outside Hermitian foot points the operator is extended by zero. This extension
does not affect the strict density domain.

The exact upper bounds follow from the extreme-kernel estimate (46) and
a scalar pinching identity. The geometric representation uses
$2/(\pi\sqrt{s}(1+s))\,ds$ on $[0,1]$, expressed with $s=t^2$ as the
smooth weight $4/(\pi(1+t^2))\,dt$. The dual WY representation is one half
of the extreme kernel at zero plus one half of the geometric kernel.
The BKM representation uses $2/(1+s)^2\,ds$.
All three bounds are attained by $\rho=I/2$, $A=\sigma_1$.

## Verified locator

DOI: https://doi.org/10.1063/1.4936215

Source: https://arxiv.org/abs/1508.03551v1

Sections 2.2 and 2.4; Section 5, Proposition 5.5; Section 6,
Theorem 6.2 and Conjecture 6.3 (PDF p. 19); Appendix B.2.
