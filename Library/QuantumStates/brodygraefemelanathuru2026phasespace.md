---
bibkey: brodygraefemelanathuru2026phasespace
authors: Dorje C. Brody; Eva-Maria Graefe; Rishindra Melanathuru
year: 2026
title: "Phase-space measurements and decoherence for angular momentum systems"
doi: 10.48550/arXiv.2605.02696
url: https://arxiv.org/abs/2605.02696v1
claim: "Equation (53) conjectures that coefficientwise domination by the Husimi kernel restores positivity for J > 1/2."
strata_touched:
  - D5/S3/Quantum/Decoherence/DampedSpinKernelPositivityRefutation
license: citation-only
triage: anchor
---

# Phase-space measurements and decoherence for angular momentum systems

Page numbers refer to arXiv:2605.02696v1.

Page 2, equation (12):

> the matrix elements of the irreducible tensors in the standard Ĵz-bases are given by ⟨J, m′|T̂^J_{L,k}|J, m⟩ = √((2L + 1)/(2J + 1)) C^{Jm′}_{Jm Lk}, where the C^{JM}_{j1 m1 j2 m2} denote the Clebsch-Gordan coefficients.

Page 2, equation (13):

> ρ̂ = Σ_{L=0}^{2J} Σ_{k=−L}^{L} ρ_{Lk} T̂^J_{L,k}, ρ_{L,k} = tr((T̂^J_{L,k})† ρ̂).

Page 3, footnote 1:

> We use the convention Y^0_0 = 1, so that the spherical harmonics are orthonormal with respect to the uniform probability measure dµ^0_{θ,ϕ} = (4π)^{−1} sin θ dθ dϕ. This differs from the Condon–Shortley convention by a factor of √4π: Y_{Lm} = √4π Y_{Lm,CS}

Equations (35)–(36) fix $a_J=(2J+1)^{-1/2}$. Page 5, equation (44):

> F^σ(θ, ϕ, t) = a_J Σ_{L,k} e^{−γ L(L+1) t/2} ( C(2J, L) / C(2J+L+1, L) )^{−σ/2} ρ_{Lk}(0) overline(Y_{Lk}(θ, ϕ)).

Page 8, Section VI, the conjecture after equation (52) and equation (53):

> For J > 1/2 we do not have an exact result, but it seems reasonable to conjecture that positivity is ensured provided that the damped σ kernel in (44), due to decoherence, becomes no sharper than the Husimi (σ = −1) kernel. That is, if e^{−½γL(L+1)} ( C(2J,L)/C(2J+L+1,L) )^{−σ/2} ≤ ( C(2J,L)/C(2J+L+1,L) )^{1/2} (53) for all L, then we restore positivity.

The Lean encoding uses $n=2J$, doubled integer arguments for Racah's
Condon–Shortley Clebsch–Gordan formula, the standard spin basis ordered
$J,J-1,\ldots,-J$, and the scaled associated-Legendre harmonics of footnote 1.
The general kernel sums all $0\leq L\leq n$ and $-L\leq k\leq L$.
Density matrices reuse the positive-semidefinite unit-trace predicate in
`CoPRelativeQuantumnessRefutation.IsDensity`.
Equation (53) omits $t$ in its printed exponent; the witness has $t=1$, so
that reading and the time-dependent reading agree.
The refutation uses $J=3/2$, $\sigma=1$, $\gamma=\log(20/11)$, the
lowest-weight pure state and the north pole. Its exact value is
$-760927/256000000$ while every coefficient inequality holds.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2605.02696
- URL: https://arxiv.org/abs/2605.02696v1
