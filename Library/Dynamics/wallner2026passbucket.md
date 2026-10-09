---
bibkey: wallner2026passbucket
authors: T. Wallner, D. Krupke, A. Schmidt, and S. P. Fekete
year: 2026
title: "Pass the Bucket: Efficient, Robust, Local Load Balancing for Teams of Heterogeneous Robots"
doi: 10.48550/arXiv.2608.27085
url: https://arxiv.org/abs/2608.27085v1
claim: "Conjecture 1 asserts strict spectral contraction and decay of centered trajectories under repeated Token-1 damped transfers."
strata_touched:
  - D5/S1/Dynamics/TridiagonalSweeps/FinitePathDynamics
  - D5/S1/Dynamics/TridiagonalSweeps/TokenDampedSweepContraction
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2608.27085

Source: https://arxiv.org/abs/2608.27085v1

## Source statements

Section IV, page 3:

> Stacking these m relations yields a three-banded system A x′ = B x + c ⇔ x′ = A⁻¹ B x + A⁻¹ c, where A and B reflect the coefficients of x′ and x in the odd/even relations, and c collects the constants.

The odd source rows are
$x_i'=-x_i+2v_i x_{i+1}/(v_i+v_{i+1})+2v_{i+1}x_{i-1}/(v_i+v_{i+1})$.
The even source rows are
$(v_i+v_{i+1})x_i'-2v_{i+1}x_{i-1}'-2v_i x_{i+1}'=-(v_i+v_{i+1})x_i$.
The centered endpoint values are zero.

Section IV.B.1, page 4:

> This changes only the first pair’s relation: 2x₁/v₁ + (x′₁ − x₁)/(αv₁) = (x₂ − x₁)/v₂ + (x₂ − x′₁)/v₂, all other equations remain unchanged. In matrix form, with the same A, replace B by Bα and obtain u′ = Mαu, with Mα := A⁻¹Bα.

> Conjecture 1 (Spectral contraction): The damped transfer map Mα is repeatedly applied and its spectral radius satisfies ρ(Mα) < 1, such that u → 0 for 0 < α < 1.

The displayed Lean entries use zero-based pair indices, so a source odd row
has `i.val % 2 = 0`. There are `m = n − 1` pair coordinates and `m + 1`
positive velocities. The Token-1 first row is the travel-time relation above
solved for its next collision coordinate. Repeated application of the same
damped map is the scope of Conjecture 1.

## Related statements and scope

Lemma 2 (Rotation radius (G-isometry)), page 3, states that a symmetric positive
definite tridiagonal matrix G satisfies MᵀGM = G. Remark 2, pages 3–4,
states in particular that all eigenvalues of M lie on the unit circle.
Lemma 3 (Determinant contraction with one token), page 4, states
|det Mα| < 1 for 0 < α < 1. A determinant bound alone does not bound
every eigenvalue; the spectral conclusion requires the loss and observability
argument.

The finite-path proof uses the weighted Dirichlet form
$Q(z)=\sum_{j=1}^{n}|z_j-z_{j-1}|^2/v_j$ with both endpoints zero.
Local reflections preserve this form. The damped first event is the strict
convex combination $(1-\theta)I+\theta E_1$, where
$\theta=\alpha(v_1+v_2)/(v_2+\alpha v_1)$.
Its loss vanishes exactly when the first reflection fixes the vector.
Finite-path rigidity and boundary observability then exclude every
unit-modulus eigenvector. The formal result includes both the strict
complex spectrum bound and convergence of every real centered trajectory.

Token-all, arbitrary mixtures of the damped and undamped transfers, and RQ1
(eventual entry into the rotational, catch-up-free regime) remain open here.
The proof applies to the source's stated linear rotational-regime map;
it does not establish entry into that regime for the full collision process.
