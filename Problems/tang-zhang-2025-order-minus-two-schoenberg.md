---
slug: tang-zhang-2025-order-minus-two-schoenberg
bibkey: tang2025schoenberg
doi: 10.48550/arXiv.2508.10341
url: https://arxiv.org/abs/2508.10341v3
triage: theorem
motivation_gids:
  - D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo.result
---

# Tang–Zhang: the sharp order −2 Schoenberg inequality

## Problem

Q. Tang, T. Zhang, "Sharp Schoenberg type inequalities and the de Bruin–Sharma problem", arXiv:2508.10341v3 (5 Dec 2025), §6, p. 31.

> The identity (5.2) leads us to the following conjectural refinements of Theorem 6.1 in the case of order −2.

> Conjecture 6.3. Let P(z) = z ∏_{j=1}^n (z − z_j), z_j ∈ C \ {0}, and let w_1, …, w_n denote the zeros of P′(z). Then Σ_{k=1}^n 1/|w_k|² ≤ 3 Σ_{j=1}^n 1/|z_j|² + |Σ_{j=1}^n 1/z_j|². (6.9) Moreover, equality in (6.9) holds whenever z_1, …, z_n all lie on the same line passing through the origin.

> In the case n = 2 we can verify Conjecture 6.3 by an explicit computation. (Proposition 6.4.)

Theorem 6.1 there proves the weaker right side (n+3) Σ 1/|z_j|².
The exact public definitions and result are:

```lean
noncomputable def P {n : ℕ} (z : Fin n → ℂ) : Polynomial ℂ :=
  Polynomial.X * ∏ j, (Polynomial.X - Polynomial.C (z j))

def claim : Prop := ∀ (n : ℕ) (hn : 1 ≤ n) (z : Fin n → ℂ), (∀ j, z j ≠ 0) →
    (((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖⁻¹ ^ 2)).sum ≤
      3 * ∑ j, ‖z j‖⁻¹ ^ 2 + ‖∑ j, (z j)⁻¹‖ ^ 2) ∧
    ((((Polynomial.derivative (P z)).roots.map (fun w => ‖w‖⁻¹ ^ 2)).sum =
      3 * ∑ j, ‖z j‖⁻¹ ^ 2 + ‖∑ j, (z j)⁻¹‖ ^ 2) ↔
        ∀ j, ∃ r : ℝ, z j = (r : ℂ) * z ⟨0, hn⟩)

theorem result : claim
```

Here n≥1, all z_j are nonzero complex numbers, and roots of the derivative
are counted with multiplicity. No simplicity, distinctness, reality or
common argument hypothesis is imposed on the nonzero roots. Since
P′(0)=∏_j(−z_j)≠0, no critical point is zero. The final equivalence says
that all z_j are real multiples of the nonzero first root, which is exactly
collinearity on a line through the origin.

## Motivation

The unrestricted conjecture is preregistered in
https://github.com/the-omega-institute/trureturing/issues/18487.
It is an explicit external conjecture in the first problem tier. The
motivation address names its general-degree resolution, including the
necessary as well as sufficient equality condition.

## Gap

The source proves the n=2 case in Proposition 6.4 and gives the weaker
Theorem 6.1 bound. Conjecture 6.3 asks for the displayed sharp bound for
general n and states the collinear sufficient equality condition.
The source locator and the boundary of the literature evidence are in
[tang2025schoenberg](../Library/Zeros/tang2025schoenberg.md).
The formal result proves the full conjecture and strengthens its equality
statement to an equivalence.

## Route

Write b_j=1/z_j, D=diag(b_j), J for the n by n all-ones matrix, and
B=D(I+J)=D+DJ. The perturbation DJ has rank one for n≥1 and nonzero b_j.
Reversing the derivative polynomial gives the exact identity

$$
(P')^{\mathrm{rev}}(t)=\left(\prod_j(-z_j)\right)\det(tI-B).
$$

Consequently the reciprocal critical points are the eigenvalues of B,
with multiplicity. Put s=√(n+1), c=1/(s+1) and

$$
R=I+cJ,\qquad R^{-1}=I-\frac{1}{s(s+1)}J.
$$

Then R is Hermitian, R²=I+J, and RBR⁻¹=RDR. Cyclicity of trace yields

$$
\|RDR\|_F^2
=\operatorname{tr}\bigl(D^*(I+J)D(I+J)\bigr)
=3\sum_j|b_j|^2+\left|\sum_j b_j\right|^2.
$$

The Schur–Frobenius inequality bounds the sum of squared eigenvalue moduli
by this Frobenius norm. Equality holds exactly when RDR is normal.
Cancelling R and R⁻¹ reduces normality to

$$
\overline{b_i}b_j=b_i\overline{b_j}\quad\text{for all }i,j.
$$

Because the b_j are nonzero, this means each b_j/b_1 is real. Inversion
preserves collinearity through the origin, giving precisely the equality
criterion in `claim`.

## Falsifier

A finite nonempty family of nonzero complex z_j whose derivative-root
reciprocal-square sum exceeds the stated bound would refute the conjecture.
Equality for a noncollinear family, or strict inequality for a collinear
family, would refute the strengthened equality criterion. All root sums
must include algebraic multiplicities; a floating-point root list alone
cannot certify any of these alternatives.

## Evidence

`D5/S3/Zeros/CriticalPoints/TangZhangOrderMinusTwo.result` proves `claim`.
The characteristic-polynomial, reciprocal-root, trace and collinearity
identities occur on its proof path. Its matrix estimate is supplied by
`D5/S3/Zeros/CriticalPoints/SchurFrobeniusInequality.schur_frobenius`,
which includes the normality equality criterion. Both public theorems have
proof_shape: content: the matrix triangularization and equality argument,
and the polynomial-to-matrix reduction, supply the substantive proof.
The settlement has admission_basis: open-problem-resolution for the
preregistered external Conjecture 6.3.

## Triage

The modules have computational_content.kind=none. The conclusion holds
for every admissible finite family and every n≥1, without a degree cutoff.

### What the settlement shows

**PROVED — reciprocal critical-point spectrum.** The private
`roots_derivative` identity in the proof of `result` identifies the entire
multiset of inverse critical points with the characteristic roots of the
rank-one perturbation D(I+J). This is an exact multiplicity-preserving
identity, rather than an estimate on individual roots.

**PROVED — exact symmetrization.** The private `spectral_inequality`,
`sandwich_reduction` and `core_trace` steps construct R and its inverse and
prove that the squared Frobenius norm of RDR is exactly the conjectured
right side. Thus Schur's inequality gives the coefficient 3 without any
extra degree-dependent loss.

**PROVED — equality if and only if collinear.** The public `result`
proves both equality directions. The conjecture's “whenever” can therefore
be strengthened to “if and only if”, including repeated nonzero roots.

**PROVED mathematical consequence — recovery of Theorem 6.1.** By the
finite Cauchy–Schwarz inequality,

$$
\left|\sum_j b_j\right|^2\le n\sum_j|b_j|^2,
$$

so the proved sharp right side is at most (n+3)Σ_j|b_j|². This recovers
the source's weaker order −2 bound. This corollary is a mathematical
consequence of `result` and Cauchy–Schwarz; it is not a separately checked
conclusion of these Lean modules.

**OPEN — higher negative even orders.** Whether the same similarity yields
sharp bounds for order −2m, including a derivation or refinement of
Section 7's order −4 inequality, remains open here. The checked result
controls the second powers of reciprocal critical-point moduli; it makes
no assertion about higher powers.

## ASSUMED-UNVERIFIED

The supplied source quotation and locator identify the conjecture in v3;
they do not establish the absence of subsequent settlements. No exhaustive
absence or worldwide priority is claimed. Theorem 6.1's corollary and the
higher-order extension have no additional Lean proof in these modules.
