# Positive Laplace boundary kernels

## Abstract

Boundary limits of a positive Laplace transform obey finite Gram inequalities and spectral budgets.

**Theorem 1.1 (Conjugate boundary limits).**

Lean statement: `D5/S3/Analytic/Laplace/PositiveSpectralBudget.boundary_limit_conjugate`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PositiveSpectralBudget.boundary_limit_conjugate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a positive measure on the real line, the Laplace transform at sigma-i*t is the conjugate of its value at sigma+i*t. Consequently, if sigma times the latter transform has a limit as sigma decreases to zero, the opposite frequency also has a limit, equal to the complex conjugate.

**Theorem 1.2 (Finite Gram positivity at the boundary).**

Lean statement: `D5/S3/Analytic/Laplace/PositiveSpectralBudget.boundary_positive_definite`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PositiveSpectralBudget.boundary_positive_definite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let mu be a positive measure on the real line such that exp(-sigma*y) is integrable for every sigma>0. Fix a finite family of frequencies t(j), and suppose the limit L(t(j)-t(k)) of sigma times the Laplace transform at sigma+i*(t(j)-t(k)) exists at each pairwise difference. For complex coefficients a(j), the double sum a(j)*conjugate(a(k))*L(t(j)-t(k)) is a nonnegative real number. This is the finite Gram positivity of the positive measure carried to boundary limits, as in step (a) of Proposition 486.1: characters give rank-one Gram matrices, integration preserves positivity, and the boundary limit preserves each finite matrix inequality.

**Theorem 1.3 (A budget for negative boundary masses).**

Lean statement: `D5/S3/Analytic/Laplace/PositiveSpectralBudget.same_sign_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PositiveSpectralBudget.same_sign_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let t(1),...,t(n) be distinct nonzero frequencies. Suppose boundary limits exist at all pairwise differences of 0,t(1),...,t(n), and Re(L(u))<=0 at each nonzero such difference u. Suppose Re(L(t(j)))<=-c with c>0. Then n*c^2<=4*L(0)^2. Apply the finite Gram inequality to the augmented family 0,t(1),...,t(n), with a real nonnegative coefficient s at zero and coefficient one elsewhere, and optimize the resulting quadratic inequality.

**Theorem 1.4 (A quadratic budget in a short window).**

Lean statement: `D5/S3/Analytic/Laplace/PositiveSpectralBudget.gap_budget`

*Proof.* Machine-checked in Lean as `D5/S3/Analytic/Laplace/PositiveSpectralBudget.gap_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let t(1),...,t(n) be a distinct finite family with abs(t(j)-t(k))<delta. Suppose boundary limits exist at all pairwise differences of 0,t(1),...,t(n), and L(u)=0 at each such difference with 0<abs(u)<delta. Then the sum of abs(L(t(j)))^2 is at most L(0)^2. In particular the conclusion applies in every interval of length less than delta. The off-diagonal entries vanish. Test the augmented matrix with the coefficient L(0) at zero and -conjugate(L(t(j))) at the other frequencies; when L(0)=0, use coefficient one at zero.

## References

- Truth anchor: `D5/S3/Analytic/Laplace/PositiveSpectralBudget.boundary_limit_conjugate`
- Truth anchor: `D5/S3/Analytic/Laplace/PositiveSpectralBudget.boundary_positive_definite`
- Truth anchor: `D5/S3/Analytic/Laplace/PositiveSpectralBudget.gap_budget`
- Truth anchor: `D5/S3/Analytic/Laplace/PositiveSpectralBudget.same_sign_budget`
- Dependency: [D5/S3/Analytic/Fourier/PositiveDefinite/Closure](../Fourier/PositiveDefinite/Closure.md)
