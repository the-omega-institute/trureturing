---
slug: dinov-2026-equipartition-duality-minimum-refutation
bibkey: dinov2026kime
doi: 10.48550/arxiv.2607.07851
url: https://arxiv.org/abs/2607.07851v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Information/CovarianceSumBound
---

# The within-DOF minimum clause of equipartition duality

## Problem

Dinov, arXiv:2607.07851v1, Conjecture 3.22 (Equipartition duality):

> Fix $n\geq2$, an entropy value $s$, and an action marginal $\rho_{\mathbf J}$ on $(0,\infty)^n$. Among all states on $\mathbb T^n\times(0,\infty)^n$ with entropy $\geq s$ and action marginal $\rho_{\mathbf J}$, the phase-equipartitioned product state (unique when it exists) simultaneously (i) maximizes the entropy, (ii) minimizes every within-DOF uncertainty $u_j$, and (iii) is the unique state at which the per-DOF conjectured bound of Problem 3.17(b) is saturated for all $j$; moreover it is the unique fixed point, with the given marginal, of the multi-DOF kime-deformed semigroup $\partial_t\tilde\rho=\sum_j(-\omega_j\partial_{\theta_j}+\varepsilon\partial^2_{\theta_j})\tilde\rho$.

This dossier anchors the necessary minimum clause (ii). The other clauses
are quoted to identify the original simultaneous assertion and receive no
separate settlement.

## Motivation

Covariance inequalities concern the actual coordinate law; uniformity of a
different marginal does not determine that covariance. The existing
`D5/S3/Quantum/Information/CovarianceSumBound` develops covariance constraints
for density states. Here the question is whether fixed actions and an entropy
lower bound force uniform phases to minimize each actual covariance determinant.

## Gap

Preregistration [#13139](https://github.com/the-omega-institute/trureturing/issues/13139)
specifies the original quantified assertion and this normalized-density route
before the mathematical probes. The accepted independent source reviews found
no resolution in their checked arXiv topic/history, OpenAlex citation and
MathDB scopes. The source remains a v1 conjecture. Semantic Scholar returned
HTTP 429; it contributes no negative literature evidence. These bounded
readings are described in the associated Library note.

## Route

Take two independent actions with density $e^{-J}$ on positive reals and two
independent phases with density

$$\phi(\theta)=\frac{1+\tfrac12\cos(2\theta)}{2\pi}.$$

Use the actual source map $(q,p)=(\sqrt{2J}\sin\theta,\sqrt{2J}\cos\theta)$.
The comparator has uniform phases and the same joint action density
$r(J_1,J_2)=e^{-(J_1+J_2)}$. Both entropies are finite and nonnegative, so
both states satisfy the same threshold $s=0$.

For one degree of freedom the nonuniform state has mean zero and covariance
$\operatorname{diag}(3/4,5/4)$; the comparator has covariance $I_2$.
Independence gives full positive-definite covariances
$\operatorname{diag}(3/4,5/4,3/4,5/4)$ and $I_4$. Both uncertainties are
$\sqrt{15/16}<1$ in the nonuniform state. Both strict comparisons occur in
the contradiction with the asserted minimum inequalities.

## Falsifier

The original assertion for every $n\geq2$ implies its minimum clause at
$n=2$, which implies `dinovTwoDofMinimumClause` on the certified subclass.
That predicate universally quantifies the entropy threshold, joint action
density, Cartesian state and existing phase-uniform product comparator, then
requires the comparator's uncertainty to be no larger for both Bool degrees
of freedom. `result : ¬ dinovTwoDofMinimumClause` refutes this necessary
consequence and therefore the simultaneous assertion as written.

## Evidence

`D5/S3/Quantum/Information/DinovOriginalMinimumRefutation.lean` retains the
needed source definitions and one public result. All analytic and realization
proofs are local to that result. The actual measures are AddCircle(2π)
angular volume, positive-action Lebesgue measure and standard Cartesian
volume. The proof certifies measurable nonnegative unit-mass densities,
integrable entropy with the exact source equality, all four coordinates in
L2, full positive-definite covariance, both angular fiber integrals, and
both torus and Cartesian joint action pushforwards.

## Triage

Tier 1 published conjecture; `proof_shape: bind-only`, `escape_witness: none`,
and `admission_basis: open-problem-resolution` under #13139. The Scribe
result carries `OpenProblemResolutionClaim(Refuted)` for this dossier, with
the refutation attributed `FromRepo`. The original conjecture is literature.
The utility is `certified-instance` with the typed negation of this module's
minimum predicate.

- **Proved in result:** all required state and source certificates, and
  failure of both minimum inequalities at the same realization and threshold.
- **Failure mechanism:** the second phase harmonic reallocates the q and p
  variances to $3/4$ and $5/4$ while preserving the joint action marginal.
  Their product is $15/16$, below the uniform-phase value. The entropy
  lower bound permits this anisotropy at $s=0$.
- **Open:** a corrected minimum principle with sufficient additional
  constraints. Fixed action marginals and a lower entropy bound alone do
  not provide those constraints.
- **Boundary:** failure of clause (ii) refutes the simultaneous conjecture;
  no separate theorem about entropy maximization, saturation uniqueness,
  Problem 3.17(b) on a fixed symplectic orbit, or the semigroup follows.
  Neighboring source inequalities and evolution results are not refuted.

## ASSUMED-UNVERIFIED

The paper-to-predicate necessary-instance implication is source correspondence
checked by the accepted independent reviews, not a generic-$n$ Lean theorem.
The interpretation of latent phase as experimental kime is not an empirical
conclusion. No global originality claim or Cartesian smoothness-at-zero
certificate is made. Information-escape registration remains paused under
CLAUDE.md §3.9; no registration-completion state is claimed.
