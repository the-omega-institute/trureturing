---
slug: bunth-pitrik-titkos-virosztek-2025-cost-cone-monotonicity
bibkey: bunthpitriktitkosvirosztek2025wasserstein
doi: 10.48550/arXiv.2501.08066
url: https://arxiv.org/abs/2501.08066v3
triage: theorem
motivation_gids:
  - D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.result
---

# Monotonicity of finite-spectrum quantum transport cost cones

## Problem

G. Bunth, J. Pitrik, T. Titkos and D. Virosztek, *Wasserstein distances and
divergences of order p by quantum channels*, arXiv:2501.08066v3
(27 April 2026; first version 14 January 2025), Conjecture 9, equation (48):

> For any separable Hilbert space ℋ, and for any parameter values
> 0<p≤p′≤∞ we have the relation 𝐂_p(ℋ) ⊆ 𝐂_{p′}(ℋ).

Equation (21) allows finite sets of self-adjoint observables, including
unbounded ones. Equation (22) assigns the cost
$C_{\mathcal A,p}=\sum_k|A_k\otimes I^T-I\otimes A_k^T|^p$.
Equation (27) defines $\mathbf C_p(\mathcal H)$ by restricting each
observable to finite spectrum. The target in
[#30813](https://github.com/the-omega-institute/trureturing/issues/30813)
is the finite-order inclusion for every $0<p\le q<\infty$, on arbitrary
complex Hilbert spaces, without a separability assumption.

## Motivation

The conjecture orders the available transport costs by their exponent.
The paper already proves the infinite-order endpoint in Proposition 15.
The finite-order inclusion supplies the missing intermediate comparisons
while retaining the exact cost operators, rather than merely comparing
their values on selected states.

## Gap

The supplied versioned quotation retains Conjecture 9, and the preregistered
task identifies Proposition 15 as the proved infinite-order endpoint. No
independent manuscript retrieval, citation census or worldwide novelty check
has been performed here. The finite-order inclusion is proved in the
algebraic tensor encoding described below, with no scalar-decomposition
or spectral-lifting hypothesis in its terminal statement.

## Route

For a finite list of real spectral values $\lambda_i$, seek finitely many
real lists $\mu_i^{(k)}$ satisfying

$$
 |\lambda_i-\lambda_j|^p
   =\sum_k|\mu_i^{(k)}-\mu_j^{(k)}|^q
 \quad\text{for all }i,j.
$$

For $p=q$, use the original list. For $0<p<q$, phase averaging of sine
differences represents the left side as a positive integral of the
right-side generators. Near zero, the scalar majorant is
$u^{q-p-1}$; near infinity, it is $u^{-1-p}$. Both are integrable, and
the representing constant is positive. This representation is classical
harmonic-analysis and metric-embedding background, not a novelty claim.

The selected route reuses the repository's finite measurable moment theorem.
Weight the sampling measure by the norm of its finite-dimensional vector
integrand and normalize the integrand pointwise. Its new measure is finite.
Exact finite cubature then applies, with selected points in the conull
positivity set. Rescaling the coefficients and using $q$-homogeneity absorbs
all nonnegative weights into the lists $\mu^{(k)}$. This avoids the
alternative closed-cone and separating-hyperplane proof supplied in the
problem brief without changing the exact decomposition target.

For a finite-spectrum self-adjoint $A=\sum_i\lambda_iP_i$, define
$B_k=f_k(A)$ with $f_k(\lambda_i)=\mu_i^{(k)}$. Spectral projections of
$B_k$ are sums of the $P_i$ in a common value fiber. Bilinearity gives
$\operatorname{cost}_p(A)=\sum_k\operatorname{cost}_q(B_k)$, and
concatenation handles a finite family of observables.

## Falsifier

The claimed conclusion would miss the source if it treated only a fixed
dimension, required separability, allowed an infinite sum of new
observables, retained a decomposition hypothesis in the terminal statement,
or compared numerical expectations instead of exact cost elements.

A self-adjoint observable with finite spectrum is bounded by its spectral
representation, so bounded continuous linear operators retain the source's
finite-spectrum class. The finite spectral cost can be written in the
algebraic tensor product after removing the transpose on the second factor.
The transpose is a linear bijection to operators on the dual Hilbert space;
the algebraic tensor representation on the Hilbert tensor product is
injective. These correspondences must accompany any use of that encoding.
The zero Hilbert space and empty observable family are included. Repeated
labels in a finite indexed family can be distinguished by scalar shifts
of the observables, which preserve all spectral gaps and costs, when
compared with the source's literal finite-set notation.

## Evidence

The source definitions and quoted conjecture are recorded in
`Library/Convexity/bunthpitriktitkosvirosztek2025wasserstein.md`.
The paper argument supplied with #30813 gives the integral representation,
closed-cone argument, finite decomposition and spectral-lift route above.
The terminal declaration
`D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.result` proves
`costCone p ⊆ costCone q` for arbitrary complex complete inner-product
spaces and real exponents `0 < p` and `p ≤ q`. Its proof uses the exact
finite decomposition and continuous-functional-calculus spectral lift.
The scoped verification covers the single Monotonicity source module and its
Reg mirror with explicitly imported analytic and finite-decomposition parts.
All twelve public theorem declarations use only `propext`, `Classical.choice`
and `Quot.sound` in their axiom closures.

All theorems have `proof_shape: bind-only`, including `result`. The sole
module has `admission_basis: open-problem-resolution`; its definitions and
auxiliary declarations all support that result. The sine representation,
finite decomposition and spectral lift are compositions of existing results,
not independent escape witnesses.

Every public theorem has a retained registration attempt. Nine are
`declared_validated`: `sineMoment_pos`, `phaseMoment_pos`,
`integrable_sineDistance`, `integral_sineDistance`, `finite_conic_moments`,
`finite_distance_decomposition_of_integral`, `finite_distance_decomposition`,
`specProj_cfc`, and `result`. Three remain `declared_unresolved` (`IE-C050`):

| Target in `D5.S3.Quantum.QuantumChannels.CostConeMonotonicity` | Rule | Reason | Missing evidence |
|---|---|---|---|
| `finiteObservable_cfc` | `source.observation_data` | `unclassified_form` | Recognized source observation-data form |
| `costElem_cfc` | `E8.serialization` | `incomplete_closure` | Complete accepted serialization closure |
| `costElem_of_decomposition` | `E8.serialization` | `incomplete_closure` | Complete accepted serialization closure |

For these three targets the registration module is
`Reg.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity.Monotonicity`;
the arena suffixes are respectively `FiniteObservable.arena`, `Cost.arena`,
and `Decomposition.arena`. Each key is the registration module, the fully
qualified arena, and the fully qualified target separated by `/`.
These boundaries are associated with
[#30813](https://github.com/the-omega-institute/trureturing/issues/30813).
Compilation does not resolve them; no online issue update is asserted.

## Triage

Tier 1 named conjecture in a research preprint, preregistered in #30813.
`theorem` identifies the completed finite-order proof in the stated
algebraic tensor encoding. The source correspondence and registration
boundaries are stated separately below.

The decisive mechanism is the positive mixture of $q$-power distances
representing a $p$-power distance. Equivalently, the real-line snowflake
$|x-y|^{p/q}$ has the corresponding $L_q$ distance representation, with
the $q$-power integral interpretation also valid when $q<1$. Finite spectral
sets allow exact finite replacement, not merely approximation.

Combining the finite-order result with the paper's Proposition 15 yields
the entire conjecture including
$p'=\infty$; the case $p=p'=\infty$ is reflexive. Proposition 13's
reverse non-inclusion applies when $\dim\mathcal H\ge3$,
$0<p<p'<\infty$, and $p'>1$. Equations
(49) and (50), and the paper's concavity inequality for $0<p\le2$, are
stated consequences in the source context; these consequences are not
formalized in this delivery and do not constitute additional proved Lean
claims here.

## ASSUMED-UNVERIFIED

The source version, literal quotation, proposition numbering and reported
consequences are supplied task data, not independently retrieved source
evidence. Exhaustive literature completeness and worldwide priority are
unverified. The finite-order terminal theorem is kernel-checked. The
transport between the algebraic tensor encoding and the source's
Hilbert-tensor cost operators is explained mathematically in the Scribe
commentary rather than formalized as a separate Lean bridge. The three
unresolved registration attempts described above remain audit boundaries,
without affecting the kernel-checked proof or its axiom closure.
