---
slug: chen-2026-fixed-order-inclusion
bibkey: chen2026fixedorderinclusion
doi: null
url: https://arxiv.org/abs/2610.09168v1
triage: theorem
motivation_gids:
  - D5/S3/Estimation/ChenFixedOrder/FixedOrderWitness.fixedOrderWitness_holds
---

# Chen's fixed-order inclusion conjecture

## Problem

For each fixed positive integer $r$, exhibit two sequences of sampling
designs on the same finite populations and the same fixed-size sample
spaces that agree on every inclusion event of order at most $r$, while
the laws of their common centered and scaled sample mean converge weakly
to distinct limits. Both the sample size and the population size must
tend to infinity. Chen states the conjecture in §1 and again in §6 of
arXiv:2610.09168v1. The paper establishes the order-two case. [§1](https://arxiv.org/html/2610.09168v1#S1.p11) · [§6](https://arxiv.org/html/2610.09168v1#S6) · [Preregistration #32021](https://github.com/the-omega-institute/trureturing/issues/32021)

### Statement echo

| Clause | Lean counterpart |
| --- | --- |
| Finite populations and prescribed sample sizes grow without bound | `Population m` has two strata of size $n_m^3$ each, where `sampleSize m` is $n_m=(m+1)^2$. Both growth clauses are in `fixedOrderWitness`. |
| Two sequences of designs on the same fixed-size samples | For each $r>0$, `fixedOrderWitness` gives $P_m,Q_m$ as probability measures on `Sample m`, the subsets of size $n_m$. The baseline $P_m$ is uniform. |
| Every inclusion probability through the fixed order agrees | For every stage $m$ and every finite subset $A$ with cardinality at most $r$, the masses of `inclusion m A` under $P_m$ and $Q_m$ are equal. This includes the empty set and exact agreement at each stage. |
| The two weak limits are distinct for a common estimator | Each map uses `estimator m`, the sample mean centered by the population mean and scaled by $\sqrt{n_m}$. The values are balanced signs with population mean zero. The limits are the standard Gaussian and a law $\nu$ unequal to it. |

## Motivation

Inclusion probabilities are design-level information used in finite-population
inference. The theorem shows that any prescribed finite order of exact
agreement leaves freedom in the weak limit, even with equal first-order
inclusion and a uniform without-replacement baseline.

## Gap

Chen's construction in the cited version treats order two. The general
question requires one construction for every fixed finite order, with
agreement on the events for specified units and two convergent estimator
laws on a shared sequence of populations.

## Route

The uniform baseline comes from independent draws of balanced signs
conditioned on distinct labels. The collision probability tends to zero
because the population has size $2n_m^3$. Forgetting the draw order then
gives the uniform fixed-size law, and the normalized sign-sum limit
transfers to its estimator.

Conditional on sampling $k$ positive units, the probability of including
a specified set with $a$ positive and $b$ negative units is
$\binom{k}{a}\binom{n_m-k}{b}/[\binom{n_m^3}{a}\binom{n_m^3}{b}]$
when such units exist in the population. The falling factorials yield
a polynomial of degree at most $a+b$ in $k$ and hence also in the
estimator, which is affine in $k$ at each stage. Weighting a sample by
a density in the estimator therefore preserves each such event if the
signed density change cancels polynomials through the prescribed order.

For $R=\max(r,2)$, use the same bounded adjugate tilt on each baseline
estimator law. Weak continuity gives the tilt of the standard Gaussian as
the second limit. The expected Gaussian residual strictly increases under
that tilt, so the two weak limits differ.

## Falsifier

A failed stagewise event identity, a density that does not define a
probability, a failure of either claimed convergence, or equality of the
two limiting laws would defeat the proposed witness. The finite inclusion
identity, density bounds and normalization, weak continuity, and strict
expectation gap supply the respective checks.

## Evidence

- `ChenFixedOrderSampling.exists_inclusionPolynomial` supplies the
  polynomial degree bound and integration identity for each specified set.
- `ChenDensityBridge.tiltedSample_spec` proves the pullback law has the
  asserted pushforward and preserves inclusion through the matched order.
- `GaussianLimit.uniformSampleLaw_tendsto` gives the Gaussian baseline
  for the same estimator and sample spaces.
- `MomentPerturbation.density_bounds`, `integral_density`,
  `integral_eval_mul_density_sub_one`, and `continuous_tilted` give
  boundedness, normalization, polynomial cancellation, and weak
  continuity. `tilted_gaussian_separation` gives a strict expectation gap.
- `fixedOrderWitness_holds` proves the conjunction in `fixedOrderWitness`.
  Its axiom closure is `Classical.choice`, `Quot.sound`, and `propext`.

## Triage

- **Kernel-checked.** For each fixed $R$, the tilt construction and
  polynomial cancellation apply to any real probability law $\mu$,
  including singular windowed Gram matrices. Put $w(x)=\max(1-|x|,0)$,
  $G_{ij}=\int w(x)x^{i+j}\,d\mu$ and
  $c_i=\int w(x)x^{i+R+1}\,d\mu$ for $0\le i,j\le R$. With
  $u=\operatorname{adj}(G)c$, the residual is
  $h(x)=w(x)(\det(G)x^{R+1}-\sum_j u_jx^j)$. The moments of $h$
  through order $R$ form the vector $\det(G)c-Gu=0$ by the adjugate
  identity. The change of density is $1+\varepsilon h$ with a positive
  scalar chosen from the coefficient bounds to keep the density between
  $1/2$ and $3/2$. The signed integrands are compactly supported, so
  the cancellation itself requires no global polynomial moments.
  These statements use `MomentPerturbation.integral_eval_mul_density_sub_one`,
  `density_bounds` and `integral_density`. The matrix entries are
  bounded continuous test integrals, yielding weak continuity of the
  law-valued tilt in `continuous_tilted`.
- **Proved in prose.** The event mechanism applies whenever the
  conditional baseline probability of the event given the estimator
  $X$ is a polynomial $p(X)$ of degree at most $R$. If the estimator
  law is $\mu$ and the sample density is $g(X)$, the change in event
  probability is $\mathbb E[(g(X)-1)1_A]=\int (g(x)-1)p(x)\,d\mu$,
  by conditional expectation. It vanishes under polynomial cancellation.
  `exists_inclusionPolynomial` and `tiltedSample_spec` provide the
  kernel-checked special case for the balanced two-stratum designs.
- **Kernel-checked.** For the standard Gaussian the windowed Gram matrix
  is positive definite by `gaussian_gram_posDef`. The residual is nonzero
  and its expectation gain is $\varepsilon\int h^2\,d\mu>0$, as proved
  by `tilted_gaussian_separation`. Separation for arbitrary baseline
  laws lies outside that statement. For instance, a point mass is fixed
  by any normalized density.
- **Proved in prose.** The tilted Gaussian here is non-Gaussian. Its
  strictly positive density agrees with the standard Gaussian density
  on $(1,\infty)$ where $w=0$. If it were a nondegenerate Gaussian, the
  equality of the continuous densities on that interval would make
  their log ratio, a quadratic polynomial, identically zero. This would
  give the standard Gaussian everywhere, contradicting the strict
  expectation gap. A degenerate Gaussian is a point mass, whereas the
  tilted law has a Lebesgue density.
- **Kernel-checked.** `fixedOrderWitness_holds` settles the fixed-order
  extension asked in §§1 and 6. Each fixed $r$ may use its own $Q$ and
  limiting law. The result concerns existence on the specified balanced
  populations. It leaves open the restrictions that would guarantee a
  common limit, including growing matching orders, and gives no
  classification of attainable limits.
- **Open.** The linked supporting audits give the exact remaining
  realization, readout, intervention and observational-dependence gaps.
  [Supporting escape audits](https://github.com/the-omega-institute/trureturing/issues/32021#issuecomment-7029401222)

## ASSUMED-UNVERIFIED

The literature screen recorded in #32021 found no later settlement within
its stated search scope. Completeness beyond those sources remains
unverified. The supporting registration gaps above remain open.
