---
slug: tolias-dornheim-vorberger-2025-kinetic-odd-moments
bibkey: tolias2025kineticmoments
doi: 10.1002/ctpp.70090
url: https://arxiv.org/abs/2508.17810v1
triage: theorem
motivation_gids:
  - D5/S3/Quantum/KineticMoments/OddMoment.result
---

# All odd kinetic frequency moments

## Problem

P. Tolias, T. Dornheim and J. Vorberger, *Kinetic contribution to the arbitrary
order odd frequency moments of the dynamic structure factor*, arXiv:2508.17810v1,
Sec. 2.3, Eq. (16), state: “Therefore, our conjecture states that the following
result holds for the interacting uniform electron gas”, followed by

$$
M_{\mathrm{S,KIN}}^{(2k+1)}(q)=
\left(\frac{\hbar q^2}{2m}\right)^{2k+1}\frac{1}{2k+2}
\sum_{i=0}^{k}\binom{2k+2}{2i+1}
\left(\frac{2}{\hbar q}\right)^{2i}\langle p^{2i}\rangle_0,
$$

“where $k$ is an arbitrary non-negative integer.” The paper explicitly checks
$k=0,1,2,3$. Its summary also asks whether similar expressions hold for other
spin statistics. [Issue #13703](https://github.com/the-omega-institute/trureturing/issues/13703)
fixes the operator representation and averaging conventions. The quotations and
locators are in the [literature note](../Library/QuantumStates/tolias2025kineticmoments.md).

## Motivation

The formula expresses the kinetic contribution to every odd dynamic structure
factor moment through finitely many per-particle radial momentum moments.
`D5/S3/Quantum/KineticMoments/OddMoment.result` establishes it for every order
and every split of the commutator nests under the stated momentum-measure
hypotheses.

## Gap

The preregistration records the arXiv version, citing-work, MathDB and repository
searches. No all-order settlement was found in that searched scope. The published
full text and the special-issue editorial are outside the verified literature
scope. A bounded search does not establish exhaustive novelty.

## Route

A configuration is $P:\mathrm{Fin}(N)\to\mathbb R^3$. States are all
complex-valued functions of $P$. The density operators are sums of pullbacks by
$P_j\mapsto P_j\pm\hbar\boldsymbol q$, and the kinetic operator multiplies
by $\sum_j\|P_j\|^2/(2m)$. This is the kinetic prescription $\hat H\equiv\hat K$
of Sec. 2.2 and Eq. (9).

Put $a=\hbar^2\|\boldsymbol q\|^2/(2m)$ and
$b_j=(\hbar/m)\langle\boldsymbol q,P_j\rangle$. For
$n=2k+1$ and $0\le\ell\le n$, the split nested commutator is multiplication by

$$
F_{k,\ell}(P)=(-1)^\ell\sum_j
\bigl((b_j+a)^{2k+1}-(b_j-a)^{2k+1}\bigr).
$$

Different-particle terms commute; same-particle opposite translations cancel.
For an isotropic measure, the integrated directional moment satisfies

$$
\int\langle\boldsymbol q,P_j\rangle^{2i}\,d\nu
=\frac{\|\boldsymbol q\|^{2i}}{2i+1}
\int\|P_j\|^{2i}\,d\nu.
$$

The proof derives this factor by comparing coefficients of integrated moment
polynomials and solving a weighted recurrence. Radial integrability controls
all directional integrals. The odd binomial expansion, the identity
$\binom{2k+1}{2i}/(2i+1)=\binom{2k+2}{2i+1}/(2k+2)$ and the complex sum-rule
prefactor yield Eq. (16).

## Falsifier

The statement requires $N\ge1$, $\hbar>0$, $m>0$,
$\boldsymbol q\ne0$, a simultaneous-$\mathrm{SO}(3)$-invariant probability
measure and finite $2k$-th radial moments for each particle. Its algebraic
operator carrier is the space of all configuration functions. A physical model
with different operator or averaging conventions requires a separate bridge.
Without isotropy the radial reduction is not asserted; without finite required
moments the integral conclusion is not asserted.

## Evidence

The canonical sources are `D5/S3/Quantum/KineticMoments/IsotropicAverage.lean`
and `D5/S3/Quantum/KineticMoments/OddMoment.lean`, with their Blueprint mirrors.
`OddMoment.claim` includes both the exact operator identity and its normalized
integral formula. `OddMoment.result` proves this complete conjunction.
`IsotropicAverage.isotropic_average` proves the directional-to-radial identity
for any isotropic measure with the specified integrable moment, without requiring
a probability measure. The operator calculation uses the frozen
`ObserverCommutator.observer_read_update_commutator_formula` and pinned Mathlib.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

## Triage

Tier 1 external conjecture, preregistered in #13703. Resolution: proved in the
recorded momentum-space model. `OddMoment.result` has `proof_shape: content`
and `admission_basis: open-problem-resolution`. `IsotropicAverage` has
`admission_basis: escape-witness`, through `isotropic_average` and the private
`weighted_recurrence`. `integrable_directional` is a consumed bind-only helper;
the private operator-identity helpers are consumed by the settling proof.
Utility is `none`: the delivery consists of universal operator and integral
identities, with no finite certificate, enumeration or numerical reduction.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved — every order and split.** `OddMoment.result` establishes Eq. (16)
  for every $k\in\mathbb N$ and every $\ell\le2k+1$, including the Eq. (17)
  commutator form with its prescribed prefactor. The decisive mechanisms are
  translation cancellation and the isotropic weighted recurrence.
- **Proved — other spin statistics, conditionally.** `OddMoment.result` has no
  statistics, particle-independence, exchangeability or interaction hypothesis.
  It applies to any statistics whose operators and momentum distribution obey
  the fixed conventions and isotropic finite-moment assumptions. **Open:**
  construction of such physical equilibrium states, their thermodynamic limit
  and moment finiteness for a specified interaction or statistics.
- **Open — dimension-$d$ analogue.** The proposed angular factor
  $\Gamma(d/2)\Gamma(i+1/2)/(\sqrt\pi\,\Gamma(i+d/2))$ is not proved here.
  The delivered theorem is for dimension three.
- **Proved — direction-resolved algebra without isotropy.** The private
  `OddMoment.multiplier_expansion`, used by `multiplier_integral`, gives
  $$F_{k,\ell}(P)=(-1)^\ell 2\sum_{i=0}^k
  \binom{2k+1}{2i}a^{2k+1-2i}(\hbar/m)^{2i}
  \sum_j\langle\boldsymbol q,P_j\rangle^{2i}.$$
  It requires no isotropy. **Open:** a separately stated normalized anisotropic
  integral theorem; none is exported by this delivery.
- **Proved — consequences for the source.** Within the fixed model, Eq. (16)
  and Eq. (17) hold beyond the four explicitly evaluated orders. The identity
  uses the actual per-particle momentum distribution and requires no replacement
  by a Fermi distribution. **Open:** kinetic dominance of the full interacting
  moment, convergence of an infinite even-frequency series and the validity of
  numerical or QMC approximations that use these moments; the identity supplies
  no estimates for those questions.

## ASSUMED-UNVERIFIED

The literature scope does not establish worldwide priority or the absence of
an independent proof. The published full text and the special-issue editorial
were not verified. Physical equilibrium-state existence, isotropy and finite
moments for a particular interacting gas remain premises, not conclusions.
