---
slug: lopes-oliveira-2026-fixed-classical-target-wasserstein
bibkey: lopesoliveira2026transport
doi: null
url: https://arxiv.org/html/2611.13904v1#S8
triage: theorem
motivation_gids:
  - D5/S3/Entropy/LopesOliveiraWassersteinRefutation.result
---

# Lopes–Oliveira fixed-classical-target Wasserstein extension

## Problem

Artur O. Lopes and Elismar R. Oliveira, *Thermodynamic Formalism for
Non-Invariant Probabilities: Entropy, Divergence, Channels*, arXiv:2611.13904v1,
Section 8, ask for a similar expression relating their non-invariant pressure
and entropy to transport distance. Issue [#30524](https://github.com/the-omega-institute/trureturing/issues/30524)
preregistered the following fixed-classical-target extension of that question.

For every integer $d\ge2$, let
$\Omega_d=\{1,\ldots,d\}^{\{1,2,3,\ldots\}}$ with the positive-index shift
$\sigma(x)_i=x_{i+1}$ and metric

$$r(x,y)=\begin{cases}0&x=y,\\2^{-\min\{i\ge1:x_i\ne y_i\}}&x\ne y.\end{cases}$$

For a real Hölder potential $\phi$ on this original shift, let $\mu_\phi$ be
the specified unique invariant classical Kolmogorov–Sinai equilibrium for the
same potential. For every Borel probability $\rho$, define the unrestricted
non-invariant entropy by conditioning the first-coordinate indicators on the
entire future sigma-algebra $\sigma^{-1}(\mathcal F_d)$, and define

$$P_{ni}(\phi)=\sup_{\rho\text{ Borel probability}}
\left(\int\phi\,d\rho+h_{ni}(\rho)\right).$$

The registered event is the existence, for each $d$ and $\phi$, of a finite
real $c=c(d,\phi)$ such that every Borel probability $\nu$ satisfies

$$W_1(\nu,\mu_\phi)\le c\sqrt{P_{ni}(\phi)-h_{ni}(\nu)-\int\phi\,d\nu}.$$

The event keeps all original quantifiers and the actual all-coupling
Wasserstein infimum. It adds no integrability premise and restricts neither
$\nu$ nor its support or invariance.

## Motivation

The extension tests whether the authors' pressure/entropy deficit can control
distance from the same classical equilibrium for arbitrary non-invariant laws.
The fixed target matters: replacing it by an equilibrium of the non-invariant
pressure would be a different problem.

## Gap

The full registered extension is false. This settlement is scoped to that
fixed-classical-target extension only. It does not settle every interpretation
of the authors' broader “similar expression” question, nor does it classify
other pressure choices or target measures.

## Route

Use $d=2$ and the constant potential $\phi=-\log 2$. The fair Bernoulli law
`SourceEquilibrium.fair` is an actual invariant probability and is proved to be
the unique classical KS variational equilibrium for this same potential.

The comparison law has a fair first symbol and a deterministic entire future.
Its entire-future conditional first-symbol entropy is $\log 2$, so it attains
the unrestricted all-law pressure for the constant potential. Its potential
integral is $-\log 2$, hence the displayed deficit is exactly zero. The
first-difference metric and the actual coupling infimum give Wasserstein
distance at least $1/8$ from every invariant probability, including the fair
Bernoulli target. Therefore no finite real $c$ can satisfy the inequality; the
argument also excludes negative and zero values of $c$.

The formal source uses the positive-index shift, the half-scaled first-
difference metric, the entire future sigma-algebra, the unrestricted
conditional entropy and all-law pressure, and the actual Borel coupling
infimum. It does not use a finite-future model, a proxy target, an assumed
zero-deficit premise, or a new integrability hypothesis.

## Falsifier

Source fidelity would fail if the target were changed, the comparison laws
were restricted to invariant laws, the entire future were replaced by a finite
tail, or the coupling infimum were replaced by a proxy distance. A proof of
the universal inequality for this exact registered event would contradict the
formal `result`; a different “similar expression” requires a separate
statement and qualification.

## Evidence

The kernel-checked source is
`D5/S3/Entropy/LopesOliveiraWassersteinRefutation.lean`, whose designated
declaration `result` has literal type `Not claim`. It depends on the delivered
source-space and full-tail modules and the classical KS/Bernoulli suppliers.
The corresponding Blueprint Scribe attaches a `Refuted`
`OpenProblemResolutionClaim` to that result. The settlement is a
`deposit-uncovered` open-problem resolution: no corresponding theory volume or
digestion atom is used.

The source note is
`Library/Entropy/lopesoliveira2026transport.md`, which acknowledges Lopes and
Oliveira and the arXiv v1 Section 8 locator. The imported entropy supplier is
the Apache-2.0 port recorded in `Library/Entropy/morgenstern2026ks.md`,
including revision `040fec2e0ddf4fcba49af9f76c866d295308dd7f` and its license.

The escape audit for the selected D5 source declarations remains unfinished
under [issue #30545](https://github.com/the-omega-institute/trureturing/issues/30545);
no `declared_validated` registration is claimed. The bounded literature
qualification is not an exhaustive worldwide novelty or priority certificate.

## Triage

Tier 1 external open-problem resolution, `Refuted`. The admission basis is
`open-problem-resolution (#30524; Refuted)`, with `utility: none`. The public
settling result is a designated refutation and has no escape witness; consumed
bind-only helpers are retained only on live proof paths.

The original issue, event hash, threshold-0 observation, forecast comment,
and fixed deadline remain unchanged. This dossier records the result under the
original event and does not reset, rescore, or create a new open-problem unit.

### What the settlement shows

- **Refuted, kernel-checked:** the exact fixed-classical-target extension fails
  at $d=2$ and $\phi=-\log 2$.
- **Actual objects:** the comparison law, fair Bernoulli target, entire-future
  conditional entropy, all-law pressure, positive-index metric, and all-law
  Wasserstein infimum are the objects in the registered statement.
- **Boundary:** the authors' broader similar-expression question, other target
  choices, finite-tail variants, and repaired inequalities remain open here.

## ASSUMED-UNVERIFIED

The source and literature screen are bounded and do not certify exhaustive
worldwide absence, priority, or author acceptance. The unfinished registration
audit is disclosed above. These qualifications do not weaken the literal Lean
refutation of the registered fixed-classical-target event.
