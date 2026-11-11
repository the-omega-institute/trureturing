---
bibkey: krishna2026quaternionicdeutsch
authors: K. Mahesh Krishna
year: 2026
title: "Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic Uncertainty Principle"
doi: 10.48550/arXiv.2610.35881
url: https://arxiv.org/abs/2610.35881v1
claim: "Question 2.12 asks for which pairs of 1-bounded continuous Parseval frames equality holds in the quaternionic Deutsch uncertainty chain."
strata_touched:
  - D5/S3/QuantumBounds/QuaternionicDeutschEquality
license: citation-only
triage: anchor
---

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2610.35881

Source: https://arxiv.org/abs/2610.35881v1

# Krishna, Quaternionic Deutsch equality question

K. Mahesh Krishna, *Quaternionic Buzano-Dragomir Inequality and Deutsch Entropic
Uncertainty Principle*, arXiv:2610.35881v1. The source's Question 2.12, printed page 12, asks:

> Let $(\Omega, \mu)$, $(\Delta, \nu)$ be measure spaces, $\mathcal{Q}$ be a
> quaternionic Hilbert space. For which pairs of 1-bounded continuous Parseval
> frames $\{\tau_\alpha\}_{\alpha\in\Omega}$ and
> $\{\omega_\beta\}_{\beta\in\Delta}$ for $\mathcal{Q}$, we have equality in
> Inequality (11)?

The source defines continuous Parseval frames by measurability of each
coefficient map and the Parseval integral identity, restricts to frame vectors
of norm at most one, and defines the continuous Shannon entropy on the domain
where every coefficient is nonzero. The formal settlement classifies equality
at the lower Deutsch endpoint on that unchanged domain: equality forces
quaternionic dimension one and unit frame norms almost everywhere, and the
pair-level existence statement additionally requires every frame vector to be
nonzero, including null indices. The same argument gives simultaneous equality
throughout the chain and an explicit singleton Dirac model.

## Definitions from the source

Definition 1.9, printed pages 4–5:

> A right quaternionic vector space 𝒬 over ℍ is said to be a (right) quaternionic Hilbert space if there exists a map (called as quaternionic inner product) ⟨·, ·⟩: 𝒬 × 𝒬 → ℍ such that the following hold.

The five conditions are positivity and definiteness, additivity in the first
argument, right linearity, conjugate symmetry, and completeness for the norm
induced by the inner product. The Lean record separates the real-self,
nonnegativity and norm identities, with `CompleteSpace` stated separately.

Section 2, printed page 5, fixes right division:

> by x/r, we mean x r⁻¹.

Definition 2.7, printed page 10:

> Let (Ω, μ) be a measure space. A collection {τα}α∈Ω in a quaternionic Hilbert space 𝒬 is said to be a continuous Parseval frame for 𝒬 if the following conditions hold.

> For each x ∈ 𝒬, the map Ω ∋ α ↦ ⟨τα, x⟩ ∈ ℍ is measurable.

Its second condition is $\|x\|^2=\int_\Omega|\langle\tau_\alpha,x\rangle|^2\,d\mu(\alpha)$ for every $x\in\mathcal Q$.

Definition 2.8, printed page 10:

> A continuous Parseval frame {τα}α∈Ω for 𝒬 is said to be 1-bounded if

$$\|\tau_\alpha\|\leq1,\qquad\forall\alpha\in\Omega.$$

The entropy definition on printed page 10 states:

> Given a continuous 1-bounded Parseval frame {τα}α∈Ω for 𝒬, we define the continuous Shannon entropy at a point x ∈ 𝒬τ as

$$S_\tau(x)\coloneqq-\int_\Omega\left|\left\langle\tau_\alpha,\frac{x}{\|x\|}\right\rangle\right|^2\log\left|\left\langle\tau_\alpha,\frac{x}{\|x\|}\right\rangle\right|^2\,d\mu(\alpha)\geq0,$$

where $\mathcal Q_\tau\coloneqq\{x\in\mathcal Q:\langle\tau_\alpha,x\rangle\ne0,\ \forall\alpha\in\Omega\}$.
