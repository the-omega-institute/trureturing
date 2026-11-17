---
bibkey: bunthpitriktitkosvirosztek2025wasserstein
authors: G. Bunth, J. Pitrik, T. Titkos, D. Virosztek
year: 2025
title: Wasserstein distances and divergences of order p by quantum channels
doi: 10.48550/arXiv.2501.08066
url: https://arxiv.org/abs/2501.08066v3
claim: "Finite-spectrum quantum transport cost cones and Conjecture 9, asserting their inclusion as the order increases."
strata_touched:
  - D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity
license: citation-only
triage: anchor
---
<!-- GID: D5/L/Convexity/bunthpitriktitkosvirosztek2025wasserstein -->
# Quantum transport cost cones and their order parameter

The cited version is arXiv:2501.08066v3, 27 April 2026; the first version
is dated 14 January 2025. The version, definitions and proposition locators
below are supplied in the problem statement. They have not been independently
checked against a downloaded manuscript.

Equation (21) defines $\operatorname{FCO}(\mathcal H)$ as the finite sets
of self-adjoint observables, allowing unbounded observables. Equation (22)
defines their order-$p$ transport costs by

$$
C_{\mathcal A,p}
 =\sum_k\iint |x-y|^p\,dE_k(x)\otimes dE_k^T(y)
 =\sum_k|A_k\otimes I^T-I\otimes A_k^T|^p.
$$

Equation (27) restricts every observable to have finite spectrum and denotes
the resulting set of cost operators by $\mathbf C_p(\mathcal H)$. These
definitions, and the paper's proved Propositions 4, 5, 10, 12 and 15 when
invoked, are literature results. In particular, Proposition 15 proves
$\mathbf C_p(\mathcal H)\subseteq\mathbf C_\infty(\mathcal H)$.

Conjecture 9, equation (48), states verbatim:

> For any separable Hilbert space ℋ, and for any parameter values
> 0<p≤p′≤∞ we have the relation 𝐂_p(ℋ) ⊆ 𝐂_{p′}(ℋ).

The finite-order proof uses phase-averaged sine functions. For
$0<p<q<\infty$, the positive finite constants

$$
J=\int_0^\infty |\sin u|^q u^{-1-p}\,du,
\qquad K=\int_0^{2\pi}|\cos\theta|^q\,d\theta
$$

give the representation

$$
\int_0^\infty\int_0^{2\pi}
 |\sin(tx+\theta)-\sin(ty+\theta)|^q\,d\theta\,
 t^{-1-p}\,dt
 =2^{q-p}KJ|x-y|^p.
$$

This type of integral metric representation is classical harmonic-analysis
and metric-embedding background: the real-line snowflake embeds in an $L_q$
representation, interpreted by its $q$-power integral also for $q<1$.
It is not claimed as a new representation theorem
of the cited quantum-transport paper or of this repository. Exact finite
distance decomposition and its spectral lift to cost-cone inclusion are
repository derivations, proved in the associated Lean module from existing
results. The terminal theorem treats arbitrary complex Hilbert spaces and finite real exponents;
it uses the finite spectral sum in an algebraic tensor product. Its
correspondence with the source's transpose and Hilbert-tensor presentation
is explained in the accompanying Scribe commentary.

## Locator

- URL: https://arxiv.org/abs/2501.08066v3
- DOI: 10.48550/arXiv.2501.08066
- Equations (21), (22), (27), (48); Conjecture 9.
- Propositions 4, 5, 10, 12, 13 and 15.

The bounded source information is the versioned quotation supplied with
preregistration issue [#30813](https://github.com/the-omega-institute/trureturing/issues/30813).
No new citation search or independent manuscript retrieval is claimed.
