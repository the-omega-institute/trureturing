---
bibkey: stokes2020naturalgradient
authors: James Stokes, Josh Izaac, Nathan Killoran and Giuseppe Carleo
year: 2020
title: Quantum Natural Gradient
doi: 10.22331/q-2020-05-25-269
url: https://quantum-journal.org/papers/q-2020-05-25-269/
claim: The real quantum geometric tensor gives the Fubini–Study metric on a pure-state variational model and defines a quantum natural-gradient update; the paper supplies a block-diagonal approximation scheme.
strata_touched: []
license: citation-only
triage: anchor
---

# Quantum Natural Gradient

## Primary source and scope

Quantum 4, 269 (2020); author preprint https://arxiv.org/abs/1909.02108.
Section 2.1 defines the quantum geometric tensor and its real metric part;
Section 2.2 discusses natural-gradient optimization and parameter redundancy.
The published page supplies the authors, title and DOI. The author PDF supplies the metric construction.
No global convergence, SAT algorithm, or identification of unobserved correlations is attributed to this source.

## Scale and the appended-gate tangent test

For a normalized pure state and horizontal vectors, the conventional metric is
$g_{\rm FS}(v,w)=\operatorname{Re}\langle v,w\rangle$.
The project's Symplectic Predictive Completion uses $g=2g_{\rm FS}$.
For an appended gate $e^{-i\alpha G}$ with finite-dimensional Hermitian $G$, the horizontal derivative at zero is

$$
v_G=-i(G-\langle G\rangle)\psi,\qquad
g(v_G,v_G)=2\operatorname{Var}_\psi(G).
$$

This follows by removing the component $-i\langle G\rangle\psi$ of the derivative $-iG\psi$.
It is the standard one-parameter specialization of the quantum geometric tensor, not a new general theorem.
For an old differentiable parameterization, compare $v_G$ with the **real** image of its projective differential.
The new differential rank increases by one exactly when $v_G$ is outside that image.
At regular immersed points this is a tangent-space statement; at singular points it is only the rank of the differential at that point.
Nonzero variance alone does not imply an independent direction, global expressivity gain or task improvement.

For an expectation-based loss with effective Hermitian derivative $K$,
$dL(v)=2\operatorname{Re}\langle v,K\psi\rangle$.
Under the project's scale the full-state negative gradient is $-(K-\langle K\rangle)\psi$;
under $g_{\rm FS}$ it is twice this vector. Pulling back to a restricted or redundant circuit model requires projection or a specified pseudoinverse rule.

## Project application

[Symplectic Predictive Completion §37](../../docs/develop/theory/SYMPLECTIC_PREDICTIVE_COMPLETION.md)
applies this geometry to the five-mode odds ratio and complex four-corner relation.
Its joint-phase direction has ambient length $2\kappa(1-\kappa)$ and quotient length $2/I$.
Those code-specific calculations and the chosen loss invariants are derived there, not claimed as results stated in this paper.
Metric estimation, state preparation and optimization arithmetic remain separate costs.
