---
bibkey: dinov2026kime
authors: Ivo D. Dinov
year: 2026
title: "Kime-Representation Formulations of Three Open Problems in the Foundations of Classical Mechanics: Uncertainty, Invariant Entropy, and Directional Degrees of Freedom"
doi: 10.48550/arxiv.2607.07851
url: https://arxiv.org/abs/2607.07851v1
claim: "Conjecture 3.22(ii) asserts that the phase-equipartitioned product state minimizes every within-DOF uncertainty at a fixed action marginal and entropy lower bound."
strata_touched:
  - D5/S3/Quantum/Information/DinovOriginalMinimumRefutation
license: citation-only
triage: anchor
---

# Equipartition duality and the within-DOF minimum assertion

The source is arXiv:2607.07851v1, Conjecture 3.22 (Equipartition duality):

> Fix $n\geq2$, an entropy value $s$, and an action marginal $\rho_{\mathbf J}$ on $(0,\infty)^n$. Among all states on $\mathbb T^n\times(0,\infty)^n$ with entropy $\geq s$ and action marginal $\rho_{\mathbf J}$, the phase-equipartitioned product state (unique when it exists) simultaneously (i) maximizes the entropy, (ii) minimizes every within-DOF uncertainty $u_j$, and (iii) is the unique state at which the per-DOF conjectured bound of Problem 3.17(b) is saturated for all $j$; moreover it is the unique fixed point, with the given marginal, of the multi-DOF kime-deformed semigroup $\partial_t\tilde\rho=\sum_j(-\omega_j\partial_{\theta_j}+\varepsilon\partial^2_{\theta_j})\tilde\rho$.

Definition 2.4 uses probability densities. Lemma 2.3 gives the source map
$q=\sqrt{2J}\sin\theta$, $p=\sqrt{2J}\cos\theta$, with angular measure
of mass $2\pi$ and Lebesgue measure on positive actions. The uncertainty in
Theorem 3.16 is the square root of the determinant of the actual two by two
coordinate covariance block. The comparison uses an entropy lower bound,
not entropy equality, and imposes no fixed symplectic orbit.

The repository refutation uses $n=2$, $s=0$ and
$r(J_1,J_2)=e^{-(J_1+J_2)}$. The independent nonuniform phases have density
$(1+\tfrac12\cos2\theta)/(2\pi)$; their uniform-phase comparator has the
same normalized joint action law. Their actual Cartesian covariances are
$\operatorname{diag}(3/4,5/4,3/4,5/4)$ and $I_4$, respectively. Both
within-DOF uncertainties are $\sqrt{15/16}<1$ in the nonuniform state.
Both states have finite nonnegative entropy, L2 coordinates and positive
definite full covariance. Source pushforwards, angular fibers and entropy
transport are proved inside the single result.

The original all-$n$ assertion implies clause (ii), and clause (ii) implies
the certified $n=2$ predicate. The formal result negates this necessary
predicate; it does not formulate a generic-$n$ transport theorem or separately
settle entropy maximization, saturation uniqueness or the semigroup claims.
The Cartesian density at zero action is a Borel zero extension on null planes.
The dynamical smoothness and decay hypotheses of neighboring Theorem 3.21
are not added to the static conjecture.

## Literature boundary

The accepted independent source reviews report the following bounded readings:
arXiv history contains only v1; the kime/equipartition topic query has one
result, this paper; OpenAlex work W7167927072 has zero indexed citations;
MathDB target 375895 has no posted solution and an unrefreshed progress panel.
Semantic Scholar returned HTTP 429. No proof or refutation was found in the
successfully checked scopes. This does not establish exhaustive literature
absence or worldwide priority. The readings and Tier 1 classification are
attached to preregistration [#13139](https://github.com/the-omega-institute/trureturing/issues/13139).

## Verified locator

- DOI: https://doi.org/10.48550/arxiv.2607.07851
- URL: https://arxiv.org/abs/2607.07851v1
- Original HTML: https://arxiv.org/html/2607.07851v1#S3.Thmtheorem22

The source HTML has SHA-256
`485c13cf847cd636050a971a324b4c2943dcbdfd76a913c7706ce5ff35817095`.
Only citation and the necessary source assertion are retained; the source's
CC BY-NC-SA 4.0 license is not assigned to the repository's original proof.
