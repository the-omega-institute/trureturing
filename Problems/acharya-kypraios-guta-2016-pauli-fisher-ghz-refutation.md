---
slug: acharya-kypraios-guta-2016-pauli-fisher-ghz-refutation
bibkey: acharyakypraiosguta2016lowranktomography
doi: 10.1088/1367-2630/18/4/043018
url: https://arxiv.org/abs/1510.03229v2
triage: theorem
motivation_gids:
  - D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.result
---

# GHZ phase tangents refute a rank-only lower bound for normalized Pauli Fisher information

## Problem

A. Acharya, T. Kypraios and M. Guţă, *Statistically efficient tomography of low rank states with incomplete measurements*, New J. Phys. 18 (2016), 043018; arXiv:1510.03229v2, Section 4, subsection “Pauli settings”, `Efficient-Ion-Tomography.tex`, line 360:

> While the full dependence of $\lambda_{min}$ on $r$ and $d$ is unclear, we conjecture that for any fixed rank, $\lambda_{min}$ is larger than a fixed constant for all states of rank $r$, of arbitrarily many ions.

Here $d=2^n$, $\bar I$ averages the Fisher information over all $3^n$ product Pauli settings, and $\lambda_{min}=\lambda_{min}(G^{-1/2}\bar I G^{-1/2})$, where $G$ is the Frobenius metric of the local rank-$r$ parametrisation. The measurement model, metric and Fisher matrix are in the same source, lines 114–121, 157–176 and 178–180; see also [the literature note](../Library/Estimation/acharyakypraiosguta2016lowranktomography.md).

Issue [#24270](https://github.com/the-omega-institute/trureturing/issues/24270) fixes the tangent reading. For complex matrices on $n$ qubits, let $u_{s,o}$ be the product Pauli eigenvector, $p_\rho(o\mid s)=\operatorname{Re}\langle u_{s,o}|\rho|u_{s,o}\rangle$, and $\bar I_\rho(v)=3^{-n}\sum_s\sum_o(\operatorname{Re}\langle u_{s,o}|v|u_{s,o}\rangle)^2/p_\rho(o\mid s)$, with zero-probability terms assigned zero.

`IsRankTangent r ρ v` means that there exists a curve $\gamma:\mathbb R\to M_{2^n}(\mathbb C)$ with $\gamma(0)=\rho$, derivative $v$ at zero, and $\gamma(t)$ a positive semidefinite trace-one matrix of rank $r$ for every real $t$. Differentiability is required only at zero.

`claim` asserts that for every natural rank $r\ge1$ there exists a real $c>0$ such that, for every $n\in\mathbb N$, every rank-$r$ density matrix $\rho$ and every `IsRankTangent r ρ v`, one has $c\operatorname{Re}\operatorname{Tr}(v^2)\le\bar I_\rho(v)$. The quantifier over $n$ includes zero. The module proves `result : ¬ claim`; its witnesses have rank one and $n>0$.

## Motivation

At fixed rank, the source proposes obtaining an $O(\log d)$ setting count from the conjectured lower bound (line 360). The bound would provide the missing spectral input for extending its concentration argument from uniformly random orthonormal bases to product Pauli settings. A family whose normalized directional Fisher information tends to zero tests the uniformity over all states and all numbers of ions directly.

## Gap

The bounded literature check recorded in #24270 found no settlement:

- The source's arXiv v2 retains the conjecture at line 360.
- Acharya and Guţă, *Statistical analysis of low rank tomography with compressive random measurements* (2016 preprint; arXiv:1609.03758), Conclusions, line 423 of `Statistical_analysis_of_low_rank_tomography_with_compressive_random_measurements_arXiv.tex`, state: “It remains an open problem if a similar scaling of the MSE exists in the Pauli measurement setup used in standard multiple ions tomography.” This is a related MSE question, rather than a settlement of the precise uniform eigenvalue conjecture.
- The orchestrator's searches by authors, title, Pauli Fisher minimum eigenvalue, conjecture and GHZ found the paper, repository copies, the follow-up and Acharya's 2018 Nottingham thesis. The thesis full text was restricted and was not read.
- The preregistration records no previous repository preregistration for arXiv:1510.03229 and no D5 computation of Pauli-setting Fisher information.

`not-found-in-searched-scope`.

## Route

For $n>0$ and real $\theta$, write $|\psi_{n,\theta}\rangle=(|0^n\rangle+e^{i\theta}|1^n\rangle)/\sqrt2$, $\rho_{n,\theta}=|\psi_{n,\theta}\rangle\langle\psi_{n,\theta}|$, and $v_{n,\theta}=(i/2)(e^{i\theta}|1^n\rangle\langle0^n|-e^{-i\theta}|0^n\rangle\langle1^n|)$.

1. **State and tangent.** For every $n>0$ and every real $\theta$, `ghz_density_rank` gives density and rank one, `ghz_derivative` gives the derivative of $t\mapsto\rho_{n,\theta+t}$ at zero, and `phase_norm` gives $\operatorname{Re}\operatorname{Tr}(v_{n,\theta}^2)=1/2$. Applying the density-and-rank statement at every $\theta+t$ supplies the globally fixed-rank curve required by `IsRankTangent`.
2. **Settings containing $Z$.** For $n>0$, any real $\theta$ and any setting $s$ with $s_j=Z$ at some site, `z_setting_zero` gives setting Fisher information zero. At that site each outcome vector has zero overlap with one of the two computational branches, so its directional readout vanishes.
3. **Settings using only $X/Y$.** For $n>0$, any setting with no $Z$, every outcome and every real $\theta$, `xy_prob_direction` gives $p=(1+\operatorname{Re}(e^{i\theta}q))/2^n$ and directional readout $-\operatorname{Im}(e^{i\theta}q)/2^n$, where $q=\prod_j(-1)^{o_j}(-i)^{\mathbf1_{s_j=Y}}$ and $o_j\in\{0,1\}$. At $\theta=\pi/4$, for $n>0$ and every such setting and outcome, `xy_prob_positive` gives strictly positive probability; `xy_setting_one` gives setting Fisher information one.
4. **Average and contradiction.** For every natural $n$, `xy_setting_count` counts $2^n$ settings with no $Z$. For $n>0$, `average_exact` therefore gives $\bar I_{\rho_{n,\pi/4}}(v_{n,\pi/4})=(2/3)^n$. For each real $c>0$, `small_ratio` supplies $n>0$ with $2(2/3)^n<c$. Specializing `claim` to rank one, this state and its tangent would give $c/2\le(2/3)^n$, a contradiction.

## Falsifier

The refutation would not answer the source conjecture if the formal measurement design, tangent class or metric did not represent its spectral bound. The correspondence is:

- `pauliEigen` uses $0,1,2$ for $X,Y,Z$ and outcomes $0,1$ for eigenvalues $+1,-1$; `productVector` takes their tensor product. `outcomeProb` is its real Born readout, and `averageFisher` is the uniform average over all Pauli settings.
- In a local rank-$r$ chart with nonsingular Frobenius metric $G$, a tangent $v=\sum_a w_a\partial_a\rho$ has $\operatorname{Tr}(v^2)=w^{\mathsf T}Gw$ and directional Fisher information $w^{\mathsf T}\bar Iw$, by the chain rule and the source's definitions. Substituting $G^{1/2}w$ in the Rayleigh quotient translates a positive lower bound for $G^{-1/2}\bar I G^{-1/2}$ into the tangent inequality. This coordinate-to-eigenvalue bridge is an argument, not a theorem of the module.
- The source's displayed Fisher formula does not specify zero-denominator terms. The preregistered reading and Lean real division assign them zero. For the witnesses with $n>0$ at $\theta=\pi/4$, every all-$X/Y$ outcome is strictly positive by `xy_prob_positive`. For any real $\theta$, a setting containing $Z$ kills one branch coordinate of each product vector; `ghz_expectation`, for $n>0$ and any vector and real phase, then makes its probability phase-independent. Thus a zero probability in that setting is identically zero along this phase curve. The refutation does not use a singular all-$X/Y$ outcome.

## Evidence

The canonical source is `D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.lean`.

- **Definitions.** It defines `pauliEigen`, `productVector`, `outcomeProb`, `settingFisher`, `averageFisher`, `IsRankTangent` and `claim`.
- **Proof.** It proves `result : ¬ claim`, using private GHZ state, derivative, norm and setting-information lemmas.
- **Reuse.** It reuses `IsDensity` from `SLDSpectralEnergy`, the Pauli eigenvectors from `WignerDistanceMinimum`, the product map and readout from `ProductPrefixRigidity`, and the rank-one density and rank lemmas from `PureStateHandshake` and `LiTheilHarrowChuangPurifyCloneRefutation`.
- **Axioms.** It uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, `native_decide`, or new axiom.
- **Escape registrations.** `result` is the designated refutation result of the `utility` header and is exempt. The module has no other public theorem.

Frozen state: `Golden/Frozen/state/D5/S3/Quantum/Tomography/PauliFisherGHZRefutation.lean.json`.

Declaration statements:

- `result`: `sha256:f8ce6310fac86eef4dea1418c895ec4055b96508a3f038a79bc1f4d22d99f557`;
- `claim`: `sha256:873b9090946682a76e9a97074308331d043c4130427bfe579a9482318bda9faa`.

## Triage

Tier 1 conjecture from a 2015 preprint of a 2016 paper, preregistered in issue #24270 before any Lean.
`theorem`; resolution `refuted`.

The module is admitted under the open-problem-resolution basis of CLAUDE.md §3.2. The refutation is a certified instance with basis `refutes`. There is no digestion atom.

### What the settlement shows

**Proved by `result`:** the assertion that every natural rank $r\ge1$ admits a real $c>0$ such that $c\operatorname{Re}\operatorname{Tr}(v^2)\le\bar I_\rho(v)$ for every $n\in\mathbb N$, every rank-$r$ density matrix $\rho$ and every `IsRankTangent r ρ v` is false.

**Computed, not formalized**. None.

**Argued, not formalized**.

- *Failure mechanism.* For $n>0$ at $\theta=\pi/4$, `z_setting_zero` for settings containing $Z$ and `xy_setting_one` for settings using only $X/Y$ identify the phase-sensitive settings; `xy_setting_count`, valid for every natural $n$, counts $2^n$ of them among $3^n$ settings, a fraction $(2/3)^n$. The rank stays one while this fraction tends to zero. Fixed rank alone therefore does not control how much measurement weight reaches a coherence-bearing tangent.
- *Randomly reduced designs.* For $n>0$ at $\theta=\pi/4$, the same two lemmas give directional information zero or one according to these setting classes. For $k$ independent uniform Pauli settings, the probability that all $k$ directional informations are zero is $(1-(2/3)^n)^k\ge1-k(2/3)^n$. If $k=O(n)=O(\log d)$, this tends to one, since $n(2/3)^n\to0$. Thus this sampling rule cannot give a high-probability positive directional lower bound uniformly over these states at that setting count.
- *Nearby statements.* For each fixed $n>0$ at $\theta=\pi/4$, `phase_norm` and `average_exact` give the positive directional ratio $2(2/3)^n$; an $n$-dependent lower bound is compatible with this family, but no all-state bound at fixed $n$ is established. For $n>0$ at the same phase, restricting a measurement design to settings using only $X/Y$ gives information one for this particular tangent, because `xy_setting_one` assigns one to every such setting. This says nothing about a lower bound for all tangents under that changed design. Bounds restricted to ranks $r\ge2$, or to a state class excluding the obstruction with adequate quantitative control, are not settled here.
- *Effect on the source.* The conditional $O(\log d)$ Pauli-setting conclusion at line 360 loses its conjectured uniform spectral premise. The random-design argument above concerns uniform sampling of product Pauli settings; it does not exclude other designs or settle the efficiency of arbitrary estimators. The source's concentration theorem at its equal-spectrum rank-$r$ state $\rho_0$ for uniformly random orthonormal bases (lines 306–316) and its weaker dimension-dependent Pauli bound $1/\lambda_{min}\le C'rd\log(2d)$ (lines 364–374) use different premises and receive no contradiction from this refutation. Its finite random-state simulations do not supply the uniformity over all states required by the conjecture.

## ASSUMED-UNVERIFIED

The bounded literature check in #24270 establishes only `not-found-in-searched-scope`, not exhaustive worldwide novelty or priority. The original conjecture and the quoted follow-up sentence were checked against their TeX sources. The orchestrator's broader web searches and prior repository search results were not independently reproduced. Acharya's restricted 2018 thesis was not read; whether it contains a settlement is unverified.

The coordinate-to-eigenvalue bridge in “Falsifier” and the consequences in “Argued, not formalized” have no separate Lean statements in this module. The source's random-basis theorem, weaker Pauli bound and estimator claims were read as source statements; their proofs and empirical claims were not independently verified. No result is asserted here for higher ranks alone, mixed GHZ families, or an all-state bound under an altered design.
