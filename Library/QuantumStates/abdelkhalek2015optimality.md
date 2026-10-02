---
bibkey: abdelkhalek2015optimality
authors: Kais Abdelkhalek; René Schwonnek; Hans Maassen; Fabian Furrer; Jörg Duhme; Philippe Raynal; Berthold-Georg Englert; Reinhard F. Werner
year: 2015
title: "Optimality of entropic uncertainty relations"
doi: 10.1142/S0219749915500458
url: https://arxiv.org/abs/1509.00398v1
claim: "Conjecture V.8 (Independence of the optimal states of (α,β)): If ρ is an optimal state for any unitary operator and any α,β>½ satisfying the duality relation (2), then ρ is also an optimal state for all other dual pairs."
strata_touched:
  - D5/S3/Quantum/Information/RenyiOptimalStateDependenceRefutation
license: citation-only
triage: anchor
---

# Optimality of entropic uncertainty relations

K. Abdelkhalek, R. Schwonnek, H. Maassen, F. Furrer, J. Duhme, P. Raynal,
B.-G. Englert and R. F. Werner, arXiv:1509.00398v1; International Journal
of Quantum Information 13, 1550045 (2015). Subject: quant-ph.

The observables are two orthonormal bases in a finite-dimensional complex
Hilbert space. Their overlap matrix is $U_{ij}=\langle x_i|y_j\rangle$;
$p_X^\rho(i)=\langle x_i|\rho|x_i\rangle$ and
$p_Y^\rho(j)=\langle y_j|\rho|y_j\rangle$. Section II, p. 4, equation (6)
defines the finite-order Rényi entropy by
$H_\alpha(p)=\log(\sum_j p(j)^\alpha)/(1-\alpha)$ for $\alpha\ne1$, and
$H_1(p)=-\sum_jp(j)\log p(j)$ at order one. Its zero-probability terms
have their continuous values. The paper states:

> The logarithms can be taken in any base (as long as it is always the same base).

With $f(\rho)=(H_\alpha(p_X^\rho),H_\beta(p_Y^\rho))$, section II, p. 4,
defines the order and optimality:

> For any choice we can define the order relation $\sqsubseteq$ on the state
> space, so that $\rho\sqsubseteq\rho'$ stands for “$f_1(\rho)\leq f_1(\rho')$
> and $f_2(\rho)\leq f_2(\rho')$”.

> We call a state $\rho$ optimal if $\rho'\sqsubseteq\rho$ implies
> $\rho\sqsubseteq\rho'$, and hence $f(\rho)=f(\rho')$.

Conjecture V.8, section V.E, p. 21, reads:

> (Independence of the optimal states of $(\alpha,\beta)$)
> If $\rho$ is an optimal state for any unitary operator and any
> $\alpha,\beta>\frac12$ satisfying the duality relation (2), then $\rho$ is
> also an optimal state for all other dual pairs.

Equation (2) is $1/\alpha+1/\beta=2$. The finite-real-order encoding
excludes the extremal pair $\{1/2,\infty\}$, which the conjecture also
explicitly excludes. Using natural logarithms multiplies each entropy
coordinate by the same positive constant relative to the paper's base two;
the coordinate preorder and optimality are preserved. The Lean carrier
includes every positive complex trace-one density matrix, and zero-based
indices relabel the paper's basis outcomes.

## Verified locator

- URL: https://arxiv.org/abs/1509.00398v1 — source `OptEUR-main.tex`,
  section II (`eq:defentropy`, `deff`) and section V.E (`conj:independence`);
  PDF pp. 4 and 21, equations (6), (7) and Conjecture V.8.
- DOI: https://doi.org/10.1142/S0219749915500458 — journal citation.
  ASSUMED-UNVERIFIED: the journal full text and its fidelity to the arXiv
  conjecture have not been checked.

## Scope

The corresponding module refutes the universal conjecture with a qutrit
basis projector optimal at $(1,1)$ and not optimal at $(3/5,3)$. The
basis projectors reuse `OrthogonalRecordEntropy.pointerState` on `Fin 3`.
Corollary IV.4 concerns equality states saturating the Maassen–Uffink
bound; that is a distinct, narrower statement. No refutation of that
corollary, the Fourier-specific conjectures, or a two-dimensional
restriction is asserted here. Literature priority beyond the searched
scope, including the other citing works, is ASSUMED-UNVERIFIED.
