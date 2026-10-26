---
bibkey: bauschcrosson2018modifiedcircuits
authors: Johannes Bausch; Elizabeth Crosson
year: 2018
title: Analysis and limitations of modified circuit-to-Hamiltonian constructions
doi: null
url: https://arxiv.org/abs/1609.08571
claim: Controlled removal of the circuit gates makes the modified propagation Hamiltonian unitarily equivalent to a clock Hamiltonian tensored with the register identity.
strata_touched: []
license: citation-only
triage: anchor
---

# Propagation constraints do not determine a physical clock scale

## Source locator

The author version of *Analysis and limitations of modified
circuit-to-Hamiltonian constructions*, Lemma 2 (PDF p. 5), supplies the
controlled gate-removal equivalence
$\mathcal W^\dagger H_{\rm prop}\mathcal W=H_{\rm clock}\otimes I$.
Its proof is on PDF p. 10. The source considers a broad class of weighted
clocks; the positive scalar weights below multiply fixed constraint
terms and do not change the constraints themselves.

## Positive weights on fixed constraints

For finite-dimensional Hilbert spaces and fixed linear maps $A_j$, let

$$
H_\lambda=\sum_{j=0}^{N-1}\lambda_jA_j^\dagger A_j,
\qquad\lambda_j>0.
$$

For every $v$,
$\langle v,H_\lambda v\rangle=\sum_j\lambda_j\|A_jv\|^2$.
Consequently

$$
\ker H_\lambda=\bigcap_j\ker A_j.
$$

Indeed, membership in the kernel makes the nonnegative quadratic form
zero, so each $A_jv=0$; the reverse implication follows by substitution.
This is the standard positive-sum kernel argument, used as supporting
linear algebra, not a new theorem of the project. Strictly positive
weights are essential to this argument for retaining every constraint;
a zero weight may remove a constraint.

For fixed gates and
$A_j=\langle j+1|\otimes I-\langle j|\otimes U_{j+1}$, the resulting
history space is therefore unchanged by these weights. With
$\mathcal W=\sum_j|j\rangle\langle j|\otimes W_j$,
$W_j=U_j\cdots U_1$, direct conjugation gives
$\mathcal W^\dagger H_\lambda\mathcal W=L_\lambda\otimes I$,
where $L_\lambda$ is the path Laplacian with edge weights $\lambda_j$.
The project-specific finite instrument correspondence is already in
[Collective oscillators, Definition 10.1 and Theorem 10.2](../../docs/develop/theory/AURIC_COLLECTIVE_OSCILLATORS_AND_RECORD_CAPACITY.md#10-含记录与程序的静态-auric-条件历史).

For every $c>0$, $H_{c\lambda}=cH_\lambda$ has the same kernel, whereas
its specified physical evolution obeys

$$
e^{-itH_{c\lambda}/\hbar}=e^{-i(ct)H_\lambda/\hbar}.
$$

Thus a constraint kernel does not specify the energy scale. A vector
in that kernel is stationary under this propagation Hamiltonian and
does not automatically execute the encoded sequence. Actual gate
control, state preparation, repeated clock measurement and physical
calibration remain separate implementation assumptions.
