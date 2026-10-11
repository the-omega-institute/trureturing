---
bibkey: johnston2010generalized
authors: Nathaniel Johnston and David W. Kribs
year: 2011
title: Generalized Multiplicative Domains and Quantum Error Correction
doi: 10.1090/S0002-9939-2010-10556-7
url: https://arxiv.org/abs/1004.5112v1
claim: A unital completely positive map has a multiplicative domain characterized by its two square equalities; its use for Schur channels retains the unital and trace-preserving hypotheses.
strata_touched: []
license: citation-only
triage: anchor
---

# Multiplicative-domain criterion consumed by calibrated five-label blocks

Primary text: [arXiv:1004.5112v1](https://arxiv.org/pdf/1004.5112v1),
section 3, equation (3), Theorem 3; the preprint is from 2010.
Published article: [Proceedings of the American Mathematical Society 139,
627–639 (2011)](https://doi.org/10.1090/S0002-9939-2010-10556-7).
The consumer is [Hidden Relations, C-29.5](../../docs/develop/theory/AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md#29-同一五模式的全输入保真方形记录与稳定子块).

For a unital completely positive map $\Phi$, the cited classical criterion is

$$
\mathrm{MD}(\Phi)=\{A:\Phi(A)^\dagger\Phi(A)=\Phi(A^\dagger A),\quad
\Phi(A)\Phi(A)^\dagger=\Phi(AA^\dagger)\}.
$$

On this algebra $\Phi$ respects multiplication and adjoints. The paper
recalls this criterion as Theorem 3; its generalized-domain theorems have
additional hypotheses. In particular, Theorems 5 and 7 require a unital
CPTP map. Theorem 11 instead treats correctable subsystems of a specified
code space using an actual representation. These statements are not an
unconditional convergence theorem for repeated channels.

For the consumer's correlation-matrix Schur map
$\Phi(A)=\Gamma\circ A$, complete positivity and unit diagonal imply
unitality and trace preservation. The two Schwarz defects are positive,
and each has trace

$$
\sum_{s,t}(1-|\Gamma_{st}|^2)|A_{st}|^2.
$$

Because a positive matrix of trace zero is zero, the cited criterion says
that the multiplicative domain consists exactly of entries with
$|\Gamma_{st}|=1$. Common unit records make that relation an equivalence
relation. In each such class the channel acts by a diagonal unitary; its
inverse is an actual correction only when the phase calibration and gate
are supplied. Raw fixed points instead require $\Gamma_{st}=1$ on each
nonzero matrix entry.

The five-label consumer applies this distinction to an actual square with
an $\{O,T\}$ block and three singleton classes. It derives the repeated
Schur formula and its phase-corrected limit from matrix-unit eigenvalues
and fresh independent environments. Those conclusions are not attributed
to this paper's general theorem. Positive class mass is required before
normalizing a conditional block, and class weights remain part of the state.
