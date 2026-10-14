---
bibkey: myhill2023granularsteadystates
authors: Alex D. C. Myhill, Raphael Blumenfeld
year: 2023
title: "Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance"
doi: 10.1088/1751-8121/ace56d
url: https://arxiv.org/abs/2306.10526v2
claim: "For the cell-order dynamics of two-dimensional granular systems (Eq. (1)), with fluxes η_{i,j} = p_{i,j}Q_iQ_j − q_{i,j}Q_{i+j−2} and steady-state equations Eq. (2), the authors prove that a detailed-balance steady state is unique when it exists, and that for C = 6, 7 no other steady state exists when one does. From numerical solution of 614400 systems up to C = 8 they conjecture that for any choice of constant rates there is only one physical (real and positive) steady state regardless of the highest cell order C."
strata_touched:
  - D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation
license: citation-only
triage: anchor
---

# Myhill–Blumenfeld, steady states of two-dimensional granular systems

A. D. C. Myhill and R. Blumenfeld, *Steady states of two-dimensional granular systems are unique, stable, and sometimes satisfy detailed balance*, J. Phys. A: Math. Theor. **56**, 345001 (2023), DOI 10.1088/1751-8121/ace56d; arXiv:2306.10526 [cond-mat.soft] (v2, the latest of versions v1–v2).

## Verified locator

DOI: 10.1088/1751-8121/ace56d (as listed on the arXiv abstract page).
Primary version read: https://arxiv.org/abs/2306.10526v2.
Source: https://arxiv.org/pdf/2306.10526v2 (text read from the PDF):
- §1, Eq. (1), the evolution equations for the cell-order fractions Q_k, 3 ≤ k ≤ C;
- §I.A, the net flux η_{i,j} and the steady-state equations, Eqs. (2)–(3);
- §I.B–C, the uniqueness of the detailed-balance state and the cases C = 6, 7;
- §I.D, the numerical investigation and the conjecture;
- §III, the restated conjecture.

## Source statements

§I.A: "Their net flux is ηi,j = pi,jQiQj − qi,jQi+j−2 and ηi,j = 0 when they are balanced. At steady state, the sum of all the processes, Σ_{i,j} η̄i,j, vanishes by definition and eqs. (1) reduce to 0 = ½ Σ_{i=3}^{k−1} η̄_{i,k−i+2}(1 + δ_{i,k−i+2}) − Σ_{i=k+1}^{C} η̄_{k,i−k+2}(1 + δ_{i,2k−2})."

§I.D: "Based on these investigations, we conjecture that, for any choice of constant rates, there is only one physical solution regardless of the upper order, C."

§III: "Intriguingly, by solving the steady state equations numerically for 614400 systems up to C = 8, we found that there is always only one physical solution, in which Qk is real and positive for all k. We conjecture that the evolution equations (1) yield only one physical solution for the steady state, which may or may not satisfy detailed balance."

## Reading used by the repository

The cell fractions are Q_3, …, Q_C, and the processes are the pairs 3 ≤ i ≤ j with i + j − 2 ≤ C. A physical state has every Q_k > 0 and Σ_k Q_k = 1. A steady state makes every right-hand side of Eq. (1) vanish.

The right-hand side is read with the flux of §I.A: the gain sum, minus the loss sum, plus Q_k Σ η, with the δ-factors of Eq. (2). The printed loss term of Eq. (1), (p_{k,j}Q_kQ_{i−k+2} − q_{k,i−k+2}Q_{i−k+2}), is read as η_{k,i−k+2}, whose splitting term removes the product cell of order i.
