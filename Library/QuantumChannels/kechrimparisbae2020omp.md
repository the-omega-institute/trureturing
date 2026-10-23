---
bibkey: kechrimparisbae2020omp
authors: Spiros Kechrimparis; Joonwoo Bae
year: 2020
title: Optimal measurement preserving qubit channels
doi: 10.1088/1367-2630/abcc9b
url: https://arxiv.org/abs/2006.16366
claim: "The authors ask whether isolated qubit ensembles exist and expect that none exist; OMP means that a POVM is optimal both before and after applying the channel."
strata_touched:
  - D5/S3/Quantum/Measurement/IsolatedQubitEnsemble
license: citation-only
triage: anchor
---

# Kechrimparis and Bae, optimal measurement preserving qubit channels

## Verified locator

DOI: 10.1088/1367-2630/abcc9b

Source: https://arxiv.org/abs/2006.16366

The journal article is *New Journal of Physics* **22**, 123024 (2020).
The arXiv source and the journal article are entitled *Optimal measurement preserving
qubit channels*. *Channel Coding of a Quantum Measurement* is a distinct JSAC article
by Kechrimparis, Kropf, Wudarski and Bae, DOI 10.1109/JSAC.2020.2969034.

## Source statements

Definition 1 (arXiv PDF, pp. 2–3):

> We call a channel $\mathcal N$ optimal measurement preserving (OMP) for an ensemble of states $S=\{q_x,\rho_x\}_{x=1}^{n}$, if an optimal measurement before and after a channel use is the same. In other words, a POVM $M=\{M_x\}_{x=1}^{n}$ that solves the state discrimination problem for the ensemble $S=\{q_x,\rho_x\}_{x=1}^{n}$, also solves it for $S^{(\mathcal N)}=\{q_x,\mathcal N[\rho_x]\}_{x=1}^{n}$.

Conclusions (arXiv PDF, p. 11):

> The first concerns the existence of ensembles whose OMP sets are all trivial. This would imply that such ensembles are isolated in that any CPTP map acting on them necessarily changes all optimal measurements. We demonstrated that two-state ensembles as well as ensembles of equal a priori probabilities are not isolated.

> We expect that no isolated ensembles exist but we have not managed to establish the result in general.

Minimum-error discrimination maximizes $\sum_x q_x\operatorname{tr}(\rho_xM_x)$
over positive operator-valued measures. The encoding uses `Fin n`, positive real
priors summing to one, positive semidefinite complex two-by-two states of trace one,
and complex-linear completely positive trace-preserving maps. A shared optimal POVM
is enough for OMP; all channels sharing one must be the identity for isolation.
An ensemble with a unique optimum makes this equivalent to preservation of that optimum.

## Scope of the refutation

The four-state example at $G=19$ has priors $(9,9,5,5)/28$. A positive dual-slack
certificate and completeness give a unique optimal POVM. First-order variations
restrict every channel preserving it to an affine Bloch form. Complete positivity
then forces that form to be the identity. The source's results for two states and
equal priors survive; this example has four states and unequal priors.

The general $G>18$ family is a separate reading, not a Lean theorem. Its experiment
entry is `docs/reports/kechrimparis-bae-2020-isolated-qubit-ensembles/check.py` in
`the-omega-institute/trureturing-experiments`, revision
`f38d88fdb3b3610abc71f4f281b1e696ca7e9b4b`, SHA-256
`a791ade275b5cd2b55c1e95200ce9b376f7982629c658d6ab0f04289aebd625a`.
Isolation in higher dimensions and the minimum number of states remain open here.
The full texts of Ko et al., JSAC (2025), and Suzuki, IEICE IT2022-13, remain
ASSUMED-UNVERIFIED because they were inaccessible to the literature search.
