---
bibkey: cha2026structural
authors: Hyunho Cha, Jungwoo Lee
year: 2026
title: "Structural perspectives from quantum states and measurements in optimal state discrimination"
doi: 10.1007/s11128-026-05335-6
url: https://arxiv.org/abs/2507.05778v2
claim: "For an ensemble of N states with optimal minimum-error POVM, I_+ is the set of labels whose optimal effect is nonzero, and P^PGM_+ is the pretty-good-measurement score restricted to I_+ with the original weights. For equal priors the paper conjectures (|I_+| - 1)(P^PGM_+ - 1/N) <= (N - 1)(P^PGM - 1/N), the equiprobable form of 'the restricted PGM bound is at most Renes's PGM bound'."
strata_touched:
  - D5/S3/Quantum/Measurement/EquiprobablePgmActiveSetRefutation
license: citation-only
triage: anchor
---

# Structural perspectives from quantum states and measurements in optimal state discrimination

Hyunho Cha and Jungwoo Lee, Quantum Information Processing 25, 310 (2026);
arXiv:2507.05778v2. Quotations are from the arXiv v2 source.

The optimal POVM (l. 232–243): maximize
$\sum_i \text{tr}(\tilde\sigma_i E_i)$ subject to $E_i \succeq 0$,
$\sum_i E_i = I$; $\hat E(\mathcal E)$ denotes the optimal POVM.

The active set and the restricted score (l. 429, 458–468):

> Let $\text{I}_+(\mathcal{E}) \equiv \{ i | \hat{E}_i (\mathcal{E}) \succ 0 \}$ denote the set of indices of positive definite (optimal) measurement operators for $\mathcal{E}$. […] $P_\mathcal{E}^{\text{PGM}+} = \sum_{i \in \text{I}_+(\mathcal{E})} \text{tr}(\Tilde{\sigma}_i E_i)$, where $S \equiv \sum_{i \in \text{I}_+(\mathcal{E})} \Tilde{\sigma}_i$ and $E_i \equiv S^{-1 / 2} \Tilde{\sigma}_i S^{-1 / 2}$ if $i \in \text{I}_+(\mathcal{E})$.

The journal version defines $I_+(\mathcal E)=\{i:\widehat E_i(\mathcal E)\ne0\}$,
"nonzero (optimal) measurement operators" (seat-reported, Section 4, p. 7),
and the arXiv example at l. 526 assigns $\text{I}_+=\{1,2\}$ to rank-one
effects; the encoding uses nonzero effects.

The conjecture (l. 636–640; journal Section 4.1.3, Eq. (18)):

> $(|\text{I}_+(\mathcal{E})| - 1) \left( P_\mathcal{E}^{\text{PGM}+} - \frac{1}{N} \right) \leq (N - 1) \left( P_\mathcal{E}^{\text{PGM}} - \frac{1}{N} \right).$ Numerical attempts have failed to identify any exceptions to Eq. (equiprobable_pgm_bound_inequality). Consequently, we conjecture that it holds universally for equiprobable states.

The encoding states it for positive definite states with equal priors and for
some optimal POVM.

## Verified locator

- DOI: https://doi.org/10.1007/s11128-026-05335-6 (Quantum Information
  Processing 25, 310 (2026); the conjecture is journal Eq. (18), Section
  4.1.3, p. 12, as reported by the literature seat).
- URL: https://arxiv.org/abs/2507.05778v2 (source `sn-article.tex`, md5
  `b9a14a8589877a76996275e1e5230bde`): the optimization (l. 232–243), the
  PGM (l. 254), the active set (l. 429), the restricted score (l. 458–468),
  the mirror-symmetric example (l. 526), the conjecture (l. 636–640).
