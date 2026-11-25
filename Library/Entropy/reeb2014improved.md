---
bibkey: reeb2014improved
authors: "David Reeb and Michael M. Wolf"
year: 2014
title: "An improved Landauer principle with finite-size corrections"
doi: 10.1088/1367-2630/16/10/103011
url: https://arxiv.org/abs/1306.4352v3
claim: "Finite-reservoir erasure uses engineered Gibbs states and swaps, with lower-eigenvalue and rank constraints."
strata_touched:
  - D5/S3/Quantum/Decoherence/GibbsBathBandwidth
  - D5/S3/Quantum/Decoherence/LabelResetBandwidth
  - D5/S3/Quantum/Decoherence/LabelResetSupport
  - D5/S3/Quantum/Decoherence/ProductRecordBandwidth
  - D5/S3/Quantum/Decoherence/FourLevelBathEntropyBudget
license: citation-only
triage: anchor
---

# Finite-reservoir erasure, spectrum and engineered Gibbs states

Example 1 and §3.3 give precedents for preparing a positive target with an engineered Gibbs state and a swap. Proposition 5 controls the lower eigenvalue. The exact bandwidth calculation uses both eigenvalue endpoints. Section 5.1 treats initially correlated memory and conditional-entropy heat bounds.

## Verified locator

§2.1, Example 1, p. 5. §3.3, Eqs. (29)–(30) and Proposition 5, Eq. (32), p. 11, with the rank and Gibbs construction on p. 12. §5.1, Eqs. (57)–(59), p. 18. Locators follow the v3 PDF. [DOI](https://doi.org/10.1088/1367-2630/16/10/103011) · [Source](https://arxiv.org/abs/1306.4352v3)

## Equality balance and the returning Gibbs bath

Theorem 3, arXiv v3 PDF p. 9, Eqs. (21)–(22), considers an initial product
of a finite system and a Gibbs reservoir followed by joint unitary
evolution. In the notation S and B for those factors, it gives

    β ΔQ = S(ρ) − S(ρ′_S) + I(S:B) + D(ρ′_B || τ_B),

where τ_B is the initial Gibbs density and ΔQ is the increase of mean
bath energy for its fixed Hamiltonian. The paper denotes its reservoir
by R.

In the four-level bath theorem the SB reduction is exactly this
product-initialized evolution with τ_B = diag(p). Its B marginal returns
to τ_B, so ΔQ and the reservoir relative entropy both vanish. This gives
I(S:B) = S(Δρ) − S(ρ) in the balance. The actual spectator reference in
the coherent Gibbs preparation is a separate factor. Its correlations
and the conditional mutual information are computed from the SBR
marginals.
[Equality form of Landauer’s principle, Theorem 3](https://arxiv.org/pdf/1306.4352v3#page=9)
