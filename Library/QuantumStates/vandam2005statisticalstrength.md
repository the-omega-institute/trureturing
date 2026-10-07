---
bibkey: vandam2005statisticalstrength
authors: W. van Dam; R. D. Gill; P. D. Grünwald
year: 2005
title: "The Statistical Strength of Nonlocality Proofs"
doi: 10.1109/TIT.2005.851738
url: https://arxiv.org/abs/quant-ph/0307125v2
claim: "There is an experiment on pairs of Bell singlets, of the 2×4×4 type, more than twice as strong as CHSH, and involving joint measurements on the pairs."
strata_touched:
  - D5/S3/QuantumBounds/StatisticalStrengthMagicSquare
license: citation-only
triage: anchor
---

# Statistical strength of nonlocality proofs

## Verified locator

DOI: https://doi.org/10.1109/TIT.2005.851738

Source: https://arxiv.org/abs/quant-ph/0307125v2

IEEE Transactions on Information Theory 51(8), 2812–2835.
The arXiv v2 PDF gives the KL conventions in Section IV.A, p. 6;
local response mixtures in Section II.D, p. 5; the three strengths
in Section IV.B, p. 8, Definitions 1–3 and equations (8)–(10);
the strengths table in Section V, p. 8; and Conjecture 5 in
Section VI.D, p. 11. The CHSH quantum and local tables appear in
Appendix III.C, pp. 18–20.

Section VI.D, Conjecture 5, p. 11:

> There is an experiment on pairs of Bell singlets, of the $2\times4\times4$ type, more than twice as strong as CHSH, and involving joint measurements on the pairs.

The type counts two parties, four settings per party, and four outcomes
per setting. Section IV.B, Definition 1, p. 8:

> When each measurement setting is sampled with equal probability, the resulting strength $S_Q^{\mathrm{UNI}}$ is defined by
> $$S_Q^{\mathrm{UNI}} := D(Q_{\sigma^\circ} \| \mathcal{P}_{\sigma^\circ}) = \inf_{\pi\in\Pi} D(Q_{\sigma^\circ} \| P_{\sigma^\circ,\pi}),$$
> where $\sigma^\circ$ denotes the uniform distribution over the settings.

Definition 2, p. 8:

> When the experimenter QM is allowed to choose any distribution on measurement settings, as long as the distribution for each party is uncorrelated with the distributions of the other parties, the resulting strength $S_Q^{\mathrm{UC}}$ is defined by
> $$S_Q^{\mathrm{UC}} := \sup_{\sigma\in\Sigma^{\mathrm{UC}}} D(Q_\sigma \| \mathcal{P}_\sigma) = \sup_{\sigma\in\Sigma^{\mathrm{UC}}} \inf_{\pi\in\Pi} D(Q_\sigma \| P_{\sigma,\pi}),$$
> where $\sigma\in\Sigma^{\mathrm{UC}}$ denotes the use of uncorrelated settings.

Definition 3, p. 8:

> When the experimeniter QM is allowed to choose any distribution on measurement settings (including correlated distributions), the resulting strength $S_Q^{\mathrm{COR}}$ is defined by
> $$S_Q^{\mathrm{COR}} := \sup_{\sigma\in\Sigma} D(Q_\sigma \| \mathcal{P}_\sigma) = \sup_{\sigma\in\Sigma} \inf_{\pi\in\Pi} D(Q_\sigma \| P_{\sigma,\pi}),$$
> where $\sigma\in\Sigma$ denoted the use of correlated settings.

The spelling “experimeniter” and “denoted” are those of the source. The
notation above expands the source small-capital strength macros and
its probability simplexes. KL is in bits; zero quantum mass contributes
zero, and positive quantum mass above zero local mass contributes
infinity. The results table lists CHSH strength 0.0462738469 in all
three columns.

## Two-singlet encoding

The local Hilbert indices are `Fin 2 × Fin 2`. The global indices group
Alice's two qubits and Bob's two qubits. The shared amplitudes multiply
the two literal singlet amplitudes `(01 − 10)/sqrt 2`, one on each
corresponding Alice–Bob qubit pair. Each party has four nonzero,
four-outcome projective measurements. A joint measurement contains a
projector that cannot be expressed as the Kronecker product of two
single-qubit operators.

The magic-square construction uses the commuting rows and columns of
`[[ZI, IZ, ZZ], [IX, XI, XX], [ZX, XZ, YY]]`. The fourth setting measures
`YI` and `IY`. Bob's projectors are transposed and conjugated by
`[[0, −1], [1, 0]]` on both qubits. The same local conjugation realizes
the source's CHSH table on a literal singlet; its displayed source
realization uses the Bell state Phi-plus.

## Magic-square credit

The parity construction originates in N. D. Mermin, “Simple unified
form for the major no-hidden-variables theorems”, Physical Review
Letters 65, 3373–3376 (1990), DOI 10.1103/PhysRevLett.65.3373,
and A. Peres, “Incompatible results of quantum measurements”, Physics
Letters A 151, 107–108 (1990), DOI 10.1016/0375-9601(90)90172-K.
Its two-party pseudo-telepathy use is due to G. Brassard, A. Broadbent
and A. Tapp, “Quantum Pseudo-Telepathy”, Foundations of Physics 35,
1877–1907 (2005), https://arxiv.org/abs/quant-ph/0407221.
The statistical-strength comparison combines this established
construction with finite log-sum and a uniform CHSH reference theory.
