---
bibkey: len2022quantum
authors: Yink Loong Len, Tuvia Gefen, Alex Retzker, Jan Kołodyński
year: 2022
title: "Quantum metrology with imperfect measurements"
doi: 10.1038/s41467-022-33563-8
url: https://arxiv.org/abs/2109.01160v2
claim: "For a pure encoded probe state and an imperfect measurement, the quantum Fisher information is multiplied by gamma = max over orthogonal pairs of sum_x Re<xi_perp|M_x|xi>^2 / <xi|M_x|xi>. The supplement conjectures that for every classical noise channel M_x = sum_i p(x|i) Pi_i applied independently to N probes, an optimal pair is a cat pair cos(theta)|j>^N + sin(theta)|k>^N, -sin(theta)|j>^N + cos(theta)|k>^N."
strata_touched:
  - D5/S3/Quantum/Measurement/NoisyMeasurementCatOptimalityRefutation
license: citation-only
triage: anchor
---

# Quantum metrology with imperfect measurements

Yink Loong Len, Tuvia Gefen, Alex Retzker and Jan Kołodyński, Nature
Communications 13, 6971 (2022); arXiv:2109.01160v2. Quotations are from the
arXiv v2 source.

The noisy Fisher coefficient (Lemma 1, Eq. (gamma_M)):

> $\gamma_\cM=\max_{\ket{\xi},\ket{\xi_{\perp}}} \sum_x \frac{\mathrm{Re}\!\left\{\langle\xi_{\perp}|M_{x}|\xi\rangle\right\}^{2}}{\langle\xi|M_{x}|\xi\rangle}$

and its multi-probe form (Supplement, Eq. (AgammaN)) with
$M_{\xvec}=M_{x_1}\otimes M_{x_2}\otimes\cdots\otimes M_{x_N}$ (Eq. (AMxvec))
and $\VPhi\ket{\psi^N_{\pm}}=\ket{\zeta^N},\ket{\zeta^N_\perp}$, where
$\ket{\psi_{\pm}^N}=\frac{1}{\sqrt{2}}(\ket{\psi^N}\pm\ket{\psi_\perp^N})$
(Eq. (AVPhichoice)).

The conjecture (Supplement, end of "A note on optimality"):

> In fact this intuition together with some numerical evidence leads us to conjecture that for any classical noise channel, $M_{x}=\sum_{i}p\!\left(x|i\right)\Pi_{i}$ that is applied independently on each of the $N$ probes, the optimal $|\zeta^{N} \rangle,|\zeta_{\perp}^{N}\rangle$ take the form of ``cat states": $|\zeta^{N} \rangle =\cos\left(\theta\right)|j\rangle^{\otimes N}+\sin\left(\theta\right)|k\rangle^{\otimes N}$, $|\zeta_{\perp}^{N} \rangle =-\sin\left(\theta\right)|j\rangle^{\otimes N}+\cos\left(\theta\right)|k\rangle^{\otimes N}$, where $ \ket{j}, \ket{k}$ can be found numerically for just a single probe, and $\theta$ depends on $N$ and should be found numerically.

The encoding reads "optimal" as maximizing Eq. (AgammaN) over all
orthonormal pairs $\zeta,\zeta_\perp$ for channels with all $p(x|i)>0$, where
a maximizing pair exists, with $V_\Phi\psi=(\zeta+\zeta_\perp)/\sqrt2$
and $V_\Phi\psi_\perp=(\zeta-\zeta_\perp)/\sqrt2$, and states the conjecture
as the existence of some cat pair with $j\ne k$ attaining that maximum.

## Verified locator

- DOI: https://doi.org/10.1038/s41467-022-33563-8 (Nature Communications
  13, 6971 (2022); the conjecture is in Supplementary Note 5, printed p. 11,
  as reported by the literature seat).
- URL: https://arxiv.org/abs/2109.01160v2 (source `QMwIM-v2.tex`, md5
  `d618d71e36ac84cb2be4e09e2335e219`): Lemma 1 (l. 324–337), Eq. (AgammaN)
  (l. 1478–1482), Eq. (AMxvec) (l. 1483–1485), the definition of
  $\psi^N_\pm$ (l. 1488), Eq. (AVPhichoice) (l. 1507–1510), "A note on
  optimality" (l. 1550–1567), the conjecture (l. 1558–1567).
