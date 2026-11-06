---
bibkey: hertzjabbourcerf2017entropypower
authors: Anaelle Hertz, Michael G. Jabbour, Nicolas J. Cerf
year: 2017
title: "Entropy-power uncertainty relations: towards a tight inequality for all Gaussian pure states"
doi: 10.1088/1751-8121/aa852f
url: https://arxiv.org/abs/1702.07286v2
claim: "The paper proposes the entropic uncertainty relation h(x)+h(p)-(1/2)ln(sigma_x^2 sigma_p^2/|gamma|) >= ln(pi e hbar), saturated by all pure Gaussian states, proves by variational calculus that pure Gaussian states are stationary points of the uncertainty functional, and states that the relation holds for all states under assumptions that include the concavity of the functional for mixed states."
strata_touched:
  - D5/S3/Quantum/Measurements/EntropyPowerCovarianceUncertaintyRefutation
license: citation-only
triage: anchor
---

# Hertz, Jabbour and Cerf, entropy-power uncertainty relations

## Verified locator

DOI: https://doi.org/10.1088/1751-8121/aa852f (J. Phys. A: Math. Theor. 50, 385301, 2017).

Source: https://arxiv.org/abs/1702.07286v2

A. Hertz, M. G. Jabbour and N. J. Cerf, arXiv:1702.07286v2 (the latest version). Quotations are from the v2 TeX source.

## Statement

For a one-mode state with $[\hat x,\hat p]=i\hbar$, $h(x)$ and $h(p)$ are the Shannon differential entropies of the quadrature distributions and $\gamma$ is the covariance matrix, with $\sigma_{xp}=\langle\{\hat x,\hat p\}\rangle/2-\bar x\bar p$. Section III.B replaces the mutual information in a joint-entropy relation by the Gaussian mutual information $I_G(x{:}p)=\frac12\ln(\sigma_x^2\sigma_p^2/|\gamma|)$:

> $$h(x)+h(p) - {1\over 2} \ln \left( \sigma_x^2 \sigma_p^2 / |\gamma| \right) \ge \ln(\pi e \hbar).$$
> We will show below (under some assumptions) that this inequality holds for all states, regardless of whether the Wigner function is positive everywhere or not.

Section III.C adds that "we also need to assume the concavity of our uncertainty functional in order to extend the proof to mixed states". The relation and both assumptions are repeated in A. Hertz and N. J. Cerf, J. Phys. A 52, 173001 (2019), arXiv:1809.01052v2, Section 3.4.

## Encoding and boundary

The repository takes $\hbar=1$, describes a finite mixture of one-mode Gaussian states by its Wigner function, a convex combination of Gaussian densities on phase space whose covariances satisfy $\det\gamma_i\ge1/4$, reads the quadrature distributions as its marginals and $\gamma$ as its central second moments, and proves that the inequality fails for such mixtures: the equal mixture of the coherent states with means $\pm(6,6)$ violates it. The relation for pure states, the joint-entropy (Wigner-entropy) relation, the $n$-mode extension and states with negative Wigner functions are outside this conclusion.
