---
bibkey: tao2005primefourier
authors: Terence Tao
year: 2005
title: An uncertainty principle for cyclic groups of prime order
doi: 10.4310/MRL.2005.v12.n1.a11
url: https://arxiv.org/abs/math/0308286v6
claim: For prime cyclic order, all square Fourier minors are nonzero and the support-size uncertainty bound improves to an additive bound.
strata_touched:
  - D5/S3/ObserverMemory/FourierFibers/FinitePronyKoopmanObservationBridge
license: citation-only
triage: anchor
---

# Prime periods remove exact Fourier erasure kernels

The v6 PDF was read, including Theorem 1.1, Lemma 1.3 and the restriction-map consequence. The pages containing Theorem 1.1 and Lemma 1.3 were also visually checked. The paper explicitly attributes the nonzero-minor result to Chebotarev and gives its polynomial proof. Neither that theorem nor its known-support interpolation corollary is new to this project.

The arithmetic-clock draft applies the result to the repository's existing finite modal time samples. For a known set of k distinct grid modes at prime cyclic period p, any k distinct time samples determine the amplitudes. For an unknown s-sparse grid signal, 2s samples give injectivity when 2s <= p. This is not an assertion of a polynomial-time sparse-support algorithm, an l1-recovery guarantee, or uniform stability.

A two-row, two-column prime Fourier matrix with unit column norms has smallest singular value sqrt(1-cos(pi/p)); it tends to zero. Thus full spark cannot replace the singular-value or noise budget. Composite period six with rows {0,2} and modes {0,3} provides an exact alias example. The Hilbert/Fourier support statement is not identified with a physical measurement uncertainty bound without an explicit experimental map.

FinitePronyKoopmanObservationBridge already provides consecutive-window injectivity for separated known nodes; it has not been extended by this note or checked against a new Lean proof. The Section 18 theory draft and code are supplied in PR #8891 discussion pending append to the unique main volume.
