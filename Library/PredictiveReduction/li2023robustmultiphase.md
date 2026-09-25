---
bibkey: li2023robustmultiphase
authors: Haoya Li; Hongkang Ni; Lexing Ying
year: 2023
title: On adaptive low-depth quantum algorithms for robust multiple-phase estimation
url: https://arxiv.org/abs/2303.08099v4
claim: Robust multiple-phase estimation distinguishes integer-power and real-power access, with arithmetic amplification choices to prevent collisions.
strata_touched:
  - D5/S3/ObserverMemory/Trajectories/FibonacciNearReturn
  - D5/S3/ObserverMemory/FourierFibers/FinitePronyKoopmanObservationBridge
license: citation-only
triage: anchor
---

# Prime factors already participate in phase-estimation algorithms

The v4 record dated 2023-10-25, parsed Sections I.C and III.C, Lemma III.8 and Remark III.9 were inspected. The PDF opening page was rendered. The source addresses several dominant eigenvalues with residual spectral weight, including gapped and gapless settings. It distinguishes a black-box unitary with integer powers from Hamiltonian access allowing real evolution times.

For real-power access, the amplification factors can be selected between two and four. For integer-power access, the source uses primes, and its remark also allows suitable pairwise coprime integers, to avoid spectral collisions. These are established results and are not credited to the repository's present arithmetic-clock research. The source's signal-processing and Hadamard-test assumptions must remain explicit.

The Section 19 draft instead gives a direct finite-horizon residual estimate for known Hermitian generator classes and separately demonstrates a single-frequency Gaussian phase decoder. A scalar phase argument does not identify a general mixture of unknown frequencies. The existing finite Prony Lean bridge proves separated known-node window injectivity, not the source's robust multiphase estimation or the new matrix-error certificate.

The source provides a concrete literature route for extending the present single-phase test to unknown multimode experiments. The extension, its stable query complexity and its relation to thermal recovery remain separate obligations. No P/NP, universal golden-ratio optimality, or new named-conjecture resolution is inferred.
