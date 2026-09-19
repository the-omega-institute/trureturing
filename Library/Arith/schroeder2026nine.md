---
bibkey: schroeder2026nine
authors: Michael Schroeder
year: 2026
title: "Nine Prime Divisors in Odd Distinct Covering Systems"
doi: 10.5281/zenodo.22759614
url: https://michaelschroeder.ai/research/NinePrimeSupport/nine-prime-support-1.0.1.zip
claim: "The author claims that every finite covering with pairwise distinct odd moduli greater than one has at least nine distinct prime divisors in the least common multiple; prime-power exponents are unrestricted."
strata_touched:
  - D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity
license: "Paper and prose: CC BY 4.0; original verification code: MIT; third-party licenses retained."
triage: anchor
---

# Total prime support

Locator: https://doi.org/10.5281/zenodo.22759614. The original manuscript is
dated 13 September 2026; edition 1.0.1 is revised 15 September 2026.
Metadata and archive checked 16 September 2026. Source archive:
https://michaelschroeder.ai/research/NinePrimeSupport/nine-prime-support-1.0.1.zip.
The archive SHA-256 is
`9e674cf1665695945dc4d6d269ec27ad1567e9c5c236c2708b451de2a2a5196c`.
This is the source identity; no source Git revision is supplied.

The bound concerns the union of prime divisors across all moduli. It neither
bounds the number of prime factors of each modulus nor resolves unrestricted
Erdős #7. The paper advertises Lean verification; no completed local kernel
replay is claimed here. Attribution remains with Schroeder.

On 19 September 2026, the pinned archive's unmodified
`python3 checks/verify.py --fresh` regenerated all 7,814 finite geometry
batches, comprising 542,274 distinct integer queries, and exited 0 in
284.291 seconds on macOS arm64 with Python 3.14.3 and Apple clang 17.
All 28,001 integer inequalities passed with minimum surplus 4; all 28 closing
records passed, including the uniform terminal comparison 5310>5299.
The generated integer certificate and closing records match the author
attachments byte for byte, with SHA-256 respectively
`a1720cea93f30e04f31db6b49700a7d5c2d0fcfe9dff2f63ea2e3130b08629ac`
and `2fc48ecf06bc7ca256f7107648158fe92bff2052368b438267e6541e3eb07b1b`.
The verification summary matches every author-supplied field; its extra
fields report this fresh computation. The verifier sources and licenses
were unchanged.

This checks the finite geometry and rational budgets from their definitions.
It does not independently establish the full arbitrary-height reduction or
replace a Lean build and fresh kernel replay. The whole theorem remains an
attributed source result with that local verification boundary.
