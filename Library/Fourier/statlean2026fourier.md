---
bibkey: "statlean2026fourier"
authors: "Junwei Lu and StatLean contributors"
year: 2026
title: "StatLean Fourier smoothing and Gaussian Hermite suppliers"
doi: null
url: "https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254"
claim: "Pinned Lean proofs provide Fourier inversion for the tent and squared-sinc kernels, a signed-density comparison estimate, and Gaussian Hermite integral identities."
strata_touched: []
license: "Apache-2.0"
triage: "anchor"
---

# Fourier smoothing and Gaussian Hermite suppliers

The source is StatLean/Stat-Lean at immutable revision
`e1ef06bf52d2a8896439c5b59d982d9aad28a254`. The relevant files are
`StatLean/HypothesisTesting/ForMathlib/EsseenSmoothing.lean`,
`StatLean/HypothesisTesting/ForMathlib/BerryEsseen.lean`,
`StatLean/HypothesisTesting/Bootstrap/Edgeworth.lean`, and
`StatLean/HypothesisTesting/Bootstrap/Consistency.lean`.

The repository's StatLeanFourierSuppliers module ports the live supplier
closure under spec A17.2. Its header retains copyright 2024 Junwei Lu,
the full Apache-2.0 license, the original file paths and adaptation details.
The pinned upstream tree contains no NOTICE file. Its LICENSE has SHA-256
`d5945fe0f38866a919940212b0e3b5b0c30629b923c3e26dcce026571a29cd93`.

The upstream pin uses Lean 4.29.1 and Mathlib
`5e932f97dd25535344f80f9dd8da3aab83df0fe6`; this port targets Lean 4.33.0
and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. These incompatible
pins preclude a direct Lake dependency. When the repository's pinned Mathlib
provides equivalent declarations, the corresponding port is replaced by
direct imports. Ported declarations are upstream results and earn no
authored mathematical content credit.

The separate CompoundPoissonEdgeworth module proves the actual-law
finite-cutoff estimates and uniform real-time consequences using these
suppliers. The port does not itself establish an irrational-jump local
limit, a rare-event prefactor, or a recovery/minimax theorem.
