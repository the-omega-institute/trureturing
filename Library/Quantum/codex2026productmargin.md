---
bibkey: codex2026productmargin
authors: Codex CLI
year: 2026
title: A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family
claim: Scalar entropy, common-lower-matrix and physical-state ingredients for a four-parameter equal-spectrum local-qubit product-margin family.
strata_touched:
  - D5/S3/Quantum/Information/ProductMarginEntropyCertificate
  - D5/S3/Quantum/Information/QubitNormalFormState
  - D5/S3/Quantum/Information/QubitEntropyContraction
  - D5/S3/Quantum/Information/ProductMarginBlockState
  - D5/S3/Quantum/Information/ProductMarginQubitOrder
  - D5/S3/Quantum/Hiai/CommonLowerHarmonicBound
license: citation-only
triage: anchor
---

# Equal-spectrum local-qubit product margins

The statement source is a local unpublished ordinary-mathematics manuscript,
`product-margin-equal-spectrum-proof/proof.tex`, supplied by the caller.
Its SHA256 is `e845aacc22ca07a78aa4309fc69aec72eff91489632ba3688aa10ccea33ff3c8`.
It is fallible input, with no priority or novelty claim. The Lean source derives
its own proof obligations; this note does not certify the complete manuscript.

For real nonnegative independent parameters $x_C,z_C,x_D,z_D$ in the two
closed unit disks, put $R_{i,\pm}=(I+x_iX\pm z_iZ)/2$,
$P=R_{C,+}\otimes R_{D,+}$ and $Q=R_{C,-}\otimes R_{D,-}$.
For an arbitrary complex PSD matrix $K\preceq P,Q$, the actual classical-bit
blocks are $(P-K)/2,K/2,K/2,(Q-K)/2$. The requested gap uses natural-log
spectral entropies of actual partial traces. Its derivation from that state
is a separate obligation from the scalar sufficient-budget theorem.

The scalar argument uses $F(u)=h((1+\sqrt u)/2)$ and its concavity on
$[0,1]$. This supplies quadratic contraction of the actual symmetric qubit
Holevo entropy. The high-reliability certificate uses ordinary binary entropy
concavity and monotonicity, with the positive exact constant
$\log(4096/3125)$. No numerical sampling supplies these universal bounds.

The common-lower-matrix argument reuses the repository's attained parallel-sum
minimum. Its equal-input split residual is $(U-V)^*K(U-V)$ after multiplying
the energy by two. This handles singular K without taking its inverse.
An explicit annihilating split handles a distinct pure local factor.
The qubit spectral bridge reuses the repository's determinant entropy formula
and accounts for its conversion from bits to nats.

These ingredients do not by themselves prove the whole four-party
Zhang–Yeung endpoint, its coordinate-free corollary, or any inequality for
arbitrary quantum states. Physical preparation, the actual-state entropy
reduction and the remaining common-trace estimate must be connected before
claiming that endpoint.
