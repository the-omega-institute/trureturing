---
bibkey: codex2026productmargin
authors: Codex CLI
year: 2026
doi: null
url: https://github.com/the-omega-institute/trureturing
title: A harmonic-mean certificate for the unequal-local-pair product-margin quantum Zhang–Yeung family
claim: Scalar entropy, qubit-state, common-lower-matrix and preparation-channel components for a four-parameter equal-spectrum local-qubit product-margin family.
strata_touched:
  - D5/S3/Quantum/Information/ProductMarginEntropyCertificate
  - D5/S3/Quantum/Information/QubitNormalFormState
  - D5/S3/Quantum/Information/QubitEntropyContraction
  - D5/S3/Quantum/Information/ProductMarginQubitOrder
  - D5/S3/Quantum/Foundation/FinitePreparationChannel
license: citation-only
triage: anchor
---

# Equal-spectrum local-qubit product margins

## Scope

The HTTPS locator identifies the repository implementation, not a public copy
of the manuscript. The statement source is a local unpublished ordinary-mathematics manuscript,
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

The common-lower-matrix argument uses the repository's split-energy carrier.
Its specialization to the attained parallel-sum minimum recovers harmonic
domination for positive definite inputs; the trace proof instead uses an
explicit split directly, including singular product margins. Its equal-input split residual is $(U-V)^*K(U-V)$ after multiplying
the energy by two. This handles singular K without taking its inverse.
An explicit annihilating split handles a distinct pure local factor. A rational
four-dimensional split gives the full common-trace bound on the two closed
local disks with x less than one; a zero denominator reduces to the pure
factor case.
The qubit spectral bridge reuses the repository's determinant entropy formula
and accounts for its conversion from bits to nats.

The preparation map uses columns of each density matrix positive square
root as Kraus operators. Its action on arbitrary complex input matrices is
the sum of their diagonal entries times the selected actual density states.
This retains zero probabilities and singular prepared states. Tensoring the Kraus
operators with an arbitrary finite spectator identity gives the local channel
on the complete joint matrix algebra. Its entry formula preserves every
spectator coherence and supplies the physical operation for data processing.

The ProductMarginZhangYeung source connects these ingredients to the actual
sixteen-dimensional state, its spectral entropy identity and local
information-processing estimates. Its nonnegative-gap statement concerns only
the four-parameter product-margin construction. It does not assert the
coordinate-free corollary or an inequality for arbitrary quantum states.

## Verified locator

URL: https://github.com/the-omega-institute/trureturing

The repository URL identifies the Lean implementation and its accompanying
source record for this local manuscript; the manuscript itself is unpublished
and is not represented as a public external publication.
