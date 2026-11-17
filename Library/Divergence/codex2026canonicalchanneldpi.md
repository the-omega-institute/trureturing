---
bibkey: codex2026canonicalchanneldpi
authors: The Omega Institute
year: 2026
title: Composite quantum-channel data processing
doi: null
url: https://github.com/the-omega-institute/trureturing
claim: Sequential composition preserves the finite support-aware quantum relative-entropy data-processing inequality.
strata_touched:
  - D5/S3/Quantum/Divergence/CanonicalChannelDPIComposition
license: citation-only
triage: anchor
---

# Composite quantum-channel data processing

This module records the closure of finite support-aware quantum relative entropy data processing under sequential composition. For channels \(A\xrightarrow{\Phi}B\xrightarrow{\Psi}C\), the existing canonical DPI is applied first to the intermediate pair \((\Phi(\rho),\Phi(\sigma))\), then to \((\rho,\sigma)\). The finite channel structure supplies the definitional identity \((\Psi\circ\Phi)(\rho)=\Psi(\Phi(\rho))\).

The theorem covers singular states through the existing `WithTop ℝ` support-aware extension and keeps the three finite carriers independent. It is a pathway lemma for longer channel chains; iterating it gives monotonicity along any finite sequence without reproving the matrix logarithm comparison.

This is a formal composition consequence, not a new independent proof of the one-step data-processing inequality.
