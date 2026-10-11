---
bibkey: leanpool2026majorizationtransfer
authors: Jon Crall; GPT-5.6 Thinking; Claude Fable 5; Claude Opus 5
year: 2026
title: "LeanPool finite-vector Hardy–Littlewood–Pólya transfer construction"
doi: null
url: https://github.com/LeanPool/lean-pool/blob/7498a16d2393e1f02245cb265d67ec4fb2587814/LeanPool/DavisKahan/ForTauCeti/Analysis/Convex/Majorization.lean
claim: "Prefix-sum domination with an antitone target admits a T-transform preserving domination and strictly decreasing the number of unmatched coordinates."
strata_touched:
  - D5/S3/Geometry/AlphaGeometry/MajorizationTransfer
license: citation-only
triage: anchor
---

## Verified locator

Source: https://github.com/LeanPool/lean-pool/blob/7498a16d2393e1f02245cb265d67ec4fb2587814/LeanPool/DavisKahan/ForTauCeti/Analysis/Convex/Majorization.lean

The declarations needed by `FiniteVector.exists_isTTransform_of_not_forall_le` are transplanted under Apache-2.0. Copyright (c) 2026 Kitware, Inc. All rights reserved. Authors: Jon Crall, GPT-5.6 Thinking, Claude Fable 5, Claude Opus 5. The complete license and NOTICE chain are retained in `docs/reports/brooks-suppliers/daviskahan-LICENSE.txt` and `daviskahan-NOTICE.txt`.

The target vector is antitone and nonnegative; the current vector is nonnegative and dominates every target prefix sum. If pointwise domination fails, the next T-transform remains nonnegative, preserves prefix-sum domination and agrees with the target in strictly more coordinates. This finite-vector transfer step is used by the logarithmic-simplex curvature proof; it is an existing third-party result, not repository novelty.

Retire this transplant when this repository's pinned Mathlib provides an equivalent transfer lemma, and replace its consumers by direct applications.
