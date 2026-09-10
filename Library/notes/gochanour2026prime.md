---
bibkey: gochanour2026prime
authors: Jason Robert Gochanour
year: 2026
title: Prime Cathedral fractional-part Mellin identities
doi: null
url: https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral
claim: The fractional-part Mellin base identity, its live floor-series prerequisites, and the substitution and tail-splitting argument.
strata_touched:
  - D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers
  - D5/S3/Weil/ZetaPntBounds/NymanMellinFloorSeries
  - D5/S3/Weil/ZetaPntBounds/NymanFractionalMellin
license: Apache-2.0
triage: anchor
---

# Prime Cathedral Fractional-Part Mellin Identities

The immutable source is `jrgochan/prime` commit
`ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2`, Copyright 2026 Jason Robert
Gochanour. The complete Apache-2.0 license is retained in
`D5/S3/Weil/ZetaPntBounds/NymanMellinHelpers.lean`.

The selected declaration is `bd_mellin_base_case_proved` in
`proofs/Cathedral/MellinBridge/IdentityBypass.lean:220`. Its argument identifies
the integral with a Mellin transform, proves analyticity, uses the floor-series
identity in the half-plane of absolute convergence, and applies the identity
theorem on the punctured positive half-plane. The live source chain includes
`MellinBridge/FloorDivMellin.lean`, selected `MellinBridge/FloorMellin.lean`
helpers, and the two plain definitions from `MellinBridge/Basic.lean`.
Connectedness is instead bound to the repository's existing
`ZetaBoundsUpper.isPathConnected_aux`; elementary complex-power prerequisites
are bound to the installed mathlib APIs. The unrelated Defs and Structural hubs
are not imported.

The real-parameter scaling adapts the substitution, split at one, and elementary
tail integration in `NymanBeurling/BDMellin.lean:169-363`, whose public reduction
begins at line 323. The local parameter ranges over all positive reals at most
one. This is a necessary binding companion for source E9, not a novelty claim.
The integrability companion uses bounded fractional part and the installed
complex-power integral estimate for every real parameter.

## Audit And Modifications

- 2026-09-08: Read the selected files at the immutable commit and compared the
  supplied dominating-theorem search receipts. The exact base hit was selected;
  no new analytic continuation was substituted.
- The recursive Git tree response was untruncated and contained `LICENSE`
  (blob `73e6084cbffc862bee625395b18de103633fe3bb`) and no NOTICE-named file.
- Upstream Lean 4.29.0 and mathlib `8a178386ffc0f5fef0b77738bb5449d50efeea95`
  differ from this repository's Lean 4.33.0 and mathlib
  `db584cd6d46c92f209a44c0f1c829460d327499d`; this is an A17.2 source port.
- Local modifications trim unused prerequisites, route namespaces, repair
  current-pin APIs, reuse exact local/mathlib prerequisites, and generalize the
  scaling parameter from natural numbers to real numbers. Fractional part is
  only assumed measurable and bounded. Null endpoints are removed by the
  installed set-integral equality.
- The local names `tail_vanishes` and `partial_zeta_tendsto` drop the upstream
  trailing apostrophe because canonical declaration selectors do not accept it.
  Their proof arguments are unchanged.
- Retirement requires an equivalent declaration in this repository's own
  installed future mathlib pin. Frozen content still follows the repository's
  migration rules and cannot simply be deleted.

E9 alone supplies no coverage edge for the combined E9/E10 atom
`dbfcaf2509c20aa2ecaf04d02d1de5f646e1f373452b1d3ec490c057f6b5eec9`.
E10, the actual Lp source vectors and separator, E11, and both directions of
the full original-object goal remain separate obligations.

## Verified locator

- Immutable source: https://github.com/jrgochan/prime/tree/ed0e4caa6c0fc0330c466d1103d88d1df8dbd4c2/proofs/Cathedral
- Selected theorem: `MellinBridge/IdentityBypass.lean:220`,
  `bd_mellin_base_case_proved`.
- Scaling argument: `NymanBeurling/BDMellin.lean:169-363`, with
  `bd_mellin_reduction_proved` at line 323.
