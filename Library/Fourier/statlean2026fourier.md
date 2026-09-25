---
bibkey: "statlean2026fourier"
authors: "Junwei Lu and StatLean contributors"
year: 2026
title: "StatLean Fourier smoothing and Gaussian Hermite suppliers"
doi: null
url: "https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254"
claim: "Pinned Lean proofs provide Fourier inversion for the tent and squared-sinc kernels, a signed-density comparison estimate, and Gaussian Hermite integral identities."
strata_touched: []
license: "Modified Apache-2.0 text in StatLean/Stat-Lean LICENSE at e1ef06bf52d2a8896439c5b59d982d9aad28a254; SHA-256 d5945fe0f38866a919940212b0e3b5b0c30629b923c3e26dcce026571a29cd93"
triage: "anchor"
---

# Fourier smoothing and Gaussian Hermite suppliers

## Verified locator

Pinned source: https://github.com/StatLean/Stat-Lean/tree/e1ef06bf52d2a8896439c5b59d982d9aad28a254

The source is StatLean/Stat-Lean at immutable revision
`e1ef06bf52d2a8896439c5b59d982d9aad28a254`. The relevant files are
`StatLean/HypothesisTesting/ForMathlib/EsseenSmoothing.lean`,
`StatLean/HypothesisTesting/ForMathlib/BerryEsseen.lean`,
`StatLean/HypothesisTesting/Bootstrap/Edgeworth.lean`, and
`StatLean/HypothesisTesting/Bootstrap/Consistency.lean`.

The repository's StatLeanFourierCore, StatLeanSignedSmoothing, and
StatLeanFourierSuppliers modules port the live supplier closure under spec A17.2.
Each header retains copyright 2024 Junwei Lu, the complete actual upstream
LICENSE text and attribution, the original file paths, and adaptation details.
The pinned upstream tree contains no NOTICE file. Its LICENSE is available at
https://raw.githubusercontent.com/StatLean/Stat-Lean/e1ef06bf52d2a8896439c5b59d982d9aad28a254/LICENSE
and has SHA-256
`d5945fe0f38866a919940212b0e3b5b0c30629b923c3e26dcce026571a29cd93`.

The upstream LICENSE heading says "Apache License" and "Version 2.0, January
2004", and its appendix says "Licensed under the Apache License, Version 2.0".
Those source labels are retained as attribution; the actual file is modified
Apache-2.0 text, not the standard Apache-2.0 full text. Salient textual differences
from the standard text are:

- The Contribution definition begins `"Contribution" shall mean, as submitted`
  rather than defining a work of authorship and its modifications or additions.
- Section 4 replaces the final paragraph about licensing modifications and
  derivative works with wording that includes "may provide additional grant of
  rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
  copies of the Work, as permitted under this License."
- Section 8 says "incidental, or exemplary damages" where the standard text
  says "incidental, or consequential damages".
- Section 9 changes the warranty-obligation wording: it says "You may offer only
  conditions consistent with this License" and then "You may add additional
  exclusion of warranty clauses, if such exclusions conflict with this License,
  or if required to do so for any reason." The standard own-behalf/responsibility
  and indemnification wording is absent.
- The appendix gives "Copyright 2024 Junwei Lu" and says "You may also add
  additional terms or conditions for use" instead of the standard recommendation
  to include identifying file/class and purpose information.

These differences occur in the LICENSE at the pinned upstream revision; they
were not introduced by this port. The three modules distribute its complete
original terms verbatim. This note identifies and distinguishes the source's
labels and actual text; it does not replace, amend, or add to those terms.

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
