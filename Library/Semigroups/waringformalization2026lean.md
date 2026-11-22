---
bibkey: waringformalization2026lean
authors: The Waring formalization authors
year: 2026
title: "Waring's theorem in Lean 4"
doi: null
url: https://github.com/yunyougu50-create/waring-lean4/tree/cd0735c253f3b640262fcc74a61306cb41e23765
claim: 'For each positive exponent k, some bound g suffices to express every natural number as a sum of at most g kth powers of natural numbers.'
strata_touched:
  - D5/S3/Arith/Additive/Waring/WaringTheorem2
license: Apache-2.0
triage: anchor
---

# Waring's theorem in Lean 4

The proof of the qualitative Hilbert–Waring theorem is by the Waring
formalization authors. Its endpoint is `Waring.waringTheorem` in
`WaringTheorem2.lean` at revision
`cd0735c253f3b640262fcc74a61306cb41e23765`. The proof follows Linnik's method
as presented by G. J. O. Jameson. It combines exponential-sum estimates,
representation counts, positive density and an additive-basis argument.
<https://www.maths.lancs.ac.uk/jameson/warlin.pdf>

The complete upstream Apache-2.0 license is included verbatim in
`D5/S3/Arith/Additive/Waring/WaringDensity.lean`. The pinned source tree's
applicable notice material consists of that license and the attribution
in its source files. Each local module identifies its source path and
revision. The upstream proof supplies the bound consumed by
`BenfieldLippard.eventual_fixed_length`.

The port can be retired when the Mathlib revision pinned by this
repository contains an exact equivalent of `Waring.WaringTheorem`,
as witnessed by a successful checked direct application to the positive
fixed-length proof and a rebuild of the theorem that uses it. Equivalence
must preserve every positive exponent, uniform bounded length and all
natural targets, with zero bases allowed in the Waring input.
