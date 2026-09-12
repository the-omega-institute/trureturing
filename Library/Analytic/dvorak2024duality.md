---
bibkey: dvorak2024duality
authors: Martin Dvorak and Vladimir Kolmogorov
year: 2026
title: Duality theory in linear optimization and its extensions -- formally verified
doi: 10.46298/afm.14253
claim: Finite Farkas alternatives and strong duality hold over ordered scalars, including valid linear programs with extended coefficients and finite opposite attained values when both programs are feasible.
strata_touched:
  - D5/S3/Analytic/Convexity/FarkasAlternative
  - D5/S3/Analytic/Convexity/ExtendedFarkas
  - D5/S3/Analytic/Convexity/FiniteStrongDuality
license: Apache-2.0 source; citation-only article
triage: anchor
---

The article appears in Annals of Formalized Mathematics, volume 2, published
13 March 2026. The publisher and Crossref metadata agree on the title, authors,
DOI and publication date. The locator retains the initial preprint year 2024;
the bibliographic year above identifies the published article.

The Lean source is madvorak/duality at immutable revision
7e6502ab40b9ea7d42bd2eadc115b6a8b653392f. Its original Lean 4.18.0 and Mathlib
aa936c36e8484abd300577139faf8e945850831a interfaces are adapted directly to
Lean 4.33.0 and the repository's adopted Mathlib revision
db584cd6d46c92f209a44c0f1c829460d327499d. The Bartl recursion retains its
noncommutative ordered division-ring scope. Extended Farkas retains all four
infinity restrictions. The selected ValidELP theorem retains all six validity
fields and supplies finite opposite reached values under both feasibility
hypotheses, for arbitrary finite row and column types over a linearly ordered
field. Feasibility excludes an objective value of positive infinity, as in
the original definition.

The three mathematical owners contain the required portions of Common,
FarkasBartl, FarkasBasic, ExtendedFields, FarkasSpecial and LinearProgramming.
The mathematical constructions are the authored source proofs. The diagnostic
Linters dependency and the separate StandardLP interface are omitted.

FarkasAlternative bundles the complete upstream Apache-2.0 license and the
historical Mathlib Apache-2.0 license. The immutable upstream archive has no
NOTICE file. Credits to Andrew Yang, Henrik Böving and Richard Copley accompany
their supporting material. ExtendedFarkas retains the Kevin Buzzard copyright
and authorship notice from its cited historical EReal inspiration and Lean3
origin. Each adapted module identifies its modifications.

Retirement requires an equivalent native declaration at a Mathlib revision
actually adopted by this repository, with direct instantiations checking the
unchanged ordered-scalar and extended-coefficient contracts and standard axiom
closure. Acceptance upstream alone does not meet this condition.

Sources:

- https://afm.episciences.org/14253
- https://api.crossref.org/works/10.46298/afm.14253
- https://arxiv.org/abs/2409.08119v3
- https://github.com/madvorak/duality/tree/7e6502ab40b9ea7d42bd2eadc115b6a8b653392f
- https://github.com/leanprover-community/mathlib4/blob/333e2d79fdaee86489af73dee919bc4b66957a52/Mathlib/Data/Real/EReal.lean
- https://github.com/leanprover-community/mathlib/blob/2196ab363eb097c008d4497125e0dde23fb36db2/src/data/real/ereal.lean
