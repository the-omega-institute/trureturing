---
bibkey: willems1976symmetry
authors: Jan C. Willems
year: 1976
title: Realization of systems with internal passivity and symmetry constraints
doi: 10.1016/0016-0032(76)90081-8
claim: Minimal internally symmetric realizations are related by changes of basis preserving the realization's invariant quadratic form; the positive-metric case gives orthogonal equivalence.
strata_touched:
  - D5/S3/Quantum/Measurements/MinimalSymmetricRealizationUniqueness
license: citation-only
triage: anchor
---

# Minimal Symmetric Realizations

Willems, Theorem II and Remark 3, describe minimal internally symmetric
realizations through factorizations of a uniquely determined nonsingular
symmetric form. Remark 4 identifies the associated quadratic form as
independent of the chosen internally symmetric realization. The preceding
proof uses uniqueness of the change of state coordinates between minimal
realizations.

The Lean theorem proves the positive real inner-product specialization from
equality of all moments, with the symmetry of both dynamics and reachability
of both realizations explicit. It constructs the orthogonal map by transporting
Gram forms on finitely supported input combinations. No passivity assumption
or stability condition is imposed. This note does not claim that Willems uses
the repository's exact moment-based statement or its Lean type-class signature.

## Verified locator

- DOI: https://doi.org/10.1016/0016-0032(76)90081-8
- Crossref metadata retrieved on 2026-09-06 confirmed the author, title,
  June 1976 publication, and DOI above.
- Author's publication list:
  https://homes.esat.kuleuven.be/~jwillems/Publications.html
- Full text, pages 609-610 for the symmetry result:
  https://homes.esat.kuleuven.be/~jwillems/Articles/JournalArticles/1976.4.pdf
- An initial download of `1976.1.pdf` was a different article, *Mechanisms for
  the Stability and Instability in Feedback Systems*. It was excluded after
  inspecting its title; the publication list supplied the correct PDF link.
