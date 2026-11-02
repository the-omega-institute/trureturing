---
bibkey: conrad2012groupextensions
authors: Brian Conrad
year: 2012
title: Math 210B. Group cohomology and group extensions
doi: null
url: https://virtualmath1.stanford.edu/~conrad/210BPage/handouts/gpext.pdf
claim: "For an arbitrary extension with abelian kernel and its induced action, H1 acts simply transitively on endpoint-fixing automorphisms modulo conjugation by kernel elements."
strata_touched:
  - D5/S3/HomologicalAlgebra/AbelianExtensionH1
license: citation-only
triage: anchor
---

# Extension automorphisms and first cohomology

Section 2.1, pp. 2–3, defines automorphisms fixing both endpoints, their equivalence modulo kernel conjugations, and the cocycle twist action. It states simple transitivity, assigning its verification to HW10. No splitting or trivial-action hypothesis is imposed. The year denotes the PDF creation metadata rather than a claimed first publication.

The corresponding Lean construction uses the given extension, descends its actual conjugation action, and proves lift independence and the mutually inverse defect and twist operations. Compatibility with automorphism composition and the resulting group isomorphism are proved in the repository; the handout literally states a simply transitive action on the quotient set. Mathlib supplies the general-action cohomology quotient. Its coboundary convention is the negative of the parameter convention used for kernel conjugation.

## Verified locator

- URL: https://virtualmath1.stanford.edu/~conrad/210BPage/handouts/gpext.pdf
- Locator: Section 2.1, pp. 2–3.
