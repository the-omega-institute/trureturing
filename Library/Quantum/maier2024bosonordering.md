---
bibkey: maier2024bosonordering
authors: Robert S. Maier
year: 2024
title: "Boson Operator Ordering Identities from Generalized Stirling and Eulerian Numbers"
doi: 10.48550/arXiv.2308.10332
url: https://arxiv.org/abs/2308.10332v4
claim: "The paper expresses normal-ordering identities for boson creation and annihilation operators through the generalized Stirling numbers of Hsu and Shiue and associated generalized Eulerian numbers, gives closed forms for several parameter pairs, and conjectures (Conjecture 5.3) a closed form for the case alpha = -1, beta = 2 with a generalized binomial coefficient."
strata_touched:
  - D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm
license: citation-only
triage: anchor
---

# Boson Operator Ordering Identities from Generalized Stirling and Eulerian Numbers

Maier works with the Hsu–Shiue generalized Stirling numbers
`S_{n,k}(α, β; r)`, `0 ≤ k ≤ n`, and the rescaled numbers
`Ŝ_{n,k} = β^k k! S_{n,k}`, defined in §4 by the expansion

> (βx + r)^{n, α} = Σ_{k=0}^{n} Ŝ_{n,k}(α, β; r) C(x, k),

where `(y)^{n, α} = y(y − α) ⋯ (y − (n − 1)α)` is the generalized falling
factorial. Theorem 4.1 gives the equivalent finite sum
`Ŝ_{n,k} = Σ_{x=0}^{k} (−1)^{k−x} C(k, x) (βx + r)^{n, α}`. These numbers
connect orderings of words in the boson operators of the Weyl–Heisenberg
algebra studied in §3 and §6. For `α = −1`, `β = 2` the factorial is the rising
factorial `y(y + 1) ⋯ (y + n − 1)`. After two closed-form theorems in §5, the
paper states, as found heuristically:

> Conjecture 5.3. For all r ∈ ℤ,
> Ŝ_{n,k}(−1, 2; r) = Σ_{j=⌊(2−r)/2⌋}^{⌊(n+2−r)/2⌋} C(n − j, n − k) n! C(n + 1, 2j + r − 1),

and remarks that the upper argument `n − j` of the first binomial coefficient
may be negative.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2308.10332
- URL: https://arxiv.org/abs/2308.10332v4
- Version and location: arXiv:2308.10332v4 (2024-02-09; journal version Adv. in Appl. Math. 156 (2024), Paper No. 102678, not read), source file `main.tex`: §4 for the definition of `Ŝ_{n,k}(α, β; r)` and Theorem 4.1; §5 for Conjecture 5.3 (the `conjecture` environment numbered with the theorem counter within sections).
