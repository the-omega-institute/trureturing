---
bibkey: stacks2026finitegluing
authors: The Stacks Project Authors
year: 2026
title: Sheaves and finite nonempty inverse systems
doi: null
url: https://stacks.math.columbia.edu/tag/086J
claim: Cofiltered limits of finite nonempty sets are nonempty without a surjectivity hypothesis; compatible dependent functions glue uniquely.
strata_touched:
  - D5/S3/ObserverMemory/InverseLimits/FiniteCofilteredLimit
  - D5/S3/ConceptDynamics/Observation/HistoryPayloadFactorization
license: citation-only
triage: anchor
---

# Finite inverse systems and assignment gluing

Lemma 4.21.7, tag 086J, states that a cofiltered diagram of finite nonempty
sets has nonempty limit. The original transition maps need not be
surjective. The proof constructs a minimal nonempty subsystem, proves its
maps surjective, and then proves its component sets are singletons.

Section 6.7, tag 006S, defines the unique gluing condition for sheaves.
Its product-of-fibers example assigns to an open set U the product of the
sets A(x) over x in U. Overlap equality supplies a unique common value at
every point, hence a unique section. A discrete topology allows arbitrary
subsets as opens.

For assignments constrained on supports K(c), the common function is legal
if each support contained in the global domain lies entirely in one member
of the cover. This last condition permits each relation to be checked on a
single local section; it is additional to the sheaf condition for functions.

## Verified locator

- Lemma 4.21.7: https://stacks.math.columbia.edu/tag/086J
- Section 6.7, including the product-of-fibers example:
  https://stacks.math.columbia.edu/tag/006S
