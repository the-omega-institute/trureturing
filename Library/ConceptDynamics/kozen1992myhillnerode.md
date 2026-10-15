---
bibkey: kozen1992myhillnerode
authors: Dexter Kozen
year: 1992
title: On the Myhill-Nerode Theorem for Trees
doi: null
url: https://www.cs.cornell.edu/~kozen/Papers/mn.pdf
claim: The opening string theorem uses equality of all continuation membership tests on the entire word space; the tree theorem extends context equivalence.
strata_touched:
  - D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality
license: citation-only
triage: anchor
---

# Continuation equivalence on all words

The opening statement on page 1 defines the string relation on all words:
two words are equivalent when appending every common continuation gives
the same language-membership answer. It identifies finite index of this
relation with regularity. The publication is Bulletin of the European
Association for Theoretical Computer Science 47, pp. 170–173.

For arbitrary output functions, the corresponding response profile records
the output at every continuation. Equality of profiles remains right stable
by associativity of concatenation. This output-valued application is distinct
from attributing an arbitrary-output theorem to Kozen's Boolean statement.
A language-restricted output can be extended to all words with a separate
illegal value. Prefix closure makes the illegal class absorbing.

## Verified locator

Author-hosted PDF: https://www.cs.cornell.edu/~kozen/Papers/mn.pdf
The string statement and relation appear on PDF page 1; the tree theorem
and the equal-state/context implication appear on PDF pages 3–4.
