---
bibkey: gronwall1913asymptotic
authors: T. H. Gronwall
year: 1913
title: Some asymptotic expressions in the theory of numbers
doi: 10.1090/s0002-9947-1913-1500940-6
claim: The limsup of sigma(n)/(n log log n) is exp(gamma); the new module supplies its lower epsilon envelope and packages it with the existing upper envelope.
strata_touched:
  - D5/S3/Weil/GronwallLowerEnvelope
license: citation-only
triage: anchor
---

# Some asymptotic expressions in the theory of numbers

T. H. Gronwall, Transactions of the American Mathematical Society 14 (1913),
no. 1, pp. 113-122. The classical result is
`limsup sigma(n)/(n log log n) = exp(gamma)`.

The new formalization uses the equivalent normalized epsilon envelopes. Its
lower witnesses are `primorial(y)^(a+1)`. The finite numerator loss is at most
`(1/2)^a * sum' m : Nat, 1/(m : Real)^2`, which tends to zero. The denominator
uses only `primorial_le_four_pow`, and the sharp factor uses the `bound''`
declaration in the frozen Mertens Third module.
The upper envelope is consumed from its existing repository owner. This is
a new Lean proof of a known result, with no claim of mathematical novelty.

On 2026-09-07 the Crossref API title query independently confirmed the author,
title, year, volume, pages, and DOI above. The Divisor function article at
<https://en.wikipedia.org/wiki/Divisor_function> was read at the displayed
limsup formula and its Gronwall 1913 reference; it states the formula above.
The AMS original PDF request returned HTTP 403 (curl exit 56), so the original
paper's internal theorem numbering and proof were not inspected. Attribution
of the statement uses that secondary source, not a claimed reading of the PDF.

Provenance: consensus-rnd implementation worker gronwall-lower-0907/attempt-1;
one Codex worker, no additional skill or review seats. The user supplied the
prime-power route. This worker checked the finite estimates and the exact
epsilon statements with Lean through `make lean`.

## Locator

- DOI: https://doi.org/10.1090/s0002-9947-1913-1500940-6
- Checked statement: https://en.wikipedia.org/wiki/Divisor_function#Growth_rate
- Verification scope: Crossref bibliographic metadata and the secondary-source
  limsup formula. No original-paper theorem number or proof is attributed.
