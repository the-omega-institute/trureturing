---
bibkey: weisstein2026repeatingdecimal
authors: Eric W. Weisstein
year: 2026
title: "Repeating Decimal"
doi: null
url: https://mathworld.wolfram.com/RepeatingDecimal.html
claim: "Rational numbers have finite or repeating decimal expansions; periodic blocks admit rational quotient expressions."
strata_touched:
  - D5/S3/Arith/RepeatingDecimal/RepeatingDecimalQuotient
license: citation-only
triage: anchor
---

# Repeating decimal and integer long division

MathWorld's entry defines repeating decimals by eventual periodicity, states
that rational numbers have finite or repeating expansions, and discusses
rational conversion. Its bibliography includes Courant and Robbins,
What Is Mathematics?, second edition, section 2.2.4, pages 66–68,
“Rational Numbers and Periodic Decimals”. The cited web entry is the
verified source; the book reference is not an independently checked source.

The formalization implements the classical fractional long-division
algorithm for natural base b, numerator p, and denominator q. It proves
q P(n) + r(n) = b^n p by induction from the recursive integer state.
For b > 1 and p < q, normalized prefixes and the positional digit series
converge to p/q. If q divides b^L - 1, the digits have period L and
(b^L - 1)(p/q) = P(L). The arbitrary-base recursive invariant and its
connection to the real series are the repository's formal bridge; this
entry does not literally state those Lean quantifiers. No mathematical
novelty or minimal-period claim is made.

## Verified locator

- URL: https://mathworld.wolfram.com/RepeatingDecimal.html
- Scope: definition of repeating decimals, rational expansions, and rational
  conversion; the recursive bridge is proved in the associated Lean source.
