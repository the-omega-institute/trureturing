---
bibkey: kimberling2017a289923
authors: Clark Kimberling; Colin Barker
year: 2017
title: "OEIS A289923: limiting inverse coefficients at 19/21 from the left"
doi: null
url: https://oeis.org/A289923
claim: "Conjecture:  all the terms are nonnegative."
strata_touched:
  - D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative
license: citation-only
triage: anchor
---

# OEIS A289923

The entry's NAME is:

> Limiting sequence of coefficients of 1/([1+r] - [1+2r]x + [1+3r]x^2 - ...), where [ ] = floor and r approaches 19/21 from the left.

Its COMMENT is:

> Conjecture:  all the terms are nonnegative.

Clark Kimberling authored the entry. Colin Barker supplied the rational
generating-function formula; that formula is a known input, not a new result.
The source's fixed numerical approximation in a separate FORMULA is not the
all-degree left-limit definition used by the Lean statement.

The cited immutable mirror is revision 14 of the entry:

- https://raw.githubusercontent.com/oeis/oeisdata/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A289/A289923.seq
- SHA-256: `439de83e66395377271d2d2ef829adacb0c2b2a42f6256a7d665a3ea6fdeae89`.
- Length: 1422 bytes.

The Lean proof establishes the connection to the source by index-dependent
stabilization of the literal real floor coefficients and the normalized formal
inverse. It does not infer that connection from a finite prefix or from Barker's
formula. The pinned source and its attribution do not establish publication
priority or an exhaustive literature search.
