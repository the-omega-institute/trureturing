---
slug: oeis-a289923-left-limit-nonnegativity
bibkey: kimberling2017a289923
doi: null
url: https://oeis.org/A289923
triage: open
motivation_gids:
  - D5/S1/Recurrence/Invariants/A289923LeftLimitNonnegative
---

# Nonnegativity of the A289923 left-limit sequence

The source definition and conjecture are quoted in
`Library/Arith/kimberling2017a289923.md`.

The complete target includes existence and uniqueness of an integer sequence
whose nth coefficient is eventually constant throughout a left neighborhood of
19/21, for each natural n including zero, and nonnegativity of every term.
Neighborhoods may depend on n. The source formal inverse is normalized by
constant coefficient one on the full domain 0 < r < 1.

The Lean declaration `A289923LeftLimitNonnegative.result` expresses all these
clauses without a generating-function hypothesis. Its denominator identity
is proved in every degree using the 21-step coefficient relation, and its
positivity conclusion follows by strong induction from a recurrence with
nonnegative forcing coefficients.

The strict target is bound to
https://github.com/the-omega-institute/trureturing/issues/29510#issuecomment-6818246365.
Independent source-fidelity review, formal admission and external problem
settlement remain outside this implementation stage. No first-publication or
statistical-independence claim follows from this proof source.
