---
bibkey: grosswald1985representations
authors: Emil Grosswald
year: 1985
title: Representations of Integers as Sums of Squares
doi: 10.1007/978-1-4613-8566-0
claim: The classical characterization of the natural numbers representable as sums of two squares by the parity of the exponents of their prime factors congruent to three modulo four.
strata_touched:
  - D5/S3/PrimeForms/SumTwoSquaresClassification
  - D5/S3/PrimeForms/ThreeModFourDescent
license: citation-only
triage: anchor
---

# Representations of Integers as Sums of Squares

Emil Grosswald's monograph (Springer-Verlag, 1985, 251 pp.) is devoted to the
representation of integers as sums of squares. Its chapter "Sums of Two
Squares" (pp. 13-23, DOI `10.1007/978-1-4613-8566-0_3`) presents the classical
two-squares theory, anchoring the characterization formalized in
`D5/S3/PrimeForms/SumTwoSquaresClassification`: a natural number is a sum of
two squares exactly when every prime congruent to three modulo four occurs to
an even exponent in its factorization.

Only the statement of the classical characterization is attributed to the
literature through this anchor. The repository proof discharges the statement
through Mathlib's `Nat.eq_sq_add_sq_iff`, so the source's proof route (descent
at primes congruent to three modulo four, representation of primes congruent
to one modulo four, and multiplicative composition) is not attributed. The
anchor also attributes the statement of the descent step itself, formalized
separately in `D5/S3/PrimeForms/ThreeModFourDescent`: a prime congruent to
three modulo four dividing a sum of two squares divides both bases. Only that
statement is attributed; the repository proof of it goes through Mathlib's
quadratic-residue machinery, not through the chapter's argument. The
full chapter text is paywalled, so the theorem numbering inside the chapter
was not verified; the attribution rests on the verified chapter title, page
range, and DOI together with the standard identification of this result as
the sum-of-two-squares theorem.

## Search log

- 2026-08-11: Queried the web for `Grosswald "Representations of Integers as
  Sums of Squares" Springer 1985 DOI 10.1007`. Publisher results verified the
  book DOI `10.1007/978-1-4613-8566-0`, and a Proceedings of the Edinburgh
  Mathematical Society review record confirmed Springer-Verlag, 1985, 251 pp.
  The result list exposed the chapter record "Sums of Two Squares" at DOI
  `10.1007/978-1-4613-8566-0_3`.
- 2026-08-11: Fetched the Springer chapter page for
  `10.1007/978-1-4613-8566-0_3`. It confirmed the chapter title "Sums of Two
  Squares" and page range pp. 13-23; the full text is paywalled, so no
  in-chapter theorem number was verified.
- 2026-08-11: Queried the web for the classical statement (`"sums of two
  squares" theorem "if and only if" prime "3 (mod 4)" even power`). Results
  (including the standard encyclopedia entry on the sum-of-two-squares
  theorem) restated the characterization by even exponents of prime factors
  congruent to three modulo four, corroborating the claim attributed here.

## Verified locator

- DOI: https://doi.org/10.1007/978-1-4613-8566-0
- Chapter: https://doi.org/10.1007/978-1-4613-8566-0_3
