---
slug: oeis-a086205-bala-complex-shift-determinant-refutation
bibkey: bala2023a086205
doi: null
url: https://oeis.org/A086205
triage: theorem
motivation_gids:
  - D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.result
---

# Bala's A086205 complex-shift determinant conjecture

## Problem

Peter Bala's formula block in [OEIS A086205](https://oeis.org/A086205/internal)
states:

> Conjecture: a(n) = the determinant of the n X n matrix ( binomial(i^2 + z, j) ) for arbitrary complex z. (End)

The entry defines $a(n)$ by the unshifted determinant. Its PARI program is
`a(n)=matdet(matrix(n,n,i,j,binomial(i^2,j)))`, with rows and columns
numbered from one through $n$. The sequence offset is $0,3$, so $n=0$
is included. For complex $w$ and natural $k$, the binomial coefficient is
the falling factorial $w(w-1)\cdots(w-k+1)/k!$, with empty product one.

The complete assertion is
$$
\forall n\in\mathbb N\;\forall z\in\mathbb C,\qquad
\det\!\left(\operatorname{choose}((i+1)^2+z,j+1)\right)_{i,j\in\operatorname{Fin}(n)}
=
\det\!\left(\operatorname{choose}((i+1)^2,j+1)\right)_{i,j\in\operatorname{Fin}(n)}.
$$
Here $\mathbb N$ includes zero and the empty determinant is one.
The Lean definition `shiftedDet` uses `Ring.choose`, and `claim`
retains both universal quantifiers and both one-based indices.

## Motivation

The conjecture asserts invariance of a determinant under a common complex
shift of all squared row arguments. This is stronger than the unshifted
definition of A086205. The one-dimensional determinant tests that asserted
invariance directly, without relying on the entry's factorial products or
recurrences.

## Gap

The bounded documentary checks recorded in
[issue 26954](https://github.com/the-omega-institute/trureturing/issues/26954)
found no matching settlement. Exact-target repository searches at
`82ca796fa3d326df95fef9758103880b5987a5bf` and observed remote revision
`a9b9333d5cdf02c45275b22b7a256d6d4f57b87c`, and pinned Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, found no exact-target match.
GitHub Lean code search for A086205 returned zero results.
MathDB searches for A086205 and distinctive phrases did not identify this
assertion or its settlement in their returned windows; the phrase-query
windows contained 20 results each. The two arXiv queries returned
`totalResults=0`. The checked fields of linked A057863 revision 59 and
A266091 revision 29 contained no explicit settlement.

These are `not-found-in-searched-scope` readings. The cited general
determinant literature was not checked theorem by theorem. Unindexed or
differently worded work remains unverified; no exhaustive absence or
priority claim follows.

## Route

Use $n=1$ and $z=1$. The shifted matrix has the single entry
$\operatorname{choose}(2,1)=2$, whereas the unshifted matrix has entry
$\operatorname{choose}(1,1)=1$. A one-by-one determinant is its entry.
The universal assertion would therefore imply $2=1$ in $\mathbb C$.

The proof applies `Matrix.det_fin_one`, unfolds `Matrix.of`, and uses
`Ring.choose_one_right` with numerical normalization. It proves the
negation of the complete assertion, rather than a different indexing
convention or a restricted shift statement.

## Falsifier

The certificate depends on the source allowing $n=1$, $z=1$, and
one-based row and column indices. A source with different conventions
would be a different assertion. Under the stated conventions, a failure
of either singleton determinant evaluation would invalidate this route;
both evaluations occur in the Lean proof of `result`.

## Evidence

The theorem
`D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.result`
has the literal type `Not claim`; the definition `claim` has type
`Prop`. Its source is
[D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.lean](../D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.lean),
with the corresponding
[Blueprint exposition](../Blueprint/D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.md).
The source conventions and verified locators are in
[the Library note](../Library/Certificates/bala2023a086205.md).

The compiled axiom closure of every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The only public theorem is `result`; `shiftedDet` and `claim`
are definitions.

## Triage

`theorem`: the exact universal complex-shift assertion is refuted.

### What the settlement shows

- **Proved** by `D5/S0/Certificates/BalaComplexShiftDeterminantRefutation.result`:
  the source's universal assertion is false. The failure mechanism is
  already present in the singleton matrix: the shift changes its only
  entry from one to two.
- **Proved by definition**: the restriction $z=0$ is reflexive for every
  $n$. **Proved by the empty-determinant convention**: at $n=0$ both
  sides are one for every $z$. These are boundary observations, not
  additional retained Lean theorems.
- **Open here**: a corrected formula or a classification of shifts for
  other matrix sizes. The refutation supplies neither.
- **Open here**: independent verification of the source's unshifted
  factorial products, recurrences, asymptotics, and related-entry
  formulas. Their truth is not negated by the failure of the distinct
  shift-invariance conjecture. Any deduction that needs that invariance
  requires a separate valid argument.

## ASSUMED-UNVERIFIED

Exhaustive literature coverage and publication priority are
`ASSUMED-UNVERIFIED`. No corrected determinant identity, classification
at other sizes, or verification of the entry's other formulas is claimed.
