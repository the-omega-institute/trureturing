---
bibkey: feldman2026missingzigzag
authors: David V. Feldman
year: 2026
title: "The Missing Zigzag: Cycles of Semitone Trichords and a Conservation Law in Equal Temperament"
doi: null
url: https://arxiv.org/html/2609.26114v1
claim: "Conjecture 9.3 gives the initial value and both parity recurrences for the balance-only count of labelled zigzag choices at n=3t, t>=2."
strata_touched:
  - D5/S3/Combinatorics/Zigzag/Choices
  - D5/S3/Combinatorics/Zigzag/FeldmanConjectureNineThree
license: CC-BY-4.0
triage: anchor
---

<!-- GID: D5/L/Combinatorics/feldman2026missingzigzag -->

# Feldman's balanced zigzag conjecture

## Verified locator

The checked primary version is https://arxiv.org/html/2609.26114v1, Section 5,
equation (2), Conjecture 9.3, and Open Problem 13.1. The checked arXiv
abstract/API records submission on 21 August 2026; that date is taken from
the record, not inferred from the identifier. No journal DOI or final
publication date is asserted. The paper/docs license is CC BY 4.0.

## Source semantics

For `n=3t`, `t>=2`, choose one directed form at each `k=2,...,n-2` in
`ZMod n`: I `(1,k-1)`, II `(k,1-k)`, III `(-1,k)`, IV `(k-1,-k)`,
V `(-k,1)`, or VI `(1-k,-1)`. At `k=2` only II, III, IV, and V are
allowed. Form labels are distinct even if endpoint pairs coincide. A choice
is balanced when outgoing minus incoming edge multiplicity is zero at every
nonzero residue. The count `a(t)` imposes no step-sum closure, connectivity,
Eulerian-circuit, or cycle-multiplicity condition.

Conjecture 9.3 asserts `a(2)=4`, `a(2r)=4a(2r-1)` for all `r>=2`, and
`(2r)a(2r+1)=6(2r-1)a(2r)` for all `r>=1`. The repository's stronger
closed forms are `a(2r)=4*6^(r-1)*choose(2r-2,r-1)` and
`a(2r+1)=2*6^r*choose(2r-1,r)` for every `r>=1`. They imply exactly those
three clauses for the literal balanced count. They do not settle all of Open
Problem 13.1, Conjecture 9.2, Hamiltonian existence, or the spectral claims.

## Prior art and provenance

The [author's repository at immutable commit
5da74e8b5a1b19ff724a5c16b3b162c67bf172dd](https://github.com/DavidVFeldman/missing-zigzag-new/tree/5da74e8b5a1b19ff724a5c16b3b162c67bf172dd)
has `Mzp.lean`'s `formPair` for the six forms. Its `BadPlan12` treats the
stricter balanced-and-closed case at `n=12`; `T6` is explicitly withdrawn;
and its dynamic program includes even antipodes but omits the odd singleton.
It supplies neither this all-`n` balance-only proof nor a reusable
source-equivalent certificate. That code uses Lean 4.28 and Mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`; this repository uses Lean
4.33 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

`Choices.lean` freshly transcribes the published Section 5 equation (2),
compared against the author's `formPair`; it imports no author code or
certificates. The remaining modules construct a labelled finite path
correspondence, a Laurent recurrence, and coefficient formulas in this
repository. Any future actual source port would require preservation of its
Apache-2.0 copyright, license, and NOTICE chain under A17.2; this delivery
is not a port and requests no dependency upgrade.

A bounded publication screen covered the exact arXiv record/title/phrase,
Crossref, the pinned author commit, and the linked Zenodo record. It found no
later public proof or final journal article in that scope; the checked paper
still lists the target as open. OpenAlex and Semantic Scholar were rate
limited. Private, unindexed, and later work remains unverified. This is no
worldwide absence or priority claim.
