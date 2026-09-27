---
bibkey: euhuangkao2026zerorun
authors: Sen-Peng Eu, Zai-Ting Huang, and Louis Kao
year: 2026
title: "Zero-Run Spectra of the (3,2) Raney numbers Modulo Primes"
doi: null
url: https://arxiv.org/html/2609.25742v1
claim: "Conjecture 7.1: for fixed positive k,r and a prime p not dividing kr, the tied left-to-right record values of the zero-run sequence of the Raney numbers modulo p belong to a finite union of families (a*p^m+b)/c, with a,b,c depending only on k,r,p."
strata_touched:
  - D5/S1/Recurrence/Raney/ZeroRunFamilies
license: citation-only
triage: anchor
---

# Zero-run spectra of Raney numbers

## Verified locator

The primary source is arXiv:2609.25742v1, submitted on 2026-09-22. Its HTML
version at https://arxiv.org/html/2609.25742v1 gives the title and authors above.
No later arXiv version was listed when the source was refreshed on 2026-09-24.

## Literal source claim

Conjecture 7.1 states:

> Fix k, r and a prime p not dividing kr. The left-to-right record values of
> the zero-run sequence of R_(k,r)(n) mod p belong to a finite union of
> families of the form (a p^m + b)/c, where a,b,c depend only on k,r,p.

The paper defines left-to-right records with ties allowed. Its zero-run sequence
is formed from the actual infinite residue sequence, rather than from terminal
runs created by cutting off a finite prefix. The source does not assert that
every term of every displayed family must occur.

The Raney number used in the repository is the literal natural quotient

`R_(k,r)(n) = r * binomial(k*n+r,n) / (k*n+r)`.

The quotient is proved integral before reduction modulo `p`; it is not replaced
by division in `ZMod p`, which would be invalid when the denominator vanishes
modulo `p`.

## Formal scope

`D5/S1/Recurrence/Raney/ZeroRunFamilies.raney_zero_run_coefficient_families`
proves a stronger statement than record containment. For every positive `k,r`
and prime `p` not dividing `k*r`, it supplies one finite set of integer triples
`(a,b,c)`, with positive `c`, before arbitrary endpoints are chosen, and proves
that every actual maximal finite zero interval has length `L` satisfying

`c*L = a*p^m + b`

for some triple in that set and some natural `m`. It also proves unbounded
nonzero support, so no infinite zero tail is silently treated as a finite run.
Tied record lengths are therefore included. No converse realization statement
for the coefficient families is made.

The construction represents the finite evaluation word by states
`Fin(max(k-1,r-1)+1) x Bool`. The Boolean component separates ordinary
binomial values from the guarded predecessor value at `n=0`. Lucas transitions
handle carries, the zero digit handles the predecessor borrow, and the fixed
word equation includes leading zeroes. The literal Raney residue is read as the
ordinary state at `r-1` minus `(k-1)` times the predecessor state. Eventually,
at indices `p^j`, this residue equals `k` modulo `p`; the coprimality hypothesis
makes it nonzero.

The paper's `(3,2)` results and the Catalan `(2,1)` specialization are known
cases and receive no separate repository credit in this delivery.

## Bounded prior-resolution evidence

A bounded search of the repository, arXiv, Crossref, and a fresh global issue
query for Raney Conjecture 7.1 found the source, known cases, and unrelated
records, but no full settlement in the searched scope. An OpenAlex request
returned HTTP 429 and supplies no absence evidence. These observations do not
certify worldwide novelty or first-publication priority.
