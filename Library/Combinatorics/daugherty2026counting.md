---
bibkey: daugherty2026counting
authors: Spencer Daugherty, Michaela Fahnestock, Shawn Huxtable, Michael Larson, Nourah Al Munayes and Storey Peacock
year: 2026
title: "Counting and Constructing Latin tableaux"
doi: null
url: https://arxiv.org/abs/2610.29291v1
claim: "Conjecture 6.3 states that for every integer k >= 5, the number LT(lambda) of Latin tableaux of shape lambda = (k,k-1,...,5,4,3,3) and conjugate type lambda-prime is 9*4^(k-3)."
strata_touched:
  - D5/S3/Combinatorics/Latin/Tableaux/Source
  - D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate
  - D5/S3/Combinatorics/Latin/Tableaux/Counting
license: citation-only
triage: anchor
---

# Counting and Constructing Latin tableaux

## Verified locator

URL: https://arxiv.org/abs/2610.29291v1

Version: arXiv:2610.29291v1, submitted 2026-10-21. The versioned
[author source](https://arxiv.org/src/2610.29291v1) and
[HTML Section 6](https://arxiv.org/html/2610.29291v1#S6) identify
Conjecture 6.3 in “Open problems”. The inspected author TeX has SHA-256
`328ad2a75c85bc166fad151ebd2515f9ba8f42c18bd56df618d3441237d52697`.
Its lines 739–741 state:

> If $\lambda = (k,k-1, \ldots, 5,4,3,3)$ with $k\geq 5$, then $LT(\lambda)=9\cdot4^{k-3}$.

The author spelling above follows the versioned paper's “Fahnestock”;
abstract metadata spells that name “Fahnesock”. The TeX and HTML were
inspected in the supplied source qualification; PDF rendering was not
checked. No DOI is established here. `citation-only` describes this
note's use of the source, not a license attestation for the paper.

## Counted objects and scope

Section 2 uses fixed left-aligned partition diagrams, with conjugation
interchanging rows and columns. Definition 2.5 specifies the type by
symbol multiplicities and prohibits an integer repeating in any row or
column. Section 4 defines $LT(\lambda)$ using type $\lambda'$.
The source explains that each row then contains the symbols from 1
through its row length. These are full fillings of fixed cells with
fixed integer symbols; the separately defined reduced counts are not
$LT$. Equal-length bottom rows remain distinct positions. The endpoint
$k=5$ has shape $(5,4,3,3)$.

The target has no finite upper cutoff or additional wide-partition
hypothesis. Conjectures 6.1, 6.2 and the broader wide partition
conjecture are separate assertions. A formal row-permutation encoding
requires its own two-way correspondence with the source shape/type
definition; the source observation is not a Lean proof of that bridge.

## Open-status attestation and evidence limits

The paragraph preceding Conjecture 6.3 says that for this family with
$k\geq 6$ nothing is known to be Latin by any result, although a simple
counting formula appears available. This is the paper version's
open-status attestation, not worldwide certification. The nearby
computation-through-size-22 statement concerns Conjectures 6.1 and 6.2;
it is not adopted as evidence for Conjecture 6.3.

The supplied bounded prior-answer screen inspected returned arXiv
metadata for exact Latin tableau/tableaux phrases and selected passages
in 2007.13835v3, math/0205288v2, 2408.04086v1 and 2511.10548v1. No
complete answer to this exact universal count was located in that
inspected scope. Unindexed literature, equivalent earlier theorems,
post-v1 answers and global priority remain unverified. A complete prior
answer must be reused with zero new solution credit.

[Issue 20269](https://github.com/the-omega-institute/trureturing/issues/20269)
registers the complete source assertion. The mathematical content
is in `Latin/Tableaux/Source`, `MatchingTemplate`, and `Counting` under
`D5/S3/Combinatorics`, with corresponding owning Blueprint Scribes.
`Counting.conjecture63_integer` proves the entire integer-parametrized
count for the literal unrestricted integer-filling definition.
The [canonical problem dossier](../../Problems/daugherty-latin-tableaux-conjecture63.md)
explains the exact source correspondence, kernel-checked complete base,
all-parameter invariant and proof boundaries. The source finiteness and
finite enumeration are connected by explicit inverse maps, without a
symmetry quotient. The ordinary counting argument and its independent
source audit are admitted inputs; the Lean proof supplies distinct
kernel evidence.

The proof begins at (5,4,3,3); the smaller (4,3,3) layer cannot support
a uniform fourfold step. The four-choice invariant, rather than finite
experimental evidence, supplies every subsequent transition. This
note makes no CI, integration, publication or solved-problem credit claim. Current per-theorem audit evidence
and any linked gaps must be reported separately. The bounded prior-art
qualification above does not establish worldwide priority.
