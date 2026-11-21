---
bibkey: mazhang2026wangcounterexamples
authors: Haobo Ma; Wenlin Zhang
year: 2026
title: Counterexamples to Wang's Conjectures 3.26 and 5.3 on semigroup algebras
doi: 10.5281/zenodo.23884901
claim: Lemma 4 computes every relative Davenport constant of the capped union monoid P_fin(U) x {0,1,2} as D_(A,k)(S_U)=|A|+k.
strata_touched:
  - D5/S0/Certificates/Algebra/CappedUnionDavenport
license: CC-BY-4.0
triage: anchor
---

# Counterexamples to Wang's conjectures on semigroup algebras

## Verified locator

- DOI: https://doi.org/10.5281/zenodo.23884901
- URL: https://zenodo.org/records/23884901

Haobo Ma and Wenlin Zhang, *Counterexamples to Wang's Conjectures 3.26 and 5.3
on semigroup algebras*, version 2, Zenodo preprint, file `note-v2.pdf`.

## Source interpretation

For a set U the note puts S_U = P_fin(U) x {0,1,2} with
(A,i)+(B,j)=(A u B, min{2,i+j}), and defines the relative constant D_a(S) as
the supremum of lengths of sequences with sum a having no proper subsequence
with the same sum; in a monoid the empty sequence has sum 0 and is allowed as
a subsequence. Lemma 4 states that D_(A,k)(S_U)=|A|+k for every finite A in U
and k in {0,1,2}. Its proof takes k copies of (empty,1) with one singleton
({a},0) for each a in A, and bounds an irreducible sequence by marking at most
k level-carrying terms and injecting the unmarked terms into exclusive support
points of A. The note attributes relative constants to G. Wang, J. Combin.
Theory Ser. A 152 (2017), 380-397, doi:10.1016/j.jcta.2017.07.001, and
refutes Conjectures 3.26 and 5.3 of G. Wang, arXiv:2509.18724v1.

The repository formalization indexes sequences by Fin n and proper
subsequences by proper index subsets, and states the constant as the greatest
element of the set of lengths of such minimal sequences. Its upper bound uses
single deletions: a term whose deletion keeps the capped level must be the only
carrier of some point of A.
