---
bibkey: mazhang2026symmetrizationnegative
authors: "Haobo Ma; Wenlin Zhang"
year: 2026
title: "A negative answer to Delgado, Süer and Yeşil's symmetrization question"
doi: "10.5281/zenodo.24391331"
url: "https://doi.org/10.5281/zenodo.24391331"
claim: "Corollary 2: for h >= 2 there are 2^(h-1) symmetric numerical sets with Frobenius number 2h-1, and at least 2^(h-2) of them lie outside the image of Phi. Corollary 3: every proper symmetric numerical semigroup S is almost symmetric and satisfies Phi(S) = S; conversely, among proper numerical semigroups these are exactly the fixed points of the extended row-deletion map. Corollary 4: Phi(S) = N0 minus {1} exactly for the ordinary semigroups O_m, m >= 2, each almost symmetric."
strata_touched:
  - D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiFixedPoints
  - D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiOrdinaryFiber
  - D5/S3/Combinatorics/Partitions/DelgadoSuerYesilPhiSymmetricTargets
license: CC BY 4.0
triage: anchor
---
<!-- GID: D5/L/FiniteGeometry/mazhang2026symmetrizationnegative -->
# Fixed points of pseudo-Frobenius row deletion

## Verified locator

The written proof is by **Haobo Ma and Wenlin Zhang**, version 2, exact-version DOI
https://doi.org/10.5281/zenodo.24391331, Corollaries 2, 3 and 4. The map Phi is the row deletion of
M. Delgado, M. Süer and M. Yeşil, arXiv:2611.14268v1, Theorem 4.2, recorded in
delgadosueryesil2026symmetrization.

## Statement

For a proper numerical semigroup S with Frobenius number F(S), genus g(S) and pseudo-Frobenius
set PF(S), Phi deletes the rows of PF(S) other than F(S). Corollary 3: every proper symmetric
numerical semigroup is almost symmetric and satisfies Phi(S) = S, and conversely the proper
numerical semigroups with Phi(S) = S are exactly the symmetric ones. The proof shows that S is
symmetric exactly when PF(S) = {F(S)}: a gap a lies below the largest gap of (a + S) ∩ G(S),
which is pseudo-Frobenius. The characterization of symmetric numerical semigroups as those of
type one is classical; the fixed-point statement for Phi is the note's.

Corollary 4: write U_1 = N0 minus {1} and O_m = {0} union {n : n >= m}. For every proper
numerical semigroup S, Phi(S) = U_1 if and only if S = O_m for some m >= 2, and every O_m is
almost symmetric; the fiber of the original map over U_1 has exactly one source at each positive
Frobenius number F, namely O_{F+1}.

Corollary 2: for every h >= 2 there are exactly 2^(h-1) symmetric numerical sets with Frobenius
number 2h - 1, one for each choice of members among the pairs {a, 2h - 1 - a}, 1 <= a <= h - 1;
the 2^(h-2) choices containing 1 lie outside the image of Phi, because Phi(S) never contains 1.
No symmetric numerical set has even Frobenius number, and at Frobenius number 1 the sole target
N0 minus {1} is reached. The total count is due to J. Marzuola and A. Miller,
arXiv:0805.3493v1, p. 12.
