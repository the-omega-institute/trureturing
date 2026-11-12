# Cyclic closure

## Abstract

Six-site cyclic closure for the exact Mertens range-two proof.

A word w of length m has a signed assignment d and Certificate(w,d). The source cycle has m+6 labelled sites, hence supplier parameter n=m+1. Assignment(m) means Fin(m) to the integers. SuccessfulProfile(n) is the subtype of SourceModel.Profile(n) admitting an acceptable stable partial matching. The matching keeps every interior old pair and old single, fulfills each actual exterior request, and uses the existing six-site buffer involution for free sites. The profile retains all first m rankings and places every nonzero buffer partner first.

**Definition 1.1 (Actual involutive source matching).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \mathrm{Word}\left(m\right),\; \forall d \in \mathrm{Assignment}\left(m\right),\; \forall h \in \mathrm{Certificate}\left(w, d\right),\; \mathrm{HasType}\left(\mathrm{matching}\left(h\right), \mathrm{Matching}\left(\mathrm{Fin}\left(m + 6\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.matching` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sum of the old interval and the six buffer vertices is identified with the labelled source cycle. Interior reciprocity is supplied by the certificate; the existing request involution supplies all exterior and new pairs. Fixed points represent singles.

**Definition 1.2 (The extended profile).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \mathrm{Word}\left(m\right),\; \forall d \in \mathrm{Assignment}\left(m\right),\; \forall h \in \mathrm{Certificate}\left(w, d\right),\; \mathrm{HasType}\left(\mathrm{profile}\left(h\right), \mathrm{Profile}\left(m + 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.profile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Every old ranking is retained literally. A buffer ranking is the existing partnerFirst permutation for its actual signed assignment, including the fixed deterministic ranking at a single.

**Theorem 1.3 (Acceptable pairs and singles).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \mathrm{Word}\left(m\right),\; \forall d \in \mathrm{Assignment}\left(m\right),\; \forall h \in \mathrm{Certificate}\left(w, d\right),\; \mathrm{IsAcceptable}\left(\mathrm{ring}\left(m + 1\right), \mathrm{matching}\left(h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.acceptable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Each assignment is zero or one of the four literal signed source offsets. Thus every nonfixed pair is an actual acceptable edge of the source ring.

**Theorem 1.4 (No cyclic blocking edge).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \mathrm{Word}\left(m\right),\; \forall d \in \mathrm{Assignment}\left(m\right),\; \forall h \in \mathrm{Certificate}\left(w, d\right),\; \mathrm{IsStable}\left(\mathrm{ring}\left(m + 1\right), \mathrm{rank}\left(\mathrm{profile}\left(h\right)\right), \mathrm{matching}\left(h\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Old--old edges use the saved exact rank transport and have no new wrap edge. A matched buffer endpoint ranks its partner first and rejects any proposed improvement. A buffer single is at position 3 or 4 in one-based numbering; all four cyclic neighbors are distinct matched buffer vertices. This also excludes an edge from an old single to a new single. The argument includes m=1 and its extra edge between buffer positions 1 and 6, m=2, and odd m. There is no parity or eventual-length hypothesis.

**Definition 1.5 (Map on successful profiles).**

$$\forall m \in \mathrm{Nat},\; \forall w \in \mathrm{CertifiedWord}\left(m\right),\; \mathrm{HasType}\left(\mathrm{close}\left(w\right), \mathrm{SuccessfulProfile}\left(m + 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Choose one certificate per certified word, construct its profile and stable matching, and retain only the successful profile. Certificates and matching witnesses are not counted.

**Theorem 1.6 (Recover the old ranking word).**

$$\forall m \in \mathrm{Nat},\; \mathrm{Injective}\left(\mathrm{close}\left(m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Equality of output profiles gives equality at each first-m coordinate, recovering the input word independently of which certificate was chosen.

**Theorem 1.7 (The lower cyclic count comparison).**

$$\forall m \in \mathrm{Nat},\; \mathrm{count}\left(m\right) \le \mathrm{card}\left(\mathrm{SuccessfulProfile}\left(m + 1\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.count_le_successful_profile_count` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Write b(m) for the number of certified ranking words, and a(n) for the number of successful labelled source profiles with supplier parameter n and n+5 sites. The injection proves b(m) <= a(m+1), equivalently b(m) <= a_(m+6) when the subscript records sites. GrowthTransfer.result consumes this bridge for the exact d=1,r=2 probability theorem. General Conjecture 3 remains outside this scope.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.acceptable`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.close_injective`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.count_le_successful_profile_count`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.matching`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.profile`
- Truth anchor: `D5/S3/Combinatorics/Graph/Roommates/CyclicClosure.stable`
- Dependency: [D5/S3/Combinatorics/Graph/Roommates/CyclicBridge](CyclicBridge.md)
