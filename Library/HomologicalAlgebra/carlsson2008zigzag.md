---
bibkey: carlsson2008zigzag
authors: "Gunnar Carlsson and Vin de Silva"
year: 2008
title: "Zigzag Persistence"
doi: null
url: https://arxiv.org/abs/0812.0197v1
claim: "Right filtrations reconstruct endomorphisms of right-streamlined zigzag modules; finite type-A zigzags admit interval decomposition."
strata_touched:
  - D5/S3/HomologicalAlgebra/Persistence/ZigzagNaturalLift
license: citation-only
triage: anchor
---

# Zigzag persistence

The versioned source is Carlsson and de Silva, *Zigzag Persistence*, arXiv:0812.0197v1. PDF page numbers below count pages from the first PDF page. The PDF SHA-256 is `e6548c911805dc337d6c3c9426ee639d6e950e429e245005ee520fa44899d9a4`.

## Verified locator

Versioned URL: https://arxiv.org/abs/0812.0197v1.

Definition 3.1, PDF page 10, defines the right filtration recursively. A length-one module has filtration $(0,V_1)$. Appending a forward map $f$ sends the old layers through $f$ and appends the new whole space. Appending a backward map $g$ prepends zero and takes the inverse images of the old layers.

Definition 3.15, PDF page 15, calls a zigzag right-streamlined when every forward arrow is injective and every backward arrow is surjective. The remark following the proof of Lemma 3.18, PDF pages 16–17, states that terminal evaluation induces an isomorphism $\operatorname{End}(V)\to\operatorname{End}(R(V))$ for streamlined modules. This is the source for unique reconstruction of a natural endomorphism from a filtration-preserving terminal endomorphism. It is distinct from the decomposition statement of Lemma 3.18 on PDF page 15.

Theorem 4.1, PDF page 17, gives interval decomposition and the multiplicities using prefix right filtrations. Lemma 4.3, PDF page 18, explicitly says **irreducible** $\tau$-module. Its printed statement is cited with that qualifier; it is not an unrestricted prefix-splitting supplier. Any unrestricted splitting used in a construction requires its own argument.

For the type-A representation context, Claus Michael Ringel, *The representations of quivers of type A_n. A fast approach*, page 1, states that a representation of a quiver of type $A_n$ is a direct sum of thin representations. The verified `a_n.pdf` SHA-256 is `867c7fe03b9b34ba02a7e498cd97ae3509dca5a3c73a839fedb9b5129c1864f9`. This reference supplies context, not an assumed natural reconstruction.

These are known mathematical results over fields, allowing zero spaces and repeated interval occurrences. No originality or resolution of an external open question is asserted. The status of a nearest related open question is UNKNOWN.
