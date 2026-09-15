---
bibkey: shin2026iterated
authors: Henry Shin
year: 2026
title: "Iterated-sumset spectra: The complete exponent law and its rank geometry"
doi: 10.48550/arXiv.2609.01690
claim: The question following Corollary 10.5 asks whether every four-point sumset cardinality is realizable at the minimum diameter of a maximal-cardinality model.
strata_touched:
  - D5/S0/Certificates/ShinFourPointCompression
license: citation-only
triage: anchor
---

# Four-point sumset compression

## Verified locator

DOI: https://doi.org/10.48550/arXiv.2609.01690

The pinned source is https://arxiv.org/html/2609.01690v1. Immediately before
Corollary 10.5 it defines nu(h,4) as the least D for which all cardinalities
of h-fold sumsets of four distinct integers occur in [0,D]. Corollary 10.5,
equation (193), proves lower and upper bounds. The unnumbered paragraph after
its proof, before Proposition 10.6, asks whether nu(h,4)=D_h^max for every
h>=2. Here D_h^max=choose(h+2,2)+1 for odd h and choose(h+2,2) otherwise.
The operation hA allows repetition and uses exactly h summands. This is an
explicit question, without attributing an affirmative conjecture to Shin.

The source HTML read on 2026-09-13 has SHA-256
453e39bc6fc2773e50582eed117b46986f75341010fea1abc1db3a18bd506d60.
The official abstract/version page https://arxiv.org/abs/2609.01690 listed
only v1 in the same day's check. A fresh public fetch of the pinned HTML
returned HTTP 200. Only bibliographic information and the short question
are paraphrased here; no source-paper text or code is redistributed.

## Mathematical scope

The affirmative claim quantifies over every natural h>=2 and every finite
four-element subset A of the integers. It asks for a four-element integer
set B in the closed interval [0,D_h^max] with |hB|=|hA|. No additive-type,
gcd, primitivity, reflection, or ordering requirement is imposed on A or B.
The proposed negative instance is h=11, A={0,7,17,80}: |11A|=347, and that
cardinality is absent from all four-element subsets of [0,79]. The Lean
result consumes the full finite exclusion after translation normalization.
It makes no assertion that nu(11,4)=80.

## Bounded duplicate and literature search

At repository base e6ad855ec601b2195efc5abdf307ab282b31fd4d, searches of
D5, Library, Problems and Blueprint for `2609.01690`, `2609.08915`,
`iterated.?sumset`, and `sumset` found no matching compression result.
The sumset mention in GreedyThreeSumfreeTwoParameter concerns a different
three-sumfree construction. Pinned mathlib revision
db584cd6d46c92f209a44c0f1c829460d327499d has no matching compression theorem.
Its repeated-pointwise-addition, finite ordering, translation-cardinality,
binary-index, and bitwise lemmas are used directly in the proof.

The 2026-09-13 GitHub issue/PR searches for either paper ID within
trureturing returned zero. The global 2609.08915 issue search found one
arXiv feed issue. Formal Conjectures was checked at
a2f4a1bb12a28e04a969da78feefac7d1ce49565; the exact 2609.01690 code query
returned zero, and a fresh worker GitHub query returned total_count=0 with
incomplete_results=false. Public arXiv queries `sumset spectra` and
`sumset compression`, ordered newest first with size 50, included the Shin
paper as a positive control and found no newer matching solution.
These observations do not establish exhaustive publication priority.

## Related source and limits

Zhang's https://arxiv.org/html/2609.08915v1#S12.Thmtheorem5,
Question 12.5, independently calls the same label-level question open and
states that its weak-type theorem does not answer it. The source is
catalogued as zhang2026sharp. Current source status, source-to-Lean fidelity,
and absence of prior solutions are literature/review obligations, not
consequences of a kernel axiom check. Independent review, canonical
admission, freezing and delivery are separate from the local proof.
