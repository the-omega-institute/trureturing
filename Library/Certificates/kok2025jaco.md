---
bibkey: kok2025jaco
authors: Johan Kok
year: 2025
title: Integer sequences with conjectured relation with certain graph parameters of the family of linear Jaco graphs
doi: 10.48550/arXiv.2507.16500
claim: Conjecture 2.2 identifies maximum degrees with the golden floor and literal A319433 deletion; Conjecture 2.9 bounds a primary minimal dom-path by the graph diameter plus one, while Conjecture 2.12 says that A000149 indexes a gamma-set of J_infinity(x) and is p-graphical for the finite J_n(x).
strata_touched:
  - D5/S0/Certificates/JacoExponentialDominationRefutation
  - D5/S3/ConceptDynamics/GraphColoring/JacoDomPathDiameterRefutation
  - D5/S3/ConceptDynamics/GraphColoring/JacoEndpointBeatty
  - D5/S3/ConceptDynamics/GraphColoring/JacoMaximumDegree
license: citation-only
triage: anchor
---

# Integer sequences and linear Jaco graph parameters

Version 1 of the preprint was submitted on 22 July 2025. Section 2.3,
Conjecture 2.12, on printed page 9 states these two clauses verbatim:

> The vertex subscripts of a γ-set X = ”{v1 }” ∪ {v2 , v7 , v20 , v54 , . . . } of the infinite linear Jaco graph J∞ (x) is given by the sequence A000149: a(t) = ⌊e^t⌋, t = 0, 1, 2, . . . where e ≈ 2.71828 is the Euler number (or Napier’s constant).

> Furthermore, it implies that sequence A000149 is p-graphical where p(G) = {i : j the subscript of vj ∈ X with X some γ-set of G} and F = {G : G = Jn(x), n = 1, 2, 3, . . . }.

The first clause identifies A000149 with a gamma-set, hence with a minimum
dominating set. The formal target retains only its necessary domination
assertion. It does not encode gamma-set minimality or the second, p-graphical
clause. Refuting the necessary assertion refutes the gamma-set assertion, not
the conjecture's separate p-graphical clause.

## Dom-path diameter conjecture

Observation 2.7 on printed pages 6--7 states verbatim:

> For any finite linear Jaco graph Jn (x), n ≥ 2 there exists a pair of
> vertices i.e. v1 , vn for which a minimal (v1 , vn )-path (not necessarily a
> diam-path) i.e. Pd (Jn (x)) exists such that a γ-set of Pd (Jn (x)) is a
> γ-set of Jn (x). We call the path Pd (Jn (x)) the primary minimal dom-path.

Conjecture 2.9 on printed page 7 states verbatim:

> For any linear Jaco graph Jn (x), n ≥ 1 the length of a diam-path and a
> primary minimal dom-path Pd satisfy |Pd | − |diam(Jn (x))| ≤ 1.

The paper measures path length in edges: its six-vertex path for `J_8(x)` is
said to have length 5. The formal assertion uses the weakest consequence of
the conjecture, namely that at least one dom-path has length at most the graph
diameter plus one. The finite graph at `n = 33` refutes even this consequence:
its diameter is 7, its domination number is 4, and every dom-path has at least
10 vertices. The path with vertices `1,2,3,4,7,11,12,20,32,33` and shared
gamma-set `{2,7,20,33}` shows that the dom-path predicate is inhabited.

The arXiv API and searches for `"Jaco" "Conjecture 2.9"`,
`"Jaco" "dom-path"`, `"linear Jaco graphs" conjecture proof`, and
`"linear Jaco graphs" 33 domination` were checked on 2026-09-18. No proof,
refutation, correction, later arXiv version, journal reference, or DOI beyond
the arXiv DOI was found in those checked surfaces. Semantic Scholar returned
HTTP 429, Google Scholar was not checked, and the full text of Kok's cited
domination research note was not available; this is therefore a bounded
literature report rather than an exhaustive priority claim.

The arXiv version history, the current OEIS A000149 entry, and the following
searches were checked on 2026-09-12: `"2507.16500" proof`,
`"Integer sequences with conjectured relation"`, `"Jaco graphs" "Euler"`,
`"Jaco" "Conjecture 2.12"`, `"Jaco" "2.12" "counterexample"`, and
`"Jaco graphs" "domination" "2026"`. A proof or refutation was not found in
the checked surfaces. The paper's conclusion leaves its conjectures for future
work. Kok's earlier *Research note: Domination of exact deg-centric Jaco graphs*
provides background but does not settle this domination assertion. This is a
bounded search report; no claim of exhaustive coverage or priority is made.

## Verified locator

- DOI: https://doi.org/10.48550/arXiv.2507.16500
- Preprint: https://arxiv.org/abs/2507.16500
- Version and scope: https://arxiv.org/pdf/2507.16500v1, section 2.3,
  Observation 2.7 and Conjecture 2.9 on printed pages 6--7, and Conjecture
  2.12 on printed page 9.
- Sequence: https://oeis.org/A000149

## Maximum degree and canonical digit deletion

The verified source locator for the resolved question is [Conjecture 2.2,
section 2.2](https://arxiv.org/html/2507.16500v1#S2.Thmtheorem2) of Johan
Kok's version 1 preprint. The sequence attribution is the Online Encyclopedia
of Integer Sequences entries [A319433](https://oeis.org/A319433) and
[A014417](https://oeis.org/A014417), including their offset-zero and
Zeckendorf conventions.

Section 2.2, Conjecture 2.2 of arXiv:2507.16500v1 states:

> For the finite linear Jaco graphs J_n(x), n=2,3,4,... the respective maximum degrees Delta(J_n(x)) are yielded by the sequence A319433 with closed formula Delta(J_n(x))=floor(2(n+2)/(1+sqrt(5)))-1, n=2,3,4,...
>
> Furthermore, it implies that sequence A319433 is p-graphical where p(G)=Delta(G) and F={G:G=J_n(x),n=1,2,3,...}.

The graphs are the underlying simple undirected graphs. For positive indices,
the recursive indegree at i counts earlier j whose right endpoint reaches i,
and the endpoint is 2i minus that count. The family retains the singleton at
n=1. Pair graph order n with actual sequence index n; the sequence's offset-zero
entry is not reassigned to the singleton.

The Online Encyclopedia of Integer Sequences, [A319433](https://oeis.org/A319433)
and [A014417](https://oeis.org/A014417), defines the sequence by deleting the
least significant position from the canonical Zeckendorf word and decoding the
remaining word in the same Fibonacci positional system. Occupied weights start
at F_2=1 and F_3=2. In the occupied-index representation this removes index 2,
then replaces every surviving index j by j-1. In particular the removed digit
does not contribute F_1. The sequence has a(0)=a(1)=0.

Source attribution: Johan Kok, DOI 10.48550/arXiv.2507.16500, and The Online
Encyclopedia of Integer Sequences. The article and OEIS content are licensed
under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/); the
plain-text mathematical transcription above adapts their notation.

The bounded source comparison includes arXiv:1404.0484v1,
arXiv:1404.1714v1, and arXiv:1506.06538v1. Bettina's theorem in those sources
concerns infinite outdegrees and is prior mathematical content, not an axiom
for the Lean graph. No exact Lean maximum-degree or A319433 supplier was found
in the bounded repository, pinned Mathlib, and third-party searches. This is
not a claim of worldwide openness or priority.
