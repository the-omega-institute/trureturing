---
slug: biswas-shankar-sivasubramanian-p1-matchings
bibkey: biswas2026matchingtriples
doi: 10.48550/arXiv.2609.08562
url: https://arxiv.org/abs/2609.08562v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings.result
  - D5/S3/Combinatorics/PatternMatchings/P13Correspondence.matchingEquiv
  - D5/S3/Combinatorics/PatternMatchings/P13Counts.c_triangular
  - D5/S3/Combinatorics/PatternMatchings/P13Enumeration.result
---

# Generating Function of Perfect Matchings Avoiding {123, 132, 213}

## Problem

Sucharita Biswas, Umesh Shankar and Sivaramakrishnan Sivasubramanian, *Matchings and shape-Wilf-Equivalence of sets
of patterns of length three I: Triples*, arXiv:2609.08562v1, Section 6, Question 1: "Can we enumerate the matchings
that avoid the set of patterns P1 = {123, 132, 213} and P13 = {132, 213, 321}?" Matching patterns follow Section 4
and Figure 1: three arcs form an occurrence only when all three left endpoints precede all three right endpoints, and
the label records the complement of the order of the right endpoints. This dossier settles the P1 clause and records
an all-size structural scan bridge, finite continuation recurrence and exact all-size enumeration for the P13 clause.
The P13 result concerns the original ordinary matching carrier, including empty and disconnected matchings.

## Motivation

The theorem `D5/S3/Combinatorics/PatternMatchings/TripleAvoidingMatchings.result` proves that the number a_n of
perfect matchings of [2n] avoiding P1 satisfies Σ a_n z^n = (1 − zH(z)) / (1 − z − zH(z)) with
H(z) = Σ_{k≥0} Cat_k F_{k+3} z^k, equivalently a_0 = 1 and a_{n+1} = a_n + Σ_{k<n} Cat_k F_{k+3} a_{n−k}.

For P13, `D5/S3/Combinatorics/PatternMatchings/P13Correspondence.matchingEquiv` proves a bijection between the
actual source avoiders and independently accepted normalized general-rank scans, for every n ≥ 0. This is a
structural construction consumed by the all-size enumeration. The merged modules
`D5/S3/Combinatorics/PatternMatchings/P13Completions` and `P13Counts` add a finite completion carrier, the
forced-prefix and first-closure bijections, the triangular recurrence `P13Counts.c_triangular`, and the transfer
law `P13Counts.actualCount_continuation` for the actual matching counts.

The all-size composition uses the actual catalytic transform of the literal completion series. Its extracted
boundary at degree two retains $X(1-X)h_0$. The proved actual bulk recurrence discharges the scalar minimality
premise, and the boundary elimination proves `P13Enumeration.actual_A_eq_G`. Put $\delta=(1-X)^2$,
$P=\Phi_1$, $R=\Phi_2$, $D=\delta(1-2X-X^2)P-X^3(1+X)R$, and $G=1+X(1-X)^3PD^{-1}$.
The $\Phi_j$ have the explicit finite coefficient definition in the
[existing BSS Library note](../Library/PermutationPatterns/biswas2026matchingtriples.md); every inverse is a
proved formal unit inverse. With $C$ the rational Catalan series, the actual ordinary series is $G(C-1)$ and

$$
a_0=1,\qquad \forall n\ge1,\quad(a_n:\mathbb Q)=[X^n](1-X)(1+X)^{2n-1}G(X).
$$

No recurrence, H, Bulk, tail, connectedness or equality-to-G premise remains in the final statement.

## Gap

Pre-registration issue 13176 records the literature screen: the authors state that the P1 and P13 classes were the
only triples not enumerated, the follow-up paper arXiv:2610.01996v1 on quadruples and quintuples does not treat them,
and the sequence 1, 3, 12, 55, 271, 1400, 7471, 40841 has no entry in the OEIS.

## Route

1. Scanning the 2n positions from left to right, a P1-avoiding matching can only close the oldest or the second-oldest
   open arc; closing a third-oldest or newer arc creates the forbidden closing order 312 or 321.
2. After the second-oldest arc closes while at least three arcs are open, the next closure must be the oldest arc,
   otherwise the order 231 appears; with exactly two open arcs there is no constraint. Conversely every scan obeying
   these rules avoids P1.
3. These rules define an automaton on states N_h and F_h, and P1-avoiding matchings are in bijection with its accepted
   words of length 2n.
4. Above height two the down-steps act by D = ((1,1),(1,0)), so a Dyck excursion with k down-steps contributes
   Cat_k shapes weighted by e_Nᵀ D^k (2,1)ᵀ = F_{k+3}; the height-one and root decompositions give the formula.

For the P13 structural bridge, a closure compares all current survivors. A post-closure base is one decreasing
block S(m), or two nonempty consecutive decreasing blocks T(a,b), with the older block first. New openings
increase a separate pending count k. The displayed source rank i is one-based; the implemented rank r is i−1.
From S(m), m>0 requires m≤i≤m+k, while S(0) permits 1≤i≤k. The new block sizes are i−1 and m+k−i, with zero
blocks removed. From T(a,b), the only legal closure has i=a; it gives T(a−1,b+k) when a>1 and S(b+k) when a=1.
The construction preserves every earlier survivor comparison. Full endpoint coverage gives a fixed-point-free
involution, and encoding and decoding are inverse on the actual matching and scan carriers. The scans may return
to zero between components.

## Falsifier

The formula would fail if some n gave a different number of P1-avoiding matchings; it agrees with the paper's table
through n = 8 and with exhaustive enumeration through n = 9.

For the P13 structural bridge, an actual source avoider with a rejected full scan, an accepted scan decoding to a
source occurrence, or a failure of either total inverse law would refute the stated construction.

## Evidence

The proof seat and an independent referee implementation enumerated all perfect matchings of [2n] for n ≤ 9 and
compared the counts with the formula and with the paper's tables for all twenty triple classes.

The P13 structural equivalence, its arbitrary-size survivor normalization and endpoint decoder have compiled
Lean proofs. Exact kernel checks include the empty scan, both first-closure ranks after two openings, disconnected
scans, and the P13 avoider (1,4),(2,8),(3,7),(5,6). For this last matching the pending opener 5 closes before the old
survivors 3 and 2; appending it to their prescribed chronological order would give the wrong order. A separate
exact finite diagnostic compares the local scan rules, both inverse algorithms and the source convention on every
matching through n=5. The source 321 crossing (1,4),(2,5),(3,6) is rejected, whereas source 123 nesting
(1,6),(2,5),(3,4) is accepted. Finite diagnostics do not establish enumeration. The separate all-size Lean proof is
`D5/S3/Combinatorics/PatternMatchings/P13Enumeration.lean`,
`D5.S3.Combinatorics.PatternMatchings.P13.result`. It recovers the actual series by lawful zero-constant
Catalan substitution and consumes the original public Lagrange supplier, which also remains live in
`NonnestingOneThreeTwoTwo.result`. The coefficient formula is unconditional for every n≥1; the empty
count is proved separately as one. Local compilation and axiom evidence are reported with the candidate
seal; required CI for the separate F delivery remains pending. This candidate is not frozen or submitted.

## Triage

`theorem`; the enumeration statement is the P1 clause of Question 1 of arXiv:2609.08562v1. The P13 structural
construction and continuation recurrence are consumed by the exact P13 all-size enumeration.

- Proved (formalized): the generating function of P1-avoiding perfect matchings is (1 − zH)/(1 − z − zH).
- Computed: the P13 counts 1, 3, 12, 54, 258, 1276, 6449 agree with the paper.
- Proved (formalized, structural bridge only): for every n ≥ 0, P13-avoiding actual matchings are in bijection with
  independently accepted normalized general-rank scans, including empty and disconnected cases.
- Proved (formalized, recurrence slice): finite P13 continuation counts admit forced-prefix and first-closure
  decompositions and the triangular recurrence `P13Counts.c_triangular`; the actual matching carrier satisfies
  `P13Counts.actualCount_continuation`.
- Proved (formalized, all-size candidate): the actual P13 series is G(Catalan−1), with empty count one
  and the displayed coefficient formula for every n≥1. Scientific local proof status does not assert
  required CI success, official acceptance, worldwide novelty, unique credit or full-Question-1 resolution.

## ASSUMED-UNVERIFIED

The literature screen is limited to the arXiv records of arXiv:2609.08562 and arXiv:2610.01996, the OEIS, web and
GitHub searches and the repository checks; the full text of Hessas, Goubi and Benkhemmou (IJMOR 32(3), 2025) was not
available.

The structural bridge carries no claim of worldwide novelty, exclusive ownership, official acceptance or unique
credit. An equivalent supplier in the unread Hessas full text is not excluded. Information-escape registration is
unfinished under the current suspension of registration authoring; no registration completion is asserted.
