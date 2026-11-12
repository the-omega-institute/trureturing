---
slug: bks11-14325-whole-event
bibkey: blitvickammounsteingrimsson2026patterns
doi: 10.48550/arXiv.2610.29846
url: https://arxiv.org/abs/2610.29846v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.result
---

# The complete 14325 overlap-two modular event

## Problem

Blitvić, Kammoun and Steingrímsson, arXiv:2610.29846v1, Section 7 item 11:

> A curiosity in the enumeration for 14325 with overlap 2 is that all the
> numbers are congruent to 6 mod 10, except when $j=2^k-1$, those are
> congruent to 1.

> Another apparent regularity in this is that 4 seems to divide all but
> those for which $j=2^i+2^p-1$ where $0\le p\le i$, such as 8,9,11,15.

For each natural $j\ge1$, $A(j)$ counts actual permutations of $[3j+2]$
whose length-five windows at $1+3t$, for every $0\le t<j$, match every
strict pairwise comparison of 14325. Extra occurrences are allowed;
there is no avoidance requirement, quotient or assumed recurrence.
The complete registered event is

$$
A(j)\bmod10=\begin{cases}1&\exists k\ge1,\ j+1=2^k,\\6&\text{otherwise},\end{cases}
\qquad
4\nmid A(j)\ \Longleftrightarrow\
\exists i,p\in\mathbb N,\ p\le i\ \land\ j+1=2^i+2^p.
$$

The cases $p=0$ and $p=i$ are included; no assertion is made at $j=0$.
The printed all-but wording does not explicitly assert the converse.
The displayed iff is the stronger exact-exception interpretation in
[the full preregistration](https://github.com/the-omega-institute/trureturing/issues/28504#issuecomment-6743850080).
The separate modulo-ten-only proposal in
[21304](https://github.com/the-omega-institute/trureturing/issues/21304)
remains unresolved under its own criteria and is not counted again.

## Motivation

The existing literal packing predicate and cardinality in
`PackingMaximumRefutation` provide the source domain. Its frozen result
concerns a different maximum claim; it does not imply either modular law.
This event asks for both laws for that same unbounded permutation family.

## Gap

The two exact actual-count conclusions are present as
`BlitvicKammounSteingrimsson14325Core.count_mod_ten` and
`BlitvicKammounSteingrimsson14325Core.count_mod_four_iff`.
Their joint resolution claim names both members. They have no frozen
membership; current resolution-source validation therefore remains an
obligation, alongside independent current-tree admission and prefreeze
judgment. Source correspondence alone supplies none of those judgments.

## Route

The Core module translates every prescribed window into
$a_t<a_{t+1}<c_t<b_t<b_{t+1}$, forces the two endpoint ranks, and removes
them by an actual permutation bijection. A second insertion/deletion
bijection on the endpoint-deleted grid derives its cardinality as
`row ℕ (j-1) 3`. No recurrence for the original count is assumed.
The Transfer module proves the modulo-five invariant and the modulo-four
Catalan-series identity. Binary Catalan parity and valuation formulas
give the exact dyadic and two-power exception sets. Composing those
universal laws with the two bijections gives both source conclusions.

## Falsifier

An omitted window comparison, a nonbijective deletion/insertion map,
a labeling factor, an index shift at $j=1$, or loss of either $p=0$ or
$p=i$ would invalidate the correspondence. The source statements retain
these boundaries. A successful selected compilation verifies the Lean
statements and proof terms, not their fidelity to the printed problem.

## Evidence

The mathematical sources are the Core and Transfer modules, with six
and five public theorem statements respectively. Their matching
Blueprint Scribes describe all eleven statements. All are universal
structural results rather than bounded enumeration, certified instances,
checkers or numeric reductions: `utility: none` is the proposed
classification for every declaration, subject to independent review.
The proposed admission basis is `escape-witness`; the live source
candidates include Core `chain_bounds`, `child_bijective` and Transfer
`row_eq_oddSeries`. The whole-event typed claim records the two exact
conclusions without adding a mathematical packaging theorem.

The eight existing successful Reg audits are retained. The three
actual-count audits for `count_eq_grid`, `count_mod_ten` and
`count_mod_four_iff` are unfinished with `IE-C050ClosedTruthReadout`,
`unclassified_form`, `source.state_or_output` and null certificate;
they are not `declared_validated`. The existing
[linked-issue disclosure](https://github.com/the-omega-institute/trureturing/issues/28504#issuecomment-6748745703)
states that boundary. No unchanged audit retry is required here.

## Triage

**Source-derived:** endpoint deletion and grid insertion supply an actual
count recurrence, rather than evidence obtained by extrapolating a finite
table. **Source-derived:** the same recurrence links modulo-five
stabilization and the modulo-four Catalan identity to one common
permutation family, allowing their residue consequences to combine.
**Unverified here:** independent reduced proof-path, utility and admission
judgments and the canonical first-freeze gates. **Open:** extensions to
other patterns or overlap lengths; no such extension follows merely from
the numerical resemblance. No finite experiments or new mathematical
claims are part of this package.

## ASSUMED-UNVERIFIED

Literature completeness and worldwide priority are `ASSUMED-UNVERIFIED`.
The primary source and bounded literature assessment belong to the
existing Library note and preregistration; this package adds no fresh
literature-search or novelty claim. The supplied independent source
classification is fallible source evidence and is not current compiled
or admission approval. The two conclusion members are unfrozen, so the
typed Proved claim is proposed content and not a validated resolution or
a problem settlement.
