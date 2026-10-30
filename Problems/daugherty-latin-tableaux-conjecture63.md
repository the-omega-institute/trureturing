---
slug: daugherty-latin-tableaux-conjecture63
bibkey: daugherty2026counting
doi: null
url: https://arxiv.org/abs/2610.29291v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Latin/Tableaux/MatchingTemplate.full_transition
---

# Daugherty et al., Latin tableaux Conjecture 6.3

## Problem

For every integer k at least five, let lambda=(k,k-1,...,5,4,3,3).
Conjecture 6.3 of arXiv:2610.29291v1 states LT(lambda)=9*4^(k-3).
The source count is the number of all fillings of the fixed left-aligned
cells by actual integer symbols, with no repetition in any row or column,
and type lambda-prime. It is not the reduced count. Both bottom rows
remain distinct positions. There is no upper cutoff or additional
wide-partition hypothesis.

The exact Lean statement is `Counting.conjecture63_integer`:
for `k : Int` with `5 <= k`,
`Source.LT k.toNat = 9 * 4^(k.toNat - 3)`.
On this domain conversion to Nat is exact. `Source.shape k.toNat` is
precisely the source diagram. `Source.SourceLatin` imposes the conjugate
multiplicity equation for every integer, including symbols outside the
positive row intervals.

## Motivation

The source lists this family as a separate open problem and states that
for k at least six its Latin property is not supplied by the preceding
results. Counting all extensions requires an invariant of the actual
availability graph. `MatchingTemplate.full_transition` identifies that
invariant without identifying tableaux under symmetry.

## Gap

The source theorem, source finiteness, reversible cardinality bridges,
complete base, transition invariant and all-parameter count are proved
in Lean for the complete source assertion.
Information-audit completion is determined only by current typed binding
evidence. Any unfinished registration is disclosed against the original
public theorem through
[issue 20269](https://github.com/the-omega-institute/trureturing/issues/20269);
the source theorem does not receive the refutation exemption.

## Route

`Source.source_row_symbols` proves from the full conjugate type that a
row of length m contains exactly integers 1 through m. The proof uses
strong induction on symbols and exact multiplicity quotas.
`Source.source_iff_rows` proves the converse by a bijection between
occurrences and rows containing a symbol. `Source.sourceEquiv` gives
explicit inverse maps to the finite carrier, interpreting value j as
integer j+1. Finiteness is transported along this actual equivalence.

`Counting.enumerationEquiv` then bijects all source fillings with the
literal row-list enumeration. The enumeration prepends every injective
selection from the availability sets; separate tails give disjoint sets.
No row, column or symbol permutation is divided out.

The ordered tail starts with [{x},{y,z},{x,y,z}], with distinct symbols.
Each inductive layer prefixes a fresh forced symbol and inserts it in
every tail set. There are exactly two tail matchings. The first three
columns have one set {a,c} and two sets {b,c}, giving two head choices.
The remaining columns are the tail sets enlarged by {a,b,c}; high and
low symbols are disjoint. Hence each full graph has four matchings.

For every one of these matchings, deletion followed by a universal new
symbol and column preserves the invariant, changes (a,b,c) to (b,c,u),
and moves a into the low-symbol set. The availability-update identity
is proved from the actual bounds on every existing row.

The complete base at k=5 is kernel-decided: all 144 tableaux of
(5,4,3,3) satisfy the next-row invariant. Induction proves the invariant
at every larger parameter, then disjoint extension counting proves
LT(k+1)=4*LT(k). Thus LT(k)=144*4^(k-5)=9*4^(k-3).
No recurrence, invariant, enumeration result or extension coverage is
assumed in the delivered theorem. The layer (4,3,3) does not justify a
uniform fourfold step, so the proof starts at the exact source endpoint.

## Falsifier

A source definition identifying rows or symbols, a mismatch in the
conjugate multiplicities, failure of an inverse map, a missing base
tableau or an invariant counterexample would invalidate the proposed
source interpretation. The Lean theorem checks the explicit definition
and all proof obligations; independent source comparison checks that
this definition matches the cited paper. A prior complete resolution
would invalidate new-solution credit and must be reused.

## Evidence

The owning Lean modules are `Latin/Tableaux/Source`,
`Latin/Tableaux/MatchingTemplate` and `Latin/Tableaux/Counting`, under
`D5/S3/Combinatorics`. The corresponding owning Blueprint Scribes
explain the definitions, bridges, invariant and universal result.
`Counting.conjecture63_integer` is the full integer-parametrized theorem;
`Counting.conjecture63` is its natural-parameter induction theorem.

The finite base uses `decide +kernel`, not native evaluation with an
additional axiom. Its numeric-reduction utility is consumed by the
universal theorem through `base_count_and_invariant`. The entire exact
source assertion was preregistered in issue 20269. The qualified source
note pins the author TeX and the bounded prior-answer search.

## Triage

`theorem`; a named externally authored open conjecture in the cited
version. The admission basis for the source resolution is
`open-problem-resolution`, with the real source and registration above.
Its reusable mathematical mechanism is the four-choice availability
invariant and its proved preservation. Consumed source/cardinality
bridges and arithmetic consequences are not independent new solutions.

### What the settlement shows

Proved: the exact count is positive for every source parameter, and
every full tableau in this family has exactly four extensions by the
next longest row (`Counting.universal_invariant`, `count_step`, and
`conjecture63`). The same ordered-template argument applies to any
availability graph satisfying `MatchingTemplate.Full`; the graph need
not be produced by a tableau. Its actual low symbols may be arbitrary,
provided the stated distinctness and freshness conditions hold
(`full_matchings`, `full_transition`).

The general tail statement includes arbitrary distinct actual symbols
and arbitrary numbers of forced-prefix layers (`tail_matchings` and
`tail_transition`). It does not establish a fourfold step at (4,3,3).
Conjectures 6.1 and 6.2 and the general wide-partition conjecture remain
outside this result; no consequence about their truth is claimed.

## ASSUMED-UNVERIFIED

The source's open-status attestation is version-specific. Completeness
of the worldwide literature search, global priority and post-version
answers remain unverified. Final independent implementation review, required CI, dev integration,
publication and KPI credit are separate from the mathematical result. An unfinished information registration is
neither a validated audit nor a defect in an already kernel-checked
mathematical proof; its exact missing evidence must remain disclosed.

### Information-audit boundary

Four original public theorem audits have current `declared_validated`
evidence: `Counting.shape_succ`, `Counting.source_enumeration`,
`Counting.conjecture63`, and `Counting.conjecture63_integer`.
The positive universal result has no designated-refutation exemption.
The other thirteen original public theorem audits remain unfinished
under the linked disclosure in
[issue 20269](https://github.com/the-omega-institute/trureturing/issues/20269).
Their exact gaps are:

| Original theorem | Actual failure / missing evidence |
|---|---|
| `MatchingTemplate.mem_matchings` | IE-C050, source.operand_mode: accepted source binding missing. |
| `MatchingTemplate.tail_subsets` | IE-C050, source.telescope_reconstruction: accepted source binding missing. |
| `MatchingTemplate.tail_matchings` | IE-C050, source.state_binder: accepted source binding missing. |
| `MatchingTemplate.tail_transition` | IE-C050, source.telescope_reconstruction: accepted source binding missing. |
| `MatchingTemplate.full_matchings` | IE-C050, source.state_binder: accepted source binding missing. |
| `MatchingTemplate.full_transition` | IE-C050, source.telescope_reconstruction: accepted source binding missing. |
| `Counting.mem_enumerate` | IE-C050, source.operand_mode: accepted source binding missing. |
| `Counting.base_count_and_invariant` | IE-C050, source.absent_occurrence: accepted source binding missing. |
| `Counting.universal_invariant` | IE-C050, source.state_or_output: accepted source binding missing. |
| `Counting.count_step` | Compiler limit 2,000,000 heartbeats in whnf / abstract nested proofs; complete compiled four-slot record and source binding missing. |
| `Source.source_row_symbols` | IE-C050, source.state_binder: accepted source binding missing. |
| `Source.source_iff_rows` | IE-C050, source.operand_mode: accepted source binding missing. |
| `Source.source_finite` | IE-C050, source.observation_data: accepted source binding missing. |

The twelve IE-C050 entries require accepted faithful source reconstruction
and observation binding at the stated source rule. The count-step entry
requires the complete compiled four-slot record, including dependence
and abstracted proofs, and accepted source binding. None of these
thirteen entries is `declared_validated`; the issue is neither a proof
nor an audit certificate.
