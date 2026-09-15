---
bibkey: switkay2026divisorpowerunion
authors: Hal M. Switkay
year: 2026
title: "OEIS A396596: divisor-power records and the highly/deeply composite union conjecture"
doi: null
url: https://oeis.org/search?q=id:A396596&fmt=text
claim: "We conjecture that the present sequence can be constructed simply as a union of highly composite numbers and deeply composite numbers."
strata_touched:
  - D5/S3/ArithSums/DivisorRecords/DivisorPowerUnionRefutation
license: citation-only
triage: anchor
---

# Divisor-power records and the proposed union

Hal M. Switkay's A396596 entry supplies the definition and the conjecture
addressed by the repository's refutation. The associated definition
of deeply composite numbers is read from A095848. The new proof is a repository
derivation, not a proof attributed to either OEIS entry.

## Verified locator

- URL: https://oeis.org/search?q=id:A396596&fmt=text
- Entry: A396596, revision 65, September 12, 2026, 21:50:13.
- Author line: `_Hal M. Switkay_, Aug 31 2026`.
- NAME (verbatim): Natural numbers k such that the sum of the x-th powers of the divisors of k achieves a record, for some x <= 0.
- Selected COMMENTS sentence (verbatim): We conjecture that the present sequence can be constructed simply as a union of highly composite numbers and deeply composite numbers.
- Original text SHA-256: `b9c56e73b68f21d84293b927175de7a19435822a26cb28986e75cb3075edd633` (1680 bytes).
- The complete pinned original was read for this note. The preregistration
  records an official HTTP 200 refetch on September 15, 2026, at 11:19 UTC,
  returning the same bytes and revision. This note does not claim a fresh
  online fetch or a complete revision-history audit.

## Source definitions and exact scope

A396596's surrounding comment identifies highly composite numbers with
records at zero, superabundant numbers with records at minus one, and deeply
composite numbers with sufficiently negative exponents. Its observation about
superabundant numbers below `10^11` is a separate source assertion; neither
that finite observation nor the A095849 intersection conjecture is the target.

A095848, revision 28, June 28, 2026, 15:47:52, at
https://oeis.org/search?q=id:A095848&fmt=text gives the following NAME:

> Deeply composite numbers: numbers n where sigma_k(n) increases to a record for all sufficiently low (i.e., negative) values of k.

Its first COMMENTS line is:

> Sigma_k(n) > sigma_k(m) for all m < n (where the function sigma_k(n) is the sum of the k-th powers of all divisors of n) for all or almost all negative values of k.

The complete pinned text has SHA-256
`8aa83cb8ac13b68499cb3f8791c605a35250adafdd2cab926f14114f1491fbfb`.
A095848's original author is Matthew Vandermast, June 9, 2004; its later
lexicographic comments include contributions by Switkay. Here the definition
uses all sufficiently low **real** powers, in A396596's real-parameter setting.
No equivalence with a separately defined lexicographic predicate is assumed.

For positive natural `n`, the sum includes every positive divisor, including
1 and `n`. A strict record beats every positive natural predecessor at the
same real exponent. The exponent and eventual threshold may depend on `n`;
neither may depend on the predecessor. At zero each summand is one, giving
the strict divisor-count record of A002182. At `n = 1` the predecessor
condition is empty. Lean's total definition also assigns an empty divisor
sum at zero; the claim explicitly restricts to positive candidates.

## Complete Lean statement mirror

The four authored declarations have the following definitions and theorem
type, in namespace
`D5.S3.ArithSums.DivisorRecords.DivisorPowerUnionRefutation`:

```lean
noncomputable def DivisorPowerSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ d ∈ n.divisors, (d : ℝ) ^ x

def StrictDivisorPowerRecord (n : ℕ) (x : ℝ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n →
    DivisorPowerSum m x < DivisorPowerSum n x

def claim : Prop :=
  ∀ n : ℕ, 0 < n →
    ((∃ x : ℝ, x ≤ 0 ∧ StrictDivisorPowerRecord n x) ↔
      (StrictDivisorPowerRecord n 0 ∨
        ∃ B : ℝ, B < 0 ∧ ∀ x : ℝ, x ≤ B →
          StrictDivisorPowerRecord n x))

theorem result : ¬ claim
```

The last line displays the theorem type, not an executable proof replacement.
The full proof belongs to the Lean source. The assertion negated is the
complete universal iff, with natural candidates and predecessors and real
exponents and thresholds; it is not a bounded or integer-exponent surrogate.

## Preregistered question and bounded source assessment

`question_answered`: does the exact A396596 union assertion above hold?
The public preregistration is
https://github.com/the-omega-institute/trureturing/issues/8081,
created September 15, 2026, at 11:22:40 UTC. Its pinned text has SHA-256
`8d4e74e669b36db6b938f2c31c793001f29bbf38386d8906799ded077e827237`.
It fixes the full statement before numerical or Lean probes and classifies
the source-labelled conjecture as first tier.

`dominating_theorem_search`: `not-found-in-searched-scope`, as reported in
that preregistration. Lexical target and conclusion-shape searches covered
D5, Problems, Library and Blueprint at dev
`b7d245a444b19b4036490129a61d9c01370052e0`, and pinned Mathlib's arithmetic
and power scope. The inspected earlier repository results concern
square-root-rank lcm divisibility or powers of prime exponents, not powers
of all divisors. No direct frozen project import occurs in this candidate.
These are bounded search results, not a semantic completeness guarantee.

The preregistration reports complete reads of the A396596, A095848, A002182
and A095849 originals and the bodies of issues/PRs 6022, 6006, 7335, 6072,
6067 and their 12 comments. The earlier targets were superseded or covered;
8054 concerned the different A094802 factorial/lcm problem. All-state GitHub
search at 10:51:20 UTC on September 15 returned 0 exact A396596 records and
6 deeply-composite records, with `incomplete_results=false`; the 11:19 UTC
ownership search returned the same counts. These pre-registration snapshots
do not assert exclusive or continuing ownership.

Alaoglu–Erdős, *On Highly Composite and Similar Numbers* (1944), printed
page 465, section 6(7), was inspected by the preregistration author in the
original scan. It discusses real divisor-power records and the near-zero
negative regime. The complete 23-page PDF extraction was also read, but its
missing or damaged equations prevent calling this a complete mathematical
reading or proof-level exclusion. No selected union settlement was located
in the readable prose. Burdette–Stewart (2020), arXiv:2009.03306v1, was read
as complete four-page text including the appendix; it concerns a different
prime-multiplication/division graph problem. Its computations were not
reproduced. These historical readings are attributed to the preregistration,
not newly performed for this note.

Bing relaxed the query to unrelated results; DuckDuckGo challenged the
client; arXiv's query API returned 429; an optional urllib refetch returned
403 before the successful official request. None supplies negative search
evidence. Uninspected papers, inaccessible monographs and full databases
remain unverified. No global absence, priority, neglect or difficulty claim
is made. A located earlier full settlement invalidates the stated eligibility.

## Proof and verification boundary

The proof uses `N = 32125373280` at `x = -4`. Its full-domain argument
combines a telescoping reciprocal-fourth-power bound for nonmultiples of
`L = 232792560 = lcm(1,...,19)` with a 137-row exact factorization and sigma
certificate for every smaller positive multiple of `L`. Local soundness
connects the certificate to the actual divisor sum. At zero the predecessor
`27935107200` ties its 3072 divisors. For every real `x ≤ -1000`, predecessor
`26771144400` wins by comparing its extra divisor 25 with N-only divisors
at least 27. For each proposed `B < 0`, `min(B,-1000)` contradicts eventual
record membership. Empirical candidate discovery is distinct from these
proof obligations; no floating-point or prime-signature completeness
assumption carries the argument. No minimality or other candidate is claimed.

The canonical module and full expanded negation checker validate the complete
claim under the standard axiom closure. Independent checking also covers the
137 exact arithmetic rows and the full predecessor and real-exponent domains.
The semantic classification is `proof_shape: content`,
`computational_content.kind: certified-instance` (also bounded enumeration),
`utility: refutes`, `admission_basis: open-problem-resolution`,
`escape_witness: none`.
The accompanying Problems dossier supplies the exact scope and route.
This theorem does not assert that all superabundant numbers lie outside
either class.

OEIS use is citation and short quotation under https://oeis.org/LICENSE.
No upstream program or proof is copied. Source definitions and claim are
literature-attested; the proof is repo-derived.
