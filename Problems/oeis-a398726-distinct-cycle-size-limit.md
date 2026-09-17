---
slug: oeis-a398726-distinct-cycle-size-limit
bibkey: kotesovec2026a398726
doi: null
url: https://oeis.org/A398726
triage: theorem
motivation_gids:
  - D5/S1/Descent/FiniteSelfMapConjugacy
---

# OEIS A398726: the distinct cycle size limit

## Problem

Vaclav Kotesovec's August 14, 2026 FORMULA line in OEIS A398726 states:

> Conjecture: a(n) ~ n * n!.

The sequence, entered by Alois P. Heinz on August 8, 2026, is the sum of the
distinct cycle sizes over all permutations of [n]. The exact source and full
statement, preregistered in issue #8059, are:

```lean
noncomputable def DistinctCycleSizes {n : ℕ}
    (σ : Equiv.Perm (Fin n)) : Finset ℕ :=
  σ.partition.parts.toFinset

noncomputable def CycleSizeSum (n : ℕ) : ℕ :=
  ∑ σ : Equiv.Perm (Fin n), ∑ k ∈ DistinctCycleSizes σ, k

theorem result :
  Filter.Tendsto
    (fun n : ℕ => (CycleSizeSum n : ℝ) /
      ((n : ℝ) * (Nat.factorial n : ℝ)))
    Filter.atTop (nhds (1 : ℝ))
```

Partition parts include fixed points as lengths one; the finite set removes
multiplicities. Each distinct length contributes its size. Both sums range
over their entire finite domains. The empty permutation contributes zero.
Fin n is a relabeling of [n], and the real normalization is positive for n>0.
No sequence, counting identity or asymptotic estimate is an assumed premise.

## Motivation

The exact preregistration is
https://github.com/the-omega-institute/trureturing/issues/8059.
D5/S1/Descent/FiniteSelfMapConjugacy supplies context for permutation cycle
invariants. It is not a direct frozen dependency or a statement of this limit.

## Gap

The original revision 28 labels the full limit a conjecture. The known
A293211/A122974 presence and avoidance formulas, credited to Dennis P. Walsh,
are finite counting identities. A132961 counts distinct lengths without
weighting them by size. Cauchy's class-size formula and cycle moment bounds
are known tools; the full application to the actual statistic is the selected
settlement, with no global priority claim.

## Route

The algorithmic address is D5/S0/Asymptotics/WeightedProbability/DistinctCycleSizeLimit, generality I.
The delivery contains only the two necessary source definitions and one
result. Every new helper is local to result, and the module imports only
pinned Mathlib.

For a partition p of n, with multiplicity m_k of part k, let
z(p)=product_k k^(m_k)*m_k!. Cauchy's formula gives exactly n!/z(p)
permutations with partition p. The cited TauCeti full-partition formulation
is adapted locally; it includes the fixed points omitted by cycleType.
Summation by fibres transfers the actual permutation statistic to partition
weights 1/z(p) and proves that these weights sum to one, for every n.

For k>=1, removing two parts k defines an injection from partitions with
m_k>=2 into partitions of n-2k. The exact relation
z(p)=k^2*m_k*(m_k-1)*z(q) and normalized nonnegative target weights give
sum_p m_k*(m_k-1)/z(p)<=1/k^2. Partitions with m_k<=1 contribute zero;
when n<2k the source of the injection is empty. No surjectivity assertion
is needed for this upper bound.

Writing D(p)=sum of the distinct parts gives
0<=n-D(p)<=sum_{k=1}^n k*m_k*(m_k-1).
Averaging yields
0<=n-CycleSizeSum(n)/n!<=H_n, where H_n=sum_{k=1}^n 1/k.
The Cesaro means of the sequence 1/(j+1), which tends to zero, give H_n/n->0.
For all positive n the normalized error is therefore squeezed to zero,
proving the complete normalized limit. The n=0 value does not affect atTop.

## Falsifier

A positive epsilon and an unbounded sequence of indices for which the actual
ratio stays at least epsilon from one would refute the limit; a proved
different limit would also suffice. Finite disagreement with a table does
not refute an asymptotic. A prior published exact settlement would change
unresolved-target eligibility, not the checked mathematical statement.

## Evidence

The complete original revision-28 entry is 1,962 bytes, SHA256
`d9bdb003dcee4319284e1c8c84491a62b084e3aac4ec830699f9a31237f1c39f`.
The exact registration preceded every numerical and Lean probe; it disclosed
root's earlier unverified duplicate-cycle/expected-weight direction.
D5/L/kotesovec2026a398726 records the original statement and cycle conventions.
D5/L/tauceti2026classsizes records the adapted predecessor, immutable source
hashes and complete Apache-2.0 license. D5/L/flajolet2009analytic records the
classical Cauchy formula and cycle-count background.

The exact Stage A source compiled with pinned Lean and Mathlib. An independent
mirror recompiled the exact source and a fresh expanded checker, checked the
complete epsilon limit, source definitions, fixed-point and empty semantics,
and positive denominator. Its public declaration axiom closures are confined
to propext, Classical.choice and Quot.sound. Root's fresh canonical checker
also verified all 16 emitted declarations against that whitelist and checked
the complete expanded limit, identity and empty permutations, and positive
denominators. The mirror is
verification of the submitted proof, not a second independently discovered
proof; its finite enumeration is not asymptotic evidence.

The literature finding is bounded: the complete A398726, A293211, A122974
and A132961 entries; the original textbook's printed pp.137,175-176,180,188,
435,674-675,715-716; and the specific original sections of the permutation
papers listed in #8059 were read. No full application establishing this exact
weighted limit was found in that inspected scope. Source names or recent
identifier misses alone were not treated as proof of novelty. D5 and pinned
Mathlib searches located no exact target in their searched scope. The later
Lean search located and reused TauCeti's class-size predecessor; it does not
supply the full target theorem. No direct frozen D5 dependency is used.

## Triage

First tier: a source-labelled recent (2026) OEIS conjecture, without a claim
that it is easy or neglected. `admission_basis: open-problem-resolution`.
The per-declaration semantic assessment is:

| Declaration | proof_shape | computational_content.kind |
| --- | --- | --- |
| DistinctCycleSizes | N/A (definition) | none |
| CycleSizeSum | N/A (definition) | none |
| result | bind-only | none |

For all three declarations, direct frozen dependencies are empty and
`escape_witness: none`. The author assessed bind-only and the mirror assessed content. Root retains
the conservative bind-only classification and makes no escape-witness claim;
this disagreement does not alter the open-problem-resolution basis.
This conservative proof-shape classification credits
the existing counting, partition-removal and analytic tools. The admission
basis is the complete preregistered external assertion, independently of
whether its steps are bindings of known results. It is an unbounded symbolic
limit, not bounded enumeration, a checker, a numerical reduction or a
certified finite instance. Other computational utility fields are
not-applicable(kind=none). No atom is claimed covered by this deposit.

## ASSUMED-UNVERIFIED

No exhaustive literature absence, global priority or independent model-family
consensus is claimed. The earlier broad literature worker was interrupted
without a conclusion; it is not an approval. Root's named original-source
inspection supplies the bounded registration decision. Walsh's linked note
was not retrieved; Springer items with DOIs 10.1007/BF02986863,
10.1007/s10440-007-9133-y, 10.1007/s10986-024-09637-z and
10.1007/s10986-025-09697-9 were available only as metadata/abstracts. Those
access gaps are not evidence that no proof exists. Papers beyond the
explicitly listed pages and the entire Arratia-Barbour-Tavare monograph were
not claimed read. Published cycle-moment formulas are credited background;
all premises needed here are discharged by the Lean proof.
