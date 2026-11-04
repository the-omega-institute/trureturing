---
slug: oeis-a152661-mathar-first-recurrence
bibkey: oeis2008a152661
doi: null
url: https://oeis.org/A152661
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/MatharSameParityRecurrence.result
---

# Mathar's first recurrence for OEIS A152661

## Problem

OEIS A152661, revision 23, defines a(n), for n >= 2, as the number of
permutations of {1,...,n} whose first two entries have the same parity.
Its first conjectural FORMULA, attributed to R. J. Mathar, states

$$
(3-n)a(n)+2(n-2)a(n-1)+(n-1)(n-2)(n-3)a(n-2)=0.
$$

The assertion here is this exact equality in the integers for every natural
n >= 4. Each sequence value is the actual permutation cardinality, cast to
the integers. The domain ensures that n, n-1 and n-2 all lie in the source
domain. The adjacent conjecture a(n)=2*A077613(n-1) is excluded.

## Motivation

The recurrence relates three consecutive values of the source permutation
count at every admissible index. Issue #22922 preregisters precisely this
first Mathar FORMULA and its counting-bridge requirement.

## Gap

The source already supplies even and odd factorial-binomial formulas. Those
are prior formulas, not new counting claims here. The missing result targeted
by #22922 is a proof of the conjectural recurrence for the actual source
count. The preregistration records bounded source, repository and literature
searches without a matching settlement; it does not establish global priority.

## Route

Represent a permutation by a bijection of Fin n, giving its value in position
i+1 the natural label p(i).val+1. Equality of parity is preserved by adding
one to both first values. Map each counted permutation to its ordered pair
of distinct first values. This gives an equivalence with the disjoint union
of the corresponding completion fibers.

For each allowed pair, the number of permutations completing it is (n-2)!.
The proof applies the frozen finite partial-injection extension theorem
`D5/S3/Combinatorics/EdgeLabeling/CubicARGraphCounting.nat_card_equiv_constraints`
to the two prescribed positions and values. If the parity classes have sizes
e and o, the pair count is e(e-1)+o(o-1). The equivalence therefore proves
that the actual source cardinality is [e(e-1)+o(o-1)](n-2)!.

## Falsifier

A natural n >= 4 whose actual permutation count violates the displayed
integer equality would contradict the theorem. Replacing that count by an
unconnected factorial formula, or checking only finitely many indices,
would not establish this assertion.

## Evidence

The mathematical source is
`D5/S3/Combinatorics/Permutation/MatharSameParityRecurrence.lean`.
Its public definition `a` is the integer cast of the cardinality of the
permutation subtype for n >= 2, with zero assigned only outside that domain.
The public theorem
`D5/S3/Combinatorics/Permutation/MatharSameParityRecurrence.result`
proves the displayed recurrence for every natural n >= 4. Its Blueprint
mirrors both public declarations and binds the recurrence to this problem.

The positive four-slot escape audit is unfinished, as documented in
[issue #22961](https://github.com/the-omega-institute/trureturing/issues/22961).
No validated registration or refutation exemption is claimed. The missing
evidence is a compiled count-realization bridge for a(4)>0, actual observation
dependence at indices 4 and 5, and a validated current four-slot binding.

## Triage

For n=2k+2, the two parity classes both have size k+1, so the ordered-pair
count is 2k(k+1) and a(2k+2)=2k(k+1)(2k)!. For n=2k+3, their sizes are k+1
and k+2, so the pair count is 2(k+1)^2 and a(2k+3)=2(k+1)^2(2k+1)!.
These identities are obtained from the actual cardinality through the fiber
equivalence. They recover the source's prior parity formulas; they are not
additional open-problem settlements.

Substitution of these formulas and the factorial successor identity proves
the recurrence separately for n=2k+4 and n=2k+5, covering every n >= 4.
The first case includes n=4 and uses a(2)=0 and a(4)=8. This establishes
exactly the first Mathar FORMULA. The adjacent A077613 conjecture remains
unresolved in this delivery and contributes no additional solution credit.

## ASSUMED-UNVERIFIED

The recorded literature searches are bounded. Worldwide novelty, first-proof
priority and the absence of an independent proof outside their scope are
unverified. No assertion is made about other OEIS conjectures or an extension
of this recurrence below n=4.
