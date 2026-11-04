---
slug: chen-chen-step-m-eulerian-parity-positivity
bibkey: chenchen2026stepm
doi: null
url: https://oeis.org/A392664
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.even_rows_positive
---

# Chen and Chen's step-m Eulerian parity positivity

## Problem

For each m=-3,-4,-5, let T map pairs of natural numbers to integers, with
T(n,1)=T(n,n)=1 for n>=1 and

`T(n,k)=(m*(n-k)+1)*T(n-1,k-1)+(m*(k-1)+1)*T(n-1,k)`

for 1<k<n. The conjectures in OEIS A392664, A392665 and A392666 assert
T(n,k)>=0 for every positive even n and every 1<=k<=n. The exact Lean
`claim` conjoins, for each parameter, existence of a solution and this
assertion for every solution. Row zero and entries outside the triangle
are unconstrained, and no uniqueness of the total extension is assumed.

## Motivation

This is the conjunction scoped by
[#24785](https://github.com/the-omega-institute/trureturing/issues/24785).
The finite verification through row 400 in the source does not prove the
unbounded claim. The stronger mathematical target uses every integer r>=3
and m=-r, and proves strictly positive even rows.

## Gap

The three directly read OEIS internal pages label the nonnegativity
assertion a conjecture. Repository and pinned Mathlib searches for the
identifiers and step-m Eulerian recursion found no exact prior theorem.
Mathlib supplies integer order, parity and induction; the row recursion
and its sign estimates are the source-specific part. arXiv API identifier
search for the disjunction of A392664, A392665 and A392666 returned zero
records. The structural query `Eulerian AND triangle AND positivity`
returned nine records, including arXiv:2007.12602, arXiv:2012.03629 and
arXiv:2608.29224. Their abstracts discuss generalized Eulerian triangles
and positivity; full-text comparison of their hypotheses with the
negative-step source remains unverified. Public GitHub repository search
for A392664 returned zero repositories. GitHub code
search required authentication, so that search is incomplete. No global
absence or priority claim follows from these bounded searches.

## Route

Construct a total solution recursively in the row index. Prove reflection
T(n,k)=T(n,n+1-k) by strong induction, using only triangular positions.

For m=-r and x(n)=T(n,2), eliminate the intervening row to obtain

`x(n+2)=(r-1)^2*x(n)+r*(r-2)*n+2-r^2` for n>=2.

The initial values are x(2)=1 and x(4)=2*r*(r-3)+3. For n>=4 the
forcing term equals

`r*(r-2)*(n-4)+3*r*(r-3)+r+2`,

which is positive for r>=3. Thus all even second-column values are
positive, and reflection supplies the penultimate column. From a
positive even row n, the negative recurrence coefficients make every
interior entry in row n+1 negative. At positions 3<=k<=n of row n+2,
both predecessors are negative and both products are positive. The
second and penultimate columns are treated by the independent column
argument, and the boundary values equal one. Induction from row two
gives strict positivity throughout every positive even row.

Specializing the one general theorem at r=3,4,5 and adjoining the
constructed existence witnesses gives the exact source conjunction.
The parameter threshold cannot include r=2: the literal recursion then
forces T(3,2)=-2 and T(4,2)=-1.

## Falsifier

A solution of one of the three literal recursions with a negative entry
at a positive even row and a column between one and that row would
refute the source claim. A disagreement outside the prescribed triangle
would not. Finite positive prefixes cannot establish the result.

## Evidence

The Lean owner is
`D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.lean`.
The generic theorem is `even_rows_positive`; `result` states the entire
`claim`, including both existence and universality at each parameter.

## Triage

The general theorem has `proof_shape: content` and admission basis
`escape-witness`: the new intermediate proposition
`forall q, 0 < T(2*q+2,2)` is proved by `second_even_positive` and used
on the live path through `positive_rows`. It requires the two-step
induction and is not an instantiation or normalization of a prior
positivity theorem. The final specialization also has `proof_shape:
content` after expanding the same-delivery general theorem and existence
construction; the same intermediate proposition remains on its live
proof path. Its admission basis is `escape-witness`, and only this exact
external conjecture conclusion carries the open-problem resolution claim.
Auxiliary statements are consumed by these proofs. `utility: none` describes an unbounded
mathematical argument, without bounded enumeration or a numeric certificate.

### What the settlement shows

The kernel-checked theorem proves strict positivity on every positive even
row for all integer steps `m = -r` with `r >= 3`; `result` specializes this
argument to the three OEIS conjectures and includes the required existence
clauses. The source-bound escape registrations remain unresolved under issue
[#24785](https://github.com/the-omega-institute/trureturing/issues/24785), so
the settlement does not claim a validated audit.

### Unfinished escape audit

The associated issue is
[#24785](https://github.com/the-omega-institute/trureturing/issues/24785).
The source-bound families in
`Reg/D5/S1/Recurrence/Algebraic/ChenChenParityPositivity.lean` have compiled
equivalence bridges, actual-positive laws, whole-family variation,
sensitivity and observational-dependence proofs. The scoped report
nevertheless returns `declared_unresolved` for both bindings:

- `even_rows_positive`: `IE-C050 ClosedTruthReadout`,
  `reason=unclassified_form`, `rule=source.params`. Recognition of the
  selected integer, triangle-function and row parameter packing is missing.
- `result`: `IE-C050 ClosedTruthReadout`, `reason=unclassified_form`,
  `rule=source.unlinked_operand`, with source operand `Classical.choice`
  in the classical Boolean observation of `ParityPositivity`.

No `declared_validated` audit is claimed. These source-binding gaps are
separate from the kernel-checked positivity theorem and exact conjunction.

## ASSUMED-UNVERIFIED

The bounded literature and repository searches recorded above do not establish
worldwide novelty or priority. The comparison with generalized Eulerian
triangle papers remains unverified, and the unresolved source-binding audit in
issue [#24785](https://github.com/the-omega-institute/trureturing/issues/24785)
does not weaken the kernel-checked theorem or make the audit validated.
