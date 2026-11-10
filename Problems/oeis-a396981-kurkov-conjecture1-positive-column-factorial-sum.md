---
slug: oeis-a396981-kurkov-conjecture1-positive-column-factorial-sum
bibkey: kurkov2026a396981c1
doi: null
url: https://oeis.org/A396981
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.result
---

# Kurkov's A396981 Conjecture 1: the positive-column factorial sum

## Problem

Mikhail Kurkov's OEIS A396981 Conjecture 1 is the assertion after
“we have” in the following literal source line. The independent array
definition is quoted with it:

```text
%N A396981 Array read by ascending antidiagonals: A(n, k) = A(n, k-A002024(k)) + (n+A002024(k)-1) * A(n-1, k) with A(n, 0) = 0^n, A(0, k) = 1.
%F A396981 Conjecture 1: similarly to |Stirling1(n+k+1, k+1)| = Sum_{j=0..n} |Stirling1(k+j, k)| * (n + k)! / (k + j)! we have A(n, k+f(k)+1) = Sum_{j=0..n} A(j, k) * (n + f(k))! / (f(k) + j)! where f(n) = A002024(n).
```

The immutable source is revision 45 of the entry, at
[oeisdata commit d4ade8b4ca7c6ff0ac8931532918fd4f6176805e](https://raw.githubusercontent.com/oeis/oeisdata/d4ade8b4ca7c6ff0ac8931532918fd4f6176805e/seq/A396/A396981.seq),
4423 bytes, SHA-256
`70ab30cae0ec41e3eac39faf58f06fcf5e23635591b90876392184c09bf37e88`.
Attribution is Mikhail Kurkov and OEIS Foundation, CC-BY-SA 4.0.
The [dependent A002024 source](https://raw.githubusercontent.com/oeis/oeisdata/d4ade8b4ca7c6ff0ac8931532918fd4f6176805e/seq/A002/A002024.seq),
SHA-256 `487637ef1b1dce6695ff421920879a81e32ea4331128f091655077e5e5be81f0`,
has onset one and repeats each positive integer s exactly s times.
Thus f(q) is the unique positive integer s with
s(s-1)/2 < q <= s(s+1)/2 for q >= 1.

The full event E preregistered in
[issue #28664](https://github.com/the-omega-institute/trureturing/issues/28664)
is the following 943 UTF-8 bytes without the final newline, SHA-256
`022ad4acf10527e78516f5d45831b7d3dfa565e15d03bb7895fefd64fbb4649b`:

```text
Let N={0,1,2,...}. For every positive integer q, let f(q) be the unique integer s>=1 satisfying s(s-1)/2<q<=s(s+1)/2 (OEIS A002024). For A:N x N -> N, IsArray(A) means A(0,q)=1 for all q>=0, A(n,0)=0 for all n>=1, and A(n,q)=A(n,q-f(q))+(n+f(q)-1)A(n-1,q) for all n,q>=1. E: There exists A with IsArray(A), and for every A with IsArray(A), every n>=0 and every k>=1,
(A(n,k+f(k)+1):Q)=sum_{j=0}^{n} (A(j,k):Q)*((n+f(k))!:Q)/((f(k)+j)!:Q).
The sum includes both endpoints; factorials are natural factorials cast to Q before ordinary division, with nonzero denominators. This is the entire defined positive-column assertion after 'we have' in OEIS A396981 Conjecture1, including n=0, without a finite cutoff. The prefatory Stirling identity, Conjectures2-4 and any f(0)/k=0 extension are outside E. No source-bridge assumption beyond the literal defining equations is permitted. The existence conjunct prevents a vacuous arbitrary-array theorem.
```

Natural subtraction in the defining equations agrees with integer
subtraction on the positive domain. The two natural quotients in the
block-index characterization use floor division. Factorial quotients in E
are ordinary rational division after casting the natural factorials.
The prefatory Stirling identity, the separate unlabelled Stirling formula,
Conjectures 2–4, and every f(0) or k=0 extension are excluded and supply no
premise.

## Motivation

This first-tier OEIS-only external conjecture asks for a complete relation
between two columns of an independently specified array. Existence and the
universal lawful-array clause make the result stronger than agreement of a
chosen implementation on a finite prefix.

The admission basis is `open-problem-resolution` under CLAUDE §3.2 and
issue #28664. The conservative classification of every authored theorem is
`proof_shape: bind-only`; there is no escape-content or escape-witness
claim. The only public declarations are f, IsArray and result. There are no
direct frozen D5 mathematical dependencies. Utility is `none`: these are
definitions and an unbounded symbolic theorem, not a bounded enumeration,
checker, numeric reduction or certified finite instance.

## Gap

The bounded qualification in issue #28664 inspected public and private D5,
Blueprint, Problems, Library, theory/digestion, pinned Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, third-party Lean and accessible
literature. Its status is `not-found-in-searched-scope`, `partial`.
No supplier of the complete literal C1 assertion was identified. Mathlib's
factorial, finite-sum and least-witness machinery is reused without a claim
of novelty for those ingredients. The related A396981 issue #24764 concerns
Conjecture 4; it is not a supplier or premise for this result.

The qualification is a bounded, read-only search result, not an exhaustive
prior-art certification. Exact-name and metadata searches do not exclude
differently named generic theorems or unindexed proofs. Semantic Scholar
returned 429 and OEIS history returned 403. The inspected weighted-Stirling
paper 2607.26613v1 concerns another sequence.

## Route

Define f(q) as the least natural s with 2q <= s(s+1). For positive q,
minimality proves the lower block inequality and positivity; conversely
the two block bounds characterize the least witness. They imply
f(k+f(k)+1)=f(k)+1 for every k>=1.

Construct the array by well-founded recursion in the lexicographic pair
(n,q). A positive column drops to q-f(q)<q, and the other recursive term
drops the row. The row-zero and column-zero clauses, followed by the literal
positive recurrence, prove IsArray for this construction.

For any lawful A and k>=1, put B(n)=A(n,k+f(k)+1). Substitution of the block
shift into the source recurrence gives
B(n+1)=A(n+1,k)+(n+1+f(k))B(n). At n=0 the identity is the ratio of a
nonzero factorial to itself. Induction on n, the factorial successor law
and the inclusive finite-sum successor law give E. This argument uses no
extra relation between A and an externally chosen array.

## Falsifier

Failure of existence of a natural-valued lawful array, or a lawful array
with natural n>=0 and k>=1 violating the literal rational identity, would
refute E. A finite prefix cannot establish E. A counterexample at k=0 or to
another source formula does not refute the stated event.

## Evidence

The endpoint is
`D5.S1.Recurrence.Algebraic.KurkovTriangularColumnSum.result`, with declaration
statement identity
`sha256:db31676b7196ad8c21dc90e8245c25e9b2c1cbceb424702455011d58c16c2d84`
and compiled type SHA-256
`a7a69311f6ba2bf237159c4bf9ad3d9c342954961f17ee97598c3117802c739c`.
The canonical freeze route is `deposit-uncovered`, without an atom or
coverage claim. The frozen state is
`Golden/Frozen/state/D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.lean.json`.
Lean is the mathematical source; the Scribe renders both conjuncts of E.

Every private authored helper has an actual consumer. Each listed consumer
uses the declaration in its row; helpers receive no separate result credit:

| Declaration | Shape or role | Actual consumers |
| --- | --- | --- |
| f | definition | IsArray, f_upper, f_lower, f_characterization, f_shift, array, column_step, column_sum, result |
| IsArray | definition | array_lawful, column_step, column_sum, result |
| upper_exists | bind-only | f, f_upper, f_lower, f_characterization |
| f_upper | bind-only | f_pos, f_lower, f_characterization, f_shift |
| f_pos | bind-only | f_lower, f_characterization, f_shift, array termination |
| f_lower | bind-only | f_characterization, f_shift |
| f_characterization | bind-only | f_shift |
| f_shift | bind-only | column_step |
| array | private definition | array_lawful, result |
| array_lawful | bind-only | result |
| column_step | bind-only | column_sum |
| factorial_ne_zero | bind-only | column_sum |
| column_sum | bind-only | result |
| result | bind-only | external settlement endpoint E |

All compiled axiom closures are contained in Classical.choice, Quot.sound
and propext. The retained mirror
`Reg/D5/S1/Recurrence/Algebraic/KurkovTriangularColumnSum.lean` carries the
source-equivalence registration of the complete telescope, including
existence and the universal array quantifier. Its current compiled binding
is `declared_validated`, with continuation `unknown`. That residual records
unknown continuation only; it proves neither undecidability nor
inexhaustibility.

## Triage

`theorem`: the result proves the full event E for every n>=0 and k>=1,
including existence and the inclusive sum. The block shift and recurrence
unrolling explain the identity; this delivery asserts no generalized
family theorem, Conjectures 2–4, k=0 extension, Stirling identity, or
independent integrality or uniqueness theorem. Mathematical truth is
separate from remote delivery and programme credit.

## ASSUMED-UNVERIFIED

Worldwide openness, priority and exhaustive absence of earlier proofs
remain unverified beyond the bounded qualification. The qualification
reports are inherited source-search evidence; the immutable primary bytes
are directly checked. Kernel validation does not establish historical
priority or replace source-fidelity review. Unknown registration
continuation does not settle any neighboring mathematical question.
