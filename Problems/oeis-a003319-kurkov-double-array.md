---
slug: oeis-a003319-kurkov-double-array
bibkey: kurkov2024a003319
doi: null
url: https://oeis.org/A003319
triage: theorem
motivation_gids:
  - D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.result
---

# Kurkov's A003319 double-array conjecture

## Problem

The source audit for this resolution read the canonical OEIS A003319 entry and
these immutable OEIS-data revisions:

- A003319 at commit `dacce77176c40534c4309db03464e7f4c08d83dd`;
- A370380 at commit `a32b213583dbdd91a31cc0975e203471b3afe0fb`;
- A370381 at commit `ed2582877dea2190aa163abe737afe7d42179fae`.

Kurkov's April 26, 2024 conjecture is quoted there verbatim as:

> Conjecture: a(n) = A370380(n-2, 0) = A370381(n-2, 0) for n > 1 with a(0) = a(1) = 1. - _Mikhail Kurkov_, Apr 26 2024

The sequence `a(n)` counts permutations of `{1,...,n}` that preserve no
proper nonempty initial interval. The formal subtype uses permutations of
`Fin n`; translating labels by one gives the same condition. Its literal
formal count is the finite cardinality
`c(n) = Fintype.card (IndecomposablePerm n)`, rather than a sequence defined
by either recurrence.

For natural row and column indices, the two source arrays are formalized
literally as

```text
U(0,k) = 1
U(m+1,k) = (k+2) U(m,k+1) + Sum_{j=0..k} U(m,j)

V(0,k) = 1
V(m+1,k) = Sum_{j=0..k+1} binomial(k+2,j+1) V(m,j).
```

The exact frozen theorem is

```lean
c 0 = 1 ∧ c 1 = 1 ∧
  ∀ n : ℕ, 2 ≤ n → c n = U (n - 2) 0 ∧ c n = V (n - 2) 0
```

## Motivation

The conjecture identifies two independently specified triangular-array
borders with the actual cardinality of a permutation class for every index,
not merely with another recurrence-defined proxy. Proving the complete
two-array statement therefore requires a faithful bridge from the
combinatorial objects to each array and a common uniqueness argument.

Issue #9477 preregistered this named external problem before the formal
resolution. The public result has `proof_shape: content`, with the result
itself as escape witness through the least-stable-prefix decomposition and
the two array invariants. Its admission basis is
`open-problem-resolution`. Utility is `none`: the theorem is an unbounded
symbolic identity, not a bounded enumeration, checker, numeric reduction, or
certified finite instance.

## Gap

The bounded source audit read all 27 recorded A370380 revisions, all 15
A370381 revisions, A003319 revisions 413--462, the Sondow proof in A003319,
Barry's arXiv:1804.06801v1, the complete 19-page King author manuscript, and
the relevant printed Hetyei pages. It found no proof of either array-border
identity in those inspected materials.

The scalar first-block recurrences are not claimed as new. The King
manuscript gives the first-block recurrence and an equivalent positive
recurrence for indecomposable permutations. Hetyei attributes
`c(n)=Sum_{i=1..n-1} i*c(i)*(n-i-1)!` to King and reconstructs the same
permutation decomposition. Reindexing identifies those scalar forms. The
formal proof establishes the needed bridge locally and gives no novelty
credit to its local helper facts.

The final Elsevier body corresponding to King's manuscript was not read.
The inspected revision histories and publications bound this source-status
claim; they do not establish manuscript/final equivalence, exhaustive
literature coverage, worldwide novelty, or priority.

## Route

1. For each positive `n`, choose the least positive prefix stabilized by a
   permutation. Splitting at that prefix is an equivalence between the fiber
   of the least-prefix map and an indecomposable permutation on the prefix
   paired with an arbitrary permutation on the suffix. Taking finite
   cardinalities yields the first-block factorial convolution for the actual
   count, together with direct proofs that `c(0)=c(1)=1`.
2. For `U`, take row partial sums `P(m,k)`. The source recurrence gives
   `P(m+1,k)+U(m,0)=(k+1)P(m,k+1)`. Induction with rising factorial weights
   produces an invariant whose specialization at `k=0` is the same
   factorial convolution for the left border `U(m,0)`.
3. For `V`, shift each row into a function `B(m)` and define a finite
   `Nat`-valued `AddMonoidHom` `T` by the binomial kernel. Its action on the
   shifted rows, a delta sequence, and power sequences is computed exactly.
   Iterating `T` and unrolling the row correction terms gives the same
   factorial convolution for `V(m,0)`.
4. The convolution is triangular with unit coefficient on its newest term.
   Strong induction therefore gives uniqueness. Applying this once to `U`
   and the actual count, and once to `V` and the actual count, proves both
   border identities for every `n>=2`.

All auxiliary identities remain local to `result`; the public source adds no
proxy count and no helper theorem API.

## Falsifier

Any natural `n>=2` for which the cardinality of the actual
indecomposable-permutation subtype differs from `U(n-2,0)` or `V(n-2,0)`
would refute the theorem. A value other than one at `c(0)` or `c(1)` would
also refute it. A mismatch between either displayed recurrence and its cited
OEIS array would instead invalidate the source identification.

## Evidence

- Frozen module:
  `D5/S1/Recurrence/Algebraic/IndecomposablePermutationDoubleArray.lean`.
- Source SHA-256:
  `b5622a97954315ea2f343a8271fbc8f36c16325687fd775ba0e24abb0f0696a4`.
- Frozen module statement identity:
  `sha256:7fd9f45b33401968b48025d17123bed6fdd4cc215506ac8f245e9e14c02b7612`.
- Exact `result` statement identity:
  `sha256:121fb8d5c2c2b1af59d66c811c812bb5548bf576a5f3a14b2c5676b34e4a9bd1`.
- Canonical Lean report SHA-256:
  `5ba9c7e6067f5c6922a26384b42c2443038f25b9ca6834c13324421f9f06cc67`.
- The report records `result` as a theorem with exactly
  `[propext, Classical.choice, Quot.sound]`; there are no direct frozen
  project dependencies.

The typed Scribe claim attaches `ResolutionKind.Proved` to that exact frozen
`result` declaration. The module-level identity and theorem identity differ
by design: the former commits the included module declaration set, while the
latter identifies this one theorem.

## Triage

`theorem`; resolution `proved` for the complete quoted A003319 assertion:
the actual indecomposable-permutation cardinality has initial values one and
is the common exact left border of both source-defined arrays for all
`n>=2`.

## ASSUMED-UNVERIFIED

The historical non-resolution statement is limited to the inspected OEIS
histories, Barry paper, King author manuscript, and Hetyei pages listed
above. The final Elsevier body was not inspected, and no exhaustive search,
manuscript/final equivalence, worldwide-priority claim, or attribution of
novelty to the known scalar recurrences is made. Source-to-Lean fidelity is
supported by the quoted definitions and independent review; it is not a
kernel theorem. The Lean theorem proves the universal statement, while any
bounded numerical comparison would be fault-detection evidence only.
