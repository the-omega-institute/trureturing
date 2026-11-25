---
slug: hardin-a235289-common-recurrence
bibkey: hardin2014a235289
doi: null
url: https://oeis.org/A235289
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.result
---

# Hardin's common six-lag recurrence for constant-stress rectangular arrays

## Problem

R. H. Hardin's OEIS A235289 defines $T(n,k)$ as the number of literal
$(n+1)\times(k+1)$ arrays with entries in $\{0,1,2,3\}$ for which every
contiguous $2\times2$ block has absolute diagonal difference four. The
FORMULA proposes one order-six recurrence for every row and column.
The OFFSET is `1,1`. The source quotations and pinned revision are
in the [library note](../Library/Automata/hardin2014a235289.md).
[Preregistration #34236](https://github.com/the-omega-institute/trureturing/issues/34236)

For all $n,k\ge1$ the proposed identities are

$$
\begin{aligned}
T(n+6,k)&=3T(n+5,k)+3T(n+4,k)-15T(n+3,k)+4T(n+2,k)+18T(n+1,k)-12T(n,k),\\
T(n,k+6)&=3T(n,k+5)+3T(n,k+4)-15T(n,k+3)+4T(n,k+2)+18T(n,k+1)-12T(n,k).
\end{aligned}
$$

### Statement echo

| Source clause | Lean counterpart |
| --- | --- |
| Ordinary $(n+1)\times(k+1)$ rectangles, alphabet $0,1,2,3$ | `Grid n k = Fin (n + 1) → Fin (k + 1) → Fin 4` |
| Every contiguous block | `Legal` quantifies over its upper left corner in `Fin n` and `Fin k`. The two embeddings reach exactly the original index and its successor. |
| Absolute diagonal difference four | `Legal` compares the natural absolute value of the integer main-diagonal sum minus the integer antidiagonal sum with four. |
| Number of literal arrays | `T` casts the cardinality of the legal subtype to `ℤ`. |
| Both signed recurrences | The two conjuncts of `result` use the six coefficients in the displayed order. |
| Positive indices and order six | `result` requires both coordinates of `d : ℕ × ℕ` to be positive. The left sides start six steps after the base index, so the varying index is at least seven. |

## Motivation

The settling GID is
`D5/S3/Combinatorics/TraceAvoidingArrays/Recurrence/HardinA235289Recurrence.result`.
Its Scribe carries an `OpenProblemResolutionClaim` of kind `Proved`. The
admission basis is `open-problem-resolution` for the Tier 1 empirical
conjecture recorded in #34236.

## Gap

The OEIS FORMULA gives empirical evidence at specific widths. It proposes
the same recurrence for arbitrary positive dimensions. The scoped literature
and repository screen in #34236 found no prior proof of that assertion.
The screen establishes what was located in those sources. Global priority
remains unverified.

## Route

Checkerboard complementation exchanges each absolute-difference constraint
for a block sum of two or ten. Adjacent blocks share two cells, and their
unshared pairs can differ in sum by at most six. Thus all the block sums
in a positive rectangle agree. Global complementation exchanges the two
classes and makes the original count twice the sum-two count.

In a sum-two array, successive rows have complementary horizontal edge-sum
profiles, with each pair of complementary sums adding to two. Fixing the
first profile makes the choices of actual rows independent, so the count is
a sum of products of alternating fiber sizes. A row in a fiber is determined
by its first entry. The number of possible first entries is bounded above by
one plus the first horizontal edge sum. The corresponding pair of bounds
adds to four. Each nonzero alternating contribution therefore grows by the
one-step ratio one or two, or by the two-step ratio two or three. Each type
satisfies the six-lag recurrence, which is preserved by summation. The
transpose is a bijection on the literal legal arrays with swapped dimensions.

## Falsifier

An exact literal count at any positive rectangle that violates either
displayed identity would refute the assertion. The recurrence starts at
varying index seven in both directions.

## Evidence

The only public theorem of the module is
`D5.S3.Combinatorics.TraceAvoidingArrays.Recurrence.HardinA235289Recurrence.result`.
Its axiom closure consists of `propext`, `Classical.choice` and
`Quot.sound`. The checkerboard bijection, the row-profile counting
identity, the bounds on fiber sizes and the two-axis identities are
kernel checked in that proof.


The escape registration uses the enrolled dependent-family realization.
Its single readout takes the pair of rectangular indices to the integer
count. The law is the full conjunction of the two signed recurrences.
Incrementing the count at dimension pair $(7,1)$ violates the first
identity at base pair $(1,1)$. The two positive pairs $(1,1)$ and $(2,1)$
give distinct actual counts. The registration is `declared_validated`
with a source-equivalence bridge and an open residual.

## Triage

### What the settlement shows

The common recurrence comes from the possible multiplicities of alternating
row profiles of a literal count. The proof applies at every positive width
and height, including width or height one in the table indexing. A slice
can satisfy a smaller recurrence. The theorem gives no minimal-order
assertion.

The order-seven square-diagonal recurrence of A235281 remains open here.
The row-profile reduction suggests grouping complementary profiles by exact
fiber multiplicities as the width and height grow together. The necessary
multiplicity counts across widths are an additional obligation. Other
alphabets also remain open here. [OEIS A235281, revision 9](https://raw.githubusercontent.com/oeis/oeisdata/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A235/A235281.seq)

## ASSUMED-UNVERIFIED

Global prior-art exclusion and the full citation graph are unverified.
The screen in #34236 records an OpenAlex HTTP 429.
