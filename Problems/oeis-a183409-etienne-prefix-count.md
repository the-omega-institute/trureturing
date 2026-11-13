---
slug: oeis-a183409-etienne-prefix-count
bibkey: hardin2011a183409
doi: null
url: https://oeis.org/A183409
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.result
---

# Etienne's all-height formula for sorted width-two prefix matrices

## Problem

R. H. Hardin's [OEIS A183409](https://oeis.org/A183409), revision 20,
offset 1,1, states:

> Number of n X 2 binary arrays with each sum of a(1..i,1..j) no greater than i*j/2 and rows and columns in nondecreasing order.

Its second FORMULA attributes the following conjecture to Luce Etienne:

> Conjecture: a(n) = (2*n^3+11*n^2+31*n+27+(n^2+n+5)*(-1)^n)/32.

For each natural n>=1, the objects are actual functions
`M : Fin n → Fin 2 → Bool`. Row words are weakly increasing in the order
00<01<10<11. The left column word is lexicographically at most the right
column word. For every 1<=i<=n and 1<=j<=2, twice the number of ones in
the top-left i by j rectangle is at most i*j. Repeated rows and equal
columns are allowed. Positions remain labeled, with no symmetry quotient.
The published examples containing 00,01,10,11 and 01,01,10,10 establish the
word-order interpretation rather than componentwise sorting.

Define a(n) as the cardinality of exactly this literal subtype. The full
question, over integers, is

    32*a(n) = 2*n^3+11*n^2+31*n+27+(n^2+n+5)*(-1)^n

for every n>=1. No recurrence, generating function, finite cutoff or
computational-resource assumption is substituted for this event.

## Motivation

The full event and its source interpretation are preregistered in
[issue #29612](https://github.com/the-omega-institute/trureturing/issues/29612).
The source note is `Library/PermutationPatterns/hardin2011a183409.md`.
The settling declaration is
`D5/S3/Combinatorics/PermutationArrays/EtiennePrefixCount.result`.

## Gap

The inspected official entry retains the conjectural label. The bounded
source, repository, pinned Mathlib and indexed third-party Lean searches
recorded in #29612 acquired no exact all-height literal-matrix proof.
The immutable [jOEIS implementation](https://github.com/archmageirvine/joeis/blob/17d03f97bf78ff208819e281e6c95767c8ca3099/src/irvine/oeis/a183/A183409.java)
implements the empirical generating function and explicitly implements
Conjectural. The immutable [LODA program](https://github.com/loda-lang/loda-programs/blob/f1b383b2344ab03ae8f79f41289360a6bd4394bd/oeis/183/A183409.asm)
evaluates an arithmetic formula. Neither supplies the literal-matrix
bijections proved here; their known formulas and programs receive no new
proof credit.

## Route

Every sorted matrix consists uniquely of four consecutive row blocks
00^A 01^B 10^C 11^D. The cuts p=A, q=A+B, r=A+B+C are recovered from
strict sublevel cardinalities of the monotone row-rank function. Extraction
and reconstruction preserve each labeled entry, yielding an equivalence
between the literal Arrays subtype and ValidCuts, with both inverse laws.

Column order is equivalent to B>0 or C=0. At prefix height i, the first
column has i-q ones and the two-column rectangle has (i-p)+(i-r) ones,
with natural subtraction. These identities prove in both directions that
all prefix bounds are equivalent to C+D<=A+B and D<=A. The reverse
direction covers each permitted prefix, not only the endpoint i=n.

Put t=C+D, d=D and u=n-t. Then 0<=t<=floor(n/2) and 0<=d<=t.
When d<t, the admissible A values are d<=A<u; when d=t, they are
d<=A<=u. The last coordinate is A-d. Reconstruction uses B=u-A,
C=t-d and D=d. The equivalence between ValidCuts and this dependent
finite parameter family has both inverse laws, including empty blocks
and all interval endpoints. Nat.card transports across both equivalences
before any summation is evaluated.

The fiber at (t,d) has u-d elements, with one extra endpoint precisely
when d=t. Pinned Mathlib finite-sum identities evaluate the fibers and
then their sum. With m=floor(n/2), the proved intermediate identity is

    2*a(n) = 2*(m+1)+(n-m)*(m+1)*(m+2).

The cases n=2*m and n=2*m+1 give the complete signed integer formula.
The n=1 case and the even-height endpoint t=n/2 remain included.
There is exactly one equal-column matrix for each t.

## Falsifier

A literal admissible matrix missing from either inverse construction,
or a positive height whose literal cardinality violates the integer
identity, would refute the corresponding claim. Agreement of a finite
sequence prefix or an arithmetic formula program is insufficient evidence
for the all-height theorem.

## Evidence

`EtiennePrefixCount.result : EtiennePrefixCount.claim` proves the entire
source event. The selected module uses only the standard axiom closure
Classical.choice, Quot.sound and propext. It has no direct frozen D5
public dependency. Its utility is none: this is an unbounded structural
counting proof, not certified finite enumeration or a numeric reduction.

The module's admission basis is open-problem-resolution under #29612.
All fourteen explicit theorems are conservatively classified bind-only;
no escape witness or independent theorem-content credit is claimed.
The twenty explicit data, type, claim and map declarations receive no
independent theorem-content credit. Historical authored counters remain
18 lemmas and 27 definitions; retained counts and compiler-generated
declaration counts are different measures.

| Retained theorem | Live consumer |
| --- | --- |
| lt_sublevel_card | block_extract |
| block_extract | assemble_bijective |
| block_sorted | assemble |
| columns_block_iff | assemble; assemble_bijective |
| ones_block | prefix_block_iff |
| prefix_block_iff | assemble; assemble_bijective |
| block_rank_lt | block_injective |
| block_injective | assemble_bijective |
| assemble_bijective | arrayEquiv |
| card_arrays | a_double |
| inner_double | total_double |
| total_double | a_double |
| a_double | result |
| result | terminal original external-question resolution |

The consumed maps connect arrayEquiv and parameterEquiv to card_arrays;
all helper paths end in result. Consumed bind-only helpers organize this
proof and are not additional mathematical results or admission witnesses.

The source-bound Reg audit is unfinished under the CLAUDE 3.9 linked-issue
exception: [concrete missing inputs and remaining obligations](https://github.com/the-omega-institute/trureturing/issues/29612#issuecomment-6840812573).
The uncompiled mirror is preserved in checkpoint
bc65b1222c5aa32298b7c48d2216fbe147eb1707 and is not delivered as valid
Reg source. No declared_validated registration or completed binding audit
is claimed.

## Triage

**Proved:** the entire positive-height literal cardinality conjecture.
Its mechanism is the two explicit equivalences, the exact prefix identities
and the single extra endpoint in each t-fiber. Equal columns and empty
blocks are essential boundary cases preserved by the construction.

**Unresolved:** extension to other widths, a general parent-table theorem,
and any independently posed recurrence or generating-function event are
not settled here. The width-two reduction uses the four specific row
words and does not establish a count-preserving correspondence in other
widths. No existing external theorem is revised by this result.

No successor research unit is selected: a precise externally posed
neighboring event and its current source/literature/ownership readings
have not been acquired for a new preregistration. This does not start a
new mathematical investigation.

## ASSUMED-UNVERIFIED

The literature screen is bounded. The inspected arXiv versions
2410.07435v2 and 2309.00487v1 concern different matrix constraints and
contain neither exact sequence identifier. Indexed formal-conjectures
identifier searches returned no match. MathDB search requests returned
HTTP 403; exact Solutions panels were unavailable. OpenAlex returned
HTTP 429; no citation-graph absence follows. Search-engine responses did
not establish proof absence. No exhaustive literature search, worldwide
continued openness, originality, priority or external acceptance is claimed.

Independent final reviews, the local gate, exact-head remote required
checks, merge and the first containing dev push are separate delivery
obligations. This mathematical dossier certifies none of those lifecycle
states and asserts no solution KPI.
