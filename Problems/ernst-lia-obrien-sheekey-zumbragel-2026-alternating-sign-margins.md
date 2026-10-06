---
slug: ernst-lia-obrien-sheekey-zumbragel-2026-alternating-sign-margins
bibkey: ernst2026italiansquares
doi: 10.48550/arXiv.2606.25884
url: https://arxiv.org/abs/2606.25884v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Latin/AlternatingSignMargins.result
---

# Equal totals characterize margins of alternating signed square matrices

## Problem

A. Ernst, S. Lia, C. O'Brien, J. Sheekey and J. Zumbrägel,
*Generalising Latin square orthogonality and Frobenius-König with alternating
sign matrices*, arXiv:2606.25884v1, Section 8, printed p. 27:

> Problem 8.3. For which (0, ±1)-vectors R and S of order n does there exist X ∈ W_n with row-sums R and column-sums S?

The same page defines the class:

> Section 4 introduces the set W_n consisting of all (0, ±1)-matrices in which the non-zero entries of each row and column alternate in sign, and the sum of each row/column is in {0, ±1}.

For every natural number n and signed integer vectors R,S on Fin n, the exact
answer is

$$
\left(\exists X\in W_n:\ \forall i,\ \sum_j X_{ij}=R_i,\quad
\forall j,\ \sum_i X_{ij}=S_j\right)
\iff \sum_i R_i=\sum_j S_j.
$$

Alternation is with respect to the natural row and column order. First and last
signs are unrestricted. The zero order and zero lines are included.

## Motivation

The total sum must be the same whether all entries are counted by rows or
columns. Sufficiency shows that no further inequality on these signed margins
is needed for the source's unrestricted matrix class.

## Gap

Issue #12576 preregisters this Tier 1 numbered external problem and its complete
quantified answer before the probe. Its literature qualification examines the
source and arXiv searches for alternating-sign row sums and Italian squares.
Brualdi–Dahl's sign-restricted matrices impose partial-sum conditions, and
Brualdi–Kim's prescribed borders impose first and last signs; neither is used
as an existing characterization of the unrestricted class here. The repository
and pinned Mathlib searches find no existing supplier of this exact answer in
the searched scope. These bounded searches establish no global priority.

## Route

Let p,q count positive and negative row margins and p′,q′ the corresponding
column margins. Transpose if necessary so that p ≥ p′. Equal totals give
p−q=p′−q′, hence d=p−p′=q−q′. Partition the positive rows into p′ matched rows
and d surplus rows, and the negative rows into q′ matched rows and d surplus
rows. Place one signed entry for each matched signed column. Place each pair
of surplus rows into its own zero-margin column, with opposite signs.

The three sign-class counts give n−p′−q′ ≥ 2d, so enough zero-margin columns
exist. The positive and negative incidence placements use the same chosen
zero columns. Their difference is one actual matrix with both margins
simultaneously. Each row has at most one nonzero entry; each column has at
most one entry of each sign. Thus every line alternates. Transposition gives
the remaining orientation. Sum commutation proves necessity.

## Falsifier

A counterexample would be signed margins with equal totals for which every
matrix in W_n fails at least one prescribed margin. A failure under an added
border constraint or zero pattern is not a counterexample to this unrestricted
statement. The local cardinality facts and both margins refer to the same
constructed matrix, rather than separately attainable witnesses.

## Evidence

The formal source is
`D5/S3/Combinatorics/Latin/AlternatingSignMargins.lean`; `result : claim` proves
the complete equivalence for every n. The public definitions are `Signed`,
`Alternates`, `W` and `claim`. The private content theorem `signed_matrix`
constructs the witness; other proof facts are local have blocks. The result's
axiom closure is `propext`, `Classical.choice` and `Quot.sound`. No finite
enumeration supplies the unbounded theorem.

The following independent finite computation enumerates every possible
alternating row, forms every square matrix with such rows, and filters its
columns. For signed alternating lines their sums are automatically in
{−1,0,1}. Its last columns compare all realizable pairs to equal totals and
compare their minimum occupied-cell counts to the larger margin support.

```sh
python3 - <<'PY'
from itertools import product

def alternates(v):
    w=[x for x in v if x]
    return all(a!=b for a,b in zip(w,w[1:]))

for n in range(1,5):
    vectors=list(product((-1,0,1),repeat=n))
    lines=[v for v in vectors if alternates(v)]
    minima={}
    for rows in product(lines,repeat=n):
        cols=list(zip(*rows))
        if not all(alternates(c) for c in cols):continue
        R=tuple(map(sum,rows));S=tuple(map(sum,cols))
        occupied=sum(x!=0 for r in rows for x in r)
        minima[R,S]=min(occupied,minima.get((R,S),occupied))
    equal={(r,s) for r in vectors for s in vectors if sum(r)==sum(s)}
    print(n,len(minima),len(equal),minima.keys()==equal,
          all(k==max(sum(x!=0 for x in r),sum(x!=0 for x in s))
              for (r,s),k in minima.items()),flush=True)
PY
```

Output (order, realizable pairs, equal-total pairs, equality, minimum-support check):

```text
1 3 3 True True
2 19 19 True True
3 141 141 True True
4 1107 1107 True True
```

## Triage

Tier 1; settlement: Proved. Admission basis: `open-problem-resolution`, with
preregistration #12576. Proof shape: content, using the signed incidence
construction. Utility: none; the definitions and theorems express a universal
structural existence result rather than a bounded computation or checker.
Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module:** the total sum is the only obstruction for signed
  square margins. The construction pairs surplus rows in shared zero-margin
  columns; its local capacity inequality is n−p′−q′ ≥ 2d. Empty order, empty
  lines and either orientation of the signed-count comparison are included.
- **Computed:** orders 1 through 4 have exactly 3, 19, 141 and 1107 realizable
  margin pairs, respectively, with no failures of the equal-total criterion.
  The command above also verifies the minimum number of nonzero entries as
  max(|supp R|, |supp S|) in these four orders.
- **Open formalization:** the all-order minimum-support formula. One occupied
  cell per nonzero-margin line gives a lower-bound route, and the sparse
  construction gives the candidate attaining route. No separate Lean statement
  certifying that optimization is delivered here.
- **Open in this delivery:** prescribed first and last signs, cyclic alternation for toroidal
  ASMs with all line sums zero, rectangular W_{m,n}, and the Section 4 question
  with prescribed zero pattern X(k). None is part of the quantified result.
- **Source consequence:** Problem 8.3's unrestricted existence question has
  this exact characterization. It occurs in the final problem list; the
  earlier Frobenius-König and orthogonality results are not used as assumptions
  or strengthened by this theorem. The separate border and zero-pattern
  questions retain their additional constraints.

## ASSUMED-UNVERIFIED

Publication history and worldwide novelty are outside Lean's kernel. The
bounded literature searches do not exclude unindexed, unpublished or unread
resolutions. Finite computed support minima do not establish their all-order
formula. The model fidelity is a source comparison; Lean proves the encoded
statement, not the authenticity of the external PDF.
