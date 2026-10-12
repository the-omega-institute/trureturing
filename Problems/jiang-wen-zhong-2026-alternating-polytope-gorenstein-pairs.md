---
slug: jiang-wen-zhong-2026-alternating-polytope-gorenstein-pairs
bibkey: jiangwenzhong2026alternating
doi: null
url: https://arxiv.org/abs/2607.14887v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.result
---

# The Gorenstein pairs for alternating adjacent-sum polytopes

## Problem

Xinru Jiang, Suzhen Wen and Yueming Zhong, *Alternating adjacent-sum
polytopes: transfer matrices and Ehrhart series*, arXiv:2607.14887v1,
§4, Question Q1 (`q-gorenstein`), ask:

> For $s=3$, direct computation (Propositions 3.22 and 3.23) shows that only $d=2$ is Gorenstein in even dimensions $d\le6$; we conjecture this extends to all $d\ge4$. Characterize all $(s,r)$ with $s\ge2$ for which $\mathcal P_{2r}^{(s)}$ is Gorenstein.

Their set is
$\mathcal P_d^{(s)}=\{x\in\mathbb R_{\ge0}^d:
 x_i+x_{i+1}\le s+\delta_i,\ 1\le i\le d-1\}$,
where $\delta_i=0$ for odd $i$ and $\delta_i=1$ for even $i$.
The Gorenstein characterization used here is the source's interior-lattice
translation condition: some integer $q\ge1$ and $c\in\mathbb Z^d$ satisfy
$\operatorname{int}((n+q)P)\cap\mathbb Z^d
=c+(nP\cap\mathbb Z^d)$ for every integer $n\ge0$.

## Motivation

`D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.result`
proves that for every $s\ge2$ and $r\ge1$ the condition holds exactly when
$(s,r)=(3,1)$. This settles both the characterization and the stated
$s=3$, $d\ge4$ conjecture. Preregistration #14591 fixes the source,
quantifiers and Lean conventions. The source note is
`Library/Geometry/jiangwenzhong2026alternating.md`.

## Gap

The literature readings attributed to the Claude Code orchestrator in
#14591 found only arXiv v1, no matching MathDB page in the stated title,
author and Gorenstein searches, and no resolution in the later
same-author paper arXiv:2607.22008, which studies a different family.
These readings establish absence within their searched scope; they do
not establish an exhaustive priority claim.

## Route

At $n=0$, the translation identity makes $c$ the unique interior lattice
point of $qP$. Every coordinate of $c$ is at least one, hence $qs\ge3$.
The all-ones vector belongs to the interior, so uniqueness gives
$c=\mathbf1$. If $qs\ge4$, the vector $(2,1,\ldots,1)$ is a different
interior lattice point. Thus $qs=3$; with $s\ge2$ this forces $q=1$
and $s=3$.

For $d\ge3$, put $w=(1,4,3,1,\ldots,1)$. Its adjacent sums are
$5,7,4,2,\ldots$, strictly below the corresponding capacities
$6,8,6,8,\ldots$ of $2P$. But the second adjacent sum of
$w-\mathbf1$ is $3+2=5>4$. The $n=1$ identity is impossible.
For $d=2$, the triangle $P=\{(u,v)\ge0:u+v\le3\}$ has the required
identity with $q=1$ and $c=(1,1)$: integral strict inequalities at scale
$n+1$ become the non-strict inequalities at scale $n$ after translation.
The actual zero dilation is included.

## Falsifier

A different parity convention, relative rather than ambient interior,
a different lattice, or omission of $n=0$ changes the encoded problem.
The public definitions use the literal adjacent inequalities, Mathlib
ambient `interior`, real set dilation and pointwise integer casts.
A single Gorenstein pair with $s\ge2$, $r\ge1$, different from $(3,1)$
would contradict `result` under these definitions.

## Evidence

The module contains `result : claim`, with
$\forall s,r\in\mathbb N,\ s\ge2\Rightarrow r\ge1\Rightarrow
(\operatorname{IsGorenstein}(s,2r)\iff s=3\land r=1)$.
Its private lemmas `index_center` and `not_gorenstein_large_dimension`
provide the uniqueness and parametric obstruction used by `result`;
`gorenstein_three_two` supplies the positive direction for every dilation.
The axiom closure of every public declaration is contained in
$\{\texttt{propext},\texttt{Classical.choice},\texttt{Quot.sound}\}$.
The source-to-Lean interpretation is the convention stated in #14591;
equivalence to other algebraic definitions of Gorenstein polytopes is not
separately formalized.

## Triage

### What the settlement shows

1. **Mechanism — proved in this module.** `index_center` handles every
   $s\ge2$ and $d\ge2$, and forces $q=1$, $s=3$, $c=\mathbf1$ from the
   translation identity. `not_gorenstein_large_dimension` uses the
   parametric $w$ for every $d\ge3$. The obstruction is one adjacent-sum
   excess after translation, caused by the alternating capacities;
   it does not require an Ehrhart-series computation.
2. **Odd dimensions — paper argument from kernel-checked lemmas.** For
   any $s\ge2$ and $d\ge3$, `index_center` reduces a supposed Gorenstein
   translation to $s=3$; `not_gorenstein_large_dimension` then contradicts
   it. This includes every odd $d\ge3$. The general-dimensional lemmas
   are in the module; a separate public odd-dimensional theorem is not
   claimed. Dimension one is outside the source's domain.
3. **The $s=1$ family — paper argument.** The source's Theorem 1.9
   (`thm-gorenstein-s1`) remains valid: for even $d=2r$, the even-indexed
   capacity-two constraints follow from the adjacent disjoint
   capacity-one pairs. Thus $P$ is the product of $r$ unit triangles.
   For one triangle, positive integral coordinates in $(n+3)P$ obey
   $u+v\le n+2$; subtracting $(1,1)$ gives $u',v'\ge0$ and
   $u'+v'\le n$. Products give index $3$ and center $\mathbf1$ for
   every $r\ge1$. This source proof is not a new Lean declaration here.
4. **$h^*$ palindromicity — paper argument and exact finite computation.**
   The eight explicit rows for $s=2,3,4$ in Remark 3.18 agree with the
   characterization: only the $(s,d)=(3,2)$ row is palindromic. The
   columns at $d=8$ are ellipses, not printed vectors. The exact
   computation below supplies all twelve cases
   $s\in\{2,3,4\}$, $d\in\{2,4,6,8\}$, and matches all eight printed
   rows. It also checks $s=1$, $d\in\{2,4,6,8\}$ and the obstruction
   vector for every $3\le d\le32$. These are finite computations;
   the unbounded classification is `result`. A general theorem about
   $h^*$ coefficients is not proved in this module.

The answer strengthens the source's Corollary 3.24 from eventual failure
to failure in every even dimension except the unique pair, and proves the
$s=3$ extension beyond dimensions four and six. The source's
transfer-matrix and Ehrhart identities, and its independent $s=1$
theorem, keep their stated hypotheses and conclusions. Q2 on unimodality
and real-rootedness remains open; this module does not settle it.

### Exact finite computation

The computation is by the implementation seat. Command:
`python3 /tmp/op-jwz/check.py`; exit code $0$.
The script can be saved from the complete source below and run using
Python's standard library. SHA-256: `aafca8eecdaab339085feb4e6a0164f5fe208b7c73a35ecb1f54f2b77dd8f030`.

For each $s,d$, the recurrence enumerates every admissible integral
coordinate prefix by its last coordinate. At dilation $n$, the adjacent
capacity is $n(s+\delta_i)$, and prefix sums count every allowed
predecessor exactly once. It computes $L(n)$ for $0\le n\le d$ and
$h_k^*=\sum_{j=0}^k(-1)^j\binom{d+1}{j}L(k-j)$.
Trailing zero coefficients are omitted from the displayed vectors.

| $s$ | $d$ | $h^*$ vector | Palindromic |
| --- | --- | --- | --- |
| 2 | 2 | $(1, 3)$ | no |
| 2 | 4 | $(1, 30, 55, 9)$ | no |
| 2 | 6 | $(1, 197, 1818, 2786, 811, 27)$ | no |
| 2 | 8 | $(1, 1180, 36610, 196846, 274966, 106075, 9271, 81)$ | no |
| 3 | 2 | $(1, 7, 1)$ | yes |
| 3 | 4 | $(1, 90, 284, 94, 1)$ | no |
| 3 | 6 | $(1, 893, 13714, 31436, 14273, 973, 1)$ | no |
| 3 | 8 | $(1, 8516, 456928, 3528084, 6770616, 3653018, 492328, 9692, 1)$ | no |
| 4 | 2 | $(1, 12, 3)$ | no |
| 4 | 4 | $(1, 205, 859, 381, 9)$ | no |
| 4 | 6 | $(1, 2919, 59352, 166411, 92672, 8442, 27)$ | no |
| 4 | 8 | $(1, 40746, 2986812, 27845877, 62524368, 39514968, 6452988, 174132, 81)$ | no |
| 1 | 2 | $(1,)$ | yes |
| 1 | 4 | $(1, 4, 1)$ | yes |
| 1 | 6 | $(1, 20, 48, 20, 1)$ | yes |
| 1 | 8 | $(1, 72, 603, 1168, 603, 72, 1)$ | yes |

```python
from math import comb
import json


def lattice_count(s, d, n):
    """Exact enumeration by the last coordinate; all states are integers."""
    assert s >= 1 and d >= 2 and n >= 0
    counts = [1] * (n * s + 1)
    for i in range(1, d):
        capacity = n * (s + (i % 2 == 0))
        prefix = []
        total = 0
        for count in counts:
            total += count
            prefix.append(total)
        counts = [prefix[min(capacity - y, len(prefix) - 1)]
                  for y in range(capacity + 1)]
    return sum(counts)


def hstar(s, d):
    ehrhart = [lattice_count(s, d, n) for n in range(d + 1)]
    coefficients = [sum((-1) ** j * comb(d + 1, j) * ehrhart[k - j]
                        for j in range(k + 1)) for k in range(d + 1)]
    assert all(c >= 0 for c in coefficients)
    while coefficients[-1] == 0:
        coefficients.pop()
    return coefficients


source_rows = {
    (2, 2): [1, 3],
    (2, 4): [1, 30, 55, 9],
    (2, 6): [1, 197, 1818, 2786, 811, 27],
    (3, 2): [1, 7, 1],
    (3, 4): [1, 90, 284, 94, 1],
    (3, 6): [1, 893, 13714, 31436, 14273, 973, 1],
    (4, 2): [1, 12, 3],
    (4, 4): [1, 205, 859, 381, 9],
}
rows = []
for s in (2, 3, 4):
    for d in (2, 4, 6, 8):
        h = hstar(s, d)
        if (s, d) in source_rows:
            assert h == source_rows[s, d]
        palindromic = h == h[::-1]
        assert palindromic == (s == 3 and d == 2)
        rows.append(dict(s=s, d=d, hstar=h, palindromic=palindromic))
for d in (2, 4, 6, 8):
    h = hstar(1, d)
    assert h == h[::-1]
    rows.append(dict(s=1, d=d, hstar=h, palindromic=True))
for d in range(3, 33):
    w = [1, 4, 3] + [1] * (d - 3)
    assert all(a > 0 for a in w)
    assert all(w[i] + w[i + 1] < 2 * (3 + ((i + 1) % 2 == 0))
               for i in range(d - 1))
    shifted = [a - 1 for a in w]
    assert shifted[1] + shifted[2] > 4
print(json.dumps(dict(rows=rows, source_rows_checked=len(source_rows),
                     witness_dimensions=[3, 32]), indent=2))
```

## ASSUMED-UNVERIFIED

- Worldwide prior-art completeness beyond the literature searches stated
  in #14591 is unverified; no priority claim is made.
- The separate algebraic equivalence of the stipulated interior-lattice
  translation condition is not formalized here.
- Q2 and uniform $h^*$ coefficient properties beyond the supplied
  classification remain open.
