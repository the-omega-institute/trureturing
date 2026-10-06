---
slug: fang-fu-kitaev-li-su-sun-2026-class69-involutions
bibkey: fangfukitaevlisusun2026mesh
doi: 10.48550/arXiv.2606.14367
url: https://arxiv.org/abs/2606.14367v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.result
---

# Class 69 Mesh Patterns Are Not Equidistributed on Involutions

## Problem

Q. Fang, S. Fu, S. Kitaev, H. Li, X. Su and Z. Sun, *On mesh patterns of short length: Equidistribution and enumeration*, arXiv:2606.14367v1, Concluding remarks, Conjecture 1:

> The patterns in the set {\pattern{scale=0.5}{2}{1/1,2/2}{1/2,1/1,2/1,0/0}, \pattern{scale=0.5}{2}{1/1,2/2}{2/2,0/1,1/1,1/0}, \pattern{scale=0.5}{2}{1/1,2/2}{0/2,1/1,2/1,1/0}, \pattern{scale=0.5}{2}{1/1,2/2}{1/2,0/1,1/1,2/0}} are equidistributed on involutions. (The first two patterns, as well as the last two patterns, are trivially equidistributed via the composition of reverse and complement.)

The macro shades the unit box with lower-left corner `(x,y)` for each `x/y` in its fourth argument; the dots are at `(1,1)` and `(2,2)`. Let `R0`, `R1`, `R2`, `R3` denote those shaded-cell sets in that order. Equidistribution requires equal numbers of involutions having exactly `k` occurrences, for every length `n`, count `k`, and pair of pattern indices.

## Motivation

The frozen declaration `D5/S3/Combinatorics/MeshPattern/Class69InvolutionRefutation.result` proves the negation of that universal claim. At length three the avoidance counts for `R0` and `R2` are respectively two and one.

## Gap

Preregistration issue #12885 quotes the source and its macro, specifies the full quantified claim and the refutation route, and records a Tier 1 literature screen. The arXiv record has only v1. The follow-up papers arXiv:2607.04111v1 and arXiv:2609.13764v1 contain no occurrence of “involution”; the checked MathDB entry 375296 lists zero solutions. The bounded screen does not establish worldwide priority.

## Route

Represent permutations by `Equiv.Perm (Fin n)` and involutions by the existing equation `s * s = 1`. For increasing positions `i < j` with increasing values, every other point must lie outside the shaded cells. Its relative box is the pair of the numbers of selected positions and selected values below it. Count occurrences by filtering the Cartesian product of positions. The proof specialises the universal equality to `n = 3`, `k = 0`, `a = 0`, `b = 2`, enumerates the six permutations through a locally certified bijection with `Fin 6`, and uses kernel evaluation to contradict the equality. There are no extra public identity or symmetry theorems.

## Falsifier

The refutation would fail if the literal source shading or the occurrence convention gave equal avoidance counts for the four involutions of length three. The complete occurrence vectors are:

| involution | R0 | R1 | R2 | R3 |
| --- | --- | --- | --- | --- |
| 123 | 1 | 1 | 2 | 2 |
| 132 | 0 | 2 | 1 | 1 |
| 213 | 2 | 0 | 1 | 1 |
| 321 | 0 | 0 | 0 | 0 |

## Evidence

**Proved in this module:** `result : ¬ claim`, with all lengths, occurrence counts and pattern pairs retained in `claim`. The proof uses no private top-level lemma, `native_decide`, `sorry`, or additional axiom.

**Computed:** an independent Python enumeration generates involutions recursively by fixing the smallest unused index or pairing it with each other unused index. For each increasing pair it computes all other relative boxes and tests intersection with each shaded-cell set. Command: `python3 /Users/auric/.sshx/f3fc2666c08d5f9f62d5d79a/attempt-1/class69_check.py`. The independently executed program is:

```python
import json
from collections import Counter
R=[{(1,2),(1,1),(2,1),(0,0)}, {(2,2),(0,1),(1,1),(1,0)}, {(0,2),(1,1),(2,1),(1,0)}, {(1,2),(0,1),(1,1),(2,0)}]
def involutions(n):
 s=list(range(n))
 def gen(left):
  if not left:
   yield tuple(s); return
  i,*rest=left
  yield from gen(rest)
  for j in rest:
   s[i],s[j]=j,i
   yield from gen([k for k in rest if k!=j])
   s[i],s[j]=i,j
 yield from gen(list(range(n)))
def occurrences(s):
 counts=[0]*4
 for i in range(len(s)):
  for j in range(i+1,len(s)):
   if s[i]>=s[j]: continue
   boxes={(int(i<r)+int(j<r),int(s[i]<s[r])+int(s[j]<s[r])) for r in range(len(s)) if r!=i and r!=j}
   for a in range(4): counts[a]+=not bool(boxes & R[a])
 return counts
readings=[]
for n in range(1,12):
 distributions=[Counter() for _ in range(4)]
 for s in involutions(n):
  values=occurrences(s)
  for a,k in enumerate(values): distributions[a][k]+=1
  if n==3: print(json.dumps({'permutation':[x+1 for x in s],'occurrences':values}),flush=True)
 assert distributions[0]==distributions[1] and distributions[2]==distributions[3]
 assert (distributions[0]!=distributions[2])==(n>=3)
 row={'n':n,'involutions':sum(distributions[0].values()),'avoidance':[d[0] for d in distributions]}
 readings.append(row);print(json.dumps(row),flush=True)
print(json.dumps({'symmetry':{'R0_transpose':{(y,x) for x,y in R[0]}==R[0],'R1_transpose':{(y,x) for x,y in R[1]}==R[1],'R2_transpose_R3':{(y,x) for x,y in R[2]}==R[3],'R0_reverse_complement_R1':{(2-x,2-y) for x,y in R[0]}==R[1]}}))
```

It reproduces the table above, the full-distribution pair equalities, and the following avoidance counts:

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| R0 and R1 | 1 | 1 | 2 | 4 | 12 | 35 | 116 | 390 | 1407 | 5222 | 20348 |
| R2 and R3 | 1 | 1 | 1 | 2 | 6 | 18 | 58 | 203 | 735 | 2824 | 11176 |

The OEIS JSON searches for the complete sequences `1,1,2,4,12,35,116,390,1407,5222,20348` and `1,1,1,2,6,18,58,203,735,2824,11176` each returned HTTP 200 with JSON `null` (no matching result in those queries).

## Triage

Tier 1; Refuted under the external open-problem-resolution basis of CLAUDE.md §3.2, preregistered in #12885. The settling theorem is honestly classified as bind-only finite evaluation. Information-escape registration is paused under CLAUDE.md §3.9.

### What the settlement shows

- **Proved in this module:** the involution-restricted four-pattern equidistribution fails. **Computed mechanism:** the unequal avoidance fibre: `132` avoids `R0` and contains `R2`, while `321` avoids both.
- **Proved consequence, using the literature theorem:** the full-symmetric-group equidistribution of Class 69 survives (Z.-R. Zhang and H. Zhao, *The last distribution-equivalence class of mesh patterns of length 2*, arXiv:2607.04111v1, Theorem 1.1). Their marked-occurrence bijection establishes the unrestricted identity; it cannot preserve involutions in the sense needed to restrict that identity to the four involution distributions, since such a restriction would contradict `result`. This is not a new formal theorem of this module.
- **Proved by symmetry, outside this module:** transposition fixes `R0` and `R1` separately and exchanges `R2` with `R3`. Reflecting the permutation plot across its diagonal gives the inverse permutation and exchanges position and value box coordinates. Since an involution equals its inverse, its `R2` and `R3` occurrence counts agree pointwise. Transposition alone does not identify `R0` with `R1`.
- **Proved by symmetry, outside this module:** reverse–complement maps `R0` to `R1`, preserving the increasing underlying pattern. On permutations it is conjugation by the longest permutation `w`; `(w s w)^2 = w s^2 w`, so it bijects involutions. Hence the `R0` and `R1` distributions agree on involutions at every length. Both within-pair equidistributions survive; formalising these symmetry arguments is a separate candidate.
- **Computed:** for every `3 ≤ n ≤ 11`, the four distributions split into exactly `{R0,R1}` and `{R2,R3}`. **Open:** proving that the two pair distributions differ at every `n ≥ 3`, or finding a later coincidence. Finite enumeration does not resolve this unbounded question.
- **Computed:** the two avoidance sequences above have no matches in the specified OEIS queries. **Open:** formulas, recurrences and generating functions for those sequences.
- **Boundary of the source results:** the refutation rejects Conjecture 1; it does not affect the source's unconditional enumeration and equidistribution theorems or Zhang–Zhao's unrestricted Class 69 theorem. Any claim requiring Conjecture 1 as a hypothesis must retain that hypothesis or be re-established separately; no further such dependency was established by this delivery.

## ASSUMED-UNVERIFIED

Literature novelty is bounded by the screen recorded in #12885 and the stated arXiv versions. The symmetry arguments are ordinary mathematical proofs, not kernel-checked declarations in this module. The computations through length eleven do not prove any claim at larger lengths. OEIS no-hit is specific to the two exact queries.
