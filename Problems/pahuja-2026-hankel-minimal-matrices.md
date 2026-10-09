---
slug: pahuja-2026-hankel-minimal-matrices
bibkey: pahuja2026minimalinversions
doi: null
url: https://arxiv.org/abs/2602.14931v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.result
---

# Minimal matrices of fixed RSK shape need not be Hankel

## Problem

Nimisha Pahuja, *Minimal Inversions in Integer Matrices of Fixed RSK Shape*,
arXiv:2602.14931v1, Conjecture 1.1, asserts that every minimal nonnegative
integer $n\times n$ matrix whose shape is a partition with exactly $n$
positive parts is symmetric and Hankel. Minimality compares the inversion
count $I(M)=\sum_{i<k,\,j>l}m_{i,j}m_{k,l}$ against all matrices of that shape.
The Hankel clause asks for integers $s_2,\ldots,s_{2n}$ with $m_{i,j}=s_{i+j}$.
The shape is that of the insertion tableau of the lexicographic matrix
biword, with the first strictly larger entry bumped during row insertion.

## Motivation

`D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.result`
proves the negation of this conjunction. The nonempty shape class
$(8,8,1,1)$ has a minimum, and every minimizer in that class is non-Hankel.
The source and definitions are recorded in preregistration #14454.
The literature note is `Library/PermutationPatterns/pahuja2026minimalinversions.md`.

## Gap

The literature readings in #14454 report arXiv v1 as the only version,
MathDB `/p/373166` with status open and zero solutions, and no settlement
in the searched repository or formal-conjectures collection. Those are
orchestrator-attributed readings, not an exhaustive priority claim.
The settled clause is Hankel; symmetry of minimizers is a separate question.

## Route

Use
$K_3=\begin{pmatrix}0&3&0&1\\3&0&2&0\\0&2&0&3\\1&0&3&0\end{pmatrix}$.
Its shape is $(8,8,1,1)$ and its inversion count is $43$. Insertion preserves
word length, so every Hankel matrix of this shape has total entry weight
$18$. Its seven nonnegative parameters have weighted sum
$t_0+2t_1+3t_2+4t_3+3t_4+2t_5+t_6=18$.
Complete weighted-composition enumeration and nineteen kernel-decided
chunks show that every such Hankel matrix has inversion count at least
$45$. Natural-number well-ordering supplies a minimizer. Its cost is at most
$43$, so it cannot be Hankel. The integer sequence in the source is recovered
from the nonnegative matrix entries; no nonnegativity assumption is added
on unused sequence values.

## Falsifier

A mismatch between the source's lexicographic biword, strict bumping,
inversion sum or comparison class and the encoded convention would invalidate
the source interpretation. The numeric contradiction requires $43<45$ and
complete coverage of every Hankel matrix of the target shape. Both sides and
the enumeration completeness are in the kernel-checked proof. The proof
neither assumes that $K_3$ is minimal nor asserts it.

## Evidence

The Lean module is
`D5/S3/Combinatorics/Permutation/RSKMinimalInversionHankelRefutation.lean`.
`K3_shape` and `K3_inv` certify the comparison matrix. `insertionTableau_size`
and `shape_size` preserve total weight; `weightedComps_complete` and
`baseChunk_complete` prove coverage; `hankel_lower_base` proves the Hankel
bound. `base_minimizer_exists` and `base_minimizer_not_hankel` close `result`.
The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

The following exact Python computation is reproducible as `python3 check.py`
after saving this code block as `check.py`. The executed command was
`python3 /tmp/op-pahuja/check.py`, exit $0$; SHA-256 `83961293d081d391c2bd5c95f3765441432efb7cd6617c3d4de4d137771095a9`.

```python
import itertools,bisect
def rsk_shape(M):
    n=len(M); word=[j for i in range(n) for j in range(n) for _ in range(M[i][j])]
    P=[]
    for x in word:
        for row in P:
            k=bisect.bisect_right(row,x)   # leftmost entry strictly greater than x
            if k==len(row): row.append(x); x=None; break
            row[k],x=x,row[k]
        if x is not None: P.append([x])
    return tuple(len(r) for r in P)
def inv(M):
    n=len(M); return sum(M[i][j]*M[k][l] for i in range(n) for j in range(n) for k in range(n) for l in range(n) if i<k and j>l)
def K(a): return [[0,a,0,1],[a,0,2,0],[0,2,0,a],[1,0,a,0]]
for a in range(3,8):
    M=K(a); print('a',a,'shape',rsk_shape(M),'inv',inv(M),'formula',2*a*a+4*a+13)
# all Hankel 4x4 with total 18 and shape (8,8,1,1) for a=3
w=[1,2,3,4,3,2,1]; tot=18; costs=[]; cnt=0
def rec(t,rem,s):
    global cnt
    if t==7:
        if rem==0:
            cnt+=1
            M=[[s[i+j] for j in range(4)] for i in range(4)]
            if rsk_shape(M)==(8,8,1,1): costs.append((inv(M),tuple(s)))
        return
    for v in range(rem//w[t]+1): rec(t+1,rem-v*w[t],s+[v])
rec(0,tot,[])
print('hankel tuples',cnt,'with shape (8,8,1,1):',len(costs),sorted(c for c,_ in costs))
# sanity: transposition invariance of shape on random matrices; and small exhaustive check that a minimizer of shape (8,8,1,1) has cost<=43 exists (K_3)
import random
random.seed(1)
for _ in range(200):
    M=[[random.randint(0,3) for _ in range(4)] for _ in range(4)]
    T=[list(r) for r in zip(*M)]
    assert rsk_shape(M)==rsk_shape(T)
print('transpose-invariance sanity ok')
```

Its output for $a=3,4,5,6,7$ is respectively shapes
$(8,8,1,1)$, $(10,10,1,1)$, $(12,12,1,1)$, $(14,14,1,1)$,
$(16,16,1,1)$ and inversion counts $43,61,83,109,139$.
There are $2743$ weighted Hankel tuples of total $18$; exactly eight have
shape $(8,8,1,1)$, with costs $45,45,49,49,57,57,69,69$.
The $200$ seeded transpose tests are a sanity check only, not an exhaustive
check of minimizers or a proof of general transposition invariance.

## Triage

Tier 1; Conjecture 1.1 is **Refuted**, through its Hankel clause.
The admission basis is `open-problem-resolution (#14454; Refuted)`.
Utility is `kind=certified-instance; basis=refutes` with `claim` and `result`.
Information-escape registration is paused under CLAUDE.md section 3.9.

### What the settlement shows

- **Proved in this module (kernel): base instance.** `K3_shape`, `K3_inv`,
  `hankel_lower_base`, `base_minimizer_exists`, `base_minimizer_not_hankel`
  and `result` establish shape $(8,8,1,1)$, comparison cost $43$, Hankel
  lower bound $45$, existence of a minimizer and failure of the conjecture.
- **Computed: family at $a=3,\ldots,7$.** The script in Evidence verifies
  $\operatorname{shape}(K_a)=(2a+2,2a+2,1,1)$ and
  $I(K_a)=2a^2+4a+13$, where
  $K_a=\begin{pmatrix}0&a&0&1\\a&0&2&0\\0&2&0&a\\1&0&a&0\end{pmatrix}$.
  The command, exit and SHA-256 are those in Evidence.
- **Proved on paper, not kernel-checked: uniform family.** For $a\ge3$,
  the maximum weights of unions of $1,2,3,4$ increasing chains in $K_a$
  are $2a+2,4a+4,4a+5,4a+6$. To see the bounds, its middle anti-diagonal
  has four incomparable groups of weights $1,2,2,1$; two chains must omit
  at least two units and three must omit at least one. A single path has
  at most one group of weight $a$ before and after that anti-diagonal,
  and at most two units on it. These bounds are attained: for two chains
  take $(1,2),(2,3),(3,4)$ and $(2,1),(3,2),(4,3)$; a third chain can take
  $(1,4)$, and a fourth $(4,1)$. Coordinates here are one-based.
  Greene's theorem gives the stated shape. Direct summation of inversion
  pairs gives $I(K_a)=2a^2+4a+13$.
- **Proved on paper, not kernel-checked: uniform Hankel form and bound.**
  For a nonnegative Hankel $4\times4$ matrix with anti-diagonal parameters
  $t_0,\ldots,t_6$, unions of $k$ increasing paths meet at most $k$ entries
  of each anti-diagonal. Nested paths attain these bounds, so Greene's
  row lengths are $t_0+\cdots+t_6$, $t_1+\cdots+t_5$,
  $t_2+t_3+t_4$, $t_3$. At shape $(2a+2,2a+2,1,1)$ this forces
  $t_0=t_2=t_4=t_6=0$, $t_3=1$ and $t_1+t_5=2a+1$.
  Thus the matrix is
  $\begin{pmatrix}0&x&0&1\\x&0&1&0\\0&1&0&y\\1&0&y&0\end{pmatrix}$,
  with $x+y=2a+1$. Its inversion count is
  $x^2+y^2+2x+2y+6$, minimized at $\{x,y\}=\{a,a+1\}$;
  the minimum is $2a^2+6a+9$.
- **Proved on paper, not kernel-checked: uniform gap.** Subtracting the
  comparison cost gives $2(a-2)>0$ for every $a\ge3$. Every minimizer of
  each family shape is non-Hankel. **Open:** a kernel formalization beyond
  the base instance $a=3$.
- **Proved on paper, not kernel-checked: mechanism.** The unequal masses
  $1,2,2,1$ on the four central positions retain the Greene chain weights
  above while reducing inversion cost. Hankel equality forces the four
  central masses to agree and moves mass to the adjacent anti-diagonals;
  their inversion pairs contribute the quadratic terms $x^2+y^2$.
  RSK shape alone does not impose the anti-diagonal equality needed by
  the conjecture. A minimum restricted to Hankel matrices does not give
  a minimum over all matrices.
- **Open: symmetry clause.** The displayed $K_3$ is symmetric
  by its entries. **Open:** whether some minimizer of shape $(8,8,1,1)$ is
  symmetric; whether every minimizer is symmetric; the exact minimum and
  whether $K_3$ attains it. No exhaustive minimizer search is asserted.
- **Literature reading / paper argument: two-row theorem.** The source's
  Theorem 4.1 proves the conjecture for two-row partitions. That theorem
  stands: this counterexample has four positive parts. It is not on this
  module's dependency path and is not formalized here.
- **Literature reading: dependent source conclusions.** Theorem 1.2 and
  Section 4's proposed general minimum formula explicitly assume the
  conjecture. Their conditional statements remain conditional; the
  hypothesis is false in general, so those arguments supply no
  unconditional formula for all shapes. The Greene relations for Hankel
  matrices used above remain valid within their stated restricted class.

## ASSUMED-UNVERIFIED

The uniform Greene and inversion arguments above are paper proofs, not Lean
proofs. The literature checks are those attributed to the orchestrator in
#14454; no exhaustive novelty or model-diversity claim is made. Symmetry of
minimizers and the exact unrestricted minimum remain open.
