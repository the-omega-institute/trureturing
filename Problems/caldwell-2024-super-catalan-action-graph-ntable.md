---
slug: caldwell-2024-super-catalan-action-graph-ntable
bibkey: caldwell2024actiongraphs
doi: 10.48550/arXiv.2507.22719
url: https://arxiv.org/abs/2507.22719v1
triage: theorem
motivation_gids:
  - D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.result
---

# Caldwell and coauthors' super Catalan action-graph identity

## Problem

D. Caldwell, A. Cochran, N. Glisson, B. Jennings, K. McDicken, L. Proctor,
S. Klanderman and A. Tebbe, *Catalan Number Sequences and Generalized Action
Graphs*, Ball State Undergraduate Mathematics Exchange **18**(1), Fall 2024,
88–106, [Conjecture 5](https://openjournals.bsu.edu/mathexchange/article/view/5831);
[arXiv:2507.22719v1](https://arxiv.org/abs/2507.22719v1), Conjecture 5.6:

> The subsequent super Catalan number can be computed from the n-table of its previous action graph via S(0, n + 1) = Σ_{ℓ=0}^{n} (2/2^ℓ) Σ_{v=0}^{n} Kℓ,v,n.

For every $n\ge0$, with precisely the graphs of Definition 5.2 and the path
counts of Definition 5.4, the named assertion is

$$S(0,n+1)=\sum_{\ell=0}^{n}\frac{2}{2^\ell}\sum_{v=0}^{n}K_{\ell,v,n}.$$

Here Definition 5.1 is used literally:
$S(m,n)=(2m)!(2n)!/(m!n!(m+n)!)$, in $\mathbb Q$.
Preregistration: [#14721](https://github.com/the-omega-institute/trureturing/issues/14721), CALD-1.

## Motivation

The frozen declaration
`D5/S3/Combinatorics/Graph/SuperCatalanActionGraphRecurrence.result`
proves the unconditional assertion for every natural $n$, including zero.
The graph encoding retains distinct vertices as child-list occurrences;
repeated equal subtrees retain multiplicity. Every growth count uses the old
tree. Natural division in `grow` is exact on all subtrees of `G n` by the
private `good_G` and `good_integral` invariant.

## Gap

The source displays an unproved identity and verifies its $n=3$ instance.
MathDB [p/369567](https://mathdb.com/p/369567) has a posted discussion proof of
Conjecture 5.5, the per-label recurrence and integrality. That proof is
acknowledged; it does not supply the all-$n$ binomial column formula or the
weighted identity of Conjecture 5.6. The preregistration's bounded literature
reading found no posted solution at [p/369568](https://mathdb.com/p/369568).
This is bounded literature evidence, not a claim of exhaustive originality.

## Route

The recursive private invariant `Good` gives bounded labels, divisibility
$2^r\mid p_n(x,r)$, zero path counts for $r>n$, and the same facts for every
child subtree. `good_grow` preserves it, so the graph construction is integral.
Deleting the last edge yields `paths_grow_succ`; summing over all starting
vertices yields `totalPaths_grow_zero` and `totalPaths_grow_succ`.
Induction gives `totalPaths_closed`, and `pathsFrom_sum` partitions the
starting vertices by label. Thus `column_closed` identifies the table columns.
The delivered proof uses Mathlib's `Nat.sum_range_add_choose` through `hockey`,
`Nat.choose_succ_succ'` and `Nat.choose_symm_half` through `central_step`, and
`Nat.cast_choose` through `S_zero` to finish the identity.

## Falsifier

A natural $n$ violating the displayed weighted identity would refute CALD-1.
A discrepancy between the old-tree growth counts and Definition 5.2, loss of
vertex multiplicity, or omission of a starting vertex in Definition 5.4 would
invalidate the encoding. The Lean proof checks the universal identity for the
literal definitions; the exact rational computation below independently
checks the source tables and the stated finite scope.

## Evidence

**Proved in this module:** `result : claim`, with no extra hypotheses.
Its axiom closure is contained in $\{\mathrm{propext},\mathrm{Classical.choice},
\mathrm{Quot.sound}\}$.

**Computed:** `python3 /tmp/op-cald/check.py 10`, exit **0**.
SHA-256: `55f1dee53b933bdfac6063b66894a4fb38f63cbbfd2057b87de732aa3c18cb96`.
The complete script is included below; it uses only Python's standard library.
Saving the code block as `check.py` and running `python3 check.py 10` reproduces
these readings: the source tables for $G_3$ and $G_4$, the weighted identity
for $n=0,\ldots,9$, all their column formulas, the exact divisions in constructing
$G_0,\ldots,G_{10}$, and root multiplicities for $k=1,\ldots,9$.
The printed root sequence is $2,2,4,10,28,84,264,858,2860$.

```python
# Literal Definition 5.2 as a rooted labeled tree; K per Definition 5.4; checks Conjecture 5.6 and Tables 4-6.
import sys
from fractions import Fraction as Fr
from math import comb, factorial
sys.setrecursionlimit(100000)
class T:
    __slots__=('a','cs')
    def __init__(s,a,cs): s.a=a; s.cs=cs
def p(t,l,tg):
    if l==0: return 1 if t.a==tg else 0
    return sum(p(c,l-1,tg) for c in t.cs)
def grow(n,t):
    cnt=0
    for l in range(n+1):
        q=p(t,l,n)*2
        assert q % 2**l==0, (n,l,q)
        cnt+=q//2**l
    return T(t.a,[grow(n,c) for c in t.cs]+[T(n+1,[]) for _ in range(cnt)])
def K(t,l,v,tg):
    return (p(t,l,tg) if t.a==v else 0)+sum(K(c,l,v,tg) for c in t.cs)
def S(m,n): return Fr(factorial(2*m)*factorial(2*n), factorial(m)*factorial(n)*factorial(m+n))
G=[T(0,[])]
N=int(sys.argv[1]) if len(sys.argv)>1 else 7
for n in range(N): G.append(grow(n,G[n]))
tab3=[[K(G[3],l,v,3) for v in range(4)] for l in range(4)]
tab4=[[K(G[4],l,v,4) for v in range(5)] for l in range(5)]
assert tab3==[[0,0,0,20],[4,4,12,0],[8,8,0,0],[8,0,0,0]], tab3
assert tab4==[[0,0,0,0,70],[10,8,12,40,0],[20,16,24,0,0],[24,16,0,0,0],[16,0,0,0,0]], tab4
ok=0
for n in range(N):
    rhs=sum(Fr(2,2**l)*sum(K(G[n],l,v,n) for v in range(n+1)) for l in range(n+1))
    assert rhs==S(0,n+1),(n,rhs); ok+=1
    for l in range(n+1): assert sum(K(G[n],l,v,n) for v in range(n+1))==2**l*comb(2*n-l,n)
print(f"CONJ56_OK n=0..{N-1} ({ok} cases); tables 4-6 reproduced; column sums = 2^l*binom(2n-l,n)")
# root multiplicities z_n (children of the root labeled n) vs 2*Catalan(n-1)
z=[sum(1 for c in G[N-1].cs if c.a==k) for k in range(1,N)]
assert z==[2*comb(2*(k-1),k-1)//k for k in range(1,N)], z
print("ROOT_MULT z_1..z_%d ="%(N-1), z, "= 2*Cat(n-1)")
```

## Triage

### What the settlement shows

1. **Mechanism — proved in this module.** For $0\le\ell\le n$, private
   `column_closed`, using `totalPaths_closed` and `pathsFrom_sum`, proves
   $$A_{\ell,n}=\sum_{v=0}^{n}K_{\ell,v,n}
     =2^\ell\binom{2n-\ell}{n}.$$
   The weighted sum is consequently
   $$2\sum_{\ell=0}^{n}\binom{2n-\ell}{n}
     =2\binom{2n+1}{n+1}=\binom{2n+2}{n+1}=S(0,n+1).$$
   The last equality and the whole identity are kernel checked by `result`.

2. **Axiom 1 for Definition 5.2 — proved by a paper counting argument.**
   Every old vertex $x$ receives exactly
   $\sum_{\ell=0}^{n}p_n(x,\ell)2/2^\ell$ distinct new children labeled
   $n+1$. The invariant makes every summand integral. All old labels are at
   most $n$, so these children are exactly the vertices labeled $n+1$ in the
   next graph. Sum over old vertices and partition them by labels
   $v=0,\ldots,n$: the count becomes the weighted table sum in `claim`.
   `result` identifies it with $S(0,n+1)$. The initial graph has one vertex
   labeled zero, equal to $S(0,0)=1$. This proves the counting half of
   Conjecture 5.3 for these specific graphs. This graph-count assertion is a
   complete paper consequence, not an additional exported Lean theorem.

3. **Conjecture 5.5 — proved in posted literature, not claimed as a new
   result here.** MathDB p/369567 contains a discussion proof by Shivam Patel
   of the per-label path recurrence and integrality. Removing the last edge
   and concatenating its old prefix with an old continuation gives the same
   vertex mechanism as the delivered private `paths_grow_succ`. The posted
   argument then sums over starting vertices with one fixed label. Its
   independent published corroboration is unverified; the Lean proof here
   checks the recurrence it actually uses.

4. **Axiom 2 of Conjecture 5.3 — proved by a paper induction.** Every edge
   strictly increases labels: only vertices labeled $n+1$ are appended at
   stage $n+1$, to vertices labeled at most $n$. A vertex born with label $j$
   has at stage $j$ the one-vertex subtree $G_0$, with its label shifted by
   $j$. Suppose at stage $n\ge j$ its subtree is a shifted copy of
   $G_{n-j}$. Since every edge points to a child, a path starting in this
   subtree cannot leave it. Paths to label $n$ correspond, with identical
   lengths and multiplicities, to paths to label $n-j$ in $G_{n-j}$.
   Strict increase of integer labels makes all paths longer than $n-j$ zero.
   Hence the extra terms in the growth range $0,\ldots,n$ vanish; the other
   terms are exactly the growth rule for $G_{n-j+1}$, shifted by $j$.
   Recursive growth of old children and the appended new leaves preserve
   this correspondence, including their multiplicities. Induction proves
   that every vertex labeled $j$ in $G_n$ has subtree $G_{n-j}$ with labels
   shifted by $j$. This is a complete paper proof; its Lean formalization
   is not delivered.

5. **Root multiplicities — computed for $k\le9$, and proved for all $k\ge1$
   by a paper power-series argument.** The computation, command, exit code,
   SHA-256 and complete source are in Evidence. Set
   $s_n=S(0,n)=\binom{2n}{n}$, $s_0=1$, and let $z_k$ count root children
   born with label $k$. The subtree isomorphism in item 4 and Axiom 1 in
   item 2 partition all vertices labeled $n$ among root-child subtrees,
   giving
   $$s_n=\sum_{i=1}^{n}z_i s_{n-i}
     =z_n+\sum_{i=1}^{n-1}z_i s_{n-i}\quad(n\ge1).$$
   In $\mathbb Q[[x]]$, put $\mathcal S(x)=\sum_{n\ge0}s_nx^n$ and
   $Z(x)=\sum_{k\ge1}z_kx^k$. Then
   $\mathcal S-1=Z\mathcal S$. The central-binomial series is
   $\mathcal S(x)=1/\sqrt{1-4x}$, with constant term one, so
   $$Z(x)=1-\sqrt{1-4x}
     =2x\sum_{j\ge0}\operatorname{Cat}(j)x^j.$$
   Coefficient comparison gives $z_k=2\operatorname{Cat}(k-1)$.
   With $j=k-1$, the factorial definition yields
   $S(1,j)=2(2j)!/(j!(j+1)!)=2\operatorname{Cat}(j)$.
   These are precisely the decomposition and generating-function forms of
   Klanderman–McDicken–Tebbe's Theorem 2.1,
   [arXiv:2507.22861](https://arxiv.org/abs/2507.22861), PUMP **9** (2026),
   158–179, DOI `10.46787/pump.v9i.6304`. The all-$k$ conclusion is proved
   on paper here; only $k\le9$ is computationally checked, and no Lean
   root-multiplicity theorem is claimed.

6. **Companion existence claim — proved as a literature scope reading.**
   Klanderman–McDicken–Tebbe §3.4 says Theorem 2.1 “answers” the existence
   question for $S(0,n)$. Theorem 2.1 constructs some generalized action
   graphs from positive sequences satisfying the decomposition; Example
   3.10 verifies the super Catalan case only through $n\le2$.
   That literature reading does not identify the graphs of Caldwell et
   al. Definition 5.2 or prove Conjecture 5.6. The uniform application of
   its hypotheses to the particular source graphs is supplied by the paper
   arguments in items 2, 4 and 5. The companion's stated finite examples do
   not supply those uniform hypotheses; no such inference from the examples
   is asserted here.

7. **Extension boundary — open.** No identity for arbitrary $S(m,n)$,
   universal weighted-tree theorem, or Lean subtree-isomorphism and
   root-multiplicity theorem is delivered. The weighted identity supplies
   the missing universal count used in the source's discussion after
   Conjecture 5.6. Items 2 and 4 settle both graph axioms for this specific
   construction on paper; other generalized action graphs and the source's
   other conjectures are not covered by `result`.

## ASSUMED-UNVERIFIED

The literature reading is bounded to the named source versions, the
preregistration's searches, MathDB and the companion article. Absence of a
prior proof in all literature is ASSUMED-UNVERIFIED. Independent published
verification of MathDB's discussion proof is unverified. The paper arguments
above are separate from this module's kernel-checked theorem surface.
The escape audit for `result` is unfinished: [#14755](https://github.com/the-omega-institute/trureturing/issues/14755).
The compiled Reg mirror uses enrolled `DependentFamily.realize` with the literal
left and right operands, an exact bridge, variation, sensitivity and actual
observational dependence. The binding verdict is `DTR-Unregistered` for `result`
and `DTR-Undeclared` for the mirror; the source-family checker rejects the explicit
escape origin with `source.residual_requires_open`. No `declared_validated` status
is claimed.
Missing evidence: a lawful source-bound escape-origin representation for $\mathbb N$
and its compiled four-slot binding certificate.
