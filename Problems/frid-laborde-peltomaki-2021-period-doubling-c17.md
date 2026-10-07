---
slug: frid-laborde-peltomaki-2021-period-doubling-c17
bibkey: fridlabordepeltomaki2021automaticppl
doi: 10.1016/j.tcs.2021.08.016
url: https://arxiv.org/abs/2009.02934v2
triage: theorem
motivation_gids:
  - D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result
---

# Period-doubling PPL-difference: Conjecture 17

## Problem

Frid, Laborde and Peltomäki, *On prefix palindromic length of automatic words*,
Theoretical Computer Science 891, 13–23, arXiv:2009.02934v2,
Section 5.1, printed page 13, Conjecture 17:

> The sequence $d_{pd}$ of the period-doubling word $\mathbf{u}_{pd}$ is not
> $2$-automatic, and so the prefix palindromic length $\operatorname{PPL}_{pd}(n)$ of
> $\mathbf{u}_{pd}$ is not $2$-regular.

The word is the fixed point beginning with a of a → ab, b → aa.
Write P(n) for the minimum number of nonempty palindrome factors of its
length-n prefix, P(0)=0, and d_pd(n)=P(n+1)−P(n) for n≥0.
C17 asks whether the set of sequences n ↦ d_pd(2^e n+r), over all natural
e and r<2^e, is infinite. No finite-prefix restriction is imposed.

## Motivation

The frozen declaration
`D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.result`
proves this infinitude without hypotheses. The supporting
`SparseKernelRank.stronger_PPL_kernel_span` proves that the rational span
of the binary kernel of P is not finite dimensional, providing the stronger
non-2-regularity criterion directly.

## Gap

Issue #13100 preregisters C17 as a tier 3 research line with
`admission_basis: escape-witness`. The source states C17 as a conjecture;
Bulgakova, Frid and Scanvic, arXiv:2201.09556v3, printed page 1, recall
period-doubling non-2-regularity as conjectural. The inspected sources and
preregistration report no resolution. This is a bounded literature result,
not an exhaustive worldwide novelty certificate.

## Route

The literal substitution is related to valuation parity. The palindrome-radius
and even-palindrome results classify legal suffix cuts, and minimum signed
binary weight gives a lower bound F(n)=signedWeight(⌊(n+1)/2⌋).
Tight optimal factorizations produce finite transducer paths. Marked-prefix
rigidity and the charge potential obstruct attaining F on a sparse diagonal.
Constructed palindrome cuts give matching upper bounds.

Define

$$N(a,b)=\sum_{i=0}^{a-1}2^{2b+2+3i}+\sum_{j=0}^{b-1}2^{2j+1}.$$

For positive odd a, the diagonal value is P(N(a,2a−1))=3a.
For positive odd a and odd b≥2a+1, the off-diagonal value is
P(N(a,b))=a+b. Sparse binary addresses turn these evaluations into
triangular matrices with an extra diagonal unit, yielding unbounded rational
kernel rank. A finite difference kernel would place the P-kernel span inside
a finite span of difference-kernel sequences and their partial sums, by
residue-block telescoping. This contradicts the rank theorem.

## Falsifier

A finite difference kernel closed under both binary address maps for every
input would contradict the settling claim. A claimed route must account for
every competing palindrome factorization; agreement on any finite prefix,
including the samples below, cannot certify C17 or the open follow-ups.

## Evidence

The settling Lean module and its Scribe mirror are
`D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.lean`
and
`Blueprint/D5/S1/Words/Palindromes/PeriodDoubling/PrefixPalindromicLengthNotAutomatic.scribe.cs`.
The latter carries `OpenProblemResolutionClaim` with resolution Proved.
The public result is `result : claim`; `claim` uses the literal integer
PPL-difference and all binary-kernel addresses. Its axiom closure is
`propext`, `Classical.choice`, and `Quot.sound`.

The source and context are recorded in
[FLP](../Library/Words/fridlabordepeltomaki2021automaticppl.md),
[Li](../Library/Words/li2020rulerperioddoubling.md),
[Bulgakova–Frid–Scanvic](../Library/Words/bulgakovafridscanvic2022sierpinski.md),
and the [signed-digit reference](../Library/Words/menezesvanoorschotvanstone1996sparse.md).

Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

Tier 3 research line #13100. Resolution: Proved.

### What the settlement shows

**Proved.** The marked-charge obstruction, exact sparse diagonal and
off-diagonal evaluations, infinite rational P-kernel span, and infinite
integer difference kernel are proved in this delivery. Their range is
unbounded; the sparse evaluations retain the stated positivity, parity,
and b-range conditions. Non-automaticity is established through the literal
kernel criterion, and non-regularity through the rational-span criterion.
The paper's period-doubling question can use these conclusions; its separate
Fibonacci, factor-complexity, and morphicity questions are not settled here.

**Open.** For every positive odd a, does
P(N(a,2a−1)+1)=3a? For every positive odd a and odd b≥2a+1, does
P(N(a,b)+1)=a+b+1? `SparseFamilyUpper` proves the corresponding successor
upper bounds, but no uniform matching lower bounds are delivered.

**Open.** Does P(n)≤F(n)+2 hold for every natural n? The signed-weight
lower bound is proved; its proposed uniform upper companion is not.

**Open.** Is d_pd morphic, meaning a coding of a fixed point of a prolongable
morphism that may have nonuniform image lengths? Non-2-automaticity excludes
the relevant uniform automatic representation, and does not settle general
morphicity. A finite prefix supplies neither a construction nor an exclusion.

**Computed.** Independent palindromic-tree dynamic programming considers
every palindromic suffix up to n=299691. The successor samples are:

| a | b | N(a,b) | P(N) | P(N+1) |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 18 | 3 | 3 |
| 1 | 3 | 298 | 4 | 5 |
| 1 | 5 | 4778 | 6 | 7 |
| 3 | 5 | 299690 | 9 | 9 |

In this finite range, max(P−F)=2, first attained at n=72. On the first
4096 differences, the numbers of distinct factors of lengths 1, 2, 4, 8, 16,
and 32 are respectively 3, 9, 43, 200, 602, and 1201. These are finite
factor-complexity readings, and do not decide morphicity. These computations
support the candidate formulas only on the stated range. The following
Python 3 command exits 0 and reproduces all these readings; its morphicity
line records the open boundary rather than an experimental test of morphicity.

```sh
python3 - <<'PY'
from functools import lru_cache

def sparse(a,b):
    return sum(2**(2*b+2+3*i) for i in range(a)) + sum(2**(2*j+1) for j in range(b))

# Independent palindromic tree: every distinct suffix palindrome is considered.
pairs=[(1,1),(1,3),(1,5),(3,5)]
bound=max(sparse(a,b)+1 for a,b in pairs)
w=[-1]; lengths=[-1,0]; links=[0,0]; edges=[{},{}]; last=1; P=[0]
for i in range(1,bound+1):
    x=((i & -i).bit_length()-1)%2
    w.append(x); q=last
    while i-1-lengths[q]<0 or w[i-1-lengths[q]]!=x:
        q=links[q]
    if x not in edges[q]:
        v=len(lengths); edges[q][x]=v
        lengths.append(lengths[q]+2); edges.append({}); links.append(1)
        if lengths[v]>1:
            t=links[q]
            while i-1-lengths[t]<0 or w[i-1-lengths[t]]!=x:
                t=links[t]
            links[v]=edges[t][x]
    last=edges[q][x]; q=last; best=i
    while lengths[q]>0:
        best=min(best,P[i-lengths[q]]+1); q=links[q]
    P.append(best)

@lru_cache(None)
def signed_weight(n):
    if n<=1:return n
    if n%2==0:return signed_weight(n//2)
    return 1+min(signed_weight(n//2),signed_weight(n//2+1))
for a,b in pairs:
    n=sparse(a,b)
    print('sparse',a,b,n,P[n],P[n+1], 'successor candidate',3*a if b==2*a-1 else a+b+1)
    assert P[n]==(3*a if b==2*a-1 else a+b)
    assert P[n+1]==(3*a if b==2*a-1 else a+b+1)
excess=[P[n]-signed_weight((n+1)//2) for n in range(bound+1)]
print('bound',bound,'max P-F',max(excess),'first maximizer',excess.index(max(excess)))
assert max(excess)<=2
d=[P[n+1]-P[n] for n in range(4096)]
for m in (1,2,4,8,16,32):
    print('difference-factors',m,len({tuple(d[i:i+m]) for i in range(len(d)-m+1)}))
print('morphic status: open; a finite prefix does not decide morphicity')
PY
```

## ASSUMED-UNVERIFIED

The inspected literature does not constitute a worldwide novelty certificate.
The coding a=false, b=true and zero-based word indices are the stated source
conventions. The three follow-up themes remain open despite their finite
successor and F+2 evidence. No morphic representation or nonmorphicity proof
is delivered.
