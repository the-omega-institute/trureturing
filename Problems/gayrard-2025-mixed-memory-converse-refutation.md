---
slug: gayrard-2025-mixed-memory-converse-refutation
bibkey: gayrard2025mixedmemories
doi: null
url: https://arxiv.org/abs/2504.04879v2
triage: theorem
motivation_gids:
  - D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.result
---

# An asymmetric mixed memory outside Gayrard's hierarchy

## Problem

Véronique Gayrard, *Mixed memories in Hopfield networks*, arXiv:2504.04879v2,
Section 1.2.1, Conjecture 1.4, printed p. 6:

> Given any $n\in\mathbb N$ odd, $\xi^{(N)}(m)$ is an $n$-mixed memory of type $F$ if and only if $m\in\mathcal M_{n,F}$.

The source uses a doubly infinite jointly independent family of fair signs,
a smooth $F$ with $F'(x)>0$ for $x>0$, fixed odd $n$, a nondecreasing pattern
count $M(N)$, and deterministic coefficients in $[-1,1]$. Definition 1.1
requires exactly $n$ nonzero coefficients, binary configurations
$\xi_i(m)=\operatorname{sign}(\sum_{\mu=1}^{M}\xi_i^\mu F'(m_\mu)
\mathbf1_{m_\mu\ne0})$, almost-sure overlap limits $m_\mu$ on that support,
and zero overlap limits on available coordinates outside it. The sign at zero
is zero (Section 2.2, printed (2.25)).

The set $\mathcal M_{n,F}$ is defined by allowable ordered compositions:
all nonfinal blocks are even and at least two, and the final block is positive
and odd. With
$\alpha^{(a)}=2^{1-a}\binom{a-1}{\lfloor(a-1)/2\rfloor}$ and
$\gamma^{(k)}=\prod_{l=1}^k\alpha^{(n_l)}$, only compositions satisfying
$2F'(\gamma^{(k)})>\sum_{r>k}n_r F'(\gamma^{(r)})$ for every nonfinal
block are retained. Their block vectors repeat $\gamma^{(k)}$ on $n_k$
coordinates and are padded by zeros. All permutations and all coordinate
signs raised to exponent one for odd $F'$ and two otherwise are included.

For every positive block size $a$, the formalization reuses `D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound.c`, equal to the source's $\alpha^{(a)}=2^{-a+1}\binom{a-1}{\lfloor(a-1)/2\rfloor}$.

## Motivation

The frozen declaration
`D5/S3/StatisticalMechanics/Hopfield/GayrardMixedMemoryRefutation.result`
refutes the full equivalence using a five-pattern mixed memory that is absent
from this literal composition hierarchy. The hierarchy remains a sufficient
construction, but cannot classify all mixed memories as defined in the paper.

## Gap

Preregistration [#13571](https://github.com/the-omega-institute/trureturing/issues/13571)
classifies the author conjecture as Tier 1 and records the literal definitions,
full quantified claim, candidate, and literature readings. Its source check
covers arXiv v1 and v2. Its citing-work checks of Hess–Morris
(arXiv:2506.05178) and Heydenreich–Hirsch–Löwe (arXiv:2604.25470), and its
Amit–Gutfreund–Sompolinsky 1985 page check, are search-seat reports. Its
MathDB and coefficient searches are orchestrator reports. These establish
`not-found-in-searched-scope`, not an exhaustive originality claim.
Amit's 1989 monograph tables are unread and their relationship to the witness
is open.

## Route

Take $F(x)=x^2/2$, $M(N)=5$, $n=5$, and
$m=(5/8,3/8,3/8,1/8,1/8)$, padded by zeros. For every
$x\in\{-1,1\}^5$, the integer field
$5x_1+3x_2+3x_3+x_4+x_5$ is odd and nonzero. The coordinate-sign sums over
the 32 cube points are $(20,12,12,4,4)$, so their normalized values equal
$m$. An infinite product of fair Boolean coordinates supplies the patterns;
the strong law applied to each bounded coordinate-spin product gives all five
almost-sure overlap limits. With $M=5$ the off-support condition is vacuous.

The allowable compositions of five are $(5)$, $(2,3)$, $(4,1)$, and
$(2,2,1)$. Their block vectors have absolute coordinates in
$\{3/8,1/2,1/4\}$; all have absolute coordinates at most $1/2$.
The system of inequalities can only remove compositions. Permutations and
the source sign powers preserve absolute values, whereas $m_1=5/8$.
Thus $m\notin\mathcal M_{5,F}$, contradicting the necessary direction.

## Falsifier

`result : ¬ claim` negates the universal equivalence with every standing
hypothesis explicit. No extra assumption is imposed on the conjecture.
The deterministic sequence $m:\mathbb N\to\mathbb R$ represents coherent
restrictions to the first $M(N)$ coordinates; the counterexample already
uses constant $M=5$, where the restrictions are the source's fixed vector.
A change to Definition 1.1, the allowed compositions, the strict hierarchy
inequalities, the sign exponent, or the zero-sign convention changes the
statement being settled. The counterexample has positive margin and is
independent of the zero-sign convention.

## Evidence

The public Lean surface is eight definitions (`allowable`, `gamma`,
`hierarchySystem`, `blockVector`, `coefficientSet`, `memorySpin`, `mixedMemory`,
`claim`) and the single theorem `result`. All helper propositions are local
proof terms. The axiom closure of every public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The finite sign sums and nonzero fields use kernel reduction; the probability
argument uses pinned Mathlib's `ProbabilityTheory.strong_law_ae` and product-law
results. The proof shape is bind-only, with escape witness none and admission
basis `open-problem-resolution (#13571; Refuted)`.

The following reproducible commands extract the corresponding inline Python
block, print its SHA-256, and run it. Each exits zero; the scripts use only
Python's standard library. Hashes include the terminal newline of the block.

```sh
python3 -c 'import sys,re,pathlib,hashlib; s=re.findall(r"```python\n(.*?)```",pathlib.Path(sys.argv[1]).read_text(),re.S)[int(sys.argv[2])]; print("sha256="+hashlib.sha256(s.encode()).hexdigest()); exec(compile(s,"<inline>","exec"))' Problems/gayrard-2025-mixed-memory-converse-refutation.md 0
python3 -c 'import sys,re,pathlib,hashlib; s=re.findall(r"```python\n(.*?)```",pathlib.Path(sys.argv[1]).read_text(),re.S)[int(sys.argv[2])]; print("sha256="+hashlib.sha256(s.encode()).hexdigest()); exec(compile(s,"<inline>","exec"))' Problems/gayrard-2025-mixed-memory-converse-refutation.md 1
```

Information-escape registration is paused under CLAUDE.md §3.9.

## Triage

### What the settlement shows

**Proved in Lean — base witness.** The theorem `result` proves that the
five-pattern vector above is a mixed memory for quadratic activation and is
outside the hierarchy, hence Conjecture 1.4 is false. The proof retains the
literal support and overlap requirements; it does not substitute a finite
correlation test for the almost-sure limits.

**Proved on paper — every odd dimension at least five.** Let $v_0=m$ and
$v_{k+1}=(1/2,1/2,v_k/2)$, of length $n=5+2k$. For a positive
self-consistent $v$ with $S=\sum_j v_j<2$ and nonzero fields, let $a,b$
be two fresh fair signs and write $h=v\cdot x$. The new field is
$(a+b)/2+h/2$. When $a=b$ its sign is $a$, since $|h|\le S<2$.
When $a=-b$ its sign is $\operatorname{sign}(h)$. Consequently
$\mathbb E[a\operatorname{sign}((a+b)/2+h/2)]=1/2$, and the same holds
for $b$: the agreement cases contribute $1/2$ and the disagreement cases
cancel. Each old coordinate has correlation
$\frac12\mathbb E[x_j\operatorname{sign}(h)]=v_j/2$, since the agreement
cases cancel in the fresh sign. This proves the recursion preserves exact
self-consistency.

The base sum is $13/8$ and its minimum absolute field is $1/8$.
Induction gives
$\sum_j(v_k)_j=2-3/(8\cdot2^k)<2$ and margin
$\delta_k=1/(8\cdot2^k)>0$. In the disagreement cases the next margin is
$\delta_k/2$; in agreement cases it is at least
$1-\frac12\sum_j(v_k)_j=3/(16\cdot2^k)$, which is larger.
For each fixed $k$, take $M(N)=n=5+2k$. The same bounded-variable strong-law
argument yields Definition 1.1 for $v_k$. This is a paper extension of the
base proof, not a further Lean theorem in this module.

**Proved on paper — even-multiplicity obstruction.** For positive $a$,
$\alpha^{(1)}=1$ and $0<\alpha^{(a)}<1$ when $a\ge2$: a single central
binomial coefficient is strictly smaller than the sum of all coefficients
of $(1+1)^{a-1}$. Therefore the block values decrease strictly through all
nonfinal blocks. The final block can equal the preceding value only when
its size is one; this equality concerns the smallest nonzero value.
Every absolute value strictly above the smallest therefore has even
multiplicity, since its block size is even. Permutations, signs, zero padding,
and the hierarchy inequalities preserve this obstruction for every $F$.
In $v_k$, the value $5/(8\cdot2^k)$ is above the smallest
$1/(8\cdot2^k)$ and occurs once. It cannot equal one of the fresh pair
values $2^{-j}$, since five is not a power of two, nor another scaled base
coordinate. Hence $v_k\notin\mathcal M_{5+2k,F}$ for every $F$.
Together with quadratic self-consistency, necessity fails for every odd
$n\ge5$.

**Computed — family through dimension thirteen.** Inline script 0 verifies
all cube points and all allowable compositions for
$n\in\{5,7,9,11,13\}$ using exact fractions. SHA-256:
`c33a341c0ce117e26750b573f37d1e284f081e0bc22d0e79401cee249d72aa1a`. The extraction command in Evidence with final argument `0`
exits zero and prints:

```text
n=5 points=32 compositions=4 margin=1/8 fixed=True outside=True
n=7 points=128 compositions=8 margin=1/16 fixed=True outside=True
n=9 points=512 compositions=16 margin=1/32 fixed=True outside=True
n=11 points=2048 compositions=32 margin=1/64 fixed=True outside=True
n=13 points=8192 compositions=64 margin=1/128 fixed=True outside=True
```

The script deliberately tests the larger hierarchy without imposing the
system of inequalities, so nonmembership also holds in its selected subset.
The uniform extension is justified by the paper induction above, not by the
finite computation. **Open in Lean:** the family and its multiplicity
obstruction are not delivered as Lean declarations.

```python
from fractions import Fraction as Q
from itertools import product
from collections import Counter
from math import comb

def compositions(n):
    yield (n,)
    for a in range(2, n, 2):
        for tail in compositions(n-a):
            yield (a,) + tail

def hierarchy(c):
    g = Q(1)
    out = []
    for a in c:
        g *= Q(comb(a-1, (a-1)//2), 2**(a-1))
        out.extend([g]*a)
    return tuple(out)

v = tuple(Q(a, 8) for a in (5, 3, 3, 1, 1))
for k in range(5):
    n = len(v)
    sums = [0]*n
    margin = None
    for x in product((-1, 1), repeat=n):
        h = sum(a*b for a, b in zip(v, x))
        assert h != 0
        s = 1 if h > 0 else -1
        margin = abs(h) if margin is None else min(margin, abs(h))
        for j in range(n):
            sums[j] += x[j]*s
    assert tuple(Q(a, 2**n) for a in sums) == v
    assert margin == Q(1, 8*2**k)
    counts = Counter(v)
    special = Q(5, 8*2**k)
    assert counts[special] == 1 and special > min(v)
    target = tuple(sorted(v))
    cs = list(compositions(n))
    for c in cs:
        u = hierarchy(c)
        assert all(a == min(u) or b % 2 == 0 for a, b in Counter(u).items())
        assert tuple(sorted(u)) != target
    print(f'n={n} points={2**n} compositions={len(cs)} margin={margin} fixed=True outside=True')
    v = (Q(1, 2), Q(1, 2)) + tuple(a/2 for a in v)
```

**Computed — dimension three at quadratic activation.** A positive-margin
threshold table is odd, so its values on the four representatives with
$x_1=1$ determine the whole table. Every self-consistent vector is exactly
the table's correlation vector, so enumerating all sixteen odd tables,
then checking the signs of their own correlation fields, is exhaustive.
Inline script 1, SHA-256 `3783d01818b6faa72c04b5846a1d4c9b02d7d1331918bc8d933f0ba32ecce333`, has extraction-command exit zero and
prints:

```text
odd_tables=16 positive_margin_fixed=14 full_support=8
full_support_absolute_vectors: [(Fraction(1, 2), Fraction(1, 2), Fraction(1, 2))]
quadratic n=3 necessity holds for every positive-margin full-support fixed vector
```

There are fourteen positive-margin fixed vectors: six signed original-pattern
vectors with support one and eight vectors with support three. Every
full-support vector has absolute coordinates $(1/2,1/2,1/2)$, the hierarchy
vector for composition $(3)$. Thus necessity holds in this computed
$n=3$, quadratic, positive-margin full-support class, including all coordinate
signs. **Open:** necessity at $n=3$ for general activation $F$, and a Lean
formalization of this enumeration. This computation is not a classification
at other dimensions or temperatures.

```python
from fractions import Fraction as Q
from itertools import product

xs = tuple(product((-1, 1), repeat=3))
reps = tuple(x for x in xs if x[0] == 1)
fixed = set()
for labels in product((-1, 1), repeat=len(reps)):
    table = dict(zip(reps, labels))
    table.update({tuple(-a for a in x): -s for x, s in zip(reps, labels)})
    v = tuple(Q(sum(x[j]*table[x] for x in xs), 8) for j in range(3))
    if all((h := sum(a*b for a, b in zip(v, x))) != 0 and
           (1 if h > 0 else -1) == table[x] for x in xs):
        fixed.add(v)
full = {v for v in fixed if all(v)}
expected = set(product((Q(-1, 2), Q(1, 2)), repeat=3))
assert full == expected
assert len(fixed) == 14
print(f'odd_tables={2**len(reps)} positive_margin_fixed={len(fixed)} full_support={len(full)}')
print('full_support_absolute_vectors:', sorted({tuple(sorted(map(abs, v))) for v in full}))
print('quadratic n=3 necessity holds for every positive-margin full-support fixed vector')
```

**Proved on paper — dimension one for quadratic activation.** With one
nonzero coefficient $t$, the correlation is $\operatorname{sign}(t)$, so
self-consistency forces $t\in\{-1,1\}$. These are the signed hierarchy
vectors for composition $(1)$. **Open:** a classification for general $F$
under the paper's full hypotheses.

**Proved in the source — surviving sufficient direction.** Theorem 1.2,
printed p. 6, asserts $m\in\mathcal M_{n,F}\Rightarrow\xi^{(N)}(m)$ is an
$n$-mixed memory. The refutation of its converse leaves that theorem's
statement and proof intact; it is a published result, not an additional
kernel-checked theorem here. Bounds enumerating $\mathcal M_{n,F}$ still
concern that constructed set and cannot be used as counts of all
Definition 1.1 mixed memories via Conjecture 1.4.

**Open — local minima and the Section 1/Section 2 discussion.** Section 1
states that the hierarchy “contains all the local minima found numerically”
and discusses completeness of local minima conditional on Conjecture 1.4.
The latter inference cannot use that conjecture. The statement about the
reported numerical sample is not independently refuted by a mixed-memory
counterexample. Section 2.2 explicitly searches for all deterministic
mixed-memory solutions, “not just those that lead to local minima”. The
vectors $v_k$ supply solutions outside the constructed hierarchy. Whether
all associated finite-$N$ configurations are energy local minima in the
source's dynamical sense, with precisely the source's load and probability
quantifiers, remains open in this delivery. No local-minimum theorem is
claimed or used to refute Conjecture 1.4.

**Open — earlier mixture tables.** Whether the base vector appears in
Amit–Gutfreund–Sompolinsky's 1985 zero-temperature mixtures, or in Amit's 1989
*Modeling Brain Function* tables, is not established. Preregistration reports
a check of the 1985 paper's printed p. 1013, equations (4.6)–(4.8), but the
1989 tables have not been read. This bibliographic question does not alter
the kernel-checked refutation; it limits claims of a newly discovered witness.

## ASSUMED-UNVERIFIED

The preregistration's secondary-literature, MathDB, web-search and 1985-page
readings are attributed reports, not independently repeated global novelty
checks. The Amit 1989 table check is open. The family argument is proved on
paper and computed through dimension thirteen; only the base refutation is
proved in Lean. Local-minimum claims and general-activation classifications
at $n=1$ and $n=3$ are open. No completeness of the literature search or
model-family diversity is asserted.
