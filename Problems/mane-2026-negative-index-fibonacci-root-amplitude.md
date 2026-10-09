---
slug: mane-2026-negative-index-fibonacci-root-amplitude
bibkey: mane2026vanishing
doi: null
url: https://arxiv.org/abs/2507.11596v4
triage: theorem
motivation_gids:
  - D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.result
---

# The negative-index root-amplitude attainment clause is refuted

## Problem

S. R. Mane, *Identically vanishing k-generalized Fibonacci polynomials*,
arXiv:2507.11596v4, Section 6, Conjecture 6.6, states:

> For fixed k ≥ 3 and n < 0, the upper bound is ζ_{n,k} ≤ ⌊|n|/k⌋.
> The bound is attained whenever r_{n,k} = 1 (equivalently n = −sk,
> where s ≥ 1), i.e. it is a tight bound.

The recurrence (1.2)–(1.3) and initial values are

$$
\mathcal F_{n,k}(x)=\sum_{j=1}^{k}x^{k-j}\mathcal F_{n-j,k}(x),\qquad
\mathcal F_{1,k}=1,\qquad
\mathcal F_{n,k}=0\quad (-(k-2)\le n\le0).
$$

The source statistic is the maximum of $|x|^k$ over nonzero complex roots;
it is zero when there are none, including vanishing polynomials. The Lean
encoding uses `a k m` for $\mathcal F_{1-m,k}$, `F k n := a k (1-n).toNat`,
and the real supremum of the nonzero-root amplitude image. Its empty and
unbounded totalizations give zero. The guards in `claim` are $k\ge3$ and
$s\ge1$, with integer index $-sk$ and real-valued right side $s$.

## Motivation

MANE-1 in [issue #14674](https://github.com/the-omega-institute/trureturing/issues/14674)
selects the nondegenerate witness $k=3$, $s=5$, $n=-15$. The unconditional
settling theorem is
`D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.result : ¬ claim`.
The refutation addresses the attainment sentence; it does not negate the
separate upper-bound inequality.

## Gap

This is a tier-1 externally published named conjecture. The preregistration
contains the source transcription and bounded literature readings: arXiv
versions, author papers, root literature and citation searches. Those readings
found no settlement in their searched scope. Exhaustive absence of prior work
is not established by finite searches. The proof needs neither Conjecture 6.4
nor Conjecture 6.5 as a premise.

## Route

The recurrence yields

$$
\mathcal F_{-15,3}(x)=-xq(x^3),\qquad
q(t)=t^4+8t^3+18t^2+15t+5=(t+5)(t+1)^3-t.
$$

The intermediate value theorem gives a real root $-A$ with $4<A<5$.
Factoring out $t+A$ leaves a monic cubic with positive coefficients
$b<4$, $c<3$, $d<5/4$. Its Cauchy bound is at most $5$, so every quartic
root has modulus strictly below $5$. Every nonzero root of
$\mathcal F_{-15,3}$ therefore has $|x|^3<5$. The amplitude image is finite
and nonempty, so its supremum is attained and is strictly below $5$.

The eleven private helpers and `result` are `bind-only` after expansion
through the same-delivery helpers to pinned Mathlib. The settling declaration
uses `admission_basis: open-problem-resolution (#14674; Refuted)`; it has no
escape witness. Its fixed-parameter exact certificate has utility
`kind=certified-instance`, with `refutes` pointing to `claim`.
Information-escape registration is paused under CLAUDE.md §3.9.

## Falsifier

A mismatch between the displayed recurrence, the root-amplitude statistic
and their Lean definitions invalidates source fidelity. An error in the
kernel-checked strict bound invalidates the witness. A prior published
settlement invalidates the asserted literature gap. The numerical checks
below are observations and are not proof premises.

## Evidence

The public result and its private proof path are in
`D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.lean`, with the
corresponding Blueprint Scribe and the source note
`Library/Zeros/mane2026vanishing.md`. The claim is `Refuted` at the settling
Scribe node. Every public declaration's axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

## Triage

### What the settlement shows

**Proved in this module — the nondegenerate witness.** The private
`zeta_lt_five` proves $\zeta_{-15,3}<5$; `result` negates the universal
attainment clause through $k=3,s=5$. The zero polynomial and the degenerate
$s=1$ case are not used.

**Computed — where attainment holds in the tested range.**
`python3 /tmp/op-mane/check.py`, exit $0$, tests $k\in\{3,4,5\}$ and every
$1\le s\le k+3$. In precisely the tested cases $2\le s\le k+1$ it reports
$\zeta_{-sk,k}=s$ to the numerical tolerance $10^{-9}$. The source's
Conjecture 6.4 factor $x^k+s$ explains this restricted range. A uniform proof
of Conjecture 6.4 belongs to a separate settlement; numerical roots do not
prove exact equality or exclude attainment at untested larger $s$.

**Proved by the following paper argument — the family at $s=k+2$.**
For $k\ge3$, put $t=x^k$ and

$$
Q_k(t)=(t+k+2)(1+t)^k+(-1)^kt.
$$

The recurrence gives $\mathcal F_{-k(k+2),k}(x)=-xQ_k(x^k)$. Here is a
coefficient derivation independent of Conjecture 6.4. With
$A(u)=\sum_{m\ge0}a_k(m)u^m$ and $B=1+x^k$, the recurrence and initial
values give the formal power-series identity

$$
A(u)=\frac{1+\sum_{j=1}^{k-1}x^ju^j}
 {1+\sum_{j=1}^{k-1}x^ju^j-u^k}
=1+\frac{u^k(1-xu)}{1-Bu^k+xu^{k+1}}
=1+u^k(1-xu)\sum_{r\ge0}(Bu^k-xu^{k+1})^r.
$$

To extract $u^{1+k(k+2)}$, let $h$ count factors $-xu^{k+1}$ and let
$\delta\in\{0,1\}$ select the numerator term. The degree condition is
$kr+h+\delta=k(k+1)+1$ with $0\le h\le r$. Its only solutions are
$(r,h,\delta)=(k+1,1,0),(k+1,0,1),(k,k,1)$. Their contributions sum to

$$
-(k+1)xB^k-xB^{k+1}+(-1)^{k+1}x^{k+1}
=-x\big((t+k+2)(1+t)^k+(-1)^kt\big).
$$

On $|t+1|=2$ one has $|t|\le3$ and

$$
|(t+k+2)(1+t)^k|\ge(k-1)2^k>3\ge|(-1)^kt|.
$$

Rouché's theorem therefore puts exactly $k$ roots of $Q_k$, counted with
multiplicity, inside $|t+1|<2$: the comparison polynomial has its $k$ roots
at $-1$, and its remaining root $-(k+2)$ lies outside this disk. Moreover,

$$
Q_k(-(k+2))=(-1)^{k+1}(k+2),\qquad
Q_k(-(k+1))=(-1)^k\big(k^k-(k+1)\big).
$$

These signs are opposite. The intermediate value theorem gives the
remaining real root in $(-(k+2),-(k+1))$, disjoint from that disk. All $k+1$
roots consequently have $|t|<k+2$; the disk roots even have $|t|<3$.
The nonzero polynomial has a finite root set and the real root has nonzero
complex $k$th roots. Thus $\zeta_{-k(k+2),k}<k+2$ for every $k\ge3$.
This family argument is a paper proof, not an additional Lean theorem.

**Computed — numerical failures.** The same command, exit $0$, produces:

| $k$ | $s$ | $\zeta_{-sk,k}$ (numerical) |
| --- | --- | --- |
| 3 | 5 | 4.918241 |
| 3 | 6 | 5.801256 |
| 4 | 6 | 5.990341 |
| 4 | 7 | 6.973533 |
| 5 | 7 | 6.999099 |
| 5 | 8 | 7.997207 |

The rows with $s=k+2$ are boundary failures; those with $s>k+2$ are
$(3,6),(4,7),(5,8)$. These are numerical root approximations, not certified
interval bounds. No universal assertion for every $s>k+2$ is established.

**Proved by the recurrence on paper — the degenerate case $s=1$.**
For $k\ge3$, the initial values give $a_k(k)=1$ and $a_k(k+1)=-x$:
in the backward step at $m=k+1$, the only nonzero summand is
$x\,a_k(k)$. Hence $\mathcal F_{-k,k}=-x$, whose only complex root is zero.
The nonzero-root amplitude set is empty and $\zeta_{-k,k}=0$. This is not
a delivered general Lean theorem and is not the settling witness.

**Open — the upper-bound inequality in general.**
$\zeta_{n,k}\le\lfloor|n|/k\rfloor$ remains open for general $k\ge3,n<0$.
It holds at the witness because the module proves the stronger
$\zeta_{-15,3}<5=\lfloor15/3\rfloor$.

**Proved on paper and computed — the failure mechanism.**
The coefficient identity at $s=k+2$ contains the extra nonzero term
$(-1)^kt$, so the factorization pattern of Conjecture 6.4 no longer gives
a root at $t=-(k+2)$. The Rouché/IVT argument places every root strictly
inside $|t|<s$. The boundary observations $4.918241$, $5.990341$, $6.999099$
for $k=3,4,5$ lie increasingly close to $s$ from below. Convergence as
$k\to\infty$ is open here; these three values alone do not prove it.
The upper-bound clause, Conjectures 6.4 and 6.5 and the branch-slope claims
are separate questions. Any inference using universal attainment as a
premise loses that premise; none of those separate statements is refuted
by the settling theorem. The surviving restricted range and the general
upper bound require their own settlement evidence.

### Reproducible computation

Command: `python3 /tmp/op-mane/check.py`. Exit code: $0$.
SHA-256: `15703055e4ebee4fc1fae8b096cd67c2da04797d2c9aaa8c2e6a97ffec2cd541`.
The script uses Python and SymPy, 30-digit numerical roots, a $10^{-20}$
zero-root cutoff and a $10^{-9}$ attainment tolerance. Its tested scope is
exactly $k\in\{3,4,5\}$, $1\le s\le k+3$. Save the following bytes as
`/tmp/op-mane/check.py` to reproduce the command; `k` in `zeta` is the
outer loop's current value.

```python
import sympy as sp
x=sp.symbols('x')
def F(k, nmin):
    vals={1:sp.Integer(1)}
    for n in range(-(k-2),1): vals[n]=sp.Integer(0)
    # backward: F_{n-k} = F_n - sum_{j=1}^{k-1} x^{k-j} F_{n-j}
    n=1
    while n-k>=nmin:
        vals[n-k]=sp.expand(vals[n]-sum(x**(k-j)*vals[n-j] for j in range(1,k)))
        n-=1
    return vals
def zeta(p):
    r=[z for z in sp.Poly(p,x).nroots(n=30,maxsteps=200) if abs(z)>1e-20]
    return max(abs(z)**k for z in r) if r else 0
for k in [3,4,5]:
    v=F(k,-k*(k+3))
    for s in range(1,k+4):
        n=-s*k
        p=v[n]; z=zeta(p) if p!=0 else 0
        print(f"k={k} s={s} n={n} zeta={float(z):.6f} floor(|n|/k)={s}", "ATTAINED" if abs(z-s)<1e-9 else "NOT attained")
    print()
print(sp.factor(F(3,-15)[-15]))
```

## ASSUMED-UNVERIFIED

The finite literature search does not establish exhaustive absence of a
prior settlement. Numerical roots are not interval-certified. The family
and degenerate-case arguments above have not been formalized in this module.
The uniform attainment characterization outside the tested finite scope,
the large-$k$ convergence claim and the general upper-bound inequality
are open here.
