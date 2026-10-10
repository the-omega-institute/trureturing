---
slug: mane-2026-negative-index-fibonacci-factorization
bibkey: mane2026vanishing
doi: null
url: https://arxiv.org/abs/2507.11596v4
triage: theorem
motivation_gids:
  - D5/S3/Zeros/NegativeIndexFibonacciFactorization.result
---

# Mane's negative-index factorization

## Problem

S. R. Mane, *Identically vanishing k-generalized Fibonacci polynomials*,
arXiv:2507.11596v4, p. 19, Section 6, Conjecture 6.4, states:

> For k ≥ 2 and n = −sk, where s ∈ [2, k + 1] (the pattern fails for s ≥ k + 2),
> 𝓕_{−sk,k}(x) = −x(x^k + 1)^{s−2}(x^k + s). (6.4)
> Hence 𝓕_{−sk,k}(x) has roots x^k = −s.

The recurrence (1.2)–(1.3) is

$$
\mathcal F_{n,k}(x)=\sum_{j=1}^k x^{k-j}\mathcal F_{n-j,k}(x),\qquad
\mathcal F_{1,k}=1,\qquad \mathcal F_{n,k}=0\quad (-(k-2)\le n\le0).
$$

The frozen definitions `a` and `F` in
`D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.lean` encode
$a_k(m)=\mathcal F_{1-m,k}$ and `F k n = a k (1-n).toNat`.
The claim is an identity in $\mathbb Z[X]$ with natural $k,s$,
$k\ge2$ and $2\le s\le k+1$; the index is the integer $-sk$.

## Motivation

[Preregistration #14688](https://github.com/the-omega-institute/trureturing/issues/14688)
selects MANE-2, the full factorization identity. The settling declaration is
`D5/S3/Zeros/NegativeIndexFibonacciFactorization.result : claim`.
It provides the exact restricted attainment range related to Conjecture 6.6.

## Gap

This is a tier-1 externally published named conjecture. The source and
literature readings recorded in #14688 inspect arXiv versions, author papers,
classical root papers and citation indexes; no settlement was found in that
scope. Finite searches do not establish exhaustive absence of prior work.

## Route

Put $t=X^k$, $A(z)=\sum_{m\ge0}a_k(m)z^m$ and
$B(z)=z^k((1+t)-Xz)$. The recurrence gives

$$
A(z)(1-B(z))=1-tz^k.
$$

A finite geometric sum gives the coefficients below degree $kL$ without
an analytic convergence assumption. At degree $sk+1$, with $s\le k+1$,
only $B^s$ contributes; at degree $(s-1)k+1$, only $B^{s-1}$ contributes.
Their coefficients are $-sX(1+t)^{s-1}$ and
$-(s-1)X(1+t)^{s-2}$. Subtracting $t$ times the latter gives
$-X(1+t)^{s-2}(t+s)$.

The public surface consists of `claim` and `result`; the private definitions
and all sixteen private theorems have live consumers. Every theorem is
`bind-only` after expansion through same-delivery helpers to frozen and
pinned Mathlib declarations. Admission is
`open-problem-resolution (#14688; Proved)`, with no escape witness.
Utility is `none`: this is a universal polynomial identity, with no
fixed-parameter numerical certificate in the delivered Lean module.
Information-escape registration is paused under CLAUDE.md §3.9.

## Falsifier

A mismatch between the recurrence, index convention, quantifier range or
polynomial factors and the source invalidates fidelity. A failing in-range
instance refutes the claim. A prior published settlement invalidates the
literature gap. The computations below are checks, not proof premises.

## Evidence

The Lean module and its corresponding Blueprint Scribe establish the exact
MANE-2 claim. The settling Scribe node has `OpenProblemResolutionClaim(Proved)`
and cites `Library/Zeros/mane2026vanishing.md`. The axiom closure of every
public declaration is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.

## Triage

### What the settlement shows

**Proved in this module — the full permitted range.** `result` establishes
(6.4) for every $k\ge2$ and $2\le s\le k+1$. Its private `A_identity`,
`A_trunc`, `G_coeff_diag` and `a_factor` implement the coefficient argument.

**Proved by the following paper argument — why the pattern stops at $s=k+1$.**
The $r$th summand $B^r$ has degree support in $[kr,(k+1)r]$.
For $r<s$, its largest possible endpoint is $(k+1)(s-1)$, which is
strictly below $sk+1$ exactly when $s\le k+1$. For $r>s$, its lower
endpoint is at least $k(s+1)>sk+1$ for $k\ge2$.
At $s=k+2$, the $r=s-1=k+1$ upper endpoint equals $sk+1$;
its leading coefficient is $(-X)^{k+1}$. The shifted numerator contribution
at degree $(s-1)k+1$ still has only the diagonal summand, because
$s-1=k+1$. Consequently an additional nonzero term $(-X)^{k+1}$ appears.
This is a paper derivation of the sharp next boundary, not an additional
Lean theorem. The kernel-checked window exclusion used within the permitted
range is `G_coeff_diag`.

**Proved by the following paper argument — roots and multiplicities.**
Over $\mathbb C$, the factors $x$, $x^k+1$ and $x^k+s$ have disjoint root
sets for $s\ge2$. Every root of either binomial is nonzero; its derivative
$kx^{k-1}$ is nonzero since $k\ge2$. Thus every root with $x^k=-s$ has
multiplicity one, every root with $x^k=-1$ has multiplicity $s-2$
(and is absent at $s=2$), and zero has multiplicity one.
Complex $k$th roots of $-s$ exist and have $|x|^k=s$; all other nonzero
roots have $|x|^k=1$. Hence $\zeta_{-sk,k}=s$ throughout the proved range,
including the restricted attainment range of Conjecture 6.6 for $k\ge3$.
These are algebraic consequences of `result` proved here on paper; no
separate Lean multiplicity or supremum theorem is delivered.

**Computed — $s=k+2$.** For $k=2,\ldots,7$, exact symbolic recurrence
calculations give six of six matches for

$$
\mathcal F_{-k(k+2),k}(x)=-xQ_k(x^k),\qquad
Q_k(t)=(t+k+2)(1+t)^k+(-1)^kt.
$$

The required orchestrator script `python3 /tmp/op-mane/check64.py`, exit $0$,
gives 27 of 27 in-range matches and six of six failures of (6.4) at
$s=k+2$, for $k=2,\ldots,7$. The supplemental self-contained script
`python3 /tmp/op-mane/stageb/boundary64.py`, exit $0$, additionally checks
the displayed $Q_k$ identity in six cases and the root-factor multiplicities
in all 27 in-range cases. These computations establish only their finite
scope; the uniform boundary argument is the paper proof above, with its
Lean formalization open here.

**Open — the source's broader simplicity sentence.** The source says
“All such roots appear to be simple” for $j\in[2,k+1]$ with $x^k=-j$
at the additional negative indices discussed on p. 19. The in-range $j=s$ roots are simple by the paper
argument above and have exact symbolic multiplicity one in all 27 tested
cases. Simplicity at other indices is open here. The $x^k=-1$ roots are
outside $j>1$ and can have multiplicity $s-2$; they do not refute that sentence.

**Open — neighbouring questions and dependence.** Conjecture 6.5,
the universal upper-bound clause and asymptotic branch claims of
Conjecture 6.6 are not settled here. The companion settlement #14674 refutes
unrestricted attainment. This identity supplies attainment only in the stated
restricted range. Any source use of (6.4) within that range can use the
proved identity; extrapolations beyond it gain no premise from this result. In particular,
the p. 20 inference of unbounded growth at fixed $k$ is not justified by
(6.4): its parameter $s$ is bounded by $k+1$, and the $s=1$ case cited
there is outside the conjecture's $s\ge2$ range.

### Reproducible symbolic checks

The scripts require Python 3 and SymPy. Save the following exact UTF-8 bytes
at the named command paths, or run equivalent local paths. The computations
are exact polynomial expansions and gcd/division checks, with no numerical
tolerance.

Command: `python3 /tmp/op-mane/check64.py`. Exit code: $0$.
SHA-256: `e7ee83f451689b57f35da62752803542cf7acab552b81e0c6980ffe2eeb6e214`.

```python
import sympy as sp
x=sp.symbols('x')
def F(k, nmin):
    vals={1:sp.Integer(1)}
    for n in range(-(k-2),1): vals[n]=sp.Integer(0)
    n=1
    while n-k>=nmin:
        vals[n-k]=sp.expand(vals[n]-sum(x**(k-j)*vals[n-j] for j in range(1,k)))
        n-=1
    return vals
ok=0; bad=0
for k in range(2,8):
    v=F(k,-k*(k+2))
    for s in range(2,k+2):
        lhs=v[-s*k]; rhs=sp.expand(-x*(x**k+1)**(s-2)*(x**k+s))
        if sp.expand(lhs-rhs)==0: ok+=1
        else: bad+=1; print("FAIL",k,s)
    # s=k+2 fails?
    s=k+2; print(k, "s=k+2 matches pattern:", sp.expand(v[-s*k]+x*(x**k+1)**(s-2)*(x**k+s))==0)
print("pattern holds", ok, "fails", bad)
```

Command: `python3 /tmp/op-mane/stageb/boundary64.py`. Exit code: $0$.
SHA-256: `535eb1b77cb46fcff894c432957caac480507c9d1e764d9e75bfff399f4b4e63`.

```python
import sympy as sp
x=sp.symbols('x')
def F(k, nmin):
    vals={1:sp.Integer(1)}
    for n in range(-(k-2),1): vals[n]=sp.Integer(0)
    n=1
    while n-k>=nmin:
        vals[n-k]=sp.expand(vals[n]-sum(x**(k-j)*vals[n-j] for j in range(1,k)))
        n-=1
    return vals
ok=0; bad=0
for k in range(2,8):
    v=F(k,-k*(k+2))
    for s in range(2,k+2):
        lhs=v[-s*k]; rhs=sp.expand(-x*(x**k+1)**(s-2)*(x**k+s))
        if sp.expand(lhs-rhs)==0: ok+=1
        else: bad+=1; print("FAIL",k,s)
    # s=k+2 fails?
    s=k+2; print(k, "s=k+2 matches pattern:", sp.expand(v[-s*k]+x*(x**k+1)**(s-2)*(x**k+s))==0)
print("pattern holds", ok, "fails", bad)

q_matches=0; root_matches=0
def multiplicity(p,q):
 count=0
 while True:
  quo,rem=sp.div(p,q,x)
  if rem!=0:return count
  p=quo;count+=1
for k in range(2,8):
 vals=F(k,-k*(k+2)); s=k+2
 q=(x**k+k+2)*(1+x**k)**k+(-1)**k*x**k
 assert sp.expand(vals[-k*s]+x*q)==0
 q_matches+=1
 for s in range(2,k+2):
  f=vals[-k*s]
  assert multiplicity(f,x)==1
  assert multiplicity(f,x**k+s)==1
  assert multiplicity(f,x**k+1)==s-2
  assert sp.gcd(x**k+s,sp.diff(x**k+s,x))==1
  assert sp.gcd(x**k+1,sp.diff(x**k+1,x))==1
  root_matches+=1
print('Boundary Q_k identity matches:',q_matches,'/ 6')
print('Root-factor multiplicities match:',root_matches,'/ 27')
```

## ASSUMED-UNVERIFIED

Exhaustive absence of a prior settlement is not established by the finite
literature search. The general root-multiplicity, amplitude and sharp-boundary
consequences have paper proofs here but no separate Lean declarations.
The broader simplicity assertion and neighbouring conjectures identified
above remain open here.
