---
slug: stampach-waclawek-2026-birman-weight-expansion
bibkey: stampachwaclawek2026birman
doi: null
url: https://arxiv.org/abs/2605.25238v1
triage: theorem
motivation_gids:
  - D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.result
---

# Štampach–Waclawek's alternative Birman weight expansion

## Problem

F. Štampach and J. Waclawek, *Optimal discrete p-Hardy–Rellich–Birman
inequalities*, arXiv:2605.25238v1, Conjecture 5.6(iii), p. 28:

> Let $\ell\in\mathbb N$ and $p>1$, and let $\tilde{\rho}^{(\ell,p)}$ be defined by (2.17) and (2.16).

> For all $n\geq\ell$, the terms $\tilde{\rho}_{n}^{(\ell,p)}$ admit a power series expansion in negative powers of $n$ with entirely non-negative coefficients; cf. (2.15).

Here $\mathbb N$ means positive integers. The convention is
$\tilde{\mathfrak g}_n=n^{1-1/p}\prod_{j=1}^{\ell-1}(n-j)$ for $n\geq0$,
with zero extension to negative integers;
$(\nabla u)_n=u_n-u_{n-1}$ and $(\mathrm{div}\,u)_n=u_{n+1}-u_n$;
$\nu^{\langle a\rangle}=\nu|\nu|^{a-1}$, with
$0^{\langle a\rangle}=0$; and
$\tilde\rho_n=(-1)^\ell[\mathrm{div}^{\ell}(m\mapsto(\nabla^{\ell}\tilde{\mathfrak g})_m^{\langle p-1\rangle})]_n/\tilde{\mathfrak g}_n^{p-1}$,
with signed power taken before the divergence iterate.

The Lean `claim` asks for one non-negative coefficient sequence
$c:\mathbb N_0\to\mathbb R$ whose series converges to
$n^{\ell p}\tilde\rho_n$ at every $n\geq\ell$. It allows any
non-negative constant coefficient. The source's (2.15) normalization implies
this claim by $c_0=((1/q)_\ell)^p$ and $c_k=c_0 A_k$ for $k\geq1$,
where $1/q=1-1/p>0$ and the rising factorial is positive.
Thus negating the weaker claim refutes part (iii).

## Motivation

Non-negative coefficients would make successive truncations increase and
would constrain all adjacent secant slopes of the normalized weight as a
function of $x=1/n$. The declaration
`D5/S3/Analytic/SeriesInequalities/StampachWaclawekExpansionRefutation.result`
proves $\neg\mathrm{claim}$, using $\ell=2$ and $p=11/10$.
Only Conjecture 5.6(iii) is refuted.

## Gap

Preregistration #14466 records the tier-1 statement and source/literature
checks. Its literature readings cover arXiv v1, MathDB `/p/374928`
(Solutions 0 in the recorded reading), and the citing paper arXiv:2608.26936,
which treats fractional quadratic operators. No settlement was found in
that searched scope. These are literature readings, not an exhaustive
priority claim. The cited Library note is
`Library/Analytic/stampachwaclawek2026birman.md`.

## Route

Set $G(n)=n^{2p}\tilde\rho_n$ at $p=11/10$. The finite certificate gives

| $n$ | lower bound for $G(n)$ | upper bound for $G(n)$ |
| --- | --- | --- |
| 100 | $80296519661/10^{12}$ | $40148259831/(5\cdot10^{11})$ |
| 200 | $39752071871/(5\cdot10^{11})$ | $79504143743/10^{12}$ |
| 400 | $79107698317/10^{12}$ | $39553849159/(5\cdot10^{11})$ |

Integer-power comparisons give rational enclosures of the required real
roots. The proof uses `Real.le_rpow_inv_iff_of_pos`,
`Real.rpow_inv_le_iff_of_pos` and `Real.rpow_natCast`.
Those enclosures imply

$$
-\frac{257467}{2500000000}\leq
200G(100)-600G(200)+400G(400)
\leq-\frac{32183}{312500000}<0.
$$

Non-negative coefficients force the opposite sign, by
`convexOn_pow`, `ConvexOn.slope_mono_adjacent`, `hasSum_le`,
`HasSum.sub` and `HasSum.div_const`. The three pointwise convergence
assumptions suffice. All these named dependencies are used in the
module's elaborated proof terms.

## Falsifier

For the non-negative expansion claim, the certified decreasing secant
slopes at $x=1/400,1/200,1/100$ are a falsifier. The result has no
additional assumptions. A sign error in the difference convention, a
wrong rational enclosure, or a failure of the source-to-claim normalization
would invalidate this interpretation; the definitions, exact comparisons
and convergent-series normalization specify the corresponding checks.

## Evidence

The module's public definitions are `gT`, `grad`, `dv`, `spow`, `rhoT`,
`claim`; its only public theorem is `result : ¬ claim`. Its proof uses
ordinary kernel-checked rational arithmetic, with no `native_decide`,
`sorry` or additional axiom. The accepted axiom closure is contained in
$\{\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}\}$.
The private `certified_slope_gap_bounds` and
`no_nonnegative_expansion` supply the finite contradiction.

The computations in Triage are reproducible using Python with `mpmath`
and `sympy`. The following sources are included in full. Write each block
verbatim to its filename and run the command shown; SHA-256 covers its
UTF-8 bytes including the final newline. Neither computation establishes
convergent-series coefficient identification in Lean.

### check.py

Command: `python3 check.py`. Measured exit code: 0.

SHA-256: `731f366790617e714fed465cbd08759c68190d365a6220686aa1c09fecafb89f`.

```python
from mpmath import mp, mpf, power, rf
mp.dps=80
def rho(n,p,l=2):
    a=1-1/mpf(p); r=mpf(p)-1
    def g(m): return power(mpf(m),a)*(m-1) if m>=0 else mpf(0)
    def b(m): return g(m)-2*g(m-1)+g(m-2)
    return (power(b(n),r)-2*power(b(n+1),r)+power(b(n+2),r))/power(g(n),r)
def F(n,p,l=2):
    a=1-1/mpf(p); C=rf(a,l)
    return rho(n,p,l)*power(mpf(n),l*mpf(p))/power(C,p)
for p in [mpf(11)/10, mpf(21)/20, mpf(6)/5, mpf(3)/2, mpf(2)]:
    # estimate A1, A2 by Richardson on large n
    Ns=[10**6,2*10**6,4*10**6]
    A1s=[n*(F(n,p)-1) for n in Ns]
    # A1(n) ~ A1 + A2/n + A3/n^2 ; Richardson twice
    r1=[2*A1s[i+1]-A1s[i] for i in range(2)]; A1=(4*r1[1]-r1[0])/3
    A2s=[n*n*(F(n,p)-1-A1/n) for n in Ns]
    r2=[2*A2s[i+1]-A2s[i] for i in range(2)]; A2=(4*r2[1]-r2[0])/3
    print('p',mp.nstr(p,6),'A1',mp.nstr(A1,15),'A2',mp.nstr(A2,15))
beta=lambda p: 1/mpf(p)
for p in [mpf(11)/10, mpf(21)/20, mpf(6)/5, mpf(2)]:
    bt=beta(p); B1=bt*(bt-3)/(bt-2); B2=bt*(bt+1)*(7*bt-26)/(12*(bt-2))
    print('p',mp.nstr(p,4),'seat B1',mp.nstr(B1,10),'B2',mp.nstr(B2,10))
# direct check at p=11/10: F(n) vs 1 + A1/n for moderate n
p=mpf(11)/10
for n in [10,100,1000,10**4]:
    print(n, mp.nstr(F(n,p),25))
# l=1 sanity: rho~(1,p) with g=n^{1-1/p}; compare with source A_k^{(1,p)}=(p)_k/p^k/(k+1)!
def rho1(n,p):
    a=1-1/mpf(p); r=mpf(p)-1
    g=lambda m: power(mpf(m),a) if m>=0 else mpf(0)
    d=lambda m: g(m)-g(m-1)
    return -(power(d(n+1),r)-power(d(n),r))/power(g(n),r)
p=mpf(11)/10; a=1-1/p
Fs=lambda n: rho1(n,p)*power(mpf(n),p)/power(a,p)
Ns=[10**6,2*10**6,4*10**6]
A1s=[n*(Fs(n)-1) for n in Ns]; r1=[2*A1s[i+1]-A1s[i] for i in range(2)]; A1=(4*r1[1]-r1[0])/3
A2s=[n*n*(Fs(n)-1-A1/n) for n in Ns]; r2=[2*A2s[i+1]-A2s[i] for i in range(2)]; A2=(4*r2[1]-r2[0])/3
print('l=1 p=1.1 A1',mp.nstr(A1,12),'src',mp.nstr(rf(p,1)/p/2,12),' A2',mp.nstr(A2,12),'src',mp.nstr(rf(p,2)/p**2/6,12))
```

### coefficient-check-stage-b.py

Command: `python3 coefficient-check-stage-b.py`. Measured exit code: 0.

SHA-256: `acee6a4b915956b8540026299a73818e73db0010d52a23706aa94ab43df2bfff`.

```python
import sympy as s
from mpmath import mp
mp.dps = 80
p, t = s.symbols("p t")
a = 1 - 1 / p
r = p - 1
B1 = (1-a)*(a+2)/(a+1)
B2 = (a-1)*(a-2)*(7*a+19)/(12*(a+1))
d1 = r*B1
d2 = r*B2 + r*(r-1)*B1**2/2
e1 = d1*(a+2)/a - (a+2)
e2 = d2*(a+2)*(a+3)/(a*(a+1)) - d1*(a+2)*(a+3)/a + s.Rational(7,12)*(a+2)*(a+3)
N = 16*p**6 + 8*p**5 - 4*p**4 - 60*p**3 + 44*p**2 - 11*p + 1
A2 = N/(4*p*(2*p-1)**3)
assert s.factor(e2 + r*e1 + r*(r+1)/2 - A2) == 0
assert s.factor(e1+r-2*p**2/(2*p-1)) == 0
print("Taylor-algebra identities: exact zero residuals")
print("N(1+t) =", s.expand(N.subs(p,1+t)))
assert N.subs(p,s.Rational(11,10)) == -s.Rational(146709,62500)
print("N(11/10) =", N.subs(p,s.Rational(11,10)))
for q in [s.Rational(21,20),s.Rational(11,10),s.Rational(6,5),s.Rational(3,2),s.Integer(2)]:
    print("p", q, "A2 exact", A2.subs(p,q), "decimal", s.N(A2.subs(p,q),30))
f = lambda z: 16*z**6+8*z**5-4*z**4-60*z**3+44*z**2-11*z+1
p0 = mp.findroot(f,(mp.mpf(11)/10,mp.mpf(6)/5))
assert mp.mpf(11)/10 < p0 < mp.mpf(6)/5
print("p0 =", mp.nstr(p0,65))
print("polynomial residual =", mp.nstr(f(p0),8))
```

## Triage

### What the settlement shows

1. **Proved in this module — finite failure mechanism.** At $\ell=2$,
   $p=11/10$, the values at $n=100,200,400$ violate the adjacent slope
   condition forced by non-negative coefficients. `result` refutes (iii)
   without assuming or identifying an asymptotic expansion.

2. **Computed — candidate second coefficient and its derivation.** In the
   (2.15) normalization, the Taylor-algebra expression is

   $$
   A_2^{(2,p)}=
   \frac{16p^6+8p^5-4p^4-60p^3+44p^2-11p+1}{4p(2p-1)^3}.
   $$

   Put $a=1-1/p$, $r=p-1$, $C=a(a+1)$, $x=1/n$.
   The backward second difference of $g(n)=n^{a+1}-n^a$ formally has
   $b(n)=Cn^{a-1}(1+B_1x+B_2x^2+O(x^3))$, where
   $B_1=(1-a)(a+2)/(a+1)$ and
   $B_2=(a-1)(a-2)(7a+19)/(12(a+1))$.
   With $d_1=rB_1$, $d_2=rB_2+r(r-1)B_1^2/2$,
   the forward second difference gives
   $e_1=d_1(a+2)/a-(a+2)$ and
   $e_2=d_2(a+2)(a+3)/(a(a+1))-d_1(a+2)(a+3)/a+7(a+2)(a+3)/12$.
   Division by $g(n)^r$ contributes $(1-x)^{-r}$, so
   $A_1=e_1+r=2p^2/(2p-1)$ and
   $A_2=e_2+re_1+r(r+1)/2$.
   `python3 coefficient-check-stage-b.py`, exit 0, verifies these
   algebraic identities exactly. Control of Taylor remainders and their
   passage through the second difference, and identification with the
   convergent expansion's coefficient, remain **open in Lean**.

3. **Computed — five Richardson comparisons.**
   `python3 check.py`, exit 0, uses 80-digit arithmetic and
   $n=10^6,2\cdot10^6,4\cdot10^6$, only for $\ell=2$ in its `rho`/`F`
   calculation. The displayed `l` argument there is not a general-order
   implementation.

   | $p$ | Richardson estimate of $A_2$ | closed-form value |
   | --- | --- | --- |
   | $21/20$ | $-0.842142007433545$ | $-18830969/22360800$ |
   | $11/10$ | $-0.308731060600727$ | $-16301/52800$ |
   | $6/5$ | $0.521433430516817$ | $107311/205800$ |
   | $3/2$ | $2.16145833332958$ | $415/192$ |
   | $2$ | $4.12499999999019$ | $33/8$ |

   Each discrepancy is below $1.1\cdot10^{-11}$ in this tested scope.
   The script's $\ell=1$ control is for the alternative weight; its
   `src` values are for the source's original weight, a different sequence,
   so their unequal coefficients do not contradict the source.

4. **Computed with an elementary sign argument — near-one sign and threshold.**
   For $t=p-1$ the numerator is
   $16t^6+104t^5+276t^4+324t^3+160t^2+17t-6$.
   Its nonconstant terms increase for $t>0$. Thus for
   $0<t\leq1/10$ it is at most $-146709/62500$, with positive
   denominator. The candidate expression is negative on
   $1<p\leq11/10$, and positive at $6/5,3/2,2$.
   It has a unique zero for $p>1$ because the numerator is strictly
   increasing in $t>0$. Numerically,
   $p_0=1.1336988558272561451661954078450210494168012824253351778274496976$,
   between $11/10$ and $6/5$; the 80-digit polynomial residual is
   $-5.060255\cdot10^{-80}$.
   Evidence: `python3 coefficient-check-stage-b.py`, exit 0, with the
   source and SHA-256 in Evidence. This is not a Lean-checked uniform
   expansion-coefficient theorem.

5. **Proved (paper argument) — the source's proved cases survive.** Positivity for
   $\ell=1$ and for $p=2$ stands: the paragraph after (2.17) identifies
   the alternative weights with the earlier optimal weights, and the
   paragraph before Conjecture 5.6 cites their proved restricted cases.
   Remark 2.12's explicit formulas concern the original weight $\rho$;
   they are not substituted for the alternative weight $\tilde\rho$.
   The proved counterexample has $\ell=2$ and $p=11/10$; the computed
   near-one failure is at $\ell=2$. No claim for every $\ell\geq2$
   follows from this certificate.

6. **Open — neighbouring questions.** Does (iii) hold for $\ell=2$
   and $p\geq p_0$? Does it hold for integer $p\geq2$ at arbitrary
   positive order? Do Conjecture 5.6(i) and (ii) hold throughout their
   stated range? These are follow-up candidates; this module settles
   none of them. A non-negative second coefficient alone does not imply
   that every coefficient is non-negative.

7. **Computed, with a conditional paper argument — truncations.**
   For the alternative weight at $\ell=2$, let
   $W_1(n)=C^p n^{-2p}(1+A_1/n)$ and
   $W_2(n)=C^p n^{-2p}(1+A_1/n+A_2/n^2)$.
   Their difference is $W_2(n)-W_1(n)=C^p A_2 n^{-2p-2}$.
   The computed sign therefore makes $W_2<W_1$ for
   $1<p\leq11/10$ and $n\geq2$; gradual improvement by adding that
   term fails for this alternative-weight candidate. This is conditional
   on coefficient identification and does not assert that either
   truncation is itself a valid Hardy weight. Remark 2.12 proposes
   truncations for the original weight $\rho$. Its original-weight
   conjecture, established results and truncation proposal are not
   refuted by this alternative-weight certificate.

## ASSUMED-UNVERIFIED

Literature completeness and priority beyond the recorded searched scope
are unverified. The candidate coefficient's convergent-series
identification and uniform Taylor remainder bounds are not Lean-checked.
The numerical root is not a certified root enclosure. Only part (iii),
via the finite witness at $\ell=2,p=11/10$, is settled by this module.
