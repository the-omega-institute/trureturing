---
bibkey: pollack2017nonresidues
authors: Paul Pollack
year: 2017
title: Bounds for the first several prime character nonresidues
doi: 10.1090/proc/13432
url: https://arxiv.org/pdf/1508.05035v2
claim: Theorem 1.1 supplies prime counts; its published real-character inputs also yield fixed reciprocal-prime mass with modulus zeros retained, usable for actual affine sources only when the enlarged cutoff reaches the Robin prefix.
strata_touched: []
license: citation-only
triage: anchor
---

# Prime nonresidues with the actual exceptions retained

The [author publication list](https://www.pollack-math.net/research.html)
identifies the article as *Proceedings of the American Mathematical Society*
145 (2017), 2815–2826, [DOI:10.1090/proc/13432](https://doi.org/10.1090/proc/13432).
The inspected sources are
[arXiv:1508.05035v2](https://arxiv.org/abs/1508.05035v2), dated 24 August
2015 in its submission history, and the [author-hosted manuscript](https://www.pollack-math.net/hudson.pdf).
Theorem 1.1 appears on p.1 of v2 and p.2 of the author manuscript;
Propositions 2.1–2.2, the smooth-number input on pp.2–3, the coprime
count in the proof of Lemma 2.6 on p.6, and Theorem 1.2 were also inspected.
The weighted deduction below is an application of those published inputs,
not a quoted statement of Theorem 1.1. Their complete original analytic
proofs and the weighted/Robin applications were not independently
formalized in Lean. The linked local mod-eight application has its own
limited verification scope. No complete current literature survey or
numerical analytic onset threshold is claimed.

## The existing uniform supply

For every fixed $\varepsilon>0$, Theorem 1.1 gives constants
$m_0(\varepsilon)$ and $\kappa(\varepsilon)>0$ such that every integer
$m>m_0$ and every nonprincipal Dirichlet character $\chi$ modulo $m$ have
more than $m^\kappa$ primes $\ell$ satisfying

$$
\ell\le m^{\beta},\qquad
\chi(\ell)\notin\{0,1\},\qquad
\beta=\frac1{4\sqrt e}+\varepsilon.
$$

For quadratic characters the nonresidue value is $-1$. The statement is not
restricted to prime moduli or primitive characters. Its threshold and count
exponent are not supplied here as numerical constants, so it is not a
finite numerical certificate. The theorem is unconditional; GRH and a
zero-free-region assumption are absent from its hypotheses.

For an explicitly stated reciprocal-prime weight supply, reuse
[Bourgain–Lindenstrauss, Theorem 5.1](bourgainlindenstrauss2003entropy.md).
Its cutoff is $Y\ge D^{1/4+\varepsilon}$ for sufficiently large positive
nonsquare $D$. The linked note records its exact weighted Robin budget
and actual-source exceptions; the prime-count theorem here does not
automatically supply that weight at $Y=\log N$.

Theorem 1.2 strengthens the cutoff for characters of higher order, using
the Dickman-function parameter $u_k$. Quadratic characters have order two,
so their parameter is $u_2=\sqrt e$; increasing the modulus does not increase
their order. Proposition 2.1 records Norton's Burgess estimate. Its extra
factor is $R_k(m)=\min\{M(m)^{3/4},Q(k)^{9/8}\}$; for $k=2$, $Q(k)=1$.
Thus the source already handles composite quadratic moduli. Reproving a
prime-modulus Burgess estimate would not improve this interface.

## A weighted real-character consequence of the published inputs

Put $\beta_0=1/(4\sqrt e)$. Fix

$$
\beta_0<b<\frac14,\qquad 0<c<\log(4\sqrt e\,b).
$$

The source inputs give the following paper-level consequence: there is
$M(b,c)$ such that every integer $m\ge M(b,c)$ and every real nonprincipal
Dirichlet character $\chi$ modulo $m$ satisfy

$$
W_\chi(m^b):=
\sum_{\substack{\ell\le m^b\\\chi(\ell)=-1}}\frac1\ell\ge c.
$$

The modulus need not be prime and the character need not be primitive.
Primes dividing $m$ remain zeros. This conclusion is obtained from the
following inputs; it is not attributed as a separately stated theorem in
Pollack, nor asserted to be unpublished or original.

* Proposition 2.1 records K. K. Norton's *A character-sum estimate and
  applications*, Acta Arithmetica 85 (1998), 51–78, Theorem 1.6. For order
  two, $R_2(m)=1$, so for fixed integer $r\ge1$ and $\eta>0$ it gives
  $|\sum_{k\le x}\chi(k)|\ll_{r,\eta}
  x^{1-1/r}m^{(r+1)/(4r^2)+\eta}$.
* Proposition 2.2 records the $c=1$ case of G. Tenenbaum's *Cribler les
  entiers sans grand facteur premier*, Philosophical Transactions of the
  Royal Society A 345 (1993), 377–384. With $u=\log x/\log y$, it gives
  $\Psi_q(x,y)=(\varphi(q)/q)\Psi(x,y)(1+O(
  \log(1+u)\log(1+\omega(q))/\log y))$ when $x\ge y\ge2$,
  $P^+(q)\le y$ and $\omega(q)\le y^{1/\log(1+u)}$.
* The smooth-number asymptotic $\Psi(x,x^{1/u})\sim\rho(u)x$ for fixed
  $u$, and $\rho(u)=1-\log u$ for $1\le u\le2$, are recorded on pp.2–3.
  These are additional inputs, not consequences of Proposition 2.2 alone.
* Inclusion–exclusion gives
  $C_m(z):=\#\{k\le z:(k,m)=1\}=z\varphi(m)/m+O(2^{\omega(m)})$.
  The corresponding coprime-multiple count is used on p.6 in Lemma 2.6.

To check the deduction, choose fixed $a>1/4$ sufficiently close to $1/4$
that $1<u:=a/b<\sqrt e$ and $\rho(u)-1/2>c$. Set
$x=m^a$, $y=m^b$, and $A_m=\varphi(m)/m$.
Choosing $r$ large and $\eta$ small in Norton's estimate gives
$\sum_{k\le x}\chi(k)=o(xA_m)$ uniformly. Indeed, its power relative to
$x$ is $(1/4-a)/r+1/(4r^2)+\eta<0$, while
$A_m=m^{-o(1)}$ and $2^{\omega(m)}=m^{o(1)}$.
Thus

$$
\#\{k\le x:\chi(k)=1\}=(1/2+o(1))xA_m.
$$

For the coprime smooth count take
$q=\prod_{p\mid m,\ p\le y}p$. Proposition 2.2's hypotheses hold
uniformly for large $m$: $u$ is fixed, $\omega(q)=O(\log m)$, and its
allowed upper bound is a positive power of $m$. Its remark gives
$\Psi_m(x,y)=\Psi_q(x,y)$, and $\varphi(q)/q\ge A_m$. Consequently

$$
\Psi_m(x,y)\ge(\rho(u)-o(1))xA_m.
$$

The number $B$ of $y$-smooth integers at most $x$ with $\chi(k)=-1$ is
therefore at least $(\rho(u)-1/2-o(1))xA_m$. Each has a prime factor
$\ell\le y$ with $\chi(\ell)=-1$, and such a prime is coprime to $m$.
Counting its **coprime** multiples gives

$$
\begin{aligned}
B&\le\sum_{\substack{\ell\le y\\\chi(\ell)=-1}}C_m(x/\ell)\\
&\le xA_mW_\chi(y)+O(y2^{\omega(m)}).
\end{aligned}
$$

After division by $xA_m$, the error is $m^{b-a+o(1)}=o(1)$, proving the
claimed weight. Counting all multiples as $x/\ell$ instead would retain an
unnecessary factor $A_m$ in the lower bound. The coprimality bookkeeping
is what preserves constant weight despite the additional modulus zeros.

There is no exceptional-real-character deletion in these inputs. No
numerical value for $M(b,c)$ has been extracted, and no exact compiled
application of this analytic deduction is claimed.

## What is required at the same arithmetic source

The [FIB theory volume](../../docs/develop/theory/FIBONACCI_ATOMIC_RELATION_GENERATION.md)
already owns the norm identities and character Euler-product estimates in
§§178,181,202. They are reused here.

For §181's actual $N=Cu$, an odd prime with $\chi(\ell)=-1$ is excluded from
the primitive factor $u$, but may still divide the multiplier $C$. To obtain
a prime missing from $N$, the supplied prime must also satisfy
$\ell\nmid C$ and $\ell\ne2$. The multiple-prime statement can survive
deleting a finite exceptional set $E$ when $|E|<m^\kappa$; the source's
full cutoff must still lie in the required actual prime prefix. A bound
for the first nonresidue alone does not remove the multiplier cost.
The actual-source examples in §§183,186 already show why that cost matters.

For §202's affine $N=h+gU$, the induced character modulo $4|D|$, with
$D=5h^2-4g^2Q$ nonsquare, takes only values $0,1$ at primes dividing $N$.
A prime where that induced character is $-1$ is consequently missing from
$N$. If instead one uses the primitive character of conductor $q$, all
primes dividing $2D$ remain exceptions: primes in the square part of $D$
may disappear from $q$ without disappearing from the original certificate.
Square $D$ gives a principal character and is outside Theorem 1.1's scope.
For odd affine offsets, the [actual mod-eight certificate](banksgaraevheathbrownshparlinski2008density.md)
recovers the prime-two contribution when the primitive character is
negative there; the actual square-part intersection still has to be retained.

One standard way to retain a finite exceptional set is to induce the
primitive character to a modulus $M$ divisible by $q$ and by every prime
in $E$. Theorem 1.1 applies to that nonprincipal induced character and its
nonresidue primes automatically avoid $E$. The cutoff then involves
$M^\beta$, not merely $q^\beta$. Alternatively, retaining modulus $q$
requires enough supplied primes to survive deletion of $E$. These are
applications of the cited result, not new character estimates.

For a CA integer with support containing every prime through
$P=P^+(N)$, exclusion by a missing prime requires the supplied prime to be
at most **that actual $P$**. The Euler-product split $x=\log N$ in
§§178,181,202 is a different parameter. A usable source application must
establish its cutoff below $P$; it cannot substitute $x$ for $P$ without
the required comparison.

The existing canonical norm estimate $q<4N/g^2$ in §182.2 does not ensure
that $q^\beta\le\log N$, much less that the exceptions-adjusted cutoff is
at most $P$. A fixed positive power of a modulus comparable to a positive
power of $N$ exceeds $\log N$ asymptotically. This is a limitation of the
available bound at those parameters, not a lower bound on the actual first
nonresidue and not a counterexample to Robin. Restricted families with a
sufficiently small actual modulus may use the theorem, while all-candidate
conductor, exception and weighted-deficit control remains missing.

Finding one omitted prime is also not, for a general integer, a complete
Robin certificate. Its contribution must pay the actual remaining Euler
budget using the same source. No general Robin or RH conclusion, new
analytic theorem, or new Lean declaration is claimed here.

## The enlarged modulus at the actual Robin cutoff

For §202's actual affine source, the original conservative modulus
$m=4|D|$ already preserves every prime-two and square-part zero. Its
negative primes all miss the same $n$, without an oddness assumption on
$h$. If $h$ is odd, write $D=\Delta t^2$ with $\Delta$ signed squarefree.
Then $\Delta\equiv1\pmod4$ is the fundamental discriminant, and either
$m=|D|$ or $m=\operatorname{rad}|D|$ supports the induced character

$$
\chi_m(k)=\chi_\Delta(k)\mathbf1_{(k,m)=1}.
$$

Both choices retain all raw-square-part zeros; the linked mod-eight
certificate also excludes two whenever $\chi_m(2)=-1$. Thus, whenever
$m\ge M(b,c)$ and $m^b\le Y=\log n$,

$$
J_{\rm miss}(n;Y)
=\sum_{\substack{p\le Y\\p\nmid n}}\log\frac p{p-1}
\ge W_{\chi_m}(m^b)\ge c.
$$

The supplied weight already avoids the enlarged modulus: no square-part
subtraction is silently discarded. The benefit of a smaller faithful
modulus is a smaller cutoff. However, $|D|\to\infty$ does not imply
$\operatorname{rad}|D|\to\infty$; a radical-based application still needs
its own $m\ge M(b,c)$ check. Fixed or bounded moduli can use earlier
fixed-character results, not an unspecified large-modulus threshold.

In particular fix $0<\delta<4\sqrt e$, put $K=4\sqrt e-\delta$, and choose

$$
\beta_0<b<\min\{1/4,1/K\},\qquad
0<c<\log(4\sqrt e\,b).
$$

Along actual affine sources with $n\to\infty$, $D$ nonsquare, $|D|\to\infty$,
and $|D|\le(\log n)^K$, use $m=4|D|$. The strict margin $Kb<1$ absorbs
the factor four, so $m^b\le\log n$ eventually. The
[same-integer Euler budget](bourgainlindenstrauss2003entropy.md) then
implies the paper-level consequence

$$
\limsup\frac{Z(n)}{e^\gamma\log\log n}\le e^{-c}<1.
$$

This admits signed nonsquare discriminants, composite conductors and raw
square parts. Relative to the previously recorded positive-$D$ cutoff
$D^{1/4+\varepsilon}$, it also admits fixed raw-discriminant log-powers
strictly below $4\sqrt e$ instead of strictly below four. Intersections
with the old safe families are applications, not new safe-family claims.

A concrete canonical realization of the additional range reuses
§205.1, not a new FIB construction. For $j\equiv1\pmod6$, take
$g=j^3$, $h=1$, and the seed $v=\alpha=(1,0)$. Then

$$
(A_j,B_j)=j^3M^jv,\qquad n_j=j^3F_{j+3}+1.
$$

The contraction readout is $A_j+B_j\psi=j^3\psi^j\to0$ from below.
Eventually it lies in $(-1,\varphi-1)$, so the existing canonical-window
test permits the external unit bit without changing the legal window
word or End. The same actual composition gives

$$
Q(A_j,B_j)=-j^6,\qquad D_j=4j^6+5,
\qquad (2j^3)^2<D_j<(2j^3+1)^2\quad(j>1).
$$

In particular $D_j$ is nonsquare and
$D_j\sim4(\log n_j/\log\varphi)^6$. For every fixed
$\beta_0<b<1/6$, the cutoff $(4D_j)^b$ is eventually at most
$\log n_j$. Taking all $0<c<\log(4\sqrt e\,b)$ and then $b\uparrow1/6$
gives the paper-level application

$$
\limsup_{\substack{j\to\infty\\j\equiv1\pmod6}}
\frac{Z(n_j)}{e^\gamma\log\log n_j}
\le\frac3{2\sqrt e}<1.
$$

No primality or squarefreeness of $D_j$ is used. Here $D_j\equiv1\pmod8$
and $n_j$ is even, so the prime-two shortcut supplies no missing weight.
The raw discriminant lies outside every previously recorded
$D\le(\log n)^{4-\delta}$ range. The variant with $g=j$ has log-power two
and was already covered by that earlier interface; it is not a new safe
family. The original character-product sufficient condition in §202.4
also does not cover this cubic-multiplier sequence: for $m=4D_j$,
$(2+\log m)m/\varphi(m)$ is at least order $\log\log n_j$, not little-o
of it. The result here remains a source-derived asymptotic application,
without a numerical onset or Lean verification of the analytic chain.

General candidates need not have nonsquare $D$ or satisfy this joint
modulus/cutoff restriction. These applications do not replace that missing
all-candidate estimate, and do not prove general Robin or RH.
