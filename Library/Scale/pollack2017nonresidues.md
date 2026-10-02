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

## Prime-power exceptions for the actual unit bit one

The conservative induction above retains every raw square-part zero.
For an actual canonical source with **unit bit $h=1$**, a smaller faithful
exception set can be read from the same prime-power exponents and the
same five-window lift. The following is a paper-level local refinement;
it supplies no new analytic nonresidue estimate or Lean verification.

Let $n>2$, $n=1+2A+3B$, $c=4A+7B$, and
$D=5-4(A^2+AB-B^2)$ be nonsquare. Write

$$
D=\delta s^2,\qquad s\ge1,\qquad
\delta\text{ signed squarefree},\qquad q=|\delta|.
$$

Positive and negative discriminants are admitted. Since $D\equiv1\pmod4$,
$s$ is odd and $\delta\equiv1\pmod4$, so $\delta$ itself is the fundamental
discriminant. Let $\chi$ be its primitive nonprincipal quadratic character
of conductor $q$. The existing FIB identity is

$$
c^2-\delta s^2=5n(n-2).
\tag{P1}
$$

If an odd prime has $\chi(p)=-1$, then

$$
v_p(c^2-\delta s^2)=2\min\{v_p(c),v_p(s)\}.
\tag{P2}
$$

Unequal valuations cannot cancel; equal valuations could cancel only if
$\delta$ became a nonzero square modulo $p$. In particular, writing
$e_p=v_p(n)>0$, a negative-character support prime $p\ne2,5$ must have
$e_p$ even and $v_p(c),v_p(s)\ge e_p/2$, since $p\nmid n-2$.
For $p=5$, negativity instead forces $e_5$ odd and both valuations at least
$(e_5+1)/2$. An odd-exponent support prime other than five cannot be a
hidden negative prime after removal of the raw square part.

Define the potential-exception set and required depths by

$$
\mathcal P_1=
\{p\mid n:p\ne2,5,\ e_p\text{ even}\}
\cup\{5:5\mid n,\ e_5\text{ odd}\},\qquad
b_p=\begin{cases}e_p/2,&p\ne5,\\(e_5+1)/2,&p=5.\end{cases}
$$

Use the actual lift, rather than a free residue, to set

$$
H_1=\prod_{p\in\mathcal P_1}p^{b_p},\qquad
\mathcal E_1=\{p\in\mathcal P_1:p^{b_p}\mid c\},\qquad
T_1=\prod_{p\in\mathcal E_1}p^{b_p},\qquad
R_1=\operatorname{rad}(T_1).
$$

The set $\mathcal E_1$ contains every negative-character support prime;
its other members need not be negative. All its membership tests are
determined by $c\bmod H_1$. The same-object divisibility relations are

$$
H_1\mid5\frac n{\operatorname{rad}(n)},\qquad
T_1\mid\gcd(c,s),\qquad qT_1^2\mid|D|.
\tag{P3}
$$

For $p\ne5$, $b_p=e_p/2\le e_p-1$. For five this inequality holds when
$e_5\ge3$; $e_5=1$ is paid by the displayed extra factor five.
For each $p\in\mathcal E_1$, both $c^2$ and $5n(n-2)$ are divisible by
$p^{2b_p}$. Thus $p^{2b_p}\mid D$, so $p^{b_p}\mid s$, proving the
remaining relations in (P3).

Set $m_1=\operatorname{lcm}(q,R_1)$ and induce the character by
$\widetilde\chi_1(k)=\chi(k)\mathbf1_{(k,m_1)=1}$. Then

$$
\widetilde\chi_1(p)=-1\Longrightarrow p\nmid n,\qquad
m_1\mid\operatorname{rad}|D|,\qquad
m_1\le qR_1\le |D|\frac{R_1}{T_1^2}.
\tag{P4}
$$

For odd support primes the first statement follows from (P2) and the mask.
If $n$ is even, $c$ is odd and $8\mid n(n-2)$, so $D\equiv1\pmod8$ and
$\chi(2)=1$; if $n$ is odd, two is already missing. This handles the prime
two without transporting an odd-prime argument to it. The second
statement holds because $q$ and $R_1$ are squarefree divisors of $|D|$.

The extra factor five is necessary in this construction. The canonical
source $n=95$ has $(A,B)=(14,22)$, $c=210$, $D=-75=-3\cdot5^2$ and
$\chi(5)=-1$. Here $H_1=T_1=R_1=5$, $m_1=15$, while
$n/\operatorname{rad}(n)=1$.

The exponent excess is exactly

$$
B_{\rm exp}(n)=\log\frac n{\operatorname{rad}(n)}
=\sum_{p\mid n}(e_p-1)\log p,\qquad
\log H_1\le\log5+B_{\rm exp}(n).
$$

Under the additional SA support asymptotic
$\operatorname{rad}(n)=n^{1-o(1)}$, this gives $H_1=n^{o(1)}$.
It does not bound the primitive conductor $q$ or guarantee
$m_1^b\le\log n$. Whenever the existing weighted supply can actually
reach the cutoff for $m_1$, (P4) lets that supplied negative-prime weight
contribute to $J_{\rm miss}$ without deleting the listed exceptions again.
The missing estimate must still cross the full same-integer Euler budget;
$D$ square, unit bit zero and uncontrolled $q$ remain separate branches.

## A canonical family outside the sufficient conductor cutoff

The [canonical local-residue construction](grahamringrose1990least.md#a-canonical-source-with-vanishing-logarithmic-character-weight)
uses the same actual unit-one source and has $D\asymp n$,
$Y=\log n\sim2z$, no negative primitive-character prime up to $z$,
and $W_\delta^{\log}(Y)\to0$. It retains the ramified zero at three.
Its primitive conductor $q=\delta$ satisfies $q>z$: choose
$1\le a<q$ with $\chi_\delta(a)=-1$. Its prime factors have nonzero
character, and at least one has value $-1$, hence lies strictly between
$z$ and $q$. In particular $q\to\infty$.

For each preassigned $\beta_0<b<1/4$, choose
$0<c<\log(4\sqrt e\,b)$. The weighted consequence above gives
$W_{\chi_\delta}(q^b)\ge c$ once $q$ reaches its stated threshold.
If $q^b\le Y$, then

$$
c\le W_{\chi_\delta}(q^b)
\le W_\delta^{\log}(Y),
$$

which contradicts the latter's convergence to zero. Thus this canonical
family eventually has

$$
q^b>\log n,\qquad m_1^b\ge q^b>\log n.
$$

The actual primitive conductor already exceeds this sufficient cutoff;
an improved upper certificate for $m_1$ cannot change that fact on this
family. The onset may depend on the fixed $b,c$. This is a paper-level
application of the existing weighted estimate, not a new analytic theorem,
an assertion $q\asymp n$, or an obstruction proved on SA/CA candidates.

## The terminal CA prime band forces a conductor lower bound

The preceding canonical family is not established to be an asymptotic CA family. For
actual CA sources, a different restriction follows by applying the
published [Thorner–Zaman prime count](thornerzaman2019chebotarev.md).
This is a paper-level application of existing analytic and canonical
interfaces, without a new analytic theorem, originality claim or Lean
verification.

Let $n$ be any actual CA maximizer, including an intermediate tied
maximizer, and put $P=P^+(n)$. Retain its own canonical unit bit $h$,
coordinates $A,B$, $c=4A+7B$, and signed discriminant
$D=5h^2-4(A^2+AB-B^2)$. In the branch $h=1$ with nonsquare $D$,
write $D=\delta s^2$ as above and let $q$ be its primitive quadratic
conductor. The existing prime-power exception result gives

$$
p\mid n,\quad p\ne2,5,\quad\chi_\delta(p)=-1
\quad\Longrightarrow\quad v_p(n)\text{ is even}.
\tag{T3}
$$

This implication is reused at the same source; no canonical coordinates
are transported from a larger representative. Primes dividing $q$
remain character zeros.

### The terminal support consists of exponent-one primes

At the actual CA price $\epsilon$, use the classical thresholds
$F(\xi_k,k)=\epsilon$, with $\xi=\xi_1$. The
[Nicolas manuscript](https://hal.science/hal-05389053v1/document),
equation (3.8) and Remark 3.1, printed p.11, give the prime-layer support
and tied choices; (3.19)–(3.23), printed pp.12–13, give
$\xi_2\le\sqrt{2\xi}$. Every prime below $\xi$ has strictly positive
first-layer gain and is included. A first-layer tie can only affect the
possible endpoint prime $\xi$. Hence $P\sim\xi$ by ordinary PNT,
while $\xi_2=o(P)$.

Every sufficiently large actual CA integer therefore satisfies

$$
v_p(n)=1\qquad\text{for every prime }P/2<p\le P.
\tag{T4}
$$

Indeed $P/2>\xi_2$ eventually: each such prime is in the initial support
and has strictly negative second-layer gain. A tied square activation
at $\xi_2$ lies below this band. The argument permits every tied
maximizer, rather than only the all-ties representative.

### The primitive conductor is bounded below at the same candidate

Let $C,x_0$ be the constants in the linked interval consequence (T2).
If $P>\max\{10,2\xi_2\}$ and $P\ge x_0$, (T3)–(T4) prohibit any
prime $p\in(P/2,P]$ with $\chi_\delta(p)=-1$. If $q^C\le P$,
(T2) instead supplies at least $P/(8\log P)$ such primes. Consequently,
with a fixed $\eta=1/C>0$,

$$
\boxed{q>P^\eta}
\tag{T5}
$$

for every sufficiently large actual CA integer in this $h=1$,
nonsquare-$D$ branch. No numerical CA onset or infinitude of this
particular canonical branch is supplied.

This is a lower bound for the actual primitive conductor, rather than
for the raw discriminant or an upper-bound certificate for the mask.
Since $m_1=\operatorname{lcm}(q,R_1)\ge q$, it also gives
$m_1>P^\eta$. On an unbounded branch of these sources, neither $q$ nor
$m_1$ can be bounded by a fixed power of $\log P$.

For the existing sufficient cutoff $m_1^b\le Y=\log n$, the necessary
range is now

$$
P^\eta<q\le m_1\le Y^{1/b},\qquad P\sim Y.
\tag{T6}
$$

The small fixed $\eta$ supplied here leaves that interval compatible;
it does not exclude fixed-power-in-$\log n$ conductors. No
reciprocal-prime deficit, exception-weight payment or signed Robin
margin follows. Unit-bit-zero sources, square discriminants and the
remaining larger conductors still require their own estimates. The
[raw-discriminant chain witnesses](../ArithSums/fibcomplement2026weightedresidues.md#recurring-doubling-activations-improve-the-unbounded-subset-rate)
are not known to belong to this canonical branch, so their bound cannot
be combined with (T5) by treating separately realized witnesses as one
source. No actual Robin violation or RH proof is obtained.

### A numerical exponent from the published progression interval

The independently published [Haynes–White interval theorem](hayneswhite2014intervals.md)
supplies a prime in $(P/2,P]$ with $\chi_\delta(p)=-1$ whenever
$q\le P^\eta$, for every fixed $0<\eta<5/67$ and sufficiently large
$P$. Applying the same contradiction (T3)–(T4), without reconstructing
either interface, gives the numerical version

$$
\boxed{q>P^\eta\quad\text{eventually for every fixed }0<\eta<5/67}
\tag{T7}
$$

on the same actual $h=1$, nonsquare-$D$ CA branch. The eventual onset
can depend on $\eta$ and is not claimed effective. For example
$q>P^{1/14}$ eventually. The effective existential version (T5) is
retained independently; no comparison of its unnamed exponent with
$5/67$ is asserted.

This numerical rate still leaves the useful faithful-mask cutoff
compatible. For example $b=1/5$ allows $m_1\le Y^5$, while the lower
bound is only $m_1>P^{1/14}$ and $P\sim Y$. A conductor lower bound
$q>P^\eta$ would contradict $m_1^b\le Y$ by powers alone if
$\eta b>1$; equality requires further constant or lower-order
information. The supplied rate does not cross that scale in the
stated $\beta_0<b<1/4$ regime. All same-source and unresolved-branch
limitations above remain in force.

## The progression count crosses the deep-layer capacity

A published quantitative count now gives a stronger numerical conductor
restriction than (T7). Reuse [Maynard, published Theorem 3.2](maynard2013bruntitchmarsh.md)
through (M2), without reconstructing its proof or the preceding canonical
and CA layer interfaces. This is a paper-level same-source application,
with no new analytic theorem, originality claim or Lean verification.

Take an actual CA maximizer $n$, including intermediate tied maximizers,
whose own canonical unit bit is $h=1$ and whose own signed $D$ is
nonsquare. Let $q$ be its primitive quadratic conductor and $P=P^+(n)$.
Every prime up to $P$ belongs to its initial support. By (T3), every
negative-character prime there, except possibly two and five, has even
positive exponent and therefore is at most $\xi_2$. The existing
$\xi_2\le\sqrt{2\xi}$ and $P\sim\xi$ give a fixed constant $C_A>0$
such that, eventually at every such source,

$$
\pi_-(P;\chi)\le\pi(\xi_2)+2
\le C_A\frac{\sqrt P}{\log P}.
\tag{T8}
$$

This is an upper bound for the same actual negative-prime population;
ramified primes remain zeros. It does not assume every prime below
$\xi_2$ has even exponent.

Suppose instead that $q\le P^{1/8}$ and $q\ge q_0$, where $q_0,c_0$
are Maynard's effective constants. Then $P\ge q^8$ and (M2) supplies

$$
\pi_-(P;\chi)\ge\frac{c_0}{2}
\frac{P\log q}{\sqrt q\log P}
\ge\frac{c_0\log q_0}{2}
\frac{P^{15/16}}{\log P}.
\tag{T9}
$$

The ratio of (T9)'s lower bound to (T8)'s upper bound tends to infinity
at least as a positive constant times $P^{7/16}$, uniformly throughout
this conductor range. For the finitely many $q<q_0$, reuse (T2) from the
[earlier effective terminal-interval supplier](thornerzaman2019chebotarev.md)
with $P\ge\max\{x_0,q_0^C\}$; its negative primes in $(P/2,P]$
contradict (T4). Thus

$$
\boxed{q>P^{1/8}}
\tag{T10}
$$

for every sufficiently large actual CA source in this canonical $h=1$,
nonsquare-$D$ branch. The exact endpoint is allowed here because
Maynard's supplied range is $P\ge q^8$. No numerical CA onset or
infinitude of this branch is asserted.

For fixed $\beta_0<b<1/4$, any sufficiently large actual source in
this branch that also satisfies the sufficient cutoff
$m_1^b\le Y=\log n$ must have its faithful mask in the range

$$
P^{1/8}<q\le m_1\le Y^{1/b},\qquad Y=\log n\sim P.
$$

This is still compatible with the existing $\beta_0<b<1/4$ cutoff;
for example $b=1/5$ permits an upper scale $Y^5$. The count comparison
excludes a larger conductor range than (T7), but supplies neither a
reciprocal-prime deficit nor the required signed Robin margin. Unit-bit
zero, square $D$ and the larger remaining conductors stay unresolved.

## All odd layers strengthen the signed-character restriction

Together with a fixed contradiction assumption $q\le P^\eta$, the
numerical bound (T10) supplies the compact parameter range needed to use [Szabó's published Proposition 6](szabo2024primeproducts.md)
with the actual alternating CA layers. Reuse (T3), the classical
thresholds and the literature estimate (S1); no new analytic theorem,
originality claim or Lean verification is made.

Continue with the same actual CA integer, its canonical $h=1$,
nonsquare signed $D$, primitive quadratic character $\chi$ of conductor
$q$, and $P=P^+(n)$. Put $L=\log P$. All asymptotics below hold along
every sequence of such actual maximizers with $P\to\infty$, including
intermediate tied choices; this quantification asserts no branch
infinitude. For every fixed $k\ge1$, the classical activation formula gives

$$
\frac{\log\xi_k}{L}\longrightarrow\frac1k.
\tag{T11}
$$

Indeed, $F(x,k)\sim1/(x^k\log x)$, and
$F(\xi_k,k)=F(\xi_1,1)$ gives $\xi_k^k\sim k\xi_1$, with
$\xi_1\sim P$. This is a fixed-layer consequence of the existing CA
formula. A prime of exponent $k$ lies between $\xi_{k+1}$ and $\xi_k$,
apart from the tied endpoints. In the logarithmic coordinate
$u=\log p/L$, the odd layers therefore approach

$$
\mathcal O=\bigcup_{j\ge0}
\left(\frac1{2j+2},\frac1{2j+1}\right),\qquad
\int_{\mathcal O}du=\log2,\quad
\int_{\mathcal O}u\,du=\frac{\pi^2}{24}.
$$

For each fixed $r\ge1$, Mertens' first theorem and partial summation give

$$
A_r(n):=\sum_{\substack{p\le P\\v_p(n)\ \mathrm{odd}}}
\frac{\log p}{p}\left(r-\frac{\log p}{L}\right)
=\left(r\log2-\frac{\pi^2}{24}+o(1)\right)L.
\tag{T12}
$$

Here $\mathrm{odd}$ means the exponent $v_p(n)$ is odd. First fix
$K$ and let $P\to\infty$ on the finitely many retained layers, then
let $K\to\infty$. Their tied endpoint primes contribute
$o(L)$ regardless of the intermediate maximizing choice. All omitted
layers lie below $\xi_{K+1}$ and have total weight at most
$r\log\xi_{K+1}+O_r(1)=O_r(L/(K+1))+o(L)$. Letting $K$ grow after
$P$ proves (T12), without a uniform-in-$k$ threshold asymptotic.

At every odd-exponent support prime other than two and five, (T3)
prohibits $\chi(p)=-1$. Thus its value is $1$ unless $p\mid q$, when
it is zero. The latter correction is bounded by

$$
r\sum_{p\mid q}\frac{\log p}{p}
=O_r(\log\log(q+3)).
\tag{T13}
$$

For large $q$, split at $p=\log q$: the smaller-prime contribution is
$O(\log\log q)$ by Mertens, and the remaining contribution is at most
$(\log q)^{-1}\sum_{p\mid q}\log p\le1$. The fixed primes two and
five cost $O_r(1)$. In a range $q\le P^\eta$ with fixed $\eta>0$,
these corrections are $o(L)$.

Define the same-character sum over all primes, including those beyond
$P$,

$$
S_r(\chi;P)=\sum_p\frac{\chi(p)\log p}{p}
\left(r-\frac{\log p}{L}\right)_+.
$$

Its total unsigned weight is $(r^2/2+o(1))L$. Give all primes outside
the protected odd layers the worst permissible value $-1$; keep the
ramified corrections (T13). This yields

$$
S_r(\chi;P)\ge
\left(2r\log2-\frac{\pi^2}{12}-\frac{r^2}{2}+o(1)\right)L.
\tag{T14}
$$

To compare (S1), put $t=L/\log q$ and $\alpha=rt$. Then
$f_\alpha(\log p/\log q)=t(r-\log p/L)_+$. In a contradiction range
$P^{1/8}<q\le P^\eta$, supplied by (T10), $\alpha$ lies in a fixed
compact interval. For fixed order bound two, the error in (S1) is
uniform over the varying characters and moduli at each fixed mesh value
of $\alpha$, as noted in the source citation. To make it uniform over
this compact interval, use a finite mesh, the bound $|f_\alpha-f_\beta|\le|\alpha-\beta|$,
and $\sum_{p\le q^A}\log p/p=O_A(\log q)$. First take $q\to\infty$
for this finite mesh, then let its spacing tend to zero. Consequently

$$
S_r(\chi;P)\le\frac r8\log q+o_{r,\eta}(L).
\tag{T15}
$$

Combining (T14)–(T15) gives

$$
\frac{\log q}{\log P}\ge
16\log2-\frac{2\pi^2}{3r}-4r-o(1).
$$

The right side is maximized for $r\ge1$ at $r=\pi/\sqrt6$. Hence, with

$$
c_*:=16\log2-\frac{8\pi}{\sqrt6}
=0.829956247664\ldots,
$$

one obtains the paper-level necessary condition

$$
\boxed{q>P^\eta\quad\text{eventually for every fixed }0<\eta<c_*}
\tag{T16}
$$

for every actual CA source in this canonical branch, including
intermediate ties. For $\eta\le1/8$, (T10) already suffices; the
compact-parameter contradiction proves the remaining range.
No endpoint $\eta=c_*$, branch infinitude or effective onset is claimed.
The constant is the optimum of this particular triangular weight family,
not an optimum over all explicit-formula weights.

The later odd layers are material. Keeping only the terminal logarithmic
band $(1/2,1]$ would instead give the lower coefficient
$r-3/4-r^2/2=-(r-1)^2/2-1/4<0$, so this weight supplies no contradiction
from that band alone. No square-depth distribution estimate is supplied here.

Even (T16) leaves the sufficient faithful-mask cutoff compatible:
$c_*b<1$ for $\beta_0<b<1/4$. This proves neither $q^b\le P$ nor
the faithful-mask condition. No weighted missing-prime deficit,
signed Robin margin, h=0 exclusion, square-$D$ exclusion or RH proof
follows. Every character and layer in the comparison belongs to the
same actual integer; no separately realized raw-$D$ witnesses are joined.

### A quantified same-source eligibility condition that would cross the cutoff

The preceding bound alone does not cross the sufficient cutoff. The
existing set $\mathcal E_1$, however, gives a specific missing FIB readout
for this signed supplier. For fixed $r\ge1$, define its actual moment

$$
M_r(n)=\sum_{\substack{p\le P,\ p\ne2,5\\v_p(n)\ \mathrm{even}\\p^{v_p(n)/2}\mid c}}
\frac{\log p}{p}\left(r-\frac{\log p}{L}\right).
\tag{T17}
$$

This is the weight of the same source's supported potential exceptions,
not the weight of an independently selected residue class. Its membership
is determined by the existing readout $c\bmod H_1$.
The total support weight is $(r-1/2+o(1))L$. Every negative support
prime outside two and five belongs to this set. Keeping the conductor-zero
cost (T13), one can therefore replace (T14) by

$$
S_r(\chi;P)\ge
\left(2r-1-\frac{r^2}{2}+o(1)\right)L-2M_r(n).
\tag{T18}
$$

In any fixed power range $q\le P^C$, (T15) then gives the conditional
comparison

$$
\frac{\log q}{L}\ge
16-\frac8r-4r-\frac{16M_r(n)}{rL}-o(1).
\tag{T19}
$$

The range is available whenever the same source satisfies
$m_1^b\le Y=\log n$, since $q\le m_1$ and $Y\sim P$.
Fix $b=6/25$, which lies in $\beta_0<b<1/4$, and $r=\sqrt2$.
For any fixed coefficient

$$
0\le\mu<\frac{71\sqrt2}{96}-1
=0.045928780505\ldots,
$$

the two conditions

$$
M_{\sqrt2}(n)\le\mu\log P,\qquad m_1^{6/25}\le\log n
\tag{T20}
$$

are incompatible at every sufficiently large actual CA source in the
$h=1$, nonsquare-$D$ branch. Indeed, (T19)'s lower coefficient exceeds
$25/6$, whereas the cutoff gives
$\log q/L\le25/6+o(1)$. The strict fixed gap absorbs both errors.
This is a conditional application of the same published signed estimate;
neither condition in (T20) is established for all remaining candidates.

The unrestricted even-layer envelope is only

$$
M_r(n)\le
\left(r(1-\log2)-\frac12+\frac{\pi^2}{24}+o(1)\right)L,
$$

whose coefficient at $r=\sqrt2$ is $0.345188935617\ldots$. It does
not imply the required $0.045928\ldots$ bound. The missing work is an
actual-source upper estimate for square-depth membership in
$c=4A+7B$, sufficiently strong at this weighted scale, together with
coverage of sources outside the cutoff. No distribution law, h=0 or
square-$D$ exclusion, reciprocal-prime deficit or RH proof is supplied.

## The actual mask pays the moment and leaves the reachable cutoff

The modulus in (P4) is $m_1=\operatorname{lcm}(q,R_1)$, so both
$q\le m_1$ and $R_1\le m_1$ hold for the same actual canonical source.
A polynomial mask cap therefore controls the moment in (T17), in addition
to the primitive conductor. This is an application of existing results,
without a new analytic theorem, originality claim or Lean verification.

Continue on the actual CA source, whose initial support contains every
prime through $P$. For fixed $C>0$, suppose $m_1\le P^C$. Then every
prime in (T17) divides $R_1$; splitting at $L=\log P$ gives

$$
0\le M_r(n)\le r\sum_{p\mid R_1}\frac{\log p}{p}
\le r\sum_{p\le L}\frac{\log p}{p}
+\frac rL\log R_1
\le r\log L+O_{r,C}(1)=o(L).
\tag{T21}
$$

This reuses the same two-range Mertens estimate as (T13), here split
at $L=\log P$. It requires no
independence, residue distribution or additional upper hypothesis about
the same source's square-depth membership. In particular the cutoff
$m_1^{6/25}\le\log n\sim P$ would imply the moment condition in (T20)
for any fixed $0<\mu<71\sqrt2/96-1$, at sufficiently large sources.
The combined (T19) lower coefficient $16-8\sqrt2=4.686291\ldots$
then exceeds $25/6$. This already rules out that joint cutoff.

A stronger existing supplier directly applies to the faithful mask.
The induced character $\widetilde\chi_1\bmod m_1$ is nonprincipal and
quadratic: reduction from units modulo $m_1$ to units modulo $q$ is
surjective, so a negative unit of the primitive character has a unit
lift. Formula (P4) says every prime with
$\widetilde\chi_1(\ell)=-1$ is missing from the actual integer.
For every actual CA maximizer with largest prime $P$, including ties,
all primes through $P$ are supported. Thus every such negative prime
satisfies $\ell>P$.

Along any unbounded sequence in this actual branch, the mask tends to
infinity with $P$. Indeed a negative unit represented
by $1\le a<m_1$ has a negative prime factor $\ell\le a<m_1$;
faithfulness gives $P<\ell<m_1$. Reuse the original published
Theorem 1.1 above, whose character need not be primitive. For every fixed
$\varepsilon>0$ and sufficiently large masks, it supplies a negative prime

$$
P<\ell\le m_1^{\beta_0+\varepsilon},
\qquad \beta_0=\frac1{4\sqrt e}.
$$

Consequently, for every fixed $0<\eta<4\sqrt e$, choosing
$\varepsilon$ with $\eta(\beta_0+\varepsilon)<1$ gives

$$
\boxed{m_1>P^\eta\quad\text{eventually}.}
\tag{T22}
$$

The statement covers every actual $h=1$, nonsquare-$D$ CA source with
its own faithful mask, including intermediate ties; it asserts no
infinitude of this branch, endpoint $\eta=4\sqrt e$ or numerical onset.
It is a lower bound for the full mask, not for the primitive conductor
$q$ alone. This direct use of Pollack's theorem is stronger than the
mask bound obtainable from (T21) and the triangular signed estimate;
neither analytic proof is repeated.

For any fixed $b>\beta_0$, choose $1/b<\eta<4\sqrt e$ in (T22).
Since $P\sim\log n$ on these actual CA sources,

$$
\frac{m_1^b}{\log n}\longrightarrow\infty
\tag{T23}
$$

along every unbounded sequence in this branch. Thus the sufficient
cutoff $m_1^b\le\log n$ has no sufficiently large realization there,
including the weighted supplier's entire $\beta_0<b<1/4$ regime.
The conductor-only lower bounds in (T10) and (T16) remain valid; their
numerical power comparison alone omitted this further mask constraint.

This excludes applicability of that small-mask route at large CA sources;
it proves no Robin violation or safety there. Outside a polynomial mask
cap, (T21) supplies no $o(L)$ bound for the actual moment. The full
large-mask signed Robin estimate, unit bit zero and square discriminants
remain unresolved. An average on free Beatty indices or independently
selected residues cannot discharge this same-source obligation.
