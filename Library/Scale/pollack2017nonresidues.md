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
