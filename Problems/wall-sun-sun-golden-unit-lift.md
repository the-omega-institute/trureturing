---
slug: wall-sun-sun-golden-unit-lift
bibkey: shi2026second
doi: 10.48550/arXiv.2603.25343
triage: wall
motivation_gids:
  - D5/S0/Carrier/Ring
  - D5/S0/Carrier/Conj
  - D5/S0/Carrier/Norm
  - D5/S0/Carrier/Units
  - D5/S1/Scale/Units
  - D5/S1/Scale/UnitGroup
  - D5/S1/Scale/Fibonacci
  - D5/S3/Arith/FibonacciRank
  - D5/S3/Arith/GoldenApparition
  - D5/S3/Arith/GoldenPrimeSplitting
  - D5/S3/Arith/GoldenPell
---

# Wall-Sun-Sun primes as a golden-unit lift problem

## Problem

Let `pi(m)` be the Pisano period, the least positive period of the Fibonacci
recurrence modulo `m`. The primary problem is whether there exists a prime `p`
with `pi(p) = pi(p^2)`. The paper also records the stronger conjecture that
infinitely many such primes exist.

Quoted from the introduction of arXiv:2603.25343v1:

> “A natural question was asked by Wall in his paper: Can there be a prime
> \(p\) such that \(\pi(p)=\pi(p^2)\)?”

> “It is known that up to \(10^{14}\), there are no such primes (cf. [16]).
> Still, using heuristics and probabilistic arguments, some authors conjecture
> the existence of infinitely many primes \(p\) satisfying
> \(\pi(p)=\pi(p^2)\) [7, 11].”

The same paper identifies the classical case with `d = 5` and says there are no
known `WSS(5)` primes.

Candidate formal statement, after defining `pisanoPeriod`:

```text
Existence:  ∃ p : Nat, Nat.Prime p ∧ pisanoPeriod p = pisanoPeriod (p^2)
Stronger:   Set.Infinite {p | Nat.Prime p ∧ pisanoPeriod p = pisanoPeriod (p^2)}
```

The paper states the difficulty:

> “The question of Wall for these sequences is related to certain deep
> arithmetic properties of real quadratic fields.”

It makes this precise for its generalized recurrence: equality of the periods
modulo `p` and `p^2` corresponds, subject to stated hypotheses, to failure of
`p`-rationality of the associated real quadratic field. This is why the global
existence question is not a routine finite-period exercise.

## Motivation

- Multiplication by `phi` on the basis `(1, phi)` is the Fibonacci matrix.
  Frozen `Scale/Fibonacci` already expresses powers of `phi` in Fibonacci
  coordinates.
- `GoldenApparition` and `FibonacciRank` control the first Fibonacci zero modulo
  a prime and the `p ± 1` Frobenius index; `GoldenPrimeSplitting` supplies the
  split/inert division according to 5 modulo `p`.
- The period can therefore plausibly be re-expressed as an order of the reduced
  golden unit or Fibonacci matrix. Equality at `p` and `p^2` is then an
  exceptional failure of the usual order multiplication by `p` under lifting.
- The first reachable theorem is not existence. It is an exact bridge among the
  pair recurrence period, the order of the Fibonacci matrix, and the order of
  `phi` in an appropriate golden algebra modulo `p^e` for `e = 1, 2`.

## Gap

- No frozen `pisanoPeriod` or recurrence-period API.
- `GoldenApparition` works modulo a prime; there is no golden algebra modulo
  `p^2` and no Hensel or p-adic order-lift theorem.
- There is no `p`-rational field or p-adic logarithm machinery.
- PID/UFD facts and the global unit classification alone do not decide the
  exceptional local lift.

## Route

1. Define the Fibonacci matrix `A = [[0,1],[1,1]]` over `ZMod m`; prove that
   `pi(m)` is its multiplicative order by tracking `(F_n, F_{n+1})`.
2. Define the reduction of `GoldenInt` over `ZMod m` and identify multiplication
   by `phi` with `A`.
3. For `r = pi(p)`, write the first lift as `A^r = I + pB (mod p^2)`. Prove
   `pi(p^2) = pi(p)` if and only if `B = 0 (mod p)`, and that otherwise the
   period acquires the expected factor `p`.
4. Use the frozen split/inert and apparition results to reduce the required
   congruence to a Fibonacci/Lucas quotient modulo `p`, separately in the two
   Legendre-symbol cases.
5. Only after those bridge theorems exist should a theorist choose between a
   conditional nonexistence theorem for a prime class, a density heuristic, or
   the global Wall question. Do not jump from a finite scan to existence.

## Falsifier

The existential Wall question has no honest finite falsifier. A proof that no
prime can satisfy the equality would refute it; a proof of finiteness would
refute only the stronger infinitely-many conjecture.

The proposed bridge is finitely falsifiable: find a prime `p` for which the
directly computed pair period disagrees with the order of the Fibonacci
matrix/golden unit, or for which `A^pi(p) = I (mod p^2)` disagrees with
`pi(p^2) = pi(p)`.

## Evidence

Implement three independent exact calculations for every prime `p < 10^6`,
excluding and separately reporting ramified and small cases:

1. direct pair-state Pisano periods modulo `p` and `p^2`;
2. fast-doubling checks of `F_r mod p^2` and `F_{r+1} mod p^2` at `r = pi(p)`;
3. matrix exponentiation of `A^r mod p^2` and the first-lift matrix `B mod p`.

Receipt fields should include `p`, `legendreSym 5 p`, `rank`, `pi_p`, `pi_p2`,
`F_r mod p^2`, `F_(r+1)-1 mod p^2`, and agreement of all three formulations.
This is bridge validation, not evidence that the global existential is false.

## Triage

`wall`. The repository is unusually close to the mod-`p` side, but the decisive
`p` to `p^2` lift is exactly the missing deep layer.

## ASSUMED-UNVERIFIED

- Whether the open problem was resolved after arXiv v1 is unverified; this
  records the paper's statement, not the entire later literature.
- The order of the reduced golden unit matches the chosen Pisano-period
  convention without a factor of 2 or a special case; that must be proved, not
  assumed.
- A useful local quotient criterion can be stated entirely with the current
  `GoldenInt` coordinate model.
- Any novelty of the proposed bridge lemmas is unassessed and belongs to the
  theorist's search step.

## Mathematical continuation: inert parity in primitive Fibonacci blocks

### IP.1 Fixed field and the parity readout

Keep the original field $K=\mathbb Q(\sqrt5)$ and the original unit
$\phi=(1+\sqrt5)/2$, with conjugate $\psi=1-\phi$. Write
$\chi(m)=(m/5)$. For primes $p\ne2,5$, quadratic reciprocity identifies
$\chi(p)$ with $(5/p)$; its value is $-1$ precisely for inert primes.
Let $r(p)$ be the least positive index with $p\mid F_{r(p)}$, and set

$$
h_p=v_p(F_{r(p)})=v_p(F_{p-\chi(p)}).
$$

The equality uses the classical rank bound $r(p)\mid p-\chi(p)$ and the
Fibonacci valuation formula; the multiplying index is coprime to $p$.
The standard WSS condition is $h_p\ge2$.

**Theorem IP1.** For every positive integer $M$ coprime to five,

$$
\chi(M)=(-1)^{c(M)},\qquad
c(M)=\#\{p\mid M:p\text{ prime},\ \chi(p)=-1,\ v_p(M)\text{ odd}\}.
$$

**Proof.** Apply the multiplicative character to the unique prime
factorization. A split prime contributes $1$ at every exponent; an inert
prime contributes $(-1)^{v_p(M)}$. Reducing the exponent sum modulo two
leaves exactly the displayed count of distinct odd-exponent inert primes.
Thus there are two linked parities: the parity of each exponent, and the
parity of the number of negative contributions. This is a multiplicative
readout with values in the two-element group. It retains one bit of each
exponent and does not distinguish depths one and three.

**Literal bridge to the existing involution theorem.** Fix an inert
integer $q$, so $\chi(q)=-1$. On the integer-state carrier take
$\operatorname{step}(M)=qM$, readout $\chi(M)$, and visible flip
$z\mapsto-z$. Multiplicativity proves
$\chi(\operatorname{step}(M))=-\chi(M)$, and the flip is involutive.
This instantiates
`D5/S3/ObserverMemory/Refinement/InvolutiveReadoutCompletion` and gives

$$
\chi(q^{2j}M)=\chi(M),\qquad
\chi(q^{2j+1}M)=-\chi(M).
$$

When $q\ge2$ and $M>0$, $q^2M>M$, even though its character has returned.
Thus the previous odd/even readout result has an explicit arithmetic
realization here. Equality of that readout does not recover the exponent
or the original integer, and no identification with Zeckendorf digit
parity is being assumed.

**Lemma IP2.** For every $n\ge1$,

$$
F_n\equiv n3^{n-1}\pmod5.
$$

In particular, for every odd $n$, $\chi(F_n)=\chi(n)$, including zero
character at multiples of five.

**Proof.** The right side has the Fibonacci initial values modulo five.
Writing $u_n=n3^{n-1}$ gives
$u_{n+2}-u_{n+1}-u_n=5(n+3)3^{n-1}$, so induction proves the formula.
For odd $n$, the factor $3^{n-1}$ is a nonzero square modulo five.

**Corollary IP3, the original prime-index block.** For each prime
$\ell\ge7$ with $\chi(\ell)=-1$, every prime $p\mid F_\ell$ satisfies
$r(p)=\ell$ and $v_p(F_\ell)=h_p$. The number of such primes that are
inert and have odd $h_p$ is odd, hence positive.

**Proof.** The number $F_\ell$ is odd because its index is not divisible
by three, and it is coprime to five by IP2. A prime divisor has rank
strictly greater than one dividing the prime $\ell$, so its rank is
$\ell$. Apply IP1 and IP2. The ordinary Fibonacci identities and rank
facts here are classical; this is the fixed-field specialization of the
character argument.

For any odd index $n=r(p)$ with $p\ne2,5$, the identity
$L_n^2-5F_n^2=-4$ shows that $-1$ is a square modulo $p$, so
$p\equiv1\pmod4$. If $p$ is inert, then $n\mid p+1$ and consequently

$$
p\equiv2n-1\pmod{4n},\qquad p\ge2n-1,\qquad
p\equiv13\text{ or }17\pmod{20}.                 \tag{IP4}
$$

Indeed, $(p+1)/n$ is $2$ modulo four. These congruences apply to all the
odd-rank inert witnesses below, regardless of their actual depth.

### IP.2 Every prime-power layer has negative character

For an odd prime $\ell\ne5$ and $k\ge0$, define the exact integer

$$
B_{\ell,k}=\frac{F_{\ell^{k+1}}}{F_{\ell^k}}.
$$

**Theorem IP5.** If $\ell\ge7$, then every prime divisor of $B_{\ell,k}$
has exact rank $\ell^{k+1}$, and its exponent in $B_{\ell,k}$ equals its
initial depth $h_p$. These layers are pairwise coprime. Moreover,

$$
\chi(B_{\ell,k})=\chi(\ell),\qquad
B_{\ell,k}\equiv\ell(-1)^{(\ell-1)/2}\pmod5.     \tag{IP5}
$$

Thus, if $\ell$ is inert, every layer contains an odd number of inert
prime divisors having odd initial depth. In particular each layer
supplies a new such prime; IP4 holds with $n=\ell^{k+1}$.

**Proof.** Fibonacci strong divisibility makes the quotient integral.
The rank bound excludes $\ell\mid F_{\ell^j}$: its rank would divide
both $\ell^j$ and $\ell-\chi(\ell)$, forcing rank one. A prime divisor
$p$ of the quotient has rank dividing $\ell^{k+1}$. If its rank divided
$\ell^k$, the valuation formula would give

$$
v_p(F_{\ell^{k+1}})-v_p(F_{\ell^k})=v_p(\ell)=0,
$$

a contradiction. Therefore its rank is exactly $\ell^{k+1}$, and its
quotient exponent is the initial depth. The rank also makes different
layers disjoint in prime support. Primes two and five are absent.

Apply IP2 to numerator and denominator, both units modulo five. Their
ratio is $\ell3^{\ell^k(\ell-1)}$. Since $\ell^k$ is odd, this is
$\ell(-1)^{(\ell-1)/2}$ modulo five. Its quadratic character is
$\chi(\ell)$, giving the displayed identities. IP1 then proves the
odd-count conclusion.

The character identity alone holds more generally for any odd natural
base $\ell$ with $\chi(\ell)=-1$; the exact-rank statement uses primality.
The corresponding Lean candidate distinguishes these scopes.

**Cumulative versus layer parity.** For an inert prime $\ell$,

$$
\chi(F_{\ell^j})=(-1)^j,\qquad
\chi(B_{\ell,k})=-1\quad\text{for every }k.
$$

At an even cumulative exponent the signs of the separate layers cancel.
For example,

$$
F_7=13,\qquad F_{49}=13\cdot97\cdot6168709,
\qquad B_{7,1}=97\cdot6168709.
$$

The inert factors $13$ and $97$ make the cumulative character positive,
while the new layer still has negative character. A positive character
therefore cannot be used to infer that no odd-depth inert factors exist.

### IP.3 Cyclotomic blocks and the ramified specialization

For odd $n>3$ with $5\nmid n$, define

$$
\mathcal C_n=\Phi_n(\phi,\psi)
=\prod_{d\mid n}F_d^{\mu(n/d)},                  \tag{IP6}
$$

where $\Phi_n(X,Y)$ is the homogeneous cyclotomic polynomial and $\mu$
is the integer Moebius function. This is a positive integer: the
homogeneous polynomial is integral and symmetric for $n>1$, so its value
at the conjugates is a rational algebraic integer; the displayed
positive rational product fixes its sign. The product identity follows
from the cyclotomic factorization of $\phi^n-\psi^n$ by Moebius inversion.

**Theorem IP7.** With $\varphi_{\rm E}$ denoting Euler's totient,

$$
\mathcal C_n\equiv3^{\varphi_{\rm E}(n)}\Phi_n(1)\pmod5,
\qquad
\chi(\mathcal C_n)=
\begin{cases}
\chi(\ell),&n=\ell^a\text{ for a prime }\ell,\ a\ge1,\\
1,&n\text{ has at least two distinct prime factors}.
\end{cases}                                      \tag{IP7}
$$

**Proof.** The homomorphism $\mathbb Z[\phi]\to\mathbb F_5$ with
$\phi\mapsto3$ also sends $\psi=1-\phi$ to $3$. Homogeneity gives the
congruence. For $n>2$, $\varphi_{\rm E}(n)$ is even, so its power of three
has quadratic character one. Finally $\Phi_n(1)=\ell$ for a prime power
$n=\ell^a$, and equals one otherwise. One proof of the latter identity
uses $n=\prod_{d\mid n,d>1}\Phi_d(1)$, obtained by evaluating
$(X^n-1)/(X-1)$ at one. Strong induction assigns one factor $\ell$ to
each prime-power divisor and forces every remaining value to one.

IP7 concerns the cyclotomic block. Its prime factors need not all be new
at index $n$. That distinction is essential in the next two sections.

### IP.4 Exact removal of the old prime

Use the classical Fibonacci valuation theorem for $p\ne2,5$:

$$
v_p(F_m)=
\begin{cases}
h_p+v_p(m),&r(p)\mid m,\\
0,&r(p)\nmid m.
\end{cases}
$$

The rank bound ensures $p\nmid r(p)$. This formula retains arbitrary
$h_p\ge1$ and does not assume WSS primes are absent.

**Theorem IP8.** For every odd $n>3$ with $5\nmid n$ and each prime
$p\ne2,5$,

$$
v_p(\mathcal C_n)=
\begin{cases}
h_p,&n=r(p),\\
1,&n=r(p)p^j\text{ for some }j\ge1,\\
0,&\text{otherwise}.
\end{cases}                                      \tag{IP8}
$$

**Proof.** For each positive $m$, write the valuation formula as

$$
v_p(F_m)=h_p\,1_{r(p)\mid m}
+\sum_{j\ge1}1_{r(p)p^j\mid m}.
$$

Only finitely many summands occur for a fixed $m$. Apply divisor Moebius
inversion to IP6. The transform of $1_{a\mid m}$ is $1_{n=a}$, since
$\sum_{d\mid n,\ a\mid d}\mu(n/d)$ is zero unless $n=a$. This gives
$h_p1_{n=r(p)}+\sum_{j\ge1}1_{n=r(p)p^j}$ and proves IP8. At prime two,
for odd $m$ the valuation is $1_{3\mid m}$, so its cyclotomic valuation
is zero for our $n>3$. At prime five it is zero because $5\nmid n$.

**Theorem IP9.** The block $\mathcal C_n$ contains at most one prime
whose rank is less than $n$. If present, that prime $q$ is the largest
prime factor of $n$, its exponent in $\mathcal C_n$ is exactly one, and
$n=r(q)q^j$ for some $j\ge1$.

**Proof.** IP8 supplies the shape and exponent. Since $n$ is odd, $r(q)$
is odd and greater than one. It divides the even number $q-\chi(q)$,
so $r(q)\le(q+1)/2<q$. All prime factors of $r(q)$ are therefore less
than $q$, proving that $q$ is the largest prime factor of $n$. The
largest prime factor is unique.

Let $P=P(n)$ be that largest prime factor, let
$t=n/P^{v_P(n)}$, and define

$$
E_n=\begin{cases}P,&t=r(P),\\1,&t\ne r(P),\end{cases}
\qquad
\mathcal R_n=\mathcal C_n/E_n.
$$

IP8-IP9 prove the exact identity

$$
\boxed{\mathcal R_n=\prod_{r(p)=n}p^{h_p}.}       \tag{IP9}
$$

The product is over prime values. It is finite because all such primes
divide $F_n$. This is a genuinely primitive block; its prime
multiplicities are exactly the initial WSS depths.

### IP.5 Complete parity classification for the primitive block

Define

$$
b(n)=\#\{p:r(p)=n,\ p\text{ prime},\ \chi(p)=-1,\ h_p\text{ odd}\}.
$$

**Theorem IP10.** For odd $n>3$ coprime to five,

$$
(-1)^{b(n)}=\chi(\mathcal R_n)=\chi(\mathcal C_n)\chi(E_n). \tag{IP10}
$$

Consequently $b(n)$ is odd exactly in the following two disjoint cases:

$$
\boxed{
\begin{aligned}
&n=\ell^a\text{ for a prime }\ell\text{ with }\chi(\ell)=-1,
\quad a\ge1;\\
&n=r(q)q^j\text{ for an odd prime }q\text{ with }\chi(q)=-1,
\quad j\ge1.
\end{aligned}}
\tag{IP11}
$$

In all other cases $b(n)$ is even. An even count can be positive.

**Proof.** Apply IP1 to IP9 and use multiplicativity in
$\mathcal C_n=E_n\mathcal R_n$; both characters are nonzero, so
$\chi(E_n)^{-1}=\chi(E_n)$. IP7 and IP9 give the two cases. They are
disjoint: if $n$ is a pure prime power, its possible largest-prime
cofactor $t$ is one, while every prime rank is greater than one. If
$n=r(q)q^j$, then $1<r(q)<q$ and $q\nmid r(q)$, so $n$ has at least two
distinct prime factors. This completes both directions of the
classification, without a hypothesis on any initial depth.

**Unbounded mixed-index consequence.** Fix any odd inert prime $q$ whose
rank $a=r(q)$ is odd. For every $j\ge1$, the primitive block at index
$a q^j$ contains an inert prime of odd initial depth. Such witnesses in
different $j$ are distinct, and each satisfies

$$
r(p)=a q^j,\qquad p\ge2a q^j-1,
\qquad p\equiv13\text{ or }17\pmod{20}.
$$

**Proof.** Inertness makes $5\nmid(q+1)$, hence $5\nmid a$. The index
$a q^j$ is odd, greater than three and coprime to five. Apply the second
case of IP11 and then IP4. Different exact ranks give distinct primes.
For example $q=13,a=7$ yields the entire family $7\cdot13^j$.

This also permits an iterated construction: after choosing such a new
prime $p$, its rank is again odd, so it may be used as the next input.
The lower bound ensures strictly increasing primes. The construction
preserves odd depth, not necessarily depth one.

### IP.6 Exact examples and the WSS boundary

At $n=91=7\cdot13$, the complete factorization is

$$
\mathcal C_{91}=13\cdot741469\cdot159607993.
$$

The factor thirteen has rank seven, so $E_{91}=13$ and

$$
\mathcal R_{91}=741469\cdot159607993=118344378961717.
$$

Here $\chi(\mathcal C_{91})=1$ but
$\chi(\mathcal R_{91})=-1$. The new inert prime is $159607993$, with
rank ninety-one and depth one; $741469$ is split. Thus removing the
old inert factor changes the parity prediction. At $n=153=9\cdot17$,

$$
\mathcal C_{153}=17\cdot7175323114950564593,
\qquad E_{153}=17,
$$

and the remaining factor is an inert prime of rank 153 and depth one.
The small mixed index $n=21$ instead has $\mathcal C_{21}=421$, with a
split prime of rank 21 and no odd-depth inert primitive factor. This
prevents extending the forced-odd assertion to every odd composite
index without the IP11 conditions.

One must distinguish initial depth from later index lifting. For the
old prime thirteen,

$$
v_{13}(F_7)=1,\qquad v_{13}(F_{91})=2,
\qquad q_{13}=F_{14}/13\equiv3\pmod{13}.
$$

The square factor in $F_{91}$ is automatic from multiplying the index
by thirteen; it does not make thirteen a WSS prime. The exact
cyclotomic removal in IP8-IP9 is what separates this automatic factor
from genuinely repeated primitive factors.

All forced witnesses above have $h_p\in\{1,3,5,\ldots\}$. The argument
never forces $h_p=1$, $h_p\ge3$, or any $h_p\ge2$. A simple witness is
non-WSS; an odd deeper witness would already be a WSS prime of depth
at least three. Both possibilities remain in the universal theorem.
The criterion IP11 classifies the parity of a set involving the real
initial depths, but it does not separate those two alternatives.
No WSS existence/nonexistence theorem or newly resolved externally
posed open problem is asserted by this appendix.

### Sources and formalization scope

The rank and valuation inputs are classical. They are recorded in
L. A. Medina and E. Rowland, *p-regularity of the p-adic valuation of the
Fibonacci sequence*, Fibonacci Quarterly 53 (2015), 265-271,
Theorems 1.2 and 1.4, https://arxiv.org/abs/0910.2907 . The separate
prime-two formula in that theorem is retained in IP8. The rank owner
in this repository is `D5/S3/Arith/FibonacciRank.lean`; the Frobenius
owner is `D5/S3/Arith/GoldenApparition.lean`.

For the classical field splitting and residue classes, see M. Ward,
*The prime divisors of Fibonacci numbers*, Pacific Journal of
Mathematics 11 (1961), 379-386,
https://msp.org/pjm/1961/11-1/pjm-v11-n1-p31-p.pdf .
For related primitive-divisor and cyclotomic valuation arguments, see
H. Hong, *On big primitive divisors of Fibonacci numbers*,
arXiv:2312.04354v2, section 5,
https://arxiv.org/html/2312.04354v2 . The occurrence of an old
cyclotomic prime is classical; IP8 supplies its exact elementary
specialization here rather than claiming that phenomenon as new.

N. Fellini and M. Ram Murty, *Wieferich primes in number fields and the
conjectures of Ankeny-Artin-Chowla and Mordell*, arXiv:2508.08472v2,
Theorem 1.3, proves a conditional implication from finitely many
super-Wieferich primes to infinitely many non-Wieferich primes:
https://arxiv.org/html/2508.08472v2 . Nothing here removes that kind of
missing global depth control. The present parity classification is a
self-contained application of the cited classical arithmetic inputs;
no worldwide priority claim is made.

The companion `GoldenInertBlockParity.lean` supplies proof-script
candidates for the explicit existing involutive-readout instance, the
actual mod-five recurrence, the factorization parity identity and the character/count/witness conclusions for every
odd-inert-base power layer. Its prime-divisor exponents refer to the
actual quotient. The exact-rank transfer for prime bases and the full
mixed-index classification IP8-IP11 are ordinary proofs in this
appendix; they are not silently asserted as kernel-certified results.


### IP.7 A first ramified digit beyond the quadratic character

Keep the original Fibonacci sequence and the fixed discriminant-five field.
For a positive integer x coprime to five define

$$
\lambda_5(x)=\frac{x^4-1}{5}\pmod5\in\mathbb F_5.
$$

This is the Fermat quotient at the FIXED prime five, with varying integer
base x. It must not be confused with the WSS quotient
$q_p=F_{p-(5/p)}/p\pmod p$ at the varying prime p.

**Lemma RP1.** The map depends only on x modulo 25 and satisfies

$$
\lambda_5(xy)=\lambda_5(x)+\lambda_5(y),\quad
\lambda_5(x^h)=h\lambda_5(x),\quad
\lambda_5(2)=3,\quad \lambda_5(1+5u)=4u\pmod5.
$$

It extends to ratios of integers coprime to five by subtraction. Its
kernel in $(\mathbb Z/25\mathbb Z)^\times$ is $\{1,7,18,24\}$.
The pair $(x\bmod5,\lambda_5(x))$ determines x modulo 25 uniquely.

**Proof.** Fermat's theorem makes the integer quotient well-defined.
Replacing x by x+25t changes x^4 by a multiple of 25. Expanding
$(1+5A)(1+5B)$ proves additivity. The kernel follows by checking the
four roots of $X^4=1$ modulo 25: each nonzero residue modulo five has a
unique lift, since its derivative $4X^3$ is a unit. More explicitly,
$\lambda_5(x+5t)-\lambda_5(x)=4x^3t\pmod5$, a bijection as t varies.

**Theorem RP2.** For every positive integer n with $5\nmid n$,

$$
\boxed{\lambda_5(F_n)=\lambda_5(n)+1-n^2\pmod5.}\tag{RP2}
$$

**Proof.** The Binet formula and binomial theorem give the integer identity

$$
2^{n-1}F_n=\sum_{j\ge0}\binom n{2j+1}5^j.
$$

The sum is finite. Modulo 25 it becomes

$$
F_n\equiv n2^{1-n}
 \left(1+\frac56(n-1)(n-2)\right)\pmod{25}.
$$

The denominators 2, 6, and n are units at five. In particular F_n is a
unit at five. Apply RP1 to obtain

$$
\lambda_5(F_n)=\lambda_5(n)+3(1-n)
 +\frac23(n-1)(n-2)=\lambda_5(n)+1-n^2\pmod5.
$$

All division by five precedes reduction; no inverse of five in a residue
ring is used. The underlying binomial identity is classical.

### IP.8 The next digit in every primitive block

For $n>3$ odd and $5\nmid n$, retain the actual cyclotomic block
$\mathcal C_n$, old factor $E_n$, and primitive block $\mathcal R_n$
from IP.3-IP.5. Put

$$
c_n=\Phi_n(1)=\prod_{d\mid n}d^{\mu(n/d)},\qquad
J_2(n)=\sum_{d\mid n}\mu(n/d)d^2.
$$

Here $c_n$ equals the underlying prime when n is a prime power and one
otherwise. $J_2$ is the classical second Jordan totient.

**Theorem RP3.** There is an exact weighted initial-depth congruence

$$
\boxed{
\sum_{r(p)=n}h_p\lambda_5(p)
\equiv\lambda_5(c_n)-J_2(n)-\lambda_5(E_n)\pmod5.
}\tag{RP3}
$$

The sum is over actual primes of exact Fibonacci rank n. Its h_p are
the actual initial WSS depths, without assuming they equal one.

**Proof.** Apply RP1 and RP2 to the Moebius product for $\mathcal C_n$.
The terms $\lambda_5(d)$ sum to $\lambda_5(c_n)$. The constant terms
sum to zero, because n>1, and the square terms sum to $-J_2(n)$.
Removing the old factor subtracts $\lambda_5(E_n)$. Finally use the
exact prime factorization $\mathcal R_n=\prod_{r(p)=n}p^{h_p}$ from IP9.

One may equivalently retain the full modulus-25 cyclotomic congruence

$$
\mathcal C_n\equiv
 c_n2^{-\varphi_{\rm E}(n)}
 \left(1+\frac56\bigl(J_2(n)-3\varphi_{\rm E}(n)\bigr)\right)
 \pmod{25}.                                           \tag{RP4}
$$

**Proof.** Multiply the modulo-25 expansions used in RP2 with exponents
$\mu(n/d)\in\{-1,0,1\}$. Products of two correction terms vanish modulo
25; a negative exponent changes the sign of its first correction. The
linear and quadratic divisor sums are $\varphi_{\rm E}(n)$ and J_2(n).
This gives RP4 directly.

RP3 supplements the earlier quadratic-character parity by a relation
modulo five on the depths. It does not recover the individual h_p from
one weighted sum. Some coefficients vanish: for example
$\lambda_5(159607993)=0$, even though this is an inert primitive prime
at rank 91. Nonzero terms can also cancel. No WSS occurrence or absence
is inferred merely from RP3.

### IP.9 Uniform two-cycle modulo 25

Let ell>1 be an odd integer with $\chi(\ell)=-1$, and retain the actual
integer quotient

$$
B_{\ell,k}=F_{\ell^{k+1}}/F_{\ell^k}\quad(k\ge0).
$$

Primality of ell is not needed in this section. When ell is a prime at
least seven, IP5 identifies its factors and exponents with exact ranks
and initial depths.

**Theorem RP5.** For all k>=0,

$$
\lambda_5(B_{\ell,k})
\equiv\lambda_5(\ell)-3(-1)^k\pmod5,              \tag{RP5}
$$

and

$$
\boxed{
B_{\ell,2j}\equiv F_\ell,\qquad
B_{\ell,2j+1}\equiv-4F_\ell\pmod{25}.
}\tag{RP6}
$$

The two displayed residues are distinct.

**Proof.** RP2 at the two power indices and RP1 give

$$
\lambda_5(B_{\ell,k})=
 \lambda_5(\ell)-\ell^{2k}(\ell^2-1)\pmod5.
$$

Inertness means $\ell^2=-1\pmod5$, proving RP5. IP5's residue formula
$B_{\ell,k}=\ell(-1)^{(\ell-1)/2}\pmod5$ also holds for composite odd
bases coprime to five, by direct division of the formula in IP2. Thus
all B have the same nonzero residue modulo five. RP5 alternates between
two values differing by one. Multiplication by -4=1-5 leaves the residue
modulo five unchanged and adds $\lambda_5(-4)=1$. RP1's uniqueness of a
modulo-25 lift from these two coordinates proves RP6, starting with
$B_{\ell,0}=F_\ell$. Since F_ell is a unit at five, their difference
$-5F_\ell$ is nonzero modulo 25.

### IP.10 Exact distance between any two layers

Define integer polynomials

$$
P_0(X)=1,\qquad P_1(X)=X-3,\qquad
P_{a+2}(X)=(X-2)P_{a+1}(X)-P_a(X).
$$

**Lemma RP7.** For every odd positive n and every a>=0,

$$
\frac{F_{(2a+1)n}}{F_n}=P_a(5F_n^2),\qquad
P_a(0)=(-1)^a(2a+1),
$$

$$
24P'_a(0)=(-1)^{a+1}(2a+1)((2a+1)^2-1).         \tag{RP7}
$$

**Proof.** Put u=phi^n and v=psi^n. Since n is odd, uv=-1 and
$(u-v)^2=5F_n^2$. The quotients
$(u^{2a+1}-v^{2a+1})/(u-v)$ have initial values 1 and
$u^2+uv+v^2=5F_n^2-3$; their two-step recurrence has coefficient
$u^2+v^2=5F_n^2-2$ and constant determinant $(uv)^2=1$.
This proves the first identity. Setting X=0 gives the second.
Differentiating the polynomial recurrence gives
$d_{a+2}=P_{a+1}(0)-2d_{a+1}-d_a$, with d_0=0,d_1=1.
Induction yields $6d_a=(-1)^{a+1}a(a+1)(2a+1)$, equivalent to RP7.
These are polynomial identities over the integers, not formal division
by the nonunit five.

**Lemma RP8.** For odd inert ell=2a+1, and distinct integers x,y divisible
by five,

$$
v_5(P_a(x)-P_a(y))=v_5(x-y).                    \tag{RP8}
$$

**Proof.** RP7 makes $P'_a(0)$ a unit modulo five: 24, ell, and
ell^2-1 are all units there. Polynomial subtraction factors as
$P_a(x)-P_a(y)=(x-y)(P'_a(0)+5z)$ for some integer z, because each
remaining divided-difference term has a factor x or y. The second
factor is a unit at five, proving the equality.

**Theorem RP9.** For every k>=0 and t>=1,

$$
\boxed{
v_5(B_{\ell,k+t}-B_{\ell,k})
 =1+v_5(\ell^{2t}-1).
}\tag{RP9}
$$

Valuations of negative integers, if any, mean valuations of their
absolute values. All differences here are nonzero.

**Proof.** Set m=ell^(k+t), n=ell^k, so m>n are odd and coprime to five.
By RP7-RP8 the left side equals $1+v_5(F_m^2-F_n^2)$.
The classical Fibonacci identity, with n odd, gives
$F_m^2-F_n^2=F_{m+n}F_{m-n}$. Lengyel's formula
$v_5(F_u)=v_5(u)$, valid for every positive u, consequently gives

$$
1+v_5(m+n)+v_5(m-n)=1+v_5(m^2-n^2)
=1+v_5(\ell^{2t}-1),
$$

because five does not divide ell. This proves RP9 with no assumption
about the WSS depths of the primes dividing the individual blocks.

### IP.11 All finite-precision periods and the full 5-adic closure

Put $s_\ell=v_5(\ell^4-1)\ge1$. Then RP9 becomes

$$
v_5(B_{\ell,k+t}-B_{\ell,k})=
\begin{cases}
1,&t\text{ odd},\\
1+s_\ell+v_5(t),&t\text{ even}.
\end{cases}                                      \tag{RP10}
$$

**Proof.** For odd t, ell^(2t)=-1 modulo five. For even t=2u,
$v_5((ell^4)^u-1)=s_ell+v_5(u)$. To prove this last elementary lifting
formula, write ell^4=1+5^s z with five not dividing z. An exponent
coprime to five preserves the initial valuation by the geometric sum;
raising a number congruent to one modulo five to the fifth power raises
its difference-from-one valuation exactly by one, by binomial
expansion. Iterate and use v_5(2)=0.

**Theorem RP11.** The least positive period of the sequence
$k\mapsto B_{\ell,k}\pmod{5^r}$, from k=0 onward, is

$$
\boxed{
T_\ell(1)=1,\qquad
T_\ell(r)=2\cdot5^{\max(0,r-1-s_\ell)}\quad(r\ge2).
}\tag{RP11}
$$

There is no smaller eventual period either.

**Proof.** RP10 is independent of k. A difference t is a period if and
only if its displayed valuation is at least r. For r>=2 it must be even,
and then v_5(t)>=max(0,r-1-s_ell). The smallest positive such integer
is the formula in RP11. The same necessary condition holds even when
the congruences are only required after an arbitrary initial index.

**Theorem RP12.** In $\mathbb Z_5$, the closure of the block values is
exactly the disjoint union

$$
\boxed{
\overline{\{B_{\ell,k}:k\ge0\}}=
\bigl(F_\ell+5^{s_\ell+1}\mathbb Z_5\bigr)
\ \cup\
\bigl(B_{\ell,1}+5^{s_\ell+1}\mathbb Z_5\bigr).
}\tag{RP12}
$$

The limiting fraction of residue classes occupied by the block values
modulo 5^r is $2/5^{s_\ell+1}$.

**Proof.** RP10 puts every even-indexed value in the first ball and
every odd-indexed value in the second. The balls are disjoint because
the difference between their centers has valuation one. For r>s_ell+1,
RP10 also shows that the first $5^{r-s_ell-1}$ values in either parity
subsequence are pairwise distinct modulo 5^r. There are exactly that
many residue classes in the relevant ball, so all its classes are hit.
This proves density in each ball at every precision, hence the closure
identity. Counting both balls gives the limiting fraction. This density
belongs to the block sequence at the fixed prime five; it is NOT the
previous Bragman-Rowland Fibonacci density delta(p).

For example $s_7=2$, because 7^4-1=2400. Hence the least block period
at modulus 125 is still two, and the closure has density 2/125.
However $h_7=v_7(F_8)=1$, so seven is not a WSS prime. The period plateau
here measures the Fermat valuation of the BASE seven at the PRIME five.
It must not be relabelled as a Fibonacci-Wieferich exception at seven.

### IP.12 Mathematical boundary of the refinement

RP3 does constrain the actual initial depths modulo five through a
known weighted sum. For a fixed prime with lambda_5(p) nonzero, changing
its depth from one to three changes its contribution by
2 lambda_5(p). Other changes can cancel it, and lambda_5 can itself
vanish on inert primes. The period and closure theorems describe the
fixed-five readout completely but do not force some h_p>=2, or force
infinitely many h_p=1. They supply additional arithmetic information
beyond quadratic parity, without resolving the WSS zero set.

No externally posed open problem is counted as newly resolved by this
appendix. Its recurrence, binomial, Jordan-totient, and valuation inputs
are classical; priority for this combination is unconfirmed.

The valuation input v_5(F_n)=v_5(n) and the varying-prime initial-depth
formula are in L. A. Medina and E. Rowland, *p-regularity of the p-adic
valuation of the Fibonacci sequence*, Fibonacci Quarterly 53 (2015),
265-271, Theorem 1.4, https://arxiv.org/abs/0910.2907 .
For the established cyclotomic/primitive-factor framework see
H. Hong, *On big primitive divisors of Fibonacci numbers*,
https://arxiv.org/abs/2312.04354 . Jordan-totient and cyclotomic-derivative
connections are already studied in P. Moree, S. Saad Eddin, A. Sedunova,
and Y. Suzuki, *Jordan totient quotients*, https://arxiv.org/abs/1810.04742 .


## S5040. Auxiliary depth constraints and the limits of the 5040 readout

### S5040.1 Scope of the existing 5040 results

The existing Robin and resource results concern specific arithmetic objectives.
`GoldenResource5040PriceInterval.golden_resource_5040_unique_maximum_of_price_interval`
requires a price strictly between log(12/11)/log(11) and log(31/30)/log(2).
`GoldenCell5040Shape.modEq_2241_shape` requires BOTH 5040 dividing the index
and the congruence 3^n=2241 modulo n. Neither hypothesis is supplied by the
initial WSS condition. `Robin.SevenSmooth` applies to integers supported on
2,3,5,7. A primitive Fibonacci block at an odd index greater than three has
none of these prime factors. These statements cannot be transferred by
identifying an arbitrary Fibonacci block with their optimized or constrained
integer. The Library entry `wu2019abundant` also records that the maximal
abundancy at eight prime factors counted with multiplicity is attained by
180180, not by 5040; the two optimization problems have different objectives.

There is nevertheless a direct auxiliary modulus interpretation:

$$
5040=16\cdot9\cdot5\cdot7.
$$

The factor nine supplies a first 3-adic digit absent from the earlier
modulo-twenty-five readout. The auxiliary character below does not change
the original golden field, Fibonacci sequence, or definition of initial depth.

### S5040.2 A modulo-nine identity and its primitive-block consequence

Define the integer-valued character

$$
\eta(n)=\begin{cases}
1,&n\equiv1,11\pmod{12},\\
-1,&n\equiv5,7\pmod{12},\\
0,&\gcd(n,6)>1.
\end{cases}
$$

It is multiplicative: on the units modulo twelve the classes 1,11 form the
kernel of an index-two character, and multiplying a nonunit leaves a nonunit.
For integers x coprime to three define

$$
\lambda_3(x)=\frac{x^2-1}{3}\pmod3.
$$

The division takes place in the integers. The residue depends only on x
modulo nine, and expansion of (xy)^2-1 gives

$$
\lambda_3(xy)=\lambda_3(x)+\lambda_3(y),\qquad
\lambda_3(x^h)=h\lambda_3(x).
\tag{S1}
$$

**Theorem.** For every positive n coprime to six,

$$
\boxed{F_n^2\equiv4-3\eta(n)\pmod9,
\qquad \lambda_3(F_n)=1-\eta(n)\pmod3.}
\tag{S2}
$$

**Proof.** The original pair recurrence gives (F_24,F_25)=(0,1) modulo
nine, hence F_(n+24)=F_n for every n by recurrence induction. The square
values at the eight unit classes modulo twenty-four are one at classes
1,11,13,23 and seven at classes 5,7,17,19. These are exactly 4-3*eta(n).
All values are units at three. Dividing the square congruence minus one
by three in the integers gives the second statement. Thus the finite
calculation proves a universal congruence after the period reduction.

For n>3 with gcd(n,30)=1, retain the actual primitive block
R_n=C_n/E_n from IP9. All Fibonacci terms F_d with d dividing n are units
at three. Let mu be the Moebius function, and set

$$
H(n)=(\mu*\eta)(n)=\sum_{d\mid n}\mu(n/d)\eta(d).
$$

**Theorem.** The actual initial depths satisfy

$$
\boxed{\sum_{r(p)=n}h_p\lambda_3(p)
\equiv-H(n)-\lambda_3(E_n)\pmod3.}
\tag{S3}
$$

Moreover,

$$
H(n)=\prod_{q^a\parallel n}\eta(q)^{a-1}(\eta(q)-1).
\tag{S4}
$$

**Proof.** Apply the homomorphism S1 to the exact Moebius product for C_n.
For a reciprocal, its value is the negative of the original value; equivalently
one can work in the units modulo nine. Equation S2 and sum_(d|n)mu(n/d)=0
for n>1 give lambda_3(C_n)=-H(n). Subtract the contribution of the actual
old factor E_n, then apply R_n=product_(r(p)=n)p^h_p. Finally mu and eta
are multiplicative, and their convolution at q^a is eta(q)^a-eta(q)^(a-1).

If some prime q dividing n is 1 or 11 modulo twelve, H(n)=0. If every
prime dividing n is 5 or 7 modulo twelve, then

$$
\lambda_3(C_n)\equiv(-1)^{\Omega(n)-\omega(n)+1}\pmod3.
$$

The sum in S3 includes split primes as well as inert primes. A nonzero
right-hand side forces a nonzero weighted contribution, but does not
force that contributor to be inert or to have depth greater than one.

**The previously blind coefficient.** At n=91, the earlier exact block is
R_91=741469*159607993 and E_91=13. Here H(91)=0 and

$$
\lambda_3(13)=\lambda_3(741469)=\lambda_3(159607993)=2.
$$

Consequently its actual depths obey

$$
2h_{741469}+2h_{159607993}\equiv1\pmod3.
\tag{S5}
$$

The previous modulo-five-digit equation is
4h_(741469)=4 modulo five, because lambda_5(159607993)=0.
Thus the additional modulo-nine coordinate detects a change of the latter
exponent from one to three. It does not eliminate coordinated changes of
several exponents. The full modulo-five residue, which is more informative
than its quadratic character, can also distinguish some such changes;
5040 is not claimed to be a minimal necessary modulus.

### S5040.3 Every Fibonacci power-layer sequence modulo 5040

**Theorem.** Let ell>1 and gcd(ell,30)=1. For all k>=0 the denominator in
B_(ell,k)=F_(ell^(k+1))/F_(ell^k) is a unit modulo 5040, and

$$
\boxed{B_{\ell,2k}\equiv F_\ell,\qquad
B_{\ell,2k+1}\equiv F_{\ell^2}F_\ell^{-1}\pmod{5040}.}
\tag{S6}
$$

Its least positive period, even allowing an eventual starting index, is

$$
\boxed{T_{5040}(\ell)=
\begin{cases}1,&\ell\equiv1,23\pmod{24},\\2,&\text{otherwise}.
\end{cases}}
\tag{S7}
$$

**Proof.** The small-prime ranks are r(2)=3,r(3)=4,r(5)=5,r(7)=8,
as verified by their first zeros in the original recurrence. None divides
ell^k under the hypothesis, proving invertibility. The actual pair periods
modulo 16,9,5,7 are respectively 24,24,20,16; the return pairs and absence
of earlier return can be checked over these complete finite periods.
The recurrence transports each return to every starting index. Their
least common multiple is 240, the already-used Fibonacci period of 5040.

Modulo 144, ell^2=1 modulo 24. Thus F_(ell^k) alternates between one
and F_ell, and the consecutive quotients alternate between F_ell and its
inverse. Modulo five, IP2 gives
B_(ell,k)=ell*3^(ell^k*(ell-1)); its value is independent of k because
ell^k is odd and ell-1 is even.

Modulo seven, Q^8=-I and Q^16=I for the Fibonacci matrix Q. Every odd
ell satisfies ell^2=1 or 9 modulo sixteen. Put A=F_ell modulo seven
and d=F_(ell^2), so d=1 or -1. The four cumulative values are
1,A,d,d*A. In the second case ell^3=ell+8 modulo sixteen; in the first
case ell^3=ell. Hence their consecutive quotients are A,d/A,A,d/A.
CRT gives S6 for all k.

To decide when the two values coincide, the complete eight-class table
modulo 144 is

$$
\begin{array}{c|rrrrrrrr}
\ell\bmod24&1&5&7&11&13&17&19&23\\\hline
F_\ell\bmod144&1&5&13&89&89&13&5&1\\
F_\ell^2\bmod144&1&25&25&1&1&25&25&1.
\end{array}
$$

Equality holds there exactly at classes 1,11,13,23. Modulo seven it
holds exactly for ell=1,7,9,15 modulo sixteen, as follows from
F_ell=1,2,5,6,6,5,2,1 at the eight odd classes 1,3,...,15, and
F_(ell^2)=1,6,6,1,1,6,6,1 at those classes. Intersecting the two
conditions leaves precisely ell=1 or23 modulo twenty-four. Modulo five
already gives equality. This proves S7. A nonconstant two-cycle cannot
acquire an eventual period one.

Examples are ell=7 with residues 13,853; ell=13 with residues 233,4553;
and ell=23 with constant residue 3457. For prime inert bases at least
seven, all preceding primitive-support conclusions still hold: a repeated
auxiliary residue does not imply repeated prime support or repeated
initial depth.

### S5040.4 Exact information limit of the fixed modulus

**Theorem.** The unit group modulo 5040 has order 1152 and exponent twelve:

$$
(\mathbb Z/5040\mathbb Z)^\times
\simeq C_4\times C_2\times C_6\times C_4\times C_6.
\tag{S8}
$$

For every integer s>=1 its counterpart modulo 5040^s has exponent

$$
\boxed{L_s=12\cdot5040^{s-1}.}
\tag{S9}
$$

**Proof.** CRT gives the factors from the moduli 16,9,5,7. Their unit
groups have the listed cyclic factors; their orders multiply to1152
and their exponents have least common multiple twelve. At higher powers,
the four local exponents are 2^(4s-2), 2*3^(2s-1), 4*5^(s-1) and
6*7^(s-1). Their least common multiple is S9. These are the standard
prime-power unit-group formulas, specialized to the actual modulus.

Consequently every unit u satisfies u^(e+12)=u^e modulo5040. Even the
full residue, and hence every character or other postprocessing of that
residue, cannot distinguish those two exponents. The analogous shift
at precision5040^s is L_s. For an inert odd-rank prime the modulo-five
order is four, so its modulo5040 order is either four or twelve.
For p=159607993, that order is twelve, and the exact residues are

$$
p\equiv1273,\qquad p^3\equiv937,\qquad
p^{13}\equiv1273\pmod{5040}.
$$

These are statements about what the observation can distinguish. They
do not assert that arbitrary altered exponent vectors occur as actual
Fibonacci factorizations. Native modulus5040 also does not include the
previous modulus25. Combining both requires their least common multiple
25200. In the displayed example the thirteenth power still has the same
residue even modulo25200. Higher precision can distinguish more, but no
fixed finite precision recovers an unbounded exponent without further
arithmetic information.

### S5040.5 Primitive-block abundancy and the Robin boundary

**Theorem.** For every odd n>3 with 5 not dividing n and R_n>1,

$$
\boxed{1<\frac{\sigma(R_n)}{R_n}
<\exp\!\left(\frac{\log\phi}{2\log(2n-1)}\right).}
\tag{S10}
$$

Thus along such indices tending to infinity the abundancy tends to one,
independently of whether any initial depth is greater than one.

**Proof.** Every prime p with r(p)=n satisfies n dividing p-chi(p).
Since n is odd and p-chi(p) is even, p>=2n-1. These primes also satisfy
p=1 modulo four. Let w be the number of distinct prime factors of R_n.
Then (2n-1)^w<=R_n<=F_n<phi^(n-1), the latter bound following by ordinary
Fibonacci recurrence induction. Prime-power divisor sums give

$$
\begin{aligned}
\log\frac{\sigma(R_n)}{R_n}
&<\sum_{p\mid R_n}-\log(1-1/p)\\
&<\sum_{p\mid R_n}\frac1{p-1}\\
&\le\frac{w}{2n-2}
\le\frac{\log R_n}{(2n-2)\log(2n-1)}
<\frac{\log\phi}{2\log(2n-1)}.
\end{aligned}
$$

The elementary inequality log(1+x)<x for x>0 gives the second step.
No h_p=1 assumption occurs. Exponentiate to obtain S10. If R_n=1,
its abundancy is one directly, so the convergence statement also holds
when those indices are included.

Theorem2 of Choie, Lichiardopol, Moree and Sole, *On Robin's criterion
for the Riemann Hypothesis*, Journal de Theorie des Nombres de Bordeaux
19 (2007),357-372, states that every odd positive integer except1,3,5,9
satisfies Robin's strict inequality. Every nontrivial R_n here is odd
and at least13, so it satisfies that inequality unconditionally. Thus
applying Robin's inequality to these unmodified primitive blocks cannot
separate their WSS and non-WSS depths. Multiplying by5040 creates a
different integer and would require a new, proved arithmetic implication.

The first mod-nine theorem is supplied as a Lean proof-script candidate
with a matching Scribe. S3 and S6-S10 are complete ordinary deductions
in this appendix, not newly kernel-certified declarations. None of these
results establishes a WSS prime, excludes an unbounded WSS prime class,
or settles a newly identified external open problem. The local-group,
rank, valuation and divisor-sum tools are classical. Their specialization
here has no worldwide mathematical priority claim.


## NP. Native-prime layers and exact coupling of initial depths

### NP.1 The native modulus and the actual sequences

Let p>=7 be prime, epsilon=chi(p)=(5/p), N=p-epsilon, and

$$
h_p=v_p(F_N)=v_p(F_{r(p)})\ge1,\qquad
q_p=F_N/p\pmod p,\qquad u_p=F_N/p^{h_p}\pmod p\ne0.
$$

Here r(p) is the least positive Fibonacci zero index. Equality of the
initial depths uses r(p)|N, p not dividing N, and the classical valuation
formula in the sources below. Neither depth is assumed to be one.
For k>=0 define the same exact integer quotient as in IP.2,

$$
B_{p,k}=\frac{F_{p^{k+1}}}{F_{p^k}}.
$$

This section observes it at the prime p itself, rather than at the fixed
auxiliary moduli five or 5040. Its prime divisors still have exact rank
p^(k+1), and their exponents are their own initial depths, by IP5.

**Lemma.** For every k>=0, F_(p^k) is a unit at p, and

$$
F_{p^k}\equiv\epsilon^k,\qquad L_{p^k}\equiv1\pmod p.       \tag{NP1}
$$

**Proof.** The rank r(p)>2 divides N and is coprime to p, so it cannot
divide p^k. This proves the unit assertion. In the original golden
algebra over F_p, Frobenius fixes phi,psi when epsilon=1 and exchanges
them when epsilon=-1. The denominator phi-psi has square five, a unit,
and the Binet difference and trace formulas therefore give the two
residues at p^k. For the swapped case, the difference changes sign at
each Frobenius application while the trace stays one. These calculations
also apply at k=0. The integer quotient is exact by Fibonacci divisibility.

### NP.2 Exact depth, all forward distances, and the first constant tail

**Theorem.** For every k>=0,

$$
\boxed{v_p(B_{p,k}-\epsilon)=h_p+k.}                       \tag{NP2}
$$

All arguments of valuations here are nonzero; valuations of negative
integers mean valuations of their absolute values.

**Proof.** Put m=p^(k+1) and n=p^k. BOTH indices are odd. The Catalan
identity in this parity gives

$$
(F_m-\epsilon F_n)(F_m+\epsilon F_n)
 =F_m^2-F_n^2=F_{m+n}F_{m-n}.                             \tag{NP3}
$$

The rank r(p) divides p-epsilon and does not divide p+epsilon. Otherwise
it would divide their difference two, contradicting r(p)>2. It is
coprime to p, so precisely one of F_(m+n), F_(m-n) vanishes modulo p.
Its index is p^k*(p-epsilon), and the valuation formula gives h_p+k.
The other factor has valuation zero. NP1 gives
F_m+epsilon*F_n=2*epsilon^(k+1) modulo p, a unit. Dividing the resulting
valuation of F_m-epsilon*F_n by the unit F_n proves NP2. Nonzeroness
also follows from this finite valuation, or from strict growth of the
positive Fibonacci quotient and epsilon in {1,-1}.

**Corollary.** For every k>=0 and t>=1,

$$
\boxed{v_p(B_{p,k+t}-B_{p,k})=h_p+k.}                    \tag{NP4}
$$

**Proof.** Their respective differences from epsilon have unequal
valuations h_p+k+t and h_p+k. The difference of two nonzero integers of
unequal p-valuations has the smaller valuation, by factoring out that
power and reducing the remaining factor modulo p.

**Corollary.** At precision p^s, s>=1, the earliest starting index of
any positive eventual period is exactly

$$
K_s=\max(0,s-h_p).                                      \tag{NP5}
$$

From K_s onward the sequence is constant epsilon and its least eventual
period is one. It has no period of any positive length starting before
K_s. Consequently B_(p,k) tends to epsilon in Z_p with exact distance
p^(-h_p-k).

**Proof.** NP2 gives constant residue epsilon precisely when k>=K_s.
At an earlier starting index k, NP4 shows that the difference to EVERY
forward index has valuation h_p+k<s, so no positive period can start
there. The limit is the restatement of these finite congruences.
General p-adic convergence of Fibonacci prime-power subsequences is
already covered by Rowland-Yassawi; the exact depth here is derived
using the stated classical valuation formula, with no novelty claim
for convergence itself.

### NP.3 The leading digit has a fixed signed coefficient

**Theorem.** With division by powers of p performed in the integers,

$$
\boxed{
\frac{B_{p,k}-\epsilon}{p^{h_p+k}}
 \equiv\frac{\epsilon^{k+1}u_p}{2}\pmod p,
\qquad
\frac{\epsilon B_{p,k}-1}{p^{k+1}}
 \equiv\frac{\epsilon^k q_p}{2}\pmod p.
}                                                       \tag{NP6}
$$

The second statement includes h_p>1, when both of its residues vanish.

**Proof.** Work with integer matrices localized at p; two is a unit.
For the actual Fibonacci matrix and its trace coordinate put

$$
Q=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
H=\begin{pmatrix}1&2\\2&-1\end{pmatrix}.
$$

Then H^2=5I and Q^a=(L_a I+F_a H)/2 for every integer a, using the
usual negative-index extension and det(Q)=-1. Because N is even,

$$
(L_N-2\epsilon)(L_N+2\epsilon)=5F_N^2.
$$

Frobenius gives L_N=2*epsilon modulo p, so the second factor is a unit
and v_p(L_N-2*epsilon)=2h_p. Thus

$$
\epsilon Q^N=I+p^{h_p}Z,\qquad
Z\equiv\epsilon u_p H/2\pmod p.
$$

For s>=1 and any p-integral matrix Z, binomial expansion gives

$$
(I+p^sZ)^p\equiv I+p^{s+1}Z\pmod{p^{s+2}}.
$$

For terms of degree 2 through p-1, the binomial coefficient supplies a
factor p; the term of degree p has sp>=s+2 because p>=3. Induction then
yields (I+p^h Z)^(p^k)=I+p^(h+k)Z modulo p^(h+k+1). Since p^k is odd,

$$
Q^{Np^k}\equiv\epsilon I+p^{h_p+k}u_pH/2
 \pmod{p^{h_p+k+1}}.                                    \tag{NP7}
$$

Let n=p^k and multiply NP7 by Q^(epsilon*n). For odd n,
F_(-n)=F_n and L_(-n)=-L_n. The off-diagonal entry of Q^aH is L_a.
Using p*n=epsilon*n+N*n gives

$$
F_{pn}-\epsilon F_n
 \equiv p^{h_p+k}\epsilon u_pL_n/2
 \pmod{p^{h_p+k+1}}.
$$

Divide by the unit F_n, and use NP1, to obtain the first formula in
NP6. Multiply it by epsilon and by p^(h_p-1) to obtain the second.
No division by p in a residue field is used.

### NP.4 A sum over disjoint primitive-prime families

For a=p^(k+1), define the finite set of actual primes

$$
\mathcal P_{p,k}=\{q:q\text{ prime},\ r(q)=a\}.
$$

IP5, which is valid for every prime base p>=7, gives

$$
B_{p,k}=\prod_{q\in\mathcal P_{p,k}}q^{h_q}.
$$

These sets are disjoint for distinct k. Their primes are all distinct
from p, and every q satisfies a|(q-chi(q)). Hence the signed integer

$$
t_{p,k}(q)=\frac{\chi(q)q-1}{p^{k+1}}
$$

is well-defined. It is negative for inert q; no nonnegativity is
assumed. Define the actual weighted sum

$$
S_{p,k}=\sum_{q\in\mathcal P_{p,k}}h_q\,t_{p,k}(q).
$$

**Theorem.** For every k>=0,

$$
\boxed{
2S_{p,k}\equiv\epsilon^k q_p\pmod p.
}                                                       \tag{NP8}
$$

More generally, for every integer s with 1<=s<=k+1,

$$
\boxed{p^s\mid S_{p,k}\quad\Longleftrightarrow\quad h_p\ge s+1.}
                                                               \tag{NP9}
$$

If k>=h_p-1, the sum is nonzero and v_p(S_(p,k))=h_p-1.
Thus for every k, WSS(p) is equivalent to S_(p,k)=0 modulo p.
For an inert base the first residues alternate in sign between layers;
for a split base they are constant.

**Proof.** The odd-index character identity gives chi(B_(p,k))=epsilon.
Therefore product chi(q)^h_q=epsilon, and the exact signed product is

$$
\epsilon B_{p,k}
 =\prod_{q\in\mathcal P_{p,k}}(1+a\,t_{p,k}(q))^{h_q}
 \equiv1+aS_{p,k}\pmod{a^2}.
$$

The congruence follows by expanding each integer power and multiplying:
every term involving at least two factors a is divisible by a^2.
Negative t and positive integer exponents cause no difficulty. Thus

$$
D_{p,k}:=\frac{\epsilon B_{p,k}-1}{p^{k+1}}
 \equiv S_{p,k}\pmod{p^{k+1}}.                           \tag{NP10}
$$

By NP2, v_p(D_(p,k))=h_p-1. For s<=k+1, NP10 makes divisibility of
S by p^s equivalent to divisibility of D by p^s, proving NP9. If
k>=h_p-1, that valuation is less than k+1, so the difference in NP10
cannot change it; this proves the exact valuation assertion. Finally
combine NP10 modulo p with NP6 to prove NP8. Changing k to k+1 in
NP8 gives S_(p,k+1)=epsilon*S_(p,k) modulo p.

The restriction s<=k+1 in NP9 is essential to the linear truncation.
It is not a statement about arbitrary precision at one fixed layer.
No value v_p(0) needs to be assigned for the divisibility version.

**Example.** At p=7, q_p=F_8/7=3 modulo seven. At k=0 the only factor
is13, so S_(7,0)=(-13-1)/7=-2=5 modulo seven. At k=1 the exact block
is97*6168709, both initial depths one. The signed coefficients are
-2 and125892, respectively. Hence S_(7,1)=125890=2 modulo seven,
as predicted by the sign reversal. The sum contains both split and
inert primes; restricting it to inert primes would invalidate NP8.

### NP.5 Prime-power primitive orbit counts retain the same depth

Use the two-vertex directed graph with adjacency matrix Q. Its number
of length-n closed walks with a marked starting position is L_n.
Let b_n be the number of cyclic orbits whose least period is exactly n.
Every such orbit supplies n marked walks, so

$$
L_n=\sum_{d\mid n}d b_d.
$$

**Theorem.** For every k>=0,

$$
b_{p^{k+1}}=\frac{L_{p^{k+1}}-L_{p^k}}{p^{k+1}}>0,
\qquad
\boxed{v_p(b_{p^{k+1}})=h_p-1.}                         \tag{NP11}
$$

Furthermore b_(p^(k+1))=5*S_(p,k) modulo p.

**Proof.** Subtract the two divisor sums at successive p-powers to
obtain the exact integer quotient; positivity follows from increasing
Lucas numbers at these positive indices. With m=p^(k+1), n=p^k both
odd, the trace-norm and Catalan identities give

$$
(L_m-L_n)(L_m+L_n)=5(F_m^2-F_n^2)=5F_{m+n}F_{m-n}.
$$

NP1 makes L_m+L_n=2 modulo p, a unit. The same valuation argument as
NP2 therefore gives v_p(L_m-L_n)=h_p+k. Divide by p^(k+1) to obtain
NP11. For the first digit, take traces in NP7 after multiplication by
Q^(epsilon*n), using tr(Q^a H)=5F_a and F_(epsilon*n)=F_n. This gives

$$
\frac{L_m-L_n}{p^{k+1}}
 \equiv\frac52\epsilon^k q_p\pmod p.
$$

Together with NP8 this proves the last statement. Orbit integrality
comes from the actual graph action, not from assuming the desired
prime divisibility. This is a consequence within the same proof family,
not another externally posed open problem being declared solved.

### NP.6 A concrete limit of the auxiliary-residue and height method

**Proposition.** The conditions of correct prime rank, inertness, odd
exponent, fixed residue modulo25200, and the available upper height
bound do not by themselves exclude a powerful candidate.

**Proof by an exact example.** Let n=337 and q=673. Both are primes,
chi(n)=chi(q)=-1, q=2n-1, and q divides F_n. Since n is prime and
F_1=1, the exact rank of q is337. Put M=q^3=304821217. Then

$$
1<M<F_{337},\qquad M\equiv F_{337}\equiv2017\pmod{25200}.
$$

The integer M is powerful, with one inert prime at odd exponent three,
and it meets the rank lower bound with equality q=2n-1. The actual
Fibonacci value and the exact distinguishing residues are

$$
F_{337}=
12004657173391489668678522013941832147005954727556362660159637892443617,
$$

$$
F_{337}\bmod673^2=172288=256\cdot673\ne0,
$$

$$
M\bmod337^2=2021,\qquad F_{337}\bmod337^2=86945.
$$

All residues are computed by the integer Fibonacci recurrence or binary
doubling. The primalities require only trial division through the square
roots. In particular q's actual initial depth is ONE, not three.
The native parent quotient is q_337=158 modulo337, so NP8 requires
S_(337,0)=79 modulo337. The candidate M instead gives3*(-2)=-6=331
modulo337. The native-prime first digit thus excludes this particular
candidate which the fixed5040/25 data and the coarse height bound admit.

This example does not give two Fibonacci factorizations of one integer.
M is not asserted to be a Fibonacci value; it has neither the exact
magnitude nor necessarily the complete prime support of F_337. It only
refutes the proposed inference from the displayed weaker necessary
conditions alone. More precise height, exact support, or native-prime
information could exclude it, as the last calculation demonstrates.

### NP.7 Arithmetic and prior-art boundary

NP8-NP9 couple the actual depth at a base prime p to actual depths at
other, strictly larger primes having exact ranks p^(k+1). This improves
the bookkeeping beyond a fixed auxiliary character, but it does not
prove that the weighted sum vanishes or stays nonzero for an unbounded
prime family. Both signs occur and weighted contributions can cancel.
Replacing h_q by one would assume away precisely the exceptions under
investigation. Neither a WSS prime nor a new unbounded non-WSS prime
family is constructed by these identities.

The underlying rank, valuation, Catalan, and matrix-power tools are
classical. The valuation formula is Theorem1.4 of L. A. Medina and
E. Rowland, *p-regularity of the p-adic valuation of the Fibonacci
sequence*, The Fibonacci Quarterly53(2015),265-271,
https://arxiv.org/abs/0910.2907 . It leaves the initial valuation
arbitrary. General p-adic subsequence convergence and interpolation
appear in E. Rowland and R. Yassawi, *p-adic asymptotic properties of
constant-recursive sequences*, Indagationes Mathematicae28(2017),205-220,
DOI10.1016/j.indag.2016.11.019, arXiv:1602.00176, Corollary11 and
section5. No first proof of that general convergence is claimed here.
The exact signed factor-sum and all-depth formulation above is an
ordinary derivation from these inputs and IP5. Priority for its combined
formulation is unconfirmed. No new externally posed open problem is
counted as resolved, and no new Lean/kernel-certified declaration is
asserted by this theory-only continuation.


## QR. Exact quadratic realization of finite Fibonacci-divisor spectra

### QR.1 What the native-prime layers do and do not add

Keep NP's actual prime-factor sums S_(p,k), epsilon=(5/p), and q_p.
The previously proved identity NP8 gives, for every fixed prime p>=7,

$$
2\epsilon^k S_{p,k}\equiv q_p\pmod p\quad(k\ge0). \tag{QR1}
$$

Consequently all finite vectors of these normalized residues are diagonal:
(q_p,...,q_p). For any nonempty finite set of layers, simultaneous vanishing
is exactly the same condition as vanishing at a single layer. Distinct
prime supports do not make these particular residue tests independent.
This is a consequence of NP8, not a new estimate on the WSS zero set.
It does not say that all information in the full prime factorizations is
redundant, or that residues at different base primes are equal.

The following use of primitive factors has a different endpoint. It closes
the realization gap in the earlier A339621/FSP result and proves positive
natural density, without any supposition that initial depths equal one.

### QR.2 Definitions and the credited primitive-prime input

For a positive integer M define the finite set of distinct positive
Fibonacci divisor VALUES

$$
D_F(M)=\{F_j:j\ge2,\ F_j\mid M\},\qquad
\sigma_F(M)=\sum_{d\in D_F(M)}d.
$$

The value one occurs once. For a set A of nonnegative integers its natural
density is lim_(X->infinity) #(A intersect [0,X])/X, when that limit exists.

We use Carmichael's classical primitive-divisor theorem in the following
precise form: for every j>12 there is a prime q_j dividing F_j whose least
positive Fibonacci zero index is exactly j. Different j give different
chosen primes. The classical rank bound j|(q_j-(5/q_j)) implies
q_j>=j-1. This implication is for the prime value, not its exponent.
The primes q_j are different from two and five for j>12.

A primary accessible statement is H. Hong, *On big primitive divisors of
Fibonacci numbers*, arXiv:2312.04354v2, introduction. The classical result
is also proved in M. Yabuta, *A simple proof of Carmichael's theorem on
primitive divisors*, Fibonacci Quarterly39(5)(2001),439-443. For the few
indices 3<=j<=12, direct Fibonacci calculations give a prime of exact
rank j except j=6,12; for j=3,4,5,7,8,9,10,11 one may take respectively
2,3,5,13,7,17,11,89. No simple-exponent assertion is used here.

### QR.3 A uniform bound on all untested large Fibonacci divisors

Let R(d) be the number of roots of x^2=-1 modulo the positive integer d.
For d>1,

$$
R(d)\le2^{\omega(d)}\le64d^{1/4}.                 \tag{QR2}
$$

**Proof.** At every odd prime power there are at most two roots: a root
is a unit and the derivative 2x is a unit, so each root modulo the prime
lifts uniquely. At two there is one root modulo two and none modulo four
or higher powers. CRT proves the first bound. For primes at least17,
2<=q^(1/4). There are just six primes below17, so their possible factors
of two contribute at most64; the larger primes' product is at most d.

Fibonacci induction gives F_j>=(3/2)^(j-2) for j>=2. Since
(3/2)^3>(4/3)^4, it follows that F_j^(-3/4)<=(3/4)^(j-2).
Thus, for every integer J>=3,

$$
\sum_{j>J}\frac{R(F_j)}{F_j}
\le256(3/4)^{J-1}=:T_J.                            \tag{QR3}
$$

**Theorem.** Uniformly for X>=2, the count of m in [0,X] for which some
j>J satisfies F_j|m^2+1 is at most

$$
XT_J+O\bigl(X^{1/2}\log X\bigr).                  \tag{QR4}
$$

The implicit constant is absolute and independent of J.

**Proof.** Only O(log X) indices can occur, since F_j<=X^2+1 and the
preceding exponential lower bound holds. For each such j, there are at
most R(F_j)(X/F_j+1) solutions in the interval. Sum the main terms using
QR3. Each error term is at most64(X^2+1)^(1/4), by QR2, and there are
O(log X) of them. This proves QR4. In particular the upper density of
the large-divisor tail is at most T_J, tending to zero exponentially.
The error estimate controls divisors larger than X as well as smaller
ones; a convergent formal density series alone would not suffice.

### QR.4 Every locally admissible integer has a positive-density realization

**Theorem.** Let K>=1 and assume x^2=-1 modulo K has a solution. Then

$$
A_K=\{m\ge0:K\mid m^2+1,\ D_F(m^2+1)=D_F(K)\}
$$

has a positive natural density.

**Proof of finite local compatibility.** Solvability is equivalent to
v_2(K)<=1 and every odd prime divisor of K being1 modulo four. At each
odd q^e exactly dividing K, choose a root modulo q^e and then a lift
modulo q^(e+1) that is NOT a root at the higher precision. Such a lift
exists: among the q lifts, precisely one is a root, because 2x is a unit.
Thus a progression can impose v_q(m^2+1)=e. If K is odd take m=0 modulo
four; if K is even take m=1 modulo four. These force v_2(m^2+1) to equal
v_2(K). Also impose m=0 modulo three, since three cannot divide K.

Choose an integer J0>=12 large enough that every Fibonacci divisor of K
has index at most J0 and every prime divisor q of K has rank at most J0.
Existence is immediate; J0=max(12,K+2) is one sufficient choice, using
F_j>=j-1 and the rank bound, with the small primes treated directly.
For each 3<=j<=J0 with F_j not dividing K, choose a prime q for which
v_q(F_j)>v_q(K). If q divides K, the exact-valuation condition already
excludes F_j. If q does not divide K, impose m=0 modulo q. Repeated
conditions agree, and the choices at two and three are consistent.
CRT now supplies one progression a modulo Q0 such that K|m^2+1 and
no forbidden F_j with j<=J0 divides m^2+1. Every prime factor of Q0
either divides K, is two or three, or divides one of those F_j. Its rank
is therefore at most J0.

**Proof of a quantitative finite exclusion bound.** For each j>J0 choose
the classical primitive prime q_j. The q_j are distinct and coprime to
Q0. Avoid the at most two roots of -1 modulo q_j. For J>=J0, CRT gives
a set of progressions of density at least

$$
\frac1{Q0}\prod_{j=J0+1}^{J}\left(1-\frac2{q_j}\right)
\ge\frac{(J0-2)(J0-1)}{Q0(J-2)(J-1)}.              \tag{QR5}
$$

The last product telescopes using q_j>=j-1; the empty product is one.
These progressions obey every required exclusion through index J.

**Proof of existence and positivity of the limiting density.** Let A_(K,J)
be the full set with K|m^2+1 and the correct Fibonacci divisor membership
only through index J. It is periodic, so its density d_(K,J) exists.
These sets decrease with J. The difference A_(K,J) minus A_K is contained
in the QR4 tail. Hence their finite counting densities differ in limsup
by at most T_J. It follows that A_K has natural density
lim_(J->infinity)d_(K,J).

For any J>=J0 this limit is at least the right side of QR5 minus T_J.
The first quantity decreases polynomially with J and T_J exponentially.
Choose J so that T_J is less than half that positive rational quantity.
This proves strictly positive density. No assertion about the primality
or squarefreeness of m^2+1 is required.

### QR.5 An exact finite-spectrum criterion

**Theorem.** Let D be a finite set of distinct positive Fibonacci values,
containing one, and let K=lcm(D). The following are equivalent:

$$
\begin{aligned}
&\exists m\ge0:\ D_F(m^2+1)=D;\\
&D_F(K)=D\quad\hbox{and}\quad x^2\equiv-1\pmod K
   \hbox{ has a solution}.
\end{aligned}                                                   \tag{QR6}
$$

If they hold, the realizing integers m have positive natural density.

**Proof.** A realization implies K|m^2+1 and hence root solvability.
Every Fibonacci divisor of K then belongs to D, while each element of D
already divides K, giving equality. Conversely apply QR.4 to K when
D_F(K)=D. This gives the stronger positive-density subset that also
satisfies K|m^2+1. The full realizing set has a natural density by the
same finite-period truncation and QR4 tail argument, so that density is
positive. Both criteria are finite statements for the given D.

### QR.6 Every even-index Fibonacci value occurs with positive density

For r>=1 put

$$
D_r=\{1\}\cup\{F_{2j+1}:1\le j<r\},\qquad K_r=\operatorname{lcm}(D_r).
$$

**Lemma.** D_F(K_r)=D_r, and x^2=-1 modulo K_r is soluble.

**Proof.** If an odd prime q divides any odd-index F_n, the identity
L_n^2-5F_n^2=-4 shows that (L_n/2)^2=-1 modulo q. Thus q=1 modulo four,
including q=5. At an odd index the Fibonacci valuation at two is at
most one, as follows from the complete period-six recurrence modulo four.
Hence v_2(K_r)<=1 and every odd prime in K_r is1 modulo four; CRT and
simple-root lifting prove the root assertion. Also three does not divide
K_r, since its rank is four and all the target indices are odd.

Now suppose F_k|K_r with k>=3. For k other than6,12 there is a prime of
exact rank k, by QR.2's classical theorem and the listed small checks.
It divides some target F_i with i odd and i<=2r-1. The entry-point theorem
then gives k|i. Therefore k is odd and at most2r-1, so F_k is a target
value. The exceptions F_6=8 and F_12=144 cannot divide K_r, since its
two-valuation is at most one. The reverse containment is the definition
of the least common multiple. This proves the exact divisor set.

**Theorem.** For every r>=1 the natural density

$$
\boxed{d_r=\lim_{X\to\infty}\frac1X
 \#\{0\le m\le X:\sigma_F(m^2+1)=F_{2r}\}>0}       \tag{QR7}
$$

exists. In particular every F_(2r) is attained infinitely often.
Combined with FSP, the Fibonacci-valued part of A339621's range is
EXACTLY {F_(2r):r>=1}.

**Proof.** Apply QR6 to D_r, then use the earlier full FSP classification:
for every m, the displayed sum equals F_(2r) exactly when its full divisor
set is D_r. The identity sum(D_r)=F_(2r) is the Fibonacci recurrence.

**Explicit positive lower certificate.** For every
J>=max(12,2r-1) satisfying the integer inequality

$$
512K_r(J-2)(J-1)3^{J-1}<4^{J-1},                  \tag{QR8}
$$

one has

$$
\boxed{d_r>\frac1{2K_r(J-2)(J-1)}.}               \tag{QR9}
$$

Such J always exist and can be found using integer arithmetic.

**Proof.** Begin with one progression modulo6K_r on which K_r|m^2+1
and three divides m. For r=1 choose the even progression; for r>=2 the
root condition already forces m odd, since F_3=2 belongs to D_r.
This deals with F_3 when forbidden, with F_4, and with the primitive
exceptions F_6,F_12. For every other forbidden index5<=j<=J, choose a
prime of exact rank j. It is coprime to6K_r: otherwise j would divide a
target odd index and would itself be a target. These primes are distinct.
Avoiding their at most two root classes gives a finite-good density at
least

$$
\frac1{6K_r}\prod_{j=5}^{J}\left(1-\frac2{j-1}\right)
=\frac1{K_r(J-2)(J-1)}.
$$

Including factors for desired or exceptional indices only lowers this
bound, so the displayed complete product is legitimate. Subtract T_J
from QR3. The condition QR8 says exactly that this tail is less than
half the last lower bound, proving QR9.

### QR.7 Scope and arithmetic significance

QR7 supplies the realization direction deliberately not asserted in the
old a339621_conjecture Lean candidate. The current OEIS entry lists the
initial even Fibonacci values and a sequence of least realizing inputs;
it does not provide a proof of the all-r positive-density assertion.
The original one-way conjecture was already addressed and is not counted
again. The stronger realization statement is not being relabelled as a
second, independently posed external conjecture. Its priority remains
unconfirmed after bounded exact-identifier and mathematical-phrase searches.

These arguments require a primitive prime at each sufficiently large
index, not a primitive prime to exponent one. All chosen primes can have
their actual unknown Fibonacci depths. No WSS occurrence, nonoccurrence,
or estimate on the fully exceptional block count H(X) follows from QR7.
The role of the large-index primes here is to exclude unwanted Fibonacci
divisors of a varying quadratic value; it does not control the exponents
of a fixed Fibonacci value. The finite CRT step and the uniform tail
estimate are separate and both are needed for the density conclusion.

This appendix contains complete ordinary proofs using the explicitly
credited primitive-prime theorem. It adds no Lean axiom or placeholder,
and does not claim a newly kernel-certified density theorem. The existing
FibonacciDivisorSumParity owner retains its previously stated scope.

Primary references: Hong, arXiv:2312.04354v2, introduction,
https://arxiv.org/html/2312.04354v2 ; Yabuta, Fibonacci Quarterly39(2001),
439-443, DOI10.1080/00150517.2001.12428701; and the target definition and
original conjecture in https://oeis.org/A339621 . The recurrence, root
lifting, CRT and finite-prime divisor bounds used above are classical;
the needed elementary proofs have been included rather than assigned
unverified new citations.
