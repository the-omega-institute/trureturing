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
