[Index](../../marked_head_profile.md) · [Original extremal family](../321-384/350-extremal-paired-branch-and-source-support.md) · [Reserved prime overlap](../321-384/361-prime-overlap-reservation-for-composite-parents.md) · [Common antichain source](../321-384/363-common-source-antichain-capacity.md)

# Prime-star overlaps force excess on the original no-prime region

Original classes with moduli \(pq_i\), for distinct primes \(q_i\),
occupy the nonzero first-\(p\) roots. Their overlaps within each root
have an exact cost under the original Haar law conditioned on avoiding
all original prime classes. This gives a correction to the scalar
conditional union bound, without requiring whole coverage in the
density estimate.

In particular, if the original palette contains \(9,15,21\), the
uncovered density is at least
\(P_0(49/48-\sum_{d\ {m composite}}1/\varphi(d))\).
A whole cover must therefore have the displayed sum at least \(49/48\).
The conclusion permits arbitrary further primes and prime-power heights.
An actual partial family below satisfies the older sum-at-least-one
test while failing this strengthened necessary condition.

These are ordinary finite deductions from CRT, the existing original
Haar identities, and a root-counting argument found in Adenwalla's
work. No literature novelty, Lean verification, new unconditional
prime-support exclusion, or resolution of Erdős #7 is claimed.

## 1. One original law, including uncovered points

Let \(A_d=a_d\bmod d\), \(d\in D\), be a finite family of distinct
odd nonunit moduli. Write
\(Q=\operatorname{lcm}(D)=\prod_{p\in\Lambda}p^{H_p}\), and let
\(H\) be uniform probability on \(\mathbb Z/Q\mathbb Z\).
Assume every support prime belongs to \(D\), and comparable original
classes are disjoint. After one CRT translation, normalize
\(A_p=0\bmod p\) for every \(p\in\Lambda\).
Every composite class thus fixes a nonzero first digit at each prime
dividing its modulus. These hypotheses hold in
[350, EB1--EB3](../321-384/350-extremal-paired-branch-and-source-support.md),
but whole coverage and divisor closure are not assumed in this section.

Put

\[
 Z=\bigcap_{p\in\Lambda}A_p^c,\qquad
 P_0=H(Z)=\prod_{p\in\Lambda}(1-1/p),\qquad
 t(x)=\sum_{\substack{d\in D\\d\ {m composite}}}\mathbf1_{A_d}(x),
 \qquad S=\sum_{\substack{d\in D\\d\ {m composite}}}\frac1{\varphi(d)}.
 \tag{PS1}
\]

The original incidence identity from
[361, PR6](../321-384/361-prime-overlap-reservation-for-composite-parents.md)
and [363, CS6](../321-384/363-common-source-antichain-capacity.md) gives

\[
 H(A_d\cap Z)=\frac{P_0}{\varphi(d)},\qquad
 \int_Z t\,dH=P_0S.
 \tag{PS2}
\]

Indeed, primes dividing \(d\) are already avoided on \(A_d\);
the other prime coordinates contribute their independent factors
\(1-1/p\). The formula retains every original exponent.

Let \(U\) be the density of integers uncovered by the complete family,
and let \(E_+=\int_Z(t-1)_+\,dH\). All uncovered points lie in \(Z\).
Since \(t\) is a nonnegative integer,

\[
 P_0(S-1)=\int_Z(t-1)\,dH=E_+-U,
 \qquad U=P_0(1-S)+E_+.
 \tag{PS3}
\]

For a whole cover, \(U=0\) and \(E_+=v\), the no-prime excess
of 363. For a partial family, \(P_0(S-1)\) need not equal its positive
excess; the uncovered term in PS3 must be retained.

## 2. Exact cost of children sharing a first-prime root

Fix \(p\in\Lambda\). Choose distinct primes \(q_1,\ldots,q_k\)
such that \(pq_i\in D\). One \(q_i\) may equal \(p\), corresponding
to the original class of modulus \(p^2\). Define

\[
 r_i=a_{pq_i}\bmod p\in\{1,\ldots,p-1\},\qquad
 w_i=\begin{cases}1/(q_i-1),&q_i\ne p,\\1/p,&q_i=p.\end{cases}
 \qquad I_r=\{i:r_i=r\}.
 \tag{PS4}
\]

Under the single probability law \(H(\,\cdot\mid Z)\), the first
\(p\)-root is uniform on the \(p-1\) nonzero roots. Conditional on
root \(r\), each child with \(i\in I_r\) has probability \(w_i\).
For \(q_i\ne p\), it fixes one nonzero first-\(q_i\) root.
For \(q_i=p\), it fixes one further \(p\)-digit, which is uniform
on \(p\) values after the first root is fixed. These tests use
different CRT coordinates, with at most one higher-\(p\) test, so
they are independent under this same conditional law.

Let \(N=\sum_i\mathbf1_{A_{pq_i}}\). On root \(r\),

\[
 \mathbb E[(N-1)_+\mid Z,r]
 =\mathbb E[N\mid Z,r]-\Pr(N\ge1\mid Z,r)
 =\sum_{i\in I_r}w_i-1+\prod_{i\in I_r}(1-w_i).
\]

The empty product is one, so an empty root contributes zero. Thus

\[
 B_p(r_1,\ldots,r_k)
 :=\frac1{p-1}\sum_{r=1}^{p-1}
       \left(\sum_{i\in I_r}w_i-1+\prod_{i\in I_r}(1-w_i)\right)
 =\frac1{P_0}\int_Z(N-1)_+\,dH.
 \tag{PS5}
\]

Pointwise \(N\le t\), hence \((N-1)_+\le(t-1)_+\).
Combining PS3 and PS5 gives

\[
 E_+\ge P_0 B_p,\qquad
 U\ge P_0(1-S+B_p).
 \tag{PS6}
\]

One may replace \(B_p\) by its minimum over all assignments of these
\(k\) weights to \(p-1\) roots. This only relaxes the actual residue
constraints. It does not assert that a minimizing assignment extends
to the remaining original classes.

For exactly \(k=p\), that finite minimum has a simple expression:

\[
 \min B_p=\frac1{p-1}\min_{i<j}w_iw_j
          =\min_{i<j}\frac1{\varphi(pq_iq_j)}.
 \tag{PS7}
\]

To prove it, let
\(f(I)=\sum_{i\in I}w_i-1+\prod_{i\in I}(1-w_i)\).
For disjoint nonempty \(I,J\),

\[
 f(I\cup J)-f(I)-f(J)
 =\left(1-\prod_{i\in I}(1-w_i)\right)
  \left(1-\prod_{j\in J}(1-w_j)\right)>0.
\]

If a root is empty and another contains at least two children, moving
one child to the empty root strictly decreases the cost. A minimum
therefore uses all \(p-1\) roots. Since there are \(p\) children,
exactly one root contains two children and every other root contains
one. Its cost is the product of that pair's weights divided by
\(p-1\), proving PS7. The formula includes a possible \(q_i=p\).

## 3. The three children 9, 15 and 21

If \(9,15,21\in D\), take \(p=3\) and \((q_1,q_2,q_3)=(3,5,7)\).
Their weights are \(1/3,1/4,1/6\). PS7 gives

\[
 B_3\ge\frac12\min\left\{\frac1{12},\frac1{18},\frac1{24}\right\}
      =\frac1{48},
 \qquad
 U\ge P_0\left(\frac{49}{48}-S\right).
 \tag{PS8}
\]

Consequently a whole cover with these original labels must satisfy

\[
 S\ge\frac{49}{48},\qquad v\ge\frac{P_0}{48}.
 \tag{PS9}
\]

Divisor closure makes \(315\in D\) a sufficient condition for the
three labels, but they may also be present without \(315\).
Arbitrary additional original primes, moduli and heights are allowed
in PS8--PS9; all their contributions remain in the same \(P_0,S,t\).

The pair proof exposes the geometry. Three nonzero first-3 roots must
share two available values, so a pair intersects. Its lcm is one of
\(45,63,105\), with totients \(24,36,48\). The intersection with
\(Z\) has exact original Haar mass \(P_0/\varphi(\operatorname{lcm})\),
and on that region the complete composite load is at least two.
This is the compatible-pair mass already used in 363, now forced by
the original root assignments. It is not an additional independent
copy of the composite budget \(M_{\mathrm{comp}}\).

## 4. Exact scope of the niceness literature

[Adenwalla, arXiv:2501.15170v3, section 1 and Lemma 3.1](https://arxiv.org/html/2501.15170v3#S3.Thmtheorem1)
calls a distinct congruence family *coprime disjoint* when intersecting
classes have coprime numerical moduli. A positive integer \(n\) is
*non-intersecting* when such an assignment exists for **all** its
nonunit divisors. Earlier versions use *good* and *nice* for the same
notions. Lemma 3.1 says that, for the least prime divisor \(p\) of
such an \(n\), one has \(\omega(n/p)<p\).
[Jia--Li--Liu, arXiv:2504.09579v3, Theorem 2](https://arxiv.org/html/2504.09579v3)
proves the converse for this full-divisor assignment problem.

[Adenwalla, Theorem 3.2](https://arxiv.org/html/2501.15170v3#S3.Thmtheorem2)
rules out a coprime-disjoint whole cover whose moduli are all nonunit
divisors of one integer. It does not state noncoverage for an arbitrary
divisor-closed subset of the divisors of its lcm. Report 350 gives the
latter property, not equality with the full divisor set of \(Q\).

There is, however, a valid local application. If \(d\in D\) and
\(D\) is divisor-closed, it contains every nonunit divisor of \(d\).
If \(p\) is the least prime divisor of \(d\) and
\(\omega(d/p)\ge p\), Lemma 3.1 forces a noncoprime overlapping
pair within that original block. More explicitly, choose \(p\)
different prime divisors \(q_i\) of \(d/p\). The labels \(pq_i\)
occupy only \(p-1\) nonzero first-\(p\) roots. A pair has gcd exactly
\(p\), lcm \(pq_iq_j\mid d\), and original Haar intersection mass
at least \(1/d\). PS6--PS7 retain its cost on \(Z\).
For \(p=3\), the local threshold is \(\omega(d)\ge3\) if \(9\mid d\),
or \(\omega(d)\ge4\) if \(3\parallel d\).

[Adenwalla, section 5](https://arxiv.org/html/2501.15170v3#S5)
also gives a packing condition for general palettes: for a common
pairwise gcd \(g>1\), at most \(g\) labels can be coprime disjoint,
since their residues modulo \(g\) must be different. This condition
is not sufficient; the paper gives \(\{3,6,12,18,30,42\}\) as a
counterexample. These general-palette observations do not extend its
full-divisor noncoverage theorem.

## 5. A partial family separates the older scalar test

For the nonunit divisors of \(315\), the composite totient sum is

\[
 \sum_{\substack{d\mid315\\d\ {m composite}}}\frac1{\varphi(d)}
 =\left(1+\frac12+\frac16\right)
  \left(1+\frac14\right)\left(1+\frac16\right)
  -1-\left(\frac12+\frac14+\frac16\right)=\frac{37}{72}.
 \tag{PS10}
\]

Let \(P\ge29\) be the first prime for which

\[
 \frac{37}{72}+\sum_{\substack{29\le q\le P\\q\ {m prime}}}
                  \frac1{2(q-1)}\ge1.
 \tag{PS11}
\]

Such a finite prime exists by the standard divergence of the reciprocal
prime sum. The last increment is at most \(1/56<1/48\), while the
preceding partial sum is below one. Therefore the palette

\[
 D=\{d>1:d\mid315\}
    \cup\{q:11\le q\le P,\ q\ {m prime}\}
    \cup\{3q:29\le q\le P,\ q\ {m prime}\}
 \tag{PS12}
\]

is odd, distinct and divisor-closed, has an initial segment of odd
support primes, and satisfies

\[
 1\le S<1+\frac1{56}<\frac{49}{48}.
 \tag{PS13}
\]

This is more than a numerical palette. Use the existing
[eleven-class 315 family](../001-064/01-survivor-reduction.md#uniform-sharp-head-obstruction-to-an-excess-energy-rebate):

\[
 (d,a_d)=(3,0),(9,4),(5,0),(15,1),(45,37),(7,0),
          (21,1),(35,9),(63,52),(105,4),(315,142).
\]

These classes are comparable-disjoint and have respective private
points
\(3,13,5,16,37,7,43,44,52,109,142\), as direct substitution shows.
The integer \(19\) avoids all eleven classes and is \(1\bmod3\).
For the extra labels in PS12 take \(A_q=0\bmod q\) and
\(A_{3q}=1\bmod3q\).

Extend each old private point by first digit 2 at every new prime.
For a new prime class, keep the old coordinate 19, use digit zero at
that prime and digit 2 at all other new primes. For \(A_{3q}\), keep
the old coordinate 19, use digit 1 at \(q\), and digit 2 at every
other new prime. CRT gives private points for every original class.
Comparable disjointness is preserved: the only new nontrivial
divisibility pairs are \(3\mid3q\) and \(q\mid3q\), and their
residues disagree.

Finally, old coordinate 19 together with digit 2 at every new prime
is uncovered. Thus this is an actual irredundant partial family,
not a whole cover. It passes the older necessary scalar condition
\(S\ge1\) from 361, but PS8 certifies positive uncovered density.
The separation concerns precisely that scalar condition; it does not
assert that these families pass every other known covering constraint
or that their noncoverage was previously unknown.

## 6. Remaining use and limits

The actual-common-source representation in 363 already has enough
information to charge any specified compatible pair. PS5 adds the
finite original-root constraint forcing such overlaps, and retains
the uncovered correction when whole coverage has not been established.
Different stars may overlap on the same points; without a simultaneous
allocation their bounds combine by maximum, not addition.

No common-factor overlap can be removed by freely changing just its
two residues while preserving their old union. For incomparable
moduli \(m,n\), suppose
\(A_m\cup A_n\subseteq A'_m\cup A'_n\), where the new classes have
the same respective moduli. If \(A'_m\ne A_m\), the two modulus-\(m\)
classes are disjoint, forcing \(A_m\subseteq A'_n\), hence \(n\mid m\),
a contradiction. Likewise \(A'_n=A_n\). A whole-family exchange would
need other original classes to rescue the points lost by a change;
the local overlap alone supplies no such guarantee.

The new scalar correction is conditional on the specified original
labels. It neither forces \(315\) into every hypothetical extremal
palette nor gives an incompatible bound for all palettes. A global
exclusion still requires enough forced original overlap, or other
joint coverage information, on the same law.
