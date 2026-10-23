# Uniqueness of actual sources above width eight

## 1. Original worlds and the partial result

A world is the complete triple $W=(P,g,d)$ with

$$
P=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad d\in\mathbb R,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3.
$$

Put

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix}.
$$

Products act on the left in chronological order. The acquired word is
$J,M,J,M,M,M$, with readings $(0,24,147/5,24,18,p,v)$ at clocks
$0,\ldots,6$. Every reading is $d+g(i)\operatorname{tr}(Q_iP)$.
The two alternative terminal actions occur at clock seven. Their readings
are denoted by $a(W)$ and $m(W)$. All readings in one world use that
world's same source, entire gain and fixed drift. Write $C(p,v)$ for
the entire acquired child.

The original question seeks some $p\ne24,v$ and independently chosen
pairs $A\ne B$ and $C\ne D$ in this one child, satisfying
$a(A)=a(B)$ and $m(C)=m(D)$. Pair overlap is allowed, including reuse
of the same pair, and the two common terminal values are independent.

**Theorem 1.1.** The following statements hold for the original worlds.

1. Every actual parent world with $b\ge4$ satisfies

$$
p<-\frac{216}{5},\qquad 6p<v<5p-9.
\tag{1.1}
$$

2. For every real $p,v$, there is at most one complete world in
$C(p,v)$ with $b\ge8$. More precisely, among worlds with $b\ge8$
and the same fifth reading $p$, increasing $b$ strictly decreases
$r$ and strictly increases the sixth reading $v$.
3. At width $b=4$ there exists an actual strict source at a negative
acquired base where the differential of $(r,b)\mapsto(p,v)$ has
rank exactly one.

Consequently every distinct terminal-J pair and every distinct terminal-M
pair in any acquired child contains a world with $b<8$. Across the union
of independently selected pairs there is at most one distinct world of
width at least eight. This is a restriction on actual configurations;
it does not exclude pairs mixing a width above eight with one below eight.

Part 3 asserts a critical source, not a terminal collision or a fold.
The theorem does not settle existence or nonexistence of the original
independent pairs. Singular parent sources and all allowed gain
degeneracies remain in the unrestricted question.

## 2. A whole-world polynomial chart

Use the following polynomials in independent coordinates $r,b$:

$$
\begin{aligned}
\mathcal J&=b^2+r(1-r),& \mathcal N&=\mathcal J+rb,\\
T&=1+b,&U&=1+2b,&S&=(8b-1)(2+5b),\\
D&=5\{(b^2+8b+4)\mathcal J\mathcal N
             -2TUb(\mathcal J+\mathcal N)\},\\
C_0&=-24D+3S\mathcal J\mathcal N,\\
C_1&=3S\mathcal N b,\\
C_2&=3(49b+34)\mathcal J\mathcal N
                       -54Ub(\mathcal J+\mathcal N),\\
C_3&=3S\mathcal J b,\\
B_5&=-4C_0+15C_1-20C_2+10C_3,\\
B_6&=-10C_0+36C_1-45C_2+20C_3,\\
H&=bD,\\
N_p&=-bC_0+(bU+\mathcal N)B_5,\\
N_v&=-bC_0+(2bU+\mathcal N)B_6.
\end{aligned}
\tag{2.1}
$$

On $D\ne0$, define

$$
\begin{gathered}
p=N_p/H,\qquad v=N_v/H,\qquad d=-C_0/D,\\
\ell_i(s)=\prod_{\substack{0\le k\le3\\k\ne i}}\frac{s-k}{i-k},
\qquad g(s)=\frac1D\sum_{i=0}^3 C_i\ell_i(s).
\end{gathered}
\tag{2.2}
$$

**Lemma 2.1.** Every strict source with $b\ge4$ has $D>0$ and
admits exactly one complete world realizing the first five prescribed
readings. It is (2.2), and its next two literal readings are the displayed
$p,v$.

**Proof.** Put $j=\mathcal J/b$ and $n=\mathcal N/b$. Multiplication
of the original action matrices gives successive traces

$$
1,\quad j,\quad T,\quad n,\quad U,\quad U+n,\quad 2U+n.
\tag{2.3}
$$

In particular no clock or source transformation is involved. Write
$e=d-24$. The first four prescribed readings require

$$
(g(0),g(1),g(2),g(3))=
(-24-e,-e/j,(27/5-e)/T,-e/n).
\tag{2.4}
$$

A polynomial of degree at most three is determined by these four samples.
Its value at four is the combination with weights $(-1,4,-6,4)$.
Imposing $d+Ug(4)=18$ therefore gives

$$
\begin{gathered}
\Lambda=1+6/T+1/U-4/j-4/n
       =\frac{2D}{5TU\mathcal J\mathcal N},\\
e\Lambda=-\frac{6S}{5TU}.
\end{gathered}
\tag{2.5}
$$

Since $j,n\ge b$, for $b\ge4$ one has

$$
\Lambda\ge1+6/T+1/U-8/b
 =\frac{2(b^3-8b-4)}{bTU}>0.
\tag{2.6}
$$

The numerator is positive at four and has positive derivative for
$b\ge4$. Thus $D>0$, and (2.5) gives the unique value
$e=-3S\mathcal J\mathcal N/D$. Substitution into (2.4) gives
$g(i)=C_i/D$ for $i=0,1,2,3$ and $d=-C_0/D$.
For the sample at two one uses
$T(49b+34)-S=9(b^2+8b+4)$.

The polynomial identities checking the remaining prescribed rows are

$$
\begin{aligned}
-bC_0+\mathcal JC_1&=24bD,\\
-C_0+TC_2&=(147/5)D,\\
-bC_0+\mathcal NC_3&=24bD,\\
-C_0+U(-C_0+4C_1-6C_2+4C_3)&=18D.
\end{aligned}
\tag{2.7}
$$

They follow by substitution into (2.1). The zero-clock identity is
$d+g(0)=0$. Interpolation at five and six gives $B_5/D$ and $B_6/D$,
so (2.3) yields $N_p/H$ and $N_v/H$. If this entire gain were zero,
clocks zero and one would have equal readings, contrary to $0\ne24$.
This proves the assertions, including uniqueness of the entire gain
and drift. No gain sample or gain coefficient has been divided out.
$\square$

## 3. Exact signs on unbounded source strips

Subscripts on polynomials below denote partial derivatives. Define

$$
\begin{aligned}
R&=(N_p)_rH-N_pH_r,\\
B&=(N_p)_bH-N_pH_b,\\
E&=\{(N_p)_r(N_v)_b-(N_p)_b(N_v)_r\}H\\
 &\quad-\{(N_p)_rN_v-N_p(N_v)_r\}H_b\\
 &\quad+\{(N_p)_bN_v-N_p(N_v)_b\}H_r,\\
A&=5N_p+216H,\\
L&=N_v-5N_p+9H,\\
C&=N_v-6N_p.
\end{aligned}
\tag{3.1}
$$

These are finite integer polynomials specified entirely by (2.1).
Their relevant degree bounds and strict signs are

| Polynomial | Degree in $r$ | Degree in $b$ | Source strip | Sign |
| --- | ---: | ---: | --- | --- |
| $R$ | 9 | 13 | $0\le r\le1,\ b\ge4$ | positive |
| $B$ | 10 | 12 | $0\le r\le1,\ b\ge4$ | positive |
| $E$ | 15 | 18 | $0\le r\le1,\ b\ge8$ | positive |
| $A$ | 6 | 6 | $0\le r\le1,\ b\ge4$ | negative |
| $L$ | 6 | 6 | $0\le r\le1,\ b\ge4$ | negative |
| $C$ | 6 | 7 | $0\le r\le1,\ b\ge4$ | positive |

Here is an explicit rational coefficient verification of every sign,
including the unbounded width direction. For each polynomial $F$ use its
listed degree $n$ in $r$ and cutoff $c=4$, except $c=8$ for $E$. Write

$$
F(r,c+u)=\sum_{k=0}^m\sum_{i=0}^n a_{ki}r^iu^k,\qquad
\beta_{kj}=\sum_{i=0}^j\frac{\binom ji}{\binom ni}a_{ki}.
\tag{3.2}
$$

The exact expansion is

$$
F(r,c+u)=\sum_{k=0}^m u^k
 \sum_{j=0}^n\beta_{kj}\binom njr^j(1-r)^{n-j}.
\tag{3.3}
$$

Thus strict positivity of all $\beta_{kj}$ implies positivity for
$u\ge0,0\le r\le1$, and strict negativity implies negativity.
An equivalent integer-coordinate check is that the coefficient of
$t^ju^k$ in $(1+t)^nF(t/(1+t),c+u)$ is
$\binom nj\beta_{kj}$.

For $R,B,E$, the following entries are the exact minima
$\min_{0\le j\le n}\beta_{kj}$; a dash denotes an absent width coefficient.

| $k$ | $R$, cutoff $4$ | $B$, cutoff $4$ | $E$, cutoff $8$ |
| ---: | ---: | ---: | ---: |
| 0 | 504653414400 | 170762649600 | 38169863321306403962880 |
| 1 | 1779459010560 | 451909017600 | 101401250462194540216320 |
| 2 | 2852762280960 | 544823331840 | 123516383228426201333760 |
| 3 | 2760620421120 | 395246668800 | 92408966136643882844160 |
| 4 | 1802614446720 | 191897346240 | 47831323593790445322240 |
| 5 | 839930489520 | 65568263520 | 18253178501987680911360 |
| 6 | 287631011220 | 16126960500 | 5335587907824962764800 |
| 7 | 73356659130 | 2866899960 | 1223763318798336000000 |
| 8 | 13942427490 | 363727500 | 223571250855631134720 |
| 9 | 1951456830 | 31864260 | 32812678008327951360 |
| 10 | 195587355 | 1805280 | 3881288795839678080 |
| 11 | 13297020 | 57900 | 369392208675280560 |
| 12 | 549735 | 750 | 28092246891539580 |
| 13 | 10440 | — | 1684793753081010 |
| 14 | — | — | 77961770281260 |
| 15 | — | — | 2686755912885 |
| 16 | — | — | 64955416230 |
| 17 | — | — | 983324115 |
| 18 | — | — | 7016670 |

For the three base inequalities it suffices to list the extremum over
all $k,j$:

| Polynomial | Extremum of the coefficients in (3.2), cutoff $4$ |
| --- | ---: |
| $A$ | $\max\beta_{kj}=-750$ |
| $L$ | $\max\beta_{kj}=-768$ |
| $C$ | $\min\beta_{kj}=171$ |

These tables are obtained by expanding exactly (2.1) and (3.1) and
applying the finite coefficient formula (3.2). They specify signs of
polynomials on the whole strips, rather than pointwise samples.
For the derivative determinant, the polynomial identity

$$
\begin{aligned}
&\{(N_p)_rH-N_pH_r\}\{(N_v)_bH-N_vH_b\}\\
&\quad-\{(N_p)_bH-N_pH_b\}\{(N_v)_rH-N_vH_r\}=HE
\end{aligned}
\tag{3.4}
$$

also checks the denominator cancellation. On $b\ge4$, where $H>0$,

$$
p_r=R/H^2>0,\qquad p_b=B/H^2>0,\qquad
p_rv_b-p_bv_r=E/H^3.
\tag{3.5}
$$

On $b\ge8$ the last expression is strictly positive. Finally,
$A<0,L<0,C>0$, divided by $H>0$, give exactly (1.1).

## 4. Global injectivity on the entire upper strip

Suppose two strict source points with $b\ge8$ have the same $p$.
If their widths agree, $p_r>0$ makes their $r$ coordinates agree.
Consider instead widths $b_1<b_2$ and let the common reading be $p_*$.
For every $b\in[b_1,b_2]$, monotonicity at the closed endpoint sources
$r=0,1$ gives

$$
p(0,b)\le p(0,b_2)<p_*,\qquad
p(1,b)\ge p(1,b_1)>p_*.
\tag{4.1}
$$

These endpoint values are well-defined by $D>0$; they are auxiliary
values, not additional original worlds. Since $p_r>0$, there is exactly
one $r(b)\in(0,1)$ with $p(r(b),b)=p_*$. The implicit-function theorem
and uniqueness join these local functions throughout the interval.
They obey

$$
r'(b)=-\frac{p_b}{p_r}<0,
\qquad
\frac{d}{db}v(r(b),b)
=v_b-v_r\frac{p_b}{p_r}
=\frac{E}{H^3p_r}>0.
\tag{4.2}
$$

The two points therefore have different sixth readings. This proves
injectivity of $(r,b)\mapsto(p,v)$ on the entire unbounded strip
$0<r<1,b\ge8$, and proves the claimed ordering at fixed $p$.
Lemma 2.1 makes equality of source points equality of complete worlds.
It follows that every entire acquired child contains at most one world
in this strip. This argument compares unequal widths and imposes no
terminal-response equality.

## 5. An exact negative-base critical source at width four

The same determinant polynomial has the exact endpoint values

$$
E(0,4)=-545620205984808960<0,\qquad
E(1,4)=437107566064435200>0.
\tag{5.1}
$$

They follow directly by substituting into (2.1) and (3.1). The
intermediate value theorem supplies $r_*\in(0,1)$ satisfying
$E(r_*,4)=0$. This is an exact algebraic source condition: one may
choose any real root of this displayed, nonzero integer polynomial
inside that open interval. No numerical root is needed for existence.

At $(r_*,4)$, Lemma 2.1 supplies the original strict source, one whole
nonzero polynomial gain of degree at most three, and its fixed drift.
The first five readings are exactly the prescribed ones. Set

$$
p_*=\frac{N_p(r_*,4)}{H(r_*,4)},\qquad
v_*=\frac{N_v(r_*,4)}{H(r_*,4)}.
\tag{5.2}
$$

By (1.1), $p_*<-216/5<0$, with $6p_*<v_*<5p_*-9$.
By (3.5), the determinant of the acquired differential vanishes
there, while $p_r>0$. The differential consequently has rank exactly
one. This proves Part 3 of Theorem 1.1. No assertion about fold
nondegeneracy, multiplicity of the child, or terminal equality follows
merely from this criticality.

## 6. Consequences for independent pairs and attribution

If a distinct terminal pair had both widths at least eight, its two
worlds would share $p,v$ in the strip, contradicting Section 4.
This applies separately to the J pair and the M pair, regardless of
overlap and regardless of their common terminal values. The same
argument shows that no acquired child contains two distinct actual
upper-width exceptional reconstruction worlds whenever both have
width at least eight. It requires no classification of exceptional
roots or special treatment of reconstruction coordinates.

In particular, apply this restriction to the actual worlds retained by
the all-width rational and exceptional reconstruction of Sections 54–59
of *An exact unequal-diagonal pair for the original terminal M response*.
For fixed $p,v$, even when the reconstructed terminal-M value is allowed
to vary, those retained worlds include at most one with $b\ge8$.
The source filters remain necessary; a reconstruction root alone is
not an actual world or a collision witness.

Thus a negative-base search involving a world above width eight must
seek every distinct companion below width eight. Worlds with
$4\le b<8$ are not covered by the injectivity assertion. Worlds with
$b<4$, including parent singularities, all positive widths and gain
degeneracies allowed by the original histories, remain available in
the original problem. The critical source in Section 5 belongs to
this remaining negative-base region. These restrictions do not imply
that a companion below width eight exists or is absent.

The regular whole-world polynomial chart agrees with Sections 2 and
31 of *An exact unequal-diagonal pair for the original terminal M
response*. The unrestricted parent and literal reading convention
agree with Sections 1–2 of *FIB common-parent geometry and two exact
mixed children*. Section 2 gives the needed interpolation and original
row identities explicitly. The exceptional-graph candidate motivates
the negative-base region but is not used as an algebraic certificate.
No exceptional classification, fixed-width collision criterion or
all-width reconstruction criterion is asserted as a new result here.

The additional conclusions are the base wedge on the whole strip
$b\ge4$, global acquired injectivity and ordering on the unbounded
strip $b\ge8$, their necessary restrictions on independent pairs,
and an actual rank-one acquired critical source at a negative base.
The coefficient signs, endpoint computations and monotone-level
argument provide ordinary mathematical proofs. No formal-kernel or
literature-priority claim is made.

## 追加锚（本行以下为增补区）

## 7. A terminal-J coordinate on the entire negative sheet

Retain the complete worlds, literal clocks, chronological left products,
and entire child $C(p,v)$ of Section 1. In particular $a(W)$ is the
alternative terminal-J reading at clock seven of that same world.
Extend the polynomial chart (2.1) by

$$
\begin{aligned}
G_7&=-20C_0+70C_1-84C_2+35C_3,\\
N_a&=-bC_0+(bT+2\mathcal J+4br)G_7,\qquad a=N_a/H.
\end{aligned}
\tag{7.1}
$$

The earlier interpolation numerators $B_5,B_6$ retain their meanings;
$G_7=Dg(7)$ is their clock-seven counterpart.

**Theorem 7.1 (Global negative-sheet terminal coordinate).** For each
$p<-216/5$, all original parent worlds with fifth reading $p$ and
$b\ge1$ form exactly one real analytic graph
$b=B_p(r)$, $0<r<1$. At every $r$ its width exceeds the unique
source-denominator pole $\lambda(r)$, where $1<\lambda(r)<4$.
Along this entire graph $a(r,B_p(r))$ strictly decreases with $r$.
Thus two distinct such complete worlds cannot have the same $p,a$,
without any requirement that their sixth readings agree.

There are no original parent worlds with $b\ge1$ and
$-216/5\le p<0$. On the full set of original parent worlds with
$b\ge1,p<0$, the map $W\mapsto(p(W),a(W))$ is a real analytic
diffeomorphism onto the explicit open region $\Omega_J$ of (11.4).
The analytic structure on this world set is the one induced by its
source coordinates $(r,b)$ and the unique whole-world lift (2.2).

**Lemma 7.2 (Literal lift at every width at least one).** For
$0<r<1,b\ge1$, a source admits an original parent world if and only
if $D\ne0$. In that case the unique entire gain and fixed drift are
(2.2), and the literal terminal-J reading is (7.1).

**Proof.** Write $j=\mathcal J/b$, $n=\mathcal N/b$ and
$\epsilon=d-24$. Both $j,n$ and $T,U$ are positive. The first
four readings force precisely (2.4). Fixed-node Lagrange
interpolation [1, §2] makes the fifth prescribed reading equivalent
to (2.5), namely

$$
\epsilon\Lambda=-\frac{6S}{5TU},\qquad
\Lambda=\frac{2D}{5TU\mathcal J\mathcal N}.
\tag{7.2}
$$

Since $S=(8b-1)(2+5b)>0$ for $b\ge1$, $D=0$ is inconsistent
with (7.2), for every real drift. For $D\ne0$, solving (7.2)
gives $\epsilon=-3S\mathcal J\mathcal N/D$. Substitution into
(2.4) gives exactly $g(i)=C_i/D$ for $0\le i\le3$;
(2.7) verifies the prescribed rows without a width-four assumption.
The initial values determine the entire polynomial of degree at
most three. It cannot vanish identically because readings zero and
one are $0$ and $24$.

For the literal acquired product and its terminal J, matrix multiplication
gives

$$
Q_6=\begin{pmatrix}3&1\\5&2\end{pmatrix},\qquad
JQ_6=\begin{pmatrix}5&2\\3&1\end{pmatrix},\qquad
\operatorname{tr}(JQ_6P)=T+2j+4r.
\tag{7.3}
$$

The interpolation values $\ell_i(7)$ are $(-20,70,-84,35)$.
Thus $g(7)=G_7/D$, and
$d+(T+2j+4r)g(7)=N_a/H$. These are the same source, gain and
drift as in every acquired row. Conversely the prescribed-row
identities and this interpolation construct that complete world.
No gain sample, leading coefficient, root difference or drift is
cancelled. Lower degrees, zero samples, repeated gain roots and zero
drift are therefore included whenever the original rows permit them.
$\square$

## 8. Exact terminal-coordinate signs on the unbounded strip

Keep $R,B$ from (3.1), and introduce distinct terminal derivative
numerators

$$
R_a=(N_a)_rH-N_aH_r,\qquad
B_a=(N_a)_bH-N_aH_b.
\tag{8.1}
$$

Define the integer polynomial

$$
\begin{aligned}
E_J={}&\{(N_p)_r(N_a)_b-(N_p)_b(N_a)_r\}H\\
&-\{(N_p)_rN_a-N_p(N_a)_r\}H_b\\
&+\{(N_p)_bN_a-N_p(N_a)_b\}H_r.
\end{aligned}
\tag{8.2}
$$

Expansion gives the exact polynomial identity

$$
RB_a-BR_a=HE_J.
\tag{8.3}
$$

In particular there is no remainder in this denominator cancellation.
Where $H\ne0$,

$$
p_b=\frac{B}{H^2},\qquad
p_ra_b-p_ba_r=\frac{E_J}{H^3}.
\tag{8.4}
$$

**Lemma 8.1.** On the entire closed auxiliary strip
$0\le r\le1,b\ge1$,

$$
N_p<0,\qquad B>0,\qquad E_J>0.
\tag{8.5}
$$

**Proof.** For each polynomial $F$ below put $u=b-1$ and use its
listed degree $n$ in $r$. Define rational coefficients by

$$
\begin{aligned}
F(r,1+u)&=\sum_{k=0}^m\sum_{i=0}^n c_{ki}r^iu^k,\\
\beta_{kj}&=\sum_{i=0}^j
 c_{ki}\frac{\binom ji}{\binom ni}.
\end{aligned}
\tag{8.6}
$$

The power-to-Bernstein basis identity [2] is

$$
F(r,1+u)=\sum_{k=0}^m u^k
 \sum_{j=0}^n\beta_{kj}\binom njr^j(1-r)^{n-j}.
\tag{8.7}
$$

All basis functions are nonnegative for $u\ge0,0\le r\le1$,
and the inner Bernstein basis sums to one. The following exact
row extrema, obtained by substituting (2.1), (7.1) and (8.2) into
the finite formula (8.6), establish every sign in (8.5).

For $N_p$, the degrees in $(r,b)$ are $(6,7)$:

| $k$ | $\min_j\beta_{kj}$ | $\max_j\beta_{kj}$ |
| ---: | ---: | ---: |
| 0 | -8519/2 | -12536/5 |
| 1 | -23475 | -27561/2 |
| 2 | -54396 | -29589 |
| 3 | -67830 | -32664 |
| 4 | -48495 | -20766 |
| 5 | -19359 | -8058 |
| 6 | -3750 | -1878 |
| 7 | -216 | -216 |

For $B$, the degrees are $(10,12)$:

| $k$ | $\min_j\beta_{kj}$ | $\max_j\beta_{kj}$ |
| ---: | ---: | ---: |
| 0 | 874277/7 | 252570 |
| 1 | 1212738 | 2465190 |
| 2 | 5297740 | 10898160 |
| 3 | 55479753/4 | 28822830 |
| 4 | 24158010 | 50734770 |
| 5 | 87422276/3 | 62558220 |
| 6 | 25265949 | 55381200 |
| 7 | 15513372 | 35489100 |
| 8 | 6657630 | 16384830 |
| 9 | 1911360 | 5352270 |
| 10 | 340080 | 1190400 |
| 11 | 30900 | 165510 |
| 12 | 750 | 11190 |

For $E_J$, the degrees are $(15,18)$:

| $k$ | $\min_j\beta_{kj}$ | $\max_j\beta_{kj}$ |
| ---: | ---: | ---: |
| 0 | 1090737612 | 8952140160 |
| 1 | 15906987720 | 128028015360 |
| 2 | 108264114000 | 857152362240 |
| 3 | 460760217840 | 3567178594080 |
| 4 | 1376750292480 | 10333282825440 |
| 5 | 3071933847000 | 22108000999680 |
| 6 | 5311118669040 | 36174741166080 |
| 7 | 7281507697920 | 46248651614880 |
| 8 | 8030219767200 | 46796723249760 |
| 9 | 7181068908600 | 37732113809280 |
| 10 | 5223381896880 | 24292734238080 |
| 11 | 3086517685680 | 12462315677280 |
| 12 | 1473100470720 | 5062862593440 |
| 13 | 561425645160 | 1611248129280 |
| 14 | 167536555920 | 394782819840 |
| 15 | 37859764320 | 72361582560 |
| 16 | 6108032160 | 9415942560 |
| 17 | 627192000 | 779644800 |
| 18 | 30729600 | 30729600 |

Each upper extremum for $N_p$ is negative and each lower extremum
for $B,E_J$ is positive. In particular their $k=0$ rows make the
signs strict even at $u=0$. The identity (8.7) proves the assertions
on the whole unbounded strip. Endpoint sources $r=0,1$ in this proof
are auxiliary polynomial values, not legal original worlds. $\square$

## 9. The unique denominator pole and its sign on both sides

**Lemma 9.1.** For every $0\le r\le1$, the function $b\mapsto D(r,b)$
has exactly one zero $\lambda(r)$ above one. This zero is simple,
$1<\lambda(r)<4$, and

$$
\begin{cases}
D(r,b)<0,&1\le b<\lambda(r),\\
D(r,b)>0,&b>\lambda(r).
\end{cases}
\tag{9.1}
$$

The function $\lambda$ is real analytic, including local extensions
at the two auxiliary endpoints.

**Proof.** Write $D(r,1+u)=\sum_{k=0}^6d_k(r)u^k$.
The exact coefficient polynomials are

$$
\begin{aligned}
d_0&=5(13r^4-39r^3+24r^2+3r-11),\\
d_1&=5(10r^4-43r^3+13r^2+31r-38),\\
d_2&=5(r^4-13r^3-20r^2+58r-45),\\
d_3&=-5(r^3+15r^2-40r+16),\\
d_4&=-5(2r^2-11r-7),\\
d_5&=5(r+6),\qquad d_6=5.
\end{aligned}
\tag{9.2}
$$

Using each $d_k$'s own degree in $r$, their Bernstein coefficient
extrema are

| $k$ | Minimum | Maximum |
| ---: | ---: | ---: |
| 0 | -55 | -55/2 |
| 1 | -190 | -95 |
| 2 | -225 | -295/4 |
| 3 | -80 | 40 |
| 4 | 35 | 80 |
| 5 | 30 | 35 |
| 6 | 5 | 5 |

Thus the coefficient signs in increasing powers of $u$ are
negative, negative, negative, arbitrary, positive, positive,
positive. After deleting any zero coefficient, there is exactly
one sign change, whatever the sign of $d_3$. Descartes' rule of
signs [3, Book III] bounds the number of positive roots counted
with multiplicity by one. Since $D(r,1)=d_0(r)<0$ and $d_6=5>0$,
the intermediate value theorem [4, Theorem 4.23] supplies a positive
$u$-root. There is exactly one and its multiplicity is one.
Uniqueness and continuity give (9.1).

For $b\ge4$, the inequality $j,n\ge b$ gives (2.6), so
$D(r,b)>0$ there, including at the auxiliary endpoints. The cubic
$b^3-8b-4$ is positive at four and strictly increasing thereafter.
Hence $\lambda(r)<4$. Simplicity permits the real analytic
implicit-function theorem [5] at every root; uniqueness joins these
local analytic functions into the stated $\lambda$. $\square$

## 10. One connected fixed-base graph and global terminal order

**Lemma 10.1.** For each fixed $0\le r\le1$, the negative fifth
readings at widths at least one are exactly $(-\infty,-216/5)$.
Each occurs exactly once, at a width $B_p(r)>\lambda(r)$.

**Proof.** Lemma 8.1 and $H=bD$ show that $p>0$ on
$1\le b<\lambda(r)$ and $p<0$ on $b>\lambda(r)$.
The pole itself supplies no actual parent world by Lemma 7.2.
On its right-hand side the exact facts are

$$
\lim_{b\downarrow\lambda(r)}p(r,b)=-\infty,\qquad
p_b=\frac{B}{H^2}>0,\qquad
\lim_{b\to\infty}p(r,b)=-\frac{216}{5}.
\tag{10.1}
$$

For the first limit, $N_p(r,\lambda(r))<0$ and $H$ approaches
zero from above. For the last, the leading terms in $b$ are
$N_p=-216b^7+\text{terms of lower degree}$ and
$H=5b^7+\text{terms of lower degree}$, independently of $r$.
Strict increase, continuity and these limits prove that
$b\mapsto p(r,b)$ is a bijection from
$(\lambda(r),\infty)$ onto $(-\infty,-216/5)$.
This proves the assertion, including the unattained endpoint.
$\square$

For each $p<-216/5$, the analytic implicit-function theorem [5]
applied to $p(r,b)=p$ gives $b=B_p(r)$, jointly real analytic
in $r,p$. Uniqueness in Lemma 10.1 joins the local solutions on
the entire connected interval $0<r<1$ and extends them to its
auxiliary endpoints. Consequently the complete negative source sheet is

$$
\mathcal S_-=
\{(r,b):0<r<1,\ b>\lambda(r)\}
=\{(r,B_p(r)):0<r<1,\ p<-216/5\}.
\tag{10.2}
$$

It is connected: $(r,p)\mapsto(r,B_p(r))$ parametrizes it
continuously from the connected product
$(0,1)\times(-\infty,-216/5)$, with continuous inverse $(r,b)\mapsto(r,p)$.
There is no other negative component with $b\ge1$.

**Lemma 10.2 (Order along the entire graph).** Set
$A_p(r)=a(r,B_p(r))$. Then

$$
\begin{aligned}
B_p'(r)&=-\frac{p_r}{p_b},\\
A_p'(r)&=a_r-a_b\frac{p_r}{p_b}
       =-\frac{E_J}{H^3p_b}<0.
\end{aligned}
\tag{10.3}
$$

**Proof.** Differentiate the exact level equation and use (8.4).
Every point in (10.2) has $H>0$, $E_J>0$ and $p_b>0$.
The mean value theorem [4, Theorem 5.10] now gives strict decrease
on the entire connected graph, including comparisons between
arbitrarily separated finite widths. If $p,a$ agree for two such
sources, strict decrease gives equal $r$, and Lemma 10.1 gives equal
$b$. Lemma 7.2 then gives equality of their complete triples.
This proves the global injectivity and ordering parts of Theorem 7.1.
$\square$

## 11. Explicit algebraic boundary functions and exact image

At the auxiliary endpoint sources the rational readings are

$$
\begin{aligned}
p_0(b)&=-\frac{3(72b^3+746b^2+465b+130)}
                   {5(b^3-8b-4)},\\
a_0(b)&=-\frac{9(136b^3+2062b^2+1163b+182)}
                   {5(b^3-8b-4)},\\
p_1(b)&=-\frac{6(36b^4+61b^3+221b^2+181b+30)}
                   {5(b+1)(b^3-4b-2)},\\
a_1(b)&=-\frac{6(204b^4+869b^3+2469b^2+2981b+610)}
                   {5(b+1)(b^3-4b-2)}.
\end{aligned}
\tag{11.1}
$$

These follow by substituting $r=0,1$ into (2.1) and (7.1) and
cancelling the displayed common factors; the denominator identities are

$$
D(0,b)=5b^3(b^3-8b-4),\qquad
D(1,b)=5b^2(b+1)(b^3-4b-2).
\tag{11.2}
$$

Let $\lambda_0=\lambda(0)$ and $\lambda_1=\lambda(1)$ be the
unique roots above one of the respective cubics in (11.2).
For $p<-216/5$, let $\beta_0(p)>\lambda_0$ and
$\beta_1(p)>\lambda_1$ be the unique solutions
$p_0(\beta_0(p))=p$ and $p_1(\beta_1(p))=p$.
Lemma 10.1 proves their existence and uniqueness and fixes the
root selections. These equations specify exact real analytic
algebraic functions of $p$. Define

$$
U_J(p)=a_0(\beta_0(p)),\qquad
L_J(p)=a_1(\beta_1(p)).
\tag{11.3}
$$

**Theorem 11.1 (Image and analytic inverse).** The image in Theorem 7.1 is

$$
\Omega_J=\{(p,a):p<-216/5,\ L_J(p)<a<U_J(p)\}.
\tag{11.4}
$$

For every such $p$, $L_J(p)<U_J(p)$. Neither boundary is included
as a legal source. The map from the entire original negative world
sheet with $b\ge1$ to $\Omega_J$ is a real analytic diffeomorphism.

**Proof.** The function $A_p$ extends analytically to local
neighborhoods of $r=0,1$ by Lemma 10.1 and the implicit-function
theorem. The signs in (10.3) hold also at those auxiliary endpoints.
It is therefore continuous and strictly decreasing on $[0,1]$,
with endpoint values $U_J(p)$ and $L_J(p)$. The intermediate value
theorem makes its image on $(0,1)$ exactly the open interval between
them, with each value attained once. This proves (11.4), its strict
boundary order and global bijectivity.

The Jacobian of $(r,b)\mapsto(p,a)$ is $E_J/H^3>0$ everywhere
on $\mathcal S_-$. The real analytic inverse-function theorem [5]
gives an analytic local inverse at every image point. Global
bijectivity makes these local inverses agree, giving one analytic
inverse on the open set $\Omega_J$. Finally (2.2) lifts each source
analytically to the entire gain coefficients and drift, and projection
onto the entries $r,b$ of $P$ recovers its source. This proves the
claimed diffeomorphism for complete worlds and completes Theorem 7.1.
$\square$

## 12. Independent pairs and the remaining original obligation

**Corollary 12.1.** At every negative base $p<0$, a distinct
terminal-J pair in any entire child $C(p,v)$ contains at least one
world with $b<1$.

**Proof.** If both widths were at least one, Lemma 10.1 would first
force $p<-216/5$, and Lemma 10.2 would make equality of $p,a$
imply equality of complete worlds. This contradicts distinctness.
The conclusion is independent of the common sixth reading. $\square$

The acquired map $(r,b)\mapsto(p,v)$ can have critical sources;
Theorem 7.1 asserts no additional acquired-map injectivity. In
particular the width-four rank-one source of Section 5 cannot yield
a terminal-J collision with any other world of width at least one
at its negative base. This applies even to a companion arbitrarily
far from its local acquired critical chart. It supplies neither the
existence nor the exclusion of a companion below width one.

The J pair may be disjoint from, overlap, or coincide with an independent
M pair. Its two members need not have equal terminal-M readings, and its
common terminal-J value need not equal the M pair's common terminal-M
value. Corollary 12.1 constrains the J pair separately. It does not
impose its width-one restriction on both members of the M pair.
Section 6's width-eight restrictions remain applicable separately.
The J pair need not contain the width-four critical world; two worlds
below width one are still possible under the stated restrictions.

The original unresolved assertion remains the existence of real
$p\ne24,v$ and complete worlds $W_0,W_1,W_2,W_3$ such that

$$
\begin{gathered}
W_0,W_1,W_2,W_3\in C(p,v),\qquad
W_0\ne W_1,\quad W_2\ne W_3,\\
a(W_0)=a(W_1),\qquad m(W_2)=m(W_3).
\end{gathered}
\tag{12.1}
$$

There is no condition relating the two pairs' terminal values or
requiring four different worlds. The negative-base route still
requires the entire $b<1$ sector and its possible common acquired
child with $\mathcal S_-$. This includes the parent-singular
$b=1/8,\Lambda=0$ sources, with arbitrary allowed drift, retained
by the zero-safe parent equation in *FIB common-parent geometry and
two exact mixed children*, Theorem 2.1. The positive-base sector,
all lower gain degrees, gain zeros and repeated roots, and zero drift
remain in (12.1). No source restriction here changes that domain.

The additional terminal-coordinate theorem therefore does not settle
(12.1) or its global negation. The determinant sign is combined with
a proved single global graph and its full image; an acquired critical
point alone proves no terminal collision. No numerical root, residual
or unsuccessful search supplies a premise of these conclusions.

## 13. Classical mathematical attribution

The fixed-node interpolation in Lemma 7.2 uses [1]. The Bernstein
basis conversion and positivity argument in Lemma 8.1 use [2].
Lemma 9.1 uses Descartes' rule [3] and the intermediate value theorem
[4]; the global ordering uses the mean value theorem [4]. Analytic
parametrization and the analytic inverse use [5]. The specific
polynomials, their exact coefficient extrema, the resulting global
negative-sheet terminal-J coordinate, and its algebraic image are the
model-specific conclusions proved in Sections 7–11. These are ordinary
mathematical proofs, with no formal-kernel or literature-priority claim.

[1] Jean-Paul Berrut and Lloyd N. Trefethen, “Barycentric Lagrange
Interpolation,” *SIAM Review* **46** (2004), 501–517, §2.

[2] Rida T. Farouki, “The Bernstein polynomial basis: A centennial
retrospective,” *Computer Aided Geometric Design* **29** (2012), 379–419.

[3] René Descartes, *La Géométrie* (1637), Book III, rule of signs.

[4] Walter Rudin, *Principles of Mathematical Analysis*, third edition,
McGraw-Hill, Theorems 4.23 and 5.10.

[5] Steven G. Krantz and Harold R. Parks, *A Primer of Real Analytic
Functions*, second edition, Birkhäuser, implicit and inverse function
theorems for real analytic functions.

## 追加锚（本行以下为增补区）

## 14. The complete singular parent in the existing chart

Keep the original complete worlds, chronological left action word,
clocks and acquired child $C(p,v)$ of Section 1. In particular the
source has $0<r<1,b>0$, and each world has one entire nonzero real
polynomial gain of degree at most three and one fixed real drift.
Here a **singular parent world** means an actual five-row parent world
whose source satisfies $\Lambda=0$, with $\Lambda$ as in (2.5).
This is a condition on the parent reconstruction, not a restriction
on the rank of an acquired-response map.

The existing first-four-sample reconstruction (2.4), before any division
by $D$, uses $\epsilon=d-24$ and gives

$$
(z_0,z_1,z_2,z_3)=
\left(-24-\epsilon,-\frac\epsilon j,
\frac{27/5-\epsilon}{T},-\frac\epsilon n\right),\qquad
 g(s)=\sum_{i=0}^3z_i\ell_i(s).
\tag{14.1}
$$

All of $j=b+r(1-r)/b$, $n=j+r$, $T=1+b$, $U=1+2b$ are
strictly positive. The full zero-safe parent equation is

$$
\epsilon\Lambda+\frac{24}{5}(b-1/8)B_{\rm par}=0,\qquad
B_{\rm par}=\frac6T-\frac2U=\frac{2(2+5b)}{TU}>0.
\tag{14.2}
$$

Indeed interpolation at four gives the exact residual identity

$$
d+Ug(4)-18
=U\left\{\epsilon\Lambda+\frac{24}{5}(b-1/8)B_{\rm par}\right\}.
\tag{14.3}
$$

The constant term after division by $U$ is
$6/U+24-162/(5T)=(24/5)(b-1/8)B_{\rm par}$; the coefficient
of $\epsilon$ is $\Lambda$. Thus (14.1) and (14.2) are necessary
and sufficient for the original five rows. This is precisely the
zero-safe parent of *FIB common-parent geometry and two exact mixed
children*, Theorem 2.1, and the parent underlying (2.4)–(2.5).
No new independent gain samples have been introduced.

At a singular parent, (14.2) forces $b=1/8$. Conversely at that width,
$\Lambda=0$ allows every real $\epsilon$. Put

$$
T=\frac98,\quad U=\frac54,\quad
j=\frac18+8r(1-r),\quad n=j+r.
\tag{14.4}
$$

Direct multiplication gives

$$
\begin{aligned}
\Phi(r)&=438272r^4-931328r^3+540800r^2-50728r-853\\
       &=64\{107jn-60(j+n)\},\\
\Lambda&=\frac{107}{15}-\frac4j-\frac4n
        =\frac{\Phi(r)}{960jn}.
\end{aligned}
\tag{14.5}
$$

Hence all legal singular sources are exactly $b=1/8$, $0<r<1$,
$\Phi(r)=0$. Their drift and whole gain are still determined by
(14.1) for the freely selected $\epsilon$. In particular neither
$\epsilon=0$ nor $\epsilon=-24$ is discarded.

## 15. An exact positive-scaled Sturm chain and root isolation

Use the following integer polynomials:

$$
\begin{aligned}
S_0&=\Phi,\\
S_1&=219136r^3-349248r^2+135200r-6341,\\
S_2&=1610816r^2-1689664r+121445,\\
S_3&=64839740164r-26327821511,\\
S_4&=78580316788659208197744775.
\end{aligned}
\tag{15.1}
$$

Here $S_0'=8S_1$. The exact division identities are

$$
\begin{aligned}
S_0&=\frac{32r-17}{16}S_1-\frac1{16}S_2,\\
S_1&=\frac{107(805408r-438787)}{633478561}S_2
       -\frac{64}{633478561}S_3,\\
S_2&=\frac{4(1631951420187716r-1049189040459405)}
                {262761994033439671681}S_3
       -\frac1{262761994033439671681}S_4.
\end{aligned}
\tag{15.2}
$$

All three factors multiplying the next negative remainder are positive.
Consequently these polynomials form a positive-scaled Sturm chain [6].
The nonzero constant last term also proves that $\Phi$ and $\Phi'$
have no common root. All roots of $\Phi$ are therefore simple.

For a real $x$ where no chain entry vanishes, let $V(x)$ count sign
changes in $(S_0(x),\ldots,S_4(x))$. The exact endpoint signs are

| $x$ | Signs of $S_0,S_1,S_2,S_3,S_4$ | $V(x)$ |
| --- | --- | ---: |
| $0$ | $(-,-,+,-,+)$ | 3 |
| $134815/10^6$ | $(-,+,-,-,+)$ | 3 |
| $134816/10^6$ | $(+,+,-,-,+)$ | 2 |
| $902449/10^6$ | $(+,-,-,+,+)$ | 2 |
| $902450/10^6$ | $(-,-,-,+,+)$ | 1 |
| $1$ | $(-,-,+,+,+)$ | 1 |

These signs can be checked with integers alone. For $x=k/N$, the
following entries are $N^4S_0(x)$, $N^3S_1(x)$, $N^2S_2(x)$ and
$NS_3(x)$; $S_4$ is the positive constant in (15.1).
For the four interior endpoints $N=10^6$; at $0,1$ use $N=1$.

| $k/N$ | $N^4S_0$ | $N^3S_1$ | $N^2S_2$ | $NS_3$ |
| --- | ---: | ---: | ---: | ---: |
| $0$ | $-853$ | $-6341$ | $121445$ | $-26327821511$ |
| $134815/10^6$ | $-42530685653395898880000$ | $6075319423423201024000$ | $-77070335689022400$ | $-17586451940790340$ |
| $134816/10^6$ | $6072081656124845064192$ | $6075372403870111891456$ | $-77071591027093504$ | $-17586387101050176$ |
| $902449/10^6$ | $42022366160253876252672$ | $-7704635405746733889536$ | $-91519167013147584$ | $32186737160261636$ |
| $902450/10^6$ | $-19614556103500800000000$ | $-7704595160110592000000$ | $-91517949316960000$ | $32186802000001800$ |
| $1$ | $-3837$ | $-1253$ | $42597$ | $38511918653$ |

Sturm's theorem now gives exactly two roots in $(0,1)$, one in each
of the following disjoint open rational intervals:

$$
\frac{134815}{10^6}<r_-<\frac{134816}{10^6},\qquad
\frac{902449}{10^6}<r_+<\frac{902450}{10^6}.
\tag{15.3}
$$

These root definitions are exact. Neither a numerical root nor a
floating-point residual is a premise of the argument.

## 16. Entire gains and all three affine responses

At either root use the same interpolation basis $\ell_i$ as (2.2) and
set

$$
h(s)=\frac85(s-1)(s-3)(s-5),\qquad
q_r(s)=-\ell_0(s)-\frac{\ell_1(s)}j
                   -\frac{\ell_2(s)}T-\frac{\ell_3(s)}n.
\tag{16.1}
$$

Thus $q_r(0),\ldots,q_r(3)$ equal
$-1,-1/j,-1/T,-1/n$. Substitution in (14.1), with $T=9/8$, proves
that the complete singular worlds are exactly

$$
W(r,\epsilon)=
\left(P(r,1/8),\ h+\epsilon q_r,\ 24+\epsilon\right),
\qquad r\in\{r_-,r_+\},\quad\epsilon\in\mathbb R.
\tag{16.2}
$$

For completeness, the fixed part has values

$$
(h(0),\ldots,h(7))=
(-24,0,24/5,0,-24/5,0,24,384/5).
\tag{16.3}
$$

The interpolation weights at four through seven give

$$
\begin{aligned}
q_r(4)&=1-4/j+6/T-4/n=-1/U,\\
q_r(5)&=4-15/j+20/T-10/n,\\
q_r(6)&=10-36/j+45/T-20/n,\\
q_r(7)&=20-70/j+84/T-35/n.
\end{aligned}
\tag{16.4}
$$

The last equality for $q_r(4)$ uses $\Lambda=0$. These identities
verify all five prescribed rows, including
$24+\epsilon+U(-24/5-\epsilon/U)=18$ at four.
A zero entire gain would make the first two readings both equal to
the drift, contrary to $0\ne24$. Thus (16.2) always has a nonzero
whole gain, without imposing nonzero samples, exact degree or simple
roots. The four interpolated samples prove its uniqueness at fixed
source and drift.

At a root, (14.5) gives $1/j+1/n=107/60$. In particular

$$
q_r(5)=\frac{71}{18}-\frac5j,\quad
q_r(6)=\frac{43}{3}-\frac{16}j,\quad
q_r(7)=\frac{129}{4}-\frac{35}j.
\tag{16.5}
$$

Define the fifth-response coefficient and the terminal-J trace by

$$
A_5(r)=1+(n+5/4)q_r(5),\qquad L(r)=T+2j+4r.
\tag{16.6}
$$

Since $n>j>0$, the root relation implies $1/j>107/120$ and
$n>120/107$. Hence

$$
q_r(5)<-\frac{37}{72},\qquad
A_5(r)<1-\left(\frac{120}{107}+\frac54\right)\frac{37}{72}
       =-\frac{6739}{30816}<0.
\tag{16.7}
$$

There is consequently exactly one complete singular world at each
source $r_\pm$ and each prescribed real fifth reading $p$:

$$
\epsilon_r(p)=\frac{p-24}{A_5(r)},\qquad
W_r(p)=W(r,\epsilon_r(p)).
\tag{16.8}
$$

This includes $p=24$, where $\epsilon=0$. It follows from the
original gain reconstruction, rather than treating gain values at
later clocks as additional free variables.

The literal products are $Q_5=\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$,
$Q_6=\left(\begin{smallmatrix}3&1\\5&2\end{smallmatrix}\right)$,
and $JQ_6=\left(\begin{smallmatrix}5&2\\3&1\end{smallmatrix}\right)$.
Their traces against the original source are $U+n$, $2U+n$, $L$.
Therefore, with the same entire $g$ and fixed $d$ throughout, put

$$
\begin{aligned}
V_0(r)&=24(7/2+n),&
V_1(r)&=\frac{1+(5/2+n)q_r(6)}{A_5(r)},\\
A_0(r)&=24+\frac{384}{5}L(r),&
A_1(r)&=\frac{1+L(r)q_r(7)}{A_5(r)}.
\end{aligned}
\tag{16.9}
$$

The exact affine responses are

$$
\begin{aligned}
p(W(r,\epsilon))&=24+A_5(r)\epsilon,\\
v(W_r(p))&=V_0(r)+V_1(r)(p-24),\\
a(W_r(p))&=A_0(r)+A_1(r)(p-24).
\end{aligned}
\tag{16.10}
$$

No terminal-M equality or additional acquired observation enters
these formulas.

## 17. A finite rational interval proof of separation

Every finite decimal in this section denotes its exact rational value.
For intervals, addition and multiplication use exact endpoints, taking
the minimum and maximum of all four endpoint products. If $0$ is
excluded, $[x_-,x_+]^{-1}=[1/x_+,1/x_-]$. These are inclusion
operations over the reals [7]; they require no floating-point rounding.

Here is an explicit evaluation prescription and its rational inputs.
For each interval $[l,u]$ in (15.3), set

$$
\begin{aligned}
j_l&=1/8+8l(1-u),&j_u&=1/8+8u(1-l),\\
n_l&=j_l+l,&n_u&=j_u+u.
\end{aligned}
\tag{17.1}
$$

The exact numerators of these endpoints, over the common denominator
$10^{12}$, are

| Root interval | $10^{12}j_l$ | $10^{12}j_u$ | $10^{12}n_l$ | $10^{12}n_u$ |
| --- | ---: | ---: | ---: | ---: |
| $r_-$ | $1058118247680$ | $1058126247680$ | $1192933247680$ | $1192942247680$ |
| $r_+$ | $829271199600$ | $829279199600$ | $1731720199600$ | $1731729199600$ |

For $k=5,6,7$, respectively, use the constant triples

$$
(c_k,\alpha_k,\beta_k)=
(196/9,15,10),\quad(50,36,20),\quad(284/3,70,35)
\tag{17.2}
$$

and define

$$
q_{kl}=c_k-\alpha_k/j_l-\beta_k/n_l,\qquad
q_{ku}=c_k-\alpha_k/j_u-\beta_k/n_u.
\tag{17.3}
$$

These enclose the unsimplified expressions (16.4), so the interval
calculation does not impose an independent root relation in place of
the original gain. Both endpoints are negative for all three $k$ in
both rows. In the following prescription, subscripts $l,u$ always denote
the lower and upper endpoint of the indicated interval:

$$
\begin{aligned}
D_l&=1+(n_u+5/4)q_{5l},&D_u&=1+(n_l+5/4)q_{5u},\\
L_l&=9/8+2j_l+4l,&L_u&=9/8+2j_u+4u,\\
F_l&=1+(5/2+n_u)q_{6l},&F_u&=1+(5/2+n_l)q_{6u},\\
G_l&=1+L_uq_{7l},&G_u&=1+L_lq_{7u}.
\end{aligned}
\tag{17.4}
$$

All of $D_l,D_u,F_l,F_u,G_l,G_u$ are negative by direct rational
comparison. Accordingly the response intervals are exactly prescribed
by the following expressions before outward decimal enclosure:

$$
\begin{aligned}
A_5&\in[D_l,D_u],\\
V_0&\in[24(7/2+n_l),24(7/2+n_u)],\\
V_1&\in[F_u/D_l,F_l/D_u],\\
A_0&\in[24+(384/5)L_l,24+(384/5)L_u],\\
A_1&\in[G_u/D_l,G_l/D_u].
\end{aligned}
\tag{17.5}
$$

The results are contained strictly in these rational open intervals:

| Quantity | At $r_-$ | At $r_+$ |
| --- | --- | --- |
| $q_r(5)$ | $(-0.781031,-0.780859)$ | $(-2.085000,-2.084794)$ |
| $A_5$ | $(-0.908012,-0.907588)$ | $(-5.216903,-5.216273)$ |
| $q_r(6)$ | $(-0.788060,-0.787676)$ | $(-4.960823,-4.960343)$ |
| $q_r(7)$ | $(-0.827956,-0.827234)$ | $(-9.955920,-9.955000)$ |
| $V_0$ | $(112.630397,112.630614)$ | $(125.561284,125.561501)$ |
| $V_1$ | $(2.102214,2.104764)$ | $(3.831926,3.832786)$ |
| $A_0$ | $(314.342130,314.343667)$ | $(515.008389,515.009926)$ |
| $A_1$ | $(2.342872,2.346990)$ | $(12.008214,12.010827)$ |

For example the lower endpoint $q_{5l}$ for the first row is exactly

$$
\frac{196}{9}
-\frac{15\cdot10^{12}}{1058118247680}
-\frac{10\cdot10^{12}}{1192933247680}.
\tag{17.6}
$$

It exceeds $-781031/10^6$. The upper endpoint uses the two upper
numerators in that row and is below $-780859/10^6$. Every table entry
has the same finite rational comparison form (17.1)–(17.5); all
denominator signs have been specified. Thus the prescription supplies
exact endpoint inequalities, not samples at decimal root estimates.

In particular $V_1(r_-)-V_1(r_+)<0$. There is exactly one possible
fifth reading at which the two singular worlds have the same sixth
reading. Define it algebraically by

$$
\delta_s=\frac{V_0(r_+)-V_0(r_-)}{V_1(r_-)-V_1(r_+)},\qquad
p_s=24+\delta_s,\qquad
v_s=V_0(r_-)+V_1(r_-)\delta_s.
\tag{17.7}
$$

Here are explicit bounds obtained using only the displayed six-decimal
response intervals. Their difference intervals give

$$
\begin{aligned}
V_0(r_+)-V_0(r_-)&\in(12.930670,12.931104),\\
V_1(r_-)-V_1(r_+)&\in(-1.730572,-1.727162),\\
A_0(r_-)-A_0(r_+)&\in(-200.667796,-200.664722),\\
A_1(r_-)-A_1(r_+)&\in(-9.667955,-9.661224).
\end{aligned}
\tag{17.8}
$$

Exact interval division yields

$$
-\frac{12931104}{1727162}<\delta_s<
-\frac{12930670}{1730572},\qquad
16.513091<p_s<16.528095.
\tag{17.9}
$$

For instance the following four rational endpoint expressions give,
respectively, lower and upper bounds on $v_s$ and on the terminal-J
difference $\Delta a_s=a(W_{r_-}(p_s))-a(W_{r_+}(p_s))$:

$$
\begin{aligned}
v_l&=\frac{112630397}{10^6}
      -\frac{2104764}{10^6}\frac{12931104}{1727162},\\
v_u&=\frac{112630614}{10^6}
      -\frac{2102214}{10^6}\frac{12930670}{1730572},\\
a_l&=-\frac{200667796}{10^6}
      +\frac{9661224}{10^6}\frac{12930670}{1730572},\\
a_u&=-\frac{200664722}{10^6}
      +\frac{9667955}{10^6}\frac{12931104}{1727162}.
\end{aligned}
\tag{17.10}
$$

Multiplication by positive denominators verifies

$$
\begin{aligned}
96.872221&<v_l<v_s<v_u<96.923071,\\
-128.480046&<a_l<\Delta a_s<a_u<-128.281626<0.
\end{aligned}
\tag{17.11}
$$

This proves strict separation using exact rational enclosures and the
isolated algebraic roots, without relying on any unprinted numerical
root or computational certificate.

## 18. Singular acquired multiplicity and the independent-pair boundary

**Theorem 18.1.** In the full original model the singular worlds over
each fifth reading $p$ are precisely $W_{r_-}(p)$ and $W_{r_+}(p)$ of
(16.8). They lie in the same acquired child if and only if
$(p,v)=(p_s,v_s)$ of (17.7). At that point there are exactly two
singular worlds and their terminal-J readings differ. At every other
$(p,v)$ the entire child contains at most one singular world.
Consequently no distinct pair of singular worlds in any entire
$C(p,v)$ has equal terminal-J readings, for any real $p,v$.

**Proof.** Equations (14.2)–(14.5) and the exact root count in
Section 15 exhaust the singular sources. The strict source inequalities
hold at both roots. Formula (16.7) makes the fifth-response lift unique
and existent for every $p$ at each source. The source matrices differ,
so the two complete worlds are distinct. Their sixth responses are
the two affine functions (16.10) with different slopes, and equality
is equivalent to (17.7). Thus both actual worlds belong to $C(p_s,v_s)$,
and there is no other singular world there. Finally (17.11) excludes
equality of their terminal-J readings. Two worlds at the same singular
source and fifth reading already coincide by (16.8). This proves the
claimed multiplicities and exclusion. $\square$

Since $16<p_s<17$, every negative-base child contains at most one
singular world even before terminal-J readings are compared. At a
negative base, a distinct J pair that uses a singular world must
therefore use a nonsingular companion. This companion is not required
to have the same width or gain direction. No exclusion of a mixed
singular/nonsingular pair at any positive width follows from the
singular-pair theorem. Nor does it exclude pairs of two nonsingular
worlds below width one, or a low-width regular world paired with one
above width one. The restrictions of Sections 6 and 12 retain their
stated separate scopes.

The original question is still exactly (12.1): some real $p\ne24,v$
and independently distinct worlds $W_0\ne W_1$, $W_2\ne W_3$ in the
one entire $C(p,v)$, with $a(W_0)=a(W_1)$ and $m(W_2)=m(W_3)$.
The pairs may differ, coincide or overlap, and their two common
terminal values are independent. Theorem 18.1 supplies neither those
pairs nor a global obstruction to them. It establishes no terminal-M
collision on any J locus. Singular worlds, zero drift, lower-degree
gains, repeated gain roots and sampled gain zeros remain in the
original model wherever its prescribed rows permit them. There is no
reset, copy, source port, shifted clock or extra acquisition.

## 19. Mathematical attribution and scope of the ordinary result

The parent equation and whole-gain reconstruction are the existing
chart (2.4)–(2.5), in the zero-safe form of *FIB common-parent geometry
and two exact mixed children*, Theorem 2.1 and Theorem 4.2. Fixed-node
interpolation uses [1]. The singular-source polynomial and its isolated
roots are the same parent objects; Sections 14–16 give the explicit
correspondence to the literal current acquisition and terminal J.
Sturm root counting [6] is used with the fully specified positive
scalings, divisions and endpoint integers in Section 15. Rational
interval inclusion [7] is used with the endpoint prescription and
explicit final inequalities in Section 17. The two singular acquired
lines, their unique intersection and terminal-J separation yield
Theorem 18.1. These are ordinary mathematical conclusions, with no
formal-kernel or literature-priority claim.

[6] Saugata Basu, Richard Pollack and Marie-Françoise Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Springer,
2006, univariate Sturm root counting.
[DOI](https://doi.org/10.1007/3-540-33099-2).

[7] Ramon E. Moore, R. Baker Kearfott and Michael J. Cloud,
*Introduction to Interval Analysis*, SIAM, 2009, interval arithmetic
and the inclusion property of interval evaluation.

## 追加锚（本行以下为增补区）

## 20. The positive-sheet chart and its correspondence with the existing chart

The complete worlds, strict source domain, chronological left action word,
clock readings and entire children $C(p,v)$ remain exactly those of Sections
1--19. In particular, one world has one fixed drift and one entire nonzero
real polynomial gain of degree at most three. The following notation makes the
positive calculation explicit while identifying every reused numerator with the
existing chart of Sections 2 and 7.

Put
$$
 j=b+r(1-r)/b,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\quad e=d-24,
$$
and put
$$
\mathcal J=b^2+r(1-r),\qquad \mathcal N=\mathcal J+rb,\qquad
 S=(8b-1)(2+5b),
$$
so that $j=\mathcal J/b$ and $n=\mathcal N/b$. Define
$$
\Lambda=1+6/T+1/U-4/j-4/n,
$$
and
$$
 D=5\{(b^2+8b+4)\mathcal J\mathcal N
          -2TUb(\mathcal J+\mathcal N)\}.
$$
These are the same $D,\Lambda,\mathcal J,\mathcal N$ as in (2.1),
(2.5), and (14.2)--(14.5). The first four rows force
$$
(g(0),g(1),g(2),g(3))
 =(-24-e,-e/j,(27/5-e)/T,-e/n).
\tag{20.1}
$$
The fifth row is equivalent, without dividing by $e$ or $D$, to
$$
 e\Lambda=-\frac{6S}{5TU},\qquad
 \Lambda=\frac{2D}{5TU\mathcal J\mathcal N},\qquad
 eD=-3S\mathcal J\mathcal N.\tag{20.2}
$$
Thus $D=0$ can occur for an actual source only when $S=0$, hence only at
$b=1/8$; the additional condition is then precisely the singular equation
$\Lambda=0$ treated completely in Sections 14--18. Its free drift branch is
therefore retained. No gain value, leading coefficient, root difference, or
drift has been cancelled.

Let
$$
\ell_i(s)=\prod_{\substack{0\le k\le3\\k\ne i}}\frac{s-k}{i-k}
$$
and define the integer polynomials
$$
\begin{aligned}
 C_0&=-24D+3S\mathcal J\mathcal N,&C_1&=3S\mathcal N b,\\
 C_2&=3(49b+34)\mathcal J\mathcal N-54Ub(\mathcal J+\mathcal N),&
 C_3&=3S\mathcal J b,\\
 B_5&=-4C_0+15C_1-20C_2+10C_3,\\
 B_6&=-10C_0+36C_1-45C_2+20C_3,\\
 B_7&=-20C_0+70C_1-84C_2+35C_3,
 \end{aligned}\tag{20.3}
$$
and $H=bD$. The regular parent lift is
$$
 d=-C_0/D,\qquad
 g(s)=D^{-1}\sum_{i=0}^3C_i\ell_i(s).
\tag{20.4}
$$
The exact row identities used by this lift are
$$
\begin{aligned}
-bC_0+\mathcal JC_1&=24bD,\\
-C_0+TC_2&=(147/5)D,\\
-bC_0+\mathcal NC_3&=24bD,\\
-C_0+U(-C_0+4C_1-6C_2+4C_3)&=18D.
\end{aligned}\tag{20.5}
$$
The zero-clock identity is $-C_0+C_0=0$. Since the four-node
interpolation weights at clocks five, six and seven are respectively
$(-4,15,-20,10)$, $(-10,36,-45,20)$ and $(-20,70,-84,35)$, the values
$Dg(5),Dg(6),Dg(7)$ are $B_5,B_6,B_7$. Thus (20.1)--(20.4) verify every
prescribed row directly and prove the regular lift without a hidden
response coordinate.

The preserved chart calls the next two numerators $N_p,N_v$ and the
terminal-J numerator $N_a$:
$$
\begin{aligned}
 N_p&=-bC_0+(bU+\mathcal N)B_5,\\
 N_v&=-bC_0+(2bU+\mathcal N)B_6,\\
 N_a&=-bC_0+(bT+2\mathcal J+4br)B_7.
\end{aligned}\tag{20.6}
$$
The preserved chart writes $G_7$ for the same clock-seven interpolation
combination; thus $B_7=G_7$ by (20.3) and (7.1). The positive-source
notation $P_p,P_v,P_a$ is exactly the alias
$$
(P_p,P_v,P_a)=(N_p,N_v,N_a),
$$
with no new redefinition. For the other terminal action define only the
corresponding response numerator
$$
 P_m=N_m:=-bC_0+(3bU+2\mathcal N)B_7.\tag{20.7}
$$
The literal products needed at clock seven are
$$
Q_5=\begin{pmatrix}2&1\\3&1\end{pmatrix},\quad
Q_6=\begin{pmatrix}3&1\\5&2\end{pmatrix},\quad
JQ_6=\begin{pmatrix}5&2\\3&1\end{pmatrix},\quad
MQ_6=\begin{pmatrix}5&2\\8&3\end{pmatrix}.
$$
Their traces against $P$ are $U+n$, $2U+n$, $T+2j+4r$ and $3U+2n$,
respectively. Hence the two terminal trace factors in (20.6)--(20.7) are
literal left products, and, whenever $D\ne0$,
$$
(p,v,a,m)=(P_p,P_v,P_a,P_m)/H.\tag{20.8}
$$
The interpolation weights in (20.3) are respectively those at clocks five,
six and seven. The polynomial identities in (2.7), together with (20.1),
prove the prescribed rows, and uniqueness of the four samples proves
uniqueness of the complete gain and drift at a regular source. Lower degree
gains, sampled zeros, repeated roots and zero drift remain included.

## 21. Exact positive-strip certificates

For a polynomial $F(r,b)$ of $r$-degree $n$ and $b$-degree $m$, write
$$
 F(r,3/4+u)=\sum_{k=0}^m\sum_{i=0}^n a_{ki}r^iu^k,\qquad
 c_{kj}(F)=\sum_{i=0}^j\frac{\binom ji}{\binom ni}a_{ki}.
$$
Then the exact Bernstein conversion is
$$
 F(r,3/4+u)=\sum_{k=0}^m u^k
 \sum_{j=0}^n c_{kj}(F)\binom njr^j(1-r)^{n-j}.
\tag{21.1}
$$
The inner weights are nonnegative and sum to one for $0\le r\le1$.

Define, using the aliases (20.6),
$$
\begin{aligned}
 \mathscr B&=(P_p)_bH-P_pH_b,\\
 \mathscr K&=\{(P_p)_r(P_a)_b-(P_p)_b(P_a)_r\}H\\
 &\quad-\{(P_p)_rP_a-P_p(P_a)_r\}H_b
 +\{(P_p)_bP_a-P_p(P_a)_b\}H_r.
\end{aligned}\tag{21.2}
$$
Their degrees in $(r,b)$ are $(10,12)$ and $(15,18)$; $P_p$ has degrees
$(6,7)$. Substitution of the displayed integer polynomials gives the
following exact row extrema. A listed maximum for $P_p$ is negative, and a
listed minimum for either derivative numerator is positive.

$$
\begin{array}{c|r|r|r}
 k&\max_j c_{kj}(P_p)&\min_j c_{kj}(\mathscr B)&\min_j c_{kj}(\mathscr K)\\ \hline
0&-512631/1024&455741690697/58720256&61954938577212579/3758096384\\
1&-1949589/512&361644750129/3670016&74588951490183225/234881024\\
2&-357721/32&1041884523313/1835008&674899196461312509/234881024\\
3&-517859/32&127071800897/65536&8340467566855923/524288\\
4&-12336&141781839535/32768&32125431211803477/524288\\
5&-11049/2&13810343235/2048&5621654643785235/32768\\
6&-1500&11400085841/1536&12090582746511435/32768\\
7&-216&186634661/32&1285263013924755/2048\\
8&\text{--}&408957381/128&3514403850475455/4096\\
9&\text{--}&9318405/8&121786481138445/128\\
10&\text{--}&1032795/4&219753083040525/256\\
11&\text{--}&28650&5031618926805/8\\
12&\text{--}&750&2975563894185/8\\
13&\text{--}&\text{--}&175630926690\\
14&\text{--}&\text{--}&65076080670\\
15&\text{--}&\text{--}&18366965280\\
16&\text{--}&\text{--}&3736317960\\
17&\text{--}&\text{--}&488908800\\
18&\text{--}&\text{--}&30729600
\end{array}\tag{21.3}
$$
These are finite rational sums from (21.1), so they are exact coefficient
certificates rather than sampled evaluations. Consequently
$$
 P_p<0,\qquad \mathscr B>0,\qquad \mathscr K>0
 \quad(0\le r\le1, b\ge3/4).\tag{21.4}
$$

For the remaining denominator sign on $3/4\le b\le2$, put
$b=3/4+5x/4$. The tensor Bernstein coefficients of $D$ are
$$
 q_{j\ell}=\sum_{i=0}^j\sum_{k=0}^{\ell}
 \frac{\binom ji\binom\ell k}{\binom4i\binom6k}d_{ik},
$$
where $D(r,3/4+5x/4)=\sum d_{ik}r^ix^k$. Direct integer expansion gives
$$
 \min_{j,\ell}q_{j\ell}=-480,\qquad
 \max_{j,\ell}q_{j\ell}=-98735/12288<0.
\tag{21.5}
$$
The tensor basis is nonnegative and sums to one, hence $D<0$ on this
rectangle. This also records the exact two-dimensional coefficient extrema.

The quotient rule gives, wherever $H\ne0$,
$$
 p_b=\mathscr B/H^2,\qquad
 p_ra_b-p_ba_r=\mathscr K/H^3.\tag{21.6}
$$
On the positive regular sheet with $b\ge3/4$, where (21.4) applies and $H<0$,
we have $p_b>0$ and $p_ra_b-p_ba_r<0$.

The cutoff $p_0=1587/25$ is exact. For the explicit specialization
$F_{3/4}(r):=(P_p-p_0H)(r,3/4)$, the degree-six Bernstein vectors after
$r=x/2$ and $r=(1+x)/2$, respectively, are
$$
\begin{aligned}
 &(6579711/81920,2539737/40960,2904477/81920,3848199/204800,\\
 &\qquad6025359/409600,890637/40960,3112737/81920),\\
 &(3112737/81920,111105/2048,32654619/409600,11522199/102400,\\
 &\qquad61574937/409600,198819/1024,20037699/81920).
\end{aligned}\tag{21.7}
$$
Every entry is positive, so $F_{3/4}(r)>0$ for $0<r<1$. At $b=1$,
exact factorization gives
$$
(25P_p-1587H)(r,1)=105(1-r)
(160r^5-640r^4+651r^3+63r^2-434r-178).\tag{21.8}
$$
Define the quotient carrying the full scale in (21.8) by
$$
Q_+(r):=\frac{(25P_p-1587H)(r,1)}{1-r}
=105(160r^5-640r^4+651r^3+63r^2-434r-178).
$$
Its degree-five Bernstein vector is
$$
(-18690,-27804,-72513/2,-37212,-37275,-39690),
\tag{21.9}
$$
so $Q_+(r)<0$ and the right side of (21.8) is negative for $r<1$. Because $H<0$ on
$3/4\le b\le2$, (21.7)--(21.9) imply
$$
 p(r,3/4)<p_0<p(r,1),\qquad0<r<1.\tag{21.10}
$$

## 22. The positive denominator boundary and the global terminal-J order

Let $\beta$ be the unique positive root of $b^3-8b-4=0$. Descartes' rule
and the intermediate value theorem give $3<\beta<31/10$. For fixed
$0\le r\le1$, write
$$
D(r,2+u)=\sum_{k=0}^6d_k(r)u^k.
$$
The degree-four Bernstein extrema of the coefficient polynomials are
$$
\begin{array}{c|rr}
k&\min_j d_{kj}&\max_j d_{kj}\\ \hline
0&-480&-60\\
1&-560&335\\
2&120&930\\
3&460&810\\
4&260&330\\
5&60&65\\
6&5&5
\end{array}\tag{22.1}
$$
Thus $d_0<0$, $d_k>0$ for $k\ge2$, while $d_1$ may have either sign.
After deleting a zero $d_1$, the coefficient sequence has exactly one sign
change. Descartes' rule bounds positive roots, with multiplicity, by one.
Since $D(r,2)<0$ and the leading coefficient is positive, there is exactly
one positive root $u=\delta(r)-2$. It is simple, and the sign is
$$
 D(r,b)<0\ (3/4\le b<\delta(r)),\qquad
 D(r,b)>0\ (b>\delta(r)),\qquad \delta(r)>2.\tag{22.2}
$$
The implicit-function theorem and uniqueness patch the local root graphs into
one real-analytic function on the closed auxiliary interval $0\le r\le1$.

At $b=\beta$,
$$
1+6/T+1/U-8/b=\frac{2(b^3-8b-4)}{bTU}=0.
$$
For $0<r<1$, $j>b$ and $n>b$, so $\Lambda(r,\beta)>0$ and hence
$D(r,\beta)>0$. At $r=0$, the exact factorization
$$
D(0,b)=5b^3(b^3-8b-4)\tag{22.3}
$$
shows $\delta(0)=\beta$; the strict-source domain is $0<r<1$.
For $0<r<1$, therefore, $2<\delta(r)<\beta$. Together with
(21.4), this proves that every actual world with $p>0$ has $b<\beta$:
widths below $3/4$ already satisfy this, while on $b\ge3/4$ positivity is
exactly $D<0$.

For each fixed $r\in(0,1)$, the positive regular sources on the strip
$b\ge3/4$ are precisely $3/4\le b<\delta(r)$ (with the possible
singular width $1/8$ already separated). Since $p_b>0$, $p(r,b)\to+\infty$ as
$b\uparrow\delta(r)$ because $P_p<0$ and $H\to0^-$. The cutoff
inequality (21.10) now gives, for every $p\ge p_0$, a unique point
$$
3/4<b_p(r)<\delta(r),\qquad p(r,b_p(r))=p.\tag{22.4}
$$
These points form one analytic graph over the connected interval
$0<r<1$. Along it,
$$
\frac{d}{dr}a(r,b_p(r))
 =a_r-a_b\frac{p_r}{p_b}
 =-\frac{\mathscr K}{H\mathscr B}>0.\tag{22.5}
$$
The mean value theorem therefore makes $a$ strictly increasing on the whole
graph. Two points with the same $(p,a)$ have the same $r$, then the same
$b$, and finally the same complete world by (20.4).

If $0<p\le p_0$, a world with $b\ge1$ would have
$p\ge p(r,1)>p_0$ by (21.10) and (21.6), a contradiction. If $p>p_0$,
(22.4)--(22.5) give uniqueness among all $b\ge1$. The acquired value $v$
only selects a subset of the fixed-$p$ graph, so the same conclusion holds in
every entire child $C(p,v)$.

**Theorem 22.1 (Positive-base terminal-J restriction).**
Every actual parent with $p>0$ has $b<\beta$, and strict widths can approach
$\beta$ only as an endpoint is approached. For $0<p\le p_0$, every world in
every $C(p,v)$ has $b<1$. For each fixed $p>0$ and real $z$, there is at most
one complete world with $p(W)=p$, $a(W)=z$ and $b(W)\ge1$; for
$p\ge p_0$, $b\ge3/4$ already suffices. Thus a positive-base terminal-J
collision has a member below one, and at bases at least $p_0$ it has a member
below $3/4$.

The width supremum is sharp in the strict domain. Choose $r_k=1/k$ and
$b_k=\delta(r_k)-1/k$ for sufficiently large $k$. Then
$b_k\to\beta$, while $b_k<\delta(r_k)$ gives $p>0$ and (21.10) gives
$p>p_0>24$. No endpoint source is an actual world. This proves both the
sharpness and the endpoint qualification.

## 23. Singular synthesis and the combined ordinary restriction

The singular classification and its two exact source roots, affine acquired
responses, unique fifth-reading lifts, and terminal-J separation are exactly
those proved in Sections 14--18. In particular, the singular width is
$b=1/8$, the two source roots lie in the displayed disjoint rational
intervals, and the two singular worlds can share an acquired child only at
$(p_s,v_s)$, where $16<p_s<17$ and their terminal-J readings are strictly
separated. The singular branch is below the positive certificate strip and
is not silently discarded by Theorem 22.1. Theorem 18.1 also makes no claim
about terminal-M injectivity.

Combining the preserved negative-sheet theorem with Theorem 22.1 gives the
following scoped ordinary corollary. At every negative base $p<0$, any
terminal-J collision of distinct complete worlds contains a member with
$b<1$ by Corollary 12.1. At every positive base $p>0$, the same conclusion
holds by Theorem 22.1; if $p\ge p_0$, one member has $b<3/4$. These statements
are about the J pair alone and do not constrain the independently selected M
pair. The case $p=0$ is not included because no positive- or negative-sheet
argument above classifies it.

The corollary does not settle the original independent-pair assertion. The
original target still asks for one entire $C(p,v)$ with $p\ne24$ and
independently distinct pairs $W_0\ne W_1$ and $W_2\ne W_3$ satisfying
$$
 a(W_0)=a(W_1),\qquad m(W_2)=m(W_3),
$$
with overlap permitted and the two common terminal values independent. The
positive and negative restrictions leave mixed-width J pairs, low-width
regular and singular sources, and all terminal-M possibilities open. No
common width, common pair, common answer, reset, copy, source port or shifted
clock has been introduced.

## 24. Attribution, exact scope, and unresolved boundary

The complete parent equation, zero-safe singular branch, literal matrix
products, and regular polynomial chart are reused from *FIB common-parent
geometry and two exact mixed children*, Theorems 2.1, 4.1--4.2 and 29.2,
and from the preserved negative-sheet source, Sections 2, 7 and 14--19.
The present addition contributes the positive-strip Bernstein certificates,
the exact cutoff $1587/25$, the unique denominator boundary below the sharp
root $\beta$, and the connected global positive-sheet terminal-J order.
The Bernstein conversion, Descartes rule, implicit-function theorem and mean
value theorem are the classical arguments cited in the preserved volume;
interval inclusion and Sturm separation for the singular branch are those
already cited there. All polynomial identities and coefficient extrema used
here are displayed as exact rational expressions.

These are ordinary mathematical conclusions. They do not provide a Lean
proof, a priority claim, a terminal-M injectivity theorem, or a global
certificate for the original independent-pair target. In particular, no
statement here adds the missing $p=0$ case, and no statement claims that two
independently distinct J/M pairs do or do not exist. The original strict
world, nonzero gain, fixed drift, all degenerate gain cases, and the literal
clocks remain unchanged.

## 25. Exact scope

A complete world is $W=(P,g,d)$, where

$$
P=P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad d\in\mathbb R,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3.
$$

The matrices $J=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ and
$M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$ act on the left.
The chronological acquired word is $J,M,J,M,M,M$, and the readings at
clocks zero through six are $0,24,147/5,24,18,p,v$.
The reading at clock $i$ is $d+g(i)\operatorname{tr}(Q_iP)$, with
$Q_0=I$ and $Q_i=E_iQ_{i-1}$. The terminal alternatives $J,M$ occur
at clock seven. Write their readings as $a(W),m(W)$.
The entire child $C(p,v)$ contains all complete worlds with that record.

The original target remains the existence of some $p\ne24,v$ with
$W_0\ne W_1$ and $W_2\ne W_3$ in one entire $C(p,v)$ such that
$a(W_0)=a(W_1)$ and $m(W_2)=m(W_3)$. The two pairs may overlap,
and their common terminal answers are independent.
This source studies the allowed sector $p=0$ only.

**Theorem 25.1.** All complete parent worlds whose fifth acquired
reading is zero form exactly two real analytic arcs
$W_-(r),W_+(r)$, each parametrized by the whole interval $0<r<1$.
Their source widths are the two simple positive roots $b_-(r),b_+(r)$
of the explicit polynomial $F(r,b)$ below, and satisfy

$$
0<b_-(r)<\frac{r(1-r)}2<b_+(r)<\frac12.
$$

Every point of both arcs is an actual complete world. Their whole
nonzero gains and fixed drifts have the zero-safe rational reconstruction
in Section 29. In every such world $d>24$ and $g(5)<0$.
The lower arc has no singular parent source. The upper arc contains
exactly the two singular parent sources specified in Section 28, with
their unique complete zero-base lifts.

This is an algebraic reduction of the entire zero sector, including its
parent singularity. It supplies no terminal collision pair and no
exclusion of terminal collision pairs.



## 26. The whole parent and the zero-base consistency identity

Put

$$
\begin{gathered}
T=1+b,\quad U=1+2b,\quad
j=b+r(1-r)/b,\quad n=j+r,\quad e=d-24,\\
\mathcal J=b^2+r(1-r),\quad\mathcal N=\mathcal J+rb,\quad
S=(8b-1)(2+5b),\\
\Lambda=1+6/T+1/U-4/j-4/n,\qquad
R=-6S/(5TU),\\
D=5\{(b^2+8b+4)\mathcal J\mathcal N
              -2TUb(\mathcal J+\mathcal N)\}.
\end{gathered} \tag{26.1}
$$

All $T,U,j,n,\mathcal J,\mathcal N$ are positive on the strict source
domain. Let $\ell_i$ be the degree-three Lagrange basis at $0,1,2,3$:

$$
\ell_i(s)=\prod_{0\le k\le3,\ k\ne i}\frac{s-k}{i-k}.
$$

The first four rows fix the entire polynomial by the four samples

$$
z_0=-24-e,\quad z_1=-e/j,\quad
z_2=(27/5-e)/T,\quad z_3=-e/n,\qquad
g(s)=\sum_{i=0}^3 z_i\ell_i(s). \tag{26.2}
$$

The row at four is equivalent to $e\Lambda=R$. This is the
zero-safe parent converse: every strict source and real $e$ satisfying
that equation gives exactly one complete parent world through (26.2).
Indeed the fourth-difference identity gives
$g(4)=-z_0+4z_1-6z_2+4z_3$, and substitution in
$24+e+Ug(4)=18$ gives precisely this equation.
A zero entire gain would force the unequal readings at zero and one
to coincide, so the constructed gain is always nonzero.

The clock-five interpolation weights are $(-4,15,-20,10)$. Hence put

$$
\begin{aligned}
g^0_5&=96-108/T,& q_5&=4-15/j+20/T-10/n,\\
A_5&=1+(U+n)q_5,& p_c&=24+(U+n)g^0_5.
\end{aligned} \tag{26.3}
$$

The literal fifth reading is $p_c+eA_5$.
Consequently a complete zero-base world must satisfy the two scalar
equations

$$
e\Lambda=R,\qquad eA_5=-p_c. \tag{26.4}
$$

Define the following integer polynomial, listed by increasing powers
of $b$:

$$
F(r,b)=\sum_{k=0}^7 c_k(r)b^k, \tag{26.5}
$$

where

$$
\begin{aligned}
c_0&=32r^3(1-r)^3,\\
c_1&=32r^2(r-1)^2(2r+1)(4r-5),\\
c_2&=-2r(r-1)(256r^3-140r^2-185r+65),\\
c_3&=r(-744r^3+1837r^2-1408r+375),\\
c_4&=1216r^3-1623r^2+639r+130,\\
c_5&=456r^2-479r+465,\\
c_6&=746-624r,\qquad c_7=72.
\end{aligned} \tag{26.6}
$$

Direct expansion gives the exact identity

$$
p_c\Lambda+RA_5=-\frac{6}{5bTU\mathcal J\mathcal N}F(r,b),\qquad
\Lambda=\frac{2D}{5TU\mathcal J\mathcal N}. \tag{26.7}
$$

Thus every complete zero-base source lies on $F=0$. Neither identity
divides by $e,D$, a gain sample or a gain coefficient.



## 27. Exactly two simple positive roots at every diagonal coordinate

For a polynomial $f(x)=\sum_{i=0}^n f_i x^i$, its degree-$n$
Bernstein coefficients on $[0,1]$ are

$$
\mathcal B_j(f)=\sum_{i=0}^j
       \frac{\binom ji}{\binom ni}f_i,\qquad 0\le j\le n.
$$

The Bernstein basis is nonnegative and sums to one. Positive
coefficients therefore prove strict positivity on the whole interval.

For $c_3/r$, the degree-three coefficient vectors after substituting
$r=x/2$ and $r=(1+x)/2$ are respectively

$$
(375,421/3,235/4,149/4),\qquad
(149/4,63/4,163/3,60).
$$

Thus $c_3>0$ for $0<r<1$. The degree-three vector for $c_4$ is
$(130,343,15,362)$, the degree-two vector for $c_5$ is
$(465,451/2,442)$, and the degree-one vector for $c_6$ is
$(746,122)$. In particular all $c_3,\ldots,c_7$ are positive.
Also $c_0>0,c_1<0$, while $c_2$ needs no sign restriction.
In descending powers the nonzero coefficient signs therefore have
exactly two changes, whether $c_2$ is positive, negative or zero.
Descartes' rule bounds the number of positive roots, counted with
multiplicity, by two.

Write $t=r(1-r)/2$. Exact substitution gives

$$
\frac{F(r,t)}{r^3(1-r)^3}
=\frac1{32}\bigl(18r^8+240r^7-745r^6-1840r^5
 +3168r^4+5884r^3-2293r^2-4272r-496\bigr). \tag{27.1}
$$

The complete degree-eight Bernstein vector of this quotient is

$$
\left(-\frac{31}2,-\frac{515}{16},-\frac{46085}{896},
-\frac{62681}{896},-\frac{186047}{2240},-\frac{38371}{448},
-\frac{16603}{224},-\frac{3077}{64},-\frac{21}2\right).
$$

Hence $F(r,t)<0$ on $0<r<1$. On the other hand the degree-six
Bernstein vector of $F(r,1/2)$ is

$$
(279/8,3241/64,5631/160,3117/320,967/80,2089/64,1485/32),
$$

so $F(r,1/2)>0$. Since $F(r,0)>0$ and $0<t\le1/8<1/2$, the
intermediate value theorem gives one positive root in $(0,t)$ and
one in $(t,1/2)$. They exhaust the Descartes bound and both are simple.
There are no other positive roots at any width.

The analytic implicit-function theorem applies since $F_b\ne0$ at
both roots. The two ordering intervals label the roots uniquely, so
the local analytic graphs patch into $b_-,b_+$ on the connected
interval $(0,1)$. This proves the root assertions of Theorem 25.1.



## 28. All parent-denominator zeros on these graphs

There is a potential logical gap between roots of a regular-chart
numerator and actual sources. The following explicit resultant
identity removes it in the entire zero sector. The resultant here is
in $r$; all inputs are the displayed integer polynomials.

$$
\operatorname{Res}_r(F,D)=62500b^{14}(2b+1)^2(5b+2)^4(8b-1)^4Q(b),
\tag{28.1}
$$

where

$$
\begin{aligned}
Q(b)={}&27b^{16}+198b^{15}-24294b^{14}-576939b^{13}
 -5180250b^{12}-22502243b^{11}\\
&-56647044b^{10}-93879326b^9-112237206b^8
 -103197064b^7-77097576b^6\\
&-49669216b^5-28167328b^4-13027456b^3
 -4266880b^2-834560b-71680.
\end{aligned} \tag{28.2}
$$

Identity (28.1) is the Sylvester determinant identity and can be
verified by polynomial expansion. For $0<b\le1/2$,
$27b^2+198b-24294<0$. Grouping the first three terms of $Q$
therefore leaves only strictly negative summands, so $Q(b)<0$.
A common finite root in $r$ forces the resultant to vanish.
It follows that every point on either positive-width graph with
$D=0$ has $b=1/8$.

At that width the exact identities are

$$
\begin{gathered}
\Phi(r)=438272r^4-931328r^3+540800r^2-50728r-853,\\
D(r,1/8)=15\Phi(r)/262144,\qquad
F(r,1/8)=-15\Phi(r)/262144. \tag{28.3}
\end{gathered}
$$

There are exactly two strict roots $r_-,r_+$ of $\Phi$, with

$$
134815/10^6<r_-<134816/10^6,\qquad
902449/10^6<r_+<902450/10^6. \tag{28.4}
$$

For completeness, a positive-scaled Sturm chain is

$$
\begin{aligned}
S_0&=\Phi,\quad S_1=219136r^3-349248r^2+135200r-6341,\\
S_2&=1610816r^2-1689664r+121445,\\
S_3&=64839740164r-26327821511,\\
S_4&=78580316788659208197744775.
\end{aligned}
$$

Here $S_0'=8S_1$ and the successive negative remainders have the
positive multipliers $1/16$, $64/633478561$ and
$1/262761994033439671681$. The signs at
$0,134815/10^6,134816/10^6,902449/10^6,902450/10^6,1$ are
respectively $--+-+$, $-+--+$, $++--+$, $+--++$, $---++$,
and $--+++$. Their variation counts are $3,3,2,2,1,1$.
Sturm's theorem gives exactly the two roots (28.4).

Since $r_\pm(1-r_\pm)/2<1/8$, both singular points lie on the
upper graph. There is no denominator zero on the lower graph.
At either singular point,

$$
T=9/8,\quad U=5/4,\quad
1/j+1/n=107/60,\quad n>j>0.
$$

The latter relation implies $1/j>107/120$ and $n>120/107$.
Using the same $q_5$ of (26.3), one obtains

$$
q_5=71/18-5/j<-37/72,\qquad
A_5<1-(120/107+5/4)37/72=-6739/30816<0. \tag{28.5}
$$

Consequently $(\Lambda,A_5)$ is never $(0,0)$ on either graph:
away from these two points $\Lambda\ne0$, and at both points (28.5)
applies. In particular no extraneous $D=0$ numerator root has been
silently promoted to an actual parent.



## 29. Zero-safe whole-world converse and the drift sign

On either graph define

$$
Z=\Lambda^2+A_5^2>0,\qquad
e=\frac{R\Lambda-p_cA_5}{Z},\qquad d=24+e, \tag{29.1}
$$

and use (26.2) for the one entire gain. The compatibility identity
(26.7) gives $p_c\Lambda=-RA_5$. It follows by direct multiplication
that (29.1) satisfies both equations (26.4):

$$
e\Lambda=R,\qquad eA_5=-p_c.
$$

The zero-safe parent converse then proves all five parent readings,
and the second equation proves that the literal fifth-M reading is
zero. This is an actual complete world, with the original strict
source, a nonzero whole gain and a fixed real drift. Conversely every
actual zero-base world has $F=0$ by (26.7), hence lies on one of the
two graphs; its two equations (26.4) uniquely force (29.1). This proves
the bijection with the two complete arcs, including their singular
points. All the reconstruction functions are real analytic on each
arc because the denominator $Z$ is positive.

At either singular point $R=0,p_c=24$, so the unique lift has
$e=-24/A_5>0$. It is a single zero-base member of the full allowed
singular drift line, not an assumption of zero drift or zero gain.

To prove the drift sign on the entire arcs, first note that $e=0$
would force $R=0$, hence $b=1/8$. At this width $g^0_5=0$, so
$p_c=24$ and the second equation (26.4) cannot hold with $e=0$.
Thus $e$ never vanishes on either connected arc.

The signs at one diagonal coordinate can be checked exactly.
At $r=1/2$,

$$
F(1/2,1/16)=-10122915/33554432<0,\qquad
F(1/2,1/3)=-365/5832<0.
$$

The root ordering implies $b_-(1/2)<1/16$ and
$1/3<b_+(1/2)<1/2$. On the lower interval $j=b+1/(4b)>4$,
$n>9/2$, so

$$
\Lambda>1+96/17-1-8/9>0,\qquad R>0.
$$

On the upper interval $j\le13/12,n\le19/12$, and therefore

$$
\Lambda\le61/10-48/13-48/19=-293/2470<0,\qquad R<0.
$$

In both cases $e=R/\Lambda>0$. Analyticity and connectedness now
imply $e>0$ on both entire arcs. Thus every actual zero-base world
has $d>24$, and its original fifth equation gives

$$
g(5)=-\frac d{U+n}<0. \tag{29.2}
$$

In particular the absence of zero drift and of a sampled zero at
clock five is a consequence proved for this sector. It was not an
imposed filter. No leading gain coefficient, gain root difference or
other sampled gain was divided out; every lower degree, repeated root
and sampled zero compatible with the original rows remains represented.



## 30. The exact entire-child incidence problem on the two arcs

The later interpolation values of the very same entire gain are

$$
\begin{aligned}
g_6&=-10z_0+36z_1-45z_2+20z_3,\\
g_7&=-20z_0+70z_1-84z_2+35z_3.
\end{aligned}
$$

For $\sigma\in\{-,+\}$ evaluate (26.1)–(26.3), (29.1) and (26.2)
at $(r,b_\sigma(r))$, and define

$$
\begin{aligned}
V_\sigma(r)&=24+e+(2U+n)g_6,\\
A_\sigma(r)&=24+e+(T+2j+4r)g_7,\\
M_\sigma(r)&=24+e+(3U+2n)g_7.
\end{aligned} \tag{30.1}
$$

These are explicit algebraic real analytic functions, defined at the
two singular points by the same positive-denominator formula (29.1).
The entire child is exactly

$$
C(0,v)=\{W_\sigma(r):\ 0<r<1,\ \sigma\in\{-,+\},\
                                      V_\sigma(r)=v\}. \tag{30.2}
$$

In particular there are no additional positive-width or singular
components outside these two arcs. The original zero-base joint
question is now exactly whether there exist four labels
$(\sigma_i,r_i)$, $i=0,1,2,3$, such that

$$
\begin{gathered}
0<r_i<1,\qquad \sigma_i\in\{-,+\},\\
V_{\sigma_0}(r_0)=V_{\sigma_1}(r_1)
 =V_{\sigma_2}(r_2)=V_{\sigma_3}(r_3),\\
(\sigma_0,r_0)\ne(\sigma_1,r_1),\qquad
(\sigma_2,r_2)\ne(\sigma_3,r_3),\\
A_{\sigma_0}(r_0)=A_{\sigma_1}(r_1),\qquad
M_{\sigma_2}(r_2)=M_{\sigma_3}(r_3).
\end{gathered} \tag{30.3}
$$

Different labels give different complete source worlds, and every
complete world has exactly one label. Thus the inequalities in (30.3)
are precisely complete-world distinctness. Cross-pair equality of
labels is permitted. Nothing in (30.3) equates the two common terminal
answers or requires a shared pair or a shared width.

The algebraic reduction (26.5)–(30.3), not a width cut alone, is the
result. A proof of collision, or a proof of injectivity sufficient to
exclude both independent pairs, remains to be supplied. The
zero-base target (30.3), and hence the unrestricted original target,
remain unresolved. Failure to find a collision in numerical
exploration supplies neither existence nor nonexistence.



## 31. Mathematical provenance and limits

The complete-world domain, chronological left products, literal clocks and zero-safe parent converse are those of *FIB common-parent geometry and two exact mixed children*, Definitions 1.1–1.3 and Theorem 2.1. Its Definition 12.1, Lemma 12.2 and Theorem 12.3 also give the polynomial criterion for an arbitrary fifth-M response, the nonzero drift-coefficient vector and the unique whole-world lift. Under the correspondence

$$
X=\mathcal J,\qquad N=\mathcal N,\qquad V=U+n,\qquad
N_4=\frac{2D}{5},\qquad \mathsf S_0=6F,\qquad K_5=p_c-24,
$$

that prior lift at response zero is exactly (29.1). Thus the zero-safe reconstruction and the source polynomial criterion are reused. The additional conclusion is the exhaustive decomposition of this entire zero-base family into the two analytic arcs, with their strict width bounds and global drift sign.

*Positive acquired bases force low-width terminal-J companions*, Section 2, has regular numerator $P_p=-3F$. Its Lemma 3.1 excludes response zero at $b\ge3/4$, because $P_p<0$ there, whereas an actual parent with $D=0$ has $b=1/8$. That width exclusion does not count the roots at smaller widths and does not establish a terminal collision or obstruction.

The two singular parent sources and their unique lifts at a prescribed fifth response are already described in *FIB common-parent geometry and two exact mixed children*, Theorem 4.2. The singular polynomial, explicit Sturm chain, isolating intervals and strict $A_5$ bound are also the results of *Uniqueness of actual sources above width eight*, Sections 14–16. These singular data and their correspondence to the original whole worlds are reused. They do not exclude a pair containing both a singular and a regular world.

*An exact unequal-diagonal pair for the original terminal M response*, Sections 54–58, gives an all-width terminal-M reconstruction for $p\ne24$, retaining its exceptional branches and strict-source conditions. Section 59 keeps the independent J and M pairs, and Section 65 gives further restrictions at nonnegative fifth responses. Those results do not classify the entire zero-base source curve into the two arcs established here.

The additional conclusions relative to these named sources are the exactly-two-simple-positive-root theorem for every $0<r<1$, the strict bounds

$$
0<b_-(r)<\frac{r(1-r)}2<b_+(r)<\frac12,
$$

the resulting two analytic components of actual zero-base worlds across both parent singular points, and the global consequences $d>24$ and $g(5)<0$. Bernstein polynomial identities, Descartes' rule, the intermediate value theorem, Sylvester elimination, Sturm's theorem and the analytic implicit-function theorem are classical. No literature-priority claim is made.

The original existence question remains some $p\ne24,v$ admitting an independently distinct J pair and an independently distinct M pair in one entire $C(p,v)$. The pairs may overlap and their common terminal answers are independent. Response zero is an allowed route within that question. Its exact incidence formulation is (30.3), which remains unresolved; the two-arc theorem supplies neither a joint witness nor a global exclusion. All singular sources and all gain degeneracies compatible with the original rows remain included. The acquisition, source domain, whole gain and clock convention are unchanged. The forbidden-base local intersection at $p=24$ is not a witness. These are ordinary mathematical results without a formal-kernel claim.

## 32. All-base consequences and the remaining boundary

The three source sectors now cover every real fifth acquired base. The
negative sector gives Corollary 12.1, the zero sector is the complete
bijection of Theorem 25.1, and the positive sector gives Theorem 22.1.
Together they imply the following width restriction for every distinct
terminal-J pair.

**Theorem 32.1 (all-base terminal-J restriction).** Let $p,v\in\mathbb R$ and
let $W_0\ne W_1$ lie in one entire child $C(p,v)$ with
$a(W_0)=a(W_1)$. Then at least one of the two worlds has $b<1$. More
specifically:

1. If $p<0$, this is Corollary 12.1.
2. If $p=0$, every world in the child is one of the two arcs of Theorem
   25.1 and therefore has $b<1/2$.
3. If $p>0$, Theorem 22.1 gives the member with $b<1$; when
   $p\ge p_0=1587/25$, it gives the stronger bound $b<3/4$.

The conclusion concerns the J pair alone. It imposes no width condition on
an independently chosen terminal-M pair, and it does not identify the two
common terminal answers. The singular classification of Theorem 18.1 adds
that no entire child contains a distinct singular-singular J pair with equal
terminal-J readings, at any real $p,v$. The inherited large-width theorem
also remains valid without a sign restriction: every entire child contains
at most one world with $b\ge8$. Consequently each distinct J pair and each
distinct M pair has a member with $b<8$, and the union of the two
independently selected pairs contains at most one world of width at least
eight.

These statements retain every strict source, the fixed drift, the literal
left word and clocks, all compatible gain degeneracies, and the singular
parents. They do not settle the original assertion: it still asks for some
$p\ne24,v$ and independently distinct pairs $W_0\ne W_1$ and
$W_2\ne W_3$ in one $C(p,v)$ with
$$
a(W_0)=a(W_1),\qquad m(W_2)=m(W_3),
$$
with overlap allowed and with independent common terminal values. No
terminal-M injectivity theorem, common pair, common width, or common answer
has been introduced. The exact zero-base incidence problem (30.3) remains
open, and so does the unrestricted original target.

## 追加锚（本行以下为增补区）

## 33. Acquired-image separation on the complete zero-base arcs

A world is the complete triple

$$
 W=(P(r,b),g,d),\qquad
 P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
 \quad 0<r<1,\quad b>0,\quad d\in\mathbb R,
 \quad 0\ne g\in\mathbb R[s],\quad\deg g\le3.
$$

The chronological acquired word is literally $J,M,J,M,M,M$, where
$J=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ and
$M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$.
Products act on the left, $Q_0=I$, $Q_i=E_iQ_{i-1}$, and the
reading at clock $i$ is $d+g(i)\operatorname{tr}(Q_iP)$.
The acquired readings at clocks zero through six are
$0,24,147/5,24,18,0,v$. The terminal alternatives occur at clock
seven and are denoted by $a(W),m(W)$. There is one fixed entire gain
and one fixed drift in each world.

We use the complete zero-base classification and zero-safe lift of
Theorem 25.1 and its proof in Sections 25–31. In particular, all complete worlds
through clock five in this sector are exactly the two analytic arcs
$W_-(r),W_+(r)$, $0<r<1$, with

$$
 0<b_-(r)<r(1-r)/2<b_+(r)<1/2.
 \tag{33.1}
$$

They are the two simple positive roots of the source polynomial $F$
recorded below. The labeling is one-to-one on complete worlds. Their
unique zero-safe lifts include both singular parent sources on the upper
arc. On both complete arcs the reused theorem gives $e=d-24>0$.
These are the classification and lift conclusions of Theorem 25.1;
the response and sign conclusions below use them as premises.

For exact correspondence with the common-parent notation in Section 12,
put

$$
 T=1+b,\quad U=1+2b,\quad j=b+r(1-r)/b,\quad n=j+r,
 \quad\mathcal J=bj,\quad\mathcal N=bn.
$$

That source's $(X,N,V,N_4,\mathsf S_0,K_5)$ are respectively

$$
 (\mathcal J,\mathcal N,U+n,2D/5,6F,p_c-24),
$$

where

$$
\begin{split}
 D&=5\{(b^2+8b+4)\mathcal J\mathcal N
                  -2TUb(\mathcal J+\mathcal N)\},\\
 \Lambda&=1+6/T+1/U-4/j-4/n,\\
 R&=-6(8b-1)(2+5b)/(5TU),\\
 q_5&=4-15/j+20/T-10/n,\quad A_5=1+(U+n)q_5,\\
 p_c&=24+(U+n)(96-108/T).
\end{split}\tag{33.2}
$$

In particular its lift at fifth response zero is exactly

$$
 Z=\Lambda^2+A_5^2>0,\qquad
 e=(R\Lambda-p_cA_5)/Z,\qquad d=24+e.
 \tag{33.3}
$$

It satisfies $e\Lambda=R$ and $eA_5=-p_c$. This is the zero-safe whole-world lift of Theorem 25.1.

**Theorem 33.1 (acquired-image separation and terminal signs).** On the complete lower arc,

$$
 n>19/5,\qquad V_-(r)>90.
 \tag{33.4}
$$

On the complete upper arc,

$$
 1+3b/2+b^2/8<n<2,\qquad V_+(r)<90.
 \tag{33.5}
$$

On both complete arcs,

$$
 b<7/20,\qquad g(7)>0,\qquad 24<d<a(W)<m(W).
 \tag{33.6}
$$

Here $V_\sigma$ is the actual clock-six acquired M response, not a
rescaled or changed observation. All these inequalities are strict and
include the two singular sources. Thus the acquired images are disjoint,
with 90 strictly between them. These claims neither assert injectivity
within an arc nor settle the independent-pair existence problem.

## 34. Source bounds by explicit barriers

For reference, the reused polynomial is $F(r,b)=\sum_{k=0}^7c_k(r)b^k$,
where

$$
\begin{split}
c_0&=32r^3(1-r)^3,\\
c_1&=32r^2(r-1)^2(2r+1)(4r-5),\\
c_2&=-2r(r-1)(256r^3-140r^2-185r+65),\\
c_3&=r(-744r^3+1837r^2-1408r+375),\\
c_4&=1216r^3-1623r^2+639r+130,\\
c_5&=456r^2-479r+465,\qquad c_6=746-624r,\qquad c_7=72.
\end{split}\tag{34.1}
$$

We use Bernstein coefficients only as elementary polynomial sign
certificates. If $f(x)=\sum_{i=0}^m f_ix^i$, its degree-$m$
Bernstein coefficient at index $k$ on $[0,1]$ is

$$
 B_k(f)=\sum_{i=0}^k f_i\binom{k}{i}/\binom{m}{i}.
 \tag{34.2}
$$

For another interval substitute its affine parameter first. The
Bernstein basis is nonnegative and sums to one.

Set $h=7/20$. The degree-six Bernstein coefficient vectors of
$F(r,h)$, multiplied by the common positive factor 1280000000,
on the consecutive intervals $[0,1/4],[1/4,1/2],[1/2,3/4],[3/4,1]$
are

$$
\begin{split}
 &(7437760176,9460653146,10419129336,10498022721,
                  9927874276,8940531976,7742750796),\\
 &(7742750796,6544969616,5136749556,3724845591,
                  2490919696,1565140846,1017785016),\\
 &(1017785016,470429186,301496376,581262561,
                  1320110716,2460130816,3884719836),\\
 &(3884719836,5309308856,7018466796,8895590631,
                  10765384336,12403458886,13563932256).
\end{split}\tag{34.3}
$$

They are all positive, so $F(r,h)>0$ on $[0,1]$. Theorem 25.1 and
the root ordering (33.1), together with $h>r(1-r)/2$, imply $b_+(r)<h$.
Indeed $F$ is negative between its two simple positive roots and
positive after the second. The lower width is smaller still. This proves
the whole-arc width bound without imposing a width restriction on worlds.

The identity $n=b+r(1-r)/b+r$ is equivalent to

$$
 L(r,b,n)=r^2-(1+b)r+b(n-b)=0.
 \tag{34.4}
$$

The following three resultant identities follow by expansion of the
Sylvester determinants in $r$:

$$
\begin{split}
 \operatorname{Res}_r(F,L|_{n=19/5})&=-b^6P_{19}(b)/15625,\\
 \operatorname{Res}_r(F,L|_{n=2})&=-4b^6P_2(b),\\
 \operatorname{Res}_r(F,L|_{n=q(b)})&=b^6P_q(b)/512,
 \qquad q(b)=1+3b/2+b^2/8,
\end{split}\tag{34.5}
$$

with the complete polynomials

$$
\begin{split}
P_{19}={}&3600000000b^8-3324000000b^7-111729310000b^6
 -3457048000b^5\\
 &+977942109175b^4+142318812570b^3-2792945037326b^2
 -13783002496b-11887464,\\
P_2={}&57600b^8+47040b^7-412636b^6-483868b^5
 +437170b^4+395592b^3\\
 &-294695b^2-25672b-372,\\
P_q={}&128b^{14}+11040b^{13}+356770b^{12}+5384920b^{11}
 +40021092b^{10}\\
 &+159483477b^9+358823600b^8+468926548b^7+364204144b^6\\
 &+163023424b^5+31365632b^4-4066048b^3-2233856b^2
 +59392b+61440.
\end{split}\tag{34.6}
$$

Here $P_{19}<0$ for $0<b<h$: group its first two terms as
$b^7(3600000000b-3324000000)<0$, and group its positive fourth
and third powers with its negative second power as

$$
 b^2(977942109175b^2+142318812570b-2792945037326)<0.
$$

The latter inequality already holds with $b$ replaced by $1/2$
in its two positive terms. All remaining summands are negative.
Similarly $P_2<0$:

$$
\begin{split}
 57600b^2+47040b-412636&<0,\\
 437170b^2+395592b-294695&\le-4107379/40<0
       \quad(0\le b\le h),
\end{split}
$$

and these expressions group respectively with $b^6$ and $b^2$,
leaving only negative terms.

For $P_q$, the complete degree-fourteen Bernstein vector on $[0,h]$
is

$$
\begin{split}
(&61440,314624/5,19955808/325,91640453/1625,
4280257506/89375,\\
&525986386441/14300000,3366744981541/132000000,
20876279105812931/1098240000000,\\
&897014111310199/34320000000,
819916880625851807/13312000000000,\\
&1046562428444737243/7040000000000,
17195177725191846303/53248000000000,\\
&3393522467177723859051/5324800000000000,
2393533558065985867593/2048000000000000,\\
&103777062152086200189321/51200000000000000).
\end{split}\tag{34.7}
$$

Thus $P_q>0$. Equations (34.5) consequently exclude every equality
$n=19/5,n=2,n=q(b)$ on either complete arc. A common real root of
$F,L$ would force the corresponding resultant to vanish, regardless
of possible leading-coefficient degeneracy in the resultant inputs.

It remains to select the side of each barrier. At $r=1/2$, the
already proved root theorem and the exact values

$$
 F(1/2,1/16)=-10122915/33554432<0,\qquad
 F(1/2,1/3)=-365/5832<0
$$

give $b_-<1/16$ and $1/3<b_+<h$. On the lower arc at this
coordinate,
$n=b+1/(4b)+1/2>9/2>19/5$.
On the upper arc, $b+1/(4b)$ decreases for $b<1/2$, so
$n<13/12+1/2=19/12<2$. Moreover

$$
 n-q(b)=1/(4b)-1/2-b/2-b^2/8
        >537/22400>0,
$$

because this expression decreases with $b$ and its value at $h$
is $537/22400$. Continuity on each connected whole arc and the
three excluded equalities now prove (33.4)'s source bound and (33.5)'s source
bounds everywhere. Also, $q(b)\le q(h)=4929/3200<19/5$, so
$n>q(b)$ on the lower arc as well.

## 35. A guarded rational chart derived from the four forced samples

Before simplification, the four forced values of the same entire gain
are exactly

$$
 z_0=-24-e,\qquad z_1=-e/j,\qquad
 z_2=(27/5-e)/T,\qquad z_3=-e/n.
 \tag{35.1}
$$

Their degree-at-most-three interpolant gives all future values:

$$
\begin{split}
 g(4)&=-z_0+4z_1-6z_2+4z_3,\\
 g(5)&=-4z_0+15z_1-20z_2+10z_3,\\
 g(6)&=-10z_0+36z_1-45z_2+20z_3,\\
 g(7)&=-20z_0+70z_1-84z_2+35z_3.
\end{split}\tag{35.2}
$$

The inherited literal trace factors at clocks five and six and the two
terminal alternatives are, respectively,

$$
 U+n,\qquad 2U+n,\qquad T+2j+4r=T+2n+2r,
 \qquad 3U+2n.
 \tag{35.3}
$$

Consequently the actual responses, before any simplification, are

$$
 V=d+(2U+n)g(6),\quad
 A=d+(T+2n+2r)g(7),\quad M=d+(3U+2n)g(7).
 \tag{35.4}
$$

Here $A=a(W)$ and $M=m(W)$; the symbol $M$ in (35.4) denotes a
response, whereas the matrix was specified in Section 33.

Introduce the following polynomials, which are different from the
parent denominator $D$ and from the source sextic in the common-parent
volume:

$$
\begin{split}
 H={}&(b^2-16b-12)n^2+b(2b^2-7b-4)n+10(1+2b)^2(1+b),\\
 C={}&16b^3+70b^2+59b+14+(8b^2+15b-2)n,\\
 B={}&160b^2+240b+80-(143b+94)n,\\
 N_6={}&320b^3-118b^2n-960b^2-139bn^2+1801bn
          -2180b-542n^2+1350n-810,\\
 N_7={}&1200b^3-392b^2n-190b^2-496bn^2+3619bn
          -3015b-1728n^2+2870n-1310.
\end{split}\tag{35.5}
$$

First prove the denominator guard. On $0<b<h$, the coefficients
$b^2-16b-12$ and $b(2b^2-7b-4)$ are strictly negative.
Thus $H$ strictly decreases with $n>0$. Exact substitution gives

$$
 H(b,q(b))=
 (b^6+24b^5-100b^4-672b^3-640b^2-384b-128)/64<0.
 \tag{35.6}
$$

Indeed its first three terms are
$b^4(b^2+24b-100)<0$ for $b<h$, and the others are negative.
Since both arcs have $n>q(b)>0$, we obtain the strict whole-arc guard

$$
 H<0.\tag{35.7}
$$

This guard is not the already known inequality $-Z<0$.

The two original scalar equations for $e$ give the polynomial
elimination identity

$$
\begin{split}
 K&:=4A_5-15(U+n)\Lambda=2H/(nTU),\\
 E&:=-4p_c-15(U+n)R=-6C/(TU),\qquad eK=E.
\end{split}\tag{35.8}
$$

Every denominator in (35.8) is positive except the explicitly guarded
$H$. We may therefore solve, everywhere on both arcs,

$$
 e=-3nC/H,\qquad d=3(U+n)B/H.\tag{35.9}
$$

To obtain future samples directly from (35.1)–(35.2), eliminate $z_1$
using the original clock-four relation in the division-free form

$$
 4z_1=R-e(1+6/T+1/U-4/n).
 \tag{35.10}
$$

Substituting (35.9)–(35.10) into (35.2), by polynomial expansion, gives

$$
 g(5)=-3B/H,\qquad g(6)=3N_6/(5H),\qquad
 g(7)=3N_7/(5H).
 \tag{35.11}
$$

For example $8H-nC=(U+n)B$ verifies the identity for $d$, and
(35.11) also yields $d+(U+n)g(5)=0$, the actual fifth reading.
The rational response chart is (35.4) with (35.9) and (35.11).
It was derived from the one common interpolant, not by assigning
independent gains to future rows.

All guards are now explicit. The strict source implies
$b,j,n,T,U,U+n>0$, while (35.7) gives $5H\ne0$.
The earlier zero-safe lift uses only $Z>0$. At either singular
source $b=1/8$, with $D=\Lambda=0$, bounds (33.5) and (35.7) still
hold; (35.8) then has $K=4A_5\ne0$. There is no division by
$D,\Lambda,e$, a gain sample, a leading coefficient, a discriminant
or a gain-root difference in this derivation. Thus neither singular
world nor any compatible gain degeneracy has been removed.

## 36. Terminal signs

From (35.5), direct substitution and differentiation give

$$
\begin{split}
 N_7(b,q(b))
 &=-\{62b^5+2096b^4+6589b^3+4822b^2+6168b+1344\}/8<0,\\
 (\partial_nN_7)(b,q(b))&=-124b^3-2312b^2-2557b-586<0,\\
 \partial_n^2N_7&=-2(496b+1728)<0.
\end{split}\tag{36.1}
$$

It follows that $N_7<0$ for all $n>q(b)$. Equations (35.7) and
(35.11) prove $g(7)>0$ on both whole arcs. The exact trace difference
in (35.3) gives

$$
 m(W)-a(W)=(2+5b-2r)g(7)>0,
 \tag{36.2}
$$

since $r<1$ and $b>0$. Also $T+2n+2r>0$, so (35.4), together
with the reused $d>24$, gives $a(W)>d>24$.
This proves all the terminal claims, including both singular points.
Equation (36.2) compares two terminal alternatives at the same world;
it makes no assertion comparing terminal values at different worlds.

## 37. Exact acquired-image separation

Expanding (35.4), (35.9) and (35.11) gives the identity

$$
 V-90=3P(b,n)/(5H),\tag{37.1}
$$

where the complete numerator is

$$
\begin{split}
 P(b,n)={}&1280b^4-452b^3n-7600b^3-824b^2n^2+6428b^2n
          -19440b^2\\
 &-139bn^3+1040bn^2+6967bn-13100b
          -542n^3+1596n^2+1820n-2720.
\end{split}\tag{37.2}
$$

On the lower arc, (33.1) gives $0<b<1/8$, and Section 34 gives
$n>19/5$. Write
$P(b,19/5+x)=\sum_{i=0}^3L_i(b)x^i$. The full Bernstein vectors
of $L_i$ on $[0,1/8]$, at their respective degrees $4,3,2,1$,
are

$$
\begin{split}
 L_0:&\quad(-312298/125,-924739/500,-14622869/12000,
                         -39053879/64000,-3667/128),\\
 L_1:&\quad(-238246/25,-916111/100,-3516607/400,-1078009/128),\\
 L_2:&\quad(-22914/5,-369347/80,-18655/4),\\
 L_3:&\quad(-542,-4475/8).
\end{split}\tag{37.3}
$$

These follow directly from (34.2) and (37.2); every entry is negative.
Thus all $L_i(b)<0$, and for $x=n-19/5>0$ we have $P<0$.
Since $H<0$, (37.1) proves $V_->90$ throughout the lower arc.

On the upper arc $q(b)<n<2$ and $0<b<h$. At the lower endpoint,

$$
 P(b,q(b))=
 \{78848-78336b-274048b^2-123904b^3-690064b^4
                  -261712b^5-12138b^6-139b^7\}/512.
 \tag{37.4}
$$

This polynomial strictly decreases with $b>0$, and

$$
 P(h,q(h))=1017472390683/655360000000>0.
 \tag{37.5}
$$

Hence $P(b,q(b))>0$ for $0<b<h$.

For completeness, positivity at that endpoint propagates in the required
$n$-direction, rather than being treated as a global numerical test.
The derivative $\partial_nP$ is a concave quadratic in $n$, with
quadratic coefficient $-3(139b+542)<0$. Its endpoint values are

$$
\begin{split}
 (\partial_nP)(b,q(b))
 &=\{216704+546560b+190912b^2-276240b^3-24818b^4-417b^5\}/64>0,\\
 (\partial_nP)(b,2)&=1700+9459b+3132b^2-452b^3>0.
\end{split}\tag{37.6}
$$

For the first sign, group the terms of degree at least two as

$$
 b^2(190912-276240b-24818b^2-417b^3),
$$

whose bracket is at least its value at $h$, namely
$729359329/8000>0$. For the second sign use
$3132-452b>0$. A concave function is at least its endpoint chord,
so $\partial_nP>0$ on $[q(b),2]$. Thus
$P(b,n)>P(b,q(b))>0$ on the whole upper arc. Equation (37.1), with
$H<0$, proves $V_+<90$. This establishes separation by exact
whole-arc signs, not by isolated source samples.

## 38. The remaining independent-pair incidence

Define $A_\sigma(r),M_\sigma(r),V_\sigma(r)$ by the guarded chart
(35.4), (35.9), (35.11) at $b=b_\sigma(r)$. The reused exhaustive lift gives

$$
 C(0,v)=\{W_\sigma(r):\ 0<r<1,\ \sigma\in\{-,+\},
                                  \ V_\sigma(r)=v\}.
 \tag{38.1}
$$

The proved separation sharpens this exactly as follows: if $v>90$,
only the lower arc can occur; if $v<90$, only the upper arc can occur;
and $C(0,90)=\varnothing$. This does not assert that every $v$
on either side belongs to the corresponding acquired image.

Consequently the zero-base part of the original independent-pair target
is equivalent to the existence of one sign $\sigma$ and four numbers
$r_0,r_1,r_2,r_3\in(0,1)$ satisfying

$$
\begin{gathered}
 V_\sigma(r_0)=V_\sigma(r_1)=V_\sigma(r_2)=V_\sigma(r_3),\\
 r_0\ne r_1,\qquad r_2\ne r_3,\\
 A_\sigma(r_0)=A_\sigma(r_1),\qquad
 M_\sigma(r_2)=M_\sigma(r_3).
\end{gathered}\tag{38.2}
$$

The first two labels give the J pair and the last two labels give the M
pair. Within-pair distinctness is exactly complete-world distinctness,
by the one-to-one arc labels. Cross-pair coincidences are allowed, and
there is no equation between the common J answer and the common M
answer. Conversely, any solution of (38.2) supplies four complete worlds
in the one entire child (38.1) with exactly the required properties.
This proves both directions of the incidence reduction.

No injectivity theorem for the acquired or terminal response maps on an
individual arc is proved here. In particular, pointwise $a(W)<m(W)$
does not rule out either kind of same-child terminal pair. Existence or
nonexistence of (38.2) remains unresolved. The original question permits
some arbitrary $p\ne24$; this source proves new bounds in its allowed
$p=0$ sector only, and does not resolve that unrestricted question.

The source barriers (33.4)–(33.6), the guarded rational
response chart, the terminal signs and the acquired-image separation
have the exact incidence consequence (38.2). Polynomial interpolation, resultants,
Bernstein positivity and elementary continuity are classical tools.

## 39. A strict negative-base singular/regular terminal-J collision

In Sections 39–46, $p$ varies again and all auxiliary symbols are
defined afresh.

A complete world is a triple $(P(r,b),g,d)$, where

$$
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad d\in\mathbb R,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3.
$$

Let $J=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ and
$M=\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)$.
Products act on the left: $Q_0=I$, $Q_i=E_iQ_{i-1}$.
The acquired word is $J,M,J,M,M,M$. At clock $i$ the reading is
$d+g(i)\operatorname{tr}(Q_iP)$. Its prescribed acquired readings are
$(0,24,147/5,24,18,p,v)$. The two terminal alternatives are at clock
seven, with the same source, whole gain polynomial and drift.
Write $a(W)$ and $m(W)$ for those J and M readings, respectively.
The set $C(p,v)$ includes every complete world satisfying these rows.

**Theorem 39.1 (a negative-base mixed J pair).** There exist real numbers $p,v$ satisfying

$$
-10.891256858561706<p<-10.891256858561705,\qquad
-8.154074713130907<v<-8.154074713130906
$$

and two distinct strict complete worlds $W_s,W_r\in C(p,v)$ such that

$$
a(W_s)=a(W_r),\qquad
95.983033177664570<a(W_s)<95.983033177664571.
$$

Their widths are $1/8$ and an element of
$(0.13212921348879,0.13212921348880)$, respectively. Moreover,

$$
0.461473279642<m(W_r)-m(W_s)<0.461473279643.
$$

This theorem concerns a J pair. It does not assert an M pair in the
entire child, or exclude a different M pair there.

## 40. Literal whole-world equations

Set

$$
j=b+r(1-r)/b,\quad n=j+r,\quad T=1+b,\quad U=1+2b,
\quad Z=T+2j+4r,\quad R=3U+2n.
$$

For $Q=(q_{ij})$ one has
$\operatorname{tr}(QP)=q_{11}r+q_{12}r(1-r)/b+q_{21}b+q_{22}(1-r)$.
Direct multiplication gives the entire chronological table:

| Clock/action | Left product | Trace against $P$ |
| --- | --- | --- |
| 0 | $I$ | $1$ |
| 1, J | $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ | $j$ |
| 2, M | $\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ | $T$ |
| 3, J | $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ | $n$ |
| 4, M | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $U$ |
| 5, M | $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ | $U+n$ |
| 6, M | $\left(\begin{smallmatrix}3&1\\5&2\end{smallmatrix}\right)$ | $2U+n$ |
| 7, J | $\left(\begin{smallmatrix}5&2\\3&1\end{smallmatrix}\right)$ | $Z$ |
| 7, M | $\left(\begin{smallmatrix}5&2\\8&3\end{smallmatrix}\right)$ | $R$ |

Put $e=d-24$, $\delta=b-1/8$, and

$$
\Lambda=1+6/T+1/U-4/j-4/n,\qquad
D_0=\frac{24}{5}\delta(6/T-2/U).
$$

Let $\ell_i(s)=\prod_{0\le k\le3,\ k\ne i}(s-k)/(i-k)$.
The unique whole polynomial compatible with clocks zero through three is

$$
g(s)=(-24-e)\ell_0(s)-\frac e j\ell_1(s)
 +\frac{27/5-e}{T}\ell_2(s)-\frac e n\ell_3(s).
\tag{40.1}
$$

Lagrange interpolation gives the exact weight table

$$
\begin{array}{c|rrrr}
s&\ell_0&\ell_1&\ell_2&\ell_3\\\hline
4&-1&4&-6&4\\
5&-4&15&-20&10\\
6&-10&36&-45&20\\
7&-20&70&-84&35
\end{array}.
\tag{40.2}
$$

In particular, direct substitution in (40.1) gives

$$
g(4)-\frac{-6-e}{U}=e\Lambda+D_0.
\tag{40.3}
$$

Consequently the zero-safe necessary and sufficient parent equation is
$e\Lambda+D_0=0$. The literal fourth acquired reading is exactly
$18+U(e\Lambda+D_0)$, while the first four readings are identically
$0,24,147/5,24$.

For an explicit sign check, put $h(s)=\frac85(s-1)(s-3)(s-5)$ and $w=g-h$.
Its four samples are
$(-e,-e/j,-(e+(24/5)\delta)/T,-e/n)$.
Thus the negative coefficients in column two of (40.2) give the positive
$\delta$ terms in the following identities:

$$
\begin{aligned}
q_5&=4-15/j+20/T-10/n,\\
q_6&=10-36/j+45/T-20/n,\\
q_7&=20-70/j+84/T-35/n,\\
g(5)&=eq_5+96\delta/T,\\
g(6)&=24+eq_6+216\delta/T,\\
g(7)&=384/5+eq_7+(2016/5)\delta/T.
\end{aligned}
\tag{40.4}
$$

Define

$$
\begin{array}{ll}
k_5=1+(U+n)q_5,&c_5=96\delta(U+n)/T,\\
k_6=1+(2U+n)q_6,&c_6=24(2U+n)+216\delta(2U+n)/T,\\
k_J=1+Zq_7,&c_J=(384/5)Z+(2016/5)\delta Z/T,\\
k_M=1+Rq_7,&c_M=(384/5)R+(2016/5)\delta R/T.
\end{array}
\tag{40.5}
$$

The direct original-row identities, before using the parent equation, are

$$
\begin{aligned}
d+g(5)(U+n)&=24+c_5+ek_5,\\
d+g(6)(2U+n)&=24+c_6+ek_6,\\
d+g(7)Z&=24+c_J+ek_J,\\
d+g(7)R&=24+c_M+ek_M.
\end{aligned}
\tag{40.6}
$$

Equations (40.1)–(40.6) use no division by a gain sample, a leading gain
coefficient, drift or difference of roots. All trace denominators
$j,n,T,U$ are strictly positive. Every resulting whole gain is nonzero:
an identically zero gain would force the unequal first two readings to
equal the same drift. Lower degrees, sampled zeros, repeated roots and
zero drift are therefore retained in the parent characterization.

## 41. Singular sources and the incidence equations

Since $6/T-2/U=2(2+5b)/(TU)>0$, an actual parent with $\Lambda=0$
must have $b=1/8$. At that width,

$$
j=1/8+8r-8r^2,\qquad n=1/8+9r-8r^2,
\qquad 960jn\Lambda=\Phi(r),
$$

where

$$
\Phi(X)=438272X^4-931328X^3+540800X^2-50728X-853.
\tag{41.1}
$$

Thus every strict zero $x$ of $\Phi$ gives a singular parent for every
real $e_s$, through (40.1). Superscript $s$ denotes evaluation at $(x,1/8)$.
On the regular chart put

$$
e_r=-D_0/\Lambda,\quad
P_*=c_5+e_rk_5,\quad V_*=c_6+e_rk_6,\quad A_*=c_J+e_rk_J.
$$

For $k_5^s\ne0$, define the rational map in coordinates $(x,r,b)$

$$
H(x,r,b)=\begin{pmatrix}
\Phi(x)/100000\\
(V_*-c_6^s-k_6^sP_*/k_5^s)/100\\
(A_*-c_J^s-k_J^sP_*/k_5^s)/1000
\end{pmatrix}.
\tag{41.2}
$$

A zero of (41.2) with strict sources and $\Lambda\ne0$ supplies the
singular drift parameter $e_s=P_*/k_5^s$.
Equations (40.3) and (40.6) then prove equality of all acquired readings and
the terminal J reading. This is an equivalence on this chart.

## 42. An exact contraction certificate

Every finite decimal in the certificate denotes its exact rational
value. Let $z_0=(x_0,r_0,b_0)$ be

$$
\begin{aligned}
x_0&=0.9024496817720562653778726512965428561862764994432208971,\\
r_0&=0.8966007636835690682237424612851910519964607303119325469,\\
b_0&=0.1321292134887946369975978574045560868312842236443399628.
\end{aligned}
$$

Let $B=\{z:\|z-z_0\|_\infty\le10^{-22}\}$ and set

$$
Y=\begin{pmatrix}
-1.62240571523041840394897227998410812397701982&0.0&0.0\\
1097.98148211497919919534155185346286404397996&-47.2756511127254963652551981931165510799754594&-9.01019676074583093624943821826100969234137133\\
-1330.63131864401657945900801852451899658672206&57.3636028152952516239422067418952637003261437&10.7704556441793128638802993407707998475554469
\end{pmatrix}.
$$

The following enclosures hold on the entire closed cube $B$:

| Quantity | Regular source | Singular source |
| --- | --- | --- |
| $j$ | $[0.833774457547,0.833774457548]$ | $[0.829274029132,0.829274029133]$ |
| $n$ | $[1.730375221230,1.730375221231]$ | $[1.731723710904,1.731723710905]$ |
| $T$ | $[1.132129213488,1.132129213489]$ | $[1.125000000000,1.125000000000]$ |
| $U$ | $[1.264258426977,1.264258426978]$ | $[1.250000000000,1.250000000000]$ |
| $Z$ | $[6.386081183317,6.386081183318]$ | $[6.393346785353,6.393346785354]$ |
| $R$ | $[7.253525723394,7.253525723395]$ | $[7.213447421809,7.213447421810]$ |
| $\Lambda$ | $[-0.018371889496,-0.018371889495]$ | — |
| $D_0$ | $[0.127223724449,0.127223724450]$ | — |

Also $k_5^s\in[-5.216672133352,-5.216672133351]$.

In particular, every denominator in (41.2) is separated from zero, and
$0<x,r<1$, $b>1/8$ on $B$. The singular and regular sources are distinct.

Rows and columns of the following derivative table correspond to the
components of (41.2) and the coordinates $(x,r,b)$:

| Row | Column 1 | Column 2 | Column 3 |
| --- | --- | --- | --- |
| 1 | $[-0.6163686374,-0.6163686373]$ | $[0.0000000000,0.0000000000]$ | $[0.0000000000,0.0000000000]$ |
| 2 | $[-13.1260899408,-13.1260899407]$ | $[1.4029428989,1.4029428990]$ | $[1.1736542985,1.1736542986]$ |
| 3 | $[-6.2392534812,-6.2392534811]$ | $[-7.4720942075,-7.4720942074]$ | $[-6.1580532166,-6.1580532165]$ |

The coarser derivative table is not used to multiply $Y$. Direct interval
evaluation of the product gives the entrywise bound

$$
|I-YDH(B)|\le10^{-14}
\begin{pmatrix}1&0&0\\1&39&36\\1&47&43\end{pmatrix}.
\tag{42.1}
$$

At the rational center,

$$
\|YH(z_0)\|_\infty<10^{-40},\qquad
\sup_{z\in B}\|I-YDH(z)\|_\infty<10^{-8}.
\tag{42.2}
$$

Here is a finite exact arithmetic prescription for these bounds.
Use intervals on the grid $10^{-90}\mathbb Z$. Convert each rational
constant to its enclosing grid interval. Add endpointwise. For a product,
take the minimum and maximum of the four endpoint products and round
outward to the grid; for a reciprocal use $[l,u]^{-1}=[1/u,1/l]$ and
round outward, only when $lu>0$. Integer powers mean repeated products.
The bounds for the source coordinates are the exact center plus or minus
$10^{-22}$. Carry three derivative intervals, initially the coordinate
unit vectors; use the sum and product rules and
$\partial_i(f^{-1})=-f^{-2}\partial_i f$.
Evaluate $j,n,T,U,Z,R,\delta,\Lambda,D_0,q,k,c$ in the displayed order,
then $e_r$ and the responses. Evaluate the singular quantities by the
same formulas with $(r,b)=(x,1/8)$. Evaluate $\Phi$ as the expanded
sum in (41.1), its powers by repeated multiplication. Within a sum use
the written left-to-right order. Evaluate (41.2) and then the products
$I-YDH$ by increasing summation index. Evaluate $YH(z_0)$ afresh on
the singleton center. This uses only integer multiplication, division
with outward rounding and comparison. Induction on the formulas proves
that the prescription encloses every value and derivative. Applying it
gives (42.1), (42.2), and the source and response tables.

**Existence proof.** Let $N(z)=z-YH(z)$. Equations (42.1)–(42.2), the
mean value inequality and convexity of $B$ give

$$
\|N(z)-z_0\|_\infty
<10^{-40}+10^{-8}10^{-22}<10^{-22}.
$$

The same derivative bound gives Lipschitz constant less than $10^{-8}$.
Banach's contraction theorem gives a unique fixed point $z_*$ in $B$.
For any $z\in B$, the matrix $YDH(z)$ is invertible because its
distance from $I$ in operator norm is less than one. Hence the square
matrix $Y$ is invertible. A fixed point of $N$ is therefore exactly a
zero of $H$. This proves existence and uniqueness of that zero in $B$.
Its first coordinate $\alpha$ is an exact root of (41.1); the other
coordinates are denoted $r_*,b_*$. No floating-point approximation is
a premise of this existence proof. $\square$

## 43. Whole-world lift and response bounds

At $z_*$ put

$$
e_r=-D_0(r_*,b_*)/\Lambda(r_*,b_*),\qquad
e_s=P_*(r_*,b_*)/k_5(\alpha,1/8).
$$

Define $W_r=(P(r_*,b_*),g_r,24+e_r)$ and
$W_s=(P(\alpha,1/8),g_s,24+e_s)$, using precisely (40.1) for each
whole polynomial. These are strict complete worlds. Their nonzero
whole gains and all acquired original rows follow from (40.1)–(40.3).
The first component of (41.2) gives the singular parent equation, and the
regular parent equation follows from the definition of $e_r$.
The other two components and (40.6) give the equal acquired sixth reading
and equal terminal J reading; $e_s$ was defined to match the fifth reading.

The following bounds hold on the whole cube under the displayed formulas:

| Quantity | Regular world | Singular world |
| --- | --- | --- |
| $e$ | $[6.924912349392,6.924912349393]$ | $[6.688412836124,6.688412836125]$ |
| $d$ | $[30.924912349392,30.924912349393]$ | $[30.688412836124,30.688412836125]$ |
| $p$ | $[-10.891256858561706,-10.891256858561705]$ | $[-10.891256858561706,-10.891256858561705]$ |
| $v$ | $[-8.154074713130907,-8.154074713130906]$ | $[-8.154074713130907,-8.154074713130906]$ |
| $a$ | $[95.983033177664570,95.983033177664571]$ | $[95.983033177664570,95.983033177664571]$ |
| $m$ | $[104.820113396369830,104.820113396369832]$ | $[104.358640116727754,104.358640116727755]$ |

The intervals enclosing the true fixed-point values can be taken open:
the grid enclosures above strictly contain the exact interval arithmetic
endpoints. The theorem follows. The different widths establish
$W_r\ne W_s$, independently of all gain and drift comparisons.

## 44. A degree-seventeen mixed-incidence eliminant

The following is a polynomial characterization of every strict mixed
singular/regular J incidence with $p\ne24$, including the necessary
filters. It also specifies a width eliminant by a finite determinant.
Use independent polynomial variables $r,b$ and write

$$
\begin{aligned}
\mathcal J&=b^2+r(1-r),&\mathcal N&=\mathcal J+rb,\\
S&=(8b-1)(2+5b),\\
D&=5\{(b^2+8b+4)\mathcal J\mathcal N
 -2(1+b)(1+2b)b(\mathcal J+\mathcal N)\},\\
C_0&=-24D+3S\mathcal J\mathcal N,&C_1&=3S\mathcal Nb,\\
C_2&=3(49b+34)\mathcal J\mathcal N-54(1+2b)b(\mathcal J+\mathcal N),
&C_3&=3S\mathcal Jb,\\
B_5&=-4C_0+15C_1-20C_2+10C_3,\\
B_6&=-10C_0+36C_1-45C_2+20C_3,\\
B_7&=-20C_0+70C_1-84C_2+35C_3,\qquad L=bD,\\
N_p&=-bC_0+\{b(1+2b)+\mathcal N\}B_5,\\
N_v&=-bC_0+\{2b(1+2b)+\mathcal N\}B_6,\\
N_a&=-bC_0+\{b(1+b)+2\mathcal J+4rb\}B_7.
\end{aligned}
\tag{44.1}
$$

On $D\ne0$, substitution in (40.1) yields
$d=-C_0/D$, $g(i)=C_i/D$ for $0\le i\le3$, and
$(p,v,a)=(N_p,N_v,N_a)/L$.
Direct polynomial identities for the first five original rows are

$$
\begin{aligned}
-bC_0+\mathcal JC_1&=24bD,\\
-C_0+(1+b)C_2&=(147/5)D,\\
-bC_0+\mathcal NC_3&=24bD,\\
-C_0+(1+2b)(-C_0+4C_1-6C_2+4C_3)&=18D.
\end{aligned}
\tag{44.2}
$$

Fix any strict root $x$ of $\Phi$. All subsequent coefficient operations
are in $K=\mathbb Q[x]/(\Phi(x))$. The polynomial $\Phi$ is irreducible
over $\mathbb Q$. Its residue classes give the following singular
coefficients, equal to those in (40.5):

$$
\begin{aligned}
K_5&=\frac{17120}3x^3-\frac{108782}9x^2+\frac{85033}{12}x-\frac{216151}{288},\\
K_6&=\frac{109568}3x^3-\frac{1162456}{15}x^2+\frac{682643}{15}x-\frac{192731}{40},\\
K_J&=35952x^3-\frac{224750}3x^2+\frac{173289}4x-\frac{438635}{96},\\
C_6^s&=-192x^2+216x+63,\\
C_J^s&=-\frac{6144}5x^2+1536x+\frac{528}5.
\end{aligned}
\tag{44.3}
$$

These reductions follow by clearing $j^sn^s$ and reducing modulo (41.1).
For example $1/j^s+1/n^s=107/60$ gives
$q_5^s=71/18-5/j^s$, $q_6^s=43/3-16/j^s$,
$q_7^s=129/4-35/j^s$, from which (44.3) follows.

Define the explicit incidence polynomials

$$
\begin{aligned}
F_6&=K_5\{N_v-(24+C_6^s)L\}-K_6(N_p-24L),\\
F_J&=K_5\{N_a-(24+C_J^s)L\}-K_J(N_p-24L).
\end{aligned}
\tag{44.4}
$$

Both have degrees $(6,7)$ in $(r,b)$ over $K$. Let
$\mathcal R(b)=\operatorname{Res}_r(F_6,F_J)$, the determinant of
the $12\times12$ Sylvester matrix: its first six rows are shifted
coefficient vectors of $F_6$, and its last six rows those of $F_J$,
using descending powers of $r$. Then

$$
\mathcal R(b)=\lambda\,b^{20}(b+2/5)^4(b-1/8)^7 W_x(b),
\quad\lambda=[b^{48}]\mathcal R(b)\ne0,
\tag{44.5}
$$

where $W_x$ is monic of degree seventeen. Thus (44.1), (44.3)–(44.5)
already specify its coefficients without root selection or numerical
input. An explicit coefficient table is given below.

For precision, the finite algebraic verification of (44.5) consists of
forming the Sylvester determinant in $K[b]$, reducing powers of $x$
using (41.1), and exact polynomial division. The result has degree 48;
the exact orders at $0,-2/5,1/8$ are $20,4,7$. Division by these monic
factors leaves the degree-seventeen factor in the table, up to its
nonzero leading scalar. Comparing each remaining coefficient in the
basis $1,x,x^2,x^3$ verifies (44.5). Irreducibility of (41.1) is verified
by rational polynomial factorization, or the same exact field arithmetic
may instead be performed separately at each real algebraic root.

**Theorem 44.1 (filtered mixed incidence).** For a fixed strict singular root $x$,
every strict mixed J pair with $p\ne24$ determines a common real root
$(r,b)$ of (44.4) satisfying

$$
0<r<1,\quad b>0,\quad b\ne1/8,\quad D\ne0,\quad
K_5\ne0,\quad N_p-24L\ne0.
\tag{44.6}
$$

Its width obeys $W_x(b)=0$. Conversely every common real root of
(44.4) satisfying (44.6) lifts by (40.1), or equivalently (44.1), to a strict
mixed J pair, with

$$
p=N_p/L,\quad v=N_v/L,\quad e_s=(N_p-24L)/(LK_5).
$$

**Proof.** In the strict domain
$\Lambda=2D/(5TU\mathcal J\mathcal N)$, so $D\ne0$ is exactly the
regular-parent condition. If $b=1/8$ and the parent is regular, then
$e_r=0$ and $p=24$, which is excluded. On the singular line
$p-24=e_sK_5$; consequently $p\ne24$ forces $K_5\ne0$ and fixes
$e_s$ uniquely. Clearing the nonzero denominators in equality of $v$
and $a$ gives exactly (44.4); reversing the calculation proves sufficiency.
Distinctness follows from the unequal widths.
Sylvester's identity gives $\mathcal R(b)=0$ for a common root.
All three explicit factors removed in (44.5) are nonzero under (44.6),
so $W_x(b)=0$. $\square$

A zero of the width eliminant alone is not sufficient: one must recover
a common real $r$ and apply every filter (44.6). The factor $b=0$ violates
the source domain; $b=-2/5$ violates positive width; $b=1/8$ contains
the singular/diagonal locus and cannot supply the regular member at
$p\ne24$. The additional pole filter $D\ne0$ is indispensable even
after these width factors have been removed. This filtered statement
does not remove singular worlds or gain degeneracies from $C(p,v)$.

## 45. Exact width-polynomial coefficients

Write $W_x(b)=\sum_{i=0}^{17}A_i(x)b^i$. The following integers define
$A_i(x)=(n_{i0}+n_{i1}x+n_{i2}x^2+n_{i3}x^3)/d_i$.
Each displayed tuple has order $(d_i;n_{i0},n_{i1},n_{i2},n_{i3})$.

For $i=0$,

$$
(67246124332910802980604210887235399951260156961976925538419509496301608416980397621960011036222432056154438360520198715068421760376052708205398840908778835980889922172002679950881897625372193727667180297328011288763321683150320;
43750486655539851129138042116501264364704917566736504205222359441878607025990098404405390611971088286794548455610229364442913647961219210029494870650717956471071474585864593655787434949241031422077313917947847433569628127935,
89524090244897646185853951411701516800603935988048979895656744234204703977806215929614441534351812479339056079173603415820110381791892693425564624617030051145199219339608675008738778032504183761901703272367078121477119673696,
-1147810816324201050014253868883530219577594806060138397684781618162926726793126563082401481645887845248181560105081298224968026062645704089969926368606069875901384156575186244648803557906030595889008613999209452422966684960896,
1080479976399489383859190021529657313192264344332542171393507448590431686516616595486736356443723871831458567598450571900436807263286371278875640281903153855113740981058041470199322244680259042755231857388094922617254529209856).
$$

For $i=1$,

$$
(134492248665821605961208421774470799902520313923953851076839018992603216833960795243920022072444864112308876721040397430136843520752105416410797681817557671961779844344005359901763795250744387455334360594656022577526643366300640;
2848991576324044677403508436595055155802625244244120389618779666379820544128365236961342258933274908082171305914119844114317377895012716127959105488175885048014554820737370242095298388428764104348833923944515151349480886174597,
27819669940089173910680447150101385044473859642325285737504803747850106426475976552592482195906527161662825942776114342863744669846425627608576228693182467334136296005636978618292071663387508519598541721948499381512525188311840,
-96714200574063714760816239228094052036308395297620506522446342096746329320462688240676191652691009411031650009366260318439128666641890551284517974732177968526491352889304431945305387190215083735445232271256858471018131361863040,
66212625869364264886985301862675685550733791554770789392006397473741583839167045294475712324723717196864768314108782103547548189743747159174342302185670017925806807476449493629704670008443253125568406846874317807319454312141312).
$$

For $i=2$,

$$
(134492248665821605961208421774470799902520313923953851076839018992603216833960795243920022072444864112308876721040397430136843520752105416410797681817557671961779844344005359901763795250744387455334360594656022577526643366300640;
37393250267176234322471028246098188716608337036607892632102516875338579038001704976664818943890355806556676899157231618924949488862987005238057111370748325649965784416219853117991388396176786980448824947241359040629409722231401,
668523406380252184187179198924314325046250975992365512672913470321636074685589769700699321090978731700680081326239089804047097539187282975972936590232960720807219817066980005551248728002720738333161505790688120530746774535162656,
-1717402353330724579349091549477569549254257025791100118182409691090682331079753398406033234099276607251683679603555179686603361534648589109211289034213408235496602726100273321074384910994472836123291958585025924746385959847209856,
990340251179293482001684536991082250553379683331812266084187361721905312014224453974064963711341202668441287245588254705953365029310066964407530429977324232906791242652673727434216953715108083770446517034655644083624124031621632).
$$

For $i=3$,

$$
(268984497331643211922416843548941599805040627847907702153678037985206433667921590487840044144889728224617753442080794860273687041504210832821595363635115343923559688688010719803527590501488774910668721189312045155053286732601280;
500667605121175201856549906694246291487144289868988146727759015480117756069961190803536605171296608416106005375555772948856667497992212319597339192910503201718008187076504146647041279823756290207164666117898874220798962543120623,
13374027216072674620747961470229010872784763791049205818576503112508411965988780826148808622355821653722597283899876447254501428727787397191884386556932190041298992851563459224258581046765683376973422863521006293471496383962274400,
-29412036199110474227144362657264007548152244682515632575368466125261452583023019296338439306423644012844992083478967788574714161470964242642459935622264639332767342650160935440754101582943390014587434032433638307803163734291914880,
15228752989696541334490232192125921534913359887464117782300420022295999772434922178988439536943296845831582818778584040743169501577210393191949603383349612670517332704738625459538527305699480218295887343080876147533181717962536448).
$$

For $i=4$,

$$
(1075937989326572847689667374195766399220162511391630808614712151940825734671686361951360176579558912898471013768323179441094748166016843331286381454540461375694238754752042879214110362005955099642674884757248180620213146930405120;
6882379600092015170549801794615637151537694406679980896156133252150584304184750412013564100906028819490537899141693331999833364672790677638397348540225618585908903796590121453365745324102846748285136102946410310559097923350858259,
267948868186207302336500977717222053762252900089957399682972093681934491454597798357768582157554416969538392168770331774453107099705057153574537870561391876483555025467499629767167138445203493123783132091383163700454907414825121504,
-496082477090961816188585180868193692761298580087480961866517461351101474241477560912467296044632801061418909797085082116046582951913885401225764356529099931082700304111341011167722656308538768258065308507258731643181712208920997504,
221968882488353493641794376007698953173669343255875185968565209902077437004307910759901213461431267583195319245496691051746380984380014514441614050014763360156964675225571346958980133004370808704620618001126704757908893828464188928).
$$

For $i=5$,

$$
(430375195730629139075866949678306559688065004556652323445884860776330293868674544780544070631823565159388405507329271776437899266406737332514552581816184550277695501900817151685644144802382039857069953902899272248085258772162048;
3025362073328421022991200138522311661182502345990199649570118096948961945636020110727387000437064523184660438191445998287361057262280933452971061675782944188838877966761544563192081486806155295016966047429972023170215715288068629,
253526922460432017150803566579520289762260755978986826578550119134653435162244324365207723300165406263043017743078188318059649496375410366296981126703728237577535040269513141047055401073616834669323716227651145487220204430735755040,
-284184604305849976642628498669046221432570581098241832274373929925431177707940331698376543640971703050011957253075014119432286419974126181771409125178363645105286759426889536990880165600282543378757214472126093495029292923939712384,
44939948513252525529271556895259870683497634962435294627711382520852805935265943082562666934014295870381781012193606161123979582871833049159085143369664927565496311594426399288725926683155136287745062492755053859110605628978344448).
$$

For $i=6$,

$$
(358645996442190949229889124731922133073387503797210269538237383980275244890562120650453392193186304299490337922774393147031582722005614443762127151513487125231412918250680959738036787335318366547558294919082726873404382310135040;
-10229635617505741906483960391227267675987574828059823587357874779064534031450767569853334829241256872411078315084710162137080972208608050520065137520397882170313486820087193315605183831502433389438471844125169559619318033708221327,
-1030528289537206893747976118342205828596019840197430968450975472860826482614080753799690586327525199703219344439279412899893843339143963510489638765126015982309108422022485282148080325439859200635516708682109412534595818844582816,
846695979105968031015932753712734300986065206009608363685342873875248239069007018708718815173216766812605679878183447036013466995349518383828586111334284753676780567534825293936894483405373118135345756238265979774924105508725521536,
-759169753774997115552821468951118494505113266883368013276020003940078089693493845579612652658901941826586013728949160336354218268294110479241282496642106851909502819751858982292927617810903089221461384082662039035431626538288547328).
$$

For $i=7$,

$$
(2151875978653145695379334748391532798440325022783261617229424303881651469343372723902720353159117825796942027536646358882189496332033686662572762909080922751388477509504085758428220724011910199285349769514496361240426293860810240;
-298747878058434930696831875145074062373907387565214918934889377251538734447915906318715440604278349485154282431748062516682991229172402723900956765270940483739918461706219127643931266913456139749760000630052006136634257303492621555,
-8926694682001356462716717932094036884628251332138492333195398773446251833801734170570580264352826282671021773607607924750514374740622695218288615104660056679746246974950984747699961182617443725287686200865950091125416738100619803232,
31147229302679535525661257119447543926836554581729866602299151060558969519592485364874317617553963469435175856930431768614215340685491464944721263562943065310238849494715253497880854409332717810259865661066163237413978701233557313152,
-20648834771591159081014788204159561301046074345051062947419186595991832621793595950872128569008653204156989456985667816633397751851842467509827087599044991912921414720670692458477422816863912339833736361819279039015501650069799419392).
$$

For $i=8$,

$$
(1075937989326572847689667374195766399220162511391630808614712151940825734671686361951360176579558912898471013768323179441094748166016843331286381454540461375694238754752042879214110362005955099642674884757248180620213146930405120;
-317010018367097937834496324902504414798506781728099738932664215967307889324182560530344987923296749917960227622177551659533511343758207497034923845754801547757104995682281709318204222489226315086963990690834745215179897663885047247,
-14191874674459263341091017677778355731361926470708108081998047923059379575210886505193358518534536587732563076143407989588757571687881287989436581108038793036946683085925725659469389964287737273618650055704593488999826857498087520688,
40259058301584548647592285803845533567835005252760862162534777240091929324916642129122347390488493494461151353070161754033152916714783419624288317617171021058465620388620063486685210996232299608148753184925033968139381653912963823488,
-24582458109007842377885771480625618314714317549739755129509939059580598687804996352986815184580046203432882017123359340931092828454908028472963803825495947755703854569492431941850245264791481038680399644877144922178939771139792099840).
$$

For $i=9$,

$$
(67246124332910802980604210887235399951260156961976925538419509496301608416980397621960011036222432056154438360520198715068421760376052708205398840908778835980889922172002679950881897625372193727667180297328011288763321683150320;
-27152467176024783404491230013964318469768049452204887419402989332400903813628796286632010733339551766570253748612884155250323612855745205269562902422282009604331645587128747330551018548984034114183516681040672510131282013066252857,
-1582478547430317915704647745649286084931854441430312939341060426768267098791129176275650097713817788068410845880424991582974461392686332394102416926427838027822395798322384766011030777454255593503469053663915876721153243593194937849,
4207992477814192644584066326425221365746830742858965555857826568613133078809799172875211004028916164590968456721025574641299534123383965712536058099430433238798742043457453004938792580328658698068475102815123926103902861682055305744,
-2494882506100063164742868164328109300276228152845159255891373704894673312973600707372551575213692854178316752909380848335648870330282754845875708918084811573736807803167230015728403078666209889293224668012416556200847978093326134336).
$$

For $i=10$,

$$
(2151875978653145695379334748391532798440325022783261617229424303881651469343372723902720353159117825796942027536646358882189496332033686662572762909080922751388477509504085758428220724011910199285349769514496361240426293860810240;
-937161314922683735730934488851198341885990403622016079991927312646777735681482703881369055246225683939890690230920308858542808669389461373259542996842173031041258421021742250748036236903021473158477895263086324351545964119049462907,
-63463982978022351607573646182481363301276148280721788816697627509871718783669397332566176454190565606231476128852293874123920152543821719006501630111534230745300765204045302808315581133469442717939770150445411572732449021206388804992,
166759193124618689937952370898127825772975334307606572259470388271520944488899956646685031405547524933041315400468059380782770075737527430687792904961554717973317605627503628740685247727219699192326567612255369326574165784455791125632,
-98425414622817045886801639692746057636907167970638310365609635243738784257948808503915375444612022665123067986360134086228436572394360598437472007013391816557166093826133452231648305332275537093381308335493412091316636427840245896704).
$$

For $i=11$,

$$
(4303751957306291390758669496783065596880650045566523234458848607763302938686745447805440706318235651593884055073292717764378992664067373325145525818161845502776955019008171516856441448023820398570699539028992722480852587721620480;
-1758912747397709908793313675061890943122354031509230083480567860144833947662805244387610117225155457190513869359760253360774298129096404350813346369619617441399387793950164030767549361354052116953301537576062338797561541108660179943,
-123905521122580333141038976003160216174238151216764987981236365760974548868072695173370109907304461303768239614651372567348486053728787718333726516688982153349728732605375933527527142332463628752311135876519196867903448089879749571872,
321870583860582123655882175449698380424629417478061167891556651473522976557364850172639756748247964534074118940504183641989197559080013628676939276234630872525956576229386904610212721297320574326883222649024769070420720815183588629632,
-188999948112817912396358698467372618001777857549110588629861444236639257625025618970191837355375239061260457743378254933601123092862762162309257703743194247521537208871544595633701553111375573355003858285206339864154104046282114250240).
$$

For $i=12$,

$$
(134492248665821605961208421774470799902520313923953851076839018992603216833960795243920022072444864112308876721040397430136843520752105416410797681817557671961779844344005359901763795250744387455334360594656022577526643366300640;
-40862633709862355715203118473753811492715536643219803192746931351376892713234086730536705242410862468113735808533002712413616607239699103913454778221873154424181683020100882341902110311379201578041831846639781394504146729978303279,
-3000423077323773834704825723104587605285954464722735253288343626300446229658207210892291526626560210737098087321506144621494987877999722560699835188842767115692910833926861270574990936327775928666967838961741942409575592392866072053,
7464630941048818022651013947511275760563506467055948334469411763223961373848484510230652873419925447483732402029634391115544639337274621417277033495626329006063540958788635111362510722007158909862632056628218977439844123023294075728,
-4282060134634881548205983354388583045922213410633449073734182856847479872095779125383418958389884692292929384606907319759868062821484062623555663280213910911275429408681894801866789760775745643881147698341193033268965894709248052032).
$$

For $i=13$,

$$
(4303751957306291390758669496783065596880650045566523234458848607763302938686745447805440706318235651593884055073292717764378992664067373325145525818161845502776955019008171516856441448023820398570699539028992722480852587721620480;
-704573785669397452176197212600584160315024409164714626676072168144525204524344088789855699048230159151137079550097649153032456229107803775060209131845212554335055858422757561077827584480919789734472786536617609111720297891503306813,
-57314314859809250627754208283346467317943579448200376414381947155852917656348280556998557365873538063115811037075952103535870134087971588791456102262275438807359821246792937085470334503702128470666319593149460455334751140498546292864,
133945899506246485489846911927424753005002264697498295174776114220568357881005855900647366101392103608332470125179796879653680895305023564158334951684691660853468296170425212614304869115096825862529815680518627739961446804803012918144,
-73963597237317469821617362377944525961579096616885545527124216831403336277153845260724069669436976297266933452147296097362654862891980597309588859331394177544596089554081547924129662880280356911373805738237739880719571058331987098112).
$$

For $i=14$,

$$
(537968994663286423844833687097883199610081255695815404307356075970412867335843180975680088289779456449235506884161589720547374083008421665643190727270230687847119377376021439607055181002977549821337442378624090310106573465202560;
-39610382996726056960511496433914890130095739906838622083913052959760744068035056343570658985573252533603829960123373343256330212309933023796540170150996850967419195043805655296607691468088412161776130391272417969953715942518362935,
-3373850662079346814494013388520418227227237693641272216404441264649934924189443959277543757919015029410851374444530338740758619973244573831223555779196491219967623833416888867289152563151191436523253271762106579586526402737365298142,
7208443353520588010789011393987506379073461365617476670548777747297093517696253031816557036340326383827029354766855770745212611471708287380729608190672963482714129340183969670526031151166098633598969629379937256526153446524896485472,
-3737661313319035036843402562961220268376359174972761999725695778480576785926675388740255051986454002821054184306308726131405958757814826560562767877354692081103260195169070587405922788480926206115816257676927942754139642374278581632).
$$

For $i=15$,

$$
(2151875978653145695379334748391532798440325022783261617229424303881651469343372723902720353159117825796942027536646358882189496332033686662572762909080922751388477509504085758428220724011910199285349769514496361240426293860810240;
-56036863202592296758781410009310926312450391245849149771993792074038103853207627556493467620039866295463423495059478905944198851493968689688810617099334286061163018902351185936372745080927484748165648854208056738360559007239437589,
-4967693681255455708867746288188829721392918783996186454373665587221148881803185436870050830108077359921643910760757881355225605568082680102384573251615580227173087935589451906486972446116630338552471456681770700912196961601495015168,
9020636388461341833614909906599420979775245560732565080864578606906677448239285413642168736399283948608788260420369052083799160578435649449643012894858714504378879217315218996011031208349812978695354804553049803439100195452937982848,
-4073422490751312665159199190025417046314866470279249261418244439612497353360943218020688596947747723745247215846432083748316301030761565659168524147881266441631040097370370989844827675706610903095006652783565888243334605570443110912).
$$

For $i=16$,

$$
(268984497331643211922416843548941599805040627847907702153678037985206433667921590487840044144889728224617753442080794860273687041504210832821595363635115343923559688688010719803527590501488774910668721189312045155053286732601280;
-546955274201210991972279004794542754511823891380537412359669182542541607270539050446223475647488925066794646091997546001704781542215880188388425807321520546910785139849218469576675502235093352832837102727499820277999536362804483,
-114094516978629118892928889556516303310837496815192307254511101692735665325646943994918649645789383102428942447142651618991969326252138029165111585986579815420639311211933247727576000996979678045536875056460495628262412452537912256,
209770246196116299523558604768560378429092882718230692609323109690460160508371788572683880917811340731005338958041150784435733239377861881897014205816733007157764369040975792253688518322830914992358024586720987383144939261840043136,
-95367826791793132778106526455164023154719983417707756435856451364727971544892619188138258096933640165843885316852381809267972368595786572639236636531419136105749194018174028826753352742922217629412959584686131387758938363284801024).
$$

For $i=17$,

$$
(1;
1,
0,
0,
0).
$$

## 46. The independent M obligation

The full target requires some $p\ne24,v$ and independently distinct
pairs $W_0\ne W_1$, $W_2\ne W_3$ in the same entire $C(p,v)$, with
$a(W_0)=a(W_1)$ and $m(W_2)=m(W_3)$. Pair overlap is allowed, and
the two common terminal answers need not coincide.

The two worlds proved above supply the first pair. Their unequal M
readings prevent using this displayed pair as the second pair. No
exhaustion of the constructed child or absence of another M pair is
asserted. Existence of the independent M pair in this child, and the
original combined target, remain unresolved.

Lagrange interpolation, Sylvester's resultant identity, the mean value
inequality and Banach's contraction theorem are the classical tools
used in these proofs.

## 追加锚（本行以下为增补区）

