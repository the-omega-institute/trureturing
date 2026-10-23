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

