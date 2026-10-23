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

