# FIB common-parent geometry and two exact mixed children

## 1. Complete worlds and the equal-odd-read parent

**Definition 1.1 (Domain and inherited history).** This volume continues
[the entire-response volume](FIB_C35_ENTIRE_JM_RESPONSE_INJECTIVITY.md),
Definitions 1.1 and 1.3 and Sections 15–19. A world is the complete triple
$W=(P,g,d)$, where

$$
P=P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R.
\tag{1.1}
$$

Write $c=r(1-r)/b$. In particular $b,c$ have no imposed upper bound.
Sampled zeros, other roots, repeated roots, lower degrees and zero drift
belong to the domain. All four entries of $P$ are positive, its trace is
one, and its determinant is zero, so its rank is exactly one.

The actions, products and readings are

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
Q_0=I,\quad Q_i=E_iQ_{i-1},\quad
y_i=d+g(i)\operatorname{tr}(Q_iP).
\tag{1.2}
$$

The initial read counts. The original clocks are $0,\ldots,7$, with one
read immediately after each action. There is no reset, copy, skip, shifted
clock, additional port or acquisition of a gain, degree or source label.
Every acquired or alternative response of a world uses this same entire
$g$, fixed $d$ and fixed $P$.

For $\beta>0$ put

$$
\begin{gathered}
a=\frac{24}{5},\qquad h(s)=\frac85(s-1)(s-3)(s-5),\\
C_\beta=24+a(1+\beta),\qquad Y_\beta=24-a(1+2\beta),\\
H_{4,\beta}=(0,J,24,M,C_\beta,J,24,M,Y_\beta),\\
K_\beta=\{(P(r,\beta),h,24):0<r<1\}.
\end{gathered}
\tag{1.3}
$$

The family $K_\beta$ and its exact-gain fifth-J and fifth-M results are
inherited from the entire-response volume, Theorems 15.2–15.4. The target
throughout the two constructions below is the one literal parent

$$
\beta=\frac18,\qquad H_4=(0,J,24,M,147/5,J,24,M,18).
\tag{1.4}
$$

**Definition 1.2 (Complete-world guards).** Let $\mathcal F(H)$ contain all
complete worlds realizing the literal history $H$. For any finite or
infinite $S\subseteq\mathcal F(H)$ retain the original recursion

$$
\begin{aligned}
L_0(S,H)&\iff |S|\ge2,\\
L_{k+1}(S,H)&\iff |S|\ge2\ \land
\bigwedge_{E\in\{J,M\}}\exists u\in\mathbb R:\quad
L_k(S\cap\mathcal F(H,E,u),(H,E,u)).
\end{aligned}
\tag{1.5}
$$

Cardinality counts different complete triples. An empty or singleton
support fails every guard. Different terminal pairs are permitted, but
both terminal actions below an acquired child must use that child's one
acquired response. In particular a fifth-M $L_2$ has one shared fifth
response $p$ for both sixth actions.

**Definition 1.3 (Coordinates and actual M continuations).** Set

$$
j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\quad V=U+n.
\tag{1.6}
$$

The following inherited products are recorded to fix the response
functions used here. A word is chronological; its matrices act by the
left-product convention (1.2).

| Word | Product $Q$ | Trace against $P$ |
| --- | --- | --- |
| empty | $I$ | $1$ |
| $J$ | $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ | $j$ |
| $JM$ | $\left(\begin{smallmatrix}1&0\\1&1\end{smallmatrix}\right)$ | $T$ |
| $JMJ$ | $\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)$ | $n$ |
| $JMJM$ | $\left(\begin{smallmatrix}1&0\\2&1\end{smallmatrix}\right)$ | $U$ |
| $JMJMM$ | $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ | $V$ |
| $JMJMMJ$ | $\left(\begin{smallmatrix}3&1\\2&1\end{smallmatrix}\right)$ | $T+j+2r$ |
| $JMJMMM$ | $\left(\begin{smallmatrix}3&1\\5&2\end{smallmatrix}\right)$ | $2U+n$ |
| $JMJMMJJ$ | $\left(\begin{smallmatrix}2&1\\3&1\end{smallmatrix}\right)$ | $V$ |
| $JMJMMJM$ | $\left(\begin{smallmatrix}2&1\\5&2\end{smallmatrix}\right)$ | $2U+j$ |
| $JMJMMMJ$ | $\left(\begin{smallmatrix}5&2\\3&1\end{smallmatrix}\right)$ | $T+2j+4r$ |
| $JMJMMMM$ | $\left(\begin{smallmatrix}5&2\\8&3\end{smallmatrix}\right)$ | $3U+2n$ |

Thus, after the prescribed fifth M, define functions on a fixed world by

$$
\begin{aligned}
p(W)&=d+Vg(5),\\
u_J(W)&=d+(T+j+2r)g(6),&u_M(W)&=d+(2U+n)g(6),\\
f_{JJ}(W)&=d+Vg(7),&f_{JM}(W)&=d+(2U+j)g(7),\\
f_{MJ}(W)&=d+(T+2j+4r)g(7),&f_{MM}(W)&=d+(3U+2n)g(7).
\end{aligned}
\tag{1.7}
$$

The subscripts of $f$ specify the sixth and seventh actions. Alternative
values in (1.7) are not additional acquired observations.

## 2. A zero-safe full parent and its saturated direction

**Theorem 2.1 (Full parent converse).** Define

$$
\begin{gathered}
\epsilon=d-24,\quad\Delta=b-\beta,\\
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\qquad
B=\frac6T-\frac2U=\frac{2(2+5b)}{TU}>0.
\end{gathered}
\tag{2.1}
$$

The complete parent $\mathcal F(H_{4,\beta})$ is in bijection with triples
$(b,r,\epsilon)$ satisfying

$$
b>0,\qquad0<r<1,\qquad
\epsilon\Lambda+a(b-\beta)B=0.
\tag{2.2}
$$

For such a triple let $w$ be the unique polynomial of degree at most three
whose values at $0,1,2,3$ are

$$
(w_0,w_1,w_2,w_3)=
\left(-\epsilon,-\frac\epsilon j,
-\frac{\epsilon+a\Delta}{T},-\frac\epsilon n\right).
\tag{2.3}
$$

The corresponding world is exactly $(P(r,b),h+w,24+\epsilon)$.

Proof. The parent traces are $(1,j,T,n,U)$ and the first five samples of
$h$ are $(-24,0,a,0,-a)$. The first four original rows, after subtracting
$h$, are precisely (2.3). The last row requires

$$
w(4)=\frac{-\epsilon+2a\Delta}{U}.
\tag{2.4}
$$

For the four-node interpolant the fourth-difference identity gives

$$
\begin{aligned}
w(4)&=-w_0+4w_1-6w_2+4w_3,\\
w(4)-\frac{-\epsilon+2a\Delta}{U}
&=\epsilon\Lambda+a\Delta B.
\end{aligned}
\tag{2.5}
$$

Consequently (2.2) is necessary and sufficient for all five original
rows. The constructed source is legal by (1.1). If its entire $g=h+w$
were zero, the first two original responses would both equal $d$,
contradicting $0\ne24$. The degree bound is automatic. Conversely a
complete world fixes $b,r,\epsilon$, and its first four gain samples fix
its entire polynomial. This proves the asserted bijection, rather than
only an equation on projected parameters. The interpolation used here is
the fixed-node tool already used in the entire-response volume, §2.1;
see Berrut–Trefethen, *Barycentric Lagrange Interpolation*, §2. ∎

There is no division in this proof by $\epsilon$, $\Lambda$, a gain
sample, a leading coefficient, a root difference or a chart denominator
$D$. The exhaustive branches of (2.2) are

$$
\begin{array}{c|c}
\text{condition}&\text{consequence}\\ \hline
\epsilon=0&b=\beta,\quad w=0\\
b\ne\beta&\Lambda\ne0,\quad
\epsilon=-a(b-\beta)B/\Lambda\ne0\\
b=\beta,\ \Lambda\ne0&\epsilon=0\\
b=\beta,\ \Lambda=0&\epsilon\in\mathbb R\text{ arbitrary}.
\end{array}
\tag{2.6}
$$

In the last branch each value of $\epsilon$ is a different complete world
at the same source, with a nonzero entire gain by the original rows.

**Theorem 2.2 (Drift and entire-direction saturation).** Write $[g]=[h]$
when $g=\lambda h$ for one nonzero real scalar $\lambda$. For every
$\beta>0$,

$$
\mathcal F(H_{4,\beta})\cap\{d=24\}
=\mathcal F(H_{4,\beta})\cap\{g=h\}
=\mathcal F(H_{4,\beta})\cap\{[g]=[h]\}
=K_\beta.
\tag{2.7}
$$

Proof. The first branch of (2.6) proves the drift assertion and the
converse for $K_\beta$. If $g=h$, clock zero forces $d=24$. More generally
if $g=\lambda h$, clock one, where $h(1)=0$, forces $d=24$, and clock zero
then forces $\lambda=1$. This enlarges the inherited exact-gain slice
identity to both the fixed-drift slice and the entire proportional
class. ∎

In particular $q_1=(24-d)/j$ is allowed to vanish. At $\beta=1/8$ the legal
world

$$
P=\begin{pmatrix}1/2&1/8\\2&1/2\end{pmatrix},\qquad g=h,\qquad d=24
\tag{2.8}
$$

has exactly $H_4$ and $q_1=0$. Nonzero entire gain is not the assertion of
nonzero individual samples. The singular branch of (2.6) also retains
$d=0$ by taking $\epsilon=-24$.

## 3. Entire gain directions on the parent

**Theorem 3.1 (At most two worlds outside the saturated direction).** For
every $\beta>0$ and every nonzero real $f$ of degree at most three, put

$$
\mathcal D_f=\{(P,g,d)\in\mathcal F(H_{4,\beta}):g=\lambda f,
\ \lambda\ne0\}.
\tag{3.1}
$$

If $[f]=[h]$, this class is $K_\beta$. Otherwise it contains at most two
complete worlds. Both signs of $\lambda$ are allowed.

Proof. Write $f_i=f(i)$. If either $f_1$ or $f_3$ is zero in a nonempty
class, the corresponding row forces $d=24$, so Theorem 2.2 makes the class
$K_\beta$ or empty. Hence assume $f_1f_3\ne0$. Lift the source to

$$
R=\lambda P=\begin{pmatrix}u&v\\w&\mu-u\end{pmatrix},
\qquad\mu=\lambda\ne0,\qquad d=-f_0\mu.
\tag{3.2}
$$

For the chosen representative $f$, the lift and $d$ determine the
complete world injectively. The four parent rows after clock zero are

$$
\begin{aligned}
f_1(v+w)-f_0\mu&=24,\\
(f_2-f_0)\mu+f_2v&=C_\beta,\\
f_3(u+v+w)-f_0\mu&=24,\\
(f_4-f_0)\mu+2f_4v&=Y_\beta.
\end{aligned}
\tag{3.3}
$$

The odd rows imply

$$
u=\kappa(v+w),\qquad
\kappa=\frac{f_1}{f_3}-1=\frac rj>0
\tag{3.4}
$$

at every legal point. The even-row coefficient matrix in $(\mu,v)$ has
rank at least one: a zero first row would contradict $C_\beta>0$.
Rank two fixes $\mu,v$, after which the odd rows fix $u,w$. In the
consistent rank-one case $(\mu,v)$ lies on an affine line, and $u,w$ are
affine functions on it. Its determinant is a polynomial of degree at most
two. Unless that polynomial vanishes identically, it gives at most two
candidate lifts; all remaining legality conditions only delete them.

It remains to exclude a nonconstant determinant-zero line containing a
legal lift $R_0$. Factor $R_0=xy^{\mathsf T}$; all coordinates of $x,y$
are nonzero. If $R_0+tN$ has identically zero determinant and $N\ne0$,
then $\det N=0$. Factoring $N=ab^{\mathsf T}$, its mixed determinant
coefficient is
$(x_1a_2-x_2a_1)(y_1b_2-y_2b_1)$. Thus $N$ shares either the column factor
$x$ or the row factor $y$ with $R_0$.

On a shared-column line, (3.4) becomes the homogeneous row-factor equation

$$
(x_1-\kappa x_2)y_1-\kappa x_1y_2=0.
\tag{3.5}
$$

Its second coefficient is nonzero, so its kernel is one dimensional.
Both row factors lie in that kernel, forcing $N$ proportional to $R_0$.
For a shared-row line the corresponding column-factor equation is

$$
(y_1-\kappa y_2)x_1-\kappa y_1x_2=0,
\tag{3.6}
$$

and gives the same conclusion. But the first functional in (3.3) takes
value $24$ on $R_0$ and value zero on $N$, because the whole affine line
satisfies that row. Proportionality forces $N=0$, a contradiction. The
identically rank-one line therefore contains no legal point. This proves
the bound without a generic-rank, drift-sign or nonzero-$\Lambda$
hypothesis. The lifting and rank-one-line method is inherited from
[the promised-fiber volume](FIB_JMJM_PROMISED_FIBERS_AND_JOINT_EXCEPTION_GEOMETRY.md),
Theorem 4.1; (3.4)–(3.6) provide the equal-odd-read argument required here,
outside that theorem's $C=48$, $24<z<48$ hypotheses. ∎

**Theorem 3.2 (Direction injectivity at the target parent).** At $H_4$ of
(1.4), every direction other than $[h]$ contains at most one complete
world. The only nonsingleton direction fiber is $K_{1/8}$.

Proof. Suppose two worlds outside $K_{1/8}$ have proportional gains. If
the gains are identical, clock zero gives a common drift. Their samples
at one and three are nonzero by Theorem 2.2, so the odd rows fix $j,n$ and
$r=n-j$. At least one of the samples at two and four is nonzero, since
$C=147/5\ne Y=18$. That even row fixes $b$ and then $c$, giving the same
complete world.

For different scales write $g_2=\lambda g_1$, $\lambda\ne0,1$. Clock zero
gives $d_2=\lambda d_1$. If $d_1=0$, both drifts are zero, and the nonzero
responses $C,Y$ imply nonzero samples at two and four. Their equations
then give $T_1=\lambda T_2$, $U_1=\lambda U_2$. Since $U_i=2T_i-1$,
these force $\lambda=1$, a contradiction.

We may therefore normalize by the two nonzero drifts:
$f=g_1/d_1=g_2/d_2$, so $f_0=-1$. The even equations are

$$
C=(1+f_2)d+f_2(db),\qquad
Y=(1+f_4)d+2f_4(db).
\tag{3.7}
$$

Two different drifts give two different solutions $(d,db)$, forcing
coefficient rank one. Consistency gives
$2Cf_4=Yf_2$ and $C(1+f_4)=Y(1+f_2)$, whence

$$
f_2=\frac{19}{15},\qquad f_4=\frac{19}{49}.
\tag{3.8}
$$

At every legal solution in this direction,

$$
d=\frac{C}{1+(19/15)(1+b)}>0,\qquad
 d\{2(C-Y)(1+b)+Y\}=CY,\qquad d<Y<24.
\tag{3.9}
$$

Thus $f_1,f_3>0$ and $k=f_1/f_3-1=r/j>0$. The cubic
fourth-difference identity yields

$$
f_1+f_3=\frac{-1+6f_2+f_4}{4}=\frac{428}{245}=:K,
\quad f_1=K\frac{k+1}{k+2},\quad f_3=\frac K{k+2}.
\tag{3.10}
$$

The original first and second rows now give

$$
\begin{gathered}
j=\frac{125+152b}{147f_1}=a_0+qb,\qquad
q=\frac{190}{321}\frac{k+2}{k+1}>0,\qquad a_0=\frac{125}{152}q>0,\\
r=kj,\qquad c=j-b.
\end{gathered}
\tag{3.11}
$$

Source rank one is exactly the quadratic equation

$$
F_k(b)=k(a_0+qb)\{1-k(a_0+qb)\}-b\{a_0+(q-1)b\}=0.
\tag{3.12}
$$

Its leading coefficient is $-A$, where

$$
\begin{aligned}
A&=k^2q^2+q-1\\
&=\frac{36100k^4+144400k^3+102349k^2-23112k+18939}
{103041(k+1)^2}>0.
\end{aligned}
\tag{3.13}
$$

For the strict sign, the quadratic
$102349k^2-23112k+18939$ has discriminant $-7219386300<0$ and positive
leading coefficient. The remaining fourth and third degree terms are
positive for $k>0$.

If any legal $b>0$ exists, (3.11) gives $0<ka_0<r(b)<1$, hence
$F_k(0)=ka_0(1-ka_0)>0$. A quadratic with negative leading coefficient and
positive constant term has exactly one positive root. Consequently there
is at most one legal $b$, fixing $j,r,c,d$ and $g=df$. The two worlds
coincide, proving the theorem. The positive-drift conclusion (3.9) was
derived only under the hypothetical different-scale pair; it imposes no
restriction on individual worlds elsewhere in the full parent. In
particular no zero-drift or singular parent branch has been deleted. ∎

## 4. The complete fixed-width exceptional slice

**Theorem 4.1 (All $b=\beta$ worlds after fifth M).** For fixed
$\beta>0$, let $v_r$ interpolate

$$
v_r(0)=-1,\qquad v_r(1)=-1/j,\qquad
v_r(2)=-1/T,\qquad v_r(3)=-1/n,
\quad b=\beta.
\tag{4.1}
$$

Set

$$
\begin{aligned}
A_4(r)&=1+Uv_r(4)=U\Lambda,\\
A_5(r)&=1+(n+U)v_r(5),\\
v_r(4)&=1-4/j+6/T-4/n,\\
v_r(5)&=4-15/j+20/T-10/n.
\end{aligned}
\tag{4.2}
$$

The fixed-width parent is exactly
$(P(r,\beta),h+\epsilon v_r,24+\epsilon)$ with
$\epsilon A_4(r)=0$. Its fifth-M response is $24+\epsilon A_5(r)$.
For every real $p$ the complete slice

$$
S_p=\mathcal F(H_{4,\beta},M,p)\cap\{b=\beta\}
\tag{4.3}
$$

is $K_\beta$ when $p=24$. When $p\ne24$, it has one complete world for
each strict root $r\in(0,1)$ of $A_4(r)=0$, with
$\epsilon=(p-24)/A_5(r)$, and no other worlds. There are at most two such
roots.

Proof. Theorem 2.1 gives the fixed-width parent and (4.2) gives its fifth
response. On the entire domain $b>0$, $0<r<1$, the pair $(A_4,A_5)$ has no
common zero: this is exactly the M case of
[the terminal-zero-plane volume](FIB_TERMINAL_ZERO_PLANE_INVERSE_AND_J_PAIR_CHAMBER.md),
Theorem 9.2, equations (9.5)–(9.14), with the same $j,n,T,U$ and
$V_M=n+U$. That supplier imposes neither a chamber nor a gain or drift
condition and includes unbounded positive $b,c$. It therefore applies to
every fixed positive $\beta$ here. If $p=24$,
$\epsilon A_4=\epsilon A_5=0$ implies $\epsilon=0$. If $p\ne24$,
$\epsilon\ne0$, so $A_4=0$ and the displayed reconstruction is both
necessary and sufficient.

For the root bound, at fixed $b$ one has $j''=n''=-2/b$ and

$$
(1/j)''=\frac{2(j')^2}{j^3}+\frac{2}{bj^2}>0,
\qquad
(1/n)''=\frac{2(n')^2}{n^3}+\frac{2}{bn^2}>0.
\tag{4.4}
$$

Thus $A_4''=-4U\{(1/j)''+(1/n)''\}<0$. Three distinct zeros would
contradict strict concavity, so there are at most two. Original gain
zeros and degree drops do not affect this argument, and the original
rows exclude an identically zero gain for every reconstructed world. ∎

For completeness, the supplier's relevant obstruction is an exact
Sylvester resultant of its $N_4,N_{5,M}$:
$256b^{14}T^4U^2P_M(b)$. Its highest three terms are
$b^{14}(27b^2+198b-24294)$, negative for $0<b<4$, and all remaining
coefficients are negative. For $b\ge4$, $j,n>b$ instead give
$A_4>1+U(b^2-b-8)/(bT)>0$. These are the supplier's two exhaustive
ranges, not an assumption that the fixed-width roots are regular in any
other chart. Its Theorem 9.3 also supplies the already known same-source
uniqueness at $(H_{4,\beta},M,p)$: the sixth original row fixes the drift
even at a singular five-row source.

**Theorem 4.2 (Target exceptional roots and a safe fifth coefficient).**
At $b=\beta=1/8$, $A_4$ has exactly two roots $r_-,r_+$ in $(0,1)$.
They are the roots of

$$
\Phi(r)=438272r^4-931328r^3+540800r^2-50728r-853
\tag{4.5}
$$

isolated by either of the pairs of intervals

$$
\begin{aligned}
&\frac18<r_-<\frac17,\qquad
\frac9{10}<r_+<\frac{10}{11},\\
&\frac{134815}{10^6}<r_-<\frac{134816}{10^6},\qquad
\frac{902449}{10^6}<r_+<\frac{902450}{10^6}.
\end{aligned}
\tag{4.6}
$$

For both roots, writing $D_r=A_5(r)$,

$$
D_r<-\frac{6739}{30816}<0.
\tag{4.7}
$$

For every $p\ne24$, $S_p$ consequently consists of exactly the two
complete worlds

$$
W_r(p)=\left(P(r,1/8),\ h+\frac{p-24}{D_r}v_r,
\ 24+\frac{p-24}{D_r}\right),\qquad r=r_-,r_+.
\tag{4.8}
$$

Proof. Here $j=1/8+8r(1-r)$, $n=j+r$, $T=9/8$, $U=5/4$ and
$\Lambda=107/15-4/j-4/n$. Exact multiplication gives

$$
\begin{aligned}
\Phi&=64\{107jn-60(j+n)\},\\
\Lambda&=\frac{\Phi}{960jn},\qquad
2048jTnA_4=3\Phi.
\end{aligned}
\tag{4.9}
$$

Every displayed denominator is positive on $(0,1)$. The values of $A_4$
at $1/8,1/7,9/10,10/11$, respectively, are

$$
-\frac{19}{36},\qquad\frac{323473}{846948},\qquad
\frac{94967}{707772},\qquad-\frac{1962151}{4995204}.
\tag{4.10}
$$

Intermediate values give two roots; strict concavity from (4.4) proves
exhaustiveness. For the finer isolations, the values of $10^{24}\Phi$ at
the four fine endpoints in the order of (4.6) are exactly

$$
\begin{gathered}
-42530685653395898880000,\quad6072081656124845064192,\\
42022366160253876252672,\quad-19614556103500800000000.
\end{gathered}
\tag{4.11}
$$

Their signs isolate the same two roots without a numerical root choice.

At a root, $1/j+1/n=107/60$ and $n>j>0$. Hence $1/j>107/120$ and
$n>120/107$. Substitution in (4.2) gives

$$
v_r(5)=\frac{71}{18}-\frac5j<-\frac{37}{72},\qquad
D_r=1+(n+5/4)v_r(5)
<1-\left(\frac{120}{107}+\frac54\right)\frac{37}{72}
=-\frac{6739}{30816}.
\tag{4.12}
$$

Theorem 4.1 now gives (4.8), including the distinction of its two sources.
On the five-row parent these same two sources each allow every real
$\epsilon$, including $\epsilon=-24$ and $\epsilon=0$; the sixth original
row, not a nonzero-gain-sample premise, selects (4.8). The symbol $D_r$
here is the fifth-response coefficient $A_5(r)$, not a hypothesis
excluding the $D=0$ strata of another inverse chart. ∎

## 5. Necessary diversity for an actual fifth-M failure

**Theorem 5.1 (Full-width slice and direction obstructions).** For every
$\beta>0$ and every real $p$, the following hold at
$H_5=(H_{4,\beta},M,p)$.

1. Every support with $L_2$ has at least three different complete worlds.
2. No support contained in one entire gain direction has $L_2$.
3. No subset of $S_p$ in (4.3) has $L_2$. In particular an unrestricted
   $L_2$ support contains a world with $b\ne\beta$, and this world has
   $d\ne24$ and $[g]\ne[h]$.

At the target $\beta=1/8$ and $p\ne24$, the direction map is injective on
the entire fifth-M fiber. Therefore every $L_2$ support there contains at
least three distinct directions. This is a count of projective
directions, not a claim that the gains have linear span at least three.
At $p=24$, any $L_2$ support must still leave $K_{1/8}$.

Proof. The unrestricted exactly-two-world fifth-M classification is the
terminal-zero-plane volume, Theorem 8.2. It applies to any two different
complete worlds, including sampled zeros and arbitrary gain and drift,
without a chamber hypothesis. Its necessary relations at initial read
$a_0=0$ are $A=D$ and $z=D+(4D/7)n$, with $n=r+b+c>0$.
At the present parent $A=z=24$, they would give

$$
D=24,\qquad24=24+\frac{96}{7}n>24,
\tag{5.1}
$$

which is impossible. Empty and singleton supports fail the original
guards. This proves the first assertion; it does not extract a two-world
$L_2$ subset from a larger support.

By Theorem 3.1 a non-$h$ direction has at most two parent worlds, so the
first assertion excludes any $L_2$ support inside it. The $h$ direction
is exactly $K_\beta$ by Theorem 2.2. The entire-response volume, Theorem
15.4, excludes the entire fifth-M arm of this exact-gain family on every
subset. More explicitly, after an acquired sixth-J response $u$ its
final-J response $f$ satisfies the inherited joint inverse

$$
r=\beta+\frac{u-24}{24}-\frac5{384}(f-24).
\tag{5.2}
$$

Thus no final-J leaf inside one acquired sixth-J child contains a
distinct pair. Other fifth responses in this family are empty.

For $p\ne24$, Theorem 4.1 gives $|S_p|\le2$, so (5.1) and the guards
exclude $L_2$ on every subset. For $p=24$, $S_p=K_\beta$ and (5.2)
applies. This proves the third assertion. The final filters follow from
(2.6) and Theorem 2.2.

At the target, Theorem 3.2 gives one world per non-$h$ direction on the
whole parent. The exceptional class $K_{1/8}$ has fifth response exactly
$24$ and so is absent when $p\ne24$. Combining this injectivity with the
first assertion proves the three-direction requirement. No gain
direction has been acquired as data. ∎

The fixed-width and one-direction exclusions concern those restrictions.
They do not exclude all-external supports, any arbitrary $p\ne24$, or a
support whose worlds all share some fixed $b\ne\beta$. In particular the
necessary condition $b\ne\beta$ somewhere does not itself force two
different $b$ values.

## 6. Exact offslice coexistence and exclusion of that support

**Theorem 6.1 (A three-world common fifth history).** At $H_4$ let

$$
\begin{gathered}
P_* =\begin{pmatrix}1/2&1/4\\1&1/2\end{pmatrix},\qquad
d_* =\frac{11268}{515},\\
g_*(s)=\frac4{2575}(1087s^3-9459s^2+23549s-14085),\qquad
p_* =\frac{19224}{515}.
\end{gathered}
\tag{6.1}
$$

The three worlds $W_*=(P_*,g_*,d_*)$, $W_{r_-}(p_*)$ and
$W_{r_+}(p_*)$ are different legal members of the identical fiber
$\mathcal F(H_4,M,p_*)$. On this three-element support, each sixth response
$u_J$ and $u_M$ is injective. Hence the support has $L_0$ but no $L_2$.

Proof. The source $P_*$ is positive, trace one and determinant zero. The
single displayed gain is cubic and nonzero. Its samples at $0,\ldots,6$
are

$$
\frac1{2575}(-56340,4368,15492,3120,-6660,12240,85908).
\tag{6.2}
$$

The traces through clock five along $JMJMM$ are
$(1,5/4,5/4,7/4,3/2,13/4)$. With the same $d_*,g_*$ they give exactly

$$
(0,24,147/5,24,18,19224/515).
\tag{6.3}
$$

The two worlds of (4.8) use
$\epsilon_r=(p_*-24)/D_r=6864/(515D_r)$ and therefore realize these same
six rows. Their $r$ values differ, and their common $b=1/8$ differs from
$b_*=1/4$, so all three complete worlds are different.

To separate their sixth responses, at either exceptional root use

$$
\begin{aligned}
v_r(6)&=\frac{43}{3}-\frac{16}{j},\\
u_E(W_r(p_*))&=24+\epsilon_r+
 (24+\epsilon_rv_r(6))\tau_E,\\
\tau_J&=\frac98+j+2r,\qquad \tau_M=\frac52+n.
\end{aligned}
\tag{6.4}
$$

These formulas follow by interpolation and $1/j+1/n=107/60$.
Rational interval evaluation on the fine intervals (4.6) gives the
following outward bounds, all endpoints in this table divided by
$10^6$:

| Root | $D_r$ bounds | $u_J$ bounds | $u_M$ bounds |
| --- | --- | --- | --- |
| $r_-$ | $[-907756,-907661]$ | $[96550280,96559227]$ | $[140658649,140671133]$ |
| $r_+$ | $[-5216745,-5216552]$ | $[159307137,159311142]$ | $[176637264,176641677]$ |

For these bounds evaluate $j=1/8+8r(1-r)$ and $n=j+r$, then
$v_r(5)=71/18-5/j$, $D_r=1+(n+5/4)v_r(5)$,
$\epsilon_r=6864/(515D_r)$ and (6.4) in that order. Both $j$ and $D_r$
intervals exclude zero. Ordinary endpoint interval operations, or the
outward rational operations of Definition 7.2 below, give the displayed
bounds.

For $W_*$, the sixth traces are $7/2$ and $19/4$, so its exact responses
are

$$
u_J(W_*)=\frac{357018}{2575}\in(138,139),\qquad
u_M(W_*)=\frac{464403}{2575}\in(180,181).
\tag{6.5}
$$

For the exceptional worlds the table puts $u_J$ in $(96,97)$ and
$(159,160)$, and $u_M$ in $(140,141)$ and $(176,177)$, respectively.
For either action all three intervals are disjoint. Every acquired
sixth child within this specified support is therefore empty or
singleton. The recursive guards exclude $L_2$ on it. A larger support in
the same fiber can contain other worlds; no exclusion of that larger
fiber follows. ∎

## 7. Rational charts and the meaning of the child certificates

**Definition 7.1 (Regular construction chart).** Only for constructing
the worlds in Sections 8–9, set $\beta=1/8$ and use the open chart
$\Lambda\ne0$, with

$$
\epsilon=-\frac{24}{5}(b-1/8)\frac B\Lambda,\qquad
W(r,b)=(P(r,b),g,24+\epsilon),\qquad
 g(s)=h(s)+\sum_{i=0}^3w_i\ell_i(s),
\tag{7.1}
$$

where $w_i$ are (2.3) and
$\ell_i(s)=\prod_{0\le k\le3,\ k\ne i}(s-k)/(i-k)$.
The parent equation holds identically. In the formulas for its actual
responses use

$$
\begin{aligned}
g(5)&=-4w_0+15w_1-20w_2+10w_3,\\
g(6)&=24-10w_0+36w_1-45w_2+20w_3,\\
g(7)&=\frac{384}{5}-20w_0+70w_1-84w_2+35w_3.
\end{aligned}
\tag{7.2}
$$

All response functions below mean exactly (1.7) evaluated through
(1.6), (2.1), (2.3), (7.1), (7.2), with $B=6/T-2/U$. Thus their factorized
rational expressions are fixed, including the equations' scale and order.
This chart defines some legal worlds; it does not remove $\Lambda=0$ or
any $D=0$ worlds from the full unresolved problem.

**Definition 7.2 (Rational inclusion certificates).** All boxes below are
closed boxes in the infinity norm. To specify finite rational inclusions
unambiguously, one may use the grid $\sigma=10^{40}$. Enclose a rational
$x$ by
$[\lfloor\sigma x\rfloor,\lceil\sigma x\rceil]/\sigma$.
On grid intervals $[l,u]/\sigma$ and $[v,w]/\sigma$, addition and negation
are exact. Multiplication has integer endpoints

$$
\left[\left\lfloor\frac{\min(lv,lw,uv,uw)}\sigma\right\rfloor,
\left\lceil\frac{\max(lv,lw,uv,uw)}\sigma\right\rceil\right].
\tag{7.3}
$$

If $lu>0$, reciprocal has integer endpoints

$$
[\lfloor\sigma^2/u\rfloor,\lceil\sigma^2/l\rceil].
\tag{7.4}
$$

Each resulting pair is again divided by $\sigma$. Every operation is an
outward inclusion. No inversion of an interval containing zero is
permitted.

For derivative inclusions, an expression carries a value interval $v$
and a vector $\dot v$ of derivative intervals. The initial variable
$z_i$ carries the $i$th unit vector. Sum, product and reciprocal use

$$
\begin{aligned}
\dot{(v+w)}&=\dot v+\dot w,\\
\dot{(vw)}&=v\dot w+w\dot v,\\
\dot{(1/v)}&=-\dot v/(vv).
\end{aligned}
\tag{7.5}
$$

Apply these rules to the displayed rational expressions, preserving their
parentheses and evaluating unparenthesized sums and products from left
to right. In particular compute $\epsilon=((-a\Delta)B)/\Lambda$ and use
$B=6/T-2/U$ for the certificate inclusions. Each matrix dot product sums
its terms in increasing index order, starting from zero. These rules
enclose every derivative on the entire box. For an
interval $I=[a,b]$, let $|I|_{\max}=\max(|a|,|b|)$. For a matrix of
intervals take the maximum row sum of these bounds. The component bounds
below concern $CF(m)$, and the derivative bounds concern
$I-CDF(\mathcal B)$, with no rescaling of $F$.

The contraction inference used inside both child proofs is the following
standard argument. If $\mathcal B=\{z:\|z-m\|_\infty\le\rho\}$ contains
no poles and

$$
\sup_{z\in\mathcal B}\|I-CDF(z)\|_\infty\le q<1,\qquad
\|CF(m)\|_\infty\le\eta,\qquad \eta+q\rho<\rho,
\tag{7.6}
$$

then $T_F(z)=z-CF(z)$ is a contraction mapping the complete closed box
strictly into itself. Its unique fixed point is interior. At $m$,
$CDF(m)$ is invertible by the Neumann series since
$\|I-CDF(m)\|<1$, so the square matrix $C$ is invertible. Therefore fixed
points of $T_F$ are exactly zeros of $F$. This proves both existence and
uniqueness of the zero in the box. This is the ordinary Banach
contraction argument, also used in the entire-response volume, §§6–8;
it is an intermediate tool for the model-specific roots below.

The zero has real algebraic coordinates. Indeed, clearing nonvanishing
denominators gives rational polynomial equations. Together with the
rational box they define a semialgebraic singleton. Projection to each
coordinate preserves semialgebraicity over $\mathbb Q$, so each coordinate
is real algebraic. This uses precisely the singleton case of
Tarski–Seidenberg, as in the entire-response volume, Theorem 8.3; see
Bochnak–Coste–Roy, *Real Algebraic Geometry*, on semialgebraic projection.
Merely clearing denominators without box uniqueness would not establish
an isolated legal realization.

## 8. An exact all-external sixth-J child

**Theorem 8.1 (A strict sixth-J $L_1$ with three independent gains).**
There exist three different complete worlds at the literal $H_4$, all
with $b\ne1/8$ and $d\ne24$, sharing a fifth-M response $p_J$ and an
acquired sixth-J response $u_J$. In that acquired child $(W_0,W_1)$ is a
final-J collision pair and $(W_0,W_2)$ is a final-M collision pair. Their
entire gains are linearly independent. In particular this child has
$L_1$.

The worlds are specified exactly by $W_i=W(r_i,b_i)$ at the unique zero
in the following rational box. Set

$$
\begin{gathered}
z=(r_0,b_0,r_1,b_1,r_2,b_2),\qquad \rho=10^{-12},\\
m_J=10^{-18}
\begin{pmatrix}
371676286016453570\\158678203745512165\\
530842632335007806\\374463489524972148\\
657472562317377937\\380228166766336695
\end{pmatrix},\qquad
\mathcal B_J=\{z:\|z-m_J\|_\infty\le\rho\},\\
F_J(z)=\begin{pmatrix}
p(W_0)-p(W_1)\\p(W_0)-p(W_2)\\
u_J(W_0)-u_J(W_1)\\u_J(W_0)-u_J(W_2)\\
f_{JJ}(W_0)-f_{JJ}(W_1)\\f_{JM}(W_0)-f_{JM}(W_2)
\end{pmatrix}.
\end{gathered}
\tag{8.1}
$$

In particular $F_J$ has no numerical tolerance in its root definition.
Its preconditioner is the exact rational matrix

$$
C_J=10^{-6}
\begin{pmatrix}
1306677&-1590440&-321680&658574&-134468&-13531\\
582496&-696538&-143400&288425&-59944&-5926\\
2300789&-2727723&-625093&1129504&-206551&-23207\\
735386&-878880&-195199&363929&-69262&-7477\\
901345&-1100132&-221895&439607&-92756&-3923\\
196438&-237627&-48360&98469&-20215&-2820
\end{pmatrix}.
\tag{8.2}
$$

Proof. First every $(r_i,b_i)$ box lies strictly in $0<r<1$, $b>0$.
The following coarse rational bounds hold on the entire six-dimensional
box. Each entry is an open interval containing the corresponding value
interval; $i$ orders the worlds.

| $i$ | $b$ | $j$ | $n$ | $T$ | $U$ | $\Lambda$ | $d$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $0$ | $(15/100,16/100)$ | $(16/10,17/10)$ | $(2,21/10)$ | $(11/10,12/10)$ | $(13/10,14/10)$ | $(2,3)$ | $(23,24)$ |
| $1$ | $(37/100,38/100)$ | $(1,11/10)$ | $(15/10,16/10)$ | $(13/10,14/10)$ | $(17/10,18/10)$ | $(-1/2,-2/5)$ | $(32,33)$ |
| $2$ | $(38/100,39/100)$ | $(9/10,1)$ | $(16/10,17/10)$ | $(13/10,14/10)$ | $(17/10,18/10)$ | $(-7/10,-3/5)$ | $(30,31)$ |

These bounds follow by (7.3)–(7.4) applied first to
$c=r(1-r)/b$, $j,n,T,U$, then to $\Lambda,B,\epsilon,d$.
In particular all divisions in (7.1)–(7.2) and their derivatives exclude
zero before they are performed. The three $b$ boxes are disjoint, all
above $1/8$, and all three drifts differ from $24$.

Apply (7.5) to the ordered six expressions in (8.1). For row $i$ of
$I-C_JDF_J(\mathcal B_J)$ the sum of the six absolute endpoint bounds is
at most the $i$th entry in the second column below. The third column
bounds the corresponding component of $C_JF_J(m_J)$. The indicated
powers of ten divide the entire column.

| Row | Derivative row bound, denominator $10^8$ | Center displacement bound, denominator $10^{24}$ |
| --- | --- | --- |
| $1$ | $73281$ | $392384$ |
| $2$ | $108999$ | $155313$ |
| $3$ | $105149$ | $408614$ |
| $4$ | $89031$ | $62180$ |
| $5$ | $56944$ | $337919$ |
| $6$ | $115486$ | $45808$ |

This is finite rational arithmetic: evaluate (1.6), (2.1), (2.3),
(7.1)–(7.2), (1.7) on the six input intervals, propagate (7.5), and form
the matrix products with the exact $C_J$ in (8.2). At the singleton center
use the same expressions without derivative vectors. Thus the largest
bounds in the two columns give

$$
q_J=\frac{115486}{10^8}<\frac1{500},\qquad
\eta_J=\frac{408614}{10^{24}}<10^{-18},\qquad
\eta_J+q_J10^{-12}<10^{-12}.
\tag{8.3}
$$

The contractions and their zero equivalence follow from (7.6).
Consequently there is exactly one interior zero of $F_J$ in the box,
with algebraic coordinates as described after (7.6). Theorem 2.1 gives
three strictly legal complete parent worlds there; their entire gains
are nonzero by the original $0,24$ rows.

At that zero define

$$
p_J=p(W_0),\qquad u_J=u_J(W_0),\qquad
 a_J=f_{JJ}(W_0),\qquad a_M=f_{JM}(W_0).
\tag{8.4}
$$

Their strict rational bounds are in the following table. Both numerator
endpoints are divided by $10^8$.

| Response | Numerator interval |
| --- | --- |
| $p_J$ | $(2744214237,2744214238)$ |
| $u_J$ | $(11662210948,11662210950)$ |
| $a_J$ | $(29225404580,29225404583)$ |
| $a_M$ | $(36874488909,36874488912)$ |

These inclusions use the displayed $W_0$ expressions on the full box;
they do not assert that the same narrow intervals enclose the other
worlds' response functions away from the exact zero. At the zero the
six exact equations, not interval overlap, give

$$
\begin{aligned}
p(W_0)=p(W_1)=p(W_2)&=p_J,\\
u_J(W_0)=u_J(W_1)=u_J(W_2)&=u_J,\\
f_{JJ}(W_0)=f_{JJ}(W_1)&=a_J,\\
f_{JM}(W_0)=f_{JM}(W_2)&=a_M.
\end{aligned}
\tag{8.5}
$$

All three worlds therefore have literal prefix
$(0,24,147/5,24,18,p_J)$ and the same acquired sixth-J response.
Each pair displayed in (8.5) has different sources by the disjoint $b$
boxes. Both terminal leaves have $L_0$, and the sixth child is
nonsingleton, proving $L_1$. Additional interval bounds are

$$
285<f_{JJ}(W_2)<286,\qquad387<f_{JM}(W_1)<388.
\tag{8.6}
$$

They show that no two-world subset of this selected triple supplies
both terminal clauses. This is not a minimum-size statement about the
entire acquired child.

To verify the stronger gain-span assertion, form the sample matrix

$$
G=\begin{pmatrix}
g_0(0)&g_0(1)&g_0(5)\\
g_1(0)&g_1(1)&g_1(5)\\
g_2(0)&g_2(1)&g_2(5)
\end{pmatrix},\qquad g_i(0)=-d_i,\quad
 g_i(1)=-\epsilon_i/j_i.
\tag{8.7}
$$

Its entry intervals, with denominator $10^8$, are

$$
\begin{pmatrix}
[-2376200957,-2376200956]&[14596897,14596898]&[110865717,110865718]\\
[-3242580101,-3242580100]&[-810527804,-810527803]&[-150141200,-150141193]\\
[-3003405178,-3003405177]&[-620461407,-620461406]&[-76447600,-76447596]
\end{pmatrix}.
\tag{8.8}
$$

For a sharper determinant inclusion, evaluate the ordinary six-term
formula directly from the grid intervals for the unrounded expressions
in (8.7), before the coarser endpoint conversion in (8.8). It gives

$$
\frac{3025190882}{10^8}<\det G<\frac{3025192384}{10^8}.
\tag{8.9}
$$

The expressions, centers and endpoint rules fully specify these rational
bounds. A linear dependence among the three entire gains would give the
same dependence among the rows of $G$, contrary to (8.9). Hence the
entire gains are linearly independent. In particular each terminal
collision pair in (8.5) has nonproportional gains. This independence is
proved by the determinant, rather than inferred from distinct
directions. ∎

## 9. An exact mixed sixth-M child at fifth response twenty-four

**Theorem 9.1 (A mixed sixth-M $L_1$ at the same parent).** There exist
three different worlds $X,A,B$ in $\mathcal F(H_4,M,24)$ with a common
acquired sixth-M response. The final-J pair is $(X,A)$ and the final-M
pair is $(A,B)$, giving an actual $L_1$ child. The two worlds $A,B$ have
$g=h,d=24,b=1/8$; the third has $b\ne1/8,d\ne24$ and gain not
proportional to $h$.

The exact definition is the unique zero in $\mathcal B_M$ below:

$$
\begin{gathered}
z=(r,b,t),\quad\rho=10^{-12},\quad
m_M=10^{-18}\begin{pmatrix}
768583210418733285\\312445051052584098\\273384932776920629
\end{pmatrix},\qquad
\mathcal B_M=\{z:\|z-m_M\|_\infty\le\rho\},\\
X=W(r,b),\qquad A=W(t,1/8),\qquad B=W(9/8-t,1/8),\\
F_M(z)=\begin{pmatrix}
p(X)-24\\u_M(X)-u_M(A)\\f_{MJ}(X)-f_{MJ}(A)
\end{pmatrix},\\
C_M=10^{-6}\begin{pmatrix}
40943&-13829&1777\\-23754&10075&-1294\\14835&-1596&-952
\end{pmatrix}.
\end{gathered}
\tag{9.1}
$$

Proof. On this box $0<t<9/8-t<1$, $0<r<1$ and $b\in(31/100,32/100)$.
The following denominator and drift bounds hold on the entire box:

| World | $b$ | $j$ | $n$ | $T$ | $U$ | $\Lambda$ | $d$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $X$ | $(31/100,32/100)$ | $(8/10,9/10)$ | $(16/10,17/10)$ | $(13/10,14/10)$ | $(16/10,17/10)$ | $(-4/5,-3/4)$ | $(27,28)$ |
| $A$ | $1/8$ | $(17/10,18/10)$ | $(19/10,2)$ | $9/8$ | $5/4$ | $(2,3)$ | $24$ |
| $B$ | $1/8$ | $(11/10,12/10)$ | $(19/10,2)$ | $9/8$ | $5/4$ | $(1,2)$ | $24$ |

As before, evaluate source quantities and $\Lambda$ first, so no
interval reciprocal contains zero. In the last two worlds the factor
$b-1/8$ is exactly zero, giving $\epsilon=0$, $g=h$ and $d=24$
identically, even away from the root. All three sources are legal.
Their $r$ or $b$ boxes separate them.

The rational derivative and center-displacement bounds, in the same
convention as Section 8, are

| Row | Derivative row bound, denominator $10^8$ | Center displacement bound, denominator $10^{24}$ |
| --- | --- | --- |
| $1$ | $130856$ | $263303$ |
| $2$ | $131938$ | $93388$ |
| $3$ | $66536$ | $381079$ |

For these three rows evaluate the ordered expressions in (9.1), using
$t$ as the third variable; the constant $1/8$ has zero derivative. With
the same endpoint and derivative rules (7.3)–(7.5) this gives

$$
q_M=\frac{131938}{10^8}<\frac1{500},\qquad
\eta_M=\frac{381079}{10^{24}}<10^{-18},\qquad
\eta_M+q_M10^{-12}<10^{-12}.
\tag{9.2}
$$

The contraction argument (7.6) proves that the specified rational box
contains exactly one zero, strictly interior, with algebraic
coordinates. The parent converse constructs $X,A,B$ as complete worlds
at $H_4$ there. The first root equation fixes $p(X)=24$; the sampled zero
$h(5)=0$ gives $p(A)=p(B)=24$.

For fixed $b=1/8$, the function

$$
n(t)=\frac18+8t(1-t)+t
\quad\text{satisfies}\quad n(t)=n(9/8-t).
\tag{9.3}
$$

Thus $u_M(A)=u_M(B)$ and $f_{MM}(A)=f_{MM}(B)$ exactly, by (1.7) and their
common $h,d,b$. The two remaining root equations give
$u_M(X)=u_M(A)$ and $f_{MJ}(X)=f_{MJ}(A)$. Therefore all three worlds have
the same sixth-M response, and the two required terminal collisions lie
inside this one acquired child. Both pairs have different complete
worlds. All non-singleton guards hold, proving $L_1$.

For exact response bounds define $u_M=u_M(A)$,
$a_J=f_{MJ}(A)$ and $a_M=f_{MM}(A)$. The following strict numerator
intervals have denominator $10^8$:

| Response | Numerator interval |
| --- | --- |
| $u_M$ | $(13170119575,13170119576)$ |
| $a_J$ | $(45767957852,45767957853)$ |
| $a_M$ | $(61728765284,61728765286)$ |

These narrow enclosures are obtained from the expressions for $A$ on the
full box. The equalities with $X$ hold at the defining zero; the equality
with $B$ for $u_M,a_M$ holds by (9.3). In particular no overlap of
intervals establishes an equality. The other terminal values satisfy

$$
599<f_{MM}(X)<600,\qquad546<f_{MJ}(B)<547.
\tag{9.4}
$$

Together with the response table these show that no two-world subset of
this selected triple supplies both terminal clauses.

Finally $27<d_X<28$ gives $\epsilon_X\ne0$, so
$g_X(1)=-\epsilon_X/j_X\ne0$, whereas $h(1)=0$.
Thus $g_X$ is not proportional to $h$. The gains of this triple have
span exactly two: $A,B$ share $h$ and $X$ supplies a nonproportional gain.
The samples $h(1)=h(3)=h(5)=0$ remain literal zeros. Their retention is
compatible with every step of the proof. ∎

## 10. The precise shared-response obligation

**Definition 10.1 (The p-free eight-slot M system).** In the complete
zero-safe parameter space (2.2) at $\beta=1/8$, associate to each label
$(E,F,a)\in\{J,M\}^2\times\{0,1\}$ a triple
$x_{EFa}=(b_{EFa},r_{EFa},\epsilon_{EFa})$ and its reconstructed complete
world $W_{EFa}$ from Theorem 2.1. Require for every label

$$
b_{EFa}>0,\quad0<r_{EFa}<1,\quad
\epsilon_{EFa}\Lambda_{EFa}
+\frac{24}{5}(b_{EFa}-1/8)B_{EFa}=0.
\tag{10.1}
$$

The unresolved M system asks for one real $p$, one real $v_J$ and one real
$v_M$ such that

$$
\begin{aligned}
p(W_{EFa})&=p &&\text{for all }E,F,a,\\
u_E(W_{EFa})&=v_E &&\text{for all }E,F,a,\\
f_{EF}(W_{EF0})&=f_{EF}(W_{EF1})&&\text{for each }E,F,\\
(b_{EF0}-b_{EF1})^2+(r_{EF0}-r_{EF1})^2
 +(\epsilon_{EF0}-\epsilon_{EF1})^2&>0&&\text{for each }E,F.
\end{aligned}
\tag{10.2}
$$

The formulas for $p,u,f$ are the literal responses (1.7), using one
entire interpolant per label. Labels may reuse a world across slots;
the last line distinguishes complete worlds within each terminal pair.
By the bijection in Theorem 2.1, this three-coordinate guard is exactly
the complete-triple guard, including singular parent sources.

This is the M-only instance of the already published guarded finite-slot
argument, rather than a new finite-extraction theorem. The
entire-response volume, Theorem 16.5, states that argument for its
fifth-J atlas; the terminal-zero-plane volume, Theorem 11.2, states its
joint form at its chamber parents. Their chamber or fifth-action
hypotheses are not transferred here. For the present M instance,
unfolding (1.5) first selects the actual $v_E$, then a final response,
then two different worlds in that $L_0$ leaf, giving (10.2). Conversely
the finite union of the selected worlds has both terminal $L_0$ leaves
inside each single acquired $v_E$ child and hence $L_2$ under the common
$p$. Extra worlds preserve these witnesses by the recursive definition.
No losing pair has been extracted from a nonterminal support.

Theorem 5.1 permits the additional necessary filter that at least one
selected label has $b\ne1/8$. It does not replace any equation or guard
in (10.1)–(10.2). At $p\ne24$ at least three distinct gain directions
are necessary, but this also is not a substitute for the actual response
equalities.

**Definition 10.2 (Remaining common parent and original strategy
questions).** Theorem 8.1 has

$$
\frac{2744214237}{10^8}<p_J<\frac{2744214238}{10^8},
\qquad\text{whereas Theorem 9.1 has }p=24.
\tag{10.3}
$$

These are two actual $L_1$ children at the same $H_4$, but their fifth-M
histories differ. They do not provide a shared solution of (10.2),
regardless of how their terminal pairs are combined. Neither theorem
excludes another sixth child at its own fifth response. Thus feasibility
of the full p-free system remains open, including all-external
$d\ne24$ supports with $p\ne24$, disjoint terminal pairs, singular
interpolation strata, sampled zeros, repeated roots, lower degrees,
zero drift, unbounded offdiagonals and the $D=0$ strata of other charts.

The inherited fifth-J $L_2$ at this exact $H_4$ uses
$r=1/2,5/8,3/4$, $b=1/8$, $g=h$, $d=24$, fifth-J response $24$ and acquired
sixth responses $54,57$; it is the entire-response volume, Theorem 15.3.
A solution of (10.1)–(10.2) would supply the missing M arm and hence an
$L_3$ at this same parent. That $L_3$ is not supplied here. The separate M
parents in the entire-response volume, Sections 7–9, have different
literal parent rows and cannot be attached to this J arm.

All earlier ancestors and alternative actions, the original guarded root
$L_7$, unrestricted deterministic adaptive eight-read recovery or
impossibility, comparison with nine total readings and full-original-domain
nine-read sufficiency remain open. The strategy may be any deterministic
function of its acquired history. No continuity, measurability,
computability or finite-description restriction is imposed.

## 11. Mathematical scope and predecessor correspondence

**Definition 11.1 (Sources and scope of the consequences).** The
model-specific results of this volume are ordinary repository-derived
mathematics (`repo-derived`). The full parent relation and its converse,
drift and proportional saturation, direction bounds, fixed-width
exceptional classification, explicit offslice support and its exclusion,
and the two exact child constructions are consequences proved at the
specified model and literal histories. They carry no priority or
exhaustive novelty assertion. Their reusable tools and exact predecessor
hypotheses are as follows.

| Mathematical source | Use at its stated hypotheses |
| --- | --- |
| [Entire-response volume](FIB_C35_ENTIRE_JM_RESPONSE_INJECTIVITY.md), Definitions 1.1, 1.3 and Table 6.1 | Complete triples, original clocks, guards and actual M continuation products. |
| Entire-response volume, Theorems 15.2–15.4 | The inherited exact-$h$ family, accepted rational J arm and entire exact-$h$ M obstruction; none is asserted as a new construction here. |
| Entire-response volume, Theorem 16.5 | The same-child finite-slot reasoning; its stated atlas is for fifth J, so the present M equations are written explicitly from the recursion. |
| [Terminal-zero-plane volume](FIB_TERMINAL_ZERO_PLANE_INVERSE_AND_J_PAIR_CHAMBER.md), Theorem 8.2 | The unrestricted exactly-two-world fifth-M classification, used only through $A=D$, $z=D+(4D/7)n$; no chamber-only corollary is applied. |
| Terminal-zero-plane volume, Theorems 9.2–9.3, equations (9.5)–(9.19) | No common zero of the fourth and fifth-M drift coefficients on all strict sources, and already known six-row same-source uniqueness. |
| Terminal-zero-plane volume, Theorem 11.2 | Predecessor joint terminal-slot association at its chamber parents; it is not a chamber membership claim for $H_4$. |
| [Promised-fiber volume](FIB_JMJM_PROMISED_FIBERS_AND_JOINT_EXCEPTION_GEOMETRY.md), Theorem 4.1 | Prior affine lifting and determinant-line method at $C=48$, $24<z<48$; Theorem 3.1 supplies the distinct equal-odd-read proof needed here. |
| Berrut–Trefethen, *[Barycentric Lagrange Interpolation](https://doi.org/10.1137/S0036144502417715)*, §2 | `literature-attested` fixed distinct-node interpolation, used inside the parent reconstruction; it does not supply a common-history collision. |
| Banach contraction principle and the Neumann-series criterion | Standard complete-box existence and zero equivalence, with their hypotheses supplied by (8.3) and (9.2). |
| Bochnak–Coste–Roy, *[Real Algebraic Geometry](https://doi.org/10.1007/978-3-662-03718-8)*, semialgebraic projection | The rational semialgebraic singleton implies algebraic coordinates, after contraction uniqueness and nonzero denominators have been established. |

Generic inverse-problem, generic-rank or invertible-calibration results
are not suppliers for the two exact children or for (10.2). A
proportional direction is only an analytical partition, never an
observed label or a recovery protocol. Fixed-width, fixed-direction and
finite-support exclusions retain their displayed scope. The interval
certificates prove their stated rational inclusions, while all asserted
response equalities follow from exact root equations, original rows or
(9.3). The full strategy questions retain precisely the unresolved
quantifiers of Definition 10.2.

## 追加锚（本行以下为增补区）

## 12. A zero-safe source equation for every fifth-M response

Throughout Sections 12–17 the domain, original clocks, left products,
complete-world cardinalities and recursion are exactly Definitions
1.1–1.3, at the literal $H_4$ in (1.4). In particular the gain is one
entire nonzero real polynomial of degree at most three, and the drift is
one fixed real number in each world. No nonvanishing sample, exact degree,
simple-root, nonzero-drift, bounded-offdiagonal or regular-chart assumption
is added. Put $\beta=1/8$, $a=24/5$ and $\Delta=b-1/8$.

**Definition 12.1 (Polynomial source coordinates).** In addition to
$j,n,T,U,V$ in (1.6), set

$$
\begin{gathered}
X=b^2+r-r^2=bj,\qquad N=X+br=bn,\qquad W=N+bU=bV,\\
N_4=2(b^2+8b+4)XN-4bTU(X+N),\\
N_5=bTXN+W\{4(b+6)XN-5bT(3N+2X)\},\\
A_5=1+V(4-15/j+20/T-10/n),\qquad
B_{\rm coef}=6/T-2/U=\frac{2(2+5b)}{TU}>0.
\end{gathered}
\tag{12.1}
$$

The sextic used below is

$$
\begin{aligned}
H(r,b)={}&14b^6+(95-73r)b^5+(47r^2-39r+30)b^4\\
&+r(147r^2-232r+105)b^3
 +2r(1-r)(44r^2-55r+15)b^2\\
&-64r^3(1-r)^2b-32r^3(1-r)^3.
\end{aligned}
\tag{12.2}
$$

Here $H(r,b)$ is a polynomial, whereas $H_4$ is the acquired history.
For a real fifth response $p$, define the scalar polynomial

$$
\mathsf S_p(r,b)=5b(p-24)N_4+6(8b-1)H(r,b).
\tag{12.3}
$$

This notation distinguishes the source equation $\mathsf S_p=0$ from
the fixed-width set $S_p$ of (4.3).

**Lemma 12.2 (The nonzero drift-coefficient vector).** At every strict
source $0<r<1$, $b>0$,

$$
\Lambda=\frac{N_4}{TU XN},\qquad
A_5=\frac{N_5}{bTXN},\qquad
\Lambda^2+A_5^2>0.
\tag{12.4}
$$

Proof. All of $b,j,n,T,U,V,X,N,W$ are strictly positive before any
division. The first two identities follow by multiplication of these
positive denominators. For the last assertion use the full strict-source
M case of the terminal-zero-plane volume, Theorem 9.2. Its parameters
are $(A,C,z,Y)=(24,147/5,24,18)$, its fifth action is $F=M$, and its
$(X,N,W_M,N_4,N_{5,M})$ are exactly $(X,N,W,N_4,N_5)$ here. Its drift
coefficients are $a_4=U\Lambda$ and $a_{5,M}=A_5$. The supplier proves
$(a_4,a_{5,M})\ne(0,0)$ for all $0<r<1,b>0$, without a chamber, degree,
gain or drift restriction. Since $U>0$, (12.4) follows. Thus this use
includes the five-row singular stratum $\Lambda=0$; it is not a use of
a chamber-only inverse. ∎

**Theorem 12.3 (The p-free criterion and unique whole-world lift).**
A strict source $(r,b)$ admits a complete world in
$\mathcal F(H_4,M,p)$ if and only if $\mathsf S_p(r,b)=0$. That world is
unique at this source. Explicitly, put

$$
\begin{gathered}
K_5=20a\Delta V/T,\qquad Z=\Lambda^2+A_5^2>0,\\
\epsilon=
\frac{-a\Delta B_{\rm coef}\Lambda+A_5(p-24-K_5)}{Z}.
\end{gathered}
\tag{12.5}
$$

Let $g$ be the unique degree-at-most-three polynomial whose values at
$0,1,2,3$ are

$$
\left(-24-\epsilon,-\epsilon/j,
 (27/5-\epsilon)/T,-\epsilon/n\right).
\tag{12.6}
$$

Then the world is $(P(r,b),g,24+\epsilon)$. Formula (12.5) is valid also
when $\Lambda=0$.

Proof. Theorem 2.1 and the same four-node interpolation give, for these
one-polynomial, fixed-drift worlds, exactly the two remaining equations

$$
\epsilon\Lambda=-a\Delta B_{\rm coef},\qquad
\epsilon A_5=p-24-K_5.
\tag{12.7}
$$

For example the fifth gain extrapolation has weights
$(-4,15,-20,10)$, which gives the second equation. The clock-four gain
discrepancy is $\epsilon\Lambda+a\Delta B_{\rm coef}$, and its actual
response residual is $U$ times that discrepancy. Direct substitution
of (12.1)–(12.2) yields

$$
\Lambda(p-24-K_5)+a\Delta B_{\rm coef}A_5
 =\frac{\mathsf S_p(r,b)}{5bTU XN}.
\tag{12.8}
$$

The denominator is positive. Write $q=-a\Delta B_{\rm coef}$ and
$z=p-24-K_5$. The two equations $\epsilon\Lambda=q$,
$\epsilon A_5=z$ are consistent exactly when
$\Lambda z-A_5q=0$, since $(\Lambda,A_5)\ne(0,0)$. Their unique solution
is $(\Lambda q+A_5z)/Z$. More explicitly its two residuals are
$A_5(\Lambda z-A_5q)/Z$ and $-\Lambda(\Lambda z-A_5q)/Z$.
This proves both directions, including every zero coefficient case.

The original responses at clocks zero and one are $0$ and $24$, so the
reconstructed gain cannot be identically zero. Interpolation supplies
one entire polynomial, rather than separate late-row gains, and fixes
all its coefficients. If $\Lambda=0$, (12.7) forces $\Delta=0$ because
$aB_{\rm coef}>0$, while Lemma 12.2 gives $A_5\ne0$; the retained lift
is then $\epsilon=(p-24)/A_5$. No division by $\Lambda$, $\epsilon$ or
any gain sample is used. ∎

## 13. The entire twenty-four fiber as a set union

**Definition 13.1 (The odd-node interpolant).** At a strict source let

$$
\begin{aligned}
L_0(s)&=-\frac{(s-1)(s-3)(s-5)}{15},&
L_1(s)&=\frac{s(s-3)(s-5)}8,\\
L_3(s)&=-\frac{s(s-1)(s-5)}{12},&
L_5(s)&=\frac{s(s-1)(s-3)}{40},\\
v(s)&=-L_0(s)-L_1(s)/j-L_3(s)/n-L_5(s)/V.
\end{aligned}
\tag{13.1}
$$

Thus $v$ has values $(-1,-1/j,-1/n,-1/V)$ at $0,1,3,5$.
The remaining values needed here are

$$
\begin{aligned}
v(2)&=\frac15-\frac3{4j}-\frac1{2n}+\frac1{20V},\\
v(4)&=-\frac15+\frac1{2j}-\frac1n-\frac3{10V},\\
v(6)&=1-\frac9{4j}+\frac5{2n}-\frac9{4V},\\
v(7)&=\frac{16}5-\frac7j+\frac7n-\frac{21}{5V}.
\end{aligned}
\tag{13.2}
$$

Put $E_2=1+Tv(2)$ and $E_4=1+Uv(4)$. Expanding these expressions gives

$$
E_4+2E_2=-\frac{H(r,b)}{10XNW}.
\tag{13.3}
$$

**Theorem 13.2 (Full fiber and unique positive sextic graph).** For each
$0<r<1$, $H(r,b)=0$ has exactly one positive root, denoted $B_H(r)$.
It is simple, $B_H$ is continuously differentiable, and
$H_b(r,B_H(r))>0$. On every strict zero of $H$, $E_2\ne0$. Define

$$
\begin{aligned}
\epsilon_H(r)&=-\frac{a(B_H(r)-1/8)}{E_2(r,B_H(r))},\\
\mathcal H(r)&=
\bigl(P(r,B_H(r)),h+\epsilon_H(r)v_{r,B_H(r)},24+\epsilon_H(r)\bigr),\\
\mathcal K(t)&=(P(t,1/8),h,24),\qquad 0<t<1.
\end{aligned}
\tag{13.4}
$$

Then the entire complete-world fiber is exactly

$$
\mathcal F(H_4,M,24)
 =\{\mathcal K(t):0<t<1\}\ \cup\ \{\mathcal H(r):0<r<1\}.
\tag{13.5}
$$

This is a set union. At an intersection $B_H(r)=1/8$ the two formulas
represent the identical complete world and contribute one element.

Proof. The four actual rows at clocks $0,1,3,5$ force
$g=h+\epsilon v$, where $\epsilon=d-24$, by uniqueness at four fixed
distinct nodes. The clock-two and clock-four equations are precisely

$$
\epsilon E_2=-a(b-1/8),\qquad
\epsilon E_4=2a(b-1/8).
\tag{13.6}
$$

If $\epsilon=0$, these give $b=1/8$ and $g=h$, hence $\mathcal K$.
If $\epsilon\ne0$, their sum and (13.3) give $H=0$.

Before solving (13.6), suppose $H=0$ and $E_2=0$. Then $E_4=0$.
The nonzero polynomial $v$, with $v(0)=-1$, would satisfy
$1+\tau_i v(i)=0$ at all six original traces
$(1,j,T,n,U,V)$. Its first four values determine it. The clock-four and
clock-five drift-null discrepancies from that interpolant are
$a_4=U\Lambda$ and $a_{5,M}=A_5$, so both would vanish. This contradicts
Lemma 12.2. Therefore $E_2\ne0$ on every strict zero of $H$.
Conversely there (13.4) solves both (13.6) by (13.3), and all six original
rows hold for this one entire gain and fixed drift. The $0,24$ rows
again exclude an identically zero gain.

For existence and uniqueness of $B_H$, divide $H$ by the positive
$b^2$. For fixed $0<r<1$, its derivative is

$$
\begin{aligned}
\partial_b(H/b^2)={}&56b^3+3(95-73r)b^2
 +2(47r^2-39r+30)b\\
&+r(147r^2-232r+105)
 +\frac{64r^3(1-r)^2}{b^2}
 +\frac{64r^3(1-r)^3}{b^3}>0.
\end{aligned}
\tag{13.7}
$$

Indeed $95-73r>22$, and the quadratic discriminants for
$47r^2-39r+30$ and $147r^2-232r+105$ are respectively $-4119$ and
$-7916$, with positive leading coefficients. The function $H/b^2$
tends to $-\infty$ as $b\downarrow0$ and to $+\infty$ as
$b\to+\infty$. The intermediate value theorem and strict increase
give exactly one positive root. At it
$H_b=b^2\partial_b(H/b^2)>0$. The ordinary implicit function theorem
therefore gives compatible local continuously differentiable graphs;
uniqueness joins them over $(0,1)$, with $B_H'=-H_r/H_b$.
This proves (13.5) over the unbounded strict domain.

At $B_H(r)=1/8$, (13.4) has $\epsilon_H=0$, so both complete triples
are literally $\mathcal K(r)$. No gain direction, drift or sampled-zero
stratum has been quotiented out. ∎

The two curves have exactly two complete-world intersections. In fact

$$
\begin{aligned}
131072H(r,1/8)=Q(r)={}&4194304r^6-13631488r^5+14499840r^4\\
&-4799744r^3-344608r^2+86780r+1347.
\end{aligned}
\tag{13.8}
$$

The signed Sturm convention in Section 14 gives endpoint sign vectors
$(+,+,-,+,+,-,+)$ at zero and $(+,+,-,-,-,+,+)$ at one, with variations
$4$ and $2$. It ends at a nonzero constant. Thus there are exactly two
strict roots; Theorem 13.2 turns each into exactly one common triple.

## 14. Exact polynomial, elimination and interval certificates

**Definition 14.1 (Actual sixth-J response polynomials).** All polynomial
expressions in this section are in $\mathbb Z[r,b]$. With (12.1), set

$$
\begin{aligned}
D&=20XNW+T\{4XNW-b(15NW+10XW-XN)\},\\
D_d&=24D-12(8b-1)XNW,\\
A_6&=4XNW-b(9NW-10XW+9XN),\\
A_7&=16XNW-b(35NW-35XW+21XN),\\
G_6&=24D-3(8b-1)A_6,\\
G_7&=384D-12(8b-1)A_7,\\
U_n&=bD_d+(X+bT+2br)G_6,\\
F_n&=5bD_d+WG_7,\\
M_n&=5bD_d+(2bU+X)G_7.
\end{aligned}
\tag{14.1}
$$

On the strict $H=0$ graph, $D=20XNW E_2\ne0$ by Theorem 13.2.
Only after this nonzero denominator is established, the complete-world
reconstruction and its actual responses are

$$
\begin{gathered}
\epsilon=-\frac{12(8b-1)XNW}{D},\quad d=\frac{D_d}{D},\quad
 g(6)=\frac{G_6}{D},\quad g(7)=\frac{G_7}{5D},\\
u:=u_J=\frac{U_n}{bD},\qquad
f:=f_{JJ}=\frac{F_n}{5bD},\qquad
m:=f_{JM}=\frac{M_n}{5bD}.
\end{gathered}
\tag{14.2}
$$

In particular $m$ is the actual seventh-M response following the
acquired sixth J. It is not $f_{MM}$, which follows a different sixth
action.

Define $P_t$ and $G$ by the exact polynomial identities

$$
\begin{aligned}
12bP_t&=16U_n-F_n-216bD,\\
3(8b-1)G&=16U_nD-864bD^2-120bP_tD+3bP_t^2.
\end{aligned}
\tag{14.3}
$$

Both divisions are exact in $\mathbb Z[r,b]$: expansion and polynomial
long division in $b$ over $\mathbb Q[r]$ give zero remainders and integer
coefficients. Thus (14.3) defines polynomials even at $b=1/8$; it is not
a rational chart deleting that stratum. The joint coordinate is

$$
t_J=\frac{P_t}{32D}
 =\frac18+\frac{u-24}{24}-\frac5{384}(f-24).
\tag{14.4}
$$

The exact-$h$ responses, derived from the products in (1.7), are

$$
\begin{aligned}
u_K(t)&=54+240t-192t^2,\\
f_K(t)&=\frac{648}{5}+\frac{3456}{5}t-\frac{3072}{5}t^2,\\
m_K(t)&=\frac{1128}{5}+\frac{3072}{5}t-\frac{3072}{5}t^2.
\end{aligned}
\tag{14.5}
$$

They obey the joint inverse in (14.4), with $t_J=t$, and

$$
u-u_K(t_J)=\frac{3(8b-1)G}{16bD^2}.
\tag{14.6}
$$

Finally define

$$
\begin{aligned}
D_t={}&((P_t)_rD-P_tD_r)H_b-((P_t)_bD-P_tD_b)H_r,\\
D_u={}&((U_n)_r(bD)-U_n(bD)_r)H_b\\
 &-((U_n)_b(bD)-U_n(bD)_b)H_r,\\
L_{63}&=U_n-63bD,\\
A(r)&=3r^2-6r-1,\qquad C(r)=4r^2-2r-1.
\end{aligned}
\tag{14.7}
$$

Along $b=B_H(r)$, implicit differentiation gives

$$
\frac{dt_J}{dr}=\frac{D_t}{32D^2H_b},\qquad
\frac{du}{dr}=\frac{D_u}{(bD)^2H_b}.
\tag{14.8}
$$

Every denominator in (14.2), (14.4), (14.6), (14.8) is nonzero by
$b,X,N,W>0$, $D\ne0$, $H_b>0$. These statements hold on the entire
strict graph, including its intersections with $\mathcal K$.

**Lemma 14.2 (Four exact eliminants).** Use generic degrees in
$\mathbb Q(r)[b]$. For $\deg_b F=m$, $\deg_b Q=n$, define
$\operatorname{Res}_b(F,Q)$ as follows: the first $n$ rows of its
Sylvester matrix are the coefficients of
$b^{n-1}F,\ldots,F$, the next $m$ rows those of
$b^{m-1}Q,\ldots,Q$, and columns are in descending powers
$b^{m+n-1},\ldots,1$. With this fixed sign convention,

$$
\begin{aligned}
\operatorname{Res}_b(H,G)
 &=163840000r^{25}(r-1)^{21}A^2C^2P_{G,30},\\
\operatorname{Res}_b(H,D_t)
 &=-11744051200000000r^{28}(r-1)^{24}A^2C^2P_{t,42},\\
\operatorname{Res}_b(H,L_{63})
 &=298598400r^{14}(r-1)^{12}AC P_{63,18},\\
\operatorname{Res}_b(H,D_u)
 &=70135097956761600000000r^{34}(r-1)^{30}A^2C^2P_{u,42}.
\end{aligned}
\tag{14.9}
$$

Each remaining $P$ is defined canonically as this exact quotient,
including its displayed constant and sign. The descending integer
coefficient vectors below also specify them directly. No leading-sign
renormalization is implicit.

The coefficients of $P_{G,30}$, from highest degree to constant, are

$$
\begin{pmatrix}
160475958299501427217730026049372160000\\
-2816894296915766617823679710805295104000\\
3988812942423034688353149749532819456000\\
157614226729840319277746990295104779284480\\
-986795454916747289402023476723817935223296\\
1533164369629737329470682468295095782599744\\
2942104554982503960298594143424221604107120\\
-10185776055379595287151779807548209308407360\\
2975482182428031810646022848420196977210468\\
14149399978414103639074730579221656060613872\\
-8836925854105333809184276658589752555331901\\
-11367370575960112913930622272821654042804112\\
9823915412987443822703048559134812468204108\\
5966800661821094098229513460178869504904872\\
-7619531359180188613257235182494647217592678\\
-1283352018274395531694736911104249170846424\\
3872804507446524927771613589081984200449360\\
-403148844335413824043168861939761152768856\\
-1154056833200412077357705011978689469230565\\
312950734599328721637021863862172678289160\\
180458018791897282828761671511198053773352\\
-79335042219370470914193004821585890970976\\
-11113300297218468865538723661420060585744\\
10458748834469630514098074961553056106624\\
-125155194040328309698134009191347581952\\
-691642322868850107612845856253030030336\\
53714358228607082968556197486806834176\\
27943447438848906372121015990454624256\\
-630383171639504804462228669419880448\\
-293607936296038535432131534719025152\\
3515141684418585608035560736161792
\end{pmatrix}.
$$

The coefficients of $P_{t,42}$, from highest degree to constant, are

$$
\begin{pmatrix}
6163413632223572740574046062740847125787539200\\
-100757960532951181943359819326906831157226177280\\
808956312618016816312711364656378564589394458688\\
-4202318408915415516885399277451876055330670505280\\
15560791490724474096068944715545467164595069819888\\
-42575095955450545398199834916732962324946969783616\\
85641940641247209987331878449631413578110073496544\\
-117290708594297525508790050864125206430370327886464\\
69309629231163733890966821236738607672861858576784\\
129108384317158235460475435604354302580316735199392\\
-435664537501222728395253055625653810367177204480460\\
584297398347115458084165046195706578736142351104924\\
-220638527227508061191565024233811216282727891530096\\
-574020701925941098238056147937130453525519227929629\\
988848165273500543764727261259900812739335943869287\\
-401398375901009926414251930274035959709458946446597\\
-489658182901504820796258963555200577916765697114076\\
591417971127243653707959305810884120955442229381650\\
-102570604916197613117483452774666800168896234377040\\
-139318898015154912263034828735082085867277369412080\\
91134025295339660555760187869138716658471278144958\\
-62043595690934130039582437582546251955515542284875\\
22428815266068443404712389399793383607961338053663\\
40860971078452866541592983328740064847744625454566\\
-29347723212510678792001890814091015472208608782183\\
-11566909241023588705223457755488922474252981581096\\
10718652204956366196123522506894429158873818058959\\
2896937312023141458715605606008219148315426229136\\
-2390269146601603182494031833625726828109177143379\\
-671523625953748675491744449932255326000992946543\\
343483731476640161010575775155203384067615209216\\
105592163132805545503811158603068058170646411555\\
-17964321825755779748413629554600343394698225265\\
-8214873049568774845656791380385513277625057450\\
-3432627473181381297851185848456285348753973375\\
-330623688629864860051941730230681368988220100\\
659689479928227985183823887420832511431405625\\
163397437747425415009716587057435209953364375\\
-30252027140637589179924867931778321483376250\\
-14394507784462654971911045144727799799837500\\
-1454519003053883492389303848153838752000000\\
3589064178391418224237706090681212500000\\
4999228655839423000140078419040562500000
\end{pmatrix}.
$$

The coefficients of $P_{63,18}$, from highest degree to constant, are

$$
\begin{pmatrix}
1221329534834700\\
-149291214439371750\\
4802147351393893929\\
-15833826576722511453\\
3912889454327641879\\
11530962199583028862\\
71458419654320096318\\
-162462747654350800791\\
80404681930118097254\\
53346918809037607976\\
-68029377082304058771\\
18485876312820863395\\
7941728818023730843\\
-6095251301945485116\\
494956210735868828\\
407213269836914585\\
-129812163491177940\\
-21524372978812236\\
406514737962432
\end{pmatrix}.
$$

The coefficients of $P_{u,42}$, from highest degree to constant, are

$$
\begin{pmatrix}
51378082316293396955020918253803723121280\\
-572001386402718270739064202279587218406016\\
3257944956222552839044796964878393264536704\\
-11981654897026572579339731482458161737691232\\
22633106219381016961961285064531085175349432\\
-8060780035530710687601371191620402602574864\\
142497085061898103662610653180186955457221584\\
-1497618280503955740682747843428466334529205872\\
5217858169064316053913335174221775458410796708\\
-7165601257608577890430983457517246540854694636\\
-3123655205837678258969034818589257909131821915\\
22839580537529253201457088662624408145023705402\\
-21395865321649796092566981678458141591983051708\\
-15901280966091424665188627701802931207356628646\\
41197252592459171369975669108083272745477575037\\
-10811629550187709688647706821044910906005471024\\
-29148297494888701271611006097658450606602801519\\
19362876722369802517855384042349650009969838588\\
9470895420013867082977022643662105372705548322\\
-8847069560877641857561950162875983482738276314\\
-2998282169145456767310806371786148004850431023\\
860515146217848298962793023707884769138503846\\
2432112096095761772825711764111770826967891046\\
791499965158341716857502183712191946124609232\\
-1535500292345089531891975841553390508936700542\\
-519765816380998326994510573314864747085353348\\
592654549429046514354499629884065507258912913\\
211702970823895399378888063511573921121878790\\
-150379364404992019352079838638451367984559490\\
-64826048816298435802314822678080193506359034\\
24898604225218015583880942751611133889216153\\
14211175586197430262269051653020799285820640\\
-2218247682299559262165103144352952267433395\\
-2067926015593630174051811674641983550258700\\
-18183102269478263743121799699367497671000\\
174368267902835163574997130564124980087450\\
25778430800234292929883094468383945963125\\
-5139939954529138884392484914202746713750\\
-1868406266886633652274804721854973647500\\
-210336491784686763575016952479567950000\\
-9802515136668485259681141520752562500\\
119291348199870336605023545862500000\\
38939275750555238385896031375000000
\end{pmatrix}.
$$

Proof and coefficient-generation procedure. Expand (12.2), (14.1),
(14.3), (14.7) by integer polynomial arithmetic. The following degrees
and constant leading $b$ coefficients give a finite exact way to
generate every coefficient in (14.9):

| $Q$ | $\deg_b Q$ | $\deg_r Q$ | Leading $b$ coefficient | Bound $B_Q$ for resultant degree in $r$ |
| --- | --- | --- | --- | --- |
| $G$ | $14$ | $14$ | $28928$ | $168$ |
| $D_t$ | $18$ | $18$ | $-1384320$ | $216$ |
| $L_{63}$ | $8$ | $8$ | $-492$ | $96$ |
| $D_u$ | $20$ | $19$ | $3007872$ | $234$ |

Here $\deg_b H=\deg_r H=6$, with leading $b$ coefficient $14$.
Every determinant term uses $n$ coefficients of $H$ and six of $Q$,
so $B_Q=6n+6\deg_r Q$ is a valid degree bound. For each integer
$k=0,\ldots,B_Q$, evaluate the fixed Sylvester matrix at $r=k$ and
compute its integer determinant $v_k$. The constant nonzero leading
coefficients ensure that specialization has not changed either
$b$ degree. Put $\delta v_k=v_{k+1}-v_k$. The exact resultant is

$$
\sum_{i=0}^{B_Q}(\delta^i v)_0
 \frac{r(r-1)\cdots(r-i+1)}{i!},
\tag{14.10}
$$

where the $i=0$ factor is one. Divide this polynomial by the respective
constant and powers in (14.9); the remainder is zero and the quotient
is the displayed integer vector. Thus the four identities can also be
checked by integer determinants at respectively $169,217,97,235$
nodes: both sides have the stated degree bound, so equality at these
nodes proves polynomial equality.

For specificity those determinants require only fraction-free
elimination. Start with the integer matrix, previous pivot $q=1$ and
row-swap sign $+1$. At stage $k$ choose the first row $i\ge k$ with
nonzero column-$k$ entry and swap it into row $k$, updating the sign.
If none exists the determinant is zero. For pivot $p=M_{kk}$ replace
all trailing entries by
$(pM_{ij}-M_{ik}M_{kj})/q$ for $i,j>k$, then set $M_{ik}=0$ for $i>k$
and $q=p$. These divisions are exact. The signed last diagonal entry
is the determinant. This specifies the arithmetic in (14.10) without
an external elimination program. ∎

**Definition 14.3 (Signed Sturm and exact interval conventions).** For
any univariate polynomial $P$ in this certificate use $S_0=P$,
$S_1=P'$ and

$$
S_{i+1}=\operatorname{pp}_{+}
 \bigl(-\operatorname{rem}_{\mathbb Q[r]}(S_{i-1},S_i)\bigr).
\tag{14.11}
$$

Here $\operatorname{pp}_{+}$ multiplies by the positive least common
multiple of coefficient denominators and divides by the positive gcd
of the resulting integer coefficients. It preserves the sign of the
remainder; it never forces a positive leading coefficient. Stop at a
nonzero constant. To compute a remainder, repeatedly subtract the
leading-coefficient ratio times the required power of $r$ times the
divisor until the degree is smaller. Let $V_P(x)$ delete zero entries
from $(\operatorname{sgn}S_0(x),\ldots,\operatorname{sgn}S_\ell(x))$
and count sign changes. Sturm's theorem gives $V_P(l)-V_P(h)$ distinct
roots in $(l,h)$ when $P(l)P(h)\ne0$.

For interval arithmetic all endpoints are exact rationals, without
rounding. Use $[a,b]+[c,d]=[a+c,b+d]$,
$-[a,b]=[-b,-a]$, and

$$
[a,b][c,d]=[\min(ac,ad,bc,bd),\max(ac,ad,bc,bd)].
\tag{14.12}
$$

Only if $0\notin[c,d]$ may one use
$1/[c,d]=[1/d,1/c]$. For a polynomial, first expand in descending
powers of $b$, evaluate each coefficient by descending-$r$ Horner
starting at zero, then apply descending-$b$ Horner starting at zero.
Missing coefficients are zeros. For a rational expression first cancel
the polynomial gcd over $\mathbb Q[r,b]$, take relatively prime integer
numerator and denominator with joint positive content one and positive
leading denominator coefficient in descending $b$, then descending $r$
order, and evaluate each by this polynomial rule. Exclude zero from
the denominator interval before taking its reciprocal. Simultaneous
sign reversal of numerator and denominator has the same interval
quotient. These conventions apply to $u,t_J,m$ in (14.2), (14.4).

**Lemma 14.4 (Root coverage and uniform positive-root boxes).** The
four remaining factors in (14.9) are squarefree. Their signed Sturm
chains have degrees $d,d-1,\ldots,0$ for the respective $d=30,42,18,42$.
In the sign words below, each character is one entry in chain order;
`+` means $+1$, `-` means $-1$. All entries in these two tables are
nonzero.

| Polynomial | Endpoint | Sign word | Variation |
| --- | --- | --- | --- |
| $P_{G,30}$ | $0$ | `+-++--++-+---+--+-----+-+--+++-` | $17$ |
| $P_{G,30}$ | $1$ | `--++--++--+---+++-----+--------` | $10$ |
| $P_{t,42}$ | $0$ | `++--++-+++--+--+-++-+++--+++----+-++----+--` | $21$ |
| $P_{t,42}$ | $1$ | `--++--++----+--+-+++-+++--+++---+++-+----+-` | $20$ |
| $P_{63,18}$ | $0$ | `+-++-+-++-+++++-+++` | $10$ |
| $P_{63,18}$ | $1$ | `++-++-++--++-----++` | $8$ |
| $P_{u,42}$ | $0$ | `++--+--+---+-++--++-++-++++---+-+---+--++--` | $23$ |
| $P_{u,42}$ | $1/50$ | `+---+--+---+-++--++-++-++++---+-+---+--++--` | $23$ |

The following eighteen closed rational boxes locate the unique positive
$H$ root uniformly: if the row is $I\times[b_-,b_+]$, then for every
$r\in I$,

$$
H(r,b_-)<-10^{-18},\qquad H(r,b_+)>10^{-18},
\qquad B_H(r)\in(b_-,b_+).
\tag{14.13}
$$

The exact Horner interval for $D$ is strictly negative on every row,
so all $bD$, $5bD$, $32D$ denominators exclude zero. The reduced
rational denominators under Definition 14.3 also exclude zero before
division. The uniform statements include nonsingleton $r$ intervals,
not just their endpoints.

| Box | $I$ (closed $r$ interval) | Closed $b$ interval |
| --- | --- | --- |
| mixed-J-0 | $[11832337873/1000000000000,5916168937/500000000000]$ | $[607574573/50000000000,607574583/50000000000]$ |
| mixed-J-1 | $[28064490543/250000000000,112257962173/1000000000000]$ | $[5474852569/50000000000,5474852579/50000000000]$ |
| mixed-J-2 | $[382033189411/500000000000,764066378823/1000000000000]$ | $[15784094723/50000000000,15784094733/50000000000]$ |
| mixed-J-3 | $[404508497187/500000000000,1294427191/1600000000]$ | $[27854800451/100000000000,27854800471/100000000000]$ |
| mixed-J-4 | $[166575271517/200000000000,416438178793/500000000000]$ | $[12711262389/50000000000,12711262399/50000000000]$ |
| mixed-J-5 | $[423306831527/500000000000,169322732611/200000000000]$ | $[11936168489/50000000000,11936168499/50000000000]$ |
| mixed-J-6 | $[852550131301/1000000000000,426275065651/500000000000]$ | $[11584194453/50000000000,11584194463/50000000000]$ |
| mixed-J-7 | $[53398688069/62500000000,170875801821/200000000000]$ | $[11473692397/50000000000,11473692407/50000000000]$ |
| t-critical-0 | $[48477521251/1000000000000,12119380313/250000000000]$ | $[1222396553/25000000000,611198279/12500000000]$ |
| t-critical-1 | $[404508497187/500000000000,1294427191/1600000000]$ | $[27854800451/100000000000,27854800471/100000000000]$ |
| t-sign | $[1/2,1/2]$ | $[17824908901/50000000000,17824908911/50000000000]$ |
| level-63-0 | $[1074995933/62500000000,17199934929/1000000000000]$ | $[1761817253/100000000000,1761817273/100000000000]$ |
| level-63-1 | $[404508497187/500000000000,1294427191/1600000000]$ | $[27854800451/100000000000,27854800471/100000000000]$ |
| level-63-2 | $[212946149973/250000000000,851784599893/1000000000000]$ | $[23260318869/100000000000,23260318889/100000000000]$ |
| u-positive-derivative | $[1/100,1/100]$ | $[205575539/20000000000,205575543/20000000000]$ |
| u-above-63 | $[1/50,1/50]$ | $[204585273/10000000000,8183411/400000000]$ |
| mixed-pair-existence-0 | $[1479/125000,1479/125000]$ | $[243022931/20000000000,1518893319/125000000000]$ |
| mixed-pair-existence-1 | $[11833/1000000,11833/1000000]$ | $[12152167677/1000000000000,12152167679/1000000000000]$ |

The polynomial Horner ranges on these boxes are enclosed by the closed
intervals in the next table. The rational inclusions are strict; here
$m=f_{JM}$ and $t=t_J$.

| Box | Polynomial | Enclosing interval | Rational bounds |
| --- | --- | --- | --- |
| mixed-J-0 | $G$ | $[-112567437/1000000000000000000000000,7027157/62500000000000000000000]$ | $62<u<63$; $17/500<t_J<7/200$; $221<m<223$ |
| mixed-J-1 | $G$ | $[-271/25000000,-1083/100000000]$ | — |
| mixed-J-2 | $G$ | $[-218244137/20000000,-545610259/50000000]$ | — |
| mixed-J-3 | $G$ | $[-330603833/50000000,-132241491/20000000]$ | — |
| mixed-J-4 | $G$ | $[-41840839/10000000,-418408151/100000000]$ | — |
| mixed-J-5 | $G$ | $[-297365263/100000000,-18585313/6250000]$ | — |
| mixed-J-6 | $G$ | $[-125668669/50000000,-10053483/4000000]$ | — |
| mixed-J-7 | $G$ | $[-14874997/6250000,-237999687/100000000]$ | — |
| t-critical-0 | $D_t$ | $[1/2500000,41/100000000]$ | — |
| t-critical-1 | $D_t$ | $[3574629543/50000000,3574636833/50000000]$ | — |
| t-sign | $D_t$ | $[4011250937/100000000,2005625543/50000000]$ | — |
| level-63-0 | $L_{63}$ | $[-546280593249/1000000000000000000000000,592718570237/1000000000000000000000000]$ | — |
| level-63-1 | $L_{63}$ | $[-615171239/100000000,-123034247/20000000]$ | — |
| level-63-2 | $L_{63}$ | $[-39041769/12500000,-312334149/100000000]$ | — |
| u-positive-derivative | $D_u$ | $[838394413/1000000000000000000000000,52412811/62500000000000000000000]$ | — |
| u-above-63 | $D_u$ | $[883991159541/1000000000000000000000000,884039536079/1000000000000000000000000]$ | $63<u<64$ |
| mixed-pair-existence-0 | $G$ | $[856837/125000000000000000000000,140897/15625000000000000000000]$ | — |
| mixed-pair-existence-1 | $G$ | $[-4161293/250000000000000000000000,-2896277/200000000000000000000000]$ | — |

Every isolating interval used in the global root counts has the
following individual variation pair and full endpoint signs. The
polynomial column names the remaining factor, not its bivariate
pre-elimination polynomial.

| Polynomial | Box's $r$ interval | Lower sign word | Upper sign word | $(V(l),V(h))$ |
| --- | --- | --- | --- | --- |
| $P_{G,30}$ | mixed-J-0 | `+-++--+--+-+++-++---+++-+--+++-` | `--++--+--+-+++-++---+++-+--+++-` | $(17,16)$ |
| $P_{G,30}$ | mixed-J-1 | `-+--++-++-++--++-+++++-+--++++-` | `++--++-++-++--++-+++++-+--++++-` | $(16,15)$ |
| $P_{G,30}$ | mixed-J-2 | `+--++-++--+--++--+++--+--++++--` | `---++-++--+--++--+++--+--++++--` | $(15,14)$ |
| $P_{G,30}$ | mixed-J-4 | `-++--++-++-+++--+-----+--++++--` | `+++--++-++-+++--+-----+--++++--` | $(14,13)$ |
| $P_{G,30}$ | mixed-J-5 | `+--++--+--+---+++--+++-++++++--` | `---++--+--+---+++--+++-++++++--` | $(13,12)$ |
| $P_{G,30}$ | mixed-J-6 | `-++--++-++-+++---+++++-++------` | `+++--++-++-+++---+++++-++------` | $(12,11)$ |
| $P_{G,30}$ | mixed-J-7 | `+--++--+--+---+++-----+--------` | `---++--+--+---+++-----+--------` | $(11,10)$ |
| $P_{t,42}$ | t-critical-0 | `+-++--+---+++-+--+--+++--+++----+-++----+--` | `--++--+---+++-+--+--+++--+++----+-++----+--` | $(21,20)$ |
| $P_{63,18}$ | level-63-0 | `+-+-++-++-+++++-+++` | `--+-++-++-+++++-+++` | $(10,9)$ |
| $P_{63,18}$ | level-63-2 | `-+--+-++--++-----++` | `++--+-++--++-----++` | $(9,8)$ |
| $C$ | mixed-J-3 / t-critical-1 / level-63-1 | `-++` | `+++` | $(1,0)$ |

For the elementary factors the chains are $(A,6r-6,1)$ and
$(C,8r-2,1)$. For $A$ the sign vectors at $0,1/50,1$ are respectively
$(-,-,+),(-,-,+),(-,0,+)$, all with variation one. For $C$ they are
$(-,-,+),(-,-,+),(+,+,+)$, with variations $1,1,0$. Thus $A$ has no
strict root, $C$ has exactly one strict root and neither has a root in
$(0,1/50)$. The $C$ root is precisely the one in the common
mixed-J-3, t-critical-1 and level-63-1 interval.

Proof. Apply (14.11) with rational polynomial remainders to the
coefficient vectors. Each final constant is nonzero, giving
squarefreeness, and the sequence degrees and endpoint words give the
stated variations. In particular $P_{G,30}$ has seven roots in $(0,1)$,
all accounted for in mixed-J-0,1,2,4,5,6,7; $P_{t,42}$ has one, in
t-critical-0; $P_{63,18}$ has two, in level-63-0 and level-63-2; and
$P_{u,42}$ has none in $(0,1/50)$. These disjoint isolating intervals
each have variation drop one, and their drops sum to the global counts,
so no other root in the stated ranges is omitted.

For (14.13), apply the exact Horner rule to $H(I,b_-)$ and $H(I,b_+)$.
Its upper bound in the first case is less than $-10^{-18}$ and its
lower bound in the second is greater than $10^{-18}$ on every row.
Theorem 13.2 then places the positive root inside the row for the
whole $r$ interval. The same Horner rule gives the displayed polynomial
bounds and a negative interval for $D$. Reduce the rational expressions
as specified, check their denominator intervals first, and use
(14.12) to obtain the strict rational bounds. Thus all of these
inclusions are specified by rational endpoints and finite arithmetic.

The interval from the singleton $r$ of mixed-pair-existence-0 to that
of mixed-pair-existence-1 contains exactly one $P_{G,30}$ root:
its endpoint variations are $(17,16)$, and mixed-J-0 is strictly
inside it. Also level-63-0 lies strictly below $1/50$. These rational
comparisons will distinguish actual zeros from projected roots in
Section 15. ∎

## 15. The entire p24 sixth-J exclusion

**Theorem 15.1 (Joint injectivity on each curve).** The map
$W\mapsto(u_J(W),f_{JJ}(W))$ is injective on each of the two sets in
(13.5). Moreover $r\mapsto t_J(\mathcal H(r))$ is strictly increasing
on the whole interval $(0,1)$.

Proof. On $\mathcal K$ the identity (14.4) recovers $t$ exactly; this
is the parameter correspondence $\beta=1/8$ in the entire-response
volume, Theorem 15.4, equation (15.12). Thus its joint map is injective.
For $\mathcal H$, a zero of $D_t$ on its graph would make the second
resultant in (14.9) vanish. Since $r\in(0,1)$ and $A$ has no root there,
its coordinate must be the one root of $P_{t,42}$ or the one root of
$C$. Lemma 14.4 locates these in t-critical-0 and t-critical-1. The
uniform positive-root brackets and the strictly positive $D_t$ bounds
in both boxes exclude a zero on the actual positive $H$ graph. These
projected roots are therefore spurious for criticality on that graph.

There are no other candidates. The graph is connected, and $D_t$
is continuous and nowhere zero on it. The t-sign box at $r=1/2$
shows its sign is positive. Since $D^2>0$ and $H_b>0$, (14.8) makes
$t_J$ strictly increasing throughout $(0,1)$. Equal $u_J,f_{JJ}$
therefore give equal $t_J$, hence equal $r$, equal positive root $b$
and the identical reconstructed complete world. This proof uses no
bounded segment of the graph and makes no genericity deletion. ∎

**Theorem 15.2 (Exactly one legal distinct final-J pair).** In the full
fiber $\mathcal F(H_4,M,24)$ there is exactly one unordered pair of
different complete worlds having both a common acquired sixth-J
response and a common final-J response. It is a mixed pair
$\{X_0,Y_0\}$, defined as follows. Let $(\alpha,b_0)$ be the unique
positive-graph solution of $H=G=0$ in mixed-J-0, and put

$$
\begin{gathered}
e_0=-\frac{12(8b_0-1)XNW}{D}\bigg|_{(\alpha,b_0)},\qquad
 t_0=\frac{P_t}{32D}\bigg|_{(\alpha,b_0)},\\
X_0=(P(\alpha,b_0),h+e_0v_{\alpha,b_0},24+e_0),\qquad
Y_0=(P(t_0,1/8),h,24).
\end{gathered}
\tag{15.1}
$$

These definitions give actual complete worlds. In particular

$$
\begin{gathered}
\frac{11832337873}{10^{12}}<\alpha<\frac{11832337874}{10^{12}},\qquad
\frac{1215149146}{10^{11}}<b_0<\frac{1215149166}{10^{11}},\\
\frac{34}{1000}<t_0<\frac{35}{1000},\qquad
62<u_J(X_0)=u_J(Y_0)<63,\qquad
f_{JJ}(X_0)=f_{JJ}(Y_0).
\end{gathered}
\tag{15.2}
$$

Proof. By Theorem 15.1 two different worlds in one of the curves cannot
form such a pair. Choose an $\mathcal H$ member and a $\mathcal K$
member. If the first has $b=1/8$, it is itself a $\mathcal K$ world by
Theorem 13.2, and joint injectivity again makes the pair identical.
Thus a distinct mixed pair necessarily has $b\ne1/8$.

Equality of $u,f$ forces the $\mathcal K$ parameter to be exactly
$t_J$ by (14.4). With the already nonzero $bD^2$ and now $8b-1\ne0$,
(14.6) forces $G=0$. Conversely, $G=0$ and $0<t_J<1$ imply
$u=u_K(t_J)$ by (14.6); the defining affine identity (14.4) then gives
$f=f_K(t_J)$. This proves equivalence to the actual joint-response
collision, rather than only to a necessary projection equation.

The first resultant in (14.9) and Lemma 14.4 exhaust the possible
strict $r$ coordinates: the seven $P_{G,30}$ roots in mixed-J-0,1,2,4,5,6,7
and the one $C$ root in mixed-J-3. In boxes 1 through 7 the exact bound
for $G$ is strictly negative at every point of the box. The uniform
positive-$H$-root bracket therefore excludes each candidate on the
actual graph. Only mixed-J-0 can remain.

Actual existence follows from the last two boxes of Lemma 14.4.
At $r=1479/125000=11832/10^6$, $G(r,B_H(r))>0$; at
$r=11833/10^6$, it is negative. The continuous positive graph gives
an actual zero between them. This coarse interval contains exactly
one $P_{G,30}$ root, already isolated in mixed-J-0, and contains no
$A$ or $C$ root. Thus the actual zero has its $r$ coordinate in that
fine box and is unique. Uniqueness of $B_H$ fixes its $b$ coordinate.
The box bounds give $0<t_0<1$, $b_0\ne1/8$ and $62<u<63$.

Theorem 13.2 supplies all six original acquired rows of $X_0$ at
clocks $0,\ldots,5$, with one nonzero entire gain and fixed drift;
$Y_0$ has the same rows by (1.3). Their sources differ because
$b_0\ne1/8$. The exact $H=G=0$ identities give both response
equalities. No numerical proximity or interval overlap is used to
establish them. All other distinct pairs have already been excluded. ∎

**Lemma 15.3 (No third world and unequal actual final-M responses).**
At $u_0=u_J(X_0)$ the entire acquired child is exactly

$$
\mathcal F(H_4,M,24,J,u_0)=\{X_0,Y_0\},
\qquad f_{JM}(X_0)\ne f_{JM}(Y_0).
\tag{15.3}
$$

Proof. A point on the positive $H$ graph with $u=63$ must satisfy
$L_{63}=0$. Its resultant in (14.9) permits only the two roots of
$P_{63,18}$ and the one root of $C$. The first $P_{63,18}$ root is
in level-63-0, strictly below $1/50$. At the two remaining projected
coordinates, level-63-1 and level-63-2 have $L_{63}<0$ throughout the
uniform positive-root boxes, excluding actual level-63 points. Thus
$u$ never equals $63$ on $[1/50,1)$. At $1/50$ the u-above-63 box gives
$63<u<64$. Continuity on that connected interval proves $u>63$
everywhere on $[1/50,1)$.

On $(0,1/50)$ the $D_u$ resultant cannot vanish: the endpoint factors
are absent, $A,C$ have no roots there, and $P_{u,42}$ has variation
difference zero. Therefore $D_u$ has no zero on this graph portion.
The u-positive-derivative box at $r=1/100$ gives $D_u>0$. Equation
(14.8) proves strict increase of $u$ there. Consequently every $u<63$
has at most one $\mathcal H$ world on the entire graph.

On $\mathcal K$, $u_K$ is strictly increasing on $(0,1/4)$ since
$u_K'=240-384t>0$ there. On $[1/4,1)$ its concavity and the values
$u_K(1/4)=u_K(1)=102$ give $u_K\ge102$. Hence a response in $(62,63)$
has at most one $\mathcal K$ world. Theorem 15.2 already supplies one
world from each curve at $u_0$. The complete-fiber set union (13.5),
with intersections counted once, leaves no third world.

The actual seventh-M response of $X_0$ is $m=M_n/(5bD)$, not a
refitted gain value; mixed-J-0 gives $221<m(X_0)<223$. From (14.5)
and $34/1000<t_0<35/1000$,

$$
m_K(t_0)>
\frac{1128}{5}+\frac{3072}{5}\frac{34}{1000}\frac{965}{1000}>245.
\tag{15.4}
$$

More precisely the same interval operations give
$3839976/15625<m_K(t_0)<3849576/15625$, both in $(245,247)$.
The two actual final-M responses are therefore different. ∎

**Theorem 15.4 (Every acquired sixth-J child fails L1 at p24).** For
every real acquired sixth-J response $u$ and every finite or infinite
support $S\subseteq\mathcal F(H_4,M,24,J,u)$,

$$
\neg L_1(S,(H_4,M,24,J,u)).
\tag{15.5}
$$

Consequently for every $S\subseteq\mathcal F(H_4,M,24)$,

$$
\neg L_2(S,(H_4,M,24)).
\tag{15.6}
$$

Proof. An $L_1$ child must have a distinct pair in a final-J leaf and
a distinct pair in a final-M leaf, with both pairs in that child's one
acquired $u$ fiber. If $u\ne u_0$, Theorem 15.2 excludes even the
final-J pair. If $u=u_0$, Lemma 15.3 says the full child has exactly
two worlds and their final-M responses differ, so no subset has a
final-M pair. Empty and singleton supports also fail the original
nonsingleton guard. This proves (15.5).

For fifth-M $L_2$, the sixth-J conjunct of (1.5) requires one acquired
$u$ child with $L_1$. None exists by (15.5), proving (15.6). The proof
allows different terminal pairs, overlapping or disjoint pairs, all
reuse of worlds and infinite supports. It does not extract a losing
two-world support from a nonterminal support. The uniqueness of the
final-J pair is used together with the complete two-world child and
the actual final-M separation; uniqueness alone would not suffice. ∎

## 16. Whole mirror components in the full-parent MM correspondence

**Definition 16.1 (Coefficient topology and ordered collisions).** Give
complete worlds the Euclidean topology of the four entries of $P$,
the four real coefficients of $g$ padded by zero, and $d$. The parent
$\mathcal F(H_4)$ carries the relative topology. On it put

$$
\begin{gathered}
p=d+(U+n)g(5),\qquad u=u_M=d+(2U+n)g(6),\\
f=f_{MM}=d+(3U+2n)g(7),\qquad k=f-\frac{32}{5}u.
\end{gathered}
\tag{16.1}
$$

These are actual functions of the same whole gain and fixed drift at
the original clocks $5,6,7$ along $JMJMMMM$. In this section $u,f$
have this sixth-M meaning, in contrast to the sixth-J functions in
Sections 14–15. Define the full ordered collision correspondence

$$
\mathcal C_{MM}=\{(W,W')\in\mathcal F(H_4)^2:
 W\ne W',\ p(W)=p(W'),\ u(W)=u(W'),\ f(W)=f(W')\}.
\tag{16.2}
$$

Equality of $(p,u,f)$ is equivalently equality of $(p,k,u)$.
The common responses are allowed to vary over $\mathcal C_{MM}$.
Writing $A_r=\mathcal K(r)$ and $s=9/8-r$, put

$$
\begin{aligned}
\Gamma_+&=\{(A_r,A_{9/8-r}):1/8<r<9/16\},\\
\Gamma_-&=\{(A_r,A_{9/8-r}):9/16<r<1\}.
\end{aligned}
\tag{16.3}
$$

**Lemma 16.2 (Full-parent homeomorphism and b-dependent chart).** Set

$$
\begin{gathered}
R_0(b,r,\epsilon)=\epsilon\Lambda+a(b-1/8)B_{\rm coef},\\
\mathcal X=\{(b,r,\epsilon):b>0,\ 0<r<1,\ R_0=0\}.
\end{gathered}
\tag{16.4}
$$

The reconstruction of Theorem 2.1 is a homeomorphism from
$\mathcal X$ onto the entire complete parent. Near every $A_r$, all
parent worlds have a smooth chart $(r,\epsilon)$ with
$b=b(r,\epsilon)$, including when $\Lambda(r,1/8)=0$. At the exact-$h$
curve this chart satisfies

$$
b(r,0)=1/8,\qquad b_r(r,0)=0,\qquad
b_\epsilon(r,0)=-\frac{25}{448}\Lambda(r,1/8).
\tag{16.5}
$$

Proof. Theorem 2.1 gives a bijection by one whole four-node
interpolant. Its coefficients are continuous rational functions of
$(b,r,\epsilon)$ with positive $b,j,n,T$ denominators; the source and
drift are continuous as well. The inverse is continuous coordinate
extraction $(b,r,\epsilon)=(P_{12},P_{11},d-24)$. This proves the
homeomorphism in complete-coefficient topology, with no quotient by
gain direction or omission of the gain.

The function $R_0$ is smooth on the open domain $b>0$, $0<r<1$,
$\epsilon\in\mathbb R$. At $A_r$, $B_{\rm coef}=56/15$ and

$$
\partial_bR_0=aB_{\rm coef}=\frac{448}{25}>0.
\tag{16.6}
$$

The implicit function theorem with dependent variable $b$ gives
exactly all nearby zeros, not just a selected parent subfamily. At
$\epsilon=0$, $a(b-1/8)B_{\rm coef}=0$ and $B_{\rm coef}>0$ force
$b=1/8$. Differentiation gives (16.5). Its nonzero IFT derivative is
$\partial_bR_0$, not $\partial_\epsilon R_0=\Lambda$; in particular
there is no division by $\Lambda$. The legal singular fixed-source
lines of (2.6) are included in this chart. ∎

**Lemma 16.3 (Derivatives from the same entire gain).** In the chart
of Lemma 16.2 take a dot to mean $\partial_\epsilon$ at $\epsilon=0$
and fixed $r$. On this curve write

$$
\begin{gathered}
j=1/8+8r(1-r),\qquad n=j+r,\qquad T=9/8,\quad U=5/4,\\
\Lambda=107/15-4/j-4/n,\qquad
\theta=1+a\dot b=1-\frac{15}{56}\Lambda.
\end{gathered}
\tag{16.7}
$$

Then the gain derivatives at clocks five through seven and the
response derivatives are

$$
\begin{aligned}
v_5:=\dot g(5)&=\frac{-256+85/j+190/n}{21},\\
v_6:=\dot g(6)&=\frac{-185+48/j+160/n}{7},\\
v_7:=\dot g(7)&=-48+10/j+45/n,\\
\alpha(r):=\dot p&=1+(n+5/4)v_5,\\
\eta(r):=\dot k&=\frac{512n}{7}+\frac{8481}{35}-\frac{925}{4n}
 -\frac{836n/35+213/2}{j},\\
\zeta(r):=\dot u&=1+(n+5/2)v_6+24\{5-64r(1-r)\}\dot b.
\end{aligned}
\tag{16.8}
$$

Proof. Differentiating the single interpolant (2.3) gives its node
values at $0,1,2,3$ as
$(-1,-1/j,-\theta/T,-1/n)$. The numerators of (2.3) vanish at the
base point, so differentiating their denominators creates no extra
term there. Substituting (16.7) gives
$-\theta/T=17/21-20/(21j)-20/(21n)$. The fixed extrapolation rows at
$5,6,7$ are respectively

$$
(-4,15,-20,10),\qquad(-10,36,-45,20),\qquad(-20,70,-84,35).
\tag{16.9}
$$

Applying these rows to those four derivatives gives $v_5,v_6,v_7$.
They are evaluations of the derivative of one entire polynomial.
Since $h(5)=0$ and $\dot d=1$, the chain rule gives $\alpha$.
For $k$ it gives

$$
\dot k=-\frac{27}{5}+(15/4+2n)v_7
 -\frac{32}{5}(5/2+n)v_6-\frac{768}{5}\dot b.
\tag{16.10}
$$

The $\dot n$ terms cancel because
$(384/5)2\dot n-(32/5)24\dot n=0$; the remaining trace terms give
the displayed $\dot b$ coefficient. Substitution yields $\eta$.
Finally $\partial_b n=1-64r(1-r)$ at $b=1/8$, which gives $\zeta$
from $u=d+(2U+n)g(6)$. All denominators here are positive $j,n$ and
fixed positive integers, so these formulas hold also at $\Lambda=0$.
There is no independent adjustment of $g(5),g(6),g(7)$ or of $d$. ∎

**Lemma 16.4 (An explicit positive transverse certificate).** For
$s=9/8-r$, $1/8<r<1$, $r\ne9/16$, set $n=n(r)=n(s)$,
$j_r=n-r$, $j_s=n-s$, and

$$
R(n)=-8192n^3+119952n^2-12320n-57875.
\tag{16.11}
$$

Then

$$
\mathcal D(r):=\alpha(r)\eta(s)-\alpha(s)\eta(r)
 =\frac{(s-r)R(n)}{1680n j_rj_s}\ne0.
\tag{16.12}
$$

Proof. On the exact-$h$ family the actual responses in this section are

$$
p=24,\qquad u=84+24n(r),\qquad
f=312+\frac{768}{5}n(r),\qquad k=-\frac{1128}{5},
\tag{16.13}
$$

where $n(r)=1/8+9r-8r^2$. Its exact difference is
$n(r)-n(t)=(r-t)\{9-8(r+t)\}$. Thus distinct exact-$h$ worlds collide
in $(p,u,f)$ exactly when $t=s=9/8-r$. Legality gives $1/8<r<1$,
and distinctness removes $9/16$. These are the inherited mirror pairs;
(16.12) concerns their transverse relation to the full parent.

For a short coefficient check write $\alpha=a_0+a_1/j$ and
$\eta=e_0-c_0/j$, with

$$
\begin{aligned}
a_0&=\frac{-512n^2-218n+475}{42n},&
a_1&=\frac{85(4n+5)}{84},\\
e_0&=\frac{10240n^2+33924n-32375}{140n},&
c_0&=\frac{1672n+7455}{70}.
\end{aligned}
\tag{16.14}
$$

The denominator-cleared polynomial identity is

$$
\begin{aligned}
&4(-512n^2-218n+475)(1672n+7455)\\
&\quad +(340n+425)(10240n^2+33924n-32375)\\
&=57344n^3-839664n^2+86240n+405125=-7R(n).
\end{aligned}
\tag{16.15}
$$

Consequently $a_0c_0+a_1e_0=-R/(1680n)$. Expanding the determinant
in (16.12) gives this scalar times $(1/j_r-1/j_s)$.
Since $j_s-j_r=r-s$, (16.12) follows. Also
$j_rj_s=n^2-n-1/64$, from $r+s=9/8$ and $rs=(n-1/8)/8$.

To prove the sign without numerical root estimates, use

$$
n=\frac{85}{32}-8(r-9/16)^2,\qquad
\frac98<n\le\frac{85}{32}.
\tag{16.16}
$$

On the closed interval $[9/8,85/32]$,

$$
\begin{aligned}
R(9/8)&=\frac{273661}{4}>0,\\
R'(n)&=-24576n^2+239904n-12320\\
&\ge-24576(85/32)^2+239904(9/8)-12320=84172>0.
\end{aligned}
\tag{16.17}
$$

Thus $R(n)>0$, and $n,j_r,j_s>0$ by source legality. The determinant
is nonzero at every distinct mirror pair, including any member on a
singular $\Lambda=0$ source. ∎

**Theorem 16.5 (Two whole connected components).** Each of
$\Gamma_+$ and $\Gamma_-$ is an entire connected component of the full
$\mathcal C_{MM}$ in Definition 16.1. Near every one of its points,
all ordered complete-parent collisions in $\mathcal C_{MM}$ are
mirror pairs on that same arc. The relevant Jacobians are invertible
pointwise, but their unnormalized absolute determinants have no
uniform positive lower bound over either whole arc.

Proof. Fix $(A_{r_0},A_{s_0})$ on either arc. Use the two full-parent
charts of Lemma 16.2, with coordinates $(r,\epsilon)$ and
$(t,\epsilon')$. Since $r_0\ne s_0$, shrink their neighborhoods to
be disjoint; the complete-world diagonal is then absent from their
product. Define the smooth response-difference map

$$
F=(p-p',k-k',u-u').
\tag{16.18}
$$

Keep $r$ free and take $(\epsilon,\epsilon',t)$ as the three unknowns.
At the mirror pair their Jacobian is

$$
D_{(\epsilon,\epsilon',t)}F=
\begin{pmatrix}
\alpha(r_0)&-\alpha(s_0)&0\\
\eta(r_0)&-\eta(s_0)&0\\
\zeta(r_0)&-\zeta(s_0)&-24n'(s_0)
\end{pmatrix}.
\tag{16.19}
$$

The first two last-column entries are zero because $p,k$ are constant
along the exact-$h$ curve; the third follows from (16.13). Its determinant
is

$$
24n'(s_0)\mathcal D(r_0)
=-\frac{4(s_0-r_0)^2R(n)}{35n j_{r_0}j_{s_0}}<0,
\tag{16.20}
$$

since $n'(s_0)=9-16s_0=-8(s_0-r_0)$. The response map is defined on an
open product of chart neighborhoods, is continuously differentiable,
vanishes at this point and has the invertible unknown-variable
Jacobian (16.19). The ordinary implicit function theorem gives a unique
nearby zero $(\epsilon,\epsilon',t)$ for each nearby $r$ and describes
all nearby zeros. But $(0,0,9/8-r)$ is already such a zero. Uniqueness
therefore identifies the complete local zero set with this mirror
curve. Shrink $r$ to the same side of $9/16$ as $r_0$. The complete-parent
homeomorphism makes this local uniqueness apply to all nearby complete
worlds, including singular-source worlds. Each arc is therefore
relatively open in the full $\mathcal C_{MM}$.

For relative closedness, use the homeomorphic coordinates in
$\mathcal X^2$. Inside $\mathcal C_{MM}$, $\Gamma_+$ is exactly the set
cut out by the closed coordinate conditions

$$
b=b'=1/8,\quad\epsilon=\epsilon'=0,\quad r+t=9/8,\quad r\le9/16.
\tag{16.21}
$$

The strict condition $t<1$ forces $r>1/8$. At $r=9/16$ the reflection
gives $t=r$, and reconstruction gives the identical whole world,
which the guard $W\ne W'$ excludes. Thus (16.21) adds no endpoint
and proves relative closedness. For $\Gamma_-$ replace $r\le9/16$
by $r\ge9/16$; the diagonal guard makes it strict and source legality
gives $r<1$.

Explicitly the only extra endpoint pairs are
$(r,t)=(1/8,1)$, $(9/16,9/16)$ and $(1,1/8)$. The first and last
violate strict source legality, and the middle is the removed
complete-world diagonal. No limit can acquire a different gain or
drift: the coefficient topology is faithfully represented by
$(b,r,\epsilon)$ and both epsilons on these arcs are zero. Escape to
infinity creates no extra finite point of this space.

Projection to $r$ is a homeomorphism from the arcs to their respective
nonempty open intervals in (16.3), so they are connected. Any connected
subset of $\mathcal C_{MM}$ meeting an arc must lie in it: otherwise
its intersections with that relatively open and closed arc and its
open complement would disconnect the subset. Each arc is thus a
maximal connected subset, namely a whole connected component. No
compactness, finite-fiber assumption or global smoothness of the rest
of $\mathcal C_{MM}$ has been used.

Finally, as $r\to9/16$ on either arc, $s-r\to0$ while $n,j_r,j_s$
have finite positive limits. Equations (16.12) and (16.20) show that
the two-by-two and three-by-three determinants tend to zero, linearly
and quadratically respectively in $s-r$. Therefore neither absolute
determinant has a uniform positive margin on the whole arc. This
does not contradict pointwise local invertibility. ∎

**Corollary 16.6 (Continuous deformation of the same ordered pair).**
Let $I$ be any connected parameter space and let
$\gamma:I\to\mathcal C_{MM}$ be continuous. If its image meets one of
$\Gamma_+,\Gamma_-$, the whole image lies in that same arc, and its
fifth response is identically $p=24$. Its common sixth-M and final-M
responses may vary.

Proof. The image of a connected space under a continuous map is
connected. Theorem 16.5 places every connected set meeting an arc
inside that arc, and (16.13) fixes $p=24$. ∎

For the ordering in Theorem 9.1, its pair $(A,B)$ lies on $\Gamma_+$.
Indeed the exact closed interval

$$
\left[\frac{273384932776920629}{10^{18}}-10^{-12},
      \frac{273384932776920629}{10^{18}}+10^{-12}\right]
 \subset(1/8,9/16)
\tag{16.22}
$$

contains its $t$ parameter, and reflection places the second source
strictly between $9/16$ and one. The original chart bounds give
$2<\Lambda(A)<3$ and $1<\Lambda(B)<2$ on that whole interval. Hence
its notation $W(t,1/8),W(9/8-t,1/8)$ really has $\epsilon=0$, $g=h$,
$d=24$, identifying it with (16.3); reversing the ordering gives
$\Gamma_-$. This application uses that exact interval and pair
identity and needs no further assertion about the third world in
Theorem 9.1.

The corollary concerns continuous legal deformation of the same
ordered distinct collision pair. It imposes no continuity,
measurability, computability or finite-description condition on actual
deterministic acquisition strategies or on their choices of witnesses.
It does not classify other components, exclude disjoint replacement
pairs or discontinuous witness choices, or permit passage through an
equal-world pair or an illegal source boundary. Those passages leave
$\mathcal C_{MM}$. All other complete-parent components, all-external
worlds, lower degrees, zero drift, sampled zeros and singular sources
remain in the correspondence wherever the actual equations permit
them.

## 17. Suppliers, inherited constructions and the remaining common parent

The full-fiber and full-parent component consequences in Sections 12–16
are ordinary model-specific repository-derived mathematics. Fixed-node
interpolation, the intermediate and implicit function theorems,
Sylvester elimination and Sturm root counting are reused tools. No
priority or exhaustive novelty assertion accompanies these consequences.
Their exact supplier correspondence is as follows.

| Supplier | Hypotheses and use here |
| --- | --- |
| This volume, Definitions 1.1–1.3 and Theorem 2.1 | Entire nonzero degree-at-most-three gain, one fixed drift, strict rank-one source, original clocks, actual left products, complete-world guards and the full parent reconstruction. Lemma 16.2 uses that reconstruction with $\beta=1/8$ in complete-coefficient topology. |
| [Terminal-zero-plane volume](FIB_TERMINAL_ZERO_PLANE_INVERSE_AND_J_PAIR_CHAMBER.md), Theorems 9.2–9.3 and (9.5)–(9.19) | Its $F=M$, $A=z=24,C=147/5,Y=18$, $V_M=U+n$ and $a_4=U\Lambda,a_{5,M}=A_5$ are precisely Lemma 12.2. Its full strict-source no-common-zero theorem includes $\Lambda=0$ and unbounded offdiagonals; a chamber inverse is not substituted for it. |
| [Entire-response volume](FIB_C35_ENTIRE_JM_RESPONSE_INJECTIVITY.md), Theorems 15.2–15.4 | Its width $\beta=1/8$ gives $\mathcal K$ and the exact joint inverse (14.4). Its exact-$h$ exclusion alone is not the whole-fiber exclusion (15.5). |
| This volume, Theorems 4.1–4.2, 5.1, 8.1, 9.1 and Definition 10.1 | Singular fixed-width worlds, the three-world and direction necessities, the two actual different-fifth-response children, the mirror pair and the same-child terminal-slot conditions retain their literal histories. |
| Berrut–Trefethen, *[Barycentric Lagrange Interpolation](https://doi.org/10.1137/S0036144502417715)*, §2, (2.1)–(2.2) | Existence and uniqueness at fixed distinct nodes. Here the nodes are $0,1,2,3$ for the parent and $0,1,3,5$ for $p=24$; the actual interpolation rows are displayed. This supplies no model collision by itself. |
| Jiří Lebl, *[Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf)*, Theorem 8.5.6 | The ordinary implicit function theorem on an open Euclidean domain for a continuously differentiable map with invertible dependent-variable Jacobian. The derivatives used are $H_b>0$, $\partial_bR_0=448/25$, and the explicit three-by-three determinant (16.20); each application includes local uniqueness of all nearby zeros. |
| Cox–Little–O'Shea, *[Ideals, Varieties, and Algorithms](https://doi.org/10.1007/978-3-319-16721-3)*, Chapter 3 | The Sylvester resultant and its necessary common-finite-root implication. Equations (14.9)–(14.10) fix the actual polynomials, row order, signs and exact coefficient generation. A projected resultant zero is never treated as sufficient for a legal world. |
| Basu–Pollack–Roy, *[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2)*, univariate real-root methods | Sturm's root-counting theorem. The signed recurrence, normalization, all endpoint signs, individual isolations and rational arithmetic needed here are given in Section 14. The generic method does not itself classify this complete-world fiber. |

The inherited exact-$h$ fifth-J $L_2$ still uses
$r=1/2,5/8,3/4$, $b=1/8$, $g=h$, $d=24$, fifth-J response $24$ and
one acquired sixth response $54$ for J and $57$ for M. Its actual
terminal pairs and original clocks are unchanged. Theorem 8.1 remains
an actual all-external sixth-J $L_1$ at its own fifth-M response
$2744214237/10^8<p_J<2744214238/10^8$. Theorem 9.1 remains an actual
sixth-M $L_1$ at $p=24$. Theorem 15.4 excludes every sixth-J $L_1$ at
that latter fifth response, so these two children do not combine to
supply the missing M arm. In particular the earlier possibility in
Definition 10.2 of another sixth-J child at $p=24$ is excluded by
(15.5); its common-parent problem remains otherwise unresolved.
The exact offslice support of Theorem 6.1 also retains its original
scope and responses $357018/2575$ and $464403/2575$ at sixth traces
$7/2$ and $19/4$; excluding that chosen support does not exclude its
whole fifth fiber.

The component theorem only rules out changing $p$ by continuous legal
continuation of the same ordered mirror pair. It leaves every other
MM component and every replacement or discontinuous pair legal. The
new necessary condition below is $p\ne24$ for the still unresolved
common-parent M arm; it is not a general-$p$ impossibility theorem,
a recovery result, a stability result or a complexity bound.

Earlier ancestors, alternative histories and actions, same-parent
$L_3$, the original guarded root $L_7$, full cubic unrestricted
deterministic adaptive eight-read recovery or impossibility, comparison
with nine total readings and full-original-domain nine-read sufficiency
remain open. Nothing here transfers a quadratic-source conclusion to
cubic worlds. In particular no restriction of continuity, measurability,
computability or finite description is imposed on actual strategies.

**Theorem 17.1 (The exact remaining common-response obligation).** An
actual fifth-M $L_2$ support at the literal $H_4$ exists if and only if
the following system has a solution. Choose one real $p\ne24$, one
real $v_J$ and one real $v_M$, and for each
$(E,F,a)\in\{J,M\}^2\times\{0,1\}$ choose a strict source
$(r_{EFa},b_{EFa})$ satisfying

$$
0<r_{EFa}<1,\qquad b_{EFa}>0,\qquad
\mathsf S_p(r_{EFa},b_{EFa})=0.
\tag{17.1}
$$

For each label use exactly (12.5)–(12.6) to construct
$\epsilon_{EFa}$ and the complete world $W_{EFa}$, and require

$$
\begin{aligned}
p(W_{EFa})&=p&&\text{for every }E,F,a,\\
u_E(W_{EFa})&=v_E&&\text{for every }E,F,a,\\
f_{EF}(W_{EF0})&=f_{EF}(W_{EF1})&&\text{for every }E,F,\\
(b_{EF0}-b_{EF1})^2+(r_{EF0}-r_{EF1})^2
 +(\epsilon_{EF0}-\epsilon_{EF1})^2&>0&&\text{for every }E,F.
\end{aligned}
\tag{17.2}
$$

The functions in (17.2) are precisely (1.7), using the single entire
gain and fixed drift of each reconstructed world. The first equality
is also automatic from (17.1) and Theorem 12.3, but displays the one
common acquired fifth response. The second line keeps the two terminal
pairs of each child inside that child's one acquired sixth response.
All label reuse, overlapping pairs and disjoint pairs are allowed.
The system includes the legal $\Lambda=0$ worlds through the positive
squared-norm lift.

Proof. If a support has fifth-M $L_2$ at response $p$, Theorem 15.4
forces $p\ne24$. Unfold (1.5): for each sixth action choose its one
acquired response $v_E$ with $L_1$. For each terminal action $F$ choose
two different complete worlds in one final-response $L_0$ leaf of
that same child. They provide the eight labels, with any permitted
reuse. Theorem 12.3 supplies (17.1) and their exact reconstruction.
The parent bijection makes the last line of (17.2) exactly the
complete-world distinctness guard. Thus every actual witness supplies
a solution, including when the original support is infinite.

Conversely a solution gives at most eight complete worlds in one
$\mathcal F(H_4,M,p)$. For each $E$, its acquired $v_E$ child contains
both distinct terminal pairs in (17.2). Each pair supplies its final
$L_0$, so the child is nonsingleton and has $L_1$. The finite union
has $L_2$ at the one common fifth response $p$. This is the guarded
terminal-slot argument of Definition 10.1 with the proved extra
condition $p\ne24$, not an extraction of a two-world nonterminal
witness. ∎

At such a $p$, Theorems 2.2, 3.2 and 5.1 still require at least three
different complete worlds and gain directions, with a world outside
$b=1/8$; all worlds have $d\ne24$ and gain not proportional to $h$.
The sixth-M final-M pair in (17.2) must lie outside $\Gamma_+\cup\Gamma_-$,
since those components have $p=24$. These necessary filters do not
replace any equation or guard. Other components, all-external supports,
singular worlds, sampled zeros, lower degrees, repeated roots, zero
drift and unbounded legal offdiagonals remain available. The exact
remaining obligation is to satisfy (17.1)–(17.2) for one common
$p\ne24$, retaining each child's one acquired $v_E$; its feasibility
and the resulting same-parent $L_3$ remain open.

## 追加锚（本行以下为增补区）

## 18. Four actual worlds at the inherited exact fifth response

**Definition 18.1 (The exact parameter and the new M-child system).**
The domain, cardinalities and action convention in Sections 18–25 are
exactly Definitions 1.1–1.3. In particular the literal parent is
$H_4=(0,J,24,M,147/5,J,24,M,18)$, the initial read counts, and the
clocks are $0,\ldots,7$. Each world has one fixed source, one entire
nonzero real polynomial gain of degree at most three, and one fixed
real drift. Write

$$
\mathcal P=\left[\frac{2744214237}{10^8},
                       \frac{2744214238}{10^8}\right].
\tag{18.1}
$$

Here $p_J$ always means $p(W_0(z_J))$, where $z_J$ is the unique
six-coordinate zero of the unchanged system (8.1) in its original
box $\mathcal B_J$. Theorem 8.1, including this exact algebraic
parameter and its strict enclosure inside $\mathcal P$, is an inherited
premise. A midpoint of $\mathcal P$ is not a definition of $p_J$.

For the construction only, use $0<r<1$, $b>0$, $\Lambda\ne0$ and

$$
\begin{gathered}
c=r(1-r)/b,\quad j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\quad V=U+n,\\
B_{\rm coef}=6/T-2/U,\quad
\Lambda=1+6/T+1/U-4/j-4/n,\\
\epsilon=-\frac{24}{5}(b-1/8)\frac{B_{\rm coef}}\Lambda,
\qquad d=24+\epsilon.
\end{gathered}
\tag{18.2}
$$

Let $g=\sum_{i=0}^3\gamma_i\ell_i$, with the fixed Lagrange
polynomials of (7.1) and the ordered samples

$$
(\gamma_0,\gamma_1,\gamma_2,\gamma_3)
 =\left(-24-\epsilon,-\frac\epsilon j,
               \frac{27/5-\epsilon}{T},-\frac\epsilon n\right).
\tag{18.3}
$$

This is the same entire gain $h+w$ as in Theorem 2.1, not a
separately fitted gain at a later clock. In particular

$$
\begin{pmatrix}g(5)\\g(6)\\g(7)\end{pmatrix}
=\begin{pmatrix}-4&15&-20&10\\-10&36&-45&20\\-20&70&-84&35\end{pmatrix}
\begin{pmatrix}\gamma_0\\\gamma_1\\\gamma_2\\\gamma_3\end{pmatrix}.
\tag{18.4}
$$

For $W=W(r,b)=(P(r,b),g,d)$ abbreviate the actual responses by

$$
\begin{aligned}
p(r,b)&=d+Vg(5),&u(r,b)&=d+(2U+n)g(6),\\
f_J(r,b)&=d+(T+2j+4r)g(7),&
f_M(r,b)&=d+(3U+2n)g(7).
\end{aligned}
\tag{18.5}
$$

Thus $u=u_M$, $f_J=f_{MJ}$ and $f_M=f_{MM}$ in (1.7). The seventh
responses follow the acquired sixth M. They are not the seventh
responses following sixth J.

Order the eight coordinates as
$z=(r_A,b_A,r_B,b_B,r_C,b_C,r_D,b_D)$. For a real parameter $p$ put

$$
F_p(z)=\begin{pmatrix}
p(r_A,b_A)-p\\p(r_B,b_B)-p\\p(r_C,b_C)-p\\p(r_D,b_D)-p\\
u(r_A,b_A)-u(r_B,b_B)\\
u(r_A,b_A)-u(r_C,b_C)\\
u(r_A,b_A)-u(r_D,b_D)\\
f_J(r_A,b_A)-f_J(r_B,b_B)
\end{pmatrix}.
\tag{18.6}
$$

There is no tolerance in this system. Its rational box is

$$
\begin{gathered}
\rho=10^{-9},\qquad \mathcal B=\{z:\|z-m\|_\infty\le\rho\},\\
m=10^{-18}\begin{pmatrix}
798291691626185419\\319422724668808667\\
352720293321024633\\159165804512783260\\
280826656614482548\\254495174825897077\\
819801620259070153\\150424754128846912
\end{pmatrix}.
\end{gathered}
\tag{18.7}
$$

The labels $A,B,C,D$ in this construction denote worlds and do not
identify them with the worlds denoted by those letters in Section 9.

**Theorem 18.2 (Four complete common-history worlds).** For every real
$p\in\mathcal P$, (18.6) has exactly one zero $z(p)$ in $\mathcal B$;
it is interior. Its four sources reconstruct four different complete
worlds at $H_4$, all with $b>1/8$ and $d\ne24$. At $p=p_J$ write these
worlds as $A,B,C,D$ and define exactly

$$
v_\star=u(A)\quad\text{at }z(p_J).
\tag{18.8}
$$

Then

$$
\begin{gathered}
p(A)=p(B)=p(C)=p(D)=p_J,\\
u(A)=u(B)=u(C)=u(D)=v_\star,\qquad f_J(A)=f_J(B).
\end{gathered}
\tag{18.9}
$$

These assertions concern four actual worlds. Exhaustion of their
acquired child is a separate assertion in Theorem 23.1.

Proof. Use exact rational interval arithmetic (14.12) and reciprocal
only after exclusion of zero, with the derivative rules (7.5). In this
proof the expression order is (18.2)–(18.6): compute $c,j,n,T,U,V$,
then $\Lambda$ and $B_{\rm coef}=6/T-2/U$, then
$\epsilon=(-(24/5)(b-1/8)B_{\rm coef})/\Lambda$, then (18.3),
(18.4), (18.5). Sums and matrix products are in increasing index order.
This fixes the rational inclusion calculation, without rounding or
algebraic refitting of the expressions.

The following enclosures hold throughout the full coordinate boxes.
Each numerator interval in the table is divided by $10^6$.

| World | $\Lambda$ | $d$ | $j$ | $n$ |
| --- | --- | --- | --- | --- |
| $A$ | $[-1165902,-1165901]$ | $[26663105,26663107]$ | $[823526,823527]$ | $[1621817,1621818]$ |
| $B$ | $[2369401,2369402]$ | $[23746741,23746742]$ | $[1593573,1593574]$ | $[1946293,1946295]$ |
| $C$ | $[-381012,-381011]$ | $[29640372,29640375]$ | $[1048078,1048079]$ | $[1328904,1328905]$ |
| $D$ | $[1403279,1403280]$ | $[23680135,23680136]$ | $[1132489,1132491]$ | $[1952291,1952292]$ |

The coordinate bounds in (18.7) give $0<r<1$, $b>1/8$, $T>1$ and
$U>1$ before division. Thus $b,j,n,T,U$ are positive and every
$\Lambda$ interval excludes zero. Also
$B_{\rm coef}=2(2+5b)/(TU)>0$. All four entries of each $P$ are
positive, its trace is one and its determinant is zero, so it has
rank exactly one. The four $r$ boxes are pairwise disjoint. This
establishes all six complete-world distinctness guards.

Use the exact preconditioner

$$
\mathsf C=10^{-8}\begin{pmatrix}
4921360&-3810382&0&0&-1407759&0&0&152411\\
-2423216&2748351&0&0&1015388&0&0&-109931\\
2063758&289613&0&0&-230496&0&0&-132042\\
-54555&1067305&0&0&6093&0&0&3491\\
1268991&2029850&-2607294&0&749935&-891665&0&-81192\\
852351&1363401&-1387346&0&503713&-598910&0&-54534\\
-2253154&-3604094&0&4951388&-1331545&0&1583194&144160\\
229692&367410&0&142330&135741&0&-161394&-14696
\end{pmatrix}.
\tag{18.10}
$$

Let $E=I-\mathsf CDF_p(\mathcal B)$ be the interval matrix obtained
by (7.5). For every $p\in\mathcal P$ the following exact bounds hold:

$$
\sum_{j=1}^8|E_{ij}|_{\max}<q_i,\qquad
 |(\mathsf CF_p(m))_i|<\eta_i.
\tag{18.11}
$$

The table specifies $q_i$ and $\eta_i$ in the coordinate order (18.7).
Both bounds concern the unscaled ordered equations (18.6).

| $i$ | $10^8q_i$ | $10^{24}\eta_i$ |
| --- | --- | --- |
| $1$ | $11111$ | $436587100487845$ |
| $2$ | $7118$ | $258578350306137$ |
| $3$ | $4419$ | $117668550203950$ |
| $4$ | $1347$ | $56093000299099$ |
| $5$ | $111278$ | $295306750456129$ |
| $6$ | $68422$ | $180154900172247$ |
| $7$ | $17725$ | $540431800271175$ |
| $8$ | $2207$ | $36971600370067$ |

The following rational upper bounds make the margins in (18.11)
explicit. The middle column divides by $10^{12}$ and bounds the row
sum in (18.11); the last divides by $10^{27}$ and bounds the center
component there. Each is strictly smaller than its declared bound.

| $i$ | Row-sum numerator | Center-component numerator |
| --- | --- | --- |
| $1$ | $111100599$ | $436587100487844497$ |
| $2$ | $71177580$ | $258578350306136259$ |
| $3$ | $44183543$ | $117668550203949499$ |
| $4$ | $13460403$ | $56093000299098885$ |
| $5$ | $1112777824$ | $295306750456128034$ |
| $6$ | $684212441$ | $180154900172246818$ |
| $7$ | $177245619$ | $540431800271174350$ |
| $8$ | $22062065$ | $36971600370066102$ |

To reproduce these inequalities, put the eight intervals
$[m_i-\rho,m_i+\rho]$ into (18.2)–(18.6), give the $i$th coordinate
its unit derivative vector, and propagate (7.5). Multiply the resulting
Jacobian by (18.10), subtract from $I$, and sum the absolute endpoint
bounds in each row. At the singleton $m$, put the full interval
$\mathcal P$ in each of the first four equations, form
$\mathsf CF_p(m)$ and bound each component. No premise about the
unknown root is used in either calculation.

Set $q=\max_iq_i=111278/10^8$ and
$\eta=\max_i\eta_i=540431800271175/10^{24}$. They satisfy

$$
q<1,\qquad
\rho-\eta-q\rho
 =\frac{18338216789153}{40000000000000000000000}>0.
\tag{18.12}
$$

The Banach contraction argument (7.6) therefore gives a unique
interior fixed point of $z\mapsto z-\mathsf CF_p(z)$ in the complete
closed box. The same norm inequality makes $\mathsf C$ invertible,
so this fixed point is exactly a zero of $F_p$, and every zero in
the box is this point. This proves the assertion uniformly over
$\mathcal P$, in particular for the inherited exact $p_J$.

For each source at the zero, (18.3) enforces the first four original
parent rows. The residual of the clock-four row is exactly

$$
d+Ug(4)-18
 =U\{\epsilon\Lambda+(24/5)(b-1/8)B_{\rm coef}\}=0.
\tag{18.13}
$$

Thus Theorem 2.1 gives a complete parent world, with the same entire
gain as (18.3). The original responses $0$ and $24$ exclude an
identically zero gain. The drift enclosures above give $d\ne24$.
Equations (18.6) now give (18.9) as exact equalities. Overlap of
response intervals is not used to establish any equality. The
products in Definition 1.3 make every response in (18.9) an actual
response at its original clock. ∎

## 19. The sharp acquired response and the terminal responses

**Theorem 19.1 (Response enclosure retaining the exact parameter).**
The actual $v_\star$ of (18.8) lies strictly inside

$$
\mathcal V=\left[\frac{144397245334493}{10^{12}},
                       \frac{144397245371500}{10^{12}}\right].
\tag{19.1}
$$

At the four worlds, the final responses have the enclosures below.
Among these worlds the only unordered distinct final-J collision
pair is $\{A,B\}$, and the final-M response is injective.

Proof. First, natural interval evaluation in the full box gives these
response and gain bounds. Every numerator interval in both tables
is divided by $10^6$; they are enclosures before imposing $F_p=0$.

| World | $p$ | $u$ | $f_J=f_{MJ}$ | $f_M=f_{MM}$ |
| --- | --- | --- | --- | --- |
| $A$ | $[27442122,27442163]$ | $[144397177,144397314]$ | $[489764880,489765207]$ | $[640171212,640171644]$ |
| $B$ | $[27442140,27442145]$ | $[144397238,144397253]$ | $[489765025,489765062]$ | $[658972311,658972359]$ |
| $C$ | $[27442037,27442248]$ | $[144396879,144397612]$ | $[403819508,403820934]$ | $[630538939,630541225]$ |
| $D$ | $[27442138,27442147]$ | $[144397231,144397260]$ | $[569047436,569047516]$ | $[659677392,659677485]$ |

| World | $g(5)$ | $g(6)$ | $g(7)$ |
| --- | --- | --- | --- |
| $A$ | $[238913,238926]$ | $[24029771,24029799]$ | $[75183233,75183286]$ |
| $B$ | $[1131951,1131954]$ | $[26325905,26325909]$ | $[80945379,80945386]$ |
| $C$ | $[-774637,-774562]$ | $[26399707,26399876]$ | $[83634921,83635239]$ |
| $D$ | $[1156421,1156425]$ | $[26507980,26507987]$ | $[81463625,81463637]$ |

These bounds follow from exactly the expressions and reciprocal guards
in the proof of Theorem 18.2. The sharper enclosure (19.1) uses their
common root, rather than treating the root coordinates independently.
Let $p_0$ be the exact rational midpoint of $\mathcal P$, let
$U_B(z)=u(r_B,b_B)$, and put

$$
\alpha=DU_B(m),\qquad K=\alpha\mathsf C,\qquad
F_0=F_{p_0}(m),\qquad E=I-\mathsf CDF_p(\mathcal B).
\tag{19.2}
$$

Here $\alpha$ is an eight-entry row with zeros outside coordinates
$r_B,b_B$; $E$ is independent of $p$ because the parameter enters
(18.6) only as four constant subtractions. For $z=z(p)$ and
$\delta=z-m$, integrate the derivative along $m+t\delta$ to obtain

$$
\delta=-\mathsf CF_p(m)+\overline E\delta,\qquad
 U_B(z)=U_B(m)+\alpha\delta+R_U,
\tag{19.3}
$$

where every entry of $\overline E$ lies in its entry of $E$, and

$$
|R_U|\le\rho\sum_{j=1}^8
 |DU_B(\mathcal B)_j-\alpha_j|_{\max}.
\tag{19.4}
$$

Consequently $U_B(z)$ is enclosed by $\mathcal I+[-e,e]$, where

$$
\begin{aligned}
\mathcal I&=U_B(m)-KF_0+
           (K_1+K_2+K_3+K_4)(\mathcal P-p_0),\\
e&=\rho\sum_{j=1}^8\left(
 \left|\sum_{i=1}^8\alpha_iE_{ij}\right|_{\max}
 +|DU_B(\mathcal B)_j-\alpha_j|_{\max}\right).
\end{aligned}
\tag{19.5}
$$

This retains the shared $p$ dependence before taking an interval.
The first term uses $F_p(m)=F_0-(p-p_0)(1,1,1,1,0,0,0,0)^{\mathsf T}$.
In the second term take the interval sum before its absolute bound.
The exact rational inclusions specified by (18.2)–(18.6), (18.10)
and (19.2)–(19.5) are

$$
\begin{gathered}
\mathcal I\subset
\frac{[144397245334498362758,144397245371494765773]}{10^{18}},\\
e<\frac{5134731}{10^{18}}<\frac{5135}{10^{15}},\\
\mathcal I+[-e,e]\subset
\frac{[144397245334493228,144397245371499901]}{10^{15}}
 \subset\operatorname{int}\mathcal V.
\end{gathered}
\tag{19.6}
$$

By (18.9), $v_\star=U_B(z(p_J))$, proving (19.1). The midpoint
$p_0$ in this estimate is only an expansion point; $p_J$ and the
entire interval $\mathcal P-p_0$ remain in the estimate.

The final-M intervals are ordered $C,A,B,D$. The successive lower
endpoint minus preceding upper endpoint differences have positive
numerators

$$
9629987,\qquad18800667,\qquad705033
\quad\text{with denominator }10^6.
\tag{19.7}
$$

Thus every two of these worlds have different actual final-M
responses. For final J, $C$ is strictly below both $A,B$, and $D$
is strictly above both; $C,D$ are also separated. This excludes all
five distinct pairs other than $A,B$. Their exact equality is the
last equation of (18.6). ∎

## 20. Exact elimination for the full strict source domain

**Definition 20.1 (The two source polynomials and their normalization).**
For arbitrary real responses $p,v$, retain the integer polynomials
$X,N,H,\mathsf S_p$ of (12.1)–(12.3) and put

$$
\begin{gathered}
D_\Lambda=(b^2+8b+4)XN-2bTU(X+N)=N_4/2,\\
K_\Lambda=(8b-1)(2+5b),\quad Z_6=N+2bU,\\
G_{6,\Lambda}=(10T+45)XN-bT(36N+20X),\\
\mathsf A(r,b,p)=\mathsf S_p(r,b)/2
 =5b(p-24)D_\Lambda+3(8b-1)H(r,b),\\
\mathsf N_u(r,b)=
\frac{120bTD_\Lambda+15Z_6D_\Lambda(80b-1)
       -3K_\Lambda(bTXN+Z_6G_{6,\Lambda})}{T},\\
\mathsf B(r,b,v)=5bD_\Lambda v-\mathsf N_u(r,b).
\end{gathered}
\tag{20.1}
$$

The numerator defining $\mathsf N_u$ divides exactly by $T=1+b$ in
$\mathbb Z[r,b]$. Thus $\mathsf A,\mathsf B$ are polynomials, not
rational equations with an unmentioned denominator. The symbol
$D_\Lambda$ here is $N_4/2$; it is different from the polynomial $D$
used only on the $p=24$ graph in (14.1).

For the ordinary Sylvester resultant use exactly the row and column
order in Lemma 14.2, now with ordered inputs $(\mathsf A,\mathsf B)$
and variable $b$. Both generic $b$ degrees are seven. Define

$$
\Psi_2=4r^2-2r-1,\qquad
\Psi_4=625r^4-1000r^3+50r^2+260r+36,
\tag{20.2}
$$

and retain $\Phi$ exactly as in (4.5). The polynomial $R_{18}$ is
specified by the identity

$$
\operatorname{Res}_b(\mathsf A,\mathsf B)
 =52488000\,r^{11}(r-1)^9\Psi_2\Psi_4\Phi\,R_{18}(r,p,v).
\tag{20.3}
$$

This fixes its scale and sign. Its integer coefficient table is given
in Section 24, with monomial order $(r,p,v)$. Its coordinate degrees
are $(18,7,7)$ and it has $668$ nonzero terms.

To specify the linear subresultant without a normalization ambiguity,
form the $12$ by $13$ matrix whose ordered rows are the coefficients of

$$
b^5\mathsf A,b^4\mathsf A,\ldots,\mathsf A,
\quad b^5\mathsf B,b^4\mathsf B,\ldots,\mathsf B
\tag{20.4}
$$

in the columns $b^{12},b^{11},\ldots,1$. Denote these columns by
$c_{12},c_{11},\ldots,c_0$ and define

$$
\begin{aligned}
\Delta_1&=\det(c_{12},c_{11},\ldots,c_2,c_1),\\
\Delta_0&=\det(c_{12},c_{11},\ldots,c_2,c_0),\\
\mathcal L_i&=\frac{\Delta_i}{72900r^6(r-1)^4},\qquad i=0,1.
\end{aligned}
\tag{20.5}
$$

Both quotients are exact integer polynomials. The ordered subresultant
sequence has generic $b$ degrees $7,7,6,5,4,3,2,1,0$, and its
penultimate member is exactly

$$
72900r^6(r-1)^4\{\mathcal L_1(r,p,v)b+\mathcal L_0(r,p,v)\}.
\tag{20.6}
$$

The polynomials $\mathcal L_0,\mathcal L_1$ have respectively $728$
and $756$ terms, coordinate degrees $(26,6,6)$ and polynomial gcd
one. Equations (20.4)–(20.5), including the divisor, are finite exact
coefficient definitions of both, so no externally chosen primitive
part or sign convention is required. The calligraphic
$\mathcal L_1$ is a polynomial coefficient, not the recursive guard
$L_1$.

**Theorem 20.2 (Necessary projection and unique nonsingular lift).**
Every complete world in $\mathcal F(H_4,M,p,M,v)$ with
$\Lambda\ne0$ has a strict source satisfying

$$
\mathsf A(r,b,p)=\mathsf B(r,b,v)=0.
\tag{20.7}
$$

It consequently has a zero of the right side of (20.3) and satisfies
$\mathcal L_1b+\mathcal L_0=0$. Wherever
$\mathcal L_1\ne0$, a given projected coordinate $r$ permits at most
one $b$, namely $-\mathcal L_0/\mathcal L_1$, and at most one complete
world.

Proof. On every strict source, $b,T,U,X,N$ are positive. Multiplying
out the original parent coefficient gives

$$
\Lambda=\frac{2D_\Lambda}{TU XN}.
\tag{20.8}
$$

Therefore $D_\Lambda\ne0$ in this branch. The zero-safe parent
relation (2.2) and the same single interpolant (18.3) give

$$
\epsilon=-\frac{3K_\Lambda XN}{5D_\Lambda},\qquad
u(r,b)=\frac{\mathsf N_u(r,b)}{5bD_\Lambda},\qquad
\mathsf A=5bD_\Lambda\{p-p(r,b)\}.
\tag{20.9}
$$

For the middle identity, (18.4) first gives
$g(6)=3(80b-1)/T+\epsilon G_{6,\Lambda}/(TXN)$; multiply
$d+(Z_6/b)g(6)$ by $5bD_\Lambda$ and substitute the first identity.
The result is exactly the divisible numerator in (20.1). The
numerator and denominator of this rational response are relatively
prime as integer polynomials, with denominator precisely
$5bD_\Lambda$. This fixes the coefficient of $v$ in $\mathsf B$.
The last identity follows either from the fifth extrapolation row
in (18.4) or directly from (12.8). Thus the actual responses $p,v$
force (20.7), without dividing by a gain sample or by the drift.

Expand the two degree-seven polynomials and take their ordered
$14$ by $14$ Sylvester determinant. Polynomial expansion gives
(20.3) with exactly the coefficient table in Section 24. This
identity involves the original source polynomials, not an
interpolated approximation to them. In the parameter box used below
the leading $b$ coefficients are $5p+216>0$ and $5v+1125>0$.
There is no loss of degree in this specialization. More generally,
the fixed Sylvester determinant's necessary common-finite-root
implication does not require such an assumption.

For clarity, the implication from the linear subresultant can also
be seen directly from its minors. At a common finite root $b=t$,
evaluation of every row in (20.4) is zero, so
$\sum_{k=0}^{12}c_kt^k=0$. Multilinearity of determinant gives

$$
\Delta_1t+\Delta_0
=\det(c_{12},\ldots,c_2,c_1t+c_0)=0,
\tag{20.10}
$$

because its last column is a linear combination of the first eleven.
For $0<r<1$, the divisor in (20.5) is nonzero. Hence
$\mathcal L_1t+\mathcal L_0=0$, even at specializations where other
subresultant coefficients vanish. The identities (20.5)–(20.6) follow
by the same exact minors; no generic nonvanishing premise is being
applied to a particular root.

If $\mathcal L_1\ne0$, (20.10) fixes $b$ uniquely. The parent
relation then fixes $\epsilon$ by (20.9), and the first four original
samples fix every coefficient of the entire gain. Alternatively,
Theorem 12.3 gives fixed-source uniqueness without choosing this
chart. Thus each such strict source has at most one complete lift.
Neither a resultant zero nor a positive proposed $b$ is used to
assert existence of a complete lift. ∎

## 21. Uniform root and lift certificates on the response rectangle

**Theorem 21.1 (Exactly six remaining projected roots).** For every
$(p,v)\in\mathcal P\times\mathcal V$, $R_{18}(r,p,v)$ has exactly
six distinct roots in $0<r<1$, one in each interval $I_1,\ldots,I_6$
below and no others. Each is simple as a root in $r$.

Proof. The certificate uses a centered parameter expansion; it keeps
all mixed terms. Let

$$
\begin{gathered}
p_c=(p_L+p_U)/2,\quad v_c=(v_L+v_U)/2,\quad
h_p=\frac1{200000000},\quad h_v=\frac{37007}{2000000000000},\\
R_{18}(r,p_c+x,v_c+y)=\sum_{i,j}A_{ij}(r)x^iy^j.
\end{gathered}
\tag{21.1}
$$

The endpoints here are those of (18.1), (19.1). On a closed interval
$[a,b]$, first write
$A_{ij}(a+(b-a)t)=\sum_{\ell=0}^{18}a_{ij\ell}t^\ell$,
padding with zeros, and define its common-degree Bernstein coefficients

$$
\beta_{ijk}=\sum_{\ell=0}^k
 a_{ij\ell}\frac{\binom{k}{\ell}}{\binom{18}{\ell}},\qquad
 e_k=\sum_{i+j>0}|\beta_{ijk}|h_p^ih_v^j.
\tag{21.2}
$$

Thus the $k$th Bernstein coefficient of $R_{18}$ for every parameter
pair is enclosed by $[\beta_{00k}-e_k,\beta_{00k}+e_k]$.
Using the integer coefficient table in Section 24 gives the following
sign words, in order $k=0,\ldots,18$. Every one of the $171$
coefficient intervals excludes zero.

| Closed $r$ interval | Bernstein coefficient signs | Variation |
| --- | --- | --- |
| $[0,1/4]$ | `-------------------` | $0$ |
| $[1/4,5/16]$ | `---------++++++++++` | $1$ |
| $[5/16,3/8]$ | `++++++++++++-------` | $1$ |
| $[3/8,1/2]$ | `-------------------` | $0$ |
| $[1/2,3/4]$ | `-------------------` | $0$ |
| $[3/4,13/16]$ | `--------------+++++` | $1$ |
| $[13/16,27/32]$ | `+++++--------------` | $1$ |
| $[27/32,7/8]$ | `---------------++++` | $1$ |
| $[7/8,1]$ | `++++---------------` | $1$ |

These are explicit finite rational inequalities: for a `+` entry,
$\beta_{00k}>e_k$; for a `-` entry, $\beta_{00k}<-e_k$.
Equations (21.1)–(21.2) specify every term, degree and radius needed
to reproduce them from the integer table. There is no evaluation
only at the parameter midpoint.

The standard Descartes transformation $r=(a+bt)/(1+t)$ converts the
Bernstein coefficients on $[a,b]$ into coefficients of
$(1+t)^{18}R_{18}((a+bt)/(1+t),p,v)$, multiplied by positive binomial
factors. Hence their sign variation bounds the roots in $(a,b)$,
counting multiplicity. On each variation-one interval the first
and last coefficients have opposite signs, so the intermediate
value theorem gives a root. It is the only root there and is simple.
Variation-zero intervals have no roots, and no shared endpoint is a
root because the endpoint coefficients exclude zero. This covers
$[0,1]$ and proves the six-root count.

The six narrower rational isolations and their uniform endpoint
signs are

| Interval | Lower endpoint | Upper endpoint | Lower, upper signs |
| --- | --- | --- | --- |
| $I_1$ | $37691915/134217728$ | $9422979/33554432$ | $-,+$ |
| $I_2$ | $11835329/33554432$ | $47341317/134217728$ | $+,-$ |
| $I_3$ | $107144897/134217728$ | $53572449/67108864$ | $-,+$ |
| $I_4$ | $55015955/67108864$ | $110031911/134217728$ | $+,-$ |
| $I_5$ | $116688531/134217728$ | $29172133/33554432$ | $-,+$ |
| $I_6$ | $59915273/67108864$ | $119830547/134217728$ | $+,-$ |

For an endpoint $s$, its sign follows by enclosing
$A_{00}(s)$ with error
$\sum_{i+j>0}|A_{ij}(s)|h_p^ih_v^j$, again with exact rational
arithmetic. Every such error is strictly smaller than
$|A_{00}(s)|$. These endpoint checks, rather than signs of all
interior Bernstein coefficients on a narrow interval, supply the
narrow isolations. Each $I_i$ lies strictly inside its respective
variation-one interval. Consequently it contains exactly that
interval's one root, uniformly on the full parameter rectangle.
The Bernstein basis identity and Descartes rule used here are standard
univariate tools; the certificate concerns
the particular $R_{18}$ in (20.3). ∎

**Theorem 21.2 (All base factors and the six possible b lifts).** On
$\mathcal P\times\mathcal V$, the following table bounds
$-\mathcal L_0/\mathcal L_1$ throughout each entire indicated box.
The $b$ numerator intervals have common denominator $10^6$.

| Projected interval | Sign of $\mathcal L_1$ | $b$ numerator interval | Possible constructed world |
| --- | --- | --- | --- |
| $I_1$ | $+$ | $[254495,254496]$ | $C$ |
| $I_2$ | $-$ | $[159165,159166]$ | $B$ |
| $I_3$ | $-$ | $[319421,319426]$ | $A$ |
| $I_4$ | $-$ | $[150424,150425]$ | $D$ |
| $I_5$ | $-$ | $[-393738,-393737]$ | none with $b>0$ |
| $I_6$ | $+$ | $[-598255,-596853]$ | none with $b>0$ |

There is one strict root of $\Psi_2$, one of $\Psi_4$ and two of
$\Phi$. Their boxes and forced lifts are

| Factor | Lower $r$ endpoint | Upper $r$ endpoint | Sign of $\mathcal L_1$ | Forced $b$ |
| --- | --- | --- | --- | --- |
| $\Psi_2$ | $416020/514229$ | $1762289/2178309$ | $+$ | $-1/2$ |
| $\Psi_4$ | $985995/1135192$ | $802168/923549$ | $-$ | $-2/5$ |
| $\Phi$ | $149383/1108052$ | $182914/1356769$ | $+$ | $1/8$ |
| $\Phi$ | $1412683/1565387$ | $1774115/1965888$ | $+$ | $1/8$ |

Thus no $\Psi_2$ or $\Psi_4$ source is strict, and a $\Phi$ source
would have $b=1/8$, $\Lambda=0$. Among the six $R_{18}$ projections,
only the first four can have positive $b$, each with at most one
complete nonsingular lift.

Proof. For reproduction of all sign and quotient bounds, use the
polynomials defined by the exact minors (20.5). For each listed
$r,p,v$ box, let $(r_c,p_c,v_c)$ be its rational midpoint and
$(h_r,h_p,h_v)$ its radii. For $Q=\mathcal L_0,\mathcal L_1$, expand
exactly

$$
Q(r_c+x,p_c+y,v_c+z)=\sum_{i,j,k}q_{ijk}x^iy^jz^k,
\quad
Q\in q_{000}+[-e_Q,e_Q],\quad
 e_Q=\sum_{i+j+k>0}|q_{ijk}|h_r^ih_p^jh_v^k.
\tag{21.3}
$$

The binomial expansion of the determinant polynomials fixes each
$q_{ijk}$. These finite Taylor enclosures give precisely the
nonzero signs in both tables; taking the interval quotient only
after this exclusion of zero gives the six displayed $b$ bounds.
Thus nonvanishing of $\mathcal L_1$ is checked on every possible
projected root, rather than assumed generically. The last two
intervals exclude positive $b$ outright.

The exact polynomial remainder identities for the base factors are

$$
\begin{aligned}
\mathcal L_0-\tfrac12\mathcal L_1&\equiv0\pmod{\Psi_2},\\
\mathcal L_0-\tfrac25\mathcal L_1&\equiv0\pmod{\Psi_4},\\
\mathcal L_0+\tfrac18\mathcal L_1&\equiv0\pmod\Phi.
\end{aligned}
\tag{21.4}
$$

They follow by polynomial division in $r$ over $\mathbb Q[p,v]$
using (20.5). In particular their quotients do not require $p$ or
$v$ to be a midpoint. Together with the nonzero $\mathcal L_1$ in
the base boxes, (20.10) gives the exact forced $b$ values in the
second table.

For explicit root coverage of these base boxes, apply the signed
Sturm convention (14.11) to the three displayed univariate factors.
The degrees and endpoint sign words are

| Polynomial | Chain degrees | Signs at $0$ | Signs at $1$ | Variation drop |
| --- | --- | --- | --- | --- |
| $\Psi_2$ | $2,1,0$ | `--+` | `+++` | $1$ |
| $\Psi_4$ | $4,3,2,1,0$ | `++--+` | `--+++` | $1$ |
| $\Phi$ | $4,3,2,1,0$ | `--+-+` | `--+++` | $2$ |

Each displayed isolating interval has opposite polynomial endpoint
signs. Their counts exhaust the global variation drops. The two
$\Phi$ roots are the same roots as in Theorem 4.2, now in sharper
rational intervals. By (4.9) a strict point with $b=1/8$ at either
root has $\Lambda=0$. These base roots therefore contribute no
additional nonsingular source. Fixed-source uniqueness in Theorem
20.2 finishes the possible-lift assertion. A label in the first
table specifies the later matching, not an existence assertion from
this projection argument. ∎

## 22. Explicit singular-source exclusion and the uniform upper bound

**Theorem 22.1 (At most four complete worlds on the whole rectangle).**
For every real $(p,v)\in\mathcal P\times\mathcal V$,

$$
|\mathcal F(H_4,M,p,M,v)|\le4.
\tag{22.1}
$$

This is an upper bound over all strict sources, with no upper bound
on $b$ or $c$. It does not assume the existence of the zero in
Theorem 18.2. In particular the branch $\Lambda=0$ contributes no
world in this response rectangle.

Proof. Take any complete world in this full child. The zero-safe
parent equation (2.2) is necessary, including when $\Lambda=0$.
If $\Lambda=0$, positivity of $B_{\rm coef}$ forces $b=1/8$.
Equations (4.9) then give

$$
j=1/8+8r(1-r),\quad n=j+r,\quad T=9/8,\quad U=5/4,
\qquad \Lambda=\frac{\Phi(r)}{960jn}.
\tag{22.2}
$$

Consequently $r$ is one of exactly the two $\Phi$ roots in the
second table of Theorem 21.2. Theorem 4.1, or equivalently the
zero-safe equations (12.7), reconstructs the entire world with

$$
\begin{aligned}
A_5(r)&=1+(n+5/4)(4-15/j+20/T-10/n),\\
\epsilon&=(p-24)/A_5(r),\\
u&=24+\epsilon+(5/2+n)
       \{24+\epsilon(10-36/j+45/T-20/n)\}.
\end{aligned}
\tag{22.3}
$$

Here $A_5\ne0$ is the inherited full-source assertion in Lemma 12.2,
not a regularity assumption on the parent. Formula (22.3) follows
from the single gain $h+\epsilon v_r$ of Theorem 4.1; in particular
$g(6)$ is the bracket in its last line.

Exact interval evaluation over the full $p$ interval $\mathcal P$
and the two rational root boxes gives

| $r$ box | $A_5$ enclosure | Actual $u$ enclosure |
| --- | --- | --- |
| $[149383/1108052,182914/1356769]$ | $[-908,-907]/10^3$ | $[119870498,119870500]/10^6$ |
| $[1412683/1565387,1774115/1965888]$ | $[-5217,-5216]/10^3$ | $[138752856,138752858]/10^6$ |

For these calculations evaluate the exact expressions (22.2)–(22.3)
with the interval rule (14.12). Before division, $j,n,T$ are positive
and the $A_5$ intervals exclude zero. The unrounded expression for
$A_5$ supplies the subsequent quotient; the displayed coarser
$A_5$ enclosures are guards, not replacements of that expression.
Both actual $u$ enclosures are disjoint from $\mathcal V$. This
excludes each singular source line after its unique fifth-response
lift, and hence every $\Lambda=0$ world in the full child.

For $\Lambda\ne0$, Theorem 20.2 gives the necessary equations
$\mathsf A=\mathsf B=0$. The exact resultant (20.3) applies to
every finite real source, regardless of how large $b$ or $c$ is.
Strictness removes $r=0,1$. Theorem 21.2 excludes all $\Psi_2$
and $\Psi_4$ roots by negative forced $b$, and all $\Phi$ roots
by the forced singular source. Theorem 21.1 leaves exactly six
possible $R_{18}$ projections. The first table of Theorem 21.2
excludes the last two by $b<0$. On each of the first four,
$\mathcal L_1\ne0$ forces the sole possible $b$, and Theorem 20.2
permits at most one complete lift. There are therefore at most
four nonsingular complete worlds and no singular ones.

The two branches exhaust the parent, so (22.1) follows. No step
supposes that an arbitrary projected root actually has a legal lift.
The bound uses neither compactness of the source domain nor a
generic-rank deletion. Lower degrees, repeated gain roots, sampled
zeros and zero drift were never divided out. An identically zero
gain alone is excluded by the original model and by the original
unequal $0,24$ rows. ∎

## 23. The entire exact acquired child and its obstruction

**Theorem 23.1 (Exact four-world child with one final-J pair).** At the
inherited exact algebraic $p_J$ of (8.4), let $v_\star$ be the actual
response (18.8) at the unique eight-equation zero of Theorem 18.2.
Then the entire complete-world child is

$$
\mathcal F(H_4,M,p_J,M,v_\star)=\{A,B,C,D\}.
\tag{23.1}
$$

The four worlds are different, their $r$ projections occur in the
order $C,B,A,D$ in $I_1,I_2,I_3,I_4$, and each is the unique
complete lift of its corresponding source. The only unordered pair
of different worlds with equal actual final-J response is $\{A,B\}$.
There is no distinct final-M collision pair. Consequently, for every
finite or infinite support $S$ inside this entire child,

$$
\neg L_1(S,(H_4,M,p_J,M,v_\star)).
\tag{23.2}
$$

Proof. Theorem 18.2 supplies four actual, distinct complete worlds
with the same acquired fifth and sixth responses. Theorem 19.1 puts
this actual $v_\star$ in $\mathcal V$, while the inherited definition
puts $p_J\in\mathcal P$. Thus the independent upper bound (22.1)
applies to their full child and permits at most four worlds. These
four already exist, proving (23.1). The upper-bound proof uses no
local existence premise; existence comes from the original eight
equations, and it discharges the premise needed for exact cardinality.

The precise coordinate association has the following sharper
certificate. From the component version of (19.3) at the fixed point,

$$
|z_i(p_J)-m_i|\le\eta_i+q_i\rho.
\tag{23.3}
$$

For the four $r$ coordinates the bounds are

| World | Coordinate index | $10^{24}(\eta_i+q_i\rho)$ | Assigned interval |
| --- | --- | --- | --- |
| $C$ | $5$ | $296419530456129$ | $I_1$ |
| $B$ | $3$ | $117712740203950$ | $I_2$ |
| $A$ | $1$ | $436698210487845$ | $I_3$ |
| $D$ | $7$ | $540609050271175$ | $I_4$ |

Exact rational endpoint comparisons give
$[m_i-\eta_i-q_i\rho,m_i+\eta_i+q_i\rho]
\subset\operatorname{int}I_k$ for every indicated row. The
coarse interval $[m_i-\rho,m_i+\rho]$ alone does not fit inside
$I_3$ for $A$ or $I_4$ for $D$; the component displacement is
required for this matching. Each $r$ is consequently the unique
$R_{18}$ root in its assigned interval at $(p_J,v_\star)$, and the
nonzero linear coefficient in Theorem 21.2 fixes the corresponding
$b$. The full-parent reconstruction fixes the complete lift. This
identifies the four possible lifts with the four actual worlds,
without inferring existence from elimination.

Theorem 19.1 gives both the exact $A,B$ final-J equality and all
five other final-J inequalities. Its four final-M intervals are
pairwise disjoint, so $f_{MM}$ is injective on the whole child
(23.1). Every final-M response fiber inside any $S$ therefore has
at most one complete world. Such a fiber fails $L_0$ in (1.5), so
the final-M conjunct required by $L_1$ fails for every $S$. Empty
and singleton supports also fail the original guard. This proves
(23.2), allowing overlapping pairs, replacement pairs, all label
reuse and any nominally infinite support. In fact (23.1) makes
every such support finite. Adding worlds from the same acquired
child cannot repair the missing final-M pair. ∎

## 24. Integer coefficients of the model-specific eliminant

**Definition 24.1 (Sparse coefficient certificate).** The following
rows specify $R_{18}=\sum c_{ijk}r^ip^jv^k$ in (20.3).
Each first entry is the ordered exponent triple $(i,j,k)$ and the
second is its integer coefficient $c_{ijk}$. Omitted coefficients
are zero. In particular the table is an exact polynomial definition,
not a list of approximate roots. It can be compared directly with
the $14$ by $14$ determinant of Definition 20.1 by multiplication
by the displayed base factors and the constant $52488000$.

| $(i,j,k)$ | $c_{ijk}$ |
| --- | --- |
| $(18,6,0)$ | $281961000000000$ |
| $(18,5,1)$ | $-313502400000000$ |
| $(18,5,0)$ | $216480097800000000$ |
| $(18,4,2)$ | $140197905000000$ |
| $(18,4,1)$ | $-183598036020000000$ |
| $(18,4,0)$ | $38770237644187500000$ |
| $(18,3,3)$ | $-32248497000000$ |
| $(18,3,2)$ | $59761081300500000$ |
| $(18,3,1)$ | $-21819533512808250000$ |
| $(18,3,0)$ | $-1305826437291597000000$ |
| $(18,2,4)$ | $4024671131250$ |
| $(18,2,3)$ | $-9350448896700000$ |
| $(18,2,2)$ | $4380240711656418750$ |
| $(18,2,1)$ | $808637782421944350000$ |
| $(18,2,0)$ | $-89049805697410355700000$ |
| $(18,1,5)$ | $-258215040000$ |
| $(18,1,4)$ | $701869919940000$ |
| $(18,1,3)$ | $-361624906848690000$ |
| $(18,1,2)$ | $-160223943658193820000$ |
| $(18,1,1)$ | $30169287387382657680000$ |
| $(18,1,0)$ | $239808455600285335680000$ |
| $(18,0,6)$ | $6635520000$ |
| $(18,0,5)$ | $-20081488896000$ |
| $(18,0,4)$ | $9701812813392000$ |
| $(18,0,3)$ | $10277902753362720000$ |
| $(18,0,2)$ | $-2540544442593776640000$ |
| $(18,0,1)$ | $-51793254288629718912000$ |
| $(18,0,0)$ | $1181282576058930689280000$ |
| $(17,6,0)$ | $11697160050000000$ |
| $(17,5,1)$ | $-13104101812500000$ |
| $(17,5,0)$ | $8463961281150000000$ |
| $(17,4,2)$ | $5912858463375000$ |
| $(17,4,1)$ | $-7348960727982000000$ |
| $(17,4,0)$ | $1483519110445186875000$ |
| $(17,3,3)$ | $-1373848967343750$ |
| $(17,3,2)$ | $2464101676362600000$ |
| $(17,3,1)$ | $-901480152387231056250$ |
| $(17,3,0)$ | $1852630614758298600000$ |
| $(17,2,4)$ | $173272946017500$ |
| $(17,2,3)$ | $-399858027945086250$ |
| $(17,2,2)$ | $200853447339149718750$ |
| $(17,2,1)$ | $1178764558700332916250$ |
| $(17,2,0)$ | $163581203033345828925000$ |
| $(17,1,5)$ | $-11230428600000$ |
| $(17,1,4)$ | $31398891817081500$ |
| $(17,1,3)$ | $-19320715680509565000$ |
| $(17,1,2)$ | $-565910651464761354750$ |
| $(17,1,1)$ | $-59412951723758184855000$ |
| $(17,1,0)$ | $-1002068877488319994248000$ |
| $(17,0,6)$ | $291133440000$ |
| $(17,0,5)$ | $-951691992768000$ |
| $(17,0,4)$ | $669833646565500000$ |
| $(17,0,3)$ | $52991656386354320400$ |
| $(17,0,2)$ | $5580283402943085196800$ |
| $(17,0,1)$ | $167175722773542968222400$ |
| $(17,0,0)$ | $-6465459314607758575488000$ |
| $(16,7,0)$ | $2632500000000$ |
| $(16,6,1)$ | $-2412000000000$ |
| $(16,6,0)$ | $-25778987032500000$ |
| $(16,5,2)$ | $468412500000$ |
| $(16,5,1)$ | $24551803095750000$ |
| $(16,5,0)$ | $58277850498875250000$ |
| $(16,4,3)$ | $177667500000$ |
| $(16,4,2)$ | $-10642238273456250$ |
| $(16,4,1)$ | $-49981742993062575000$ |
| $(16,4,0)$ | $1381789224939490031250$ |
| $(16,3,4)$ | $-92011609375$ |
| $(16,3,3)$ | $2743545339423750$ |
| $(16,3,2)$ | $16751914988508646875$ |
| $(16,3,1)$ | $-794180536379427397500$ |
| $(16,3,0)$ | $-358800186378400652722500$ |
| $(16,2,5)$ | $15729300000$ |
| $(16,2,4)$ | $-433954102623750$ |
| $(16,2,3)$ | $-2738662987915579500$ |
| $(16,2,2)$ | $166925606597690512500$ |
| $(16,2,1)$ | $161601580331149063275000$ |
| $(16,2,0)$ | $3973723002509355032096250$ |
| $(16,1,6)$ | $-1203120000$ |
| $(16,1,5)$ | $38271776460000$ |
| $(16,1,4)$ | $217682926930129500$ |
| $(16,1,3)$ | $-14658587741956167900$ |
| $(16,1,2)$ | $-23812074204232783632750$ |
| $(16,1,1)$ | $-1340397357819435481929750$ |
| $(16,1,0)$ | $-1479530902765750369259400$ |
| $(16,0,7)$ | $34560000$ |
| $(16,0,6)$ | $-1419395328000$ |
| $(16,0,5)$ | $-6691576819320000$ |
| $(16,0,4)$ | $414780030289321650$ |
| $(16,0,3)$ | $1140971295045214973520$ |
| $(16,0,2)$ | $110823773166903325036590$ |
| $(16,0,1)$ | $934342106402867173085520$ |
| $(16,0,0)$ | $-31216780548911643539112000$ |
| $(15,7,0)$ | $111574125000000$ |
| $(15,6,1)$ | $-103320356250000$ |
| $(15,6,0)$ | $-4456655095351500000$ |
| $(15,5,2)$ | $20684554687500$ |
| $(15,5,1)$ | $4898237975623050000$ |
| $(15,5,0)$ | $113237387029630687500$ |
| $(15,4,3)$ | $7464690953125$ |
| $(15,4,2)$ | $-2223610766705471250$ |
| $(15,4,1)$ | $-47312379333346303125$ |
| $(15,4,0)$ | $-64983014889925613400000$ |
| $(15,3,4)$ | $-3983787921875$ |
| $(15,3,3)$ | $533085775652855625$ |
| $(15,3,2)$ | $2750486153551683750$ |
| $(15,3,1)$ | $42016415828859017033625$ |
| $(15,3,0)$ | $2232134160162941119288500$ |
| $(15,2,5)$ | $691841940000$ |
| $(15,2,4)$ | $-71142806039973750$ |
| $(15,2,3)$ | $1255037152501550250$ |
| $(15,2,2)$ | $-10097512016622968190825$ |
| $(15,2,1)$ | $-1086858251282043827131950$ |
| $(15,2,0)$ | $-20238357387815524798996050$ |
| $(15,1,6)$ | $-53598960000$ |
| $(15,1,5)$ | $5009789862507000$ |
| $(15,1,4)$ | $-209312063799718500$ |
| $(15,1,3)$ | $1066222921549146072750$ |
| $(15,1,2)$ | $176092609292407586212110$ |
| $(15,1,1)$ | $6885610579010880780020280$ |
| $(15,1,0)$ | $5191476292651153238934570$ |
| $(15,0,7)$ | $1555200000$ |
| $(15,0,6)$ | $-145410233328000$ |
| $(15,0,5)$ | $9238451720292000$ |
| $(15,0,4)$ | $-41590600779643803000$ |
| $(15,0,3)$ | $-9489715182034635855510$ |
| $(15,0,2)$ | $-580992779299191555419640$ |
| $(15,0,1)$ | $-3878381517820338677568570$ |
| $(15,0,0)$ | $313443481402177642899545040$ |
| $(14,7,0)$ | $-158815181250000$ |
| $(14,6,1)$ | $89930548125000$ |
| $(14,6,0)$ | $-17111443304292750000$ |
| $(14,5,2)$ | $-2249134265625$ |
| $(14,5,1)$ | $19174277394129900000$ |
| $(14,5,0)$ | $2067841429274540458125$ |
| $(14,4,3)$ | $-5618524681250$ |
| $(14,4,2)$ | $-8914248768510993750$ |
| $(14,4,1)$ | $-1734765612990253921125$ |
| $(14,4,0)$ | $99631651760059410846000$ |
| $(14,3,4)$ | $2219172608750$ |
| $(14,3,3)$ | $2189784719877819375$ |
| $(14,3,2)$ | $584545048890477603750$ |
| $(14,3,1)$ | $-70844182348382774011575$ |
| $(14,3,0)$ | $-3537943032769888225842675$ |
| $(14,2,5)$ | $-636116370000$ |
| $(14,2,4)$ | $-298722769028683500$ |
| $(14,2,3)$ | $-98944313096640915000$ |
| $(14,2,2)$ | $18597322087780479191550$ |
| $(14,2,1)$ | $1809265060751636782496385$ |
| $(14,2,0)$ | $31139899829637714678369240$ |
| $(14,1,6)$ | $94333520000$ |
| $(14,1,5)$ | $21399797709027000$ |
| $(14,1,4)$ | $8421011668157321925$ |
| $(14,1,3)$ | $-2138214153515488435350$ |
| $(14,1,2)$ | $-309427252881111651139875$ |
| $(14,1,1)$ | $-10415267930705140671031260$ |
| $(14,1,0)$ | $13945519257347033181517050$ |
| $(14,0,7)$ | $-5064960000$ |
| $(14,0,6)$ | $-627474739440000$ |
| $(14,0,5)$ | $-288663422025592800$ |
| $(14,0,4)$ | $90881999485177155210$ |
| $(14,0,3)$ | $17679885195945061871100$ |
| $(14,0,2)$ | $876037112747708601138156$ |
| $(14,0,1)$ | $1264499593315944502957812$ |
| $(14,0,0)$ | $-815559397149448532961540054$ |
| $(13,7,0)$ | $-42484924980000000$ |
| $(13,6,1)$ | $38014303947000000$ |
| $(13,6,0)$ | $158535647683951500000$ |
| $(13,5,2)$ | $-7407199891225000$ |
| $(13,5,1)$ | $-177292659015041662500$ |
| $(13,5,0)$ | $-15317465770807306768125$ |
| $(13,4,3)$ | $-2641456247073125$ |
| $(13,4,2)$ | $81801717817536159375$ |
| $(13,4,1)$ | $12515207955734144561625$ |
| $(13,4,0)$ | $305537360152190946933600$ |
| $(13,3,4)$ | $1446015108561875$ |
| $(13,3,3)$ | $-19940102529479572500$ |
| $(13,3,2)$ | $-4097528305824404655000$ |
| $(13,3,1)$ | $-182779505661415891403700$ |
| $(13,3,0)$ | $-2297555524336452728876280$ |
| $(13,2,5)$ | $-265061597085000$ |
| $(13,2,4)$ | $2709556674053454000$ |
| $(13,2,3)$ | $672226570157468858775$ |
| $(13,2,2)$ | $40665797973846698733675$ |
| $(13,2,1)$ | $992701482397551646096185$ |
| $(13,2,0)$ | $-2205855679363871541128595$ |
| $(13,1,6)$ | $22386826520000$ |
| $(13,1,5)$ | $-194689779147948000$ |
| $(13,1,4)$ | $-55290262766534455725$ |
| $(13,1,3)$ | $-3979316129682813842745$ |
| $(13,1,2)$ | $-137104515802931526089325$ |
| $(13,1,1)$ | $-159135550895104043819643$ |
| $(13,1,0)$ | $11168609547462613033143762$ |
| $(13,0,7)$ | $-735108480000$ |
| $(13,0,6)$ | $5781542513184000$ |
| $(13,0,5)$ | $1825196130278820000$ |
| $(13,0,4)$ | $144032767072475373000$ |
| $(13,0,3)$ | $5936090316411381303150$ |
| $(13,0,2)$ | $64334528787432067368012$ |
| $(13,0,1)$ | $1109474755106615816336946$ |
| $(13,0,0)$ | $627167213373704369108209740$ |
| $(12,7,0)$ | $-203686471496250000$ |
| $(12,6,1)$ | $187481619466312500$ |
| $(12,6,0)$ | $-281638534264379212500$ |
| $(12,5,2)$ | $-39091754242268750$ |
| $(12,5,1)$ | $330550299047335695000$ |
| $(12,5,0)$ | $29515658193907553812500$ |
| $(12,4,3)$ | $-12522969253597500$ |
| $(12,4,2)$ | $-158898243419312851500$ |
| $(12,4,1)$ | $-24687887460015462393375$ |
| $(12,4,0)$ | $-863227138411552677802650$ |
| $(12,3,4)$ | $7298433327005000$ |
| $(12,3,3)$ | $40184205970352475000$ |
| $(12,3,2)$ | $8255822900193218805525$ |
| $(12,3,1)$ | $555103322511848832493575$ |
| $(12,3,0)$ | $10054267044731947033790850$ |
| $(12,2,5)$ | $-1371408843090000$ |
| $(12,2,4)$ | $-5652379336591047000$ |
| $(12,2,3)$ | $-1380037559518677551400$ |
| $(12,2,2)$ | $-133807743124863585459795$ |
| $(12,2,1)$ | $-4867016331336909058338975$ |
| $(12,2,0)$ | $-25169612741555713984634724$ |
| $(12,1,6)$ | $117549533360000$ |
| $(12,1,5)$ | $420041365144437000$ |
| $(12,1,4)$ | $115341011751264779700$ |
| $(12,1,3)$ | $14321932034249106690165$ |
| $(12,1,2)$ | $786164623529110362691515$ |
| $(12,1,1)$ | $9743820101860564475633223$ |
| $(12,1,0)$ | $-196219768329315226167672159$ |
| $(12,0,7)$ | $-3886667520000$ |
| $(12,0,6)$ | $-12900183210840000$ |
| $(12,0,5)$ | $-3856950292797590400$ |
| $(12,0,4)$ | $-573892814541698016300$ |
| $(12,0,3)$ | $-42422819951148291463482$ |
| $(12,0,2)$ | $-902054937937966726446756$ |
| $(12,0,1)$ | $24848108220318945754317786$ |
| $(12,0,0)$ | $410678133015909160191933648$ |
| $(11,7,0)$ | $1275014587871250000$ |
| $(11,6,1)$ | $-1169566193721187500$ |
| $(11,6,0)$ | $66213158072845612500$ |
| $(11,5,2)$ | $243503085666187500$ |
| $(11,5,1)$ | $-131965915824425726250$ |
| $(11,5,0)$ | $-17511017941074666525750$ |
| $(11,4,3)$ | $77643370571580625$ |
| $(11,4,2)$ | $86554214702529806625$ |
| $(11,4,1)$ | $15755180891548097250675$ |
| $(11,4,0)$ | $617592408091626171797775$ |
| $(11,3,4)$ | $-45455458095606875$ |
| $(11,3,3)$ | $-27187529812780240500$ |
| $(11,3,2)$ | $-5653514744149528672650$ |
| $(11,3,1)$ | $-411994671243949089514665$ |
| $(11,3,0)$ | $-6898376552311638266286015$ |
| $(11,2,5)$ | $8605753902580000$ |
| $(11,2,4)$ | $4510649094278331750$ |
| $(11,2,3)$ | $1012170888093868851825$ |
| $(11,2,2)$ | $103399759491348600025920$ |
| $(11,2,1)$ | $3285608846570861684794965$ |
| $(11,2,0)$ | $3583754689099746219406875$ |
| $(11,1,6)$ | $-746755379400000$ |
| $(11,1,5)$ | $-382725687219405000$ |
| $(11,1,4)$ | $-90466063367006969325$ |
| $(11,1,3)$ | $-11569404569001813031410$ |
| $(11,1,2)$ | $-526644587195830431575694$ |
| $(11,1,1)$ | $-815381346902577574134456$ |
| $(11,1,0)$ | $263627414461458806275048239$ |
| $(11,0,7)$ | $25140922240000$ |
| $(11,0,6)$ | $13126021801344000$ |
| $(11,0,5)$ | $3230581392686285100$ |
| $(11,0,4)$ | $486841944516293680830$ |
| $(11,0,3)$ | $28547709274587137676930$ |
| $(11,0,2)$ | $1426888166607259348356$ |
| $(11,0,1)$ | $-39222220702731903124042878$ |
| $(11,0,0)$ | $-485813541162222623284397442$ |
| $(10,7,0)$ | $-1714516555063500000$ |
| $(10,6,1)$ | $1576508402247225000$ |
| $(10,6,0)$ | $161908863906828037500$ |
| $(10,5,2)$ | $-329491752983392500$ |
| $(10,5,1)$ | $-112317591624511646250$ |
| $(10,5,0)$ | $279364557918124552500$ |
| $(10,4,3)$ | $-104212742107221250$ |
| $(10,4,2)$ | $19839816780822771750$ |
| $(10,4,1)$ | $-1352363530451157648675$ |
| $(10,4,0)$ | $-188567611771534923817125$ |
| $(10,3,4)$ | $61307832107473125$ |
| $(10,3,3)$ | $2967881022166143000$ |
| $(10,3,2)$ | $878365289363522813775$ |
| $(10,3,1)$ | $122409868014051126289605$ |
| $(10,3,0)$ | $3372669509338098667909755$ |
| $(10,2,5)$ | $-11647759309035000$ |
| $(10,2,4)$ | $-1464915332961227250$ |
| $(10,2,3)$ | $-226912280084029541700$ |
| $(10,2,2)$ | $-30288076886839312248615$ |
| $(10,2,1)$ | $-1328023534974787791864072$ |
| $(10,2,0)$ | $-21669492718294957297200294$ |
| $(10,1,6)$ | $1015454575410000$ |
| $(10,1,5)$ | $181979633419143000$ |
| $(10,1,4)$ | $26403799622820081750$ |
| $(10,1,3)$ | $3394769079076055492670$ |
| $(10,1,2)$ | $164236092455713931156547$ |
| $(10,1,1)$ | $5562813773912458705923870$ |
| $(10,1,0)$ | $14206482862245729257883453$ |
| $(10,0,7)$ | $-34407526240000$ |
| $(10,0,6)$ | $-7712696895696000$ |
| $(10,0,5)$ | $-1156504481773237800$ |
| $(10,0,4)$ | $-145783957586278141890$ |
| $(10,0,3)$ | $-6172178824442844868608$ |
| $(10,0,2)$ | $-243258682119518419917624$ |
| $(10,0,1)$ | $-16001878706098330066828776$ |
| $(10,0,0)$ | $281806618587987766855312026$ |
| $(9,7,0)$ | $439773888767062500$ |
| $(9,6,1)$ | $-404970488081362500$ |
| $(9,6,0)$ | $-20040067970958352500$ |
| $(9,5,2)$ | $79839394437790000$ |
| $(9,5,1)$ | $-3264395014362611250$ |
| $(9,5,0)$ | $-6772165704754097805000$ |
| $(9,4,3)$ | $28262795760856875$ |
| $(9,4,2)$ | $13351452197678248125$ |
| $(9,4,1)$ | $6120645189819369249375$ |
| $(9,4,0)$ | $449258099615096758046325$ |
| $(9,3,4)$ | $-15402145543139375$ |
| $(9,3,3)$ | $-6065475725660315250$ |
| $(9,3,2)$ | $-2222818121438184483225$ |
| $(9,3,1)$ | $-284023702817920180789065$ |
| $(9,3,0)$ | $-9826496962705335770868105$ |
| $(9,2,5)$ | $2795196516685000$ |
| $(9,2,4)$ | $1189578439168224750$ |
| $(9,2,3)$ | $404641430047794059775$ |
| $(9,2,2)$ | $67166989911522642659715$ |
| $(9,2,1)$ | $4517424290372040816896529$ |
| $(9,2,0)$ | $91131273134348773801076775$ |
| $(9,1,6)$ | $-233141389890000$ |
| $(9,1,5)$ | $-110266080740919000$ |
| $(9,1,4)$ | $-36850496723349782175$ |
| $(9,1,3)$ | $-7048075199430492390600$ |
| $(9,1,2)$ | $-684148026537323475364656$ |
| $(9,1,1)$ | $-30188653869783569596472808$ |
| $(9,1,0)$ | $-97455349369195619958271629$ |
| $(9,0,7)$ | $7552636000000$ |
| $(9,0,6)$ | $3962118909336000$ |
| $(9,0,5)$ | $1340804589012648000$ |
| $(9,0,4)$ | $277292742002717022540$ |
| $(9,0,3)$ | $33915108138126809086296$ |
| $(9,0,2)$ | $2458062613126332054044874$ |
| $(9,0,1)$ | $42188739135352039427272776$ |
| $(9,0,0)$ | $-2096104949743402813554519894$ |
| $(8,7,0)$ | $-13360664766937500$ |
| $(8,6,1)$ | $3777523919812500$ |
| $(8,6,0)$ | $-2795277112117852500$ |
| $(8,5,2)$ | $9928832919558750$ |
| $(8,5,1)$ | $23057492776626239250$ |
| $(8,5,0)$ | $4937668726970539282050$ |
| $(8,4,3)$ | $-3276207067287500$ |
| $(8,4,2)$ | $-19569754987766280000$ |
| $(8,4,1)$ | $-5268163869124430665725$ |
| $(8,4,0)$ | $-347775255599540041848915$ |
| $(8,3,4)$ | $-563253712701250$ |
| $(8,3,3)$ | $6816166799904675750$ |
| $(8,3,2)$ | $2140850372691019057650$ |
| $(8,3,1)$ | $244373002841550804008175$ |
| $(8,3,0)$ | $8251645282455651283998315$ |
| $(8,2,5)$ | $359823080130000$ |
| $(8,2,4)$ | $-1179592722784617000$ |
| $(8,2,3)$ | $-421574894774971732350$ |
| $(8,2,2)$ | $-63566991451863840167730$ |
| $(8,2,1)$ | $-4174153813667904971713056$ |
| $(8,2,0)$ | $-65175253985866168138858704$ |
| $(8,1,6)$ | $-51536214170000$ |
| $(8,1,5)$ | $100771388372226000$ |
| $(8,1,4)$ | $40619811783926602575$ |
| $(8,1,3)$ | $7274151634338083088180$ |
| $(8,1,2)$ | $702018648670562503479684$ |
| $(8,1,1)$ | $22413753776353677297281154$ |
| $(8,1,0)$ | $-144973160884344868194260601$ |
| $(8,0,7)$ | $2419717600000$ |
| $(8,0,6)$ | $-3390350605272000$ |
| $(8,0,5)$ | $-1540850184190817100$ |
| $(8,0,4)$ | $-309529644278285694420$ |
| $(8,0,3)$ | $-39117702101361025355676$ |
| $(8,0,2)$ | $-1998478351864103770814562$ |
| $(8,0,1)$ | $18711925461125207184271176$ |
| $(8,0,0)$ | $2710623282850926585549145782$ |
| $(7,7,0)$ | $472707251910225000$ |
| $(7,6,1)$ | $-427211422806345000$ |
| $(7,6,0)$ | $-144017129004397582500$ |
| $(7,5,2)$ | $82894019485622500$ |
| $(7,5,1)$ | $125624979354233291250$ |
| $(7,5,0)$ | $9797679342070846846650$ |
| $(7,4,3)$ | $29940109191258750$ |
| $(7,4,2)$ | $-39560275601410915125$ |
| $(7,4,1)$ | $-6798514960834181562600$ |
| $(7,4,0)$ | $-270614314392618665416005$ |
| $(7,3,4)$ | $-16201305975883750$ |
| $(7,3,3)$ | $4858493458469358375$ |
| $(7,3,2)$ | $1760639132105808813675$ |
| $(7,3,1)$ | $144264048237616528907550$ |
| $(7,3,0)$ | $3432859212825070618268223$ |
| $(7,2,5)$ | $2940573989865000$ |
| $(7,2,4)$ | $14677842513880500$ |
| $(7,2,3)$ | $-200679460713785171025$ |
| $(7,2,2)$ | $-27383938871198301342180$ |
| $(7,2,1)$ | $-1342685044947053325630591$ |
| $(7,2,0)$ | $-27309651593730861366063639$ |
| $(7,1,6)$ | $-245611745300000$ |
| $(7,1,5)$ | $-50698718870679000$ |
| $(7,1,4)$ | $8260264543843998675$ |
| $(7,1,3)$ | $2112111771088033808640$ |
| $(7,1,2)$ | $161844400487351260689966$ |
| $(7,1,1)$ | $9504418980290065695082062$ |
| $(7,1,0)$ | $102586555852249608949383927$ |
| $(7,0,7)$ | $7964484800000$ |
| $(7,0,6)$ | $3005087996784000$ |
| $(7,0,5)$ | $32286755756135700$ |
| $(7,0,4)$ | $-50520390281051278050$ |
| $(7,0,3)$ | $-5497503220728627346746$ |
| $(7,0,2)$ | $-765206747028002884606596$ |
| $(7,0,1)$ | $-36670994812379084185788426$ |
| $(7,0,0)$ | $93724753446222794732655846$ |
| $(6,7,0)$ | $153951032323350000$ |
| $(6,6,1)$ | $-111365610128782500$ |
| $(6,6,0)$ | $48048560956918215000$ |
| $(6,5,2)$ | $10145082636700625$ |
| $(6,5,1)$ | $-55679873895962451750$ |
| $(6,5,0)$ | $-6576265632598611335325$ |
| $(6,4,3)$ | $10355637895032500$ |
| $(6,4,2)$ | $24417933539756373000$ |
| $(6,4,1)$ | $5643883533226636706400$ |
| $(6,4,0)$ | $290259820353763043811765$ |
| $(6,3,4)$ | $-3565124381844375$ |
| $(6,3,3)$ | $-5224568821072347375$ |
| $(6,3,2)$ | $-1887032131070420536425$ |
| $(6,3,1)$ | $-186780879076099134370770$ |
| $(6,3,0)$ | $-5508490802257692619216164$ |
| $(6,2,5)$ | $461331431080000$ |
| $(6,2,4)$ | $563490048786474750$ |
| $(6,2,3)$ | $308015654455230891750$ |
| $(6,2,2)$ | $44597532912150385961280$ |
| $(6,2,1)$ | $2650130173690237875086775$ |
| $(6,2,0)$ | $37933358938627818230681130$ |
| $(6,1,6)$ | $-24786640910000$ |
| $(6,1,5)$ | $-26883779056962000$ |
| $(6,1,4)$ | $-24549787033936532100$ |
| $(6,1,3)$ | $-4682317097670471181440$ |
| $(6,1,2)$ | $-425628376700939191532961$ |
| $(6,1,1)$ | $-13192637494499893775042262$ |
| $(6,1,0)$ | $97205137942269157155633321$ |
| $(6,0,7)$ | $363526560000$ |
| $(6,0,6)$ | $305700120504000$ |
| $(6,0,5)$ | $762652697673855600$ |
| $(6,0,4)$ | $182278676990667492360$ |
| $(6,0,3)$ | $22721696373785552063784$ |
| $(6,0,2)$ | $1179831362120344307864772$ |
| $(6,0,1)$ | $-7269428231520127803332712$ |
| $(6,0,0)$ | $-1543497978224919601492965612$ |
| $(5,7,0)$ | $-455916709018912500$ |
| $(5,6,1)$ | $381449679086520000$ |
| $(5,6,0)$ | $54439165551188250000$ |
| $(5,5,2)$ | $-62127482294222500$ |
| $(5,5,1)$ | $-35341571454349505250$ |
| $(5,5,0)$ | $-2174362799632851995775$ |
| $(5,4,3)$ | $-29356845960326250$ |
| $(5,4,2)$ | $4112052339925972500$ |
| $(5,4,1)$ | $865878530022457515900$ |
| $(5,4,0)$ | $29711670190267269008475$ |
| $(5,3,4)$ | $13801718648952500$ |
| $(5,3,3)$ | $1954803651384981000$ |
| $(5,3,2)$ | $40923130832764631325$ |
| $(5,3,1)$ | $-681366253188490057665$ |
| $(5,3,0)$ | $9965706469830807346701$ |
| $(5,2,5)$ | $-2315363705530000$ |
| $(5,2,4)$ | $-656291733436167750$ |
| $(5,2,3)$ | $-64108611239856051600$ |
| $(5,2,2)$ | $-4277978532530243351730$ |
| $(5,2,1)$ | $-158947126710149901960504$ |
| $(5,2,0)$ | $1286514870271314641831592$ |
| $(5,1,6)$ | $179044080730000$ |
| $(5,1,5)$ | $74042120428092000$ |
| $(5,1,4)$ | $10318685045870938950$ |
| $(5,1,3)$ | $939772263816544415085$ |
| $(5,1,2)$ | $52129115619889732315767$ |
| $(5,1,1)$ | $-682861320536525317261413$ |
| $(5,1,0)$ | $-49620082784655854140897401$ |
| $(5,0,7)$ | $-5327416800000$ |
| $(5,0,6)$ | $-2954594307216000$ |
| $(5,0,5)$ | $-516868550696506500$ |
| $(5,0,4)$ | $-57532034539668933990$ |
| $(5,0,3)$ | $-4341916022420430717066$ |
| $(5,0,2)$ | $44743272171570520706700$ |
| $(5,0,1)$ | $15125902141507872048862254$ |
| $(5,0,0)$ | $249201558597546702210696858$ |
| $(4,7,0)$ | $52503881150587500$ |
| $(4,6,1)$ | $-62195152783792500$ |
| $(4,6,0)$ | $-13931189734286722500$ |
| $(4,5,2)$ | $20027730543647500$ |
| $(4,5,1)$ | $10415719019387529750$ |
| $(4,5,0)$ | $1409394333257886129750$ |
| $(4,4,3)$ | $2462221534775000$ |
| $(4,4,2)$ | $-1158001349963331750$ |
| $(4,4,1)$ | $-952309344856818886200$ |
| $(4,4,0)$ | $-60902497105369156504485$ |
| $(4,3,4)$ | $-2845652931579375$ |
| $(4,3,3)$ | $-852551257556229000$ |
| $(4,3,2)$ | $214160475710249637750$ |
| $(4,3,1)$ | $34054262544299420022390$ |
| $(4,3,0)$ | $1173218706093120056970363$ |
| $(4,2,5)$ | $662632356880000$ |
| $(4,2,4)$ | $298752599120499750$ |
| $(4,2,3)$ | $-13875965702738317350$ |
| $(4,2,2)$ | $-6773549010379776945855$ |
| $(4,2,1)$ | $-532395184569773278431753$ |
| $(4,2,0)$ | $-7737497489188015862580270$ |
| $(4,1,6)$ | $-66479515860000$ |
| $(4,1,5)$ | $-36534246422070000$ |
| $(4,1,4)$ | $-1036179587138425875$ |
| $(4,1,3)$ | $549375400238791691655$ |
| $(4,1,2)$ | $80816951120505777015327$ |
| $(4,1,1)$ | $2821013417419691554479357$ |
| $(4,1,0)$ | $-27542497060316628910734228$ |
| $(4,0,7)$ | $2517796800000$ |
| $(4,0,6)$ | $1589952290112000$ |
| $(4,0,5)$ | $120300383353419000$ |
| $(4,0,4)$ | $-14056699179152445210$ |
| $(4,0,3)$ | $-4077660688602846431958$ |
| $(4,0,2)$ | $-264197762883083648014632$ |
| $(4,0,1)$ | $1246117969430580169827198$ |
| $(4,0,0)$ | $358882373294915132418146370$ |
| $(3,7,0)$ | $17818142730075000$ |
| $(3,6,1)$ | $7500636903135000$ |
| $(3,6,0)$ | $-3846715977745957500$ |
| $(3,5,2)$ | $-13772887985780000$ |
| $(3,5,1)$ | $-85374761633508000$ |
| $(3,5,0)$ | $219615250711181886900$ |
| $(3,4,3)$ | $2419302640450000$ |
| $(3,4,2)$ | $1709240775033528750$ |
| $(3,4,1)$ | $7082698957050140550$ |
| $(3,4,0)$ | $-4583399481351912654450$ |
| $(3,3,4)$ | $1026597031097500$ |
| $(3,3,3)$ | $-702365483037543000$ |
| $(3,3,2)$ | $-61310861406270417375$ |
| $(3,3,1)$ | $-885475255959471344310$ |
| $(3,3,0)$ | $35769916238526414409824$ |
| $(3,2,5)$ | $-413637701505000$ |
| $(3,2,4)$ | $114841760592361500$ |
| $(3,2,3)$ | $19248977255649813450$ |
| $(3,2,2)$ | $1097900579464904373705$ |
| $(3,2,1)$ | $12971043617839508409300$ |
| $(3,2,0)$ | $-469117696518566190781470$ |
| $(3,1,6)$ | $52207861800000$ |
| $(3,1,5)$ | $-8100815528223000$ |
| $(3,1,4)$ | $-2286506676728847150$ |
| $(3,1,3)$ | $-210440650894541776620$ |
| $(3,1,2)$ | $-7400111465175954562998$ |
| $(3,1,1)$ | $221643086977481068590930$ |
| $(3,1,0)$ | $5343490800444740750515476$ |
| $(3,0,7)$ | $-2284114560000$ |
| $(3,0,6)$ | $186262799616000$ |
| $(3,0,5)$ | $96519654141613200$ |
| $(3,0,4)$ | $12210778918209439620$ |
| $(3,0,3)$ | $713688633370920496446$ |
| $(3,0,2)$ | $-16173520504574591382696$ |
| $(3,0,1)$ | $-2255256990214861795690014$ |
| $(3,0,0)$ | $-18340547612442511868925948$ |
| $(2,7,0)$ | $4802345460900000$ |
| $(2,6,1)$ | $-2886428712930000$ |
| $(2,6,0)$ | $-213180354470745000$ |
| $(2,5,2)$ | $-107510147800000$ |
| $(2,5,1)$ | $723186342879480000$ |
| $(2,5,0)$ | $-68181649587964663200$ |
| $(2,4,3)$ | $351692250760000$ |
| $(2,4,2)$ | $-720676995939751500$ |
| $(2,4,1)$ | $24566869056152682900$ |
| $(2,4,0)$ | $4898332051598506487040$ |
| $(2,3,4)$ | $-69753748782500$ |
| $(2,3,3)$ | $301945437717751500$ |
| $(2,3,2)$ | $6672520716213887100$ |
| $(2,3,1)$ | $-2438439733766302193340$ |
| $(2,3,0)$ | $-111238594232317103084184$ |
| $(2,2,5)$ | $1621832045000$ |
| $(2,2,4)$ | $-62027856325253250$ |
| $(2,2,3)$ | $-4240729541933509050$ |
| $(2,2,2)$ | $389084516826338764755$ |
| $(2,2,1)$ | $49837710767809048000560$ |
| $(2,2,0)$ | $683052385628236708469484$ |
| $(2,1,6)$ | $680523520000$ |
| $(2,1,5)$ | $6236674107744000$ |
| $(2,1,4)$ | $668957885928690525$ |
| $(2,1,3)$ | $-17387531165773919880$ |
| $(2,1,2)$ | $-7556589780271291601847$ |
| $(2,1,1)$ | $-260368141871781765546156$ |
| $(2,1,0)$ | $4121866581189977961306612$ |
| $(2,0,7)$ | $-48364800000$ |
| $(2,0,6)$ | $-246704152920000$ |
| $(2,0,5)$ | $-34798708357713000$ |
| $(2,0,4)$ | $-404628380555355000$ |
| $(2,0,3)$ | $385304551800655978620$ |
| $(2,0,2)$ | $25941996301169048323896$ |
| $(2,0,1)$ | $-319060217488336140311748$ |
| $(2,0,0)$ | $-41516715015756270067633632$ |
| $(1,7,0)$ | $10651852684800000$ |
| $(1,6,1)$ | $-13199233946160000$ |
| $(1,6,0)$ | $-797551901097120000$ |
| $(1,5,2)$ | $4550154651540000$ |
| $(1,5,1)$ | $1177950097832292000$ |
| $(1,5,0)$ | $5035141734856545600$ |
| $(1,4,3)$ | $449014866500000$ |
| $(1,4,2)$ | $-615658603481244000$ |
| $(1,4,1)$ | $-24694990206969092400$ |
| $(1,4,0)$ | $841238662162692019680$ |
| $(1,3,4)$ | $-622908190410000$ |
| $(1,3,3)$ | $147889102587120000$ |
| $(1,3,2)$ | $14354789092081267500$ |
| $(1,3,1)$ | $-109049559818216137920$ |
| $(1,3,0)$ | $-22770486351146067734448$ |
| $(1,2,5)$ | $149921160250000$ |
| $(1,2,4)$ | $-16745159028268500$ |
| $(1,2,3)$ | $-3282094160800945200$ |
| $(1,2,2)$ | $-72348398324831599830$ |
| $(1,2,1)$ | $8153571068758682706456$ |
| $(1,2,0)$ | $156426252760199748124872$ |
| $(1,1,6)$ | $-15348605900000$ |
| $(1,1,5)$ | $730253397015000$ |
| $(1,1,4)$ | $336386485355937750$ |
| $(1,1,3)$ | $18099210219339861900$ |
| $(1,1,2)$ | $-842957008205002901460$ |
| $(1,1,1)$ | $-64243386275577969860352$ |
| $(1,1,0)$ | $650590483833086263918416$ |
| $(1,0,7)$ | $590696000000$ |
| $(1,0,6)$ | $-574165800000$ |
| $(1,0,5)$ | $-12951188034007500$ |
| $(1,0,4)$ | $-1152761507445381750$ |
| $(1,0,3)$ | $18218365393741244100$ |
| $(1,0,2)$ | $5801670583753643604990$ |
| $(1,0,1)$ | $57248321444495574116472$ |
| $(1,0,0)$ | $-7750841669805112825149000$ |
| $(0,7,0)$ | $1882751385600000$ |
| $(0,6,1)$ | $-2263677342720000$ |
| $(0,6,0)$ | $-151016590264320000$ |
| $(0,5,2)$ | $748023099920000$ |
| $(0,5,1)$ | $185688356712384000$ |
| $(0,5,0)$ | $3213119827373529600$ |
| $(0,4,3)$ | $86499824520000$ |
| $(0,4,2)$ | $-79489752877140000$ |
| $(0,4,1)$ | $-4582429898420995200$ |
| $(0,4,0)$ | $20139300986778011520$ |
| $(0,3,4)$ | $-104994784920000$ |
| $(0,3,3)$ | $13974915331788000$ |
| $(0,3,2)$ | $1930774481745552000$ |
| $(0,3,1)$ | $27732303000570925440$ |
| $(0,3,0)$ | $-1328950410111727441920$ |
| $(0,2,5)$ | $24568115060000$ |
| $(0,2,4)$ | $-606455904474000$ |
| $(0,2,3)$ | $-350157940064861400$ |
| $(0,2,2)$ | $-14881434899784436440$ |
| $(0,2,1)$ | $373016175423409668096$ |
| $(0,2,0)$ | $10595277593992649825568$ |
| $(0,1,6)$ | $-2463508550000$ |
| $(0,1,5)$ | $-90146197365000$ |
| $(0,1,4)$ | $28271364990156000$ |
| $(0,1,3)$ | $2354855881859675100$ |
| $(0,1,2)$ | $-11783192383653335640$ |
| $(0,1,1)$ | $-4549726426833142306416$ |
| $(0,1,0)$ | $31564683645673100745312$ |
| $(0,0,7)$ | $93076000000$ |
| $(0,0,6)$ | $7864914000000$ |
| $(0,0,5)$ | $-801730808347500$ |
| $(0,0,4)$ | $-123235854816726000$ |
| $(0,0,3)$ | $-2261785083620012100$ |
| $(0,0,2)$ | $354101571359596806480$ |
| $(0,0,1)$ | $8889210017909233702704$ |
| $(0,0,0)$ | $-442341971780697441347328$ |

## 25. Mathematical suppliers and the remaining response quantifiers

**Definition 25.1 (Correspondence and scope).** The consequence
(23.1)–(23.2) is ordinary model-specific repository-derived
mathematics (`repo-derived`). Its objects are complete worlds in
Definitions 1.1–1.3, and the exact algebraic fifth response is
inherited from Theorem 8.1. The new content is the off-twenty-four
acquired sixth-M child, its complete four-world classification and
its whole-child final-M injectivity. The uniform upper bound (22.1)
and the local construction (18.9) have different quantifiers and
are joined only at the actual response (18.8).

| Mathematical supplier | Exact use and hypothesis correspondence |
| --- | --- |
| This volume, Theorems 2.1, 4.1–4.2 and 12.3 | The zero-safe full parent, the complete singular fixed-width lines and the unique six-row whole-world lift. Here $\beta=1/8$, $\epsilon=d-24$, with the same $j,n,T,U,V$. These supply the reconstruction and singular branch, rather than a regular-chart restriction of the full child. |
| This volume, Theorem 8.1 and (8.1), (8.4) | The already defined unique six-coordinate root, its exact $p_J$ and its actual sixth-J $L_1$ child. No midpoint of its response enclosure replaces this premise, and no new sixth-J construction is inferred. |
| This volume, Definitions 1.1–1.3 and Sections 7, 12, 14 | Original clocks, complete-triple guards, actual left products, fixed-node response formulas and the specified exact interval and Sylvester conventions. The polynomial $D_\Lambda=N_4/2$ in (20.1) is distinguished from the $p=24$ graph denominator in (14.1). |
| [Terminal-zero-plane volume](FIB_TERMINAL_ZERO_PLANE_INVERSE_AND_J_PAIR_CHAMBER.md), Theorems 9.2–9.3 | At $(A,C,z,Y)=(24,147/5,24,18)$, $F=M$, its drift coefficients are $a_4=U\Lambda$ and $a_{5,M}=A_5$. Its full-source no-common-zero and fixed-source uniqueness apply also to $\Lambda=0$, arbitrary drift and unbounded positive offdiagonals. |
| Berrut–Trefethen, *[Barycentric Lagrange Interpolation](https://doi.org/10.1137/S0036144502417715)*, §2, (2.1)–(2.2) | `literature-attested` fixed distinct-node interpolation, with nodes $0,1,2,3$ and samples (18.3). The later values (18.4) are evaluations of that one polynomial. This standard result supplies no model-specific common-history pair or fiber count. |
| Banach contraction principle and the Neumann-series criterion, as used in Section 7 | Standard existence and zero equivalence, applied with the exact box, matrix and inequalities (18.7), (18.10)–(18.12). Their use supplies four actual lifts independently of the upper-bound proof. |
| Cox–Little–O'Shea, *[Ideals, Varieties, and Algorithms](https://doi.org/10.1007/978-3-319-16721-3)*, Chapter 3 | Standard resultant elimination. Equations (20.1)–(20.6) fix the actual polynomials and ordered determinant minors. Equation (20.10) supplies the necessary linear relation at common roots, with nonvanishing checked on every candidate box. |
| Basu–Pollack–Roy, *[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2)*, univariate real-root and subresultant methods | Standard real-root tools within the concrete certificates: the centered-parameter Bernstein/Descartes transformation (21.1)–(21.2), rational endpoint signs, and the signed Sturm rule (14.11) for all base factors. These tools are not separate new principles or classifications. |

All enclosures in Sections 18–23 are rational inclusions over their
stated full boxes. The equalities (18.9) and the final-J collision
come from exact original equations. The common value $v_\star$ is
never selected by rounding its interval. In the upper bound the
resultant is only necessary, negative $b$ lifts are illegal, and
singular sources are explicitly evaluated. The proof includes every
original legal sampled-zero, lower-degree, repeated-root and
zero-drift stratum at this acquired child; no uniform conditioning
or source bound is assumed. No physical realization or exhaustive
literature-priority claim accompanies this model-specific result.

The remaining exact-$p_J$ question is whether some acquired sixth-M
response $v\ne v_\star$ has, inside its one entire child
$\mathcal F(H_4,M,p_J,M,v)$, both a distinct final-J collision pair
and a distinct final-M collision pair. Theorem 23.1 excludes this
one $v_\star$ and every proposed support within it. It leaves other
terminal pairs, components, replacement worlds, discontinuous choices
and all legal strata at other $v$ available. The uniform bound
(22.1) is only an at-most-four statement on
$\mathcal P\times\mathcal V$; it does not assert final-M injectivity
at every other point of that rectangle, or classify all acquired
responses at $p_J$.

Thus the full fifth-$p_J$ fiber and the p-free common-parent M
$L_2$ system (17.1)–(17.2) retain their unresolved response
quantifiers. The same-parent $H_4$ $L_3$, all earlier ancestors,
the guarded root $L_7$, unrestricted deterministic adaptive
eight-read recovery or impossibility, comparison with nine total
readings and full-original-domain nine-read sufficiency remain
unresolved. Strategies still have no continuity, measurability,
computability or finite-description premise. The exact sixth-J
child at $p_J$, the $p=24$ exclusion and the mirror-component
statements keep their own previously stated scopes.

## 追加锚（本行以下为增补区）

## 26. The inherited exact parameter in a narrow rational interval

**Definition 26.1 (Entire sixth-M children and the parameter interval).**
Retain exactly the model (1.1)–(1.2), the literal history (1.4), and
all response functions (1.7). Thus each complete world has the strict
nonnegative rank-one idempotent $P(r,b)$, $0<r<1$, $b>0$, one entire
nonzero real gain polynomial of degree at most three, and one fixed
real drift, at the original clocks $0,\ldots,7$. Lower degrees,
sampled zeros, repeated gain roots, zero drift, singular sources and
unbounded positive offdiagonals remain included. Set

$$
\mathcal C_v=\mathcal F(H_4,M,p_J,M,v),\qquad
p_c=2744214237392974691433531179656369993836520133001835\cdot10^{-50},
\quad h_p=10^{-40},\quad \mathcal K=[p_c-h_p,p_c+h_p].
\tag{26.1}
$$

Here $p_J$ is exactly (8.4), at the unique zero $z_J$ of (8.1) in
$\mathcal B_J$; neither $p_c$ nor another rational response replaces
it. In $\mathcal C_v$, the acquired response is $u_M=v$, and the two
terminal functions are $f_{MJ},f_{MM}$, each using its world's same
entire gain and drift. Define the rational vector

$$
\bar z=10^{-65}\begin{pmatrix}
37167628601645357039239931692567316942507744298499183101863573058\\
15867820374551216484478543909642311448334240424841487608028511343\\
53084263233500780640864798687162772058023806790719140489523657620\\
37446348952497214793773020692649629953376632953783280004187273388\\
65747256231737793733797288888315727537832424764159334831141487501\\
38022816676633669495425130849116059753179797644548761383361452793
\end{pmatrix}.
\tag{26.2}
$$

**Theorem 26.2 (Transport of the original exact fifth response).**
The parameter defined by Theorem 8.1 satisfies $p_J\in\mathcal K$.

Proof. Use the original $F_J,m_J,C_J$ in (8.1)–(8.2), without
rescaling or changing the root system. Exact substitution gives

$$
\|\bar z-m_J\|_\infty<10^{-18},\qquad
\|C_JF_J(\bar z)\|_\infty<2\cdot10^{-51}.
\tag{26.3}
$$

Theorem 8.1 supplies, on the entire original box,
$q=115486/10^8<1$ for the contraction $z\mapsto z-C_JF_J(z)$.
Both $\bar z$ and its inherited fixed point $z_J$ lie in that box.
The contraction inequality therefore gives

$$
\|\bar z-z_J\|_\infty\le\frac{2\cdot10^{-51}}{1-q}
 <3\cdot10^{-51}<2\cdot10^{-48}.
\tag{26.4}
$$

The original expressions (1.6), (2.1), (2.3), (7.1)–(7.2), (1.7)
on $\|z-\bar z\|_\infty\le2\cdot10^{-48}$ give the exact inclusion

$$
|p(W_0(z))-p_c|<10^{-44}.
\tag{26.5}
$$

For (26.3) substitute the rational vector (26.2); for (26.5) the
rational ball inclusions (30.2) below applied to those same expressions
supply the bound. Every denominator excludes zero, already on the
larger box by Theorem 8.1. Equations (26.4)–(26.5) imply (26.1)
for the original exact $p_J$. ∎

## 27. A polynomial representation of the terminal-M image

**Definition 27.1 (Inherited elimination polynomials and the image).**
Use $X,N,H,T,U$ of (12.1)–(12.2), and exactly
$D_\Lambda,K_\Lambda,Z_6,G_{6,\Lambda},\mathsf N_u,\mathsf A,\mathsf B$
of (20.1). In particular $D_\Lambda=N_4/2$,
$\mathsf A=5b(p-24)D_\Lambda+3(8b-1)H$ and
$\mathsf B=5bD_\Lambda v-\mathsf N_u$.
Write $R=R_{18}$ with its exact integer coefficients in Definition
24.1 and its scale and sign fixed by (20.3). Set
$E=\Psi_2\Psi_4\Phi$, using (20.2) and (4.5).
Retain the exact minors $\mathcal L_0,\mathcal L_1$ of (20.4)–(20.5),
including their divisor $72900r^6(r-1)^4$; these are polynomial
coefficients, distinct from the recursive guards $L_k$.
All these definitions apply to arbitrary $p,v$, without the response
rectangle hypotheses of Section 21. Now define

$$
\begin{gathered}
Z_7=2N+3bU,\qquad
G_{7,\Lambda}=(20T+84)XN-bT(70N+35X),\\
N_m=\frac{120bTD_\Lambda+12Z_7D_\Lambda(200b+11)
 -3K_\Lambda(bTXN+Z_7G_{7,\Lambda})}{T},\qquad
D_m=5bD_\Lambda.
\end{gathered}
\tag{27.1}
$$

For $C(r,b)=\sum_{k=0}^7C_k(r)b^k$, always padded to degree seven,
put

$$
\mathcal H(C)=\sum_{k=0}^7 C_k(r)(-\mathcal L_0)^k\mathcal L_1^{7-k},
\qquad F=\mathcal H(N_m),\quad G=\mathcal H(D_m).
\tag{27.2}
$$

**Theorem 27.2 (The actual terminal-M rational image).**
The quotient in (27.1) is exact in $\mathbb Z[r,b]$.
The coordinate degree pairs $(\deg_r,\deg_b)$ of $N_m,D_m$ are
$(6,7),(4,7)$ respectively; $N_m$ has $28$ nonzero terms. Moreover

$$
\deg_r F\le188,\quad\deg_r G\le186,\qquad
\deg_p F,\deg_v F,\deg_p G,\deg_v G\le42.
\tag{27.3}
$$

At every nonsingular parent world, $f_{MM}=N_m/D_m$.
At a nonsingular child source with $\mathcal L_1\ne0$, this is $F/G$.

Proof. The single four-node interpolant (12.6), at the original
clock seven, gives

$$
g(7)=\frac{12(200b+11)}{5T}
       +\epsilon\frac{G_{7,\Lambda}}{TXN}.
\tag{27.4}
$$

For $\Lambda\ne0$, (20.8)–(20.9) give
$\epsilon=-3K_\Lambda XN/(5D_\Lambda)$ and $D_m\ne0$.
The actual trace in (1.7) is $3U+2n=Z_7/b$.
Multiplying $24+\epsilon+(Z_7/b)g(7)$ by $5bD_\Lambda T$
yields the numerator in (27.1). Its value at $b=-1$ vanishes
identically in $r$, so division by the monic $T=b+1$ is exact over
$\mathbb Z[r,b]$. Expansion gives the stated degree pairs and term
count. Since each $\mathcal L_i$ has coordinate degrees $(26,6,6)$,
(27.2) gives (27.3). Theorem 20.2 fixes
$b=-\mathcal L_0/\mathcal L_1$ at every common finite root where
$\mathcal L_1\ne0$. Homogenization to the fixed degree seven gives

$$
F=\mathcal L_1^7N_m(r,b),\qquad
G=\mathcal L_1^7D_m(r,b),\qquad f_{MM}=F/G.
\tag{27.5}
$$

No gain sample, drift, gain leading coefficient or gain root difference
was divided out. These identities concern the entire original world. ∎

## 28. The determinant-defined response polynomial

**Definition 28.1 (Fixed padding and the polynomial Q).**
For degree bounds $m,n$, let $\operatorname{Res}^{m,n}_x(A,B)$ be
the fixed $(m+n)$ by $(m+n)$ Sylvester determinant. Its ordered rows
are $x^{n-1}A,\ldots,A,x^{m-1}B,\ldots,B$, with columns in descending
powers $x^{m+n-1},\ldots,1$; all absent coefficients are zero.
The degree bounds stay fixed under every specialization. Using exactly
the polynomials of Definition 27.1, define

$$
\begin{aligned}
a(p,v)&=[r^{18}]R,\\
E_1(p,v)&=\operatorname{Res}^{18,26}_r(R,\mathcal L_1),\\
E_2(p,v)&=\operatorname{Res}^{10,26}_r(E,\mathcal L_1),\\
E_3(p,v)&=\operatorname{Res}^{18,186}_r(R,G),\\
T_*(p,v,w)&=\operatorname{Res}^{18,188}_r(R,F-wG),\\
E_4(p,v)&=\operatorname{Res}^{18,17}_w(T_*,\partial_wT_*),\\
Q(p,v)&=a(p,v)E_1(p,v)E_2(p,v)E_3(p,v)E_4(p,v).
\end{aligned}
\tag{28.1}
$$

The input $F-wG$ is padded to degree $188$ in $r$, and $T_*$ and
its derivative are padded to degrees $18,17$ in $w$. Equations
(12.1)–(12.2), (20.1)–(20.5), (27.1)–(27.2), (28.1) are finite
polynomial and determinant definitions of $Q$, with no choice of a
primitive part, unspecified elimination operation or existential
projection. Definition 24.1 supplies the existing coefficient table
of $R$; no expansion of $Q$ is implicit in this notation.

**Theorem 28.2 (Integer coefficients and a response-degree bound).**
The expression (28.1) is an integer polynomial $Q\in\mathbb Z[p,v]$
with $\deg_v Q\le74935$.

Proof. Theorem 20.2 and Definition 20.1 give the exact integer
polynomials $R,\mathcal L_i$ and the source polynomials, including
all stated exact divisions. Theorem 27.2 supplies the remaining
integer inputs. Every fixed determinant and derivative in (28.1)
therefore remains polynomial over $\mathbb Z$.
A Sylvester determinant of bounds $m,n$ is homogeneous of degrees
$n,m$ in the two inputs' coefficient sets. The respective upper
bounds in $v$ for $a,E_1,E_2,E_3,T_*,E_4$ are

$$
\begin{gathered}
7,\qquad18\cdot6+26\cdot7=290,\qquad10\cdot6=60,\\
18\cdot42+186\cdot7=2058,\qquad
18\cdot42+188\cdot7=2072,\\
(18+17)\cdot2072=72520.
\end{gathered}
\tag{28.2}
$$

The $w$ degree of $T_*$ is at most eighteen because only the eighteen
rows arising from $F-wG$ depend on $w$. Differentiation in $w$ does
not increase its $v$ degree. Summing the five factor bounds gives
$7+290+60+2058+72520=74935$. Specialization may lower these degrees;
it cannot increase them. ∎

## 29. The two exhaustive singular-source responses

**Definition 29.1 (Explicit algebraic exceptional responses).**
Let $r_-,r_+$ be exactly the two strict roots of $\Phi$ specified
by Theorem 4.2 and its rational intervals (4.6). At $b=1/8$ use
$j=1/8+8r(1-r)$, $n=j+r$, $T=9/8$, and put

$$
\begin{aligned}
A_5(r)&=1+(n+5/4)(4-15/j+20/T-10/n),\\
a_6(r)&=10-36/j+45/T-20/n,\\
s_\pm(p)&=\left.
\left[24+24(5/2+n)+\frac{p-24}{A_5(r)}
              \{1+(5/2+n)a_6(r)\}\right]\right|_{r=r_\pm}.
\end{aligned}
\tag{29.1}
$$

**Theorem 29.2 (Coverage of every legal singular world).**
For every real fifth response $p$, the complete worlds in
$\mathcal F(H_4,M,p)$ with $\Lambda=0$ are exactly the unique
fifth-response lifts at $(r_-,1/8)$ and $(r_+,1/8)$.
Their acquired sixth-M responses are respectively $s_-(p),s_+(p)$.

Proof. The zero-safe parent equation (2.2) and $B_{\rm coef}>0$
force $b=1/8$ when $\Lambda=0$. Then (4.9), equivalently (22.2),
gives $\Lambda=\Phi(r)/(960jn)$. Theorem 4.2 supplies exactly the
two strict roots. At either, Lemma 12.2 gives $A_5\ne0$, since its
full strict-source assertion is $\Lambda^2+A_5^2>0$.
Theorem 12.3, or the entire singular lines of Theorem 4.1, gives
$\epsilon=(p-24)/A_5$ and the unique whole-world reconstruction.
It is legal for every $p$, including $p=24$, and its gain is nonzero
by the original unequal $0,24$ rows. Substitution into (22.3) gives
(29.1). No singular line or zero-drift value is removed. ∎

## 30. Exact root and image separation at response zero

**Definition 30.1 (Rational disks for the polynomial certificate).**
For a complex rational number $z$, put
$\mathrm u(z)=|\Re z|+|\Im z|$ and
$\mathrm l(z)=\max(|\Re z|,|\Im z|)$, so that
$\mathrm l(z)\le|z|\le\mathrm u(z)$.
Write $B(a,e)=\{z:|z-a|\le e\}$, and set $\rho=10^{-30}$.
At any center $c$ below, the notation $q_{ij}$ for a polynomial $P$
means its exact finite expansion

$$
P(c+x,p_c+y)=\sum_{i,j}q_{ij}x^iy^j.
\tag{30.1}
$$

Addition of disk centers and radii is exact; the following rational
inclusions specify multiplication and division:

$$
\begin{aligned}
B(a,e)B(b,f)&\subseteq B(ab,\mathrm u(a)f+\mathrm u(b)e+ef),\\
\frac{B(a,e)}{B(b,f)}&\subseteq
 B\left(\frac ab,\frac e{\mathrm l(b)-f}
 +\frac{\mathrm u(a)f}{\mathrm l(b)(\mathrm l(b)-f)}\right),
 \qquad \mathrm l(b)>f.
\end{aligned}
\tag{30.2}
$$

Centers may be replaced in each component by a nearest multiple of
$10^{-80}$ if the sum of the absolute component displacements is
added to the radius and that radius is rounded upward to a multiple
of $10^{-80}$. This is a rational outer inclusion. Every displayed
decimal power or center specifies an exact rational number.

**Theorem 30.2 (A uniform nonzero certificate for Q).**
For every real $p\in\mathcal K$, $Q(p,0)\ne0$.

Proof. For $P=R(r,p,0)$, its exact expansion (30.1) at each center
in the following table satisfies

$$
\frac{\sum_{(i,j)\ne(1,0)}\mathrm u(q_{ij})\rho^ih_p^j}
 {\mathrm l(q_{10})\rho}\le10^{-8}<1.
\tag{30.3}
$$

In particular $q_{10}\ne0$. Comparing with $q_{10}x$ on
$|x|=\rho$, Rouché's theorem gives exactly one root, counted with
multiplicity, in each open disk, uniformly for $p\in\mathcal K$.
The center columns are integers divided by $10^{40}$. Each final-M
column specifies a closed interval whose integer endpoints are
divided by $10^8$; together the two columns enclose $F/G$ at the
corresponding root, uniformly in $p$.

| Root | Real center integer | Imaginary center integer | Final-M real interval integers | Final-M imaginary interval integers |
| --- | --- | --- | --- | --- |
| 1 | -31286150750762348802582409638467942713210 | 0 | [-21887636653,-21887636652] | [-1,1] |
| 2 | -2510014337059397316607414505088077690918 | 0 | [-13457154407,-13457154406] | [-1,1] |
| 3 | -2201928132261813013156348402737147496681 | 0 | [-22257063649,-22257063648] | [-1,1] |
| 4 | -295339115593097622628545335531497584380 | 0 | [-429098031,-429098030] | [-1,1] |
| 5 | 6495400363492816083307776565981278600092 | 0 | [-429248955,-429248954] | [-1,1] |
| 6 | 7597956179996037506048366830960946112912 | 0 | [-316565929,-316565928] | [-1,1] |
| 7 | 8332844315115451824657774735864810594552 | 0 | [-19123156260,-19123156259] | [-1,1] |
| 8 | 8579543799807686620077353697156115092966 | 0 | [-12378084067,-12378084066] | [-1,1] |
| 9 | 13032005827875331206999793808430624224058 | 0 | [-22263129775,-22263129774] | [-1,1] |
| 10 | 15696137244599728988715826184137251622975 | 0 | [-54416627322,-54416627321] | [-1,1] |
| 11 | 21955821216897387232488869335883708357553 | 0 | [-1020006161,-1020006160] | [-1,1] |
| 12 | 147645156763814419992946682846077866533935 | 0 | [-28063165458,-28063165457] | [-1,1] |
| 13 | -3545882418108118881545305728183083288159 | -2816741025257046459800497011396257596596 | [-11160217993,-11160217992] | [-4018571031,-4018571030] |
| 14 | -3545882418108118881545305728183083288159 | 2816741025257046459800497011396257596596 | [-11160217993,-11160217992] | [4018571030,4018571031] |
| 15 | -2195809642070093369709174604000871308723 | -986606892418947139933972967341018785613 | [-365192715,-365192714] | [116970003,116970004] |
| 16 | -2195809642070093369709174604000871308723 | 986606892418947139933972967341018785613 | [-365192715,-365192714] | [-116970004,-116970003] |
| 17 | 126454269704896557137078182823930776094 | -8647072583113490383075719955918362469337 | [4103234087,4103234088] | [2409885444,2409885445] |
| 18 | 126454269704896557137078182823930776094 | 8647072583113490383075719955918362469337 | [4103234087,4103234088] | [-2409885445,-2409885444] |

The minimum distance between these centers in the maximum norm exceeds
$24/1000$, so the eighteen disks are disjoint. If
$a(p_c+y,0)=\sum_j a_jy^j$, its exact coefficients satisfy

$$
a_0\ne0,\qquad
\sum_{j\ge1}|a_j|h_p^j\le10^{-8}|a_0|.
\tag{30.4}
$$

Thus $R$ has degree eighteen throughout $\mathcal K$, and the eighteen
disks exhaust its complex roots, all simple. For
$P=\mathcal L_0(r,p,0),\mathcal L_1(r,p,0)$, (30.1) gives

$$
P\in B\left(q_{00},\sum_{i+j>0}\mathrm u(q_{ij})\rho^ih_p^j\right).
\tag{30.5}
$$

For $\mathcal L_1$ the radius in (30.5), divided by
$\mathrm l(q_{00})$, is at most $10^{-8}$ at every one of the
eighteen disks. Thus $\mathcal L_1\ne0$ there. Form the disk for
$b=-\mathcal L_0/\mathcal L_1$ by (30.2). Substitution into
$D_m,N_m$ in Horner order descending first in $b$ and then in $r$,
padded to their degree pairs in Theorem 27.2, gives the displayed
image rectangles through $N_m/D_m=F/G$. For $D_m$, the resulting radius
divided by the maximum norm of its center is at most $10^{-8}$ on
every disk. Hence $D_m\ne0$ and $G=\mathcal L_1^7D_m\ne0$.
All these are finite exact rational inequalities from the inherited
integer polynomials and (27.1); (30.1)–(30.2) specify their outer
inclusions on the full disks and parameter interval, not only at
center values.

The following ten real centers, also integers divided by $10^{40}$
and with radius $\rho$, give all roots of $E=\Psi_2\Psi_4\Phi$.

| Real center integer |
| --- |
| -3351069069459178730563748013341910269139 |
| -3090169943749474241022934171828190588602 |
| -1611881117277527956213452635364774515677 |
| -145131642254964415874148343533081827154 |
| 1348158750676386533670177160610812651109 |
| 8090169943749474241022934171828190588602 |
| 8685711315796832210935933386297551290576 |
| 9024496817720562653778726512965428561863 |
| 11022476073858015228425244669956840614183 |
| 12277238870939874475841267262409133494240 |

For this parameter-independent $E$, (30.3) is at most $10^{-8}$ at
each center. The disks are disjoint, and their ten simple roots
exhaust degree ten. The relative radius in (30.5) for
$\mathcal L_1(r,p,0)$ is also at most $10^{-8}$ at each disk.
Thus $\mathcal L_1$ vanishes at no $E$ root for any $p\in\mathcal K$.

The image rectangles in the first table are pairwise disjoint.
Even rows 4 and 5, the closest pair, have real intervals separated
by more than $10^{-3}$. Hence the eighteen complex $F/G$ values
are distinct, including projections outside the legal real source
domain. The fixed padded resultant has the product expression

$$
T_*(p,0,w)=a(p,0)^{188}
 \prod_{R(\alpha,p,0)=0}\{F(\alpha,p,0)-wG(\alpha,p,0)\},
\tag{30.6}
$$

with roots counted with multiplicity. It has degree eighteen in $w$
and no multiple root. Thus $a,E_1,E_2,E_3,E_4$ are all nonzero:
(30.4) supplies $a$, the two root covers and the nonzero
$\mathcal L_1$ supply $E_1,E_2$, the nonzero $G$ supplies $E_3$,
and the separated images supply $E_4$.
Their product proves the assertion. This certificate uses all complex
projected roots; it assumes no projected root has an actual legal lift. ∎

## 31. The finite necessary restriction for every sixth-M response

**Theorem 31.1 (At most 74937 possible collision responses at exact p_J).**
For the exact inherited parameter $p_J$,
$Q(p_J,0)\ne0$ and $\deg_v Q(p_J,v)\le74935$. For every real $v$,

$$
\begin{aligned}
&\bigl[\exists W\ne W'\in\mathcal C_v:
                   f_{MM}(W)=f_{MM}(W')\bigr]\\
&\qquad\Longrightarrow
 \bigl[Q(p_J,v)=0\ \lor\ v=s_-(p_J)\ \lor\ v=s_+(p_J)\bigr].
\end{aligned}
\tag{31.1}
$$

Consequently the responses for which one entire $\mathcal C_v$ can
contain both a distinct terminal-J pair and a distinct terminal-M
pair, with any overlap permitted, lie in the real roots of
$Q(p_J,v)$ together with the two explicit responses (29.1).
There are at most $74937$ such scalar responses. The same necessary
restriction applies to every support contained in $\mathcal C_v$.

Proof. Theorems 26.2 and 30.2 give $Q(p_J,0)\ne0$, and Theorem
28.2 gives the degree bound, so this is a nonzero univariate
polynomial at the original parameter.
Fix distinct worlds in (31.1). If either has $\Lambda=0$, Theorem
29.2 gives one of the two explicit singular responses. Suppose both
are nonsingular, and assume for contradiction that $Q(p_J,v)\ne0$.

Theorem 20.2 gives $\mathsf A=\mathsf B=0$ for each actual source.
The necessary common-finite-root implication of the fixed Sylvester
determinant gives $E(r)R(r,p_J,v)=0$ by (20.3), since $r\ne0,1$.
This implication holds even if a leading coefficient drops: at a
finite common root $t$ the nonzero vector of descending powers of
$t$ annihilates every row of the padded matrix, so its determinant
is zero. Similarly, (20.10) gives
$\mathcal L_1b+\mathcal L_0=0$ under every degree specialization.
Its proof only divides by $72900r^6(r-1)^4\ne0$.

If $E(r)=0$, nonzero $E_2$ forces $\mathcal L_1(r,p_J,v)\ne0$.
The exact identities (21.4), valid for arbitrary $p,v$, then force
$b=-1/2$ on $\Psi_2=0$, $b=-2/5$ on $\Psi_4=0$, or $b=1/8$
on $\Phi=0$. The first two violate $b>0$; the last gives
$\Lambda=0$ by (4.9), contrary to the branch. This reasoning still
applies at any intersection of base factors. Therefore both sources
are roots of $R$.

Nonzero $E_1$ forces $\mathcal L_1\ne0$ at every $R$ root. The
linear relation fixes $b=-\mathcal L_0/\mathcal L_1$ from $r$.
If the two worlds had the same $r$, they would have the same $b$,
and Theorem 12.3 would make their complete lifts identical. Their
$r$ coordinates are therefore distinct.

Nonzero $a$ makes $R$ have degree eighteen, and nonzero $E_3$ makes
$G$ nonzero at every complex $R$ root. For a polynomial of full
first degree $m$ and leading coefficient $a$, the fixed padded
resultant is $a^n\prod_i B(\alpha_i)$ even if the second input has
degree less than $n$. Thus the product formula (30.6), now at the
arbitrary response $v$, makes $T_*$ have degree eighteen in $w$.
By (27.5), the two distinct source roots have the same image
$f_{MM}$, which is consequently a multiple root of $T_*$.
Then $\operatorname{Res}^{18,17}_w(T_*,\partial_wT_*)=E_4=0$,
contradicting $Q\ne0$. This proves (31.1).

Every nonvanishing condition used to divide or fix a degree follows
from one of the five nonzero factors of $Q$, or from the strict-source
hypotheses. If a required factor vanishes, that response remains a
root of $Q$. Degree drops in the source inputs remain covered by the
padded common-finite-root implications; no genericity assumption
deletes those specializations. The only use of
the nonsingular formula (20.9) is on $\Lambda\ne0$, and Theorem
29.2 exhausts its complementary branch. The full-domain lift of
Theorem 12.3 uses $Z=\Lambda^2+A_5^2>0$ only under Lemma 12.2's
strict-source hypotheses. Lower-degree gains, sampled zeros,
repeated gain roots and zero drift have not been cancelled.
No compactness or upper bound on $b,c$ is used.

A nonzero real polynomial of degree at most $74935$ has at most
that many distinct real roots. Adding at most two singular responses
gives $74937$. A terminal-J pair is an additional requirement
inside that same acquired child, so any child containing both pairs
already satisfies the terminal-M necessary restriction. ∎

## 32. Mathematical correspondence and the remaining joint obligation

**Definition 32.1 (Suppliers and the unresolved witness system).**
The finite restriction (31.1) is ordinary model-specific
repository-derived synthesis (`repo-derived`). Definitions 1.1–1.3
and Theorem 2.1 supply the full original model and parent; Theorem
8.1 supplies the exact algebraic $p_J$, its root box and contraction
bounds; Theorem 12.3 supplies the zero-safe unique whole-world
lifts. Theorem 17.1 supplies the same-child terminal-pair equivalence
with all pair reuse permitted. Equations (20.1)–(20.6), (21.4),
Theorems 4.2 and 22.1, and the coefficient table in Definition 24.1
supply the source elimination, forced base-factor lifts and complete
singular sources. Their response-rectangle conclusions are not
extended to other responses; (31.1) uses their polynomial identities
and singular formulas with the new certificate of Section 30.

Sylvester resultants and subresultants are the standard tools cited
in Sections 17 and 25, especially Cox–Little–O'Shea,
*[Ideals, Varieties, and Algorithms](https://doi.org/10.1007/978-3-319-16721-3)*,
Chapter 3. Rouché's theorem is used only within the concrete disk
certificate (30.3). Rational univariate representation and separating
rational images have the literature background of Fabrice Rouillier,
*[Solving Zero-Dimensional Systems Through the Rational Univariate Representation](https://doi.org/10.1007/s002000050114)*,
and the parameter-dependent treatment by Wang, Wei, Xiao and Zheng,
[DOI 10.1145/3476446.3535496](https://doi.org/10.1145/3476446.3535496).
These supply general methods, not a FIB-specific collision conclusion.
The abstract real-closed-field decidability and algebraic-witness
transfer of [the fourth relation volume](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md),
Corollary 9.4, also do not imply (31.1) by themselves. No global
priority or exhaustive literature claim is attached to this synthesis.

For a candidate $v$, the remaining joint obligation is the existence
of four labeled strict sources $W_{J0},W_{J1},W_{M0},W_{M1}$, with
labels allowed to coincide across the two pairs, all reconstructed
by (12.5)–(12.6), satisfying simultaneously

$$
\begin{gathered}
0<r_{Fa}<1,\quad b_{Fa}>0,\quad
\mathsf S_{p_J}(r_{Fa},b_{Fa})=0,\quad
p(W_{Fa})=p_J,\quad u_M(W_{Fa})=v
\quad(F\in\{J,M\},\ a\in\{0,1\}),\\
f_{MJ}(W_{J0})=f_{MJ}(W_{J1}),\quad W_{J0}\ne W_{J1},\\
f_{MM}(W_{M0})=f_{MM}(W_{M1}),\quad W_{M0}\ne W_{M1}.
\end{gathered}
\tag{32.1}
$$

These are equalities and legalities of complete worlds in one entire
child, not marginal feasibility of projections. Determinant roots
may be extraneous; no root enumeration, feasible common child,
existence or absence of either pair is asserted for any candidate.
Finding such a joint witness at some candidate, together with the
inherited sixth-J child of Theorem 8.1, would give the local fifth-M
$L_2$ at $p_J$ by Theorem 17.1. Exclusion of (32.1) at every candidate
would exclude every sixth-M $L_1$ at that $p_J$. Both alternatives
remain unresolved. The exact four-world child of Theorem 23.1
retains its own response and does not classify other responses.

Other fifth responses, earlier ancestors, same-parent $L_3$, root
$L_7$, unrestricted cubic eight-versus-nine recovery or impossibility,
and full-original-domain nine-read sufficiency remain unresolved.
The finite necessary list implies neither minimax depth, a uniform
decision strategy nor a global lower or upper bound. No continuity,
measurability, computability or finite-description condition on
witnesses or strategies is imposed, and no physical realization is
inferred from these algebraic conditions.

## 追加锚（本行以下为增补区）
