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
