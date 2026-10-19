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
