# FIB JMMJM Forbidden Root Rectangles and the Bounded Drift Core

## 1. Complete worlds on one original ancestor

A complete world is $W=(P,g,\delta)$, where $P$ is a strictly entrywise
positive real $2\times2$ matrix of rank one and trace one,
$0\ne g\in\mathbb R[T]$ has degree at most three, and $\delta\in\mathbb R$.
No symmetry of $P$ is assumed. Both gain signs, lower degrees, sampled
roots and repeated roots are admitted until explicitly excluded. Put

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{J,M\}.
\tag{1.1}
$$

The reading at original clock $i$ is $g(i)\operatorname{tr}(A_iP)+\delta$.
The initial reading counts. Every atom has its immediate reading on one
unresettable, uncopyable trajectory. A chronological word $EF$ means first
$E$, then $F$, giving cumulative matrix $FEA$. There are no skipped reads,
unread compound acquisitions, additional ports or renumbered clocks.
Policies are arbitrary deterministic functions of the entire actual
history; no regularity or computational restriction is added.

Fix arbitrary $D_0,Y,z\in\mathbb R$ and $\lambda\ne0$, and exactly

$$
H=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
 M,D_0+312\lambda/5,J,Y,M,z).
\tag{1.2}
$$

All six readings of this literal $JMMJM$ ancestor remain imposed. Define

$$
f=g/\lambda,\quad d=(\delta-D_0)/\lambda,\quad
y=(Y-D_0)/\lambda,\quad \zeta=(z-D_0)/\lambda,\quad c_0=312/5.
\tag{1.3}
$$

The parameter $D_0$ is a reading, not an assumed drift. The six cumulative
matrices are $I,J,L,J+L,C,Q$, where

$$
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
C=\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad
Q=\begin{pmatrix}1&1\\3&2\end{pmatrix}=I+2J+2L-C.
\tag{1.4}
$$

Write

$$
P=\begin{pmatrix}r&u\\v&1-r\end{pmatrix},\quad
0<r<1,\quad u,v>0,\quad uv=r(1-r)\le1/4,\quad
j=u+v,\quad \ell=1+u,\quad t=j+\ell=1+2u+v>1.
\tag{1.5}
$$

These conditions are exactly source legality: determinant zero and trace
one imply rank one. Direct multiplication gives all six equations

$$
\begin{aligned}
f(0)+d&=0,\\
f(1)j+d&=24,\\
f(2)\ell+d&=48,\\
f(3)t+d&=c_0,\\
f(4)(1+r+j)+d&=y,\\
f(5)(j+2\ell-r)+d&=\zeta.
\end{aligned}
\tag{1.6}
$$

Every trace factor is positive. In general, if $B$ is a nonzero
entrywise nonnegative matrix, then
$\operatorname{tr}(BP)=\sum_{i,k}B_{ik}P_{ki}>0$. In particular

$$
JQ=\begin{pmatrix}3&2\\1&1\end{pmatrix}=2C-L,\qquad
MQ=\begin{pmatrix}3&2\\4&3\end{pmatrix}=I+2J+2L,
\tag{1.7}
$$

so the normalized sixth responses are

$$
v_J=d+f(6)(2+2r+2j-\ell),\qquad
v_M=d+f(6)(1+2t).
\tag{1.8}
$$

The normalized seventh response after chronological $EF$ is
$d+f(7)\operatorname{tr}(FEQP)$. It is $d$ for every $E,F$ when
$f(7)=0$. Raw responses are obtained by $s\mapsto D_0+\lambda s$.
Counterfactual response functions are not additional observations.

Let $\mathcal F(H)$ retain legality and every equation of (1.6). For any
known candidate set at a literal history, define the actual-child recursion

$$
\begin{aligned}
L_0(K,H')&\Longleftrightarrow |K|\ge2,\\
L_{q+1}(K,H')&\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{J,M\}}\exists w\in\mathbb R:\
L_q(K\cap\mathcal F(H',E,w),(H',E,w)).
\end{aligned}
\tag{1.9}
$$

The same fixed worlds and whole shared ancestor occur in every child.
For either sign of $\lambda$, $w\mapsto(w-D_0)/\lambda$ is a bijection
preserving response equalities, target distinction and child cardinality.
Induction on (1.9) preserves every $L_q$. The inverse returns the whole
world by $g=\lambda f$, $\delta=D_0+\lambda d$, with $P$ unchanged.

The model and history are those of *FIB self-calibrating relation
mathematics VII*, Definitions 1.1–1.3, and *FIB JMMJM Terminal-Root
Decoders and the Simultaneous Core*, Section 1. The latter volume's
Sections 3–5 and 8–9 supply the reused terminal-root core in Section 7
below. The continuous forbidden rectangles, exterior-drift whole-class
decoder and strict further core restrictions are the deductions developed
here. The general pair theorem and large coefficient arrays of VII are
not premises of these deductions.

## 2. Two closed forbidden root rectangles

**Theorem 2.1.** No legal world satisfying even the first four equations
of (1.6) has

$$
f(T)=\gamma(T-a)(T-b)(T-7),\quad \gamma\ne0,
\qquad (a,b)\in[3,4]\times[4,5]\ \text{or}\ [4,5]\times[5,6].
\tag{2.1}
$$

The assertion includes all edges, corners and permitted coincidences
$a=b=4$ or $a=b=5$. There is no restriction on $y,\zeta$.

**Proof, elimination without a clock-three division.** Put

$$
\begin{gathered}
s=a+b,\quad p=ab,\quad U=p-s+1=(a-1)(b-1),\\
V=p-2s+4=(a-2)(b-2),\quad W=p-3s+9=(a-3)(b-3).
\end{gathered}
\tag{2.2}
$$

Here $p,U,V>0$, $U-2>0$, while $W$ may be zero. The samples at
zero through three are $-7p\gamma,-6U\gamma,-5V\gamma,-4W\gamma$.
Thus $d=7p\gamma$ and, dividing only by $\gamma\ne0$,

$$
6Uj=7p-24/\gamma,\quad
5V\ell=7p-48/\gamma,\quad
4W(j+\ell)=7p-c_0/\gamma.
\tag{2.3}
$$

Eliminating $1/\gamma$ gives

$$
5V\ell=12Uj-7p,\qquad
20W(j+\ell)=78Uj-56p.
\tag{2.4}
$$

Define

$$
\begin{aligned}
D&=78UV-20WV-48WU\\
 &=10p^2+58ps-350p-108s^2+708s-840,\\
L_0&=19p-39s+99,\qquad K_0=9p-29s+109.
\end{aligned}
\tag{2.5}
$$

Multiplying the second equation in (2.4) by $5V$ and substituting
the first yields $5Dj=140p(2V-W)$. Since $2V-W=p-s-1$,

$$
Dj=28p(p-s-1),\qquad
D\ell=\frac{14}{5}pL_0,\qquad
D(\ell-j)=\frac{14}{5}pK_0.
\tag{2.6}
$$

For completeness the second identity follows from
$5V D\ell=12U\cdot28p(p-s-1)-7pD$ and
$336U(p-s-1)-7D=14VL_0$; the last follows from
$L_0-10(p-s-1)=K_0$. As $j>0$ and $p-s-1=U-2>0$,
the first identity proves $D>0$, including exclusion of $D=0$.
Consequently

$$
j=\frac{28p(p-s-1)}D,\quad
\ell=\frac{14pL_0}{5D},\quad
u=\ell-1,\quad v=1-\frac{14pK_0}{5D}.
\tag{2.7}
$$

The following four complete polynomial certificates contradict
$uv\le1/4$.

**First rectangle.** Substitute $a=3+X$, $b=4+Z$ with
$0\le X,Z\le1$. Then $p=12+4X+3Z+XZ$, $s=7+X+Z$. Set

$$
\begin{aligned}
E_1&=14pL_0-8D
 =186p^2-1010ps+4186p+864s^2-5664s+6720,\\
E_2&=35D-168pK_0
 =-1162p^2+6902ps-30562p-3780s^2+24780s-29400.
\end{aligned}
\tag{2.8}
$$

In the ordered monomial basis
$(1,X,Z,X^2,XZ,Z^2,X^2Z,XZ^2,X^2Z^2)$ the entire coefficient
rows are

$$
\begin{array}{c|rrrrrrrrr}
 &1&X&Z&X^2&XZ&Z^2&X^2Z&XZ^2&X^2Z^2\\ \hline
E_1&1584&632&-948&-200&702&-492&478&106&186\\
E_2&4536&14140&24276&5236&2730&6468&-2394&-70&-1162
\end{array}
\tag{2.9}
$$

Here $632X-200X^2\ge0$; the other terms of $E_1$ except
$-948Z,-492Z^2$ are nonnegative. Thus

$$
E_1\ge1584-948-492=144>0,\qquad
E_2\ge4536-2394-70-1162=910>0.
\tag{2.10}
$$

For $E_2$ the inequality drops its nonnegative terms and bounds the
three remaining monomials by one. Equations (2.7)–(2.8) give exactly

$$
\frac{E_1}{5D}=\ell-\frac85=u-\frac35,\qquad
\frac{E_2}{60D}=v-\frac5{12}.
\tag{2.11}
$$

Hence $u>3/5$, $v>5/12$ and $uv>1/4$, a contradiction.

**Second rectangle.** Substitute $a=4+X$, $b=5+Z$ with
$0\le X,Z\le1$. Then $p=20+5X+4Z+XZ$, $s=9+X+Z$. Put

$$
\begin{aligned}
E_3&=28pL_0-15D
 =382p^2-1962ps+8022p+1620s^2-10620s+12600,\\
E_4&=5D-28pK_0
 =-202p^2+1102ps-4802p-540s^2+3540s-4200.
\end{aligned}
\tag{2.12}
$$

The full rows in exactly the same basis are

$$
\begin{array}{c|rrrrrrrrr}
 &1&X&Z&X^2&XZ&Z^2&X^2Z&XZ^2&X^2Z^2\\ \hline
E_3&8320&7520&1876&1360&6506&-116&1858&1094&382\\
E_4&5440&1040&4004&-80&-2206&636&-918&-514&-202
\end{array}
\tag{2.13}
$$

Dropping nonnegative terms and bounding the remaining monomials by one,

$$
E_3\ge8320-116=8204>0,\qquad
E_4\ge5440-80-2206-918-514-202=1520>0.
\tag{2.14}
$$

Now

$$
\frac{E_3}{10D}=\ell-\frac32=u-\frac12,\qquad
\frac{E_4}{10D}=v-\frac12.
\tag{2.15}
$$

Both $u,v>1/2$, contradicting $uv\le1/4$ again.

**Complete coefficient identity.** Every entry of (2.9) and (2.13)
can be checked with the following single distribution identity. For

$$
F(p,s)=Ap^2+Bps+Cp+Es^2+F_0s+G,
$$

at $a=a_0+X,b=b_0+Z$ write $p_0=a_0b_0$, $s_0=a_0+b_0$,
$H=b_0X+a_0Z+XZ$, $N=X+Z$. Then exactly

$$
\begin{aligned}
F(p_0+H,s_0+N)={}&F(p_0,s_0)
 +(2Ap_0+Bs_0+C)H+(Bp_0+2Es_0+F_0)N\\
 &+AH^2+BHN+EN^2.
\end{aligned}
\tag{2.16}
$$

The constant, $H$ and $N$ coefficients and the remaining three
quadratic coefficients are respectively

$$
\begin{array}{c|rrr|rrr}
 &F(p_0,s_0)&[H]&[N]&A&B&E\\ \hline
E_1&(1584)&1580&-5688&186&-1010&864\\
E_2&(4536)&-10136&54684&-1162&6902&-3780\\
E_3&(8320)&5644&-20700&382&-1962&1620\\
E_4&(5440)&-2964&15860&-202&1102&-540
\end{array}
\tag{2.17}
$$

Here $(p_0,s_0)=(12,7)$ for the first two rows and $(20,9)$ for
the last two. To spell out all terms, if $H=hX+kZ+XZ$ then

$$
\begin{aligned}
H^2&=h^2X^2+2hkXZ+k^2Z^2+2hX^2Z+2kXZ^2+X^2Z^2,\\
HN&=hX^2+(h+k)XZ+kZ^2+X^2Z+XZ^2,\\
N^2&=X^2+2XZ+Z^2.
\end{aligned}
\tag{2.18}
$$

Thus no higher or unlisted coefficient is suppressed. The bounds hold
on the closed squares, and every variable denominator in this proof is
positive by (2.6). No division by $W$, $f(3)$, $a-b$, or an endpoint
root sample occurred. This proves both closed rectangles. ∎

## 3. A single-world sign invariant

**Theorem 3.1.** Every legal world on (1.2) with $f(7)=0$ satisfies

$$
f(4)f(5)<0\quad\Longrightarrow\quad f(3)f(6)<0.
\tag{3.1}
$$

**Proof.** A sign change supplies a root $b\in(4,5)$ by continuity.
If $f(3)=0$, the roots $3,b,7$ force a nonzero cubic proportional to
the product in the first forbidden rectangle. If $f(6)=0$, the roots
$b,6,7$ give the second rectangle. If both vanish there are already
four distinct roots. Hence $f(3),f(6)$ are nonzero.

Suppose their signs agree. If $f(4)$ has the opposite sign to $f(3)$,
there is a root $a\in(3,4)$, yielding $a,b,7$ in the first rectangle.
Otherwise $f(5)$ has the opposite sign to $f(6)$, giving a root in
$(5,6)$ and the second rectangle. Three distinct roots of a nonzero
polynomial of degree at most three force exactly the corresponding
cubic factorization. Theorem 2.1 excludes each case. Thus the two
nonzero samples have opposite signs. This argument imposes no extra
degree or simplicity hypothesis. ∎

## 4. Complete interpolation on a sixth-M response fiber

Fix one normalized drift $d$ and the entire same ancestor. Write

$$
A=24-d,\quad B=48-d,\quad C_*=c_0-d,\quad
Y_*=y-d,\quad Z_*=\zeta-d.
\tag{4.1}
$$

On a sixth-$M$ response fiber let $c=v_M-d$, so
$f(6)=c/(1+2t)$ and $f(3)=C_*/t$. Suppose $f(7)=0$.

**Lemma 4.1.** The complete gain is

$$
f(T)=\frac d{126}(T-3)(T-6)(T-7)
 +\frac{C_*}{36t}T(T-6)(T-7)
 -\frac c{18(1+2t)}T(T-3)(T-7).
\tag{4.2}
$$

Its full increasing-power coefficient vector is

$$
\left(
-d,\quad
\frac{9d}{14}+\frac{7C_*}{6t}-\frac{7c}{6(1+2t)},\quad
-\frac{8d}{63}-\frac{13C_*}{36t}+\frac{5c}{9(1+2t)},\quad
\frac d{126}+\frac{C_*}{36t}-\frac c{18(1+2t)}
\right).
\tag{4.3}
$$

All its samples needed here are

$$
\begin{array}{c|l}
i&f(i)\\ \hline
0&-d\\
1&-10d/21+5C_*/(6t)-2c/(3(1+2t))\\
2&-10d/63+10C_*/(9t)-5c/(9(1+2t))\\
3&C_*/t\\
4&d/21+2C_*/(3t)+2c/(3(1+2t))\\
5&2d/63+5C_*/(18t)+10c/(9(1+2t))\\
6&c/(1+2t)\\
7&0
\end{array}
\tag{4.4}
$$

**Proof.** The three numerator products in (4.2) are respectively

$$
T^3-16T^2+81T-126,\quad T^3-13T^2+42T,\quad
T^3-10T^2+21T.
\tag{4.5}
$$

They give (4.3) by distribution and (4.4) by substitution. The values
at $0,3,6,7$ are the required $-d,C_*/t,c/(1+2t),0$.
The difference from any other degree-at-most-three interpolant has
four distinct zeros, and therefore vanishes. The root bound follows
by successive division by the distinct linear factors. All variable
denominators are positive since $t>1$. This includes degree drops,
zero sixth gains and multiple roots. ∎

**Lemma 4.2 (equal trace parameter reconstructs the whole world).**
For fixed $d,c,y,\zeta$ with $AB\ne0$, two legal members of this
root-seven response fiber with the same $t$ are the same complete world.

**Proof.** Formula (4.2) first gives the same polynomial. Since
$f(1)j=A$ and $f(2)\ell=B$ and both traces are positive,
$f(1),f(2)\ne0$. Recover

$$
j=A/f(1),\qquad \ell=B/f(2),\qquad
u=\ell-1,\quad v=j-\ell+1.
\tag{4.6}
$$

Both $f(4),f(5)$ cannot vanish: their roots with seven would be the
forbidden pair $(a,b)=(4,5)$. If $f(4)\ne0$ use

$$
r=Y_*/f(4)-1-j;
\quad\text{if }f(4)=0\text{ use }r=j+2\ell-Z_*/f(5).
\tag{4.7}
$$

These determine $P$, and then the raw gain and drift follow from
(1.3). The unused late equation, positivity and rank one remain
membership conditions; reconstruction does not replace them. ∎

## 5. Exact early and late secants for an actual M collision

Consider two distinct legal worlds sharing $d,y,\zeta$, root seven and
sixth-$M$ response $d+c$. Assume $AB\ne0$. Lemma 4.2 implies their
parameters $t_1,t_2$ differ. All functions below are the interpolation
functions of this one response fiber, evaluated at its actual members.
Put

$$
q=(1+2t_1)(1+2t_2)>0,\qquad p=t_1t_2>1.
\tag{5.1}
$$

**Lemma 5.1 (early secant).** Define

$$
\begin{aligned}
D_1(t)&=tf(1)=-\frac{10d}{21}t+\frac{5C_*}{6}
                     -\frac{2c}{3}\frac{t}{1+2t},\\
D_2(t)&=tf(2)=-\frac{10d}{63}t+\frac{10C_*}{9}
                     -\frac{5c}{9}\frac{t}{1+2t},\\
a_1&=-\frac{10d}{21}-\frac{2c}{3q},\qquad
a_2=-\frac{10d}{63}-\frac{5c}{9q}.
\end{aligned}
\tag{5.2}
$$

Then

$$
\begin{gathered}
D_i(t_2)-D_i(t_1)=(t_2-t_1)a_i\quad(i=1,2),\\
\frac{A}{D_1(t)}+\frac{B}{D_2(t)}=1,\\
\frac{Aa_1}{D_1(t_1)D_1(t_2)}
 +\frac{Ba_2}{D_2(t_1)D_2(t_2)}=0.
\end{gathered}
\tag{5.3}
$$

If $d\ne0$ and $AB>0$, necessarily

$$
\frac27<\frac{-c}{d(1+2t_1)(1+2t_2)}<\frac57,
\qquad dc<0.
\tag{5.4}
$$

**Proof.** The first identities use exactly

$$
\frac{t_2}{1+2t_2}-\frac{t_1}{1+2t_1}
 =\frac{t_2-t_1}{q}.
\tag{5.5}
$$

At either actual world $A/D_1=j/t$ and $B/D_2=\ell/t$,
so their sum is one. Both gain samples and both $D_i$ are nonzero
by $AB\ne0$ and the positive trace equations. Subtract the two
reciprocal identities and cancel only $t_2-t_1\ne0$ to get the
last line of (5.3). Each denominator product there is positive:
at fixed $A$ the two $f(1)$ have the same nonzero sign, and likewise
for fixed $B$ and $f(2)$. If $AB>0$, the weights have a common
sign, forcing $a_1,a_2$ to have opposite signs, unless both vanish.
They cannot both vanish when $d\ne0$, because with
$R=-c/(dq)$ the exact identities are

$$
a_1=\frac{2d}{3}(R-5/7),\qquad
a_2=\frac{5d}{9}(R-2/7).
\tag{5.6}
$$

The distinct thresholds force exactly (5.4). This is a necessary
condition for an actual pair, not a construction from arbitrary $t$.
∎

**Lemma 5.2 (late secant, including zero samples).** Put

$$
\begin{aligned}
K_4(t)&=(1+2t)f(4)
 =\frac{2d}{21}t+\frac d{21}+\frac{4C_*}{3}
                    +\frac{2C_*}{3t}+\frac{2c}{3},\\
K_5(t)&=(1+2t)f(5)
 =\frac{4d}{63}t+\frac{2d}{63}+\frac{5C_*}{9}
                    +\frac{5C_*}{18t}+\frac{10c}{9},\\
b_4&=\frac2{21}\left(d-\frac{7C_*}{p}\right),\qquad
b_5=\frac4{63}\left(d-\frac{35C_*}{8p}\right).
\end{aligned}
\tag{5.7}
$$

For $i=4,5$ the exact identity is
$K_i(t_2)-K_i(t_1)=(t_2-t_1)b_i$. If $Y_*Z_*\ne0$, both late
samples are nonzero in both worlds and

$$
\frac{Y_*}{K_4(t)}+\frac{Z_*}{K_5(t)}=1,\qquad
\frac{Y_*b_4}{K_4(t_1)K_4(t_2)}
 +\frac{Z_*b_5}{K_5(t_1)K_5(t_2)}=0.
\tag{5.8}
$$

If $Y_*=0$, then $f_1(4)=f_2(4)=0$ and $b_4=0$.
If $Z_*=0$, then $f_1(5)=f_2(5)=0$ and $b_5=0$.
In particular neither zero case occurs for a distinct pair when
$dC_*<0$.

If $d\ne0$ and $Y_*Z_*>0$, necessarily

$$
dC_*>0,\qquad
\frac{35}{8}\frac{C_*}{d}<t_1t_2<7\frac{C_*}{d},
\qquad 0<d<273/5.
\tag{5.9}
$$

**Proof.** Expand (4.4) after multiplication by $1+2t$ to get
(5.7). Its differences use $1/t_2-1/t_1=-(t_2-t_1)/p$.
The two actual late trace factors sum exactly to

$$
(1+r+j)+(j+2\ell-r)=1+2t.
\tag{5.10}
$$

Dividing their original equations by the nonzero $K_i$ therefore
proves the first line of (5.8); subtraction proves its secant as
before. The denominator products are positive by positivity of the
late traces and the common nonzero readings $Y_*,Z_*$.

When a late residual is zero, the corresponding positive trace forces
both samples zero. Their two $K_i$ values vanish, so their secant
forces $b_i=0$ before any gain division. If $dC_*<0$, both
$d-7C_*/p$ and $d-35C_*/(8p)$ have the same nonzero sign as $d$;
thus neither $b_i$ is zero. Both late residuals cannot vanish even
in other drift ranges, by Theorem 2.1 at roots $4,5,7$.

If $Y_*Z_*>0$, the two terms of the secant have weights of one
sign. Thus $b_4,b_5$ have opposite signs or both vanish. Both
vanishing would imply $d=7C_*/p=35C_*/(8p)$, hence $C_*=d=0$,
inconsistent with $C_*=c_0-d$ and $c_0>0$. Opposite signs first
force $dC_*>0$. Because $C_*=c_0-d$, this means $0<d<c_0$.
The zero thresholds in (5.7) then give exactly the strict product
bounds in (5.9). Since $p>1$, its upper bound requires
$1<7(c_0-d)/d$, or $8d<7c_0$, giving $d<273/5$.
The fourth and fifth readings belong to the same worlds throughout;
separate marginal estimates have not been combined. ∎

## 6. One fixed M decodes the entire exterior-drift class

**Theorem 6.1.** Fix any full ancestor (1.2) and any fixed normalized
drift $d<0$ or $d>312/5$. The sixth response under the single fixed
action $M$ is injective on the entire known class

$$
\mathcal K_d^7=\{W\in\mathcal F(H):d_W=d,\ f_W(7)=0\}.
\tag{6.1}
$$

There is no restriction on $y,\zeta$, cardinality, gain degree,
gain sign, ancestor zeros or future zeros. One immediate sixth read
recovers the complete actual target, and the same action works on
every known subset. Both $L_1$ and $L_2$ are false on every such subset.

**Proof, injectivity.** Suppose two distinct worlds share the $M$
response $d+c$. Here $A,B\ne0$, $AB>0$, $d\ne0$ and $dC_*<0$.
Lemma 4.2 gives $t_1\ne t_2$. The early secant (5.4) gives $dc<0$;
hence $c$ and $C_*$ have the same nonzero sign. In both worlds,

$$
f(3)f(6)=\frac{C_*c}{t(1+2t)}>0.
\tag{6.2}
$$

The zero late branches of Lemma 5.2 are impossible since $dC_*<0$.
Thus (5.8) applies. Both $b_4,b_5$ have the same nonzero sign as
$d$. If $Y_*,Z_*$ had the same sign, both summands of (5.8) would
have that same nonzero sign after multiplication by $\operatorname{sgn}d$,
an impossibility. They therefore have opposite signs. The positive
late traces imply $f(4)f(5)<0$ in each world. Theorem 3.1 gives
$f(3)f(6)<0$, contradicting (6.2). No distinct pair shares the
response. This excludes every collision on the whole class at once,
including putative collisions involving disjoint pairs. ∎

**Actual-read inverse and legality.** Choose $M$, immediately read its
raw value $w$ at original clock six, and set

$$
c=(w-D_0)/\lambda-d.
\tag{6.3}
$$

The actual candidate supplies a legal $t>1$ in the fiber defined by
(4.2), all six equations (1.6), and source legality. Theorem 6.1
and Lemma 4.2 give uniqueness of this legal parameter: equal parameters
already give equal worlds, while different worlds cannot share this
response. Recover the full gain by (4.2), then $j,\ell,u,v,r$ by
(4.6)–(4.7), then $P,g=\lambda f,\delta=D_0+\lambda d$.
An arbitrary root of an eliminated equation, or arbitrary $t$ obeying
only a secant bound, is not an inverse candidate. All original
constraints, the nonzero gain and degree bound remain imposed. The
actual candidate supplies existence; injectivity supplies uniqueness.
No sign of $\lambda$ is excluded, and no zero sixth sample is divided
out. Empty classes are unreachable; a known singleton may stop.

For every known $K\subseteq\mathcal K_d^7$ and every real raw $w$,

$$
K_w=\{W\in K:D_0+\lambda[d+f_W(6)(1+2t_W)]=w\}
\quad\text{has }|K_w|\le1.
\tag{6.4}
$$

Consequently $L_0(K_w,(H,M,w))$ and $L_1(K_w,(H,M,w))$ are both
false for every $w$. The $M$ conjunct in (1.9) fails for both
$L_1(K,H)$ and $L_2(K,H)$; empty and singleton parents fail their
cardinality clause as well. At most seven total readings are used,
and every executed atom has its immediate read. This inverse is a
known-class inverse: root seven and fixed drift are hypotheses, not
consequences of observed equalities. The endpoint drifts $0,312/5$
and the internal drifts $24,48$ are the already established cases of
the terminal-root companion, not new exterior cases.

## 7. The credited terminal-root core, with every original constraint

The results and rational equivalence in this section are reused from
*FIB JMMJM Terminal-Root Decoders and the Simultaneous Core*, Sections
2–5 and 8–9. Their explicit formulation and supporting arguments are
included to state precisely what the new restrictions act on.

**Lemma 7.1 (credited root-seven interpolation).** If $f(7)=0$,
$f(0)=-d$ and $a_i=f(i)$ for $i=1,2,3$, then

$$
\begin{aligned}
20d+70a_1-84a_2+35a_3&=0,\\
f(4)&=a_1/2-9a_2/5+9a_3/4,\\
f(5)&=a_1-16a_2/5+3a_3,\\
f(6)&=a_1-3a_2+5a_3/2.
\end{aligned}
\tag{7.1}
$$

The full increasing-power coefficient vector is

$$
\left(-d,\ \frac{11d}{6}+3a_1-\frac{3a_2}{2}+\frac{a_3}{3},
-d-\frac{5a_1}{2}+2a_2-\frac{a_3}{2},
\frac d6+\frac{a_1}{2}-\frac{a_2}{2}+\frac{a_3}{6}\right).
\tag{7.2}
$$

**Proof.** The interpolation basis at $0,1,2,3$ is

$$
\begin{aligned}
\ell_0&=-(T-1)(T-2)(T-3)/6,&\ell_1&=T(T-2)(T-3)/2,\\
\ell_2&=-T(T-1)(T-3)/2,&\ell_3&=T(T-1)(T-2)/6.
\end{aligned}
\tag{7.3}
$$

Its evaluation rows at $4,5,6,7$ are respectively
$(-1,4,-6,4)$, $(-4,15,-20,10)$, $(-10,36,-45,20)$ and
$(-20,70,-84,35)$. The last gives the first line of (7.1).
Solving it for $f(0)$ and substituting in the other rows gives the
three stated sample identities. Distribution of
$-d\ell_0+a_1\ell_1+a_2\ell_2+a_3\ell_3$ gives (7.2).
Only fixed nonzero integer denominators occur. ∎

**Lemma 7.2 (credited exceptional drifts and late-root size bound).**
For each fixed $d\in\{0,24,48,c_0\}$, sixth $M$ is injective on
$\mathcal K_d^7$. Each entire known class
$\mathcal Z_{a7}=\{W\in\mathcal F(H):f(a)=f(7)=0\}$,
$a=4,5$, has at most two complete worlds, with arbitrary initial drift.

**Proof of the exceptional drift statement.** Put $k=j/\ell>0$.
Substitution of the first four readings into (7.1) gives

$$
20d+70A/j-84B/\ell+35C_* /(j+\ell)=0.
\tag{7.4}
$$

For $d=0$, multiplication by $j\ell(j+\ell)$ reduces this to
$(8k-5)(3k+2)=0$, hence $k=5/8$. Interpolation gives
$f(T)=cT(T-5)(T-7)$, $c=1/j>0$, $\ell=8j/5$ and
$v_M=-6c-156/5$, strictly decreasing in $c$.
For nonzero $d$, (7.4) reads

$$
20d\ell=84B-70A/k-35C_* /(k+1).
\tag{7.5}
$$

Its complete specializations are

$$
\begin{array}{c|c|c}
d&\ell&v_M-d\\ \hline
24&7(3k+1)/(5(k+1))&\frac{24}{7}(9-42k+10/(3k+1))\\
48&7(7k+10)/(40k(k+1))&\frac{24}{7}(69/7-14/k-480/(7(7k+10)))\\
c_0&7(20-9k)/(65k)&\frac{312}{7}(-1+12/(20-9k))
 +\frac{48}{5}(9k+1-8/k)
\end{array}
\tag{7.6}
$$

The last row has $0<k<20/9$ by positivity of $\ell$.
These are obtained from (7.1), with sixth samples respectively
$120(1-3k)/(7(3k+1))$, $480(k-2)/(7(7k+10))$ and
$312(9k-8)/(7(20-9k))$. The simplifications are certified by

$$
\begin{gathered}
(1-3k)(42k+19)=(9-42k)(3k+1)+10,\\
(k-2)(69k+70)-\tfrac{69}{7}k(7k+10)
 =-14(7k+10)-\tfrac{480}{7}k,\\
(9k-8)/(20-9k)=-1+12/(20-9k),\\
(9k-8)(k+1)/k=9k+1-8/k.
\end{gathered}
\tag{7.7}
$$

The row for $24$ strictly decreases; those for $48,c_0$ strictly
increase on their legal intervals. No sixth sample is divided out,
so its possible zeros $k=1/3,2,8/9$ are included. Equal responses
therefore fix $k$, then $\ell,j$ and the first four gain samples,
then the entire gain. At $d=0$, $f(4)=12c\ne0$ fixes $r$.
At the other drifts the gain has a root $q\in\{1,2,3\}$, so
$f(4),f(5)$ cannot both vanish along with $q,7$. A nonzero late
sample fixes $r$. The complete worlds coincide. The inverse and
all actual-child negations follow exactly as in (6.4).

**Proof of the late-root size bound.** The reading at $a$ forces
the common drift $d=y$ for $a=4$, or $d=\zeta$ for $a=5$.
Factor

$$
f(T)=(T-a)(T-7)(b+eT),\qquad b=-d/(7a).
\tag{7.8}
$$

For $d\notin\{0,24,48,c_0\}$, $b\ne0$ and the first three
noninitial samples are nonzero. Put $\mu=e/b$. The factors
$1+\mu,1+2\mu,1+3\mu$ are nonzero. With
$p_1=1+5\mu+6\mu^2$, $p_2=1+4\mu+3\mu^2$ and
$p_3=1+3\mu+2\mu^2$, the trace sum $A/f(1)+B/f(2)=C_*/f(3)$
becomes respectively

$$
10Ap_1+18Bp_2-45C_*p_3=0\quad(a=4),\qquad
5Ap_1+8Bp_2-15C_*p_3=0\quad(a=5).
\tag{7.9}
$$

The full coefficient triples, constant first, are

$$
\begin{array}{c|ccc}
a&1&\mu&\mu^2\\ \hline
4&17d-1704&13d-3768&-24d-1584\\
5&2d-432&-12d-672&-24d
\end{array}
\tag{7.10}
$$

Indeed the unsimplified triples are
$(10A+18B-45C_*,50A+72B-135C_*,60A+54B-90C_*)$ and
$(5A+8B-15C_*,25A+32B-45C_*,30A+24B-30C_*)$.
The first polynomial is not identically zero: its quadratic coefficient
vanishes only at $d=-66$, where its constant is $-2826$.
The second has nonzero quadratic coefficient. Hence at most two
$\mu$ values occur. The other late sample is nonzero by Theorem 2.1
at $(4,5)$, and fixes $r$ after the first two samples fix $j,\ell$.
Each $\mu$ thus supplies at most one world. Every other legality
condition and actual fifth equation still apply.

For $d\in\{24,48,c_0\}$ the additional root $q\in\{1,2,3\}$
forces the unique gain $d(T-a)(T-q)(T-7)/(7aq)$. At the two
non-root early clocks the traces determine $j,\ell$ (use
$\ell,j+\ell$ for $q=1$, $j,j+\ell$ for $q=2$, and $j,\ell$
for $q=3$); the other late sample is nonzero and fixes $r$.
At most one world results, without division by the root sample.

For $d=0$, $b=0$. If $a=4$, the samples at $1,2,3$ are
$18e,20e,12e$, requiring $j=4/(3e)$, $\ell=12/(5e)$ and
$j+\ell=26/(5e)$. The first two sum to $56/(15e)$, not
$78/(15e)$, a contradiction. If $a=5$, the gain is
$cT(T-5)(T-7)$, $c>0$, with $j=1/c$, $\ell=8/(5c)$,
$u=8/(5c)-1$, $v=1-3/(5c)$. Write $A_0=(y-12)/12$.
Then $r=A_0/c-1$ and the rank-one equation is

$$
c^2-(3A_0-11/5)c+A_0^2-24/25=0.
\tag{7.11}
$$

After multiplying by $c^2$, the two sides $uv$ and $r(1-r)$
are $(11/5)c-c^2-24/25$ and $3A_0c-2c^2-A_0^2$.
Thus (7.11) has at most two amplitudes, each fixing a whole world;
the fifth equation is retained and also requires $\zeta=0$.
These cases exhaust the drifts and include lower degrees and repeated
roots. ∎

**Proposition 7.3 (credited actual core reduction).** Let three pairwise
distinct fixed worlds on the full ancestor all satisfy $f_h(7)=0$.
Their triple has $L_2$ exactly when, for each sixth action $E$,
some pair has equal drift and equal $v_E$. If the triple has $L_2$
and no proper pair has $L_2$, all three drifts are one common $d$ and

$$
\begin{gathered}
d\notin\{0,24,48,c_0,y,\zeta\},\qquad
f_h(i)\ne0\quad(0\le i\le6),\\
\operatorname{sgn}f_1(6)=\operatorname{sgn}f_2(6)
 =\operatorname{sgn}f_3(6)\ne0,\\
v_J(W_1)=v_J(W_2)\ne v_J(W_3),\qquad
v_M(W_1)=v_M(W_3)\ne v_M(W_2)
\end{gathered}
\tag{7.12}
$$

after relabeling. Sources are pairwise distinct, as are the one-dimensional
polynomial subspaces containing the gains.

**Proof.** In an actual sixth child every seventh response is its
world's drift, irrespective of the last action. The child has $L_1$
exactly when it contains an equal-drift pair. This proves the stated
equivalence with every response quantifier. If the drifts are not
all equal, there is at most one equal-drift pair; it must collide
under both sixth actions, so it itself has $L_2$. Minimality therefore
forces common drift.

If that drift equals any ancestor reading, positivity forces every
gain to vanish there. For clocks $0,1,2,3$, Lemma 7.2's fixed-$M$
inverse contradicts $L_2$. For clock $4$ or $5$, its at-most-two
world bound contradicts the three distinct worlds. Conversely any
ancestor zero forces drift equal to its reading. This proves the
exceptional exclusions and nonvanishing through clock five.

For either action $\operatorname{sgn}(v_E-d)=\operatorname{sgn}f(6)$.
If the three signs do not all agree, either there is no colliding
pair or the only possible pair for either action is the one repeated
sign pair. In the latter case $L_2$ forces that proper pair to collide
under both actions, a contradiction. If all signs are zero every
proper pair has $L_2$. Thus their common sign is nonzero. If one
sixth action were constant on all three worlds, a collision pair for
the other action would again give a proper $L_2$ pair. Each action
therefore has exactly one pair and one singleton, and the pairs must
differ. Their intersecting endpoint gives precisely (7.12).

If two gains were proportional, their common nonzero constant term
$-d$ forces equality. The first two positive trace equations then
fix $j,\ell$, and the nonzero fourth sample fixes $r$, so the worlds
would coincide. If two sources agreed, the first four readings with
common drift would fix the gain by interpolation, again giving the
same world. This proves only the stated restricted pairwise diversity.
∎

**Theorem 7.4 (credited exact rational simultaneous system).** For
$d\notin\{0,24,48,c_0,y,\zeta\}$, the core of Proposition 7.3 is
realizable if and only if there are three pairwise distinct $k_h>0$
satisfying all the following conditions, evaluated with one common
$d,y,\zeta$:

$$
\begin{aligned}
N_d(k)&=(4032-84d)k^2+(168+21d)k+70d-1680,\\
\ell(k)&=\frac{N_d(k)}{20d\,k(k+1)},\quad j=k\ell,\quad
u=\ell-1,\quad v=(k-1)\ell+1,\quad \ell>1,\ v>0,\\
a_1&=\frac{24-d}{k\ell},\quad
a_2=\frac{48-d}{\ell},\quad
a_3=\frac{c_0-d}{(k+1)\ell}.
\end{aligned}
\tag{7.13}
$$

Let $f_k$ have exactly the coefficients (7.2), and define

$$
\begin{aligned}
h_4&=a_1/2-9a_2/5+9a_3/4,\\
h_5&=a_1-16a_2/5+3a_3,\\
h_6&=a_1-3a_2+5a_3/2,\qquad h_4h_5h_6\ne0,\\
r(k)&=(y-d)/h_4-1-k\ell,\qquad 0<r(k)<1,\\
(\ell-1)((k-1)\ell+1)&=r(k)(1-r(k)),\\
\zeta-d&=h_5((k+2)\ell-r(k)),\\
P_k&=\begin{pmatrix}r(k)&\ell-1\\(k-1)\ell+1&1-r(k)\end{pmatrix}.
\end{aligned}
\tag{7.14}
$$

Finally put

$$
U(k)=h_6(2+2r(k)+(2k-1)\ell),\qquad
V(k)=h_6(1+2(k+1)\ell),
\tag{7.15}
$$

and require a common nonzero sign for the three $h_6(k_h)$ and

$$
U(k_1)=U(k_2)\ne U(k_3),\qquad
V(k_1)=V(k_3)\ne V(k_2).
\tag{7.16}
$$

No equation or inequality in (7.13)–(7.16) may be dropped.

**Proof, necessity.** For an actual world $k=j/\ell>0$.
Equation (7.5), multiplied by $k(k+1)$, is exactly

$$
20d\ell k(k+1)=84B k(k+1)-70A(k+1)-35C_*k=N_d(k).
\tag{7.17}
$$

Its full coefficient list is

$$
\begin{array}{c|c|c}
\text{power of }k&\text{unsimplified}&\text{simplified}\\ \hline
2&84B&4032-84d\\
1&84B-70A-35C_*&168+21d\\
0&-70A&70d-1680.
\end{array}
\tag{7.18}
$$

Since $d\ne0$, (7.17) gives (7.13). Interpolation gives (7.2),
(7.14), and $f(7)=0$; the fourth reading fixes $r$, source legality
gives the determinant equation, and the actual fifth reading is the
retained last scalar equality. Formula (1.8) gives (7.15), and
Proposition 7.3 gives the sign and pair conditions. Equal $k$ fixes
$\ell,j$, the full gain and $r$, hence the world; distinct worlds
therefore have distinct $k$. Divisors are nonzero by $d\ne0$,
$k>0$, $\ell>1$ and $h_4\ne0$.

**Proof, sufficiency and actual children.** Conversely let every
condition hold. All four entries of $P_k$ are positive and its trace
is one; the retained determinant equation gives rank one.
The coefficient vector (7.2) is a nonzero degree-at-most-three gain
because its constant term is $-d\ne0$. Its first four samples are
$-d,a_1,a_2,a_3$ by (7.3). Equation (7.17) gives
$20d+70a_1-84a_2+35a_3=0$, hence $f_k(7)=0$. Its later samples
are exactly $h_4,h_5,h_6$. Every ancestor equation is

$$
\begin{aligned}
f_k(0)+d&=-d+d=0,\\
f_k(1)j+d&=\frac A{k\ell}(k\ell)+d=24,\\
f_k(2)\ell+d&=\frac B\ell\ell+d=48,\\
f_k(3)(j+\ell)+d&=\frac{C_*}{(k+1)\ell}(k+1)\ell+d=c_0,\\
f_k(4)(1+r+j)+d&=h_4(1+r+k\ell)+d=y,\\
f_k(5)(j+2\ell-r)+d&=h_5((k+2)\ell-r)+d=\zeta.
\end{aligned}
\tag{7.19}
$$

The worlds are distinct because their sources determine different
ratios $j/\ell$. None of their ancestor samples vanishes because
$d$ differs from every ancestor reading and each trace is positive.
Their sixth values are $d+U(k)$ and $d+V(k)$ and their terminal
values all equal $d$.

In the one fixed triple $K$, first action $J$ with actual raw response
$D_0+\lambda(d+U(k_1))$ retains exactly $\{W_1,W_2\}$.
Under each last action $F$, raw response $D_0+\lambda d$ retains
that same pair, so this sixth child has $L_1$. First action $M$
with response $D_0+\lambda(d+V(k_1))$ retains exactly
$\{W_1,W_3\}$, and either last action again retains it at raw
response $D_0+\lambda d$. Thus both action clauses of $L_2$
hold. The only $J$ collision pair is $\{1,2\}$ and the only $M$
collision pair is $\{1,3\}$; each proper pair fails one sixth-action
clause. Empty and singleton proper subsets fail cardinality. This
is exactly the inclusion-minimal core. Both normalization signs
return the original worlds $g_h=\lambda f_{k_h}$,
$\delta_h=D_0+\lambda d$ and readings
$Y=D_0+\lambda y,z=D_0+\lambda\zeta$. No feasibility verdict is
contained in this equivalence. ∎

## 8. The strictly bounded residual core and its exact root sectors

**Theorem 8.1.** Every simultaneous core of Proposition 7.3 and
Theorem 7.4 necessarily satisfies

$$
0<d<312/5,\qquad d\ne24,48,y,\zeta.
\tag{8.1}
$$

All of (7.13)–(7.16), including the common nonzero sixth sign,
rank-one equality, actual fifth reading, different collision pairs,
and pairwise source and shape distinctions, remain mandatory.
Sixth-gain signs here mean the signs of the normalized $f_h(6)$;
the raw signs are multiplied by $\operatorname{sgn}\lambda$.

If the common sixth gain is positive, then necessarily

$$
24<d<48,\qquad y>d,\qquad \zeta>d.
\tag{8.2}
$$

If the common sixth gain is negative, every gain is exactly a cubic
with three distinct simple roots $\alpha,\beta,7$. Its early root
is in the following unique unit interval:

$$
\begin{array}{c|c}
\text{drift}&\alpha\\ \hline
0<d<24&(0,1)\\
24<d<48&(1,2)\\
48<d<312/5&(2,3).
\end{array}
\tag{8.3}
$$

Its late root belongs to the same unit interval for all three worlds,
classified exactly by their common late readings:

$$
\begin{array}{c|c}
\text{late residual signs}&\beta\\ \hline
y<d,\ \zeta<d&(3,4)\\
y>d>\zeta&(4,5)\\
y>d,\ \zeta>d&(5,6).
\end{array}
\tag{8.4}
$$

The other sign combination $y<d<\zeta$ is impossible. The exact
factorization and all four coefficients in the negative sector are

$$
\begin{gathered}
f(T)=\frac d{7\alpha\beta}(T-\alpha)(T-\beta)(T-7),\\
\left(-d,\ \frac{d(\alpha\beta+7\alpha+7\beta)}{7\alpha\beta},
-\frac{d(\alpha+\beta+7)}{7\alpha\beta},
\frac d{7\alpha\beta}\right).
\end{gathered}
\tag{8.5}
$$

In particular its leading coefficient is positive.

**Proof of the drift reduction.** The credited core already excludes
$0,24,48,c_0,y,\zeta$. If $d<0$ or $d>c_0$, Theorem 6.1's
single fixed sixth $M$ is injective on the entire common-drift
root-seven class, contradicting the required actual $M$ collision.
Thus only (8.1) remains. This is a whole-class exclusion of drift
ranges, not a separate choice of decoder for separate pairs.

**Proof of the positive sixth sector.** In the core the actual $M$
pair is $\{1,3\}$. Its common $c=V(k_1)=V(k_3)$ has the common
sixth gain sign. Its parameters $t_h=(k_h+1)\ell_h$ differ by
Lemma 4.2. If $d$ were in $(0,24)$ or $(48,c_0)$, $AB>0$,
so (5.4) with $d>0$ would force $c<0$. Hence positive sixth gains
require $24<d<48$. Now $f(1)<0<f(2)$, so there is an early root
in $(1,2)$. Also $f(3)>0$ and $f(6)>0$. A negative value at four
or five would force two further distinct roots between three and
six. Together with the early root and seven this gives four distinct
roots, impossible. The core already excludes zero late samples, so
both are positive, and the positive traces give $y>d,\zeta>d$.

**Proof of the negative sixth sector.** The increasing first four
readings $0,24,48,c_0$ and positive trace factors force a sign change
in exactly the early interval listed in (8.3). Thus there is a root
$\alpha$ there. Since $C_*>0$ and $f(6)<0$, there is a root
$\beta\in(3,6)$ as well. These two roots and seven are distinct.
Their three linear factors exhaust the degree bound, proving the
gain is exactly cubic and each root simple, with no other roots.
Its initial value $-d$ gives exactly the positive scalar
$d/(7\alpha\beta)$ in (8.5); expansion gives every coefficient
shown. The denominators are positive since $d,\alpha,\beta>0$.

Between $\alpha$ and seven the sign is positive before $\beta$
and negative after it. Because $d\ne y,\zeta$, the late root is
neither four nor five. The signs of $f(4),f(5)$ therefore give
exactly (8.4), including the common interval for every world because
the readings and drift are common. The combination $y<d<\zeta$
would demand a negative then positive sign after $\alpha$ and before
seven, contradicting this one late crossing.

There is also a sign exclusion independent of the sixth sector:
for any root-seven world with $0<d<c_0$, the combination
$y<d<\zeta$ gives $f(0)<0<f(3)$ and $f(4)<0<f(5)$.
It forces distinct roots in $(0,3)$, $(3,4)$, $(4,5)$ and at seven.
Hence it is impossible even without a sixth-gain assumption. ∎

**Theorem 8.2 (quantitative actual-pair restrictions).** In any such
core, for the actual $M$ pair $\{1,3\}$ put

$$
t_h=(k_h+1)\ell_h>1,\qquad c=V(k_1)=V(k_3).
\tag{8.6}
$$

If $AB>0$ then

$$
\frac27<\frac{-c}{d(1+2t_1)(1+2t_3)}<\frac57.
\tag{8.7}
$$

If $(y-d)(\zeta-d)>0$, then

$$
\frac{35}{8}\frac{312/5-d}{d}<t_1t_3
 <7\frac{312/5-d}{d},\qquad d<273/5.
\tag{8.8}
$$

Consequently the entire remaining high-drift strip obeys

$$
273/5\le d<312/5\quad\Longrightarrow\quad
 y>d>\zeta,\quad f_h(6)<0,\quad
 \alpha_h\in(2,3),\quad\beta_h\in(4,5)\quad(h=1,2,3).
\tag{8.9}
$$

**Proof.** Lemma 4.2 ensures distinct $t_1,t_3$. Their pair belongs
to the same full ancestor and has one common $d,c,Y_*,Z_*$, so
(8.7) is exactly Lemma 5.1 and (8.8) is Lemma 5.2. The latter's
strict inequality excludes equal late signs even at $d=273/5$:
there the upper product bound would be $t_1t_3<1$, whereas each
$t_h>1$. In the strip of (8.9), the residuals are nonzero and
cannot have equal signs; the impossible order $y<d<\zeta$ was
excluded in Theorem 8.1. Thus $y>d>\zeta$. Since $273/5>48$,
the positive-sixth sector (8.2) is unavailable, so all sixth gains
are negative. Their intervals in (8.3)–(8.4) are exactly $(2,3)$
and $(4,5)$. This proves (8.9), including its lower endpoint. ∎

All these inequalities are necessary consequences of actual jointly
legal worlds. They are not sufficient realizability tests. In particular,
(8.5), (8.7) or (8.8) cannot replace the common fourth-reading
reconstruction, rank-one equation or fifth-reading equation in
(7.14), nor the shared sign and different-pair conditions in (7.16).
The full rational system together with these now-proved consequences
has the same feasibility question as before, on the strictly reduced
drift and root sectors. No exact triple and no emptiness proof for
this bounded core is supplied.

## 9. Permanent mathematical credits and open boundaries

The permanent companion *FIB JMMJM Terminal-Root Decoders and the
Simultaneous Core* supplies the earlier core: its Section 2 is the
root-seven interpolation (7.1)–(7.3); Section 3 supplies the actual-child
equal-drift-pair reduction; Section 4 supplies the four exceptional-drift
fixed-$M$ inverses; Section 5 supplies the two late-and-terminal-root
size bounds; Sections 8–9 supply the no-ancestor-zero, sign, different-pair,
diversity and exact rational equivalence retained in Section 7.
These are reused results, not new exclusions credited to this volume.
Its Section 6's conditioned pair separation and Section 7's sharp
roots-$\{5,7\}$ example retain their original scopes; neither an exact
bounded-core triple nor a general unrestricted pair theorem follows
from that example.

The new deductions relative to that core are Theorems 2.1 and 3.1,
the full $0,3,6,7$ interpolation and secants in Sections 4–5, the
entire exterior-drift known-class decoder in Section 6, and the strict
bounded-core and quantitative root restrictions of Section 8. Their
proofs use polynomial factorization, root counting and continuity,
interpolation, direct trace algebra and the four complete small
coefficient rows. These are established mathematical tools; their
application here carries no worldwide-priority or literature-completeness
claim. The isolated forbidden root set $\{4,5,7\}$ was already
excluded in the companion's Section 5. The two continuous closed
rectangles extend that isolated exclusion.

[FIB self-calibrating relation mathematics VII](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md),
Definitions 1.1–1.3, supplies the exact model, normalization and
$JMMJM$ matrices. Its Theorem 4.1 states general two-target $L_2$
exclusion using a separate large-array certificate. No theorem here
uses that general result or its nine coefficient matrices as a premise;
there is no independent large-array certification asserted here.
If that pair theorem is separately accepted, the companion's
variable-drift root-seven proper-pair branch can be removed, but the
bounded simultaneous system still requires its own feasibility proof.
Without that general result, unrestricted root-seven proper pairs
outside the conditioned classes resolved here remain outside these
exclusions.

VII's Sections 8–11 concern the specialized history

$$
H_*=(0,J,24,M,48,M,312/5,J,48/5,M,-532/5)
\tag{9.1}
$$

and its affine transports. In particular its Theorem 10.2 is a
known-domain sixth-$J$ inverse on an existential sufficiently small
source band $|\operatorname{tr}(JP)-1|<\varepsilon$. That theorem
allows arbitrary drift and root behavior inside its band; it is
not the fixed-drift, known-root-seven sixth-$M$ theorem of Section 6.
Its proof uses its exhaustive closed slice, two local inverses and
an unbounded-drift no-escape bridge. None of those specialized
hypotheses is inferred for arbitrary $y,\zeta$ here, and none is
needed for the rectangle or secant arguments. Band membership is a
known input restriction, not an observation. A result on either
promised class does not identify the unrestricted union.

All stated decoders select one action for an entire known class and
restrict it to every known subset, with arbitrary cardinality.
They never choose a separate arm for different unknown members.
The actual scalar is normalized before inversion for either sign of
$\lambda$, and all source inequalities, six ancestor equations and
original clocks remain part of the inverse domain. In particular,
$y=\zeta$ alone does not identify $d$, a root or a fixed-gain class.

The bounded core's exact unresolved question is whether one common
$d,y,\zeta$ and three simultaneously legal positive $k_h$ can satisfy
all of (7.13)–(7.16), now necessarily obeying Section 8, with the
$J$ pair $\{1,2\}$ and $M$ pair $\{1,3\}$. Separate realizations
of the two pairs cannot settle that question. Necessary eliminated
relations, interval bounds, or the absence of a displayed example
prove neither emptiness nor nonemptiness. No numerical feasibility
or experimental claim is made.

Unrestricted triples with nonzero or mixed terminal gains, arbitrary
unrelated drifts, the full actual fibers and larger families retain
their open obligations. On such sets, different sixth actions may
retain different pairs, including disjoint pairs in larger sets; a
shared-three child can require different terminal collision pairs.
The exterior theorem excludes its entire promised class, not these
unrestricted cases. The literal $MMJM$ and $MJMMJ$ histories are
not identified with $JMMJM$. The earlier $JMMJ$ joint losing-arm
realization and complementary parent arms remain unresolved here.

The original-root alternative remains whether
$n_{\mathrm{det}}(3,0)\ge9$ or a lawful complete-target decoder with
at most eight total original-clock readings exists for every complete
world, all gain signs, roots and degree drops, all initial actions,
actual histories and early stops. This volume settles neither
alternative. No Lean/kernel verification, general-neural-network or
empirical conclusion, numerical stability, resource or computational
cost guarantee, or global completion claim is supplied.

## 追加锚（本行以下为增补区）

## 10. A uniform two-world bound on actual terminal-root components

**Definition 10.1 (the component of one actual continuation).** Keep
the entire history (1.2), its normalization (1.3), every equation
(1.6), and source legality (1.5). For arbitrary normalized responses
$\sigma,\theta\in\mathbb R$ and $F\in\{J,M\}$, put

$$
\begin{aligned}
\mathcal R^7_{MF}(H;\sigma,\theta)=\{W\in\mathcal F(H):\;&
 f_W(7)=0,\quad v_M(W)=\sigma,\\
 &d_W+f_W(7)\operatorname{tr}(FMQP_W)=\theta\}.
\end{aligned}
\tag{10.1}
$$

This is the root-seven component of the single actual history
$(H,M,D_0+\lambda\sigma,F,D_0+\lambda\theta)$, with immediate
readings at original clocks six and seven. The ambient fiber imposes
no root-seven promise. Source, gain shape and drift are
initially variable in (10.1); studying this component supplies no
root-class label for that ambient fiber.

**Theorem 10.2 (uniform root-seven component bound).** For every
$D_0,Y,z\in\mathbb R$, every $\lambda\ne0$, every
$\sigma,\theta\in\mathbb R$ and either terminal action $F$,

$$
\bigl|\mathcal R^7_{MF}(H;\sigma,\theta)\bigr|\le2.
\tag{10.2}
$$

Equivalently, for every fixed $d,\sigma\in\mathbb R$,

$$
\bigl|\{W\in\mathcal F(H):f_W(7)=0,\ d_W=d,
                                      \ v_M(W)=\sigma\}\bigr|\le2.
\tag{10.3}
$$

Empty and singleton components are included. The bound is on complete
worlds, retaining all six ancestor readings, all strictly positive
rank-one trace-one sources without a symmetry requirement, arbitrary
constant drift, both signs of the nonzero gain, every actual degree at most three,
sampled roots and repeated roots. It is uniform over the whole
component, without a finite-cardinality premise on the ambient fiber.

**Proof, the terminal response and the two exceptional reconstruction
branches.** In (10.1) the actual terminal response is $d_W$ for
either $F$, so every retained world has $d_W=\theta$.
Conversely the set in (10.3) is exactly
$\mathcal R^7_{MF}(H;\sigma,d)$ for either terminal action. It
therefore suffices to prove (10.3), with $d$ now fixed.

First let $d=0$. The credited zero-drift calculation in Lemma 7.2,
equivalently Terminal-Root, Theorem 4.1, gives exactly

$$
\begin{gathered}
k=j/\ell=5/8,\qquad f(T)=cT(T-5)(T-7),\quad c>0,\\
j=1/c,\quad \ell=8/(5c),\quad
\sigma=-6c-156/5,\quad f(4)=12c\ne0.
\end{gathered}
\tag{10.4}
$$

Thus the actual sixth response fixes $c=-(\sigma+156/5)/6$,
and the fourth reading fixes $r=y/(12c)-1-1/c$. These fix the
whole world, subject to all remaining equations and source legality.
Although $k=5/8$ throughout this branch, $k$ alone does not fix
the amplitude $c$. At most one world survives the fixed response.

Next suppose $d\ne0$ but $d=y$. Positivity of the clock-four
trace in (1.6) forces $f(4)=0$. The entire roots-$\{4,7\}$
class has at most two worlds by the credited late-root bound of
Lemma 7.2, equivalently Terminal-Root, Theorem 5.1. Its proof
includes every exceptional drift and the exclusion of roots
$4,5,7$ by rank-one legality. Taking an actual sixth-response
subset cannot increase its cardinality. This handles the branch
where the clock-four sample cannot reconstruct $r$.

**Proof, the sixth-$M$ polynomial at every remaining drift.** Assume
henceforth $d\ne0$ and $d\ne y$. Set

$$
\begin{gathered}
A=24-d,\quad B=48-d,\quad C_*=312/5-d,\quad
n_1=168+21d,\quad k=j/\ell>0,\quad \nu=\sigma-d,\\
N_d(k)=84Bk^2+n_1k-70A,\\
Q_{6,d}(k)=-3Bk^2+(36-d/2)k+A.
\end{gathered}
\tag{10.5}
$$

The root-seven interpolation (7.1) and the first four actual
equations give

$$
\begin{aligned}
20d\ell k(k+1)
 &=84Bk(k+1)-70A(k+1)-35C_*k=N_d(k),\\
\ell k(k+1)f(6)
 &=A(k+1)-3Bk(k+1)+\tfrac52 C_*k=Q_{6,d}(k).
\end{aligned}
\tag{10.6}
$$

For the first identity the coefficient of $k$ is
$84B-70A-35C_*=168+21d$; for the second it is
$A-3B+5C_*/2=36-d/2$. The other coefficients are exactly
those displayed in (10.5). These identities divide by no gain
sample. Since $d\ne0$, $k>0$ and $\ell>1$, they imply

$$
N_d(k)\ne0,\qquad
\ell=\frac{N_d(k)}{20d\,k(k+1)},\qquad
f(6)=\frac{20d\,Q_{6,d}(k)}{N_d(k)}.
\tag{10.7}
$$

The actual sixth-$M$ trace is $1+2(k+1)\ell$. Consequently its
response equation is exactly

$$
\nu=\frac{20d\,Q_{6,d}(k)}{N_d(k)}
                         +\frac{2Q_{6,d}(k)}k,
\tag{10.8}
$$

and hence every legal world supplies a positive root of

$$
\begin{aligned}
\Pi_{d,\nu}(k)
 &=\nu kN_d(k)-20dkQ_{6,d}(k)-2Q_{6,d}(k)N_d(k)\\
 &=p_4k^4+p_3k^3+p_2k^2+p_1k+p_0,
\end{aligned}
\tag{10.9}
$$

with the complete coefficient list

$$
\begin{aligned}
p_4&=504B^2,\\
p_3&=6B(14\nu+45d-840),\\
p_2&=(168+21d)\nu-557d^2+40272d-689472,\\
p_1&=-2A(35\nu+66d-2352),\\
p_0&=140A^2.
\end{aligned}
\tag{10.10}
$$

For an explicit expansion of every coefficient, put
$q_2=-3B$, $q_1=36-d/2$, $q_0=A$ and $n_2=84B$,
$n_0=-70A$. Multiplication in (10.9) gives respectively

$$
\begin{array}{c|l}
\text{coefficient}&\text{uncollected expression}\\ \hline
p_4&-2q_2n_2\\
p_3&\nu n_2-20dq_2-2(q_2n_1+q_1n_2)\\
p_2&\nu n_1-20dq_1-2(q_2n_0+q_1n_1+q_0n_2)\\
p_1&\nu n_0-20dq_0-2(q_1n_0+q_0n_1)\\
p_0&-2q_0n_0.
\end{array}
\tag{10.11}
$$

Substitution of $A=24-d$, $B=48-d$ and $n_1=168+21d$
in these five expressions gives (10.10), without suppressing any
coefficient or parameter restriction.

**Proof, at most two positive roots for every real $d,\nu$.** The
following count applies to (10.9) for all real parameters, including
values outside the current reconstruction branch. At $d=24$,

$$
\Pi_{24,\nu}(k)
 =k^2\bigl(290304k^2+(2016\nu+34560)k+672\nu-43776\bigr).
\tag{10.12}
$$

After discarding the root $k=0$, which is outside $k>0$, the
remaining polynomial is a nonzero quadratic. At $d=48$,

$$
\Pi_{48,\nu}(k)
 =(1176\nu-39744)k^2+(1680\nu+39168)k+80640.
\tag{10.13}
$$

Its constant term is positive. Its quadratic coefficient vanishes
only at $\nu=1656/49$, where its linear coefficient is
$4701312/49\ne0$. Thus it has degree two or one and is never
the zero polynomial. Both exceptional drifts therefore give at
most two distinct positive roots.

For $d\notin\{24,48\}$, the polynomial has degree exactly four
and $p_4,p_0>0$. If it had three distinct positive roots, factor
their three real linear factors. The remaining factor is linear
with a real root. The product of all four roots is $p_0/p_4>0$,
so that fourth root is positive as well, including any coincidence
with the first three. Viete's coefficient formulas for four positive
roots force

$$
p_3<0,\qquad p_2>0,\qquad p_1<0.
\tag{10.14}
$$

These three inequalities are incompatible with (10.10). To see
this on the entire real drift axis, put

$$
\begin{aligned}
L_3&=14\nu+45d-840,&L_1&=35\nu+66d-2352,\\
R_3(d)&=-\tfrac12(1249d^2-81984d+1358784),\\
R_1(d)&=\tfrac15(-2983d^2+206832d-3390912).
\end{aligned}
\tag{10.15}
$$

The two exact decompositions of the middle coefficient are

$$
p_2=\frac{n_1L_3}{14}+R_3(d)
     =\frac{n_1L_1}{35}+R_1(d).
\tag{10.16}
$$

The quadratic inside $-2R_3$ has positive leading coefficient and
discriminant

$$
81984^2-4\cdot1249\cdot1358784=-67108608<0.
\tag{10.17}
$$

Equivalently it is
$1249(d-40992/1249)^2+67108608/(4\cdot1249)>0$.
Thus $R_3(d)<0$ for every real $d$.

If $d<-8$, then $A>0$, so $p_1<0$ forces $L_1>0$.
Here $n_1<0$ and $R_1<0$, the latter because all three terms
in its numerator are negative for $d<0$. The second decomposition
in (10.16) gives $p_2<0$.

If $-8\le d<48$, then $B>0$, so $p_3<0$ forces $L_3<0$.
Here $n_1\ge0$, and the first decomposition in (10.16) again
gives $p_2<0$, including $d=-8$.

If $d>48$, then $A<0$, so $p_1<0$ forces $L_1<0$,
while $n_1>0$. Writing $e=d-48>0$ gives the exact identity

$$
5R_1(48+e)=-2983e^2-79536e-335808<0.
\tag{10.18}
$$

The second decomposition in (10.16) yields $p_2<0$ here too.
These intervals exhaust all remaining drifts. Each contradicts
the necessary $p_2>0$ in (10.14). Hence (10.9) is a nonzero
polynomial with at most two distinct positive roots for every
real $d,\nu$.

**Proof, complete-world reconstruction and all legality filters.**
Return to $d\ne0,y$. Each positive root $k$ arising from a legal
world determines $\ell$ by (10.7), then $j=k\ell$. The first
four samples are exactly

$$
f(0)=-d,\quad f(1)=\frac A{k\ell},\quad
f(2)=\frac B\ell,\quad f(3)=\frac{C_*}{(k+1)\ell}.
\tag{10.19}
$$

They uniquely determine the entire degree-at-most-three gain by
(7.2)–(7.3). Positivity and $d\ne y$ make $f(4)\ne0$, so
the same actual fourth reading gives

$$
r=\frac{y-d}{f(4)}-1-k\ell,\qquad
u=\ell-1,\qquad v=(k-1)\ell+1.
\tag{10.20}
$$

Thus each legal positive $k$ gives at most one complete world.
In particular every retained candidate must still satisfy

$$
\begin{gathered}
\ell>1,\quad v>0,\quad 0<r<1,\quad
(\ell-1)((k-1)\ell+1)=r(1-r),\\
\zeta-d=f(5)((k+2)\ell-r).
\end{gathered}
\tag{10.21}
$$

The last line is the original fifth-reading equation, not a
new adjustable response. All six equations (1.6), the root-seven
condition and the sixth-response equation remain imposed.
An eliminated root of (10.9) is only a necessary candidate;
it is not asserted to satisfy these filters or to define a world.

No division by $f(1),f(2),f(3),f(5)$ or $f(6)$ occurred.
Thus the drifts $24,48,312/5,\zeta$ are retained, including
the degree exceptions (10.12)–(10.13). The possible zero-sixth
response is also retained: at $\nu=0$ the exact factorization is

$$
\Pi_{d,0}(k)=-2Q_{6,d}(k)(N_d(k)+10dk),\qquad
N_d(k)+10dk=10dk\bigl(2(k+1)\ell+1\bigr)\ne0
\tag{10.22}
$$

on the present legal chart. It therefore forces $Q_{6,d}(k)=0$,
exactly $f(6)=0$, without an additional legal exception. The gain
is nonzero because $f(0)=-d\ne0$ in this branch; (10.4) has
$c>0$, and the credited late-root class likewise retains nonzero
gain. No leading gain coefficient, root difference or discriminant
of a gain was divided out, so all degree drops and repeated roots
within the stated domain are included.

There are at most two positive $k$ values, each with at most one
world in this branch. Together with the zero-drift and $d=y$
branches this proves (10.3) and hence (10.2). Finally (1.3) gives
$g=\lambda f$ and $\delta=D_0+\lambda d$. For either sign of
$\lambda$, the response map is bijective and preserves complete
worlds and actual children, so the same count holds in raw readings.
∎

## 11. Mathematical correspondence and the remaining joint condition

**Definition 11.1 (component count and actual-child condition).**
For any known $K\subseteq\mathcal F(H)$, with no cardinality
restriction, its actual children after sixth $M$ and terminal $F$
are

$$
K_{M,\sigma;F,\theta}
 =K\cap\mathcal F(H,M,D_0+\lambda\sigma,
                         F,D_0+\lambda\theta).
\tag{11.1}
$$

Theorem 10.2 bounds their root-seven parts by two for every real
$\sigma,\theta$ and both $F$. These parts may be empty, singletons
or pairs. Its new cardinality content concerns the interior drift
range left after Theorem 6.1's exterior-drift injectivity and the
credited exceptional-drift inverses in Lemma 7.2. Those stronger
injections on their respective known classes remain prior results.
The roots-$\{4,7\}$ size bound used when $d=y$ is likewise
prior content. At $d=\zeta$, the credited roots-$\{5,7\}$
size bound already gives the same upper bound, while (10.9) also
covers that case without dividing by $f(5)$. The additional count
therefore concerns $0<d<312/5$ outside
$\{24,48,y,\zeta\}$, although Theorem 10.2 has no such exclusions.
The uniform quartic count (10.9)–(10.18) controls this remaining
variable-source, variable-shape component without acquiring either
label.

The complete actual-child condition remains exactly (1.9).
A surviving pair can satisfy $L_0$, so the upper bound two does
not make its terminal child a uniquely recoverable target. The
ambient child may also contain non-root-seven worlds. Thus the
component count supplies neither an injective response nor an
inverse on the ambient fiber. It does not bound the non-root-seven
part of a mixed child.

In particular the simultaneous feasibility problem (7.13)–(7.16)
still requires three distinct legal $k_h$ at one common
$d,y,\zeta$, with the actual $J$ collision pair $\{1,2\}$ and
actual $M$ collision pair $\{1,3\}$. The latter pair is compatible
with the cardinality upper bound two; the bound supplies neither
that pair nor the other pair nor their common realization. Rank
one, the same fourth and fifth readings, the sign restrictions
and every actual-child quantifier must hold jointly. Neither
nonemptiness nor emptiness of this full system follows from the
quartic root count.

As an inhabited instance within the proof's credited zero-drift
branch, take normalized data $D_0=0$, $\lambda=1$ and

$$
P=\begin{pmatrix}2/5&3/5\\2/5&3/5\end{pmatrix},\qquad
f(T)=T(T-5)(T-7),\qquad d=0.
\tag{11.2}
$$

Its source entries are positive, its trace is one, and
$uv=r(1-r)=6/25$, so it is legal. Its gain coefficient vector
is $(0,35,-12,1)$. The full actual trace and reading table is

$$
\begin{array}{c|c|c|c|c}
i&A_i&\operatorname{tr}(A_iP)&f(i)&
       d+f(i)\operatorname{tr}(A_iP)\\ \hline
0&I&1&0&0\\
1&J&1&24&24\\
2&L&8/5&30&48\\
3&J+L&13/5&24&312/5\\
4&C&12/5&12&144/5\\
5&Q&19/5&0&0\\
6&MQ&31/5&-6&-186/5\\
7&FMQ&\operatorname{tr}(FMQP)>0&0&0.
\end{array}
\tag{11.3}
$$

Every row follows by the matrices (1.4), (1.7), the polynomial
samples and trace multiplication; the last row holds for either
$F$. This is one world on $H(144/5,0)$, with sixth-$M$ response
$-186/5$ and terminal response zero. It demonstrates nonemptiness
of a component, not sharpness of the bound two or a losing-set
realization. It is an instance of the already credited zero-drift
family (10.4), rather than an additional decoder theorem.

The new model-specific deduction is Theorem 10.2 with its
parameter-uniform positive-root argument. Polynomial interpolation,
the factor theorem and Viete's formulas are established tools used
inside that deduction. The relevant permanent correspondences are:

| Mathematical source | Hypotheses and use |
| --- | --- |
| [Terminal-Root Decoders and the Simultaneous Core](FIB_JMMJM_TERMINAL_ROOT_DECODERS_AND_SIMULTANEOUS_CORE.md), Lemma 2.1, Theorems 4.1 and 5.1, Sections 8–9 | The interpolation, zero-drift inverse and roots-$\{4,7\}$ size bound are reused through Lemmas 7.1–7.2. Its rational system has extra nonvanishing hypotheses; (10.6) derives the needed identities directly and therefore retains the exceptional drifts. The simultaneous system remains joint. |
| [IX](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md), Theorem 3.1 | The complete compatible fiber is a rational graph over its legal source set. Conditional recovery of gain and drift from a supplied source does not identify that source. The count here concerns variable sources in one actual component, rather than a restatement of conditional rank five. |
| [Whole-Class Affine Decoders](FIB_JMMJM_WHOLE_CLASS_AFFINE_DECODERS.md), Sections 4–8; [VIII](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VIII.md), Theorem 2.1 | Fixed-source, fixed-shape and known-initial-root inverses retain their supplied class labels. None provides such a label for (10.1) or its ambient fiber. The zero-drift branch in (10.4) is credited reuse. |
| [VII](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md), Sections 4 and 8–11 | Pair exclusion and the specialized $H_*$ gain-ray and known-band inverses retain their own hypotheses. None of their coefficient arrays, slice certificates or local inverses is a premise of (10.9)–(10.18). The arbitrary late readings in Theorem 10.2 are not restricted to $H_*$. |
| [Nonzero-Terminal Collision Sparsity and Ratio Diversity](FIB_JMMJM_NONZERO_TERMINAL_COLLISION_SPARSITY_AND_RATIO_DIVERSITY.md), Sections 4–7 | Its terminal stratum requires $f(7)\ne0$. The nonzero-ratio cancellation and terminal matrix inverse do not apply when $f(7)=0$; they supply no cardinality bound for the component in (10.1). |
| [Zero-Sixth Root Rigidity and Terminal Collision Geometry](https://github.com/the-omega-institute/trureturing/blob/7a5bd6a6bce1b3213422b7b3a1eca2d6c10ec707/docs/develop/theory/FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md), Theorems 2.1, 4.1 and 6.1 | Its repeated-sixth rigidity implies that a world with $f(6)=f(7)=0$ cannot have a repeated root at six. Its three-terminal-coordinate injections require $f(7)\ne0$. Neither result gives the root-seven component count. Equation (10.22) retains a zero sixth gain with $f(7)=0$, including the simple-sixth-root possibilities. |
| Y. Li, K. Lee and Y. Bresler, [*A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems with Applications to Subspace and Sparsity Models*, arXiv:1501.06120v1](https://arxiv.org/html/1501.06120v1), Theorems 2.8 and 3.3 | Theorem 2.8 separates identification of the first-factor orbit among all compatible pairs from identification of the second factor conditional on the first. Theorem 3.3's BGPC sufficient condition assumes an entrywise nonvanishing gain vector, full row rank of the signal matrix, and a full-column-rank sensing matrix with indecomposable row space. Those hypotheses do not cover arbitrary sampled zeros, the affine drift and the complete-world target here. Neither theorem is a premise for the quartic bound. |

These correspondences distinguish the repository deduction from
its standard algebraic tools; they assert no external priority or
exhaustive classification. The uniform count asserts no two-world
sharpness, numerical stability or computational cost bound.

The original-root problem still quantifies over all legal worlds,
all deterministic policies and stops, both initial actions and
every actual history on one unresettable trajectory. A resolution
would require either a jointly realizable obstruction with the
original-root and earlier-history bridges, or a lawful complete-target
decoder on that full domain. No root acquisition, earlier-parent
gluing, exact losing triple, $L_2$ witness, eight-reading decoder
or nine-reading upper bound is supplied by the component count.
The alternative $n_{\mathrm{det}}(3,0)\ge9$ versus an everywhere
at-most-eight-reading decoder remains unresolved by these deductions.

## 追加锚（本行以下为增补区）
