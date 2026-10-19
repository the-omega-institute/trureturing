# FIB JMMJM Zero-Sixth Pair Injectivity and Joint Collision Obstructions

## 1. Complete worlds and the fixed full ancestor

A legal complete world is $W=(P,g,\delta)$, where $P$ is a strictly
entrywise positive real $2\times2$ matrix of rank one and trace one,
$0\ne g\in\mathbb R[T]$ has degree at most three, and
$\delta\in\mathbb R$. The source need not be symmetric. Both gain
signs, every lower degree, sampled roots and repeated roots are allowed.
Set

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
A_0=I,\quad A_i=E_iA_{i-1},\quad E_i\in\{J,M\}.
\tag{1.1}
$$

The reading at original clock $i$ is
$g(i)\operatorname{tr}(A_iP)+\delta$. The initial reading counts.
Every selected atom is immediately read on one unresettable, uncopyable
trajectory. A chronological word $EF$ acts by $FE$ and includes both
immediate readings. Actions, stops and answers may be arbitrary
deterministic functions of the entire actual history, without
regularity or computability assumptions. The target is the entire
triple $(P,g,\delta)$.

Fix arbitrary real $D_0,Y,z$ and $\lambda\ne0$, and the one literal
six-reading ancestor

$$
H=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
             M,D_0+312\lambda/5,J,Y,M,z).
\tag{1.2}
$$

Write $\mathcal F(H)$ for the legal complete worlds realizing all
six readings. Normalize by

$$
\begin{gathered}
f=g/\lambda,\qquad d=(\delta-D_0)/\lambda,\qquad
y=(Y-D_0)/\lambda,\qquad \zeta=(z-D_0)/\lambda,\\
\mathbf c=(c_0,\ldots,c_5)=(0,24,48,312/5,y,\zeta).
\end{gathered}
\tag{1.3}
$$

The inverse is $g=\lambda f$, $\delta=D_0+\lambda d$.
The map $w\mapsto D_0+\lambda w$ is a bijection of real response
values for either sign of $\lambda$, preserving equality and every
actual response partition. In particular the observed $D_0$ is not
assumed to equal the drift.

Use the legal source coordinates

$$
P=\begin{pmatrix}r&u\\v&1-r\end{pmatrix},\qquad
0<r<1,\quad u,v>0,\quad uv=r(1-r).
\tag{1.4}
$$

These conditions are exactly strict positivity, rank one and trace
one. The cumulative matrices are

$$
\begin{gathered}
(A_0,A_1,A_2,A_3,A_4,A_5)=(I,J,L,J+L,C_{\rm mat},Q),\\
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
J+L=\begin{pmatrix}1&1\\2&1\end{pmatrix},\quad
C_{\rm mat}=\begin{pmatrix}2&1\\1&1\end{pmatrix},\\
Q=\begin{pmatrix}1&1\\3&2\end{pmatrix},\qquad
Q^{-1}=\begin{pmatrix}-2&1\\3&-1\end{pmatrix}.
\tag{1.5}
\end{gathered}
$$

Direct multiplication gives all six actual equations:

$$
\begin{aligned}
f(0)+d&=0,\\
f(1)(u+v)+d&=24,\\
f(2)(1+u)+d&=48,\\
f(3)(1+2u+v)+d&=312/5,\\
f(4)(1+r+u+v)+d&=y,\\
f(5)(2-r+3u+v)+d&=\zeta.
\end{aligned}
\tag{1.6}
$$

Each trace factor $t_j=\operatorname{tr}(A_jP)$ is positive, since
$A_j$ is nonzero and nonnegative and $P$ is strictly positive.
Both late readings are fixed constraints on the same world.
For one arbitrary but fixed real $d$, the whole class studied here is

$$
\mathcal K_{\mathbf c,d}
 =\{W\in\mathcal F(H):(\delta-D_0)/\lambda=d,
                         \ f(6)=0,\ f(7)\ne0\}.
\tag{1.7}
$$

Common drift and the two sample conditions are promises on candidates,
not labels extracted from the ancestor. There is no cardinality bound
on this class. The model and normalization are those of
[IX, Definitions 1.1–1.4](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md),
[G, Section 1](FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md)
and [F, Section 1](FIB_JMMJM_NONZERO_TERMINAL_COLLISION_SPARSITY_AND_RATIO_DIVERSITY.md).

## 2. Exact source graph and baseline interfaces

For $P$ in (1.4), or in the larger nonnegative domain

$$
\mathcal N=\left\{\begin{pmatrix}r&u\\v&1-r\end{pmatrix}:
              0\le r\le1,\ u,v\ge0,\ u+v>0\right\},
\tag{2.1}
$$

all six traces in (1.6) remain positive. In IX's trace coordinates
$\mathsf u=u+v$, $\mathsf v=1+u$, their row is

$$
(t_0,\ldots,t_5)
 =(1,\mathsf u,\mathsf v,\mathsf u+\mathsf v,
                    1+r+\mathsf u,\mathsf u+2\mathsf v-r).
\tag{2.2}
$$

Define

$$
\begin{aligned}
\ell_j(T)&=\prod_{\substack{0\le k\le3\\k\ne j}}
                          \frac{T-k}{j-k},\\
V_P(T)&=\sum_{j=0}^3\frac{\ell_j(T)}{t_j},&
U_{P;\mathbf c}(T)&=\sum_{j=0}^3\frac{c_j\ell_j(T)}{t_j},\\
\alpha_i&=1-t_iV_P(i),&\beta_i&=c_i-t_iU_{P;\mathbf c}(i)
                                      \quad(i=4,5),\\
\Delta(P)&=\alpha_4^2+\alpha_5^2,&
\mathcal C(P;\mathbf c)&=\alpha_4\beta_5-\alpha_5\beta_4.
\end{aligned}
\tag{2.3}
$$

The only interpolation divisors are positive traces and nonzero fixed
integers. [IX, Theorem 2.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md)
proves on all of $\mathcal N$ that

$$
\alpha_4=0\ \Longrightarrow\
V_P(5)>V_P(3)=1/t_3\ge1/t_5,\quad \alpha_5<0;
\qquad \Delta(P)>0.
\tag{2.4}
$$

Thus the following formulas have no omitted denominator-zero stratum:

$$
d_P=\frac{\alpha_4\beta_4+\alpha_5\beta_5}{\Delta(P)},\qquad
f_P=U_{P;\mathbf c}-d_PV_P.
\tag{2.5}
$$

[IX, Theorem 3.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md)
gives compatibility exactly when $\mathcal C(P;\mathbf c)=0$ and
then uniquely recovers $(f,d)=(f_P,d_P)$ for that supplied source.
Its residual identity is

$$
\begin{pmatrix}\beta_4\\\beta_5\end{pmatrix}
 -d_P\begin{pmatrix}\alpha_4\\\alpha_5\end{pmatrix}
 =\frac{\mathcal C(P;\mathbf c)}{\Delta(P)}
                  \begin{pmatrix}-\alpha_5\\\alpha_4\end{pmatrix}.
\tag{2.6}
$$

Consequently the exact legal source slice is

$$
\mathcal Z_{\mathbf c,d}=\{P\text{ satisfying (1.4)}:
 \mathcal C(P;\mathbf c)=0,\ d_P=d,\ f_P(6)=0,\ f_P(7)\ne0\}.
\tag{2.7}
$$

The map

$$
P\longmapsto(P,\lambda f_P,D_0+\lambda d)
\tag{2.8}
$$

is a bijection from (2.7) to the entire class (1.7). The first two
different readings exclude a zero reconstructed polynomial. Distinct
complete worlds therefore have distinct sources. These statements
are conditional recovery given $P$; the ancestor has not identified
an unknown $P$. The new terminal maps below are rational maps on this
whole source slice.

Two baseline results from
[G](FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md)
will be used with their full hypotheses:

* G, Theorem 2.1: on this entire fixed ancestor and at fixed $d$, at
  most one legal world has $f(6)=f'(6)=0$. Every such gain is exactly
  cubic with exactly a double sixth root and one simple root $\rho$;
  its normalized leading coefficient and $f(7)$ are positive. Its
  necessary ranges are $d<0$, $-3<\rho<0$; or $0<d<24$,
  $0<\rho<1$; or $48<d<312/5$, $2<\rho<3$. These are not
  existence assertions. In particular neither a quadratic double
  sixth root nor a triple sixth root is legal on this ancestor.
* G, Theorem 4.1: each of the four maps given by any three of the
  chronological terminal coordinates $A,B,C,D$ is injective on
  (1.7). Hence a distinct pair agrees in at most two coordinates.
  G, Theorem 6.1 gives the resulting incidence count and common
  terminal sign for a losing triple. These results do not assume
  a common source, gain shape, source sum or terminal amplitude.

The terminal notation is fixed in Section 3. The large repeated-root
certificate and the triple-coordinate proofs are reused at these exact
scopes rather than reproved as new results.

The geometry in fresh IX, Sections 7–11 has its stated history
restrictions. In normalized coordinates IX, Theorem 7.2 places source
escape exactly on

$$
\zeta=12y-288/5,\qquad -1788/25<y\le-5268/155.
\tag{2.9}
$$

IX, Theorems 8.1, 9.2 and 10.1 give a full trace corridor and the
compact complete-world closure obtained by adjoining six source-boundary
targets for $H_*=(0,J,24,M,48,M,312/5,J,48/5,M,-532/5)$ and its fixed
affine copies. IX, Definition 11.1 retains both possible boundary limits
and coalescing triples in its incidence set. Neither this history-specific
compactification nor the conditional corridor in IX, Theorem 4.1 is a
compactness, smoothness or joint-feasibility assertion for arbitrary
$(d,y,\zeta)$. None is a premise of the new proofs below.

## 3. Complete terminal and ancestor linear certificates

For a world in (1.7), put

$$
X=f(7)QP=\begin{pmatrix}a&b\\c&e\end{pmatrix},\quad
S=Q^{-1}X=f(7)P,\quad h=f/f(7),\quad
\sigma_j=\operatorname{tr}(A_jS).
\tag{3.1}
$$

Here $c$ is a matrix entry, distinct from the reading vector
$\mathbf c$. The entries of $X$ and all six $\sigma_j=f(7)t_j$
are nonzero and have the sign of $f(7)$, and $ae=bc$.
In particular a negative terminal gain is permitted. We have

$$
\deg h\le3,\quad h(6)=0,\quad h(7)=1,\qquad
h(j)\sigma_j=c_j-d\quad(0\le j\le5).
\tag{3.2}
$$

There is no division by a possibly zero ancestor gain in (3.2).
Both sixth response functions are $d$. The terminal functions, in
literal chronological order, are

$$
\begin{array}{c|c|c}
EF&FE&r_{EF}=d+\operatorname{tr}(FE X)\\ \hline
JJ&I&A=d+a+e\\
JM&\begin{pmatrix}1&0\\1&1\end{pmatrix}&B=d+a+b+e\\
MJ&\begin{pmatrix}1&1\\0&1\end{pmatrix}&C=d+a+c+e\\
MM&\begin{pmatrix}1&1\\1&2\end{pmatrix}&D=d+a+b+c+2e.
\end{array}
\tag{3.3}
$$

Indeed multiplication gives $J^2=I$, $MJ=L$,
$JM=\left(\begin{smallmatrix}1&1\\0&1\end{smallmatrix}\right)$ and
$M^2=\left(\begin{smallmatrix}1&1\\1&2\end{smallmatrix}\right)$;
taking their traces against $X$ gives every displayed coefficient.
These are functions on candidates. Only one chronological word is
executed on an actual trajectory. This terminal interface is established
in [F, Definition 2.2 and Lemma 2.3](FIB_JMMJM_NONZERO_TERMINAL_COLLISION_SPARSITY_AND_RATIO_DIVERSITY.md)
and [G, Section 3](FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md).

For the ancestor conversion, direct multiplication gives

$$
S=\begin{pmatrix}-2a+c&-2b+e\\3a-c&3b-e\end{pmatrix}.
\tag{3.4}
$$

Taking the traces against the six matrices in (1.5) yields the complete
six-by-four array, with column order $a,b,c,e$:

$$
\begin{pmatrix}\sigma_0\\\sigma_1\\\sigma_2\\\sigma_3\\\sigma_4\\\sigma_5\end{pmatrix}
=\begin{pmatrix}
-2&3&1&-1\\
3&-2&-1&1\\
-2&1&1&0\\
1&-1&0&1\\
-1&1&1&0\\
1&0&0&1
\end{pmatrix}
\begin{pmatrix}a\\b\\c\\e\end{pmatrix}.
\tag{3.5}
$$

For completeness the six traces from (3.4) are respectively
$-2a+3b+c-e$, $3a-2b-c+e$, $-2a+b+c$, $a-b+e$,
$-a+b+c$, and $a+e$. For example $\operatorname{tr}(LS)$
is $\operatorname{tr}S+S_{12}$, and
$\operatorname{tr}((J+L)S)=\operatorname{tr}(JS)+\operatorname{tr}(LS)$.
The $C_{\rm mat}$ trace is $2S_{11}+S_{21}+S_{12}+S_{22}$;
the $Q$ trace is $S_{11}+S_{21}+3S_{12}+2S_{22}$.
These give all 24 coefficients and, in particular, the identity

$$
\sigma_3=\sigma_1+\sigma_2.
\tag{3.6}
$$

For two worlds write $\Delta X=X_2-X_1$ and
$\Delta\sigma_j=\sigma_{2,j}-\sigma_{1,j}$. At common $d$, solving
each indicated pair of equalities in (3.3) gives the full table

$$
\begin{array}{c|c|l}
\text{equal coordinates}&\Delta X&(\Delta\sigma_0,\ldots,\Delta\sigma_5)\\ \hline
AB&\begin{pmatrix}-\epsilon&0\\\gamma&\epsilon\end{pmatrix}
 &(\epsilon+\gamma,-2\epsilon-\gamma,2\epsilon+\gamma,0,\epsilon+\gamma,0)\\[2mm]
AD&\begin{pmatrix}-\epsilon&\beta\\-\epsilon-\beta&\epsilon\end{pmatrix}
 &(2\beta,-\beta-\epsilon,\epsilon,-\beta,0,0)\\[2mm]
AC&\begin{pmatrix}-\epsilon&\beta\\0&\epsilon\end{pmatrix}
 &(\epsilon+3\beta,-2\epsilon-2\beta,2\epsilon+\beta,-\beta,\epsilon+\beta,0).
\end{array}
\tag{3.7}
$$

To derive every conversion, put $\Delta e=\epsilon$. Equal $A$
gives $\Delta a=-\epsilon$. In the $AB$ row, equal $B$ gives
$\Delta b=0$, leaving $\Delta c=\gamma$. In the $AD$ row,
equal $D-A=b+c+e$ gives $\Delta c=-\epsilon-\beta$ when
$\Delta b=\beta$. In the $AC$ row, equal $C-A=c$ gives
$\Delta c=0$, leaving $\Delta b=\beta$. Substitution of these
four entries into each of the six linear forms in (3.5) gives
exactly the 18 displayed trace differences. No scalar cancellation
is used in this table; it includes zero values of its parameters.

If $X_1=X_2$, then $S_1=S_2$ and taking traces gives the same
nonzero $f(7)$ because $\operatorname{tr}P_i=1$. Dividing by that
value gives $P_1=P_2$. At common $d$, the first four positive trace
factors in (1.6) give equal gain samples; degree-at-most-three
uniqueness gives $f_1=f_2$. Thus the complete original worlds agree.
This implication includes degree drops and all multiplicities and
also follows from the IX source graph.

## 4. Two terminal-pair maps are injective on the whole class

**Theorem 4.1 (whole-class $AB$ and $AD$ injection).** For every fixed
arbitrary ancestor (1.2) and common $d$, each of

$$
W\longmapsto(A(W),B(W)),\qquad W\longmapsto(A(W),D(W))
\tag{4.1}
$$

is injective on the entire $\mathcal K_{\mathbf c,d}$.
Equivalently the associated rational pair maps are injective on all
of $\mathcal Z_{\mathbf c,d}$. Sources and gain shapes may differ;
no common source sum or additional sign condition is assumed.

**Proof for $AB$.** Suppose two worlds agree in $A,B$, and use their
first row in (3.7). Their traces $\sigma_{i,3}$ agree and their
traces $\sigma_{i,5}$ agree. All these traces are nonzero.
The actual equations (3.2) give $h_1(3)=h_2(3)$ and
$h_1(5)=h_2(5)$, even if either sample is zero. The difference
$h_2-h_1$ also vanishes at six and seven. Its degree is at most
three and it has the four distinct roots $3,5,6,7$, so
$h_1=h_2=h$.

Subtract (3.2) at clocks one and two. It gives

$$
h(1)(-2\epsilon-\gamma)=0,\qquad
h(2)(2\epsilon+\gamma)=0.
\tag{4.2}
$$

If $h(1)=0$, the actual first reading forces $d=24$; if
$h(2)=0$, the actual second reading forces $d=48$. They cannot
both vanish. Thus when both are nonzero either equation applies;
when $h(1)=0$ the second applies; and when $h(2)=0$ the first
applies. In every case $\gamma=-2\epsilon$.
If $\epsilon=0$, then $\gamma=0$ and $X_1=X_2$, giving equal
complete worlds as proved after (3.7).

If $\epsilon\ne0$, the trace differences at clocks zero and four
are both $-\epsilon$. Hence $h(0)=h(4)=0$, and the actual
clock-zero equation gives $d=0$ (the fourth also gives $y=d$).
Together with $h(6)=0$ and $h(7)=1$ these distinct roots force

$$
h(T)=\frac{T(T-4)(T-6)}{21}
 =\frac{T^3-10T^2+24T}{21}.
\tag{4.3}
$$

The normalizing divisor is $7(7-4)(7-6)=21\ne0$; three distinct
roots and a nonzero value exclude every lower degree in this branch.
The increasing-power coefficient row is $(0,24/21,-10/21,1/21)$.
The required rational samples are

$$
h(1)=15/21=5/7,\qquad h(2)=16/21,\qquad h(3)=9/21=3/7.
\tag{4.4}
$$

They follow by evaluating the three factors in (4.3), and all are
nonzero. For either world the actual readings at $d=0$ therefore give

$$
\sigma_1=\frac{24}{5/7}=\frac{168}{5},\quad
\sigma_2=\frac{48}{16/21}=63,\quad
\sigma_3=\frac{312/5}{3/7}=\frac{728}{5}.
\tag{4.5}
$$

But (3.6) would require $728/5=168/5+63=483/5$, with discrepancy
$245/5=49\ne0$. This contradiction excludes $\epsilon\ne0$.
Thus the $AB$ map is injective, including every sampled-zero branch.

**Proof for $AD$.** Its row of (3.7) gives equal nonzero traces at
clocks four and five. The two actual late equations give equal $h$
values there. Together with six and seven, four distinct roots
$4,5,6,7$ force $h_1=h_2=h$.

If $\beta\ne0$, trace differences $2\beta$ at zero and
$-\beta$ at three force $h(0)=h(3)=0$. The actual readings
would give $d=0$ and $d=312/5$, a contradiction. Hence
$\beta=0$. Now if $\epsilon\ne0$, the trace differences at
one and two are $-\epsilon$ and $\epsilon$. They force
$h(1)=h(2)=0$ and the incompatible values $d=24$ and $d=48$.
Thus $\epsilon=0$ as well. The matrices and complete worlds agree.
No nonzero ancestor gain, leading coefficient or root-separation
premise has been added. This proves both injections. ∎

These are stronger than G's three-coordinate injections at the same
whole-class quantifiers. Their two alternative coordinates are still
functions on fixed worlds, not jointly acquired terminal observations.

## 5. An $AC$ collision constrains the whole common slice

**Theorem 5.1 (strict $AC$ obstruction).** If two distinct worlds in
$\mathcal K_{\mathbf c,d}$ agree in $A,C$, then necessarily

$$
\begin{array}{ll}
\text{I:}&0<d<24,\quad y<d,\quad \zeta<d,\\
\text{II:}&24<d<48,\quad y>d.
\end{array}
\tag{5.1}
$$

In alternative I, every world on the same full ancestor with this
same $d$ and $f(6)=0$ is exactly cubic with three simple roots
$\rho\in(0,1)$, $\tau\in(3,4)$ and six. Its normalized leading
coefficient and $f(7)$ are positive, as is the leading coefficient
of $h=f/f(7)$. In alternative II every sixth root on that entire
same-ancestor zero-sixth slice is simple. There is no additional
terminal-sign or other-root assertion in alternative II, and neither
alternative asserts existence or sufficiency.

**Proof, the nonzero parameters and every zero-difference case.**
Use the $AC$ row in (3.7). If $\epsilon=0$, the two matrices have
the same $a,c,e$. Their nonzero common $c$ and rank-one equations
$ae=bc$ then give the same $b$, contradicting distinctness.
Thus $\epsilon\ne0$.

Equal $A$ gives equal nonzero $\sigma_5$. The actual fifth equation
gives $h_1(5)=h_2(5)$, including a possible zero sample.
Both polynomials agree at six and seven, so

$$
h_2(T)-h_1(T)=kR(T),\qquad R(T)=(T-5)(T-6)(T-7).
\tag{5.2}
$$

The difference has degree at most three; factorization proves this
identity also for $k=0$ and all lower degrees. We first exclude
$k=0$. Then $h_1=h_2=h$, and the difference of (3.2) is
$h(j)\Delta\sigma_j=0$ at every ancestor clock.

If $d\notin\{24,48\}$, both $h(1),h(2)$ are nonzero, so
$\epsilon+\beta=0$ and $2\epsilon+\beta=0$.
If $d=24$, both $h(0),h(2)$ are nonzero, so
$\epsilon+3\beta=0$ and $2\epsilon+\beta=0$.
If $d=48$, both $h(0),h(1)$ are nonzero, so
$\epsilon+3\beta=0$ and $\epsilon+\beta=0$.
These cases exhaust all real $d$; each system forces
$\epsilon=\beta=0$, a contradiction. Thus $k\ne0$.

**Proof, full coefficients, samples and excluded breakpoints.**
Multiplication gives

$$
R(T)=(T^2-12T+35)(T-6)=T^3-18T^2+107T-210.
\tag{5.3}
$$

Its complete increasing-power row is $(-210,107,-18,1)$, and its
complete samples at the displayed clocks, directly from the three
factors, are

$$
\begin{array}{c|rrrrrrrr}
j&0&1&2&3&4&5&6&7\\ \hline
R(j)&-210&-120&-60&-24&-6&0&0&0.
\end{array}
\tag{5.4}
$$

Thus $h_2(j)-h_1(j)\ne0$ at every $j=0,\ldots,4$.
At any such clock, $c_j=d$ would make both $h_i(j)=0$ by
(3.2), which is impossible. Also $\Delta\sigma_j=0$ would
make the two $h$ values equal by their common nonzero trace,
again impossible. Consequently

$$
d\notin\{0,24,48,312/5,y\}.
\tag{5.5}
$$

Define $\theta=\beta/\epsilon$ only now that $\epsilon\ne0$.
The entire trace-difference vector is $\epsilon F$, where

$$
F=(1+3\theta,-2(1+\theta),2+\theta,-\theta,1+\theta,0).
\tag{5.6}
$$

Nonvanishing of its first five entries proves
$\theta\notin\{-2,-1,-1/3,0\}$. These are all its breakpoints.
No exclusion of $d=\zeta$ is inferred: the clock-five sample may
vanish. All exclusions so far are consequences of the distinct
$AC$ hypothesis, not deletions from the model.

**Proof, the exact sign identity and exhaustive table.** The common
$A-d=f_i(7)\operatorname{tr}(QP_i)$ is nonzero and its trace
factor is positive. Thus $f_1(7),f_2(7)$ have the same sign and
$\sigma_{1,j}\sigma_{2,j}>0$ at every clock. Subtracting
$h_i(j)=(c_j-d)/\sigma_{i,j}$ gives the identity

$$
kR(j)=-\frac{(c_j-d)\epsilon F_j}
                         {\sigma_{1,j}\sigma_{2,j}},
\qquad 0\le j\le4.
\tag{5.7}
$$

All divisors here are nonzero. Because $R(j)<0$ at these clocks,

$$
\operatorname{sgn}(k/\epsilon)
 =\operatorname{sgn}((c_j-d)F_j),\qquad 0\le j\le4.
\tag{5.8}
$$

The first four entries of (5.6), and their global negatives, have
exactly the following signs on all five intervals:

| $\theta$ interval | $(F_0,F_1,F_2,F_3)$ | Global negative | Compatible reading-sign row |
| --- | --- | --- | --- |
| $\theta<-2$ | $(-,+,-,+)$ | $(+,-,+,-)$ | none |
| $-2<\theta<-1$ | $(-,+,+,+)$ | $(+,-,-,-)$ | first row, $0<d<24$ |
| $-1<\theta<-1/3$ | $(-,-,+,+)$ | $(+,+,-,-)$ | first row, $24<d<48$ |
| $-1/3<\theta<0$ | $(+,-,+,+)$ | $(-,+,-,-)$ | none |
| $\theta>0$ | $(+,-,+,-)$ | $(-,+,-,+)$ | none |

Each entry follows from the signs of the four linear factors
$1+3\theta$, $-2(1+\theta)$, $2+\theta$, $-\theta$.
For clarity, all drift intervals from the increasing actual readings
$0<24<48<312/5$, after the excluded endpoints (5.5), give

$$
\begin{array}{c|c}
d\text{ interval}&\operatorname{sgn}(c_0-d,c_1-d,c_2-d,c_3-d)\\ \hline
(-\infty,0)&(+,+,+,+)\\
(0,24)&(-,+,+,+)\\
(24,48)&(-,-,+,+)\\
(48,312/5)&(-,-,-,+)\\
(312/5,\infty)&(-,-,-,-).
\end{array}
\tag{5.9}
$$

Equation (5.8) requires this reading-sign row to be the $F$ row
when $k/\epsilon>0$, or its global negative when $k/\epsilon<0$.
The table lists both choices for every interval. Only its second
and third $F$ rows occur in (5.9); no global negative occurs.
Therefore

$$
\begin{gathered}
k/\epsilon>0,\\
-2<\theta<-1,\quad 0<d<24,
\qquad\text{or}\qquad
-1<\theta<-1/3,\quad 24<d<48.
\end{gathered}
\tag{5.10}
$$

At clock four, (5.8) now requires
$(y-d)(1+\theta)>0$. Hence $y<d$ in the first case and
$y>d$ in the second. This uses the fixed actual fourth reading.

**Proof, the entire-slice root and fifth-reading consequences.**
In the first case, take any legal world on the same ancestor with
this $d$ and $f(6)=0$, whether or not it belongs to the collision
pair. Positivity of every trace and (1.6) give

$$
f(0)<0,\quad f(1),f(2),f(3)>0,\quad f(4)<0.
\tag{5.11}
$$

The intermediate value theorem gives a root $\rho\in(0,1)$ and
a root $\tau\in(3,4)$. Along with six these are three distinct
roots. The nonzero gain has degree at most three, so it is exactly

$$
f(T)=\kappa(T-\rho)(T-\tau)(T-6),\qquad \kappa\ne0,
\tag{5.12}
$$

and all three roots are simple, with no further root. At $T=3$ the
three factors have signs $(+,-,-)$; (5.11) forces $\kappa>0$.
At five their signs are $(+,+,-)$, giving $f(5)<0$.
The actual fifth equation with its positive trace now forces
$\zeta<d$. At seven all three factors are positive, giving
$f(7)>0$. The leading coefficient of $h=f/f(7)$ is therefore
also positive. This proves every assertion of alternative I on the
entire same-ancestor slice; it even forces terminal nonvanishing
without assuming it for this last argument.

In the second case, $24<d<48$. G, Theorem 2.1, at exactly this
same fixed ancestor and common $d$, permits a repeated sixth root
only for $d<0$, $0<d<24$, or $48<d<312/5$. None meets this
interval. Thus every sixth root on the same zero-sixth slice is
simple. No further sign or existence conclusion is taken from
that baseline theorem. This proves (5.1) and all whole-slice claims. ∎

The proof divided only by promised terminal gains, nonzero ancestor
traces, the proved nonzero $\epsilon$, and fixed integers.
The $k=0$ branch and every sampled-zero and sign breakpoint were
settled before the corresponding sign argument. No sixth ratio,
leading gain coefficient, discriminant or root difference was canceled.
In original coordinates the forced-positive normalized terminal gain
in alternative I means $\operatorname{sgn}g(7)=\operatorname{sgn}\lambda$;
it does not assume positivity of the original gain.

## 6. Exact TT recursion and joint pattern exclusions

For a known compatible set $K$ at a history $H'$, within the remaining
original-clock horizon, use the actual-child recursion

$$
\begin{aligned}
L_0(K,H')&\Longleftrightarrow |K|\ge2,\\
L_{m+1}(K,H')&\Longleftrightarrow |K|\ge2\ \land\
 \bigwedge_{E\in\{J,M\}}\exists w\in\mathbb R:
 L_m(K\cap\mathcal F(H',E,w),(H',E,w)).
\end{aligned}
\tag{6.1}
$$

Every $w$ is a raw real response. For the same three distinct worlds
$K=\{W_1,W_2,W_3\}\subseteq\mathcal K_{\mathbf c,d}$, put

$$
\Pi(R)=(R_1-R_2)(R_1-R_3)(R_2-R_3).
\tag{6.2}
$$

**Proposition 6.1 (established actual TT equivalence).** On this same
triple,

$$
L_2(K,H)\ \Longleftrightarrow\
\Pi(A)=\Pi(B)=\Pi(C)=\Pi(D)=0.
\tag{6.3}
$$

**Proof.** For either sixth action $E$ and every raw $w$,

$$
K\cap\mathcal F(H,E,w)=
\begin{cases}
K,&w=D_0+\lambda d,\\
\varnothing,&w\ne D_0+\lambda d.
\end{cases}
\tag{6.4}
$$

Thus only the entire same triple can witness $L_1$ at sixth, under
either action. On this child the last action $F$ and raw value $v$
retain exactly

$$
\{W_i\in K:D_0+\lambda r_{EF}(W_i)=v\}.
\tag{6.5}
$$

This has at least two members for some $v$ exactly when its column
has a collision. For sixth $J$ the columns are $A,B$; for sixth
$M$ they are $C,D$. Expanding (6.1) proves necessity. Conversely,
choose the raw sixth response in (6.4) for each $E$, and for each
last action separately choose its colliding pair and that pair's
common raw terminal value in (6.5). These witness both $L_1$
children and hence $L_2$. The four pairs and terminal values may
differ. The affine bijection works also for $\lambda<0$.
This is G, Proposition 5.1, equivalently the zero-sixth specialization
of F, Proposition 7.2 and IX, Definition 5.2. ∎

A column constant on all three worlds contributes all three unordered
pair collisions. A nonconstant but noninjective column contributes
exactly one proper pair. Literal columns retain their meanings
$A=JJ$, $B=JM$, $C=MJ$, $D=MM$.

**Theorem 6.2 (strict simultaneous pattern obstructions).** Suppose
$L_2(K,H)$ for such a triple. Then the following list exhausts its
possible collision patterns.

1. If a column is constant, it can only be $C$. The proper columns
   $A,B,D$ must use three different pairs. This configuration
   satisfies one of the alternatives (5.1), and every sixth root
   on the entire same-ancestor common-drift slice is simple.
2. If no column is constant and the pair multiplicities are
   $(2,2,0)$, the only possible assignment is $AC\mid BD$:
   one pair shares $A,C$, a different pair shares $B,D$, and the
   remaining pair has no collision. This configuration has the
   same restrictions (5.1) and entire-slice simplicity.
3. If no column is constant and the multiplicities are $(2,1,1)$,
   the unique repeated pair can occupy only $AC$, $BC$, $BD$ or
   $CD$. An $AC$ repeat has all restrictions (5.1) and the same
   entire-slice simplicity. No additional collision-specific
   restriction is asserted here for repeats $BC$, $BD$ or $CD$.

For every configuration containing an $AC$ pair, alternative I also
forces the cubic root intervals and normalized signs of Theorem 5.1
for every member of the slice. If
$d\notin(0,24)\cup(24,48)$, or if the triple contains a repeated
sixth root, only case 3 with repeated subset $BC$, $BD$ or $CD$
can survive. All these are necessary conditions, not realizations.

**Proof.** G, Theorem 4.1 applies on exactly (1.7), so each distinct
pair has at most two terminal-coordinate collisions. There are three
pairs. If $n$ of the four noninjective columns are constant, the
number of incidences is $3n+(4-n)=4+2n\le6$, hence $n\le1$.
If $n=1$, each pair has already used one incidence in the constant
column and can use only one more. The other three columns must use
the three different pairs. If $n=0$, the three counts are at most
two and sum to four; their only types, up to pair ordering, are
$(2,2,0)$ and $(2,1,1)$. This is the baseline count of G,
Theorem 6.1, with its full three-world hypothesis retained.

A constant $A$ and a collision in $B$ would give a distinct $AB$
pair, contrary to Theorem 4.1 here. A constant $B$ and a collision
in $A$ give the same contradiction. A constant $D$ and a collision
in $A$ give a forbidden $AD$ pair. These arguments exclude each
whole configuration regardless of the choices of proper pairs.
Thus only constant $C$ survives. Its $A$ pair is an $AC$ pair;
Theorem 5.1 applies on the common slice and proves every restriction
in case 1, including simplicity for all three members.

For type $(2,2,0)$ the two repeated pairs occupy disjoint two-element
coordinate subsets partitioning the four columns. All possibilities
are $AB\mid CD$, $AC\mid BD$, $AD\mid BC$.
The first contains forbidden $AB$, and the third forbidden $AD$.
Only $AC\mid BD$ remains. Its $AC$ pair gives precisely the
whole-slice restrictions asserted in case 2.

For type $(2,1,1)$ the six possible two-coordinate subsets for its
repeated pair are $AB,AC,AD,BC,BD,CD$. Theorem 4.1 excludes
$AB,AD$; the four listed subsets remain. If that subset is $AC$,
Theorem 5.1 again applies to the full common slice. This proves
case 3 and exhausts the no-constant possibilities without permuting
the literal terminal coordinates.

All patterns except $(2,1,1)$ with repeated subset $BC,BD,CD$
contain an $AC$ pair. Such a pair requires the two strict drift
alternatives and excludes any repeated-sixth-root member of the
entire same slice by Theorem 5.1. This proves the final exclusion,
even if the repeated-root world would have been the member outside
the $AC$ pair. ∎

The common normalized terminal sign is also necessary. Indeed each
terminal offset from $d$ has the sign of $f_i(7)$ because its trace
factor is positive. If signs on three worlds were mixed, only the
unique same-sign pair could collide in any column. All four collision
products would then force that pair to share $AB$, contradicting
Theorem 4.1. Thus all three signs agree, as in G, Theorem 6.1.
If a repeated-sixth member is present, G, Theorem 2.1 makes this
common sign positive, and gives at most one such member, exactly
double and exactly cubic, with its stated strict root/drift ranges.
A negative normalized terminal sign therefore forces all three sixth
roots simple. Original terminal signs are obtained by multiplying
by the one common nonzero $\lambda$.

## 7. The exact remaining joint system and the policy boundary

The remaining feasibility obligation preserves complete-source
legality and one simultaneous realization. Choose one common real
$d,y,\zeta$ and three pairwise distinct sources $P_i$ with

$$
\begin{gathered}
P_i=\begin{pmatrix}r_i&u_i\\v_i&1-r_i\end{pmatrix},\quad
0<r_i<1,\quad u_i,v_i>0,\quad u_iv_i=r_i(1-r_i),\\
\mathcal C(P_i;\mathbf c)=0,\quad d_{P_i}=d,\quad
f_{P_i}(6)=0,\quad f_{P_i}(7)\ne0,\qquad i=1,2,3,\\
\mathbf c=(0,24,48,312/5,y,\zeta),\\
\Pi(A)=\Pi(B)=\Pi(C)=\Pi(D)=0,
\end{gathered}
\tag{7.1}
$$

where all reconstructed functions are (2.3)–(2.5) for these same
readings and the terminal functions are (3.3) on
$X_i=f_{P_i}(7)QP_i$. No gains or late readings can be selected
independently after a source is chosen.

**Proposition 7.1 (necessary-and-sufficient remaining system).**
Solutions of (7.1) correspond bijectively to ordered triples of
distinct worlds of (1.7) with $L_2(K,H)$, through

$$
W_i=(P_i,\lambda f_{P_i},D_0+\lambda d).
\tag{7.2}
$$

**Proof.** Necessity follows from IX, Theorem 3.1: every legal world
on the full ancestor has precisely its compatible source and the
reconstructed gain and drift. Projection onto sources is injective,
so distinct complete worlds give distinct $P_i$. The sixth-zero and
seventh-nonzero requirements give the corresponding conditions in
(7.1), and Proposition 6.1 gives all four products.

For sufficiency, the strict inequalities, trace and determinant
conditions in (7.1) give legal sources. The positive denominator
$\Delta(P_i)$ and compatibility give the unique interpolated
$(f_{P_i},d)$ satisfying all six actual equations by (2.6).
Each gain has degree at most three and is nonzero because the
initial readings zero and 24 differ. The two future sample
conditions place (7.2) in (1.7), with distinct complete worlds
because their sources differ. The affine inverse works for both
signs of $\lambda$. Finally the four products and Proposition 6.1
provide the actual sixth children and last-action real-response
witnesses on this very triple. Reconstruction and projection are
inverse by IX's uniqueness. ∎

Theorem 4.1, Theorem 5.1 and Theorem 6.2 are necessary consequences
of this exact system. Their parameter inequalities do not replace its
source equations, do not prove sufficiency and do not constitute an
implicit witness. Separately realizable colliding pairs, or extrema
attained at different sources, cannot be joined without (7.1).
This is the source-graph version of G, Proposition 7.1, retaining
IX, Definition 5.2 and F, Proposition 7.2.

For a supplied known finite $K\subseteq\mathcal K_{\mathbf c,d}$,
one scalar injective on the whole $K$ gives the lawful policy of
G, Proposition 5.2: select its literal word $EF$, execute and read
sixth $E$, then execute and read seventh $F$. For every pair of
raw real responses $w,v$ the retained set has at most one member:
it is empty if $w\ne D_0+\lambda d$, and otherwise the selected
terminal scalar separates $K$. At reachable responses actual
membership supplies the unique complete target. A singleton can stop
earlier. This policy is conditional on whole-known-set scalar
injectivity. Two-coordinate injectivity alone does not acquire both
coordinates on one trajectory and does not imply that every allowed
triple has an injective scalar. The present obstructions supply no
uniform policy on the full class or on a larger losing family.

## 8. Permanent correspondence, strict increase and remaining obligation

The permanent project references used here are
[IX](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md),
[G](FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md),
and [F](FIB_JMMJM_NONZERO_TERMINAL_COLLISION_SPARSITY_AND_RATIO_DIVERSITY.md).
Their exact roles are as follows.

| Permanent source and location | Established result and correspondence here |
| --- | --- |
| IX, Definitions 1.1–1.4; Theorems 2.1 and 3.1 | Complete-world model, full arbitrary ancestor, positive traces, interpolation, $\Delta>0$ throughout the nonnegative domain, and the exact source-conditioned rational graph in Section 2. Conditional gain/drift recovery does not identify the unknown source. |
| IX, Theorem 4.1; Proposition 4.2 | Bounds require a fixed positive finite trace corridor and bounded readings; arbitrary moving late readings can carry arbitrary drift. Neither result gives compactness of our arbitrary-history slice. |
| IX, Definitions 5.2–5.3 | Same three fixed legal worlds, actual-response recursion, common-history joint obligation and the retained original-root eight-versus-nine quantifiers. Sections 6–7 here preserve this exact interface. |
| IX, Theorem 7.2; Theorems 8.1, 9.2 and 10.1; Definitions 11.1–11.2 | Exact history-dependent source-escape locus, and the $H_*$ trace corridor, six boundary targets and compact complete-world closure. Section 2 states their limited comparison; no arbitrary-history compactness or legal-triple conclusion is imported. |
| G, Theorem 2.1 | Fixed full ancestor and common-drift repeated-sixth singleton, exact cubic/double multiplicity, root/drift ranges and normalized positive sign. Theorem 5.1 uses only these necessary ranges for its second alternative; the full-slice first alternative has its own proof. |
| G, Section 3; Theorem 4.1; Theorem 6.1 | Signed terminal representation and complete-world reconstruction; whole-class three-coordinate injectivity and the pair-at-most-two bound; baseline incidence count and sign restrictions. Section 6 reuses these at their exact three-world scope. |
| G, Propositions 5.1–5.2 and 7.1 | TT actual-child equivalence, policy conditional on an injective scalar on the whole known set, and exact joint feasibility. Sections 6–7 retain all real responses and both late equations. |
| F, Sections 1–2; Lemmas 2.1 and 2.3; Definition 2.2 | Model, legal positive $Q$ chart, chronological terminals and four-terminal complete-world inverse. The signed representation in Section 3 has the same normalization and admits both terminal signs. |
| F, Theorem 4.1 and Corollary 4.2 | Five strict ratios and the exchanged-source argument require common drift, both common sixth predictions and nonzero sixth gains to obtain a common source sum. Those hypotheses do not hold merely from $f_i(6)=0$. |
| F, Theorem 6.1; Proposition 7.2; Corollary 7.3 | Diagonal-swap obstruction requires common $q=f(6)/f(7)\ne0$; PP/PT/TP/TT is the exact actual-child table, and all-zero TT versus nonzero varying-ratio PP remains the common-drift alternative. Here $q=0$; there is no cancellation by $q$ and no common-sum inference. |
| This volume, Theorems 4.1, 5.1 and 6.2 | Source-relative new deductions: whole-class $AB$ and $AD$ injections, strict $AC$ drift/late-reading restrictions and entire-slice root consequences, and the resulting complete TT pattern exclusions. The exact remaining system is preserved rather than declared feasible or impossible. |

G's three-coordinate result permits a distinct pair to share any two
terminal coordinates; its count permits any one constant column and
all three partitions of type $(2,2,0)$. Theorem 4.1 here removes
$AB$ and $AD$ globally on the whole promised class. Consequently
constant $A,B,D$ and both partitions $AB\mid CD$, $AD\mid BC$
are excluded as entire simultaneous configurations. The remaining
constant $C$, partition $AC\mid BD$, and type $(2,1,1)$ with
repeated $AC$ acquire strict common-drift and actual-late-reading
constraints, together with simplicity on the entire source slice.
These are strict additional obstructions relative to the supplied
baselines, not a reparametrization of their graph or a new label for
their incidence count.

The mathematical tools inside the new proofs are elementary matrix
algebra, polynomial factorization and root counting, signs of linear
factors, and the intermediate value theorem. Lagrange interpolation
and the positive residual denominator are established interfaces.
No external-priority or literature-completeness conclusion is made.
These model-specific symbolic results carry no empirical, general
neural-network, kernel or Lean verification, stability, efficiency
or computational-resource claim.

The full common-drift zero-sixth TT feasibility question is unresolved.
Its surviving patterns are constant $C$ and $AC\mid BD$ under
(5.1) and the entire-slice restrictions, and type $(2,1,1)$ with
repeated $AC,BC,BD,CD$ under the respective restrictions above.
Outside the $AC$ drift range, or with a repeated-sixth member, only
repeated $BC,BD,CD$ in type $(2,1,1)$ remain. None is asserted
attainable. There is no exact legal witness and no uniform exclusion
for the full system (7.1).

The common-drift nonzero-sixth varying-$q$ PP case, variable drifts,
other terminal-root strata, larger or infinite losing families, their
full actual fibers, other literal histories, the earlier $JMMJ$
parent-arm gluing and the separate $MMJM$ and $MJMMJ$ obligations
remain unresolved here. A larger losing family is not proved to
contain a losing triple. No acquisition of unchosen terminal
coordinates is supplied.

The original-root alternative remains a lawful complete-target decoder
on every legal world with at most eight total readings versus
$n_{\mathrm{det}}(3,0)\ge9$. It still includes both initial actions,
every actual history and early stop, arbitrary constant drift, all
positive nonsymmetric rank-one trace-one sources, and every nonzero
cubic-or-lower gain with both signs, sampled roots and multiplicities.
A result on this one ancestor still needs its earlier-history bridge.
The strongest conclusions here are the two entire-class terminal-pair
injections and the strict $AC$ and joint-pattern obstructions. The
remaining obligation is exactly to produce one simultaneous legal
three-source solution of (7.1), for common $d,y,\zeta$, or to exclude
all such solutions; neither alternative is settled by these necessary
restrictions.
