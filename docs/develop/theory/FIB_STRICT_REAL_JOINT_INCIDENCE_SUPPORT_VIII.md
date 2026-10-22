# FIB strict-real joint incidence: raw complex obstruction and trace saturation

This volume gives a concrete obstruction to using the raw complex four-world
projection as a finite list of candidate bases for the original strict-real
joint problem. A fully guarded complex family forces every nonzero raw joint
eliminant to contain a specified irreducible conic factor. The raw two-world
terminal-$M$ system, by itself, projects onto an explicit complex Zariski-open
set. Neither statement decides the original real problem. Trace saturation
preserves its entire strict-real domain and restores the missing clock-four
constraint; the resulting projection remains **OPEN**.

All polynomial rings and identities below are over $\mathbb Q$ unless a
real or complex locus is specified. The source definitions cited in
Section 8 are taken at the fixed revision
`c91f4841791e83e61d117ab81a4a70495567f21d`.

## 1. Complete worlds and the unchanged joint question

**Definition 1.1 (Original strict-real world).** A complete world is

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad
0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R.
$$

There is one entire gain polynomial and one fixed drift per world. Positive
source entries have no upper bound. Zero drift, sampled gain zeros, repeated
gain roots, lower gain degrees, singular sources and worlds unused by a
selected pair are permitted. No gain positivity, regularity hypothesis or
positive separation floor is imposed.

Set

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
A_0=I,\quad A_k=E_kA_{k-1},\quad
y_k=d+g(k)\operatorname{tr}(A_kP).
$$

The acquired chronological word is $J,M,J,M,M,M$. The literal parent and
child are

$$
H_4=(0,J,24,M,147/5,J,24,M,18),\qquad
C(p,v)=\mathcal F(H_4,M,p,M,v),\qquad p\ne24.
$$

Thus $(y_0,\ldots,y_6)=(0,24,147/5,24,18,p,v)$. The initial read counts;
there is no reset, copy, skipped read, clock shift or additional port. At
clock seven $J$ and $M$ are alternatives on the same world.

**Definition 1.2 (Independent pairs at one base).** Write

$$
\begin{gathered}
c=r(1-r)/b,\quad j=b+c,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\\
a(W)=d+(T+2j+4r)g(7),\qquad
m(W)=d+(3U+2n)g(7).
\end{gathered}
$$

The original joint event is membership in $D_J\cap D_M$, where

$$
\begin{aligned}
(p,v)\in D_J&\iff p\ne24,\quad
\exists W_0\ne W_1\in C(p,v):a(W_0)=a(W_1),\\
(p,v)\in D_M&\iff p\ne24,\quad
\exists W_2\ne W_3\in C(p,v):m(W_2)=m(W_3).
\end{aligned}
$$

Both selected pairs belong to the same entire child. The pairs may overlap
or be disjoint, and their two common terminal values may differ. The event
requires actual complete real worlds, rather than projected roots or
complex labels. This volume supplies neither such a joint witness nor an
exhaustive exclusion.

**Lemma 1.3 (Literal traces and whole interpolation).** The traces at clocks
$0,\ldots,6$ and the two clock-seven traces are respectively

$$
(1,j,T,n,U,U+n,2U+n),\qquad T+2j+4r,\quad 3U+2n.
$$

For four sample variables $q=(q_0,q_1,q_2,q_3)$ define the entire polynomial

$$
g_q(s)=\sum_{k=0}^3q_k\prod_{\substack{0\le l\le3\\l\ne k}}
\frac{s-l}{k-l}.
$$

Its values at clocks $4,5,6,7$ are the rows

$$
\begin{aligned}
B_4(q)&=-q_0+4q_1-6q_2+4q_3,\\
B_5(q)&=-4q_0+15q_1-20q_2+10q_3,\\
B_6(q)&=-10q_0+36q_1-45q_2+20q_3,\\
B_7(q)&=-20q_0+70q_1-84q_2+35q_3.
\end{aligned}
$$

Proof. Left multiplication in the prescribed order gives

$$
\begin{array}{c|c|c}
k&A_k&\operatorname{tr}(A_kP)\\ \hline
0&\begin{pmatrix}1&0\\0&1\end{pmatrix}&1\\
1&\begin{pmatrix}0&1\\1&0\end{pmatrix}&j\\
2&\begin{pmatrix}1&0\\1&1\end{pmatrix}&T\\
3&\begin{pmatrix}1&1\\1&0\end{pmatrix}&n\\
4&\begin{pmatrix}1&0\\2&1\end{pmatrix}&U\\
5&\begin{pmatrix}2&1\\3&1\end{pmatrix}&U+n\\
6&\begin{pmatrix}3&1\\5&2\end{pmatrix}&2U+n
\end{array}
$$

Multiplying $A_6$ by $J$ and $M$ gives, respectively,
$\begin{pmatrix}5&2\\3&1\end{pmatrix}$ and
$\begin{pmatrix}5&2\\8&3\end{pmatrix}$; their traces against $P$ are
$T+2j+4r$ and $3U+2n$. The four Lagrange basis polynomials are

$$
-\frac{(s-1)(s-2)(s-3)}6,\quad
\frac{s(s-2)(s-3)}2,\quad
-\frac{s(s-1)(s-3)}2,\quad
\frac{s(s-1)(s-2)}6.
$$

Their values at $4,5,6,7$ give exactly the four displayed rows.
Distinct interpolation nodes suffice; neither the sample values nor the
exact degree require a further hypothesis. These are the whole-world
interfaces of O, Definitions 1.1–1.3, and SII, Section 2. ∎

## 2. A fully specified raw polynomial presentation

**Definition 2.1 (One raw world).** Work over $\mathbb Q$. For each label
$i\in\{0,1,2,3\}$ use eleven variables

$$
t_i,b_i,e_i,j_i,n_i,T_i,U_i,q_{0i},q_{1i},q_{2i},q_{3i}.
$$

The expression $r_i=t_ib_i$ is not a further variable. Put

$$
L_i=b_i^2+8b_i+4,\qquad A_i=(8b_i-1)(5b_i+2).
$$

Include these four definition equations and one parent equation:

$$
\begin{gathered}
j_i-t_i-b_i(1-t_i^2)=0,\quad n_i-j_i-t_ib_i=0,\\
T_i-1-b_i=0,\quad U_i-1-2b_i=0,\\
P_i^{\rm raw}:=
5e_i\{2L_ij_in_i-4T_iU_i(j_i+n_i)\}+6A_ij_in_i=0.
\end{gathered}
$$

Include the four sample equations

$$
\begin{aligned}
l_{0i}&=q_{0i}+24+e_i=0,&
l_{1i}&=j_iq_{1i}+e_i=0,\\
l_{2i}&=5T_iq_{2i}-27+5e_i=0,&
l_{3i}&=n_iq_{3i}+e_i=0.
\end{aligned}
$$

Define, without introducing more variables,

$$
\begin{aligned}
P_i^{\rm out}&=24+e_i+(U_i+n_i)B_5(q_i),\\
V_i^{\rm out}&=24+e_i+(2U_i+n_i)B_6(q_i),\\
A_i^{\rm out}&=24+e_i+(T_i+2j_i+4t_ib_i)B_7(q_i),\\
M_i^{\rm out}&=24+e_i+(3U_i+2n_i)B_7(q_i).
\end{aligned}
$$

Include $P_i^{\rm out}-p=V_i^{\rm out}-v=0$ for each label, with the
same two shared variables $p,v$.

**Definition 2.2 (All slack and inverse equations).** For each label add
three variables $\alpha_i,\beta_i,\gamma_i$ and equations

$$
t_i\alpha_i^2-1=0,\qquad b_i\beta_i^2-1=0,\qquad
(1-t_ib_i)\gamma_i^2-1=0.
$$

Add three inverse variables $\delta_J,\delta_M,\pi$ and equations

$$
\begin{aligned}
\delta_J\{(t_0-t_1)^2+(b_0-b_1)^2\}-1&=0,\\
\delta_M\{(t_2-t_3)^2+(b_2-b_3)^2\}-1&=0,\\
\pi(p-24)-1&=0.
\end{aligned}
$$

Finally add $A_0^{\rm out}-A_1^{\rm out}=0$ and
$M_2^{\rm out}-M_3^{\rm out}=0$. Let $R$ be the polynomial ring over
$\mathbb Q$ in all these variables, let $I_{\rm raw}\subset R$ be the
ideal generated by exactly these equations, and set

$$
\Delta_{\rm raw}=I_{\rm raw}\cap\mathbb Q[p,v].
$$

There are $4(11+3)+2+3=61$ variables and $4(4+1+4+2+3)+5=61$
generators. The raw $J$ subsystem uses labels $0,1$, their world equations,
slacks, common responses, the $J$ terminal equation, $\delta_J$ and $\pi$.
The raw $M$ subsystem uses labels $2,3$ and the corresponding $M$ data.
Their complex base projections are denoted $\mathcal P_J,\mathcal P_M$;
the four-world projection is $\mathcal P_{JM}$.

Over $\mathbb R$ the square slacks encode exactly
$t_i>0,b_i>0,t_ib_i<1$. The pair inverses then encode unequal source
coordinates. Over $\mathbb C$ the square slacks enforce only nonzeroness
of their three factors; they encode no order. Also, over $\mathbb C$ a
sum of two squares can vanish at distinct coordinates. The raw complex
system is the specified polynomial system, not an assertion that these
guards express all possible complex distinct pairs.

**Proposition 2.3 (Faithfulness on the strict-real locus).** Real zeros of
$I_{\rm raw}$ are precisely slack lifts of the original joint witnesses,
up to the nonuniqueness of slack choices.

Proof. Suppress a world label. The real slacks give $r=tb\in(0,1)$ and
$b>0$. Hence $c=t(1-tb)>0$, $j=b+c>0$, $n=j+r>0$, $T>1$, $U>1$.
The sample equations force

$$
q=\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right),
\qquad d=24+e.
$$

The interpolant $g_q$ is one entire polynomial, and its first four
readings are $0,24,147/5,24$. It cannot be identically zero, since those
first two readings differ. Put

$$
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\qquad
\mathcal H=e\Lambda+\frac{6(8b-1)(5b+2)}{5TU}.
$$

Using $TU+6U+T=2(b^2+8b+4)$ gives the exact identities

$$
P^{\rm raw}=5TUjn\,\mathcal H,\qquad
B_4(q)-\frac{-6-e}{U}=\mathcal H.
$$

Thus the raw parent equation gives exactly $y_4=18$, with no division by
$\Lambda$. All later response equations are the literal traces of Lemma
1.3. Conversely every complete world gives these variables, the positive
square-slack choices and the inverse guards.

For completeness, unequal sources are equivalent to unequal complete
worlds within a fixed child. At a fixed source with $\Lambda\ne0$, the
parent fixes $e$. If $\Lambda=0$, the undivided parent forces $b=1/8$;
then $T=9/8,U=5/4$ and $1/j+1/n=107/60$. The coefficient of $e$ in
$p$ is

$$
A_5=1+(n+5/4)\left(\frac{71}{18}-\frac5j\right).
$$

Since $n>j>0$, one has $1/j>107/120$ and $n>120/107$, so

$$
A_5<1-\left(\frac{120}{107}+\frac54\right)\frac{37}{72}
=-\frac{6739}{30816}<0.
$$

The fixed value of $p$ again fixes $e$, and the samples fix the whole
gain and drift. This includes the singular source stratum. Since $b>0$,
$(t,b)$ and $(r,b)$ determine each other, and the real sum-of-squares
inverse excludes exactly equal sources. The terminal equations therefore
express precisely the independent-pair predicate of Definition 1.2. ∎

**Remark 2.4 (Meaning of elimination).** Every original joint base is a real
zero of every polynomial in $\Delta_{\rm raw}$. This necessary-condition
statement is sound. It does not say that every zero of the elimination
ideal has a real, strict or even pointwise complex lift. The next two
results compute obstructions to obtaining a raw unit ideal or a finite
base list, without refuting the original real model.

## 3. The fully guarded zero-trace family

**Lemma 3.1 (Two raw M endpoints).** Put

$$
T=1+b,\quad U=1+2b,\quad D_s=5b^2+2b+1,\qquad
R_b(r)=r^2-(1+b)r-b^2.
$$

For $bTU D_s\ne0$ let $r_+,r_-$ be its two roots. For either root set

$$
t=r/b,\quad e=0,\quad j=-r,\quad n=0,\qquad
q=(-24,0,27/(5T),z).
$$

For arbitrary $z\in\mathbb C$ the two labels have common responses

$$
\begin{aligned}
B_5&=96-108/T+10z,\\
B_6&=240-243/T+20z,\\
B_7&=480-2268/(5T)+35z,\\
p&=24+UB_5,\qquad v=24+2UB_6,\qquad m=24+3UB_7.
\end{aligned}
$$

Whenever $p\ne24$, these give a raw $M$ pair with every required inverse
and square slack.

Proof. For the source formula $j_{\rm src}=r/b+b-r^2/b$,

$$
b(j_{\rm src}+r)=-R_b(r).
$$

Thus $j_{\rm src}=-r$ and $n=j+r=0$. All four sample equations hold;
the parent vanishes because $e=n=0$. The response formulas follow directly
from the interpolation rows and are independent of the chosen root.
The discriminant of $R_b$ is $D_s$, so

$$
(t_+-t_-)^2+(b-b)^2=D_s/b^2\ne0,\qquad \delta_M=b^2/D_s.
$$

The complete slack specification is

$$
\alpha_\pm^2=b/r_\pm,\qquad
\beta_\pm^2=1/b,\qquad
\gamma_\pm^2=1/(1-r_\pm),\qquad \pi=1/(p-24).
$$

These squares have complex square roots. Their denominators are nonzero:
$R_b(0)=-b^2$ and $R_b(1)=-bT$ exclude $r=0,1$. Substitution verifies
all the equations, including the squared slacks, not just the responses.
No real square-root existence is asserted. ∎

**Lemma 3.2 (A four-world subfamily).** Specialize

$$
z=-\frac{12(200b+11)}{175T}.
$$

Then $B_7=0$. Use labels $0,2$ at $r_+$ and labels $1,3$ at $r_-$. Both
terminal common values are $24$, both pair inverses are $b^2/D_s$, and

$$
\begin{aligned}
p_b&=-\frac{12(240b^2+164b-13)}{35T},\\
v_b&=-\frac{6(800b^2+682b+71)}{35T},\\
p_b-24&=-\frac{36U(40b+19)}{35T}.
\end{aligned}
$$

Every parameter outside the zeros of $bTU D_s(40b+19)$ gives a raw joint
lift. In particular every real $b>0$ does so over $\mathbb C$.

Proof. Substitution makes $B_7$ vanish identically. The two terminal
responses are therefore both the drift $24$, irrespective of their
trace factors. Lemma 3.1 supplies all other equations and slacks; the
last displayed identity supplies the off-$24$ inverse. The permission
for cross-pair reuse is exactly the original predicate. ∎

## 4. N1: every raw joint eliminant contains a conic factor

**Theorem 4.1 (Conic containment of the raw elimination ideal).** Set

$$
F(p,v)=525p^2-665pv-9108p+210v^2+5952v+35424.
$$

This polynomial is geometrically irreducible, and

$$
\Delta_{\rm raw}\subseteq(F)\subset\mathbb Q[p,v].
$$

Consequently every nonzero raw joint eliminant is divisible by $F$.
The raw elimination ideal is not the unit ideal, and its zero set cannot
be zero dimensional. The ideal may be zero.

Proof. Make the invertible affine change

$$
X=\frac{7(3p-2v-24)}{96},\qquad
Y=\frac{5(5p-3v-48)}{54}.
$$

Its linear determinant is $35/5184\ne0$. Substituting Lemma 3.2 gives

$$
X=2b+1,\qquad Y=\frac{2b+1}{b+1},\qquad
(X+1)Y-2X=\frac{F(p,v)}{5184}=0.
$$

The inverse parameter on this image is

$$
b=\frac{21p-14v-264}{192}.
$$

The homogeneous conic matrix is

$$
\begin{pmatrix}
525&-665/2&-4554\\
-665/2&210&2976\\
-4554&2976&35424
\end{pmatrix},\qquad \det=-3175200\ne0.
$$

Thus the projective conic is nonsingular. A degree-two polynomial that
factors over $\mathbb C$ gives two lines, whose intersection is singular
(or a double line); hence $F$ is geometrically irreducible. Equivalently,
in the affine $X,Y$ coordinates the curve is
$(X+1)(Y-2)=-2$. The rational inverse exhibits the parametrized image
as a dense subset of this curve. Excluding the finite guard zeros does
not change density. Even the real parameter interval $b>0$ is Zariski
dense in the curve: a rational function vanishing on that interval has
identically zero numerator.

Every polynomial in $\Delta_{\rm raw}$ vanishes on every lifted point
of Lemma 3.2, so vanishes on this dense conic. The ideal of the conic is
$(F)$, proving the stated containment over $\mathbb Q$. Thus its zero
set contains a curve. This also excludes the unit ideal. ∎

There is no assertion that $F\in\Delta_{\rm raw}$, that
$\Delta_{\rm raw}=(F)$, or that the lifted family is a maximal component.
No nonzero element of $\Delta_{\rm raw}$ has been produced here. The
containment alone blocks a raw finite-base or raw unit-ideal outcome.
It leaves elimination valid as a necessary-condition method.

## 5. N2: the raw M subsystem has zero elimination ideal

**Theorem 5.1 (Explicit open-set lift).** Write

$$
w=v-4p,\qquad E(w)=(w+30)(w+72)(5w^2+684w+35793),
$$

and define the nonempty complex Zariski-open set

$$
\mathcal O=\{(p,v)\in\mathbb C^2:(p-24)E(v-4p)\ne0\}.
$$

Every base in $\mathcal O$ has the raw $M$ lift of Lemma 3.1. In
particular the raw $M$ elimination ideal in $\mathbb Q[p,v]$ is zero.

Proof. The family satisfies

$$
v-4p=\frac{6(32b^2+18b-5)}{b+1}.
$$

For a prescribed base choose a root of

$$
f_w(b)=192b^2+(108-w)b-30-w.
$$

This quadratic always has a complex root and has constant nonzero leading
coefficient. Its exact resultant with the prohibited factors is

$$
\operatorname{Res}_b(f_w,bTU D_s)=432E(w).
$$

The four factor identities, proved in Proposition 9.2, are

$$
\begin{aligned}
\operatorname{Res}_b(f_w,b)&=-w-30,\\
\operatorname{Res}_b(f_w,b+1)&=54,\\
\operatorname{Res}_b(f_w,2b+1)&=-2(w+72),\\
\operatorname{Res}_b(f_w,5b^2+2b+1)&=4(5w^2+684w+35793).
\end{aligned}
$$

Since $E(w)\ne0$, every root of $f_w$ avoids all four prohibited
factors. Take any root, even if $f_w$ has a repeated root, and put

$$
z=\frac{p-24}{10U}-\frac{48}{5}+\frac{54}{5T}.
$$

Substitution into the family gives $p_{\rm lift}-p=0$ and
$v_{\rm lift}-v=f_w(b)/T=0$. All remaining guards are those proved in
Lemma 3.1. Thus $\mathcal O\subset\mathcal P_M$.

A polynomial in the $M$ elimination ideal vanishes on this nonempty
open subset of the irreducible affine plane, hence is the zero
polynomial. This proves the ideal assertion without a genericity
assumption about the roots of $f_w$. ∎

**Corollary 5.2 (The raw M condition adds no projected restriction there).**
On this same open set,

$$
\mathcal P_{JM}\cap\mathcal O=\mathcal P_J\cap\mathcal O.
$$

Proof. Restricting a four-world lift gives its $J$ pair. Conversely, at
a base in $\mathcal O$, append the $M$ pair from Theorem 5.1 to any raw
$J$ pair. The labels have no cross-pair equality, distinctness or
terminal-value restrictions. They share only $p,v$ and its inverse, so
the resulting four-world tuple is a raw joint lift. ∎

Theorem 5.1 and Corollary 5.2 concern the complex projection of the
specified raw equations. They imply neither a strict-real $M$ pair nor
density of strict-real collision bases.

**Lemma 5.3 (Jacobian of the raw M family).** In the coordinates $(b,z)$
of Lemma 3.1,

$$
\det D_{(b,z)}(p,v)=-\frac{60U(32b^2+64b+23)}{T^2}.
$$

Proof. Write $v=4p+w(b)$, where
$w(b)=6(32b^2+18b-5)/T$. Then

$$
\partial_zp=10U,\qquad
w'(b)=\frac{6(32b^2+64b+23)}{T^2},\qquad
\det D(p,v)=-\partial_zp\,w'(b).
$$

These identities prove the formula. It is not the zero rational
function. The pointwise lift of Theorem 5.1 includes the exceptional-root
analysis that this derivative statement alone does not supply. ∎

## 6. An explicit non-witness and the lost original reading

**Proposition 6.1 (The positive-parameter conic lifts are false worlds).**
For every real $b>0$ in Lemma 3.2,

$$
r_-<0,\qquad r_+>1+b>1,\qquad
y_4-18=-\frac{6(1800b^2+1391b+158)}{175T}<0.
$$

Thus each displayed raw joint lift fails the strict source conditions
and the original clock-four reading.

Proof. The root product is $-b^2<0$, so one root is negative and one
positive; $R_b(1+b)=-b^2<0$ puts the positive root above $1+b$.
Their slack squares in Lemma 3.1 consequently cannot all be nonnegative
real numbers. They are valid complex slack lifts. At clock four the
literal trace is $U$, and substitution into $24+UB_4-18$ gives the
stated rational expression. All numerator coefficients and $T$ are
positive for $b>0$. The raw parent nevertheless vanished because its
multiplier contained $n=0$. ∎

**Example 6.2 (Exact algebraic point).** At $b=1$ take

$$
\begin{gathered}
r_\pm=1\pm\sqrt2,\quad t_\pm=r_\pm,\quad j_\pm=-r_\pm,
\quad n_\pm=e_\pm=0,\\
g(s)=\frac{3(s-7)(s-1)(337s-800)}{700},\qquad d=24,\\
q=(-24,0,27/10,-1266/175),\qquad
(p,v)=(-2346/35,-4659/35),\qquad a=m=24,\\
\delta_J=\delta_M=1/8,\qquad \pi=-35/3186.
\end{gathered}
$$

Use labels $0,2$ at $r_+$ and $1,3$ at $r_-$. Square slacks are fixed
by

$$
\begin{aligned}
\alpha_+^2&=\sqrt2-1,&\alpha_-^2&=-\sqrt2-1,\\
\beta_+^2&=\beta_-^2=1,\\
\gamma_+^2&=-1/\sqrt2,&\gamma_-^2&=1/\sqrt2.
\end{aligned}
$$

Choose any complex square roots of these values. This satisfies all 61
raw generators. Direct literal matrix readings for either endpoint are

$$
(0,24,147/5,24,-6897/175,-2346/35,-4659/35),
$$

with both terminal alternatives equal to $24$. In particular
$y_4-18=-10047/175$. This is a raw-ideal point and an explicit
non-witness. It excludes neither other lifts at this base nor other
actual joint bases.

Proof of the displayed data. The relation $r^2-2r-1=0$ gives all source
equations. At the eight integer clocks the displayed gain has values

$$
\begin{array}{c|rrrrrrrr}
k&0&1&2&3&4&5&6&7\\ \hline
g(k)&-24&0&27/10&-1266/175&-3699/175&-1062/35&-1833/70&0.
\end{array}
$$

At clocks $0,\ldots,6$ the trace row is $(1,-r,2,0,3,3,6)$.
Thus $24+g(k)\operatorname{tr}(A_kP)$ gives exactly the stated reading
row; in particular $24+3(-3699/175)=-6897/175$. Both terminal readings
are $24$ because $g(7)=0$. The first four gain values determine the
whole cubic by Lemma 1.3, so the factored gain and the sample vector
are the same polynomial. Finally,

$$
(r_+-r_-)^2=8,\quad p-24=-3186/35,\quad
\frac1{r_\pm}=\pm\sqrt2-1,\quad
\frac1{1-r_\pm}=\mp\frac1{\sqrt2}.
$$

These identities prove the inverse and square-slack equations. The
remaining raw equations follow from Lemma 3.2 at $b=1$, whose prohibited
factors are all nonzero there. This accounts for every one of the
$4\cdot14+5=61$ generators of Definition 2.2. ∎

## 7. Strict-real-preserving trace saturation

**Definition 7.1 (Corrected trace ideal and guarded system).** Let

$$
Q=\prod_{i=0}^3T_iU_ij_in_i,\qquad
I_{\rm tr}=I_{\rm raw}:Q^\infty
=\{f\in R:\exists k\ge0,\ Q^kf\in I_{\rm raw}\},\qquad
\Delta_{\rm tr}=I_{\rm tr}\cap\mathbb Q[p,v].
$$

The pointwise guarded presentation is
$\widetilde I_{\rm tr}=(I_{\rm raw},hQ-1)\subset R[h]$.
For a two-world subsystem use the product of $TUjn$ over its two labels
and the same definitions. These definitions do not report a computation
of either corrected elimination ideal.

**Theorem 7.2 (Exact strict-real preservation).** The real zero sets of
$I_{\rm raw}$ and $I_{\rm tr}$ are equal. Equivalently, their
strict-real admissible points are exactly the original witnesses of
Proposition 2.3. Each has a unique extension in $h$ to the real guarded
system.

Proof. Every real raw zero has $T_i,U_i,j_i,n_i>0$, by its real slacks
and source equations. Thus $Q>0$ at every real raw zero. If
$Q^kf\in I_{\rm raw}$, evaluation there implies $f=0$. This gives
$V_{\mathbb R}(I_{\rm raw})\subset V_{\mathbb R}(I_{\rm tr})$;
the reverse inclusion follows from $I_{\rm raw}\subset I_{\rm tr}$.
Taking $h=1/Q$ gives the unique guarded extension.

The factors used are positive for every strict source, independently
of the gain, drift or chart. No condition on $\Lambda$, drift, any gain
sample, gain leading coefficient, root difference, regularity or pair
separation was added. Hence singular and unused worlds, zero drift,
sampled-zero and repeated-root gains and every gain degree drop remain
in the original domain. ∎

**Theorem 7.3 (Restored-clock ideal membership).** For each world define

$$
C_{4i}=U_iB_4(q_i)+6+e_i.
$$

This is its literal clock-four residual $y_{4i}-18$. The following exact
identity holds modulo the two definition generators
$T_i-1-b_i,U_i-1-2b_i$, without imposing the equations for $j_i,n_i$:

$$
\begin{aligned}
5T_ij_in_iC_{4i}={}&P_i^{\rm raw}
-5T_iU_ij_in_i l_{0i}+20T_iU_in_i l_{1i}\\
&-6U_ij_in_i l_{2i}+20T_iU_ij_i l_{3i}.
\end{aligned}
$$

Consequently $C_{4i}\in I_{\rm tr}$. The explicit correction below makes
the identity an equality in the independent-variable ring $R$.

Proof. Expand the right side using Definition 2.1 and collect the four
$q$ coefficients and the constant term. With $T=1+b,U=1+2b$, the
constant coefficient is $5Tjn(6+e)$ because
$TU+6U+T=2L$ and $6A$ has the stated value. The remaining coefficients
are exactly $5TjnU(-1,4,-6,4)$. This proves the identity. Since $T_ijn_i$
divides $Q$, multiplication by
$U_i\prod_{k\ne i}T_kU_kj_kn_k$ puts $QC_{4i}$ in $I_{\rm raw}$,
with the harmless rational factor $1/5$. Thus $C_{4i}\in I_{\rm tr}$.
In the ring with independent $T_i,U_i$, the same argument includes
their definition generators. ∎

There is a completely explicit ambient-ring correction to the displayed
identity. If $D_i$ denotes its left side minus right side, before imposing
$T_i=1+b_i,U_i=1+2b_i$, then

$$
D_i=j_in_i\{5e_i(T_iU_i+6U_i+T_i-2L_i)+30T_i-6A_i+120T_iU_i-162U_i\}.
$$

Writing $T_i^0=1+b_i,U_i^0=1+2b_i$, the expression in braces equals

$$
\{5e_i(U_i+1)+30+120U_i\}(T_i-T_i^0)
+\{5e_i(T_i^0+6)+120T_i^0-162\}(U_i-U_i^0).
$$

This supplies ideal membership in precisely the independent-variable
presentation of Definition 2.1, rather than silently changing its ring.

**Proposition 7.4 (Pointwise guards and closure have different boundaries).**
Over $\mathbb C$, the guarded system projects in all original variables
onto $V(I_{\rm raw})\cap\{Q\ne0\}$, whereas

$$
V(I_{\rm tr})=\overline{V(I_{\rm raw})\cap\{Q\ne0\}}^{\rm Zar},
\qquad
\widetilde I_{\rm tr}\cap R=I_{\rm tr}.
$$

In particular eliminating $h$ and the world variables gives
$\Delta_{\rm tr}$ in either presentation. The unrestricted complex
point sets need not agree: the closure can contain $Q=0$ boundary points.

Proof. The equation $hQ=1$ has a solution exactly when $Q\ne0$, and
then $h=1/Q$. The ring map to the localization $R[Q^{-1}]$ has
contraction of the extended ideal equal to $I_{\rm raw}:Q^\infty$:
clearing a power of $Q$ proves both inclusions. The algebraically closed
zero-set statement is the corresponding closure theorem, or follows by
applying the Nullstellensatz to this localization. Contraction once more
to $\mathbb Q[p,v]$ gives the elimination assertion. ∎

All displayed $n=0$ lifts are removed by the pointwise guard $hQ-1$.
The positive-$b$ joint lifts of Proposition 6.1 are also excluded from
$V(I_{\rm tr})$ itself, since their restored residual $C_4$ is nonzero.
No claim excludes every complex-parameter boundary specialization, every
false complex lift, or other lifts of their projected bases. In particular
nothing here proves that the corrected base projection is smaller or
that it has a nonzero elimination ideal.

## 8. Open problems and mathematical references

**Open problem 8.1 (Corrected algebra).** Determine the elimination geometry
of the trace-saturated two-world $M$ subsystem, or of $I_{\rm tr}$.
Specifically, determine its elimination ideal in $\mathbb Q[p,v]$,
including whether it is zero and whether a corrected component has dense
base projection. The raw family of Section 3 has $n=0$ and therefore
does not give a lift to the pointwise corrected system.

**Open problem 8.2 (Original strict-real target).** Find real $p\ne24,v$
and four complete worlds satisfying Definition 1.2, with all original
clocks and both within-pair distinctness conditions, or prove absence
over the entire original domain. A corrected algebraic base, if found,
still needs four strict-real lifts, their entire nonzero gains and fixed
drifts. Independent pairs, cross-pair overlap and separate common
terminal values remain allowed. A negative answer must cover all actual
strata and all bases; no unexamined component, boundary mechanism or
unbounded range is excluded by the present results.

No exclusion of a negative-$p$ $J$ branch, a positive-$p$ $J$ arc, or any
other actual component follows here. The false family has equal $b$ at
both endpoints but contains no actual pair. Consequently it supplies no
counterexample to an injectivity statement about actual strict worlds.

The following references fix the model and notation. All definitions
needed for the preceding results are also displayed above.

| Reference | Mathematical correspondence |
| --- | --- |
| [O: common parent](https://github.com/the-omega-institute/trureturing/blob/c91f4841791e83e61d117ab81a4a70495567f21d/docs/develop/theory/FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Definitions 1.1–1.3, Theorems 2.1 and 4.2 | Whole strict source, literal traces, zero-safe converse; its $\epsilon$ is $e$ here, its $\beta=1/8$, and $r=tb$. The singular fifth-response coefficient used in Proposition 2.3 is its $A_5$. |
| [F: finite fibre](https://github.com/the-omega-institute/trureturing/blob/c91f4841791e83e61d117ab81a4a70495567f21d/docs/develop/theory/FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md), Lemma 30.2 and Definition 33.1 | Faithful whole-world reconstruction and independent same-base pair semantics. Its $(x,d)$ coordinates are not substituted for the complete worlds here. No finite-world theorem supplies a finite list of all bases. |
| [S: joint support](https://github.com/the-omega-institute/trureturing/blob/c91f4841791e83e61d117ab81a4a70495567f21d/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md), Definitions 1.1–1.2 | The original entire child and the unchanged $D_J,D_M$ quantifiers. |
| [SII: unused companion](https://github.com/the-omega-institute/trureturing/blob/c91f4841791e83e61d117ab81a4a70495567f21d/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_II.md), Definitions 2.1–2.2 and Proposition 2.3 | Original gain samples and response/interpolation interface; its regular division by $\Lambda$ is not used to define the present domain. |
| [SIII: J tail](https://github.com/the-omega-institute/trureturing/blob/c91f4841791e83e61d117ab81a4a70495567f21d/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md), Definitions 1.1–1.2 | Whole-world quantifiers, literal traces and undivided parent, with all singular and unused worlds retained. |
| [SIV: undivided responses](https://github.com/the-omega-institute/trureturing/blob/c91f4841791e83e61d117ab81a4a70495567f21d/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_IV.md), Theorem 8.2 | Interpolation identities valid on the undivided parent; no permission to divide by $\Lambda$ merely because a regular formula exists. |
| [SV: regional result](https://github.com/the-omega-institute/trureturing/blob/c91f4841791e83e61d117ab81a4a70495567f21d/docs/develop/theory/FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_V.md), Sections 1–2 | Original joint target and explicit clock-four residual. Its regional exclusions and strict $M$ point are not promoted to global claims. |

For Lagrange interpolation, see Berrut and Trefethen,
*Barycentric Lagrange Interpolation*, §2,
[DOI 10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715).
For Sylvester resultants, irreducible conics, elimination and saturation,
see Cox, Little and O'Shea, *Ideals, Varieties, and Algorithms*, fourth
edition, Chapters 3–4,
[DOI 10.1007/978-3-319-16721-3](https://doi.org/10.1007/978-3-319-16721-3).

## 9. Finite polynomial identities

**Proposition 9.1 (Integer conic identity).** Define

$$
N_p=156-1968b-2880b^2,\quad
N_v=-426-4092b-4800b^2,\quad D=35+35b.
$$

Then $p_b=N_p/D,v_b=N_v/D$, and

$$
525N_p^2-665N_pN_v-9108N_pD+210N_v^2+5952N_vD+35424D^2=0.
$$

Proof. The coefficients of the six summands, in ascending powers of $b$,
are the following exact integers.

| Summand | $b^0$ | $b^1$ | $b^2$ | $b^3$ | $b^4$ |
| --- | ---: | ---: | ---: | ---: | ---: |
| $525N_p^2$ | 12776400 | -322358400 | 1561593600 | 5951232000 | 4354560000 |
| $-665N_pN_v$ | 44193240 | -133010640 | -5673205440 | -14118854400 | -9192960000 |
| $-9108N_pD$ | -49729680 | 577629360 | 1545445440 | 918086400 | 0 |
| $210N_v^2$ | 38109960 | 732140640 | 4375153440 | 8249472000 | 4838400000 |
| $5952N_vD$ | -88744320 | -941189760 | -1852381440 | -999936000 | 0 |
| $35424D^2$ | 43394400 | 86788800 | 43394400 | 0 | 0 |
| Sum | 0 | 0 | 0 | 0 | 0 |

For example the $b^2$ coefficient in the first row is
$525(1968^2-2\cdot156\cdot2880)=1561593600$; the other entries
follow from the same multiplication rule
$[b^k](AB)=\sum_{i=0}^k[b^i]A\,[b^{k-i}]B$.
Each column sums to zero, proving the polynomial identity. Division by
$D^2$ on $b\ne-1$ proves $F(p_b,v_b)=0$. This identity asserts no
membership of $F$ in $\Delta_{\rm raw}$. ∎

**Proposition 9.2 (Resultant identities and determinant data).** With
$f_w$ and $D_s$ as in Theorem 5.1, the four factor identities there hold,
and

$$
\operatorname{Res}_b(f_w,bTU D_s)=432E(w).
$$

Proof. For a degree-two polynomial $f$ and a linear polynomial $ab+c$,
its root product gives
$\operatorname{Res}_b(f,ab+c)=a^2f(-c/a)$ when $a\ne0$.
Consequently the first three factors are

$$
f_w(0)=-w-30,\quad f_w(-1)=54,\quad
4f_w(-1/2)=-2(w+72).
$$

For the fourth factor put $h=156-5w$ and $k=-342-5w$. There is the
polynomial identity

$$
5f_w(b)-192D_s(b)=hb+k.
$$

The roots $s_1,s_2$ of $D_s$ satisfy
$s_1+s_2=-2/5$ and $s_1s_2=1/5$. The degree-two resultant is symmetric
in its two arguments. Its root product therefore gives

$$
\begin{aligned}
\operatorname{Res}_b(f_w,D_s)
&=25f_w(s_1)f_w(s_2)\\
&=(hs_1+k)(hs_2+k)\\
&=\frac{h^2-2hk+5k^2}{5}\\
&=20w^2+2736w+143172\\
&=4(5w^2+684w+35793).
\end{aligned}
$$

Multiplicativity in the second argument now gives $432E(w)$, with
constant factor $1\cdot54\cdot(-2)\cdot4$ and the sign from $-w-30$.
The argument uses only root sums and products, so repeated roots cause
no exception.

For explicit determinant data,

$$
bTU D_s=10b^5+19b^4+13b^3+5b^2+b,
$$

and the Sylvester matrix is

$$
\begin{pmatrix}
192&108-w&-30-w&0&0&0&0\\
0&192&108-w&-30-w&0&0&0\\
0&0&192&108-w&-30-w&0&0\\
0&0&0&192&108-w&-30-w&0\\
0&0&0&0&192&108-w&-30-w\\
10&19&13&5&1&0&0\\
0&10&19&13&5&1&0
\end{pmatrix}.
$$

By the defining Sylvester determinant formula its determinant is the
resultant just computed. Expanding
$(w+30)(w+72)=w^2+102w+2160$ and multiplying by the quadratic factor
of $E$ yields the exact coefficient table

| Polynomial | $w^0$ | $w^1$ | $w^2$ | $w^3$ | $w^4$ |
| --- | ---: | ---: | ---: | ---: | ---: |
| $E(w)$ | 77312880 | 5128326 | 116361 | 1194 | 5 |
| $432E(w)$ | 33399164160 | 2215436832 | 50267952 | 515808 | 2160 |

This proves all the determinant coefficients without an assumption about
any specialized root. ∎

**Proposition 9.3 (Supports of the cleared polynomials).** Impose only

$$
T=1+b,\quad U=1+2b,\quad j=t+b(1-t^2),\quad n=j+tb,\quad r=tb.
$$

Let $\widehat P$ be $P^{\rm raw}$ after these substitutions. Define
$R_p=P^{\rm out},R_v=V^{\rm out},R_a=A^{\rm out},R_m=M^{\rm out}$,
suppressing the world label from Definition 2.1. For each response substitute
$q=(-24-e,-e/j,(27/5-e)/T,-e/n)$ and define the polynomial
$H_x=5TjnR_x$. With an independent output indeterminate $o_x$, put
$G_x=H_x-5Tjn\,o_x$. Then

| Polynomial | Nonzero monomials | Total degree |
| --- | ---: | ---: |
| $\widehat P$ | 39 | 9 |
| $H_p$ | 53 | 11 |
| $H_v$ | 54 | 11 |
| $H_a$ | 54 | 11 |
| $H_m$ | 54 | 11 |
| $G_p$ | 67 | 11 |
| $G_v$ | 68 | 11 |
| $G_a$ | 68 | 11 |
| $G_m$ | 68 | 11 |

These are identities of polynomials; no division on a zero-trace locus
is used to infer the existence of a world.

Proof. In the polynomial ring $\mathbb Q[t,b,e]$ write $D_0=5Tjn$ and

$$
\begin{aligned}
K_5={}&480Tjn-540jn
 +e(20Tjn-75Tn+100jn-50Tj),\\
K_6={}&1200Tjn-1215jn
 +e(50Tjn-180Tn+225jn-100Tj),\\
K_7={}&2400Tjn-2268jn
 +e(100Tjn-350Tn+420jn-175Tj).
\end{aligned}
$$

Multiplying the interpolation rows by $D_0$ gives $D_0B_k=K_k$ in
$\mathbb Q(t,b,e)$ for $k=5,6,7$, and hence the polynomial formulas

$$
\begin{aligned}
H_p&=D_0(24+e)+(U+n)K_5,\\
H_v&=D_0(24+e)+(2U+n)K_6,\\
H_a&=D_0(24+e)+(T+2j+4tb)K_7,\\
H_m&=D_0(24+e)+(3U+2n)K_7,\\
\widehat P&=5e\{2(b^2+8b+4)jn-4TU(j+n)\}
 +6(8b-1)(5b+2)jn.
\end{aligned}
$$

Here the coefficient lists in ascending powers of $t$ of $j,n$ are
$(b,1,-b)$ and $(b,1+b,-b)$. Ordinary polynomial multiplication gives
the following numbers of nonzero $b$ coefficients in each $t$ coefficient.
Each polynomial has the form $Z_0(t,b)+eZ_1(t,b)$.

| Polynomial | $Z_0$: counts at $t^0,\ldots,t^6$ | $Z_1$: counts at $t^0,\ldots,t^6$ | $\deg Z_0$ | $\deg Z_1$ |
| --- | --- | --- | ---: | ---: |
| $\widehat P$ | $(3,4,5,4,3,0,0)$ | $(3,5,5,4,3,0,0)$ | 8 | 8 |
| $H_p$ | $(3,4,5,5,4,3,2)$ | $(4,5,4,5,4,3,2)$ | 10 | 10 |
| $H_v$ | $(3,4,5,5,4,3,2)$ | $(4,5,5,5,4,3,2)$ | 10 | 10 |
| $H_a$ | $(3,4,5,5,4,3,2)$ | $(4,5,5,5,4,3,2)$ | 10 | 10 |
| $H_m$ | $(3,4,5,5,4,3,2)$ | $(4,5,5,5,4,3,2)$ | 10 | 10 |

Every entry is obtained by the coefficient convolution rule in
Proposition 9.1 applied to the displayed short formulas. Summing the two
lists gives 39 for $\widehat P$, 53 for $H_p$ and 54 for each of the
other $H_x$. Their degrees are the displayed degrees plus the one power
of $e$ in $eZ_1$. Finally $D_0$ has coefficient lists

$$
5b^2(1+b),\quad 5b(1+b)(2+b),\quad
5(1+b)(1+b-2b^2),\quad -5b(1+b)(2+b),\quad 5b^2(1+b)
$$

at $t^0,\ldots,t^4$, with respectively $2,3,4,3,2$ nonzero
$b$ coefficients and total degree 7. Thus $D_0o_x$ contributes exactly
14 new monomials to $G_x$, disjoint from those of $H_x$, and has total
degree 8, below 11. This proves every count and degree in the first
table. ∎

## 追加锚（本行以下为增补区）

## 10. An evaluated lower-face mixed-J target

Sections 10–16 retain the complete worlds, acquired history and clocks of
Section 1. They give an exact off-$24$ base with three actual worlds,
an explicit rectangle on which $M$ is injective on every entire child,
and actual $J$ collisions whose bases tend to that $J$-injective target.
The lower-face tuple used to specify the target is auxiliary, not a world.

For supplier references, O denotes
[the common-parent volume](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md),
F denotes [the finite-fibre volume](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md),
S denotes [strict support](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT.md),
SIII denotes [support III](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md),
and SVII denotes [support VII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VII.md).
Every child below is the whole original $C(p,v)$, including unused companions.

**Definition 10.1 (Source circuit and B0 tuple).** With $j,n,T,U$ as in
Definition 1.2, put

$$
\begin{gathered}
L=b^2+8b+4,\qquad A=(8b-1)(5b+2),\\
D=5\{Ljn-2TU(j+n)\},\\
C_0=-24D+3Ajn,\quad C_1=3An,\\
C_2=3(49b+34)jn-54U(j+n),\quad C_3=3Aj,\\
\mathcal B_5=-4C_0+15C_1-20C_2+10C_3,\\
\mathcal B_6=-10C_0+36C_1-45C_2+20C_3,\\
\mathcal B_7=-20C_0+70C_1-84C_2+35C_3,\\
N_p=-C_0+(U+n)\mathcal B_5,\quad
N_v=-C_0+(2U+n)\mathcal B_6,\\
N_a=-C_0+(T+2j+4r)\mathcal B_7,\quad
N_m=-C_0+(3U+2n)\mathcal B_7.
\end{gathered}
\tag{10.1}
$$

On a strict source with $D\ne0$, the reused full-parent converse gives

$$
\begin{gathered}
(p,v,a,m)=(N_p,N_v,N_a,N_m)/D,\qquad d=-C_0/D,\\
g(s)=\sum_{k=0}^3\frac{C_k}{D}
\prod_{\substack{0\le l\le3\\l\ne k}}\frac{s-l}{k-l}.
\end{gathered}
\tag{10.2}
$$

The $C_k/D$ are four samples of one entire polynomial. Substitution
verifies the original readings $0,24,147/5,24,18$ at clocks $0,\ldots,4$.
The later responses use Lemma 1.3's literal left-product traces. The
gain is nonzero because the first two readings differ. This regular
circuit is SVII, Section 2; possible companions are not assumed regular.

For $t>0$, $t\ne1$, define the auxiliary B0 tuple by

$$
\begin{gathered}
(r,b,c)=(0,0,t),\qquad
P_B(t)=\begin{pmatrix}0&0\\t&1\end{pmatrix},\qquad q(t)=10(t-1),\\
P_0=-3(16t^2-80t+65),\quad V_0=3(45t^2+125t-172),\\
A_0=3(384t^2-113t-273),\quad M_0=3(384t^2+271t-659),\\
(p_B,v_B,a_B,m_B)=(P_0,V_0,A_0,M_0)/q,\qquad
d_B=24+\frac{3t}{10(t-1)},\\
g_B=\operatorname{Interp}_{0,1,2,3}
\left(-d_B,\frac{24-d_B}{t},\frac{147}{5}-d_B,\frac{24-d_B}{t}\right).
\end{gathered}
\tag{10.3}
$$

The local symbols $A_0,P_0$ in (10.3) are scalar polynomials, not the
chronological product matrices. Substituting
$r=tz,b=z,c=t(1-tz)$ in the source chart and setting $z=0$ gives
(10.3). The original matrix products give these auxiliary readings.
The tuple is nonstrict and is never admitted into $C(p,v)$.

With variable order $(r,b,t)$ define

$$
E_i=q(t)b^3N_i-A_i(t)b^3D,\qquad F_i=E_i/15,\qquad
(A_p,A_v,A_a)=(P_0,V_0,A_0).
\tag{10.4}
$$

After substituting $j=b+r(1-r)/b$, each $E_i$ is an integer
polynomial of content exactly $15$. The $F_i$ are primitive with
the signs in (10.4) retained. Section 11 gives every coefficient
and an isolating cube $X_*$. Define the exact target by

$$
(r_*,b_*,t_*)=\text{the unique zero of }(F_p,F_v,F_a)\text{ in }X_*,
\qquad y_*=(p_B(t_*),v_B(t_*)).
\tag{10.5}
$$

Its existence is proved below. Decimal orientations, not definitions, are

$$
\begin{aligned}
r_*&\simeq0.68399878084156020855,& b_*&\simeq0.32366813280827214357,\\
t_*&\simeq2.07806639693805013875,& p_*&\simeq8.94700529903320808475,\\
v_*&\simeq78.49734436733537437471,& a_*&\simeq320.13669693593505.
\end{aligned}
$$

**Theorem 10.2 (Evaluated result).** The exact target belongs to the
actual off-$24$ base image. Its entire child consists of exactly the
three strict complete worlds constructed in Section 14, and both
terminal responses are injective on it. The explicit closed rectangle
$\mathcal B$ in Section 11 contains $y_*$ in its interior, and on
every entire child over $\mathcal B$ any two distinct worlds have
$M$ responses separated by more than $1/20$. There is an actual
distinct equal-$J$ pair arc tending to $y_*$, with one endpoint
having $b\to0$ and both endpoints having $b<1$. Consequently $D_J$
is not relatively closed in the actual off-$24$ base image. No
original joint base lies in $\mathcal B$.

The proof consists of the target contraction in Section 11, the
all-world root filter in Sections 12–13, the strict constructions and
exact face rejection in Section 14, and the continuation in Section 15.
No constant child cardinality in a neighborhood is asserted.

## 11. Complete target data and explicit base rectangle

A row $(i,j,k;c_p,c_v,c_a)$ below gives the coefficients of
$r^ib^jt^k$ in $(F_p,F_v,F_a)$. Every omitted coefficient is zero.
This fixes the signs and normalization without a primitive-part convention.

| $(i,j,k)$ | $c_p$ | $c_v$ | $c_a$ |
| --- | --- | --- | --- |
| $(6,1,1)$ | -512 | -1770 | -8256 |
| $(6,1,0)$ | 512 | 1770 | 8256 |
| $(6,0,1)$ | 64 | -180 | -1536 |
| $(6,0,0)$ | -64 | 180 | 1536 |
| $(5,2,1)$ | 1024 | 3540 | 24768 |
| $(5,2,0)$ | -1024 | -3540 | -24768 |
| $(5,1,1)$ | 1408 | 5670 | 29376 |
| $(5,1,0)$ | -1408 | -5670 | -29376 |
| $(5,0,1)$ | -192 | 540 | 4608 |
| $(5,0,0)$ | 192 | -540 | -4608 |
| $(4,3,2)$ | 16 | -45 | -384 |
| $(4,3,1)$ | 1408 | 8575 | 3697 |
| $(4,3,0)$ | -1423 | -8528 | -3311 |
| $(4,2,2)$ | 128 | -360 | -3072 |
| $(4,2,1)$ | -2224 | -4730 | -51170 |
| $(4,2,0)$ | 2104 | 5106 | 54258 |
| $(4,1,2)$ | 64 | -180 | -1536 |
| $(4,1,1)$ | -1280 | -6030 | -33984 |
| $(4,1,0)$ | 1220 | 6218 | 35528 |
| $(4,0,1)$ | 192 | -540 | -4608 |
| $(4,0,0)$ | -192 | 540 | 4608 |
| $(3,4,2)$ | -16 | 45 | 384 |
| $(3,4,1)$ | -2352 | -11795 | -34577 |
| $(3,4,0)$ | 2367 | 11748 | 34191 |
| $(3,3,2)$ | -160 | 450 | 3840 |
| $(3,3,1)$ | -2874 | -20862 | -16340 |
| $(3,3,0)$ | 3024 | 20392 | 12480 |
| $(3,2,2)$ | -320 | 900 | 7680 |
| $(3,2,1)$ | 1420 | -1216 | 27420 |
| $(3,2,0)$ | -1120 | 276 | -35140 |
| $(3,1,2)$ | -128 | 360 | 3072 |
| $(3,1,1)$ | 384 | 2130 | 12864 |
| $(3,1,0)$ | -264 | -2506 | -15952 |
| $(3,0,1)$ | -64 | 180 | 1536 |
| $(3,0,0)$ | 64 | -180 | -1536 |
| $(2,5,2)$ | -32 | 90 | 768 |
| $(2,5,1)$ | -752 | -6250 | 2062 |
| $(2,5,0)$ | 782 | 6156 | -2834 |
| $(2,4,2)$ | -112 | 315 | 2688 |
| $(2,4,1)$ | 3806 | 17719 | 42071 |
| $(2,4,0)$ | -3701 | -18048 | -44773 |
| $(2,3,2)$ | 208 | -585 | -4992 |
| $(2,3,1)$ | 1776 | 16135 | 18701 |
| $(2,3,0)$ | -1971 | -15524 | -13683 |
| $(2,2,2)$ | 256 | -720 | -6144 |
| $(2,2,1)$ | -280 | 2594 | 526 |
| $(2,2,0)$ | 40 | -1842 | 5650 |
| $(2,1,2)$ | 64 | -180 | -1536 |
| $(2,1,0)$ | -60 | 188 | 1544 |
| $(1,6,2)$ | 16 | -45 | -384 |
| $(1,6,1)$ | 1168 | 6975 | 9009 |
| $(1,6,0)$ | -1183 | -6928 | -8623 |
| $(1,5,2)$ | 96 | -270 | -2304 |
| $(1,5,1)$ | 478 | 5750 | -4508 |
| $(1,5,0)$ | -568 | -5468 | 6824 |
| $(1,4,2)$ | 96 | -270 | -2304 |
| $(1,4,1)$ | -1758 | -8398 | -18552 |
| $(1,4,0)$ | 1668 | 8680 | 20868 |
| $(1,3,2)$ | -96 | 270 | 2304 |
| $(1,3,1)$ | -270 | -4130 | -8724 |
| $(1,3,0)$ | 360 | 3848 | 6408 |
| $(1,2,2)$ | -64 | 180 | 1536 |
| $(1,2,1)$ | 60 | -188 | -1544 |
| $(0,7,2)$ | 16 | -45 | -384 |
| $(0,7,1)$ | -224 | -875 | -703 |
| $(0,7,0)$ | 209 | 922 | 1089 |
| $(0,6,1)$ | -1492 | -8862 | -12372 |
| $(0,6,0)$ | 1492 | 8862 | 12372 |
| $(0,5,2)$ | -128 | 360 | 3072 |
| $(0,5,1)$ | -290 | -3972 | -7882 |
| $(0,5,0)$ | 410 | 3596 | 4794 |
| $(0,4,2)$ | -64 | 180 | 1536 |
| $(0,4,1)$ | 60 | -188 | -1544 |

Let $c_*=(c_r,c_b,c_t)$ have the exact coordinates

$$
\begin{aligned}
c_r&=\frac{683998780841560208554448616829450442743353086213714530710823392695898901305303170647814829}{10^{90}}\\
c_b&=\frac{323668132808272143570558182191714710928582728719431916896201439825400776925540069693240735}{10^{90}}\\
c_t&=\frac{207806639693805013875346556547794225462574257058612065292917036392093267796706525036285234}{10^{89}}
\end{aligned}
$$

Set $\rho_*=10^{-55}$ and $X_*=c_*+[-\rho_*,\rho_*]^3$.
The exact matrix $Y_*$, with rows $(r,b,t)$ and columns
$(F_p,F_v,F_a)$, is

$$
Y_*=\begin{pmatrix}
\frac{-607990027587487344605795890799641148237160622019418468014035922364951571907898522035797344}{10^{90}} & \frac{305381878397587486604018418033990630432356276180516384346545748730185696087463629958595926}{10^{90}} & \frac{-60853367161827409022811324059116128253913093312976751977787264196628598803835302468190496}{10^{90}}\\
\frac{24211969687691792822123073183827724727165028671274347715808671409023763591616712330706864}{10^{89}} & \frac{-127714408932321601750711922689088534080457170249401884905842951786265774817986676977428551}{10^{90}} & \frac{24972762933605451580513027179903339753052795313026658367502348806907945325513657619770364}{10^{90}}\\
\frac{-532592903480221121556787650304534462562384923159556252625777002824964629934801372001519375}{10^{90}} & \frac{-195725198457326240439318636330721134598943596020313349296919977613756166617579540901916278}{10^{90}} & \frac{141698514158573154175786178559020183467729406846188233894093598883601097119811508531506328}{10^{90}}
\end{pmatrix}.
\tag{11.1}
$$

The following rational rule specifies all finite enclosures below.
Put $S=10^{100}$. Store a real interval as $[l/S,u/S]$ with integer
endpoints; embed rationals by outward floor and ceiling. Addition and
subtraction use exact endpoints. Multiplication takes the smallest and
largest of the four endpoint products and rounds outward to the grid.
For reciprocal, first exclude zero, reverse reciprocal endpoints and
round outward. Powers and coefficient convolution use these operations.
A complex rectangle is a pair of real intervals with ordinary complex
operations, using the real-coordinate infinity norm. Evaluate sparse
polynomials by coefficient sums; for the carrier first enclose each
coefficient in $(p,v)$ and then use Horner evaluation in $x$.
Derivatives are taken before interval evaluation.

**Proposition 11.1 (Target contraction and containment).** The literal
data above give

$$
\|Y_*F(c_*)\|_\infty<10^{-85},\qquad
\sup_{X_*}\|I-Y_*DF\|_\infty<10^{-45}.
\tag{11.2}
$$

Throughout $X_*$ one has $0<r<1$, $b>0$, $t>1$ and $D\ne0$.
Thus (10.5) is well-defined and its strict source gives a complete
world with exact original $(p,v,a)=(p_B,v_B,a_B)(t_*)$.

The base rectangle is

$$
\begin{aligned}
p_c&=\frac{894700529903320808475410711061329702914773370179062}{10^{50}},\\
v_c&=\frac{7849734436733537437471326878376706014015012078412063}{10^{50}},\\
\delta&=10^{-35},\qquad
\mathcal B=[p_c-\delta,p_c+\delta]\times[v_c-\delta,v_c+\delta].
\end{aligned}
\tag{11.3}
$$

Evaluation of $p_B,v_B$ on $[c_t-10^{-55},c_t+10^{-55}]$ lies
strictly inside the respective intervals in (11.3), so
$y_*\in\operatorname{int}\mathcal B$. Every point of $\mathcal B$
has $p\ne24$.

Proof. Each bound is an endpoint rational comparison from the
coefficient table and displayed circuits under the specified rule.
For the cube self-map use
$10^{-85}+10^{-45}\rho_*<\rho_*$. The map
$w\mapsto w-Y_*F(w)$ is a strict contraction. Also $Y_*DF$ is
within distance less than one of $I$, so is invertible, making
$Y_*$ nonsingular. Banach's contraction theorem gives exactly one
fixed point, which is exactly a zero of $F$. Strictness, the source
denominator and the rectangle inclusion are direct evaluations.
The equalities follow from the polynomial equations, not overlap
of rounded response intervals. ∎

## 12. Reused all-world carrier and zero-safe faithful inverse

The precise reused interface is recorded to specify the finite
calculation. Put $x=n/U>0$, $\mathscr D=x(x+1)(x+2)$ and define

$$
\begin{gathered}
h_3=(24-d)/x,\quad h_4=18-d,\quad
h_5=(p-d)/(x+1),\quad h_6=(v-d)/(x+2),\\
H(s)=\sum_{i=3}^6h_i
\prod_{\substack{3\le k\le6\\k\ne i}}\frac{s-k}{i-k},\\
H_0=20h_3-45h_4+36h_5-10h_6,\\
H_1=10h_3-20h_4+15h_5-4h_6,\quad
H_2=4h_3-6h_4+4h_5-h_6,\\
H_7=-h_3+4h_4-6h_5+4h_6,\\
\beta_0=294/5-2d-H_2,\qquad \chi_0=d^2+\beta_0^2,\\
U=\frac{-dH_0+\beta_0H_2}{\chi_0},\quad
b=(U-1)/2,\quad j=\frac{U(24-d)}{H_1},\quad r=xU-j.
\end{gathered}
\tag{12.1}
$$

The local symbols $\beta_0,\chi_0$ distinguish this circuit from the
source $C_0$ and the B0 face. F, Lemma 30.2, gives exactly the guards

$$
\begin{gathered}
x>0,\quad d\ne24,\quad H_1\ne0,\quad \chi_0>0,\quad U>1,
\quad0<r<1,\\
j=b+r(1-r)/b,\qquad dU=-H_0,\qquad \beta_0U=H_2.
\end{gathered}
\tag{12.2}
$$

They are necessary and sufficient for the reconstructed actual
world, with one entire gain $g=H/U$, fixed drift $d$, and

$$
a=d+\frac{T+2j+4r}{U}H_7,\qquad m=d+(3+2x)H_7.
\tag{12.3}
$$

In particular $(x,d)$ determines at most one actual world. A root
of a necessary eliminant is not a sufficient lift.

The following coefficient construction fixes the carrier completely:

$$
\begin{gathered}
z_3=(24-d)(x+1)(x+2),\quad z_4=(18-d)\mathscr D,\\
z_5=(p-d)x(x+2),\quad z_6=(v-d)x(x+1),\\
a_0=20z_3-45z_4+36z_5-10z_6,\\
a_1=10z_3-20z_4+15z_5-4z_6,\quad
a_2=4z_3-6z_4+4z_5-z_6,\\
z_*=xa_1-\mathscr D(24-d),\\
f=5d\mathscr D a_2+a_0\{(294-10d)\mathscr D-5a_2\},\\
K=4a_0^2z_*^2+2a_0(d\mathscr D-a_0)z_*a_1
-(a_0+d\mathscr D)\{d\mathscr D+(1-2x)a_0\}a_1^2,\\
F_0=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480.
\end{gathered}
\tag{12.4}
$$

Let $\mathsf S$ have rows $d^3f,d^2f,df,f,dK,K$ and columns
$d^5,d^4,d^3,d^2,d,1$, retaining that size at every specialization.
Define $R\in\mathbb Z[x,p,v]$ by the exact quotient

$$
\det\mathsf S=256\mathscr D^8F_0^2R.
\tag{12.5}
$$

Division has zero remainder, yields $512$ nonzero monomials and
coordinate degrees $(18,6,6)$, and removes no primitive factor.
This is F's carrier: $K=4k$ scales its last two Sylvester rows,
changing the factor $16$ to $256$ and leaving $R$ unchanged.
Its constant $x$ coefficient is

$$
[x^0]R=10^6(32p-5v-366)^2
(120p^2-38pv-3360p+3v^2+522v+23112)^2.
\tag{12.6}
$$

Write $f=A_fd^2+B_fd+C_f$, $K=\sum_{i=0}^4K_id^i$ and set

$$
\begin{aligned}
\alpha={}&K_4(-B_f^3+2A_fB_fC_f)
+K_3A_f(B_f^2-A_fC_f)-K_2A_f^2B_f+K_1A_f^3,\\
\zeta={}&K_4(-B_f^2C_f+A_fC_f^2)
+K_3A_fB_fC_f-K_2A_f^2C_f+K_0A_f^3,\\
Q={}&K_4(A_f^2d^2-A_fB_fd+B_f^2-A_fC_f)
+K_3A_f(A_fd-B_f)+K_2A_f^2.
\end{aligned}
\tag{12.7}
$$

Exact coefficient convolution gives

$$
A_f^3K-\alpha d-\zeta=fQ,
\tag{12.8}
$$

with $280$ and $405$ monomials in $\alpha,\zeta$. S, Theorem 4.1,
and SVII, Lemma 15.1 and Section 16, give for every actual world

$$
R(x,p,v)=0,\qquad \alpha(x,p,v)d+\zeta(x,p,v)=0.
\tag{12.9}
$$

The exceptional-point mechanisms of these suppliers matter here.
Identity (12.8) divides by neither $A_f$ nor $d$, so includes
specialized degree drops. At $d=0$, an actual world has $H_0=0$,
making $K=0$ directly. The actual equations in (12.2) exclude
$d=\beta_0=0$, which would give both $H_2=0$ and $H_2=294/5$.
Thus the inverse remains safe at zero drift.

At $F_0=0$ one does not cancel $F_0$ in (12.5). The suppliers use
polynomial density on the regular source chart; a nonzero pullback
witness is

$$
(r,b)=(1/2,1/4),\qquad
(x,p,v,F_0)=(7/6,19224/515,464403/2575,5736351/4120).
$$

At a singular actual source $b=1/8$ and $e=d-24\ne0$ off $24$.
The undivided parent is
$e\Lambda+(24/5)(b-1/8)B=0$, where
$\Lambda=1+6/T+1/U-4/j-4/n$ and $B=6/T-2/U$. On that line

$$
\begin{gathered}
\Lambda=\Phi(r)/(960jn),\\
\Phi=438272r^4-931328r^3+540800r^2-50728r-853,\\
\operatorname{disc}\Phi=3648425367354069653778543411200\ne0.
\end{gathered}
$$

Hence $e\Lambda_r\ne0$, yielding nearby actual regular parent worlds
with continuous whole-gain interpolation and responses. The
polynomial identity $R=0$ passes to the singular limit. This reuses
all-world necessity, not a converse resultant test. Singular sources,
sampled zeros, lower-degree and repeated-root gains, zero drift,
specialized degrees and unused companions enter (12.9) before the
nonvanishing bounds below.

## 13. All eighteen roots and the uniform entire-child M gap

For each row below let $c_i=u_i+\mathrm i w_i$, $\rho=10^{-20}$ and

$$
\mathcal Q_i=\{z:|\Re z-u_i|\le\rho,\ |\Im z-w_i|\le\rho\}.
\tag{13.1}
$$

The table gives all exact centers and fixed nonzero preconditioners
$\gamma_i=\gamma_{i,R}+\mathrm i\gamma_{i,I}$ for
$z\mapsto z-\gamma_iR(z;p,v)$. These are finite rational data.

| $i$ | $u_i$ | $w_i$ | $\gamma_{i,R}$ | $\gamma_{i,I}$ |
| --- | --- | --- | --- | --- |
| 0 | $\frac{-1674980116533792451987440132631898202894043969833888796935355889616351}{10^{69}}$ | $0$ | $\frac{20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{193467607294322285886885074342873196006543064569131802212140061230361932830527413592046045909912197453632664389733856862119}$ | $0$ |
| 1 | $\frac{-1532480509951015084539590946320930338531248575311112160262318230990753}{10^{69}}$ | $0$ | $\frac{-20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{615309457106885128863796800778534164582392944166207595658721913402668186233251700451425470577265176137783905029620842939}$ | $0$ |
| 2 | $\frac{-1529152698029606291817699900815665937749990817880624624221683235874183}{10^{69}}$ | $0$ | $\frac{1000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{29810762319570271463908926639698414593432660434091509125993075509011329262307805331289071077921968891767888695957425729}$ | $0$ |
| 3 | $\frac{-1330553510252441170421512125338117267142373804575206202542412725116797}{10^{69}}$ | $0$ | $\frac{-10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{1887026814515927617804228888517256992502147094976711083023996654776516574156937437383820879182061628951973762930110774161}$ | $0$ |
| 4 | $\frac{-1243050725901622950709345985765718701184361471565410461069221200887468}{10^{69}}$ | $0$ | $\frac{2500000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{271252184178022164032269590172084027792424259062827586084483452909021489785675942827992558010030810064211569037609283709}$ | $0$ |
| 5 | $\frac{-1192787486826273907026978687227809831770410770321036375795471126397086}{10^{69}}$ | $0$ | $\frac{-5000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{977417906749166619812213348599082161614414032417076819962818208135904389064279000335022135782604847319065603536255328929}$ | $0$ |
| 6 | $\frac{-3701944638994143236214389040130619269633005326796689780658411776720153}{10^{70}}$ | $0$ | $\frac{10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{47852395422702302952428335347063793829416742279964915248229229443101812771956418726126651581929031794430979240716187653469}$ | $0$ |
| 7 | $\frac{3377471171711428118798584524298030194156407749075116993020719726941311}{10^{70}}$ | $0$ | $\frac{-1250000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{104181991909180212334071572593177973808378714681906283546965276835287791523633155423920812951925981396352494005640313551}$ | $0$ |
| 8 | $\frac{5465222330920732209478350400921313345377928802520609428964190146106766}{10^{70}}$ | $0$ | $\frac{2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{16620706668464074155492446364856582958255997535034045751374335173074539637994105463655389894159220921328880551930510723}$ | $0$ |
| 9 | $\frac{6805696568501061794503306769779346643873209222832295093737786964586342}{10^{70}}$ | $\frac{-9426366105413476038724843015250395563659151721407318532460957065393859}{10^{71}}$ | $\frac{-226346014655765251068033757620884542598334070846932950792853993705736808914096729071903584459482391467778554386610272000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{29602798677893370617128598538545519497445372218948513014817086840034319052530727627093093051577007653147009737403673307160199193419733720224020011143824967016096842020820994610797591427010061137431166486930440694109151733623525410726257}$ | $\frac{3993780199323785209358654169655157041623150143335663503672023082850492058277865661360254309358476725904729520854730606000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{29602798677893370617128598538545519497445372218948513014817086840034319052530727627093093051577007653147009737403673307160199193419733720224020011143824967016096842020820994610797591427010061137431166486930440694109151733623525410726257}$ |
| 10 | $\frac{6805696568501061794503306769779346643873209222832295093737786964586342}{10^{70}}$ | $\frac{9426366105413476038724843015250395563659151721407318532460957065393859}{10^{71}}$ | $\frac{-226346014655765251068033757620884542598334070846932950792853993705736808914096729071903584459482391467778554386610272000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{29602798677893370617128598538545519497445372218948513014817086840034319052530727627093093051577007653147009737403673307160199193419733720224020011143824967016096842020820994610797591427010061137431166486930440694109151733623525410726257}$ | $\frac{-3993780199323785209358654169655157041623150143335663503672023082850492058277865661360254309358476725904729520854730606000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{29602798677893370617128598538545519497445372218948513014817086840034319052530727627093093051577007653147009737403673307160199193419733720224020011143824967016096842020820994610797591427010061137431166486930440694109151733623525410726257}$ |
| 11 | $\frac{9597760030318847739404564762986359735147237348074533152928125412263423}{10^{70}}$ | $0$ | $\frac{-2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{2902234615256389674825723890703588572512821391913580056105393042414425666900096286634516305982927733376201490639896639}$ | $0$ |
| 12 | $\frac{1017074325399700763419912380015379363022684507227251208399369811825529}{10^{69}}$ | $0$ | $\frac{20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{17678271564057753044056047066731694530430198575982956027729727472469918831195019226207449517180616822170365983196165889}$ | $0$ |
| 13 | $\frac{1066779998986559072448501960952991981961420411025737330246461050064693}{10^{69}}$ | $0$ | $\frac{-4000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{6690073991452022430059493453851370883228771500888634221199330782202931856648234301483399811281393323730572362188696633}$ | $0$ |
| 14 | $\frac{1150238036587101873365132685965161555855080431674371541026267645250505}{10^{69}}$ | $0$ | $\frac{20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{320005284495622882578312916430570715797366634129021406116764024544626054134274795898356043174658032333836032568969513439}$ | $0$ |
| 15 | $\frac{2000689834749820553291033461304454408615608738144412349007251700824657}{10^{69}}$ | $0$ | $\frac{-20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{3564327682433838281095078468981122421880064499671315427326926341466990121663306652911568891457751103240183238177474743962171}$ | $0$ |
| 16 | $\frac{2078066396938050138753465565477942254625742570586120652929170363920933}{10^{69}}$ | $0$ | $\frac{10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{3522675104272643647263336865665276398297226751349150091651806620750618965404737246346350178930693458240642954599651146926023}$ | $0$ |
| 17 | $\frac{9640741162555142973925614937206280796513310762761193691136198644754174}{10^{69}}$ | $0$ | $\frac{-20000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000}{18258895907268044438119511573908549292508566174571476656687258542495357160778668332924265899437824626550548509941077807965608976185079387}$ | $0$ |

**Proposition 13.1 (Uniform exhaustive simple root cover).** For
every real base in $\mathcal B$ the eighteen disjoint boxes contain
exactly one root each and exhaust all roots with multiplicity.
Labels $0,\ldots,6$ are negative real, $9,10$ are nonreal, and
precisely $7,8,11,12,13,14,15,16,17$ are positive real.

Proof. Section 11's rational rule, applied to (12.4)–(12.5) and the
literal table, gives uniformly on every listed box and all $\mathcal B$

$$
\begin{gathered}
\eta_i:=\|\gamma_iR(c_i;p,v)\|_\infty<10^{-24},\\
q_i:=\sup|\Re(1-\gamma_iR_x)|
+\sup|\Im(1-\gamma_iR_x)|<10^{-8}.
\end{gathered}
\tag{13.2}
$$

The real $2\times2$ derivative has row-sum norm bounded by $q_i$.
Since $\eta_i+q_i\rho<\rho$, each is a self-map and strict
contraction for each fixed base. The leading and constant
coefficients are units throughout $\mathcal B$, with the following
exact uniform enclosures:

| Coefficient | Enclosure |
| --- | --- |
| $[x^{18}]R$ | $[\frac{-233365484215914889761319312526642595262848183579120807688925128709663275563413030169646688783418529923873357164255839135}{10^{100}},\frac{-233365484215914889761319312526642591222552921896891561463449864989738432406212771663140619924446995473115344640460757286}{10^{100}}]$ |
| $[x^0]R$ | $[\frac{2798584262059794233174571427534223342406993557583249952035775615319908859882477526370899738370795336861653398401220809506}{10^{100}},\frac{2798584262059794233174571427534223742912596315300368337657237180621557485838333026936829794780976176285521545943770299188}{10^{100}}]$ |

There are eighteen distinct roots of an exactly degree-eighteen
polynomial. The fundamental theorem of algebra with multiplicities
leaves no additional or repeated root. At each root (13.2) also gives
$R_x\ne0$. Conjugation and uniqueness make the real-centered roots
real; the other two boxes miss the real axis. Endpoint signs give
the stated negative and positive lists. ∎

At all nine positive boxes, uniformly over $\mathcal B$, the exact
forced reconstruction has the unit bounds

$$
|\alpha|>10^{15},\qquad |H_1|>1/4,\qquad \chi_0>7.
\tag{13.3}
$$

Thus an actual world must have $d=-\zeta/\alpha$ and the single
source, whole gain and responses in (12.1)–(12.3). Division is made
only after these nonvanishing bounds. The complete positive-root filter is
below; all intervals are closed and uniform on $\mathcal B$. The
last column identifies an original strict guard that fails, or keeps
the location as a necessary candidate without asserting existence.

| Label | Forced $d$ | Forced $b$ | Forced $r$ | Forced $m$ | Status |
| --- | --- | --- | --- | --- | --- |
| 7 | $[\frac{17689728}{10^{6}},\frac{17689729}{10^{6}}]$ | $[\frac{3335008}{10^{6}},\frac{3335009}{10^{6}}]$ | $[\frac{484723}{10^{5}},\frac{4847231}{10^{6}}]$ | $[\frac{480121768}{10^{6}},\frac{480121769}{10^{6}}]$ | Reject: violates $r<1$ |
| 8 | $[\frac{-875828}{10^{6}},\frac{-875827}{10^{6}}]$ | $[\frac{-13126141}{10^{6}},\frac{-1312614}{10^{5}}]$ | $[\frac{-780704}{10^{6}},\frac{-780703}{10^{6}}]$ | $[\frac{476186188}{10^{6}},\frac{476186189}{10^{6}}]$ | Reject: violates $b>0$ |
| 11 | $[\frac{39514627}{10^{6}},\frac{39514628}{10^{6}}]$ | $[\frac{11189}{10^{5}},\frac{111891}{10^{6}}]$ | $[\frac{119856}{10^{6}},\frac{119857}{10^{6}}]$ | $[\frac{415244008}{10^{6}},\frac{415244009}{10^{6}}]$ | Possible location; all guards required |
| 12 | $[\frac{35225287}{10^{6}},\frac{35225288}{10^{6}}]$ | $[\frac{323668}{10^{6}},\frac{323669}{10^{6}}]$ | $[\frac{683998}{10^{6}},\frac{683999}{10^{6}}]$ | $[\frac{426241555}{10^{6}},\frac{426241556}{10^{6}}]$ | Possible location; all guards required |
| 13 | $[\frac{37561958}{10^{6}},\frac{37561959}{10^{6}}]$ | $[\frac{-421753}{10^{6}},\frac{-421752}{10^{6}}]$ | $[\frac{865212}{10^{6}},\frac{865213}{10^{6}}]$ | $[\frac{401676516}{10^{6}},\frac{401676517}{10^{6}}]$ | Reject: violates $b>0$ |
| 14 | $[\frac{3537385}{10^{5}},\frac{35373851}{10^{6}}]$ | $[\frac{-566737}{10^{6}},\frac{-566736}{10^{6}}]$ | $[\frac{-313568}{10^{6}},\frac{-313567}{10^{6}}]$ | $[\frac{400523021}{10^{6}},\frac{400523022}{10^{6}}]$ | Reject: violates $b>0$ |
| 15 | $[\frac{24815713}{10^{6}},\frac{24815714}{10^{6}}]$ | $[\frac{2404}{10^{5}},\frac{24041}{10^{6}}]$ | $[\frac{972815}{10^{6}},\frac{972816}{10^{6}}]$ | $[\frac{434727993}{10^{6}},\frac{434727994}{10^{6}}]$ | Possible location; all guards required |
| 16 | $[\frac{24578275}{10^{6}},\frac{24578276}{10^{6}}]$ | $[\frac{-1}{10^{6}},\frac{1}{10^{6}}]$ | $[\frac{-1}{10^{6}},\frac{1}{10^{6}}]$ | $[\frac{434780144}{10^{6}},\frac{434780145}{10^{6}}]$ | Possible location; all guards required |
| 17 | $[\frac{19658967}{10^{6}},\frac{19658968}{10^{6}}]$ | $[\frac{-420468}{10^{6}},\frac{-420467}{10^{6}}]$ | $[\frac{1241367}{10^{6}},\frac{1241368}{10^{6}}]$ | $[\frac{446841701}{10^{6}},\frac{446841702}{10^{6}}]$ | Reject: violates $b>0$ |

These nine rows and their unit checks account for every positive-root
possibility, including the root close to the B0 face. The other nine
roots fail $x>0$. Only $11,12,15,16$ can support actual worlds over
$\mathcal B$, with at most one world per label. No assertion that
all four locations lift at an arbitrary base is used.

**Theorem 13.2 (Explicit uniform entire-child exclusion).** For every
$(p,v)\in\mathcal B$ and distinct actual complete worlds
$W,W'\in C(p,v)$,

$$
|m(W)-m(W')|\ge\frac{1043}{20000}>\frac1{20}.
\tag{13.4}
$$

Consequently $D_M\cap\mathcal B=\varnothing$, and no original joint
configuration has a base in this rectangle.

Proof. Every actual companion lies on a carrier root by (12.9).
The drift is unique by (13.3), and the faithful inverse gives at
most one world at each root. The five rejected positive rows fail
strictness. The four remaining $M$ intervals are disjoint, in the
increasing order $11,12,15,16$. Their smallest adjacent endpoint gap is

$$
\frac{27173759}{62500}-\frac{217363997}{500000}
=\frac{1043}{20000}.
$$

Distinct worlds must have different labels, proving (13.4).
The argument applies to the entire child, with all unused companions,
independently of any chosen $J$ endpoints. ∎

## 14. Three constructed worlds and exact rejection of the face root

For labels $i=11,12,15$ use the following source centers
$s_i=(r_i^c,b_i^c)$, cubes
$X_i=s_i+[-10^{-40},10^{-40}]^2$, and common parameter interval
$T_*=[c_t-10^{-55},c_t+10^{-55}]$.

| Label | $r_i^c$ | $b_i^c$ |
| --- | --- | --- |
| 11 | $\frac{1198566537020403586474854060714996620255859287540785390526009611799258745685084057717}{10^{85}}$ | $\frac{1118902357658860262418344034804907519442473738125956460721648103774555963546702225237}{10^{85}}$ |
| 12 | $\frac{6839987808415602085544486168294504427433530862137145307108233926958989013053031706478}{10^{85}}$ | $\frac{3236681328082721435705581821917147109285827287194319168962014398254007769255400696932}{10^{85}}$ |
| 15 | $\frac{9728156841474466323424500642523815847102343759829374872197794003486470100222785107682}{10^{85}}$ | $\frac{2404057337749434335260554928210203367802413829117825492501640315641652763355981719665}{10^{86}}$ |

The following exact matrices have rows $(r,b)$ and columns
$(E_p,E_v)$, the **unprimitive** pair in (10.4):

$$
Y_{11}=\begin{pmatrix}
\frac{-125367330951557649057425822524940348133684256936789430798043776429785195937847944006874}{10^{85}} & \frac{60409054291662253675603566858979517073306796751714888411646080911278372652982892467493}{10^{85}}\\
\frac{-111111551200059377087950837931456956470494316841150418178425791495501660777259311903721}{10^{85}} & \frac{5343877673821574604397569952897842744840049792590721407024723380004549945173599645835}{10^{84}}
\end{pmatrix}.
$$

$$
Y_{12}=\begin{pmatrix}
\frac{-557810389378121643902053604943246059250587440383658757569220070867010371200961441236}{10^{85}} & \frac{147550928775680184202533099688122938274527562681530570215960113068597991376582003842}{10^{85}}\\
\frac{223988787732041915570046350316257701344864704859253450897448513041347805154652358705}{10^{85}} & \frac{-6214670200592453499751578843566976694913154941666615230043501253595210681381442016}{10^{84}}
\end{pmatrix}.
$$

$$
Y_{15}=\begin{pmatrix}
\frac{-38401473303908941455439541838953532719814552665379108760975699579885690082499489275618}{10^{85}} & \frac{2160095025508721404899961971303037387673581268025962152603516563944918317833263249494}{10^{85}}\\
\frac{44613878853077829858807470602632609974974327303727529783734751041739267879119519315424}{10^{85}} & \frac{-5135614762804676431499587214211430373313405240618275260568317195656356579087660586003}{10^{85}}
\end{pmatrix}.
$$

For every $t\in T_*$ the maps

$$
\mathcal T_{i,t}(s)=s-Y_i(E_p,E_v)(s,t)
\tag{14.1}
$$

have the uniform bounds

$$
\|Y_i(E_p,E_v)(s_i,t)\|_\infty<10^{-48},\qquad
\sup_{X_i}\|I-Y_iD_s(E_p,E_v)\|_\infty<10^{-30}.
\tag{14.2}
$$

Equivalently one may use the primitive pair $(F_p,F_v)$ with
$15Y_i$. The primitive pair with unscaled $Y_i$ is not the
pairing in (14.2).

Since $10^{-48}+10^{-30}10^{-40}<10^{-40}$, these are self-maps
and strict contractions. The matrices are nonsingular by their
derivative defects. They give unique zeros $s_i(t)\in X_i$ of
the source equations. Each cube lies in $0<r<1,b>0,D\ne0$.
For each $t$, the original full-parent converse (10.2) gives a
complete world with exact acquired base $(p_B(t),v_B(t))$.
This establishes actual worlds independently of a resultant lift.

The following are outward enclosures on the source cubes. The
resulting $x=n/U$ lies strictly in the indicated carrier box.

| Label | $D$ enclosure | $d$ enclosure | Carrier box | Terminal $J$ | Terminal $M$ |
| --- | --- | --- | --- | --- | --- |
| 11 | $[\frac{643}{10^{4}},\frac{64301}{10^{6}}]$ | $[\frac{39514627}{10^{6}},\frac{39514628}{10^{6}}]$ | 11 | $[\frac{270471868}{10^{6}},\frac{270471869}{10^{6}}]$ | $[\frac{415244008}{10^{6}},\frac{415244009}{10^{6}}]$ |
| 12 | $[\frac{-2553076}{10^{6}},\frac{-2553075}{10^{6}}]$ | $[\frac{35225287}{10^{6}},\frac{35225288}{10^{6}}]$ | 12 | $[\frac{320136696}{10^{6}},\frac{320136697}{10^{6}}]$ | $[\frac{426241555}{10^{6}},\frac{426241556}{10^{6}}]$ |
| 15 | $[\frac{14844512}{10^{6}},\frac{14844513}{10^{6}}]$ | $[\frac{24815713}{10^{6}},\frac{24815714}{10^{6}}]$ | 15 | $[\frac{424976172}{10^{6}},\frac{424976173}{10^{6}}]$ | $[\frac{434727993}{10^{6}},\frac{434727994}{10^{6}}]$ |

For an additional check on the entire gain, the eight sample
enclosures below all belong to the same polynomial in each column.
They are consequences of (10.2), not free clock parameters or
additional gain assumptions.

| Clock | $g_{11}(k)$ | $g_{12}(k)$ | $g_{15}(k)$ |
| --- | --- | --- | --- |
| 0 | $[\frac{-39514628}{10^{6}},\frac{-39514627}{10^{6}}]$ | $[\frac{-35225288}{10^{6}},\frac{-35225287}{10^{6}}]$ | $[\frac{-24815714}{10^{6}},\frac{-24815713}{10^{6}}]$ |
| 1 | $[\frac{-14710013}{10^{6}},\frac{-14710012}{10^{6}}]$ | $[\frac{-11321924}{10^{6}},\frac{-11321923}{10^{6}}]$ | $[\frac{-725679}{10^{6}},\frac{-725678}{10^{6}}]$ |
| 2 | $[\frac{-9096787}{10^{6}},\frac{-9096786}{10^{6}}]$ | $[\frac{-4400867}{10^{6}},\frac{-4400866}{10^{6}}]$ | $[\frac{4476665}{10^{6}},\frac{4476666}{10^{6}}]$ |
| 3 | $[\frac{-1320894}{10^{5}},\frac{-13208939}{10^{6}}]$ | $[\frac{-6699811}{10^{6}},\frac{-669981}{10^{5}}]$ | $[\frac{-389012}{10^{6}},\frac{-389011}{10^{6}}]$ |
| 4 | $[\frac{-17580464}{10^{6}},\frac{-17580463}{10^{6}}]$ | $[\frac{-10456449}{10^{6}},\frac{-10456448}{10^{6}}]$ | $[\frac{-650304}{10^{5}},\frac{-6503039}{10^{6}}]$ |
| 5 | $[\frac{-12745349}{10^{6}},\frac{-12745348}{10^{6}}]$ | $[\frac{-7908477}{10^{6}},\frac{-7908476}{10^{6}}]$ | $[\frac{-5045748}{10^{6}},\frac{-5045747}{10^{6}}]$ |
| 6 | $[\frac{10762415}{10^{6}},\frac{10762416}{10^{6}}]$ | $[\frac{8706413}{10^{6}},\frac{8706414}{10^{6}}]$ | $[\frac{12802533}{10^{6}},\frac{12802534}{10^{6}}]$ |
| 7 | $[\frac{62408835}{10^{6}},\frac{62408836}{10^{6}}]$ | $[\frac{47150524}{10^{6}},\frac{47150525}{10^{6}}]$ | $[\frac{55861474}{10^{6}},\frac{55861475}{10^{6}}]$ |

The B0 root is rejected separately, by exact identities. Substitution
in (12.4)–(12.8) gives, as rational identities in $t$ away from their
displayed denominators,

$$
\begin{gathered}
R(t,p_B(t),v_B(t))=0,\\
\alpha(t,p_B(t),v_B(t))d_B(t)+\zeta(t,p_B(t),v_B(t))=0.
\end{gathered}
\tag{14.3}
$$

The exact $t_*$ is strictly inside box $16$, so the unique root there
at $y_*$ is exactly $x=t_*$. The nonzero $\alpha$ forces exactly
$d=d_B(t_*)$. Substituting $(x,d,p,v)=(t,d_B,p_B,v_B)$ in the
late interpolation gives

$$
H_0=-d_B,\qquad H_2=147/5-d_B,\qquad tH_1=24-d_B.
\tag{14.4}
$$

Hence $\beta_0=H_2$ and the forced inverse gives
$U=1,b=0,j=t,r=0$. Its denominators are units by (13.3), but it
fails the strict guards exactly. No sign decision is made from an
interval containing zero. The entry $c=t$ refers only to the
auxiliary matrix (10.3); $r(1-r)/b$ is not evaluated at $b=0$.

**Theorem 14.1 (Exact entire-child inventory).** At $t=t_*$ let
$W_i$ be the whole world given by $s_i(t_*)$ and (10.2). Then

$$
C(p_*,v_*)=\{W_{11},W_{12},W_{15}\}.
\tag{14.5}
$$

All three worlds are actual and strict. Their displayed terminal
$J$ intervals are pairwise disjoint, as are their $M$ intervals.
The strict mixed-$J$ mate at $(r_*,b_*)$ is exactly $W_{12}$.
Its equal-response B0 partner is auxiliary and is not in the child.

Proof. The three contractions construct actual worlds with the exact
same acquired base. Their distinct carrier boxes make them distinct.
The all-world filter leaves only $11,12,15,16$, at most one world
per root, and (14.3)–(14.4) reject $16$. This exhausts the child.
The target source lies in $X_{12}$ and solves the unprimitive pair,
so uniqueness there identifies its whole world with $W_{12}$.
The two sets of terminal intervals give injectivity. This inventory
is at the single exact target; the neighborhood theorem is only
the uniform $M$ assertion, without constant cardinality. ∎

## 15. Actual J-collision continuation and relative nonclosedness

Use the analytic chart

$$
r_A=tz,\quad b_A=z,\quad c_A=t(1-tz),\quad
j_A=t+z(1-t^2),\quad n_A=j_A+tz.
\tag{15.1}
$$

Substitute these polynomial $j_A,n_A$ into (10.1)–(10.2) to define
$\Psi_A(t,z)=(p_A,v_A,a_A)$ analytically near $(t_*,0)$.
Its value at zero is $(p_B,v_B,a_B)(t)$. Set

$$
\begin{gathered}
\Psi_B(r,b)=(N_p,N_v,N_a)/D,\qquad w=(r_B,b_B,t),\\
G(w,z)=\Psi_B(r_B,b_B)-\Psi_A(t,z).
\end{gathered}
\tag{15.2}
$$

The exact target solves $G((r_*,b_*,t_*),0)=0$. Write
$J_*=D_wG$ and $h_*=-\partial_zG$ there. Below a pair $(l,u)$
means the closed rational interval $[l,u]/10^6$. These enclosures
are rounded outward from evaluation on the full target cube.

| Quantity | Column 1 | Column 2 | Column 3 |
| --- | --- | --- | --- |
| Row 1 of $J_*$ | (411984742,411984743) | (978148952,978148953) | (4541874,4541875) |
| Row 2 of $J_*$ | (1484873052,1484873053) | (3697853021,3697853022) | (-14016251,-14016250) |
| Row 3 of $J_*$ | (3599524146,3599524147) | (8784271411,8784271412) | (-115716251,-115716250) |
| $h_*$ | (145780327,145780328) | (471860159,471860160) | (1162490523,1162490524) |
| $w\prime(0)$ | (950502,950503) | (-252827,-252826) | (328096,328097) |

For the determinant and Cramer quotients use the original interval
circuits on $X_*$ before rounding the entries to this coarse table.
They give

$$
\begin{gathered}
J_*w'(0)=h_*,\qquad
p'(0)=\partial_zp_A+\partial_tp_A\,t'(0),\\
-8056958<\det J_*<-8056957,\\
\frac{28858031}{200000}<p'(0)<\frac{36072539}{250000}.
\end{gathered}
\tag{15.3}
$$

In particular $144<p'(0)<145$. These are rational circuit
evaluations from the printed target and source data.

**Theorem 15.1 (Strict continuation and actual nonclosedness).** Put

$$
Y=\{(p,v)\in\mathbb R^2:p\ne24,\ C(p,v)\ne\varnothing\}.
\tag{15.4}
$$

There is an analytic $w(z)$ for all sufficiently small $|z|$ with
$w(0)=(r_*,b_*,t_*)$ and $G(w(z),z)=0$. For every sufficiently
small $z>0$, the source (15.1) and $(r_B(z),b_B(z))$ give two
distinct actual strict worlds with equal terminal $J$ in the same
$C(p(z),v(z))$. Their bases lie in $D_J\subset Y$ and tend to
$y_*\in Y\setminus D_J$. Thus $D_J$ is not relatively closed in $Y$.

Proof. Both rational charts are analytic at the target: the strict
source is regular and the auxiliary side has $t_*>1$. The nonzero
determinant in (15.3) permits the analytic implicit-function theorem.
For small positive $z$ one has $t(z)>0$, $0<t(z)z<1$ and
$b_A=z>0$, so (15.1) is an original strict source with
$c_A=r_A(1-r_A)/b_A$. Its $D$ stays nonzero. The other source
remains strict and regular near $(r_*,b_*)$. Shrinking the parameter
interval gives $b_A<1$, $b_B<1$, and
$b_A<b_*/2<b_B$, ensuring distinctness. The base remains off $24$.

Apply (10.2) to each source for each $z$. Every world has its own
single entire nonzero real gain of degree at most three and its own
fixed drift at every original clock. These may vary with the family
parameter, never with the clock within a world. Equation (15.2)
gives exact equality of $p,v,a$. These are actual equal-$J$ pairs,
separately established from the auxiliary tuple and root necessity.
Continuity gives their limiting base $y_*$, and (15.3) makes the
base arc nonconstant.

Theorem 14.1 puts $y_*$ in $Y$ and makes its entire child
$J$-injective. Therefore $y_*\notin D_J$. Any positive sequence
$z_n\to0$ supplies the required failure of relative closedness.
The endpoint $b_A=z_n\to0$ escapes the strict source domain at a
bounded base. Its limiting tuple is never counted as an actual pair. ∎

**Corollary 15.2 (All independent joint routes into this target are
excluded).** No sequence of original joint configurations can have
bases tending to $y_*$. In particular the actual $J$ pairs above
eventually lie in entire children with no distinct equal-$M$ pair.

Proof. The target is in the interior of $\mathcal B$, so any such
base sequence is eventually in $\mathcal B$. Theorem 13.2 excludes
an equal-$M$ pair anywhere in its entire child. This covers arbitrary
$M$ endpoints, unused companions, overlapping or disjoint pairs,
and independent common terminal values. ∎

## 16. Supplier scope, provenance and the remaining question

The global question is still precisely Definition 1.2: at one real
off-$24$ acquired base, find independently selected distinct equal-$J$
and equal-$M$ pairs in the same entire child, or exclude every such
configuration. No extra common terminal value, cross-pair restriction,
selected gain degree or positivity condition has been introduced.

SIII, Theorem 7.1 and Corollary 8.1, bound the
acquired bases and all complete companion coordinates over $D_J$.
SIII, Corollary 8.2, supplies separation from $p=24$ only on the
joint locus $D_J\cap D_M$, where it gives a compact ambient region.
They exclude unbounded fifth-response joint mechanisms
and unbounded companion coordinates. Their bounds give no individual
positive lower bound for every endpoint's $b,c$, do not make the
strict locus closed, and do not make the actual collision projection
compact. The finite-face arc above is consistent with those bounds.
The unresolved global remainder consists of actually undecided
finite boundary incidences and strict separated-pair incidences in
that bounded region, with all original exceptional and gain strata
retained. No unbounded joint regime is reintroduced as a global gap.

The evaluated target, its three-world inventory, the explicit
whole-child gap and the actual nonclosedness at this target are
source-specific content. The circuit, carrier, faithful inverse and
zero-safe identities are reused:

| Supplier | Exact role and limit |
| --- | --- |
| O, Definitions 1.1–1.3 and Theorem 2.1 | Original whole nonzero gain, fixed drift, acquired history, matrix products and full-parent necessity and converse. |
| F, Lemma 30.2 and Definition 31.1–Lemma 31.2 | Injective whole-world inverse with all guards and the fixed normalized carrier. A root alone supplies no actual world. |
| S, Theorem 4.1; SVII, Lemma 15.1 and Section 16 | All-world necessity through singular, zero-drift and $F_0=0$ strata, and the zero-safe drift identity. The normalization here uses $K=4k$. |
| SVII, Sections 14–20 | Existing carrier-root and whole-companion filtering on a different negative-base rectangle. Its rectangle is not transferred to this target. |
| SVII, Theorem 24.1 and Corollary 24.2 | Strict augmented-$J$ critical classification and immersion at nonnegative $p$. This local strict information does not prevent the separated strict/boundary escape above. |
| SIII, Sections 7–9 | Bounded global joint region and bounded complete companions, with no global closedness or individual endpoint margin. |

Fixed-node interpolation is the classical distinct-node formula; see
Berrut–Trefethen, *Barycentric Lagrange Interpolation*, §2,
[doi:10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715).
The Sylvester determinant is the classical elimination construction,
used in its stated necessary direction; see Basu, Pollack and Roy,
*Algorithms in Real Algebraic Geometry*, second edition, Chapter 8,
[doi:10.1007/3-540-33099-2](https://doi.org/10.1007/3-540-33099-2).
The self-map arguments use Banach's contraction theorem; see Lebl,
*Basic Analysis II*, [§8.5](https://www.jirka.org/ra/realanal2.pdf),
which also gives the $C^1$ implicit-function theorem (Theorem 8.5.6).
For the analytic regularity in Theorem 15.1, use Lebl,
*Tasty Bits of Several Complex Variables*, version 4.4,
[Theorem 1.3.8, p. 32](https://www.jirka.org/scv/scv.pdf),
the holomorphic implicit-function theorem.

To apply it, regard the parameter $z$ in (15.2) as complex and
$w=(r_B,b_B,t)$ as three complex variables. The strict chart has
$b_*>0$ and $D(r_*,b_*)\ne0$ by Proposition 11.1. On the auxiliary
chart (15.1), the substituted denominator $D$ at $z=0$ is
$20t(t-1)$, nonzero at $t=t_*>1$. The source quotient
$r_A(1-r_A)/b_A$ has already been replaced by the polynomial
$c_A=t(1-tz)$ before forming that chart. Both rational charts
therefore extend holomorphically to a complex neighborhood of the
target on which their denominators are nonzero. Their difference
$G$ has real coefficients, vanishes at the target, and has invertible
complex $w$-Jacobian there: its determinant is the same nonzero
real number enclosed in (15.3). The cited theorem supplies a unique
local holomorphic solution $w(z)$ through $(r_*,b_*,t_*)$.
After shrinking to conjugation-invariant neighborhoods, the real
coefficients and uniqueness give
$w(\overline z)=\overline{w(z)}$. Thus $w(z)$ is real for real
$z$, and its restriction is the real-analytic solution asserted in
Theorem 15.1.
These standard tools are not claimed as new.

The global existence-or-exclusion question outside this evaluated
neighborhood remains unresolved.

## 追加锚（本行以下为增补区）

## 17. The evaluated lower-face response and its necessary identities

The auxiliary B0 tuple of (10.3) will here be denoted by $B_s$, with
$s>0$. This changes only the parameter name. The result of Sections
17–20 is the following restricted exclusion:

**Theorem 17.1 (Empty lower-face/strict-unit-$j$ J incidence).** For
every finite auxiliary complete label $B_s$ satisfying the original
parent readings, and every actual strict complete parent world $W$
with $j(W)=1$, one has

$$
(p(B_s),v(B_s),a(B_s))\ne(p(W),v(W),a(W)).
\tag{17.1}
$$

The quantifier includes every $s>0$; at $s=1$ there is no such finite
complete label. The strict mate ranges over the entire unit-$j$ parent
layer, including any world unused by selected pairs. No $M$ collision
or off-$24$ hypothesis is needed for this theorem. In particular,
$p=24$, $d=0$, $d=24$ and endogenous gain-sample zeros are retained
whenever the original equations permit them. The label $B_s$ is never
an actual strict world.

For clarity, the unchanged interface used in the proof is recorded
explicitly. A strict source has $0<r<1$, $b>0$,
$c=r(1-r)/b$, $j=b+c$, $n=j+r$, $T=1+b$, $U=1+2b$.
Its single entire real gain has degree at most three, its fixed drift
is $d=24+e$, and its first four gain samples are

$$
(q_0,q_1,q_2,q_3)
=\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right).
\tag{17.2}
$$

The polynomial is exactly the interpolant in Lemma 1.3. The original
clock-four condition, before solving for any parameter, is

$$
\begin{gathered}
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,
\qquad
\eta=-\frac{6(8b-1)(5b+2)}{5TU},\\
g(4)-\frac{-6-e}{U}=e\Lambda-\eta=0.
\end{gathered}
\tag{17.3}
$$

The literal trace row is $(1,j,T,n,U,U+n,2U+n)$ at clocks
$0,\ldots,6$. At the original clock seven the alternative traces are
$T+2j+4r$ and $3U+2n$. Consequently

$$
\begin{aligned}
p&=24+e+(U+n)g(5),&
v&=24+e+(2U+n)g(6),\\
a&=24+e+(T+2j+4r)g(7),&
m&=24+e+(3U+2n)g(7).
\end{aligned}
\tag{17.4}
$$

These are the original unshifted clocks, actions and readings of
Section 1. The first two readings, $0$ and $24$, force the whole
interpolant to be nonzero. Equations (17.2)–(17.4) impose no condition
on a sample being nonzero, an exact gain degree or multiplicity of a
gain root, and do not divide by $e$ or $\Lambda$.

For the auxiliary matrix

$$
P_s=\begin{pmatrix}0&0\\s&1\end{pmatrix}
\tag{17.5}
$$

the same literal products have $j=n=s$ and $T=U=1$.
Thus the undivided parent (17.3) reads

$$
\frac{8e(s-1)}s-\frac{12}{5}=0.
\tag{17.6}
$$

At $s=1$ this is the contradiction $-12/5=0$, for every finite
proposed gain and drift. Only after this exclusion may one solve it.
For $s>0$, $s\ne1$, the unique finite auxiliary complete label has

$$
\begin{gathered}
e_s=\frac{3s}{10(s-1)},\qquad
d_s=\frac{3(81s-80)}{10(s-1)}
=\frac{243}{10}+\frac{3}{10(s-1)},\\
g_s(t)=\frac32t^3-\frac{141}{10}t^2+\frac{369}{10}t-d_s,\\
g_s(4)=-\frac{63}{10}-\frac{3}{10(s-1)},\qquad
g_s(5)=-\frac{24}{5}-\frac{3}{10(s-1)},\\
g_s(6)=\frac{27}{2}-\frac{3}{10(s-1)},\qquad
g_s(7)=\frac{288}{5}-\frac{3}{10(s-1)}.
\end{gathered}
\tag{17.7}
$$

Here $t$ is the gain's polynomial argument; $s$ is the source
parameter. Interpolation at $0,1,2,3$ gives exactly (17.7), rather
than separate gains for separate clocks. Its four responses are

$$
\begin{aligned}
p_s&=\frac{96}{5}-\frac{24s}{5}-\frac{3}{10(s-1)}
=-\frac{3(16s^2-80s+65)}{10(s-1)},\\
v_s&=51+\frac{27s}{2}-\frac{3}{5(s-1)}
=\frac{3(45s^2+125s-172)}{10(s-1)},\\
a_s&=\frac{813}{10}+\frac{576s}{5}-\frac{3}{5(s-1)}
=\frac{3(384s^2-113s-273)}{10(s-1)},\\
m_s&=\frac{3(384s^2+271s-659)}{10(s-1)}.
\end{aligned}
\tag{17.8}
$$

Direct multiplication gives three identities needed below:

$$
\begin{aligned}
10v_s-20p_s-126&=231s,\\
770a_s+6780p_s-4160v_s+19383&=0,\\
48s^2+(10p_s-240)s+195-10p_s&=0.
\end{aligned}
\tag{17.9}
$$

These are necessary equations for the evaluated boundary response,
not sufficient conditions for an actual source. The zero-drift label
$s=80/81$ is included. There is no $d_s=24$ label for $s>0$, since
$e_s\ne0$. Also

$$
10(s-1)(p_s-24)=3(15-16s^2),
\tag{17.10}
$$

so the positive $p_s=24$ label $s=\sqrt{15}/4$ is retained. These
boundary fractions are the existing B0 response, also given in SII,
Definition 12.1 and Lemma 12.2; the new assertion is (17.1).

## 18. Every actual strict unit-j mate, including singular guards

The condition $j=1$ gives $c=1-b>0$, so write $z=b$ with
$0<z<1$. The source equation factors as

$$
r(1-r)-z(1-z)=(r-z)(1-r-z)=0.
\tag{18.1}
$$

Thus there are exactly two source branches, $r=z$ and $r=1-z$.
Their intersection $z=1/2$ remains in both descriptions. The following
response polynomials use scalar symbols $P_i,V_i,A_i,R_i,Q_i$;
they are not the chronological product matrices. The convention is

$$
(p,v,a,m)=(P_i,V_i,A_i,R_i)/Q_i.
\tag{18.2}
$$

**Branch 3: $r=z$.** Here $c=1-z$, $n=T=1+z$, $U=1+2z$,
and (17.3) gives

$$
\begin{gathered}
\Lambda=-\frac{2z(2+3z)}{(1+z)(1+2z)},\qquad
\eta=-\frac{6(8z-1)(5z+2)}{5(1+z)(1+2z)},\\
-10ez(2+3z)+6(8z-1)(5z+2)=0,\\
e=\frac{3(8z-1)(5z+2)}{5z(2+3z)},\qquad
Q_3=5z(2+3z)(1+z)>0.
\end{gathered}
\tag{18.3}
$$

The undivided equation precedes the expression for $e$; its multiplier
is $5(1+z)(1+2z)>0$, and $\Lambda$ has no zero on this branch.
Substitute (18.3) into the single interpolant (17.2) and then use
the original responses (17.4). The literal numerators are

$$
\begin{aligned}
P_3&=360z^4+1611z^3+1086z^2+111z+6,\\
V_3&=2400z^4+8805z^3+5349z^2+576z+12,\\
A_3&=6000z^4+21210z^3+13686z^2+1890z+12,\\
R_3&=9600z^4+33888z^3+22131z^2+2970z+24.
\end{aligned}
\tag{18.4}
$$

**Branch 4: $r=1-z$.** Now $c=1-z$, $n=2-z$, $T=1+z$,
$U=1+2z$. Put

$$
K=3z^3-12z^2-4z+2.
\tag{18.5}
$$

Before division, the same parent gives

$$
\begin{gathered}
\Lambda=\frac{2K}{(1+z)(1+2z)(2-z)},\qquad
\eta=-\frac{6(8z-1)(5z+2)}{5(1+z)(1+2z)},\\
10eK+6(8z-1)(5z+2)(2-z)=0.
\end{gathered}
\tag{18.6}
$$

The multiplier is $5(1+z)(1+2z)(2-z)>0$. If $K=0$, the last
equation forces $(8z-1)(5z+2)(2-z)=0$. Both $5z+2$ and $2-z$
are positive on the strict interval, so $z=1/8$. But

$$
K(1/8)=675/512\ne0.
\tag{18.7}
$$

Therefore no actual finite complete parent world has $K=0$ on this
branch. This excludes the singular parent itself, independently of
any proposed finite $e$; it is not a regularity assumption. We may
now write

$$
e=-\frac{3(8z-1)(5z+2)(2-z)}{5K},\qquad
Q_4=5K(1+z)\ne0.
\tag{18.8}
$$

No sign of $K$ is assumed. The original interpolation and traces give

$$
\begin{aligned}
P_4&=120z^5-543z^4-6057z^3-3732z^2+1698z+36,\\
V_4&=1440z^5-10749z^4-29562z^3-12723z^2+5214z+564,\\
A_4&=-3600z^5+38202z^4-41784z^3-73575z^2+13497z+3486,\\
R_4&=4800z^5-30216z^4-106653z^3-58392z^2+16731z+3486.
\end{aligned}
\tag{18.9}
$$

For both branches the construction reproduces all first five original
readings; it uses exactly one entire nonzero polynomial and one
fixed drift for each world. Conversely (18.1), the undivided parent
and fixed-node uniqueness show that every actual strict $j=1$
parent world appears in these formulas.

The potentially exceptional specializations are visible without
canceling any gain or drift factor:

$$
\begin{aligned}
P_3-24Q_3&=3(8z-1)(15z^3+54z^2+27z-2),\\
P_4-24Q_4&=3(z+1)(8z-1)(5z^3-42z^2-170z+68),\\
5z(2+3z)d_3&=3(160z^2+91z-2),\\
5Kd_4&=3(160z^3-549z^2-184z+84),
\end{aligned}
\tag{18.10}
$$

where $d_i=24+e_i$. At $z=1/8$, on either branch,

$$
e=0,\quad d=24,\quad p=24,\qquad
g(t)=\frac85(t-1)(t-3)(t-5).
\tag{18.11}
$$

Thus actual sampled zeros are explicitly present. The factor $8z-1$
is never canceled, and $d=0$ is not excluded by (18.10). No division
by a gain sample, its leading coefficient, a discriminant or a root
difference occurs. Every permitted lower-degree or repeated-root
specialization is therefore within the argument, without a demand
that any such specialization exist on a particular branch.

## 19. Necessary incidence equations and exact coprimality

Suppose an incidence in (17.1) existed. For its branch $i=3$ or $4$
define the integer polynomials

$$
\begin{gathered}
Y_i=10V_i-20P_i-126Q_i,\\
H_i=48Y_i^2+231(10P_i-240Q_i)Y_i
+231^2(195Q_i-10P_i)Q_i.
\end{gathered}
\tag{19.1}
$$

The first identity of (17.9) forces
$s=Y_i/(231Q_i)$. The precise clearing identity for the third is

$$
\begin{aligned}
&(231Q_i)^2\left[
48\left(\frac{Y_i}{231Q_i}\right)^2
+\left(\frac{10P_i}{Q_i}-240\right)\frac{Y_i}{231Q_i}
+195-\frac{10P_i}{Q_i}\right]=H_i.
\end{aligned}
\tag{19.2}
$$

It is valid on the actual branches, where $Q_i\ne0$. The plane in
(17.9) gives the exact factors

$$
\begin{aligned}
770A_3+6780P_3-4160V_3+19383Q_3&=-15zF_3,\\
F_3&=194880z^3+605585z^2+257731z-370,\\
770A_4+6780P_4-4160V_4+19383Q_4&=45F=45(z+1)F_4,\\
F&=-176640z^5+1572013z^4+1085901z^3-679526z^2+468z+17242,\\
F_4&=-176640z^4+1748653z^3-662752z^2-16774z+17242.
\end{aligned}
\tag{19.3}
$$

Since $z>0$, the only removed plane factors are $-15z$ and
$45(z+1)$. Every actual incidence must consequently satisfy either
$F_3=H_3=0$ or $F_4=H_4=0$. We remove no factor of $H_i$, $K$
or $8z-1$. These equations are used only in their necessary direction.

The complete integer expansions of (19.1) are

$$
\begin{aligned}
H_3={}&27518400000z^8+177518250000z^7+368996938425z^6\\
&+267730272000z^5+59654522925z^4-1077954750z^3\\
&+334970100z^2-415800z,\\
H_4={}&10238400000z^{10}-166796442000z^9+301746232125z^8\\
&+2996922767850z^7+4151231372025z^6+924829196400z^5\\
&-1094584387500z^4-279813538800z^3+109848546900z^2\\
&+3104870400z-233309700.
\end{aligned}
\tag{19.4}
$$

We now give small coefficient identities proving both coprimality
claims. Throughout the next calculations a bar means reduction of
the entire integer polynomial modulo $13$, before normalization.
Every equality in these calculations is in $\mathbb F_{13}[z]$.
Reducing the integer coefficients in (19.1) gives the useful rule

$$
\overline H_i=9\overline Y_i^{\,2}
+(9\overline P_i+5\overline Q_i)\overline Y_i
+\overline P_i\overline Q_i.
\tag{19.5}
$$

**Branch 3 calculation.** The full reductions and a monic
normalization are

$$
\begin{gathered}
\overline F_3=10z^3+6z^2+6z+7,\qquad
f_3=4\overline F_3=z^3+11z^2+11z+2,\\
\overline H_3=11z^6+9z^5+10z^4+11z^3+10z^2+5z,
\qquad k=z^2+3z+1.
\end{gathered}
\tag{19.6}
$$

For a direct check of the multiplication in (19.5), the remainders
modulo $f_3$ of $P_3,Q_3,Y_3$ are respectively

$$
7z^2+10z+11,\qquad3z^2+z+9,\qquad11z^2+6z+4.
\tag{19.7}
$$

Thus $9P_3+5Q_3$ has remainder $4z+1$. The small complete
division identities are

$$
\begin{aligned}
\overline H_3&=(11z^3+5z^2+3z+5)f_3+3k,\\
f_3&=(z+8)k+(12z+7),\\
k&=(12z+3)(12z+7)+6.
\end{aligned}
\tag{19.8}
$$

The last remainder is a nonzero constant, so
$\gcd(\overline F_3,\overline H_3)=1$.
Equivalently $12z+7$ has root $7$, and $k(7)=6\ne0$.

**Branch 4 calculation.** Here the full reductions are

$$
\begin{aligned}
\overline F_4&=4z^4+10z^3+z^2+9z+4,\\
\overline H_4&=10z^{10}+7z^9+11z^7+10z^6+5z^5
+7z^4+10z^3+z^2+8z.
\end{aligned}
\tag{19.9}
$$

For a short multiplication check retaining the original plane factor,
put

$$
\begin{gathered}
f_4=10\overline F_4=z^4+9z^3+10z^2+12z+1,\\
f=10\overline F=z^5+10z^4+6z^3+9z^2+1=(z+1)f_4,\\
L=5z^3+9z^2+6z+2,\qquad h=8L=z^3+7z^2+9z+3.
\end{gathered}
\tag{19.10}
$$

Modulo $f$, the remainders of $P_4,Q_4,Y_4$ are respectively

$$
\begin{aligned}
p_0&=12z^4+9z^3+11z^2+8z+7,\\
q_0&=2z^4+7z^3+11z^2+3z+10,\\
y_0&=10z^4+2z^3+4z^2+5z+6.
\end{aligned}
\tag{19.11}
$$

These lowercase symbols are local polynomial remainders, not gain
samples or an acquired base. Ordinary multiplication gives

$$
9y_0^2+(9p_0+5q_0)y_0+p_0q_0
=11z^8+12z^7+6z^6+7z^5+10z^4+3z^3+z^2+12z+6.
\tag{19.12}
$$

The corresponding small identities are

$$
\begin{aligned}
\overline H_4&=(10z^5+11z^4+12z^3+8z^2+6z)f+zL,\\
f&=(z^2+3z+2)h+4(z+1)(z+2),\\
h&=(z+4)(z+1)(z+2)+8(z+1).
\end{aligned}
\tag{19.13}
$$

Since $f(0)=1$, its gcd with $zL$ equals its gcd with $h$.
The last two identities give $\gcd(f,h)=z+1$:
$h(-1)=0$ whereas $h(-2)=5$. But $f_4(-1)=4\ne0$, so
$\gcd(f_4,\overline H_4)=1$. This conclusion can also be
reconstructed directly, without passing through $f$, from

$$
\begin{gathered}
u_3=3z^3+8z^2+7z+8,\quad u_2=11z^2+9z,\quad u_1=3z+8,\\
\overline H_4
=(10z^6+8z^5+10z^4+7z^3+z^2+6z+5)f_4+u_3,\\
f_4=(9z+5)u_3+u_2,\qquad
u_3=(5z+12)u_2+u_1,\\
u_2=(8z+12)u_1+8,\qquad u_1=(2z+1)8.
\end{gathered}
\tag{19.14}
$$

All normalization constants $4,10,8$ used above are units modulo
$13$. The coefficient and degree data relevant to lifting are

| Polynomial | Degree over $\mathbb Q$ | Integer content | Leading coefficient modulo $13$ | Reduced degree |
| --- | ---: | ---: | ---: | ---: |
| $F_3$ | 3 | 1 | 10 | 3 |
| $H_3$ | 8 | 675 | 0 | 6 |
| $F_4$ | 4 | 1 | 4 | 4 |
| $H_4$ | 10 | 675 | 10 | 10 |

In particular, the first $H$ really drops from degree eight to six;
its reduced leading coefficient is $11$. No preservation of its
degree is assumed.

**One-sided Gauss lifting.** If $F_i$ and $H_i$ had a nonconstant
common divisor over $\mathbb Q$, choose a primitive integer common
divisor $G$. Gauss lemma gives integer quotients
$F_i=GB$ and $H_i=GC$. Since

$$
13\nmid\operatorname{lc}(F_i)
=\operatorname{lc}(G)\operatorname{lc}(B),
\tag{19.15}
$$

the reduction of $G$ retains its positive degree and divides both
$\overline F_i$ and $\overline H_i$. This contradicts (19.8) or
(19.14). No condition on $\operatorname{lc}(H_i)$ is required.
Hence both gcds over $\mathbb Q$ are one. The Euclidean identity
over $\mathbb Q$ then also rules out a common complex root of
either necessary pair. This is only a statement about these two
explicit univariate pairs, not an elimination of a global complex
collision system.

There can therefore be no actual incidence in (17.1). This proves
Theorem 17.1, with all the branch and singular guards of Section 18.

## 20. Complete-coordinate limits and the unchanged joint remainder

For a polynomial of degree at most three, use its four coefficients
in the fixed basis $1,t,t^2,t^3$, padding with zeros. A complete
coordinate tuple consists of $(r,b,c,d)$ and those four coefficients.
The literal readouts are polynomial, hence continuous, in these
coordinates even at the auxiliary matrix (17.5). The expression
$r(1-r)/b$ is not evaluated at $b=0$.

**Corollary 20.1 (Guarded complete-limit exclusion).** There is no
sequence of actual distinct equal-$J$ pairs in common entire children
whose first endpoint converges in complete coordinates to a finite
tuple with source $(0,0,s)$, $s>0$, and whose second endpoint
converges in complete coordinates to an actual strict source with
$j=1$. This exclusion needs no $M$ condition.

Proof. The first five fixed readings pass to both limits. The
limiting gains cannot be zero polynomials, since then their readings
at clocks zero and one would both equal their drift, contradicting
$0\ne24$. Thus the strict-source limit is a complete parent world.
On the first side, (17.6) excludes $s=1$, and fixed-node uniqueness
identifies the entire limiting label with (17.7). Shared acquired
$p,v$ and equality of terminal $J$ also pass to the limits. This
is exactly the incidence excluded by Theorem 17.1. ∎

For the original joint problem retain, for each index $n$, the exact
independent-pair quantifiers

$$
\begin{gathered}
p_n\ne24,\qquad
W_{0n},W_{1n},W_{2n},W_{3n}\in C(p_n,v_n),\\
W_{0n}\ne W_{1n},\qquad W_{2n}\ne W_{3n},\\
a(W_{0n})=a(W_{1n}),\qquad m(W_{2n})=m(W_{3n}).
\end{gathered}
\tag{20.1}
$$

The pairs may overlap, and their two terminal common values are
independent and need not agree. Membership is in the entire child,
including unused companions.

**Corollary 20.2 (Source-only joint-limit consequence).** No sequence
of (20.1) can satisfy

$$
(r_{0n},b_{0n},c_{0n})\longrightarrow(0,0,s),\quad s>0,
\qquad
(r_{1n},b_{1n},c_{1n})\longrightarrow(r_*,b_*,c_*),
\tag{20.2}
$$

where the second limiting source is strict and $b_*+c_*=1$.
Here the starred coordinates are local limit variables, unrelated to
the evaluated target (10.5). Convergence of gain and drift need not
be initially specified.

Proof. SIII, Theorem 7.1 and Corollary 8.1, bound the bases and all
complete companion coordinates over $D_J$, including every world
unused by either selected pair. Apply these existing bounds to
(20.1), and take a simultaneous convergent complete-coordinate
subsequence of its four selected worlds. The assumed source limits
are unchanged. Corollary 20.1 now gives a contradiction. The
compact ambient region separated from $p=24$ is supplied for joint
bases by SIII, Corollary 8.2; the source-only argument needs only
the bounds of Corollary 8.1. Neither step changes the selected $M$
pair or imposes equality of its common value with the $J$ value. ∎

Theorem 17.1 permits the extra guard $j\ne1$ only for the strict
mate in this evaluated real lower-face incidence relation. Within
that guarded relation it can equivalently be recorded by an auxiliary
inverse equation $h(j-1)=1$. This gives no permission to saturate
an arbitrary complex closure or a global joint collision ideal.
It supplies no uniform positive lower bound for $|j-1|$, no collar
for all selected $J$ endpoints and no exclusion of mates at $j\ne1$.

The original global alternative is still Definition 1.2: construct
independently selected actual distinct $J$ and $M$ pairs at one real
off-$24$ base in the same entire child, or exclude every such
configuration. Sections 10–16 retain their evaluated target,
whole-child inventory and nonclosedness result. SIII, Sections 7–9,
retain their bounded-base and all-companion conclusions. The
unevaluated finite boundary and strict incidence questions in that
bounded region remain unresolved; there is no new infinity residual.

The original whole-world interpolation is reused from Lemma 1.3
and O, and the boundary response is reused from (10.3) and SII,
Definition 12.1 and Lemma 12.2. The source-specific addition is the
empty incidence (17.1), its exhaustive singular guards and exact
coprimality calculations, and the guarded consequences above.
Fixed-node interpolation, polynomial Euclidean division and Gauss
lemma are standard tools, not new claims. For interpolation see the
Berrut–Trefethen reference in Section 16; for Euclidean division and
Gauss lemma see Dummit and Foote, *Abstract Algebra*, third edition,
Chapter 9, §§9.2–9.3. The calculations here give all coefficients
needed for this subtheorem and do not depend on an external
classification or a separate computational artifact.

## 追加锚（本行以下为增补区）

## 21. Four complete worlds and a uniform M gap near p=20

Sections 21–27 use the complete-world definition and independent-pair
quantifiers of Section 1 without changing their domain. Every finite
terminating decimal in these sections denotes the exact rational given
by its decimal expansion. In particular set

$$
\begin{gathered}
v_c=117.098504601811652853143640342847009910281780880505313347322910056227344807162345328734117,\\
\epsilon=10^{-8},\qquad
B=\{(p,v)\in\mathbb R^2:|p-20|\le\epsilon,\ |v-v_c|\le\epsilon\}.
\end{gathered}
\tag{21.1}
$$

The symbol $B$ in these sections denotes this closed rectangle, distinct
from the lower-face rectangle $\mathcal B$ in (11.3). It has $p\ne24$
everywhere. The source matrix remains

$$
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0.
$$

Each world has one fixed real drift $d$ and one whole nonzero real
polynomial $g$ of degree at most three. The original acquired word is
$J,M,J,M,M,M$, its readings at clocks $0,\ldots,6$ are
$(0,24,147/5,24,18,p,v)$, and clock seven has the two alternatives of
Definition 1.2 on that same world. All singular sources, zero drift,
sampled gain zeros, lower degrees, repeated gain roots and unused
companions are included in the whole-child quantifier.

**Theorem 21.1 (Evaluated whole-child rectangle).** For every real
$(p,v)\in B$, the entire original child consists of exactly four distinct
complete worlds. Label them $W_{12},W_{15},W_{16},W_{17}$ by the carrier
disks in Section 23. For all distinct $i,j$ in this four-element set,

$$
|m(W_i)-m(W_j)|\ge\frac{382743}{10^6}>\frac13.
\tag{21.2}
$$

The rectangle also contains a base $(20,v_*)$ of the existing actual
$J$-pair arc of SIII, Theorem 16.4, with

$$
|v_*-v_c|<10^{-60}.
\tag{21.3}
$$

Nevertheless $D_M\cap B=\varnothing$ and
$(D_J\cap D_M)\cap B=\varnothing$. The $J$ and $M$ pairs in the latter
predicate may overlap, and their two common terminal values remain
independent.

The four-world inventory and the uniform original-$M$ separation are
the evaluated content here. Actual $J$ existence on the SIII arc is
reused. The proof supplies every positive carrier location, its original
source filter and its complete lift, before comparing all six terminal
pairs. It is an ordinary mathematical result; no Lean or kernel
verification is asserted.

## 22. Exact coefficient circuit and its original-world interpretation

For this rectangle reuse the coordinates of F, Lemma 30.2, and Section
12: $x=n/U$, $H=Ug$, with the original drift $d$ unchanged. At arbitrary
$x>0$ and real $d$ put

$$
\begin{gathered}
h_3=(24-d)/x,\quad h_4=18-d,\quad
h_5=(p-d)/(x+1),\quad h_6=(v-d)/(x+2),\\
H(s)=\sum_{i=3}^6h_i
\prod_{\substack{3\le l\le6\\l\ne i}}\frac{s-l}{i-l},\\
H_0=20h_3-45h_4+36h_5-10h_6,\\
H_1=10h_3-20h_4+15h_5-4h_6,\\
H_2=4h_3-6h_4+4h_5-h_6,\qquad
H_7=-h_3+4h_4-6h_5+4h_6,\\
B_0=294/5-2d-H_2.
\end{gathered}
\tag{22.1}
$$

These are four samples and four extrapolations of a single entire
polynomial. Distinct interpolation nodes suffice at every permitted
gain degree and every pattern of sample zeros.

**Definition 22.1 (Integer circuit, with fixed normalization).** In
$\mathbb Z[x,p,v,d]$ set

$$
\begin{gathered}
D=x(x+1)(x+2),\\
z_3=(24-d)(x+1)(x+2),\quad z_4=(18-d)D,\\
z_5=(p-d)x(x+2),\quad z_6=(v-d)x(x+1),\\
a_0=20z_3-45z_4+36z_5-10z_6,\\
a_1=10z_3-20z_4+15z_5-4z_6,\qquad
 a_2=4z_3-6z_4+4z_5-z_6,\\
z_*=xa_1-D(24-d),\\
f=5dDa_2+a_0\{(294-10d)D-5a_2\},\\
K=4a_0^2z_*^2+2a_0(dD-a_0)z_*a_1
 -(a_0+dD)\{dD+(1-2x)a_0\}a_1^2,\\
F_0=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480.
\end{gathered}
\tag{22.2}
$$

Here $a_i=DH_i$ for $i=0,1,2$. Write
$f=Ad^2+B_fd+C_f$ and $K=\sum_{i=0}^4k_id^i$, with coefficients
in $\mathbb Z[x,p,v]$. The symbols $A,B_f,C_f,k_i$ denote exactly
these coefficient extractions, not a primitive-part normalization. Put

$$
\begin{aligned}
\alpha={}&k_4(-B_f^3+2AB_fC_f)
 +k_3A(B_f^2-AC_f)-k_2A^2B_f+k_1A^3,\\
\zeta={}&k_4(-B_f^2C_f+AC_f^2)
 +k_3AB_fC_f-k_2A^2C_f+k_0A^3,\\
Q_2={}&k_4(A^2d^2-AB_fd+B_f^2-AC_f)
 +k_3A(Ad-B_f)+k_2A^2.
\end{aligned}
\tag{22.3}
$$

The exact polynomial identities and quotients specifying the carrier are

$$
\begin{gathered}
A^3K-(\alpha d+\zeta)=fQ_2,\\
E=\frac{A\zeta^2-B_f\alpha\zeta+C_f\alpha^2}{A^3},\qquad
R=\frac{E}{256D^8F_0^2},\\
A\zeta^2-B_f\alpha\zeta+C_f\alpha^2
 =A^3\,256D^8F_0^2R.
\end{gathered}
\tag{22.4}
$$

Both quotients in this display are exact in the polynomial ring; their
meaning does not involve division at an individual zero of $A,D$ or
$F_0$. They give $R\in\mathbb Z[x,p,v]$ with $512$ nonzero monomials
and coordinate degrees $(18,6,6)$. Thus (22.2)–(22.4), including the
coefficient extractions, specify every coefficient used below.

For the fixed six by six Sylvester matrix $\mathsf S$ with rows
$d^3f,d^2f,df,f,dK,K$ and descending columns $d^5,\ldots,1$,

$$
\operatorname{Res}_d(f,K)=\det\mathsf S
 =E=256D^8F_0^2R.
\tag{22.5}
$$

The determinant is retained at this fixed size under specialization.
This is precisely F31's carrier: the present $K=4k$ multiplies its last
two rows by four and its factor $16$ by sixteen. For a check on the
remaining scalar normalization,

$$
[x^0]R=10^6(32p-5v-366)^2
(120p^2-38pv-3360p+3v^2+522v+23112)^2.
\tag{22.6}
$$

A direct way to verify (22.4) is to reduce $d^2,d^3,d^4$ using the
quadratic $f$, multiplying through by $A^3$. Their remainders give
exactly (22.3); the quotient is the displayed $Q_2$. At generic $A\ne0$
the quadratic norm of $\alpha d+\zeta$ gives the numerator defining
$E$, with the factor $A^3$ in the denominator. Equivalently expansion
of the fixed determinant gives the same polynomial $E$. Exact
polynomial division then gives $R$ and (22.6). These identities are
identities before any specialization or cancellation of a source guard.

For smaller coefficient evaluations define the exact polynomial quotients

$$
\alpha_r=\frac{\alpha}{32D^3},\qquad
\zeta_r=\frac{\zeta}{32D^3}.
\tag{22.7}
$$

They have respectively $220$ and $315$ nonzero monomials; the
unreduced $\alpha,\zeta$ have $280$ and $405$. Only the displayed
constant and $D$ factors have been removed. In particular no
actual-world equation is divided by $F_0$.

**Lemma 22.2 (Reused necessity on the entire child).** Every original
complete world at every base in $B$ satisfies

$$
x>0,\qquad f=K=R=0,\qquad \alpha d+\zeta=0.
\tag{22.8}
$$

Proof. F, Lemma 30.2, gives the following necessary and sufficient
whole-world reconstruction guards at an off-$24$ base:

$$
\begin{gathered}
x>0,\quad d\ne24,\quad H_1\ne0,\quad d^2+B_0^2>0,\\
U=\frac{-dH_0+B_0H_2}{d^2+B_0^2}>1,\quad
b=(U-1)/2,\quad j=U(24-d)/H_1,\quad r=xU-j,\\
0<r<1,\quad j=b+r(1-r)/b,\quad
 dU=-H_0,\quad B_0U=H_2.
\end{gathered}
\tag{22.9}
$$

The corresponding whole gain is $g=H/U$. Its parameters are exactly
F30.2's $x=n/U,H=Ug,d=d$; the $B_0$ in (22.1) is its
$2(147/5-d)-H_2$. O, Theorem 2.2, gives the $d=24$ branch only at
$p=24$, so it has not been discarded from an off-$24$ child by
assumption. The pair $(d,B_0)$ cannot vanish: the last two equations
would give $H_2=0$ while its definition gives $H_2=294/5$.

SVII, Lemma 15.1, applies to exactly (22.2), with its $\mathscr D=D$
and $\mathscr R=R$. Its all-world necessity is also recorded in
(12.9). In particular

$$
f=5D^2(dH_2+H_0B_0).
\tag{22.10}
$$

At nonzero $d$, the rank-one relation in (22.9) gives $K=0$ by
(24.4) below. At $d=0$, the original clock-zero equation gives
$H_0=0$ and every term of $K$ vanishes without division by $d$.
The extension to actual $F_0=0$ and singular $\Lambda=0$ sources is
SVII15.1's polynomial-density and continuous-parent argument, explicitly
recalled in Section 12: a nonzero $F_0$ pullback on the regular source
chart is witnessed at $(r,b)=(1/2,1/4)$, and singular sources are
approached through the undivided parent using its nonzero $r$ derivative.
This establishes $R=0$ there without cancelling $F_0$ or $\Lambda$.
Finally the first polynomial identity in (22.4) gives
$\alpha d+\zeta=0$ even at a degree drop $A=0$.

These are necessity statements for every original world before any
local unit test. They retain all zero-sample, lower-degree,
repeated-root, drift-zero, singular and specialized-degree strata,
and every companion unused by either selected pair. ∎

## 23. Eighteen disjoint disks on the full closed rectangle

Here $c_i$ denotes a Gaussian-rational disk centre, unrelated to the
lower-left source entry $r(1-r)/b$. The following numbers are exact.

| i | Re c | Im c |
| --- | --- | --- |
| 0 | -111.51328221036275269813593036810076850320509016207 | 0 |
| 1 | -1.1906148889285123614541681173453120033434750921264 | 0 |
| 2 | -1.1337532491993255077133682034498355640757074404294 | 0 |
| 3 | -1.1290545072684844282021529658919344881321324068489 | 0 |
| 4 | -0.96554916203673813408738944211871833614590246690031 | 0 |
| 5 | -0.898685114642393189425679073906655182325530246967 | 0 |
| 6 | -0.8671051523429890662594563067223192183146386168557 | 0 |
| 7 | -0.33944688669671700668344219007757459083892196548762 | 0 |
| 8 | 0.34724093496614319098500208581190115961576958956363 | 0 |
| 9 | 0.59424515717182932944601397251980409438628914220184 | 0 |
| 10 | 0.67346562432234461370144692386304708472884126319468 | -0.082218136347753466217958051317227417193190996022994 |
| 11 | 0.67346562432234461370144692386304708472884126319468 | 0.082218136347753466217958051317227417193190996022994 |
| 12 | 0.92395558913390014419017551494504769238618866276621 | 0 |
| 13 | 0.95864756880894689716304503664017241738585678201911 | 0 |
| 14 | 1.0228441352219800410889104908130472473246259688377 | 0 |
| 15 | 1.0276514400336170498816930331077903081337497860047 | 0 |
| 16 | 1.69358189366958820461855751329778218736145239035 | 0 |
| 17 | 1.7186931428253876343395784977424180557139997102399 | 0 |

Use the respective positive rational radii $\rho_i$ below. For a
polynomial $P\in\mathbb Q[x,p,v]$, define its exact translated
coefficients by

$$
P(c_i+t,20+u,v_c+w)
 =\sum_{a,b,c\ge0}T_{abc}(P;c_i)t^au^bw^c.
\tag{23.1}
$$

This is a finite coefficient definition. More explicitly, if
$P=\sum P_{lmn}x^lp^mv^n$, then

$$
T_{abc}(P;c_i)=\sum_{l\ge a,m\ge b,n\ge c}
 P_{lmn}\binom la\binom mb\binom nc
 c_i^{l-a}20^{m-b}v_c^{n-c}.
\tag{23.2}
$$

For a Gaussian rational $z$ put
$\mathcal U(z)=|\Re z|+|\Im z|$ and
$\mathcal L(z)=\max(|\Re z|,|\Im z|)$.
They satisfy $\mathcal L(z)\le|z|\le\mathcal U(z)$.
For each row of the next table, direct rational evaluation gives
$\mathcal L(T_{100}(R;c_i))>0$ and

$$
\sum_{(a,b,c)\ne(1,0,0)}
 \mathcal U(T_{abc}(R;c_i))\rho_i^a\epsilon^{b+c}
 <q_i\,\mathcal L(T_{100}(R;c_i))\rho_i,
 \qquad q_i<\tfrac12.
\tag{23.3}
$$

The column $q_i$ gives an exact upper bound for the ratio in (23.3).
The sum includes the constant residual, every nonlinear $x$ term
and every parameter term over all of $B$.

| $i$ | $\rho_i$ | $q_i$ |
| --- | --- | --- |
| 0 | 2048/244140625 | 489100/10^6 |
| 1 | 1/976562500 | 427990/10^6 |
| 2 | 1/976562500 | 347739/10^6 |
| 3 | 1/976562500 | 347574/10^6 |
| 4 | 1/976562500 | 296010/10^6 |
| 5 | 1/976562500 | 271414/10^6 |
| 6 | 1/976562500 | 251992/10^6 |
| 7 | 1/3906250000 | 397081/10^6 |
| 8 | 1/62500000000 | 486012/10^6 |
| 9 | 1/3906250000 | 479826/10^6 |
| 10 | 1/7812500000 | 405154/10^6 |
| 11 | 1/7812500000 | 405154/10^6 |
| 12 | 1/15625000000 | 482538/10^6 |
| 13 | 1/976562500 | 251214/10^6 |
| 14 | 1/976562500 | 335283/10^6 |
| 15 | 1/488281250 | 325342/10^6 |
| 16 | 1/244140625 | 462784/10^6 |
| 17 | 1/244140625 | 437753/10^6 |

All evaluations in (23.3) can be performed using (22.2)–(22.7) and
(23.2) alone. A rational enclosure rule for these sums and the subsequent
tables is as follows. For $S=10^{100}$ replace a real interval $[l,u]$
by $[\lfloor Sl\rfloor/S,\lceil Su\rceil/S]$. Embed rational constants
this way; round outward after each sum, product and quotient. For a
product take all four endpoint products; for a reciprocal first exclude
zero and use $[1/u,1/l]$. Complex enclosures are pairs of real intervals
with the ordinary complex operations. Binomial translation of the
integer circuit encloses every $T_{abc}$. The inequalities themselves
are rational inequalities on the exact finite sums, independent of an
implementation of that enclosure rule.

**Proposition 23.1 (Exhaustive root inventory).** At every real base in
$B$, $R(\,\cdot\,,p,v)$ has exactly one root, counted with multiplicity, in
each open disk $|x-c_i|<\rho_i$ and no roots elsewhere. Indices
$0,\ldots,7$ give eight negative real roots; indices $10,11$ give two
nonreal roots; indices $8,9,12,13,14,15,16,17$ give eight positive real
roots. All eighteen roots are simple.

Proof. On the boundary of a listed disk, separate the linear term
$T_{100}(R;c_i)(x-c_i)$ from the rest of (23.1). By (23.3) the modulus
of the rest is strictly less than the modulus of this linear term.
Both are holomorphic on a neighborhood of the closed disk because they
are polynomials in $x$ after fixing the real base. Rouché's theorem
therefore gives exactly one zero with multiplicity inside.

The exact centres and radii satisfy, for every $i<j$,

$$
|c_i-c_j|^2>(\rho_i+\rho_j)^2.
\tag{23.4}
$$

For $i\le7$, $\Re c_i+\rho_i<0$; for the eight positive indices,
$c_i-\rho_i>0$; and for $i=10,11$,
$|\Im c_i|>\rho_i$. The real-centred disks are invariant under
conjugation. Since the specialization has real coefficients, uniqueness
makes their roots real. The other two disks miss the real axis.

A specialization has degree at most eighteen by (22.4). The eighteen
disjoint disks already account for eighteen roots with multiplicity, so
the degree is exactly eighteen and there are no further roots or
multiplicities. An identically zero specialization also contradicts
(23.3): the sum of the rest would then have boundary modulus equal to
the linear term. Thus neither a degree drop nor a zero polynomial
specialization leaves an omitted root stratum on $B$. ∎

## 24. Every positive source location, and four complete lifts

The root indices in this section have the local meaning fixed in
Section 23. At each of the eight positive roots first enclose the
polynomials $\alpha_r,\zeta_r,A,k_4$ by their translations (23.1).
For a real-centred disk and real parameters, a polynomial $P$ lies in

$$
T_{000}(P;c_i)+[-s_i(P),s_i(P)],\qquad
s_i(P)=\sum_{a+b+c>0}|T_{abc}(P;c_i)|
 \rho_i^a\epsilon^{b+c}.
\tag{24.1}
$$

Use $\alpha=32D^3\alpha_r$ for its unreduced value. The resulting
strict unit bounds are

| i | $\lvert\alpha\rvert>$ | $\lvert A\rvert>$ | $\lvert k_4\rvert>$ | $\lvert H_1\rvert>$ |
| --- | --- | --- | --- | --- |
| 8 | 10^15 | 10^3 | 10^5 | 10^1 |
| 9 | 10^14 | 10^2 | 10^2 | 10^1 |
| 12 | 10^17 | 10^3 | 10^6 | 10^1 |
| 13 | 10^17 | 10^3 | 10^6 | 10^0 |
| 14 | 10^16 | 10^3 | 10^7 | 10^1 |
| 15 | 10^17 | 10^3 | 10^7 | 10^0 |
| 16 | 10^27 | 10^5 | 10^10 | 10^-1 |
| 17 | 10^27 | 10^5 | 10^10 | 10^-1 |

After the $\alpha$ bound, put $d=-\zeta_r/\alpha_r$; the resulting
$d$ intervals below exclude both zero and $24$. Evaluate (22.1) and
then

$$
U=-H_0/d,\qquad b=(U-1)/2,\qquad
j=U(24-d)/H_1,\qquad r=xU-j.
\tag{24.2}
$$

The $H_1$ lower bounds in the preceding table are obtained at this
forced $d$. All divisions thus have nonzero denominators before use.
The $A,k_4$ bounds are local unit facts; no division by $k_4$ is needed.
The complete outward rational source enclosures are

| i | d | U | r | decision |
| --- | --- | --- | --- | --- |
| 8 | [20.16970797, 20.16970808] | [4.919893, 4.919895] | [3.11807, 3.118072] | r>1 |
| 9 | [0.00754263, 0.00754265] | [273.352856, 273.35366] | [35.001338, 35.002195] | r>1 |
| 12 | [33.51861545, 33.51861687] | [1.387317, 1.387322] | [0.215415, 0.215427] | actual |
| 13 | [36.19763147, 36.19765382] | [0.186005, 0.18606] | [0.86737, 0.86781] | U<1 |
| 14 | [34.46462405, 34.46494971] | [-0.160108, -0.159296] | [-0.325302, -0.323455] | U<1 |
| 15 | [29.47531508, 29.47537988] | [1.621929, 1.622122] | [0.744657, 0.745213] | actual |
| 16 | [24.29045413, 24.29046019] | [1.192654, 1.192673] | [0.887157, 0.887961] | actual |
| 17 | [24.21292303, 24.21292895] | [1.175494, 1.175513] | [0.187268, 0.189951] | actual |

The word “actual” in this table is justified by the complete lift below.
For indices $8,9$ the forced $r>1$ contradicts the original source.
For $13,14$ the forced $U<1$ contradicts $U=1+2b>1$.
The remaining four rows have $U>1$ and $0<r<1$ throughout their
whole certified ranges. No resultant root has been counted as an
actual world without these guards and the restored equations.

**Proposition 24.1 (Existence, uniqueness and all-world completeness).**
For each real base in $B$, every root in disks $12,15,16,17$ lifts to
one original strict complete world, and these are exactly the entire
child.

Proof. Fix one of the four retained roots and its forced drift. In
(22.4), $R=0$ and $\alpha\ne0$ give

$$
f(-\zeta/\alpha)
 =\frac{A\zeta^2-B_f\alpha\zeta+C_f\alpha^2}{\alpha^2}=0.
\tag{24.3}
$$

The first identity in (22.4) then gives $A^3K=0$. The local bound
$A\ne0$ yields $K=0$. This argument is valid even if $F_0=0$;
there is no cancellation of that factor at the root.

Equation (22.10), with $D>0$ and $d\ne0$, gives
$dU=-H_0$ and $B_0U=H_2$ for the $U$ in (24.2). Consequently
$d^2+B_0^2>0$ and

$$
\frac{-dH_0+B_0H_2}{d^2+B_0^2}=U.
$$

This identifies (24.2) with the zero-safe F30.2 reconstruction, not a
new choice of source. Put $Z=xH_1-(24-d)$, so that
$r=UZ/H_1$. Substitution of $H_0=-dU$, $b=(U-1)/2$ and $a_i=DH_i$
in (22.2) gives the exact identity

$$
K=4D^4d^2H_1^2
 \{r^2-(1+b)r+b(xU-b)\}.
\tag{24.4}
$$

Its prefactor is nonzero at this root, hence the last brace vanishes.
Since $j=xU-r$, it follows that

$$
bj=b^2+r-r^2,\qquad
j=b+r(1-r)/b.
$$

Here $b>0$ follows from the certified $U>1$. Thus every guard of
(22.9) holds. Set

$$
\begin{gathered}
c_{\rm src}=r(1-r)/b,\quad n=xU=j+r,\quad T=(U+1)/2,\\
W_i=(P(r,b),H/U,d).
\end{gathered}
\tag{24.5}
$$

The gains in (24.5) are whole polynomials, not independently chosen
sample values.
At clocks zero and two the restored equations give respectively
$d+H_0/U=0$ and

$$
d+\frac{U+1}{2U}H_2
 =d+\frac{H_2+B_0}{2}=147/5.
$$

Clock one gives $d+jH_1/U=24$. At clocks $3,4,5,6$, the trace row
$(n,U,U+n,2U+n)$ and (22.1) give $24,18,p,v$ exactly. These are all
original readings at their original unshifted clocks. The first two
readings differ, so the one polynomial $H/U$ is nonzero. It has degree
at most three; no sign, exact degree or root-multiplicity condition is
needed. This constructs four strict complete worlds.

Conversely take any original complete world, including any unused
companion or specialized stratum. Lemma 22.2 places its $x>0$ among
the eight positive roots in Proposition 23.1. The nonzero $\alpha$
there forces exactly the drift in (24.2), so its original source must
have the indicated forced coordinates by F30.2. Four rows violate
strictness and cannot contain it. At each remaining root F30.2's
injectivity gives at most one complete world, exactly the one in
(24.5). Distinct roots have different $x=n/U$, so the four worlds are
distinct. This proves the inventory for every base in the full closed
rectangle. ∎

## 25. The six original terminal-M comparisons

For every reconstructed whole world the literal clock-seven $M$ response
of Section 1 is

$$
m=d+(3U+2n)g(7)=d+(3+2x)H_7.
\tag{25.1}
$$

Evaluation with (22.1), (23.1)–(24.2) gives the following uniform
outward rational enclosures for all $(p,v)\in B$.

| i | M enclosure |
| --- | --- |
| 12 | [541.213619, 541.213687] |
| 15 | [551.327079, 551.330178] |
| 16 | [567.672573, 567.672888] |
| 17 | [568.055631, 568.05594] |

All six endpoint subtractions, with the indicated increasing order,
are recorded here. The right column is a lower bound $\ell_{ij}$ for
$m(W_j)-m(W_i)$.

| $(i,j)$ | $\ell_{ij}$ |
| --- | --- |
| 12,15 | 10113392/10^6 |
| 12,16 | 26458886/10^6 |
| 12,17 | 26841944/10^6 |
| 15,16 | 16342395/10^6 |
| 15,17 | 16725453/10^6 |
| 16,17 | 382743/10^6 |

The enclosures imply $m(W_j)-m(W_i)\ge\ell_{ij}$; taking the least
of these six exact rationals gives

$$
\ell_{16,17}=\frac{382743}{10^6}>\frac13,
\qquad 3\cdot382743=1148229>10^6.
\tag{25.2}
$$

This proves (21.2), hence excludes any distinct equal-$M$ pair in the
entire child at every base in $B$. It applies to arbitrary choices of
$M$ endpoints, including worlds unused by a selected $J$ pair. Allowing
cross-pair overlap or different common terminal values cannot produce a
joint witness in a child whose $M$ response is injective.

## 26. Exact location on the existing actual J arc

SIII, Theorem 16.4, already supplies an actual distinct equal-$J$ pair
for every $10\le p\le34$. To place its $p=20$ base in the particular
rectangle (21.1), use the following exact refinement in source coordinates.
For a strict regular source define

$$
\begin{gathered}
j=b+r(1-r)/b,\quad n=j+r,\quad T=1+b,\quad U=1+2b,\\
\Lambda=1+6/T+1/U-4/j-4/n,\qquad \kappa=6/T-2/U,\\
e=-\frac35(8b-1)\frac{\kappa}{\Lambda},\qquad d=24+e,\\
(G_0,G_1,G_2,G_3)
 =(-24-e,-e/j,(27/5-e)/T,-e/n),\\
g(s)=\sum_{i=0}^3G_i
 \prod_{\substack{0\le l\le3\\l\ne i}}\frac{s-l}{i-l},\\
G_5=-4G_0+15G_1-20G_2+10G_3,\\
G_6=-10G_0+36G_1-45G_2+20G_3,\\
G_7=-20G_0+70G_1-84G_2+35G_3,\\
p=d+(U+n)G_5,\quad v=d+(2U+n)G_6,\\
a=d+(T+2j+4r)G_7,\quad m=d+(3U+2n)G_7.
\end{gathered}
\tag{26.1}
$$

This is the O/SIII whole-parent circuit in $(r,b)$ coordinates.
Regularity is checked locally in the refinement box and is not imposed
on other worlds in $C(p,v)$.

Use the order $z=(r_0,b_0,r_1,b_1)$ and define

$$
\mathcal F(z)=(p_0-20,p_1-20,v_0-v_1,a_0-a_1)^{\mathsf T}.
\tag{26.2}
$$

The exact centre $z_c$ has coordinates

$$
\begin{aligned}
r_0^c&=0.188609969005790726954750425361978757320076728067631441609450871052699587751571188601\\
b_0^c&=0.08775174853069677250961002319440696838931877110051100417039854435209240912687731002016\\
r_1^c&=0.7449349616581750282704923253789474373577799506618427744371610640512144077480737966858\\
b_1^c&=0.311012873552808465827513096002875398040583011764607097299775506391087240258629783837
\end{aligned}
$$

Let $X_J=z_c+[-10^{-65},10^{-65}]^4$ and take the exact rational
preconditioner below, with rows in the order of $z$ and columns in the
order of $\mathcal F$:

$$
C=\begin{pmatrix}
0.01045792770978278974638177877390515482518360407573044422 & 0.009574706592749354158598771695216445994828891668481182697 & 0.0007243686806192904288079057799065235427642636910396977312 & 0.000736886813810193263587497888890726818665308938678165401\\
0.008298474664842742342157285812773850320309468101987930928 & 0.0006460780067431796788963789366975005175211165977451894236 & 0.00004887864382978584685426321160763134288033366407782833217 & 0.0000497233371331032263159274693118433128256773767935624993\\
-0.03231392066200190998312818329721322259812071140889747591 & 0.03761558614551570779506365415539237346935109673225844043 & 0.01453089516606807027968136348707601466723404882192691542 & -0.002156210346703906769102175394090881642595299382896369991\\
0.02150823701464699708389991883708640467372228838240384434 & -0.02173090022478990630289574190331434436075709237382211413 & -0.009671804933107065132635689830452110188319398886051944746 & 0.00143517970708134745086087890670772177082280211217484817
\end{pmatrix}.
$$

On this full closed box the rational circuit and its derivatives satisfy

$$
\begin{gathered}
\|C\mathcal F(z_c)\|_\infty<10^{-85},\qquad
\sup_{z\in X_J}\|I-CD\mathcal F(z)\|_\infty<10^{-50},\\
10^{-85}+10^{-50}10^{-65}<10^{-65}.
\end{gathered}
\tag{26.3}
$$

Here a matrix infinity norm is the maximum absolute row sum. Derivatives
in (26.3) are those of the displayed rational expressions, using the
product and quotient rules. They are enclosed on the same $10^{-100}$
outward rational grid defined in Section 23. Every denominator is
nonzero throughout $X_J$; more particularly,

$$
3.2030<\Lambda_0<3.2031,\qquad
-0.5453<\Lambda_1<-0.5452.
\tag{26.4}
$$

Both sources have $0<r_i<1$, $b_i>0$, and disjoint $r_i$ intervals
throughout $X_J$. The two direct ambient-box response enclosures are

$$
\sup_{z\in X_J}|v_0(z)-v_c|<10^{-60},\qquad
\sup_{z\in X_J}|v_1(z)-v_c|<10^{-59}.
\tag{26.5}
$$

The second enclosure in (26.5) is the $10^{-59}$ enclosure; no second
ambient-box $10^{-60}$ enclosure is used.

**Proposition 26.1 (Existing J pair belongs to B).** There is a unique
$z_*\in X_J$ solving $\mathcal F(z_*)=0$. Its two source coordinates
lift through (26.1) to distinct actual whole worlds at the common base
$(20,v_*)$, with equal terminal $J$ response and (21.3). They are the
$p=20$ pair of SIII, Theorem 16.4, and are $W_{17},W_{15}$ in the
inventory of Proposition 24.1.

Proof. The map $z\mapsto z-C\mathcal F(z)$ has Lipschitz constant
less than $10^{-50}$ on the convex box $X_J$ by (26.3). Its displacement
from $z_c$ is less than $10^{-85}+10^{-50}10^{-65}$, so it carries
the closed box strictly into itself. The box is complete. Banach's
contraction theorem gives a unique fixed point. Since
$\|I-CD\mathcal F\|_\infty<1$, the square matrix $CD\mathcal F$
is invertible, and hence $C$ is nonsingular. The fixed point therefore
satisfies the exact four equations (26.2).

For each source, (26.1) obeys the undivided parent

$$
e\Lambda+\frac{24}{5}(b-1/8)\kappa=0.
\tag{26.6}
$$

Indeed $(24/5)(b-1/8)=(3/5)(8b-1)$. The one interpolant at
$0,1,2,3$ gives $0,24,147/5,24$ at those original readings, and

$$
g(4)-\frac{-6-e}{U}
 =e\Lambda+\frac{24}{5}(b-1/8)\kappa=0
$$

gives the original clock-four reading $18$. Thus the O, Theorem 2.1,
and SIII, Lemma 10.2, converse supplies an entire nonzero real gain and
one fixed real drift per source, exactly as (26.1). The gain is nonzero
because the first two readings differ. The disjoint $r$ intervals make
the complete worlds distinct. Equations (26.2) give equal actual $p,v,a$,
not merely overlapping response enclosures. The common value satisfies

$$
v_*=v_0(z_*)=v_1(z_*),\qquad |v_*-v_c|<10^{-60}<10^{-8}
$$

by the first bound in (26.5). This proves membership in $B$ with $p=20$.
The two different bounds in (26.5) are compatible with this sharper
statement about the actual common value.

To identify the pair with the existing arc, use the SIII coordinate
order $(r_1/b_1,b_1,r_0/b_0,b_0)$. At $p=20$, the $[20,30]$ block of
SIII (16.7), evaluated at its parameter $u=-1$, has the exact centre

$$
(2.39519011914154796714,\ 0.31101287354119756876,\
 2.14935852750507905684,\ 0.08775174853136000343).
\tag{26.7}
$$

The transform of the whole box $X_J$ lies within $10^{-8}$ of this
centre in infinity norm. This is inside SIII, Lemma 16.3's
radius-$10^{-5}$ uniqueness ball. The source-order change and the
replacement of $(r,b)$ by $(r/b,b)$ preserve the same four zero
equalities, up to their ordering and signs. Uniqueness therefore
identifies this refinement with the pair already in Theorem 16.4;
it supplies no additional branch or arc-exhaustion assertion.

Finally direct coordinate interval division of $x=n/U$ on the two
source boxes lies strictly in disks $17$ and $15$ respectively.
Proposition 24.1 identifies their whole worlds with $W_{17}$ and
$W_{15}$. This completes the $J$ membership statement and the proof of
Theorem 21.1. ∎

## 27. Mathematical suppliers and the remaining original problem

The interfaces in the appendix have the following fixed correspondences.

| Supplier | Correspondence used here |
| --- | --- |
| [F: finite-fibre geometry](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md), Lemma 30.2 | $x=n/U$, $H=Ug$, original $d$, and $B_0=294/5-2d-H_2$; all original-world guards and injectivity, with whole gain $H/U$. |
| F, Definition 31.1 and Lemma 31.2 | The same $f$ and carrier $R$; $K=4k$ accounts for $\operatorname{Res}_d(f,K)=256D^8F_0^2R$ and the constant coefficient (22.6). |
| [SVII: support VII](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_VII.md), Lemma 15.1 and Section 16 | All-world $R=0$ and $\alpha d+\zeta=0$ before local unit tests, including drift zero, singular parent, $F_0=0$ and all specialized-degree strata. |
| [O: common-parent geometry](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Theorems 2.1–2.2 | Whole-parent necessity and converse and the $d=24\Rightarrow p=24$ branch for this original history. |
| [SIII: support III](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md), Lemmas 10.2 and 16.3, Theorem 16.4 | The same whole-parent lift, the uniqueness ball in $(r/b,b)$ coordinates and the existing actual $J$ arc. |

Fixed-node interpolation is the classical distinct-node formula, used
with nodes $3,4,5,6$ or $0,1,2,3$ and degree at most three; see
Berrut and Trefethen, *Barycentric Lagrange Interpolation*, §2,
[doi:10.1137/S0036144502417715](https://doi.org/10.1137/S0036144502417715).
The Sylvester determinant and its quadratic norm formula are classical
resultant identities over the rational-function coefficient field and
then polynomial identities; see Cox, Little and O'Shea,
*Ideals, Varieties, and Algorithms*, fourth edition, Chapter 3,
[doi:10.1007/978-3-319-16721-3](https://doi.org/10.1007/978-3-319-16721-3).
Rouché's theorem is used only for polynomials holomorphic on a
neighborhood of a closed disk with a strict boundary modulus inequality;
see Ahlfors, *Complex Analysis*, third edition, Chapter 4, the argument
principle and its applications. Banach's contraction theorem is used
only for a strict contraction mapping the displayed complete closed box
to itself; see Lebl, *Basic Analysis II*,
[§8.5](https://www.jirka.org/ra/realanal2.pdf).
These tools are reused at their stated hypotheses, not proposed as new
general theorems.

The result establishes a finite rectangle with exactly four actual
worlds at every base and a quantitative separation of every original
terminal-$M$ pair. It also locates the already existing actual $J$ pair
inside that rectangle. No larger $J$ component classification, global
joint witness, global joint exclusion, closedness or properness follows.
The original task remains Definition 1.2 over its whole domain, including
all other bases and all original singular, gain and companion strata.
The bounded-base and bounded-companion results of SIII, Sections 7–9,
retain their existing scope; this local calculation does not introduce
a new infinity residual. The unevaluated finite boundary and strict
incidences in that bounded global region remain unresolved. No
literature-wide novelty, model-diversity or kernel-proof claim is made.

## 追加锚（本行以下为增补区）

## 28. An exact exceptional point on the actual J arc

Retain the complete worlds, literal traces and independent-pair
quantifiers of [Definitions 1.1–1.2 and Lemma 1.3](#1-complete-worlds-and-the-unchanged-joint-question).
Thus a world has $0<r<1$, $b>0$, one nonzero real polynomial gain of
degree at most three, and one fixed real drift. The acquired word remains
$J,M,J,M,M,M$, with readings
$(0,24,147/5,24,18,p,v)$ at clocks $0,\ldots,6$; clock seven has the
original $J$ or $M$ alternative on that same world. Zero drift, sample
zeros, lower degrees, repeated gain roots, singular sources and every
unused companion remain in the original domain.

Write $z_J(p)$ and $v_J(p)$ for the actual analytic arc of
[SIII, Lemma 16.3 and Theorem 16.4](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md),
on the whole interval $[10,34]$, with $p=24$ omitted only in the original
joint question. The point below is on this actual arc. Its defining
rational centres are not substituted for the arc.

**Definition 28.1 (Seven equations and an exact rational box).** For a
source pair $(t,b)$ put

$$
\begin{gathered}
r=tb,\qquad j=t+b(1-t^2),\qquad n=j+r,\qquad
T=1+b,\qquad U=1+2b,\\
\mathcal D=5\{(b^2+8b+4)jn-2TU(j+n)\},\qquad
A_s=(8b-1)(2+5b),\\
C_0=-24\mathcal D+3A_sjn,\qquad C_1=3A_sn,\\
C_2=3(49b+34)jn-54U(j+n),\qquad C_3=3A_sj,\\
B_5=-4C_0+15C_1-20C_2+10C_3,\\
B_6=-10C_0+36C_1-45C_2+20C_3,\\
B_7=-20C_0+70C_1-84C_2+35C_3.
\end{gathered}
\tag{28.1}
$$

Where the displayed denominators are nonzero define

$$
\begin{aligned}
p_s&=\frac{-C_0+(U+n)B_5}{\mathcal D},&
v_s&=\frac{-C_0+(2U+n)B_6}{\mathcal D},\\
a_s&=\frac{-C_0+(T+2j+4r)B_7}{\mathcal D},&
m_s&=\frac{-C_0+(3U+2n)B_7}{\mathcal D},\\
d_s&=-\frac{C_0}{\mathcal D},&x_s&=\frac nU.
\end{aligned}
\tag{28.2}
$$

These are exactly the rational functions of SIII (16.1)–(16.5), with
$t=\tau=r/b$ and its denominator renamed $\mathcal D$. In particular
$\mathcal D$ is distinct from $D=x(x+1)(x+2)$ in (22.2).

Use coordinates $z=(t_H,b_H,t_L,b_L,t_G,b_G,p)$ and the exact rational
vector

$$
\begin{aligned}
c={}&(2.2370940478987060045085363750558034267468,\\
&0.3169968078628325686668274079165338900579,\\
&2.0957225084128123115511607571336586558593,\\
&0.0306709682738657107657705994335984762705,\\
&-2.0787332127658314313751707162468341877283,\\
&-0.4166428794531794513317775898703661812074,\\
&13.1377186191279091547601137468519685572483).
\end{aligned}
\tag{28.3}
$$

Every terminating decimal here and below denotes its exact rational
value. Set $\rho_*=10^{-30}$ and

$$
\begin{gathered}
\mathcal B_*=c+[-\rho_*,\rho_*]^7,\\
\Phi(z)=\bigl(p_H-p,\ p_L-p,\ v_H-v_L,\ a_H-a_L,
\ p_G-p,\ v_G-v_H,\ x_G-x_H\bigr).
\end{gathered}
\tag{28.4}
$$

A subscript in (28.4) means evaluation at that source pair in $z$.

**Theorem 28.2 (Evaluated point and its complete lifts).** There is a
unique zero $z_*$ of $\Phi$ in $\mathcal B_*$. Write $p_*$ for its last
coordinate and $v_*=v_H(z_*)$. Then

$$
\begin{gathered}
13.13771861912<p_*<13.13771861914,\\
92.7068988914<v_*<92.7068988915,\\
(t_H,b_H,t_L,b_L)(z_*)=z_J(p_*),\qquad v_*=v_J(p_*).
\end{gathered}
\tag{28.5}
$$

For each $s\in\{H,L,G\}$ the formulas

$$
\begin{gathered}
P_s=P(t_sb_s,b_s),\qquad
 g_s(q)=\sum_{i=0}^3\frac{C_i(t_s,b_s)}{\mathcal D(t_s,b_s)}
 \prod_{\substack{0\le h\le3\\h\ne i}}\frac{q-h}{i-h},\qquad
 d_s=-\frac{C_0(t_s,b_s)}{\mathcal D(t_s,b_s)}
\end{gathered}
\tag{28.6}
$$

are evaluated at $z_*$. They specify one whole gain polynomial and one
fixed drift for each source. The two worlds $W_H=(P_H,g_H,d_H)$ and
$W_L=(P_L,g_L,d_L)$ are distinct original strict worlds in the entire
$C(p_*,v_*)$ and satisfy $a_H=a_L$. The lift $G$ satisfies the same
algebraic acquisition equations and has $p_G=p_*$, $v_G=v_*$ and
$x_G=x_H$, but $b_G<0$, so it is not an original admissible world.
Their values obey

| Quantity | Exact rational enclosure |
| --- | --- |
| $r_H$ | $(0.70,0.72)$ |
| $r_L$ | $(0.06,0.07)$ |
| $d_H$ | $(32.7382713922,32.7382713923)$ |
| $d_L$ | $(24.4,24.5)$ |
| $d_G$ | $(37.0216525196,37.0216525198)$ |
| $x_H=x_G$ | $(1.0261995683,1.0261995685)$ |
| $a_H=a_L$ | $(356,357)$ |
| $m_H$ | $(471.63688484,471.63688486)$ |
| $m_L$ | $(483,485)$ |
| $m_G$ | $(445.92293460,445.92293463)$ |

In particular the algebraic lift $G$ has a different terminal-$M$ value
from $H$.

Proof. First, interval evaluation of the polynomial factors in (28.1)
on $\mathcal B_*$ gives the following open rational enclosures.

| Factor | $H$ | $L$ | $G$ |
| --- | --- | --- | --- |
| $b$ | $(0.316,0.317)$ | $(0.030,0.031)$ | $(-0.417,-0.416)$ |
| $T$ | $(1.316,1.317)$ | $(1.030,1.031)$ | $(0.583,0.584)$ |
| $U$ | $(1.633,1.634)$ | $(1.061,1.062)$ | $(0.166,0.167)$ |
| $j$ | $(0.967,0.968)$ | $(1.991,1.992)$ | $(-0.696,-0.695)$ |
| $n$ | $(1.676,1.677)$ | $(2.055,2.056)$ | $(0.171,0.172)$ |
| $\mathcal D$ | $(-3.068,-3.067)$ | $(42.66,42.67)$ | $(0.0098,0.01)$ |

Thus all divisions in (28.2) are defined on the whole box, and all of
$b,T,U,j,n$ are nonzero there. The factors $T,U,j,n$ are positive
for $H,L$. Consequently it is legitimate to define

$$
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,
\qquad \mathcal D=\frac52 TUjn\Lambda.
\tag{28.7}
$$

The identity is SIII (16.2); the same rational evaluation gives

$$
-0.352<\Lambda_H<-0.351,\qquad
3.809<\Lambda_L<3.810,\qquad
-0.342<\Lambda_G<-0.341.
\tag{28.8}
$$

Here is an exact interval construction for the remaining finite
inequalities. It also specifies the preconditioner without decimal
matrix approximations. Put $h_*=10^{-80}$ and, for rational $u$, set

$$
\operatorname{rd}_-(u)=h_*\lfloor u/h_*\rfloor,\qquad
\operatorname{rd}_+(u)=h_*\lceil u/h_*\rceil,\qquad
\langle[a,b]\rangle=[\operatorname{rd}_-(a),\operatorname{rd}_+(b)].
\tag{28.9}
$$

For interval addition, subtraction and multiplication use

$$
\begin{aligned}
[a,b]+[e,f]&=\langle[a+e,b+f]\rangle,\\
[a,b]-[e,f]&=\langle[a-f,b-e]\rangle,\\
[a,b][e,f]&=\langle[\min(ae,af,be,bf),\max(ae,af,be,bf)]\rangle.
\end{aligned}
\tag{28.10}
$$

For $0\notin[a,b]$, use
$[a,b]^{-1}=\langle[1/b,1/a]\rangle$; division means multiplication
by this reciprocal. Enclose each rational input by (28.9). Evaluate
(28.1)–(28.4) in their displayed order, associating sums and products
from the left. Use $t^2=tt$ and $b^2=bb$.

To enclose derivatives, attach to every interval value $V$ its seven
interval derivatives $(V_1,\ldots,V_7)$. The input coordinates have
unit coordinate derivatives and constants have zero derivatives. For a
product $VW$ use $V_iW+VW_i$. For a reciprocal first form $Q=V^{-1}$
and use $(-V_i)QQ$, with the products in that order. Addition and
subtraction act componentwise. These formulas give an interval
Jacobian $J(\mathcal X)$ of $\Phi$ on each box $\mathcal X$ used here.
The point box $\{c\}$ has exactly represented rational coordinates.
Let

$$
\mathsf M_{ij}=\frac{\inf J(\{c\})_{ij}+\sup J(\{c\})_{ij}}2,
\qquad
C_{ij}=10^{-40}\left\lfloor10^{40}(\mathsf M^{-1})_{ij}\right\rfloor.
\tag{28.11}
$$

Let $P$ be the permutation matrix with
$P(y_1,\ldots,y_7)^{\mathsf T}=(y_1,y_3,y_2,y_4,y_5,y_6,y_7)^{\mathsf T}$.
Start exact rational Gauss–Jordan elimination with the augmented matrix
$[P\mathsf M\mid P]$. For $k=1,\ldots,7$, take as pivot the current
$(k,k)$ entry of the left block, divide the entire row $k$ by that
pivot, and then, in increasing order of $i\ne k$, subtract from row $i$
its current column-$k$ entry times the normalized row $k$. All these
operations act on both blocks; use no further row permutations and no
column permutations. The seven successive pivots lie respectively in

$$
\begin{gathered}
(110.639,110.640),\quad(126.232,126.233),\quad(-2.875,-2.874),\\
(-5875.445,-5875.444),\quad(-10931.139,-10931.138),\\
(-3072.116,-3072.115),\quad(-0.012,-0.011).
\end{gathered}
\tag{28.12}
$$

Thus every pivot is nonzero. The final augmented matrix is
$[I\mid\mathsf M^{-1}]$: if $E$ is the product of the row-operation
matrices, then $EP\mathsf M=I$ and $EP=\mathsf M^{-1}$.
This is the inverse used in (28.11).

For an interval $I$ write $|I|_{\max}=\max(|\inf I|,|\sup I|)$.
Form $N=I-CJ(\mathcal B_*)$ and $w=C\Phi(c)$ with interval
operations (28.9)–(28.10); matrix scalar products sum from index one
to seven, enclosing each product before adding it. The finite rational
bounds, in the coordinate order of $z$, are

| $i$ | $10^{24}\sum_{j=1}^7|N_{ij}|_{\max}\le$ | $10^{44}|w_i|_{\max}\le$ |
| --- | --- | --- |
| $1$ | $201$ | $2481$ |
| $2$ | $11$ | $1046$ |
| $3$ | $45$ | $2021$ |
| $4$ | $55$ | $3475$ |
| $5$ | $7$ | $4077$ |
| $6$ | $2$ | $4337$ |
| $7$ | $7134$ | $4307$ |

All entries of these tables are obtained by rational endpoint
operations on the seven coordinates (28.3); no unknown zero is used in
their construction. The pivot intervals follow by taking exact rational
midpoints in (28.11) and performing the stated rational elimination.
The derivative and displacement bounds are, in particular,

$$
\begin{aligned}
q_*:=\sup_{z\in\mathcal B_*}\|I-C\Phi'(z)\|_\infty
 &\le\frac{7134}{10^{24}}<10^{-20},\\
\eta_*:=\|C\Phi(c)\|_\infty
 &\le\frac{4337}{10^{44}}<10^{-37},\\
\eta_*+q_*\rho_*&\le
\frac{4337}{10^{44}}+\frac{7134}{10^{54}}<\rho_*.
\end{aligned}
\tag{28.13}
$$

The rational functions are analytic on a neighbourhood of the box by
the nonzero denominator bounds. The map $z\mapsto z-C\Phi(z)$ is
therefore a contraction of the complete closed box into its interior.
Moreover $\|I-C\Phi'(c)\|_\infty<1$ makes $C\Phi'(c)$ invertible,
and hence makes $C$ invertible. Banach's theorem now gives exactly one
zero $z_*$ of $\Phi$ in $\mathcal B_*$. Evaluation of (28.2) by the
same interval rules gives all the numerical enclosures in the statement.

For the whole-world assertion, substitution in (28.1) gives the
polynomial identities

$$
\begin{gathered}
-C_0+jC_1=24\mathcal D,\qquad
5(-C_0+TC_2)=147\mathcal D,\qquad
-C_0+nC_3=24\mathcal D,\\
-C_0+U(-C_0+4C_1-6C_2+4C_3)=18\mathcal D.
\end{gathered}
\tag{28.14}
$$

Together with $d+g(0)=0$, these are the literal readings at clocks
zero through four for (28.6). In particular the original clock-four
reading $18$ is retained. The interpolation rows $B_5,B_6,B_7$ in
(28.1) give the literal clocks five, six and seven of Lemma 1.3.
Distinct-node interpolation specifies the entire polynomial, including
any lower-degree or zero-sample case. The gain cannot be identically
zero, since the first two readings are $0$ and $24$.

The bounds $b_H,b_L>0$ and $0<r_H,r_L<1$ prove original strictness of
$H,L$; their disjoint $r$ intervals prove distinctness. Equations
$\Phi(z_*)=0$ prove that they share $(p_*,v_*)$ and their terminal-$J$
value. The same identities apply algebraically to $G$, since its
$b$ and $\mathcal D$ are nonzero; its negative $b$ excludes it from
$C(p_*,v_*)$.

It remains to identify the strict pair with the specified actual arc.
Let $I_*=[13.13771861912,13.13771861914]$, let
$\mathcal B_{HL}$ be the projection of $\mathcal B_*$ onto its first
four coordinates, and let $\widehat z_{[10,20]}$ be the polynomial
centre map of SIII (16.7). Evaluate its four displayed coefficient
arrays by descending Horner evaluation at $(I_*-15)/5$, dividing each
integer coefficient by $10^{20}$. The rules (28.9)–(28.10) give

| Coordinate $i$ | $10^{16}\sup\{|z_i-\widehat z_{[10,20],i}((p-15)/5)|:z\in\mathcal B_{HL},\ p\in I_*\}\le$ |
| --- | --- |
| $t_H$ | $3354$ |
| $b_H$ | $206$ |
| $t_L$ | $807$ |
| $b_L$ | $963$ |

Consequently

$$
\|(t_H,b_H,t_L,b_L)(z_*)-
\widehat z_{[10,20]}((p_*-15)/5)\|_\infty
\le\frac{3354}{10^{16}}<10^{-10}<10^{-5}.
\tag{28.15}
$$

The first four equations of $\Phi=0$ are precisely SIII (16.6).
SIII, Lemma 16.3, gives uniqueness of its zero in this radius-$10^{-5}$
ball at each fixed $p\in[10,20]$. Thus these exact sources are
$z_J(p_*)$, and their common response is $v_J(p_*)$, as asserted. ∎

## 29. A vanishing drift coefficient and a multiple carrier root

Use exactly the integer polynomials $f,K,F_0,\alpha,\zeta,R$ and the
fixed Sylvester matrix of [(22.1)–(22.5)](#22-exact-coefficient-circuit-and-its-original-world-interpretation).
In particular $f=Ad^2+B_fd+C_f$ uses the literal coefficient
extractions of Definition 22.1 and $K=4k$ in the normalization of
[F, Sections 31–32](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md).
Put $x_*=x_H(z_*)=x_G(z_*)$ and $v_*=v_J(p_*)$, with the exact point
of Theorem 28.2.

**Theorem 29.1 (Evaluated failure of the nonzero linear drift chart).**
At this actual point,

$$
\begin{gathered}
\alpha(x_*,p_*,v_*)=\zeta(x_*,p_*,v_*)=0,\\
1306<F_0(x_*,p_*,v_*)<1307,\qquad
-5287<A(x_*,p_*,v_*)<-5285.
\end{gathered}
\tag{29.1}
$$

The specialized polynomial $R_*(X)=R(X,p_*,v_*)$ is nonzero and

$$
\operatorname{ord}_{X=x_*}R_*(X)\ge2.
\tag{29.2}
$$

The common finite drift roots of
$f(x_*,d,p_*,v_*)=K(x_*,d,p_*,v_*)=0$ are exactly the two distinct
real numbers $d_H$ and $d_G$ of Theorem 28.2. The first belongs to an
actual strict endpoint of the specified $J$ arc, has $d_H\ne0$ and
$\Lambda_H\ne0$, and lies outside $F_0=0$. The second belongs to the
negative-$b$ algebraic lift $G$ and supplies no original admissible
endpoint.

Proof. All nonzero source factors used below were established on the
whole box before the divisions in (28.7). The drift intervals in
Theorem 28.2 show $d_H,d_G\notin\{0,24\}$ and $d_H\ne d_G$.
They also give $x_*>0$, so
$D(x_*)=x_*(x_*+1)(x_*+2)>0$.

For $s\in\{H,G\}$ put $\mathcal H_s(q)=U_sg_s(q)$. The two lifts
have the same $p_*,v_*,x_*$, and their literal clocks three through
six give

$$
\mathcal H_s(3)=\frac{24-d_s}{x_*},\qquad
\mathcal H_s(4)=18-d_s,\qquad
\mathcal H_s(5)=\frac{p_*-d_s}{x_*+1},\qquad
\mathcal H_s(6)=\frac{v_*-d_s}{x_*+2}.
\tag{29.3}
$$

Thus the interpolant (22.1) at drift $d_s$ is exactly this whole
scaled gain. Clock zero gives $H_0=-d_sU_s$. Clock two gives
$T_sH_2=U_s(147/5-d_s)$. Since $2T_s=U_s+1$, the definition
$B_0=294/5-2d_s-H_2$ gives $B_0U_s=H_2$. Identity (22.10) now
yields

$$
f(x_*,d_s,p_*,v_*)=5D(x_*)^2(d_sH_2+H_0B_0)=0.
\tag{29.4}
$$

Also $H_1=U_s(24-d_s)/j_s\ne0$, using the already established
nonzero $U_s,j_s$ and $d_s\ne24$. The source relation

$$
r_s^2-(1+b_s)r_s+b_s(n_s-b_s)=0
\tag{29.5}
$$

is a polynomial identity after $r_s=t_sb_s$ and
$n_s=t_s+b_s(1-t_s^2)+t_sb_s$. Substitution of $H_0=-d_sU_s$,
$b_s=(U_s-1)/2$ and $r_s=x_*U_s-j_s$ into (22.2), exactly as in
(24.4), therefore gives

$$
\begin{aligned}
K(x_*,d_s,p_*,v_*)&=
4D(x_*)^4d_s^2H_1^2
\{r_s^2-(1+b_s)r_s+b_s(x_*U_s-b_s)\}\\
&=0.
\end{aligned}
\tag{29.6}
$$

These algebraic equalities use the nonzero factors just listed, not
positivity of $b_s$. They consequently apply to $G$ as well as $H$.

Apply the first identity of (22.4) to both common drift roots. It gives

$$
\alpha(x_*,p_*,v_*)d_H+\zeta(x_*,p_*,v_*)=0,
\qquad
\alpha(x_*,p_*,v_*)d_G+\zeta(x_*,p_*,v_*)=0.
\tag{29.7}
$$

Subtracting and using $d_H\ne d_G$ proves $\alpha=0$, and either
equality then proves $\zeta=0$.

For the remaining coefficient bounds, evaluate (22.2) on the rational
intervals $x=x_H(\mathcal B_*)$, $p=\mathcal B_{*,7}$ and
$v=v_H(\mathcal B_*)$, using (28.9)–(28.10). The coefficient $A$
can equivalently be evaluated as
$(f(x,1,p,v)+f(x,-1,p,v)-2f(x,0,p,v))/2$.
This gives the two bounds in (29.1). In particular $f$ has degree
exactly two in $d$ at $(x_*,p_*,v_*)$. The two distinct drifts
already found exhaust all its roots and hence all finite common drift
roots with $K$. At the second drift the interpolant fixes $H_0$, and
$d_G\ne0$ forces $U=-H_0/d_G=U_G<1$ in any whole-world lift.
Consequently $b=(U-1)/2<0$ there; this drift cannot supply an
alternative strict lift.

Before using root-order notation, the same interval evaluation at the
base gives

$$
\begin{gathered}
-410<32p_*-5v_*-366<-409,\\
27575<120p_*^2-38p_*v_*-3360p_*+3v_*^2+522v_*+23112<27576.
\end{gathered}
\tag{29.8}
$$

Both factors in the exact constant-coefficient formula (22.6) are
nonzero. Thus $[X^0]R_*(X)>0$, and $R_*$ is not the zero
polynomial.

Finally specialize the fixed matrix (22.5) at $(p_*,v_*)$, retaining
its rows $d^3f,d^2f,df,f,dK,K$ and columns $d^5,\ldots,1$.
At $X=x_*$, its nullspace contains the two independent columns

$$
(d_H^5,d_H^4,d_H^3,d_H^2,d_H,1)^{\mathsf T},\qquad
(d_G^5,d_G^4,d_G^3,d_G^2,d_G,1)^{\mathsf T}.
\tag{29.9}
$$

Their independence follows already from their last two coordinates.
Extend them to a constant invertible change of columns. The resulting
polynomial matrix has two columns vanishing at $X=x_*$, so each of
those columns is divisible by $X-x_*$. Its determinant, and hence
$\det\mathsf S(X,p_*,v_*)$, is divisible by $(X-x_*)^2$.
This is the determinant-multiplicity argument of
[F, Theorem 32.1](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md), applied
here to the two explicitly supplied common finite drifts.

By (22.5),

$$
\det\mathsf S(X,p_*,v_*)=
256\{X(X+1)(X+2)\}^{8}F_0(X,p_*,v_*)^2R_*(X).
\tag{29.10}
$$

The factors preceding $R_*$ are nonzero at $x_*$, by $x_*>0$ and
(29.1). The nonzero-polynomial assertion just proved therefore makes
its order at $x_*$ well defined, and (29.10) proves (29.2). ∎

**Remark 29.2 (Scope of the evaluated obstruction).** The point of
Theorems 28.2 and 29.1 disproves the assertion that every actual
endpoint on the whole specified arc has $\alpha\ne0$, even after
excluding $F_0=0$ and $\Lambda=0$. It also disproves the assertion
that every positive projected carrier root arising from such an actual
endpoint is simple. At this point the equation $\alpha d+\zeta=0$
is $0=0$ and cannot determine drift by division. The two common drifts
are retained by the undivided equations $f=K=0$; only $d_H$ among
these two lifts is admissible, since $b_G<0$.

The evaluated point and its inequalities use the actual arc and its
uniqueness balls from
[SIII, Lemma 16.3 and Theorem 16.4](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md),
the normalized identities [(22.1)–(22.6)](#22-exact-coefficient-circuit-and-its-original-world-interpretation),
and the determinant-order argument of
[F, Theorem 32.1](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md).
Contraction, fixed-node interpolation and the general determinant
argument are reused proof ingredients; the evaluated specialization is
the assertion here.

These results leave the entire child $C(p_*,v_J(p_*))$ unrestricted
apart from the exhibited members. They do not enumerate that child or
supply an actual terminal-$M$ pair in it. The $J$ arc remains the whole
$[10,34]\setminus\{24\}$ arc, with arbitrary original companions.
Existence of an independent actual $M$ pair somewhere above this arc,
or its exclusion over the entire arc, remains open. The original joint
question of Definition 1.2 still ranges over every original base and
every strict complete world, with overlapping or disjoint pairs and
independent common terminal values; an exclusion confined to this arc
would not settle that global question.

## 追加锚（本行以下为增补区）

## 30. The endpoint drift-division exceptional set on the whole actual arc

**Definition 30.1 (Actual endpoint functions and their unchanged domain).**
Let $z_J(p)=(t_H(p),b_H(p),t_L(p),b_L(p))$ and $v_J(p)$ be the
actual analytic functions of
[SIII, Lemma 16.3 and Theorem 16.4](FIB_STRICT_REAL_JOINT_INCIDENCE_SUPPORT_III.md),
for $p\in[10,34]$. Use the source circuit (28.1)–(28.2), with
$\mathcal Q=\mathcal D/5$, and write

$$
x_s(p)=\frac{n(t_s(p),b_s(p))}{U(b_s(p))},\qquad
\alpha_s(p)=\alpha(x_s(p),p,v_J(p)),\qquad s\in\{H,L\}.
\tag{30.1}
$$

The polynomial $\alpha$ is the literal coefficient extraction (22.3).
In particular $K$ is the polynomial in (22.2), without division by four.
The source denominator $\mathcal D=5\mathcal Q$ is distinct from
$D=x(x+1)(x+2)$. The reduced polynomials remain exactly
$\alpha_r=\alpha/(32D^3)$ and $\zeta_r=\zeta/(32D^3)$ of (22.7).

The worlds and their clocks are those of Definitions 1.1–1.2:
$W=(P(r,b),g,d)$, $0<r<1$, $b>0$, $0\ne g\in\mathbb R[q]$,
$\deg g\le3$, $d\in\mathbb R$, with the original acquired word
$J,M,J,M,M,M$ and readings $(0,24,147/5,24,18,p,v)$.
The closed interval here includes the analytic endpoints at $p=24$;
the original joint question still has $p\ne24$.
No sign, exact degree, sample nonvanishing, drift restriction or
regular-source restriction is imposed on the entire original child.

**Definition 30.2 (Source factors and an exact quotient).** For independent
indeterminates $t,b$, use $j,n,T,U,C_i,N_p,N_v$ of (28.1)–(28.2) and set

$$
\begin{aligned}
\mathcal S={}&b^4(t^6-3t^5-6t^4+17t^3+14t^2-23t-15)\\
&+b^3(23t^6-72t^5-89t^4+320t^3+25t^2-230t+94)\\
&+b^2(-69t^5+95t^4+348t^3-349t^2-241t+252)\\
&+b(69t^4+22t^3-271t^2-19t+135)-23t^3-46t^2+15t+20,\\
\mathcal B={}&b^3(309t^4-309t^3-298t^2+149t-11)\\
&+b^2(162t^4-780t^3+465t^2+220t-318)\\
&+b(-324t^3+631t^2-236t-160)+162t^2-160t.
\end{aligned}
\tag{30.2}
$$

Define $\mathcal T\in\mathbb Z[t,b]$ by the exact polynomial quotient

$$
\mathcal T=
\frac{U^{23}\mathcal Q^3}{27\mathcal S^2}
\alpha_r\left(\frac nU,\frac{N_p}{5\mathcal Q},
                         \frac{N_v}{5\mathcal Q}\right).
\tag{30.3}
$$

Here the right side specifies a polynomial identity before any source
is evaluated. To specify its coefficients by integer arithmetic, write

$$
\alpha_r(x,p,v)=\sum_{i,j,k}a_{ijk}x^ip^jv^k.
$$

Coefficient extraction in (22.2)–(22.7) gives $i\le23$, $j+k\le3$.
Consequently

$$
\begin{aligned}
\mathcal W&=\sum_{i,j,k}a_{ijk}n^iU^{23-i}
 N_p^jN_v^k(5\mathcal Q)^{3-j-k},\\
\mathcal W&=3375\mathcal S^2\mathcal T.
\end{aligned}
\tag{30.4}
$$

Expansion and exact division in $\mathbb Z[t,b]$ give zero remainder.
The numerator $\mathcal W$ has $1683$ nonzero monomials;
$\mathcal T$ has $1034$ and bidegree $(46,27)$, in the order $(t,b)$.
Thus (22.2)–(22.7), (28.1)–(28.2) and (30.2)–(30.4) specify every
coefficient without a floating coefficient list or a source specialization.
In particular $\mathcal S^2$ has not been dropped at its zero set.

**Theorem 30.3 (Exhaustive endpoint inventory).** The function
$\alpha_H$ has exactly four zeros on the whole closed interval $[10,34]$.
They are simple and are the unique points $p_i$ in the following open
rational intervals $I_i=(l_i,h_i)$, respectively. Every decimal denotes
its exact terminating rational value.

| $i$ | $l_i$ | $h_i$ |
| --- | --- | --- |
| 1 | $13.1377186191279091547601$ | $13.1377186191279091547602$ |
| 2 | $19.5319320737263986033004$ | $19.5319320737263986033005$ |
| 3 | $32.8725952384491631141317$ | $32.8725952384491631141318$ |
| 4 | $33.9742535335153124186754$ | $33.9742535335153124186755$ |

The function $\alpha_L$ has no zero on $[10,34]$. These statements
include the seams, the two external endpoints and $24$.
The first point is the point $p_*$ of Theorem 28.2.
On both distinguished actual endpoints throughout $[10,34]$,

$$
x_s>4/5,\qquad F_0(x_s,p,v_J(p))>0,\qquad
A(x_s)<0,\qquad k_4(x_s)>0.
\tag{30.5}
$$

The complete gains of these two endpoints have cubic coefficient in
$(1,2)$, and $d_H>24$, $d_L>22$ there. These are properties of the
two specified endpoints, not hypotheses on an arbitrary original world.

Proof. The source-specific arithmetic and the closed-cover argument
are given in Sections 31–32. Their conclusions count zeros of
$\mathcal T(t_H(p),b_H(p))$ and exclude zeros at L. On every source
tube used there, $U,\mathcal Q,\mathcal S$ and $D(x_s)$ are nonzero.
Thus (22.7) and (30.3) give on the actual arc

$$
\alpha_s(p)=
\frac{864D(x_s(p))^3\mathcal S(t_s(p),b_s(p))^2}
 {U(b_s(p))^{23}\mathcal Q(t_s(p),b_s(p))^3}
\mathcal T(t_s(p),b_s(p)).
\tag{30.6}
$$

The multiplier is analytic and nonzero, so it preserves both zeros and
their orders. This also explains why the rational centres cannot be
substituted for the actual endpoints. The source inequalities below
prove (30.5) and the gain and drift bounds. Finally Theorem 28.2 places
$p_*$ inside $I_1$, using its radius-$10^{-30}$ enclosure (28.3), and
Theorem 29.1 gives $\alpha_H(p_*)=0$. Uniqueness in $I_1$ identifies
$p_1=p_*$. The previously specified first point is therefore retained. ∎

## 31. Rational source bounds on a finite closed cover

**Definition 31.1 (Closed cells and outward rational arithmetic).** Let
$\widehat z_{[l,h]}$ be precisely the rational polynomial centre of
SIII (16.7), evaluated with $u=(2p-l-h)/(h-l)$ and denominator $10^{20}$.
For each $[l,h]\in\{[10,20],[20,30],[30,34]\}$ put

$$
P_k=\left[l+\frac{(h-l)k}{1024},
          l+\frac{(h-l)(k+1)}{1024}\right],\qquad
Z_k=\widehat z_{[l,h]}(P_k)+[-10^{-5},10^{-5}]^4,
\quad 0\le k<1024.
\tag{31.1}
$$

These are enclosures of the actual arc, by SIII, Lemma 16.3.
They are not additional source restrictions. Use outward arithmetic
on $\epsilon\mathbb Z$, $\epsilon=10^{-80}$: for rational $a,b$,

$$
\langle[a,b]\rangle=
[\epsilon\lfloor a/\epsilon\rfloor,
 \epsilon\lceil b/\epsilon\rceil].
\tag{31.2}
$$

Addition and subtraction use $[a+c,b+d]$ and $[a-d,b-c]$;
multiplication uses the minimum and maximum of $ac,ad,bc,bd$;
then apply (31.2) to each operation. A reciprocal is the enclosure of
$[1/b,1/a]$ only when $0\notin[a,b]$. Enclose each rational input
before its first use. Sums and matrix scalar products start at zero
and use increasing indices, enclosing each multiplication and addition.
A square may use the exact interval square before outward rounding.

For a polynomial $P(t,b)=\sum_{a,e}c_{ae}t^ab^e$, its exact
translated array at a rational point $(t_0,b_0)$ is

$$
P(t_0+\xi,b_0+\eta)=\sum_{i,j}\widetilde c_{ij}\xi^i\eta^j,
\qquad
\widetilde c_{ij}=
\sum_{a\ge i,e\ge j}c_{ae}\binom ai\binom ej
 t_0^{a-i}b_0^{e-j}.
\tag{31.3}
$$

For a cell, take $t_0,b_0$ from its block centre at the nearest integer
to its parameter midpoint, with the smaller integer chosen in a tie.
Use the first block at integer $20$ and the second at integer $30$.
All arrays in (31.3) are exact rational arrays. Evaluate them by
descending Horner in $\eta$ insidedescending Horner in $\xi$,
including intervening zero coefficients. Differentiate exact
polynomials before translation and interval evaluation. Evaluate
$\widehat z$ itself by the Horner convention of SIII (16.7).
These conventions apply also to $\mathcal T$ and its gradient.

**Lemma 31.2 (Source guards, coefficient signs and excluded cells).**
On every initial tube (31.1) the source factors satisfy

$$
\begin{gathered}
\mathcal S_H<-50,\quad\mathcal S_L<-50,\quad
\mathcal B_H<-29,\quad\mathcal B_L>100,\\
x_H,x_L>4/5,\qquad \mathcal D_H<0<\mathcal D_L,\\
0<r_H,r_L<1,\qquad b_H,b_L>0.
\end{gathered}
\tag{31.4}
$$

The gain coefficient and drift evaluations on these tubes give

$$
1<\frac{-C_0+3C_1-3C_2+C_3}{6\mathcal D}<2,\qquad
-\frac{C_{0,H}}{\mathcal D_H}>24,\qquad
-\frac{C_{0,L}}{\mathcal D_L}>22.
\tag{31.5}
$$

On L, $\mathcal T_L<0$ on every one of the $3072$ initial tubes.
On H, the only initial tubes whose $\mathcal T_H$ enclosure contains
zero have the following indices; in every other H tube it excludes zero.

| Block | Number of H tubes excluding zero | Remaining indices $k$ |
| --- | ---: | --- |
| $[10,20]$ | $1012$ | $318,319,320,321,322,323,973,974,975,976,977,978$ |
| $[20,30]$ | $1024$ | none |
| $[30,34]$ | $1022$ | $735,1017$ |

Proof. Expand (30.2)–(30.4) using the coefficient circuit, and evaluate
by (31.2)–(31.3) on (31.1). This is a finite collection of rational
inequalities with all coefficient and endpoint inputs specified.
For the source signs, one may also use the larger radius-$2\cdot10^{-5}$
tubes and their hulls in SIII (16.12):

$$
\begin{gathered}
69/100<r_H<98/100,\quad31/100<b_H<39/100,\\
15/1000<r_L<49/100,\quad7/1000<b_L<23/100,\\
-6<\Lambda_H<-29/100,\qquad7/5<\Lambda_L<41/10.
\end{gathered}
\tag{31.6}
$$

Since $t=r/b>0$, the identities $T=1+b$, $U=1+2b$ and
$j=b+r(1-r)/b$, $n=j+r$ make $T,U,j,n$ positive on these source
boxes. Identity (28.7) gives the signs of $\mathcal D=5\mathcal Q$.
In particular source response denominators are nonzero before any
quotient derivative is evaluated.

For an additional exact reduction of the coefficient checks, direct
expansion before specialization gives

$$
F_0\left(\frac nU,\frac{N_p}{5\mathcal Q},
                       \frac{N_v}{5\mathcal Q}\right)
 =-\frac{3\mathcal B\mathcal S}{5U^3\mathcal Q}.
\tag{31.7}
$$

Equivalently, multiplication by $5U^3\mathcal Q$ is the polynomial
identity

$$
\begin{aligned}
&405n^3(5\mathcal Q)
 +(975(5\mathcal Q)-18N_p+5N_v)n^2U\\
&\quad +(90(5\mathcal Q)-36N_p+5N_v)nU^2
 -480U^3(5\mathcal Q)=-3\mathcal B\mathcal S.
\end{aligned}
\tag{31.8}
$$

Thus (31.4) proves $F_0>0$ on both endpoints with its denominator
already guarded. The first expression in (31.5) is the cubic
coefficient of the entire interpolant (28.6), because the third
forward difference is $-C_0+3C_1-3C_2+C_3$.

The coefficient extractions in (22.2) also give exactly

$$
A=-10(177x^6+724x^5+542x^4-742x^3-629x^2+196x+160)
\tag{31.9}
$$

and

$$
\begin{aligned}
k_4=4(&810000x^{14}+6462000x^{13}+16947800x^{12}+8105575x^{11}\\
&-32819677x^{10}-39897876x^9+19542116x^8+43133645x^7\\
&-598103x^6-21163284x^5-3719936x^4+5003840x^3\\
&+1396400x^2-464000x-160000).
\end{aligned}
\tag{31.10}
$$

Here is a finite rational sign prescription for these univariate
polynomials. For $P=A$ or $P=k_4$ form $S_0=P$, $S_1=P'$ and
$S_{i+1}=-\operatorname{rem}(S_{i-1},S_i)$ over $\mathbb Q[x]$, stopping
at a nonzero constant. No negative rescaling is made. Let $V(a)$ be
the sign variation after zero values are removed, and at $+\infty$
use the signs of the leading coefficients. The exact variations are

$$
\begin{array}{c|c|c|c}
P&a&V(a)&V(+\infty)\\ \hline
A&0&1&1\\
k_4&4/5&2&2.
\end{array}
\tag{31.11}
$$

Neither polynomial vanishes at its displayed left endpoint. Sturm's
zero count gives no positive zero of $A$ and no zero of $k_4$ above
$4/5$. The evaluations $A(1)<0$ and $k_4(1)>0$ give the signs in
(30.5). Thus the degrees two and four in $d$ are established on these
source tubes, rather than postulated as model assumptions. The other
finite inequalities in the lemma follow by the interval operations
already specified; the table retains every tube not excluded in this
first evaluation. ∎

## 32. Velocity bounds, simple zeros and exact parameter isolation

**Lemma 32.1 (Exhaustion of the remaining closed cells).** Let
$\Theta(p)=\mathcal T(t_H(p),b_H(p))$. On each of the fourteen
remaining cells in Lemma 31.2, $\Theta'$ has a strict sign. Endpoint
signs, in increasing cell order, are

$$
\begin{array}{c|l}
[10,20] &(+,+),(+,+),(+,+),(+,-),(-,-),(-,-),
          (-,-),(-,-),(-,-),(-,+),(+,+),(+,+)\\
[30,34] &(+,-),(-,+).
\end{array}
\tag{32.1}
$$

The four sign-changing cells, in increasing order, have these
whole-cell derivative enclosures:

| Cell | Enclosure of $\Theta'$ |
| --- | --- |
| $[6725/512,3365/256]$ | $[-6000000000000,-4900000000000]$ |
| $[625/32,10005/512]$ | $[13200000000000,14300000000000]$ |
| $[8415/256,263/8]$ | $[-231400000000000,-228400000000000]$ |
| $[8697/256,4349/128]$ | $[155100000000000,156600000000000]$ |

For the two groups of six remaining cells in $[10,20]$, the following
whole-cell bounds hold uniformly within each group:

| Remaining indices $k$ | Enclosure of $\Theta'$ |
| --- | --- |
| $318,319,320,321,322,323$ | $[-5600000000000,-5300000000000]$ |
| $973,974,975,976,977,978$ | $[13000000000000,14100000000000]$ |

There is exactly one zero on each of the four sign-changing cells, all
are in their interiors, and there are no further zeros on $[10,34]$.
Each $I_i$ of Theorem 30.3 contains the corresponding zero.

Proof. We specify the source enclosure and its velocity enclosure,
so that a derivative of the centre polynomial is never mistaken for
a derivative of the actual arc. Use the four equations

$$
F(z,p)=(p_H-p,p_L-p,v_H-v_L,a_H-a_L)^T,\qquad
\beta=(1,1,0,0)^T.
\tag{32.2}
$$

Their literal coefficient numerators are (28.1)–(28.2), and
$F(z_J(p),p)=0$. In particular $D_zF$ is independent of $p$.
Start with $Z=Z_k$ on a remaining cell $P=P_k$ and let $c$ be its
rational coordinate midpoint. Enclose $D_zF(c)$ by (31.2); take the
rational midpoint matrix $M$ of this enclosure, invert $M$ over
$\mathbb Q$, and set

$$
C_{ij}=10^{-40}\lfloor10^{40}(M^{-1})_{ij}\rfloor.
\tag{32.3}
$$

The inversion here uses ordinary rational row elimination on
$[M\mid I_4]$: at column $i$ use the first nonzero pivot in rows
$i,\ldots,3$, swap rows, normalize that row, then eliminate its column
from the other rows. All four pivots in these midpoint matrices are
nonzero. This defines a rational matrix without claiming it is the
exact inverse of an interval matrix.

For a numerator $N$ and denominator $\mathcal D$, use

$$
\begin{aligned}
(N/\mathcal D)_i&=N_i/\mathcal D-N\mathcal D_i/\mathcal D^2,\\
(N/\mathcal D)_{ij}&=N_{ij}/\mathcal D
 -(N_i\mathcal D_j+N_j\mathcal D_i+N\mathcal D_{ij})/\mathcal D^2
 +2N\mathcal D_i\mathcal D_j/\mathcal D^3.
\end{aligned}
\tag{32.4}
$$

For each row $i$, combine the coefficients of the two numerator arrays

$$
N_{iH}=C_{i0}N_p+C_{i2}N_v+C_{i3}N_a,\qquad
N_{iL}=C_{i1}N_p-C_{i2}N_v-C_{i3}N_a
\tag{32.5}
$$

before applying (32.4). Their two-source mixed Hessian entries are
zero. The centre gradient of these combined quotients and their
Hessian bounds on $Z$ give an enclosure of $CD_zF(Z)$: enclose its
$(i,j)$ entry by the centre gradient plus

$$
[-B_{ij},B_{ij}],\qquad
B_{ij}=\sum_l\sup_Z|(CD_z^2F)_{ijl}|\sup|Z_l-c_l|.
\tag{32.6}
$$

Thus $E=I-CD_zF(Z)$ is an interval matrix enclosing every corresponding
exact matrix on the convex box. The denominator signs in Lemma 31.2
continue to hold on every intersection below. At each enclosure step
replace $Z$ by

$$
Z\cap\bigl(c-CF(c,P)+E(Z-c)\bigr).
\tag{32.7}
$$

The evaluation of $CF(c,P)$ retains its exact dependence on the
parameter: its $i$th entry is
$N_{iH}(c_H)/\mathcal D(c_H)+N_{iL}(c_L)/\mathcal D(c_L)
 -(C_{i0}+C_{i1})P$.
Recenter after each intersection and repeat the midpoint construction.
Five intersections suffice for the displayed cells. These operations
use only rational endpoints and the exact arrays in (31.3), (32.4)–(32.6).

To justify retention of actual points, let $F(z,p)=0$ with
$p\in P$, $z\in Z$. The integral mean value formula gives

$$
z=c-CF(c,p)+(I-C\overline J)(z-c),\qquad
\overline J=\int_0^1D_zF(c+u(z-c))\,du.
\tag{32.8}
$$

The convex-box enclosure $E$ contains $I-C\overline J$.
Consequently (32.7) cannot remove an actual root. This argument needs
neither an existence conclusion from the interval intersection nor an
assumption that $C$ is an exact inverse. Existence and identification
of the actual arc are already SIII, Lemma 16.3.

After the intersections, recompute $C,E$ and put
$q=\|E\|_\infty$, using the sums of absolute entry suprema.
These fourteen cells have $q<1/100$; in particular the four
sign-changing cells have $q<1/5$. Differentiating the actual equation in (32.2) gives
$D_zF(z_J(p))z_J'(p)=\beta$, and hence

$$
z_J'=C\beta+Ez_J',\qquad
\|z_J'\|_\infty\le\frac{\|C\beta\|_\infty}{1-q}.
\tag{32.9}
$$

The equation with interval $E$ means membership in the right side,
not equality to a freely selected interval entry. Starting with the
symmetric box given by the last inequality, perform five intersections

$$
V\ \longleftarrow\ V\cap(C\beta+EV).
\tag{32.10}
$$

Each retains the true velocity at every $p\in P$.
Finally evaluate

$$
\Theta'(p)=
\mathcal T_t(t_H(p),b_H(p))\,t_H'(p)
+\mathcal T_b(t_H(p),b_H(p))\,b_H'(p)
\tag{32.11}
$$

using the translated exact gradient and the first two components of
$V$. Equations (31.2)–(31.3), (32.3)–(32.11) give the derivative
intervals in the table; on each of the other ten remaining cells the
derivative interval also excludes zero.

For endpoint signs apply the same source intersections at the singleton
parameter endpoint, starting from
$\widehat z(p)+[-10^{-5},10^{-5}]^4$, and evaluate $\mathcal T_H$.
This gives precisely the nonzero signs (32.1). For $l_i,h_i$ in
Theorem 30.3 use eight source intersections; the pairs of signs are
$(+,-),(-,+),(+,-),(-,+)$, respectively. The actual root remains in
every such enclosure by (32.8). Thus these signs concern the actual
arc and not the values of $\mathcal T$ at approximate centres.

Strict monotonicity and (32.1) exclude a zero on each same-sign cell,
and the intermediate value theorem gives exactly one interior zero
on each opposite-sign cell. The whole-cell derivative bounds make
each zero simple. Every other initial cell was already excluded by
Lemma 31.2. The narrower opposite-sign intervals therefore isolate
these same four zeros. This proves the assertion. ∎

**Corollary 32.2 (No uncovered parameter or unguarded zero).** The zero
classification in Theorem 30.3 holds on the entire closed interval,
and hence also on $[10,34]\setminus\{24\}$. Each $p_i$ is equivalently
the unique parameter in $I_i$ for which

$$
F(z,p)=0,\qquad \mathcal T(t_H,b_H)=0,\qquad
\|z-\widehat z(p)\|_\infty<10^{-5}.
\tag{32.12}
$$

Here $F=0$ may be replaced by its four source-denominator-cleared
polynomial equations, with the same guards and uniqueness ball.

Proof. The cells (31.1) are closed and cover all three closed blocks.
Their common cell endpoints have not been removed. Every remaining
cell endpoint has a nonzero sign in (32.1), and every excluded cell
has an enclosure excluding zero even at its endpoints. The seams
$20,30$, the external endpoints $10,34$ and $24$ belong to excluded
closed cells. SIII's seam identification joins the actual root
functions across the two block seams; neither centre discrepancy
creates an additional branch. The pointwise uniqueness balls in
SIII, Lemma 16.3, identify any guarded solution of (32.12) with
$z_J(p)$. Lemma 32.1 then proves uniqueness of its parameter.
Lemma 31.2 guards every denominator used in (30.6), so no zero is
hidden by clearing denominators or by the squared factor
$\mathcal S^2$. ∎

## 33. Common drifts and all complete lifts above the four projections

**Definition 33.1 (Four exact projections and their whole gains).**
For $i\in\{1,2,3,4\}$ let $p_i$ be defined by Theorem 30.3,
$v_i=v_J(p_i)$ and $x_i=x_H(p_i)$. For $s=H,L$ evaluate the original
source functions at $z_J(p_i)$ and set

$$
W_{s,i}=(P(t_sb_s,b_s),g_s,d_s),\qquad
 d_s=-\frac{C_0}{\mathcal D},\qquad
 g_s(q)=\frac1{\mathcal D}\sum_{k=0}^3C_k
 \prod_{\substack{0\le l\le3\\l\ne k}}\frac{q-l}{k-l}.
\tag{33.1}
$$

These formulas specify a whole fixed polynomial and drift on each
world. Their evaluation uses the actual source coordinates, specified
by (32.12), throughout.

**Theorem 33.2 (Two real common finite drifts, exactly one strict lift).**
At each projection $(x_i,p_i,v_i)$,

$$
\alpha=\zeta=0.
\tag{33.2}
$$

The common finite roots in $d$ of the literal polynomials $f$ and $K$
are exactly two distinct real numbers. They are $d_{H,i}$ from
(33.1) and

$$
d_{G,i}=-\frac{B_f(x_i,p_i,v_i)}{A(x_i)}-d_{H,i}.
\tag{33.3}
$$

Exactly one of these two drifts has an original strict whole-world
lift at this fixed projection, namely $W_{H,i}$. The second drift
has the following forced negative-$b$ value. The open rational
intervals also establish distinctness and finiteness of both drifts.

| $i$ | $d_{H,i}$ | $d_{G,i}$ | Forced $b_{G,i}$ | $H_{1,G,i}$ |
| --- | --- | --- | --- | --- |
| 1 | $(32.73827139,32.73827140)$ | $(37.02165251,37.02165252)$ | $(-0.41664288,-0.41664287)$ | $(3,4)$ |
| 2 | $(29.67423205,29.67423206)$ | $(34.50222779,34.50222780)$ | $(-0.57919713,-0.57919712)$ | $(10,11)$ |
| 3 | $(24.99557948,24.99557949)$ | $(33.28110767,33.28110768)$ | $(-0.60441407,-0.60441406)$ | $(11,12)$ |
| 4 | $(24.67345843,24.67345844)$ | $(34.11309262,34.11309263)$ | $(-0.37742775,-0.37742774)$ | $(3,4)$ |

Both $W_{H,i}$ and $W_{L,i}$ are distinct original strict worlds in
$C(p_i,v_i)$ and have equal original terminal-$J$ readings.
The assertion about exactly one strict lift concerns the fixed
projection $x_i$, not all source locations in that child.

Proof. The source circuit supplies the exact identities

$$
\begin{gathered}
-C_0+jC_1=24\mathcal D,\qquad
5(-C_0+TC_2)=147\mathcal D,\qquad
-C_0+nC_3=24\mathcal D,\\
-C_0+U(-C_0+4C_1-6C_2+4C_3)=18\mathcal D.
\end{gathered}
\tag{33.4}
$$

Clock zero is $d+g(0)=0$. The identities (33.4) therefore restore
the literal clocks one through four. The late interpolation rows
(16.4) of SIII, equivalently (28.1)–(28.2), give the literal readings
$p_i,v_i,a_s$ at clocks five, six and seven. The equations $F=0$
give $a_H=a_L$ at those same actual sources. Positivity and strictness
are (31.4), and the disjoint source ranges (31.6) make the two worlds
distinct. The two different acquired readings $0,24$ imply that each
gain is nonzero. These checks also explain why no degree or sample
assumption is needed for the whole-world lift.

Every $p_i$ is off $24$. Thus the faithful inverse of
[F, Lemma 30.2](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md),
with exactly the interpolant (22.1), applies to these actual worlds.
In particular necessity (22.8) gives
$f(x_i,d_{H,i},p_i,v_i)=K(x_i,d_{H,i},p_i,v_i)=0$.
The defining zero of $\alpha_H$ and the undivided identity (22.4) give
$\zeta=0$ on substituting $d_{H,i}$. Since $A\ne0$, the same identity
now says that $f$ divides $K$ as polynomials in $d$ at this projection.
There is no division by $\alpha$, $\zeta$ or a sample value here.
The polynomial $f$ has degree exactly two by (30.5), so its second
root is exactly (33.3).

For the explicit lift test at the second root let $H_G$ be the unique
whole interpolant of degree at most three at the original nodes
$3,4,5,6$, with samples

$$
\left(\frac{24-d_G}{x_i},\ 18-d_G,\
      \frac{p_i-d_G}{x_i+1},\ \frac{v_i-d_G}{x_i+2}\right).
\tag{33.5}
$$

Use its extrapolations $H_{0,G},H_{1,G},H_{2,G}$ from (22.1), and put

$$
\begin{gathered}
B_{0,G}=294/5-2d_G-H_{2,G},\\
U_G=\frac{-d_GH_{0,G}+B_{0,G}H_{2,G}}
 {d_G^2+B_{0,G}^2},\qquad b_G=(U_G-1)/2,\\
j_G=U_G(24-d_G)/H_{1,G},\qquad r_G=x_iU_G-j_G.
\end{gathered}
\tag{33.6}
$$

The arithmetic for the table is entirely rational interval arithmetic:
start with each closed $[l_i,h_i]$ and its actual source tube,
perform the eight source intersections specified after (32.11), and
evaluate $x_i=n_H/U_H$, $v_i=v_H$, $d_H=-C_{0,H}/\mathcal D_H$,
(33.3), (33.5) and (33.6), in this order, using (31.2)–(31.3).
The intervals in the table are outward bounds on these expressions.
Their distinct drift intervals prove that $f$ has two simple real
roots; both are common roots because $f\mid K$, and there is no
third finite common root. The leading-coefficient signs in (30.5)
exclude a drift-degree drop at these projections.

All the denominators used to test this second root have explicit
guards: $x_i,x_i+1,x_i+2>0$, $A<0$, $d_G>33$,
$d_G^2+B_{0,G}^2>0$, and $H_{1,G}\ne0$ by the table. Each $b_G$
interval avoids both $0$ and $-1/2$, so $b_G\ne0$ and $U_G\ne0$.
In particular the algebraic coordinates in (33.6) are well defined.
For completeness they determine a whole algebraic lift, even though
it is inadmissible. Indeed (22.10) and $f(d_G)=0$ give

$$
d_GH_{2,G}+H_{0,G}B_{0,G}=0.
\tag{33.7}
$$

Since $d_G\ne0$, (33.6) and (33.7) imply
$U_G=-H_{0,G}/d_G$ and $B_{0,G}U_G=H_{2,G}$.
Substitute these relations and $j_G$ into $K(d_G)=0$. The identity
used in (29.6) becomes

$$
0=4D(x_i)^4d_G^2H_{1,G}^2
\{r_G^2-(1+b_G)r_G+b_G(x_iU_G-b_G)\}.
\tag{33.8}
$$

Its prefactor is nonzero. Dividing its braces by $b_G\ne0$ gives
$j_G=b_G+r_G(1-r_G)/b_G$, since $x_iU_G=j_G+r_G$.
Set $g_G=H_G/U_G$ and use $P(r_G,b_G)$ as an algebraic matrix.
The identities $d_GU_G=-H_{0,G}$ and $B_{0,G}U_G=H_{2,G}$,
with $T_G=(U_G+1)/2$, restore clocks zero and two. The definition
of $j_G$ restores clock one, and the four samples (33.5) restore
clocks three through six. This is one entire nonzero polynomial
with one fixed drift; its nonzero property follows again from $0,24$.
It is not an original world, because $b_G<0$.

More directly, any putative original world at $(x_i,d_G,p_i,v_i)$
must have exactly this $H_G,U_G,b_G$ by the necessity half of F,
Lemma 30.2. The negative-$b$ interval therefore rejects every possible
strict lift there, irrespective of any other failed positivity guard.
At $d_H$ the same faithful inverse admits at most one original world,
and (33.1) constructs it. This proves both the exact common-drift
count and the unique strict-lift assertion. ∎

## 34. Exact projected multiplicity and the retained joint boundary

**Theorem 34.1 (Multiplicity exactly two at all four projections).**
For $i=1,2,3,4$, hold $p=p_i$ and $v=v_i$ fixed and consider the
single polynomial $R_i(X)=R(X,p_i,v_i)$. It is nonzero and

$$
\operatorname{ord}_{X=x_i}R_i(X)=2.
\tag{34.1}
$$

Thus the multiplicity assertion at the first point strengthens the
lower bound of Theorem 29.1; the other three points have the same
exact multiplicity. Each of these four multiple projections has
exactly one strict whole-world lift among its common finite drifts,
as in Theorem 33.2.

Proof. Put $a=\alpha_r$ and $z=\zeta_r$ solely in this proof. The exact
norm identity (22.4), after substitution of (22.7), reads near each
point, where its denominator is a unit,

$$
R=\frac{4\{Az^2-B_faz+C_fa^2\}}{A^3D^2F_0^2}.
\tag{34.2}
$$

All $x$ subscripts below are partial derivatives with $p,v$ fixed.
At the point, $a=z=0$ by Theorem 33.2, and
$A,D,F_0$ are nonzero by (30.5). Consequently (34.2) gives
$R=R_x=0$ and

$$
R_{xx}=\frac{8\{A\zeta_{r,x}^2
                  -B_f\alpha_{r,x}\zeta_{r,x}
                  +C_f\alpha_{r,x}^2\}}
                 {A^3D^2F_0^2}.
\tag{34.3}
$$

Terms differentiating the denominator, or the coefficient functions
inside the numerator, multiply either $a$ or $z$ and vanish there.
Thus (34.3) uses fixed-base derivatives, without inferring a
fixed-base multiplicity from a derivative along the arc.

Differentiate the exact reduced coefficient arrays (22.7) with
respect to $x$ before evaluating them. Use the same eight-step
source enclosures over $[l_i,h_i]$ as in Theorem 33.2, and evaluate
(34.3) at $x=n_H/U_H$, $p\in[l_i,h_i]$, $v=v_H$ with the outward
operations (31.2) and exact translated arrays (31.3).
The resulting open rational bounds are

$$
\begin{aligned}
-17010000000000000000&<R_{xx}(x_1,p_1,v_1)
                         <-17000000000000000000,\\
7667000000000000000&<R_{xx}(x_2,p_2,v_2)
                         <7668000000000000000,\\
26270000000000000&<R_{xx}(x_3,p_3,v_3)
                         <26290000000000000,\\
-2955000000000000&<R_{xx}(x_4,p_4,v_4)
                         <-2954000000000000.
\end{aligned}
\tag{34.4}
$$

Every denominator in (34.3) is guarded before this evaluation.
The strict nonzero second derivative proves both that $R_i$ is not
the zero polynomial and that its first nonzero Taylor coefficient at
$x_i$ is the quadratic coefficient $R_i''(x_i)/2$. This is precisely
(34.1). No reduced square-free carrier has replaced the polynomial
$R$ of Definition 22.1. ∎

**Proposition 34.2 (Mathematical scope of the endpoint inventory).**
The classification above settles the drift-division exceptional set
on the two distinguished actual endpoints over the whole
$[10,34]\setminus\{24\}$ arc, and the exact multiplicity of its four
exceptional H projections. It leaves open the existence or exclusion
of an independent actual terminal-$M$ pair in the entire
$C(p,v_J(p))$ anywhere on that arc. It also leaves open the original
full-domain same-child independent-$J/M$ question of Definition 1.2,
with overlapping or disjoint pairs and independent common terminal
values.

Proof. The statements proved classify only $\alpha_H,\alpha_L$ and
the common drift roots at four fixed H projections. They do not
classify all source locations of an arbitrary original child and do
not compare terminal-$M$ values of every pair in that child.
In particular, the negative-$b$ algebraic lift cannot be an actual
member of such a pair. None of the source enclosures is a restriction
on unused companions. Zero drift, gain degree drops, repeated roots,
vanishing samples and singular sources remain in the entire original
domain, as do unbounded positive source offdiagonals. The acquisition
and the clock-seven alternatives are unchanged.

The actual-arc theorem and its pointwise identification are reused
from SIII, Lemma 16.3 and Theorem 16.4; the first exceptional point is
Theorems 28.2–29.1; the fixed normalization and necessity identities
are Section 22 and SVII, Section 15; and faithful whole-world
reconstruction is F, Lemma 30.2. Distinct-node interpolation, Sturm's
zero-count theorem, the mean value theorem and the intermediate value
theorem are classical ingredients within these source-specific
proofs. The additional source-specific conclusions are the exhaustive
four-H-zero/no-L-zero inventory, its three further exceptional
projections and common-drift lifts, and the exact multiplicity two at
all four points. These are consequences of the displayed rational
circuits and inequalities; no literature-priority assertion is made.
No injectivity assertion for the terminal-$M$ map on an entire child
follows from this endpoint classification. The original global
completion criterion is therefore still **OPEN**. ∎

## 追加锚（本行以下为增补区）
