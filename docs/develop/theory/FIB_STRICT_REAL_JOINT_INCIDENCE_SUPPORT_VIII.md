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
