# FIB strict-real joint-incidence support

This volume records three source-specific results for the unchanged strict-real
same-child problem. The complete parent parametrisation, fixed history and
off-twenty-four reconstruction are those of [O](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md), Definitions 1.1–1.3, and [F](FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md),
Sections 30–33. All references below use the acquired word $J,M,J,M,M,M$,
the original clocks $0,\ldots,7$, and the two actions at clock seven as
counterfactual alternatives.

## 1. The common parent and the joint predicate

**Definition 1.1 (Complete worlds and one acquired child).** A complete world is

$$
W=(P(r,b),g,d),\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1, b>0,\quad 0\ne g\in\mathbb R[s],\quad\deg g\le3,\quad d\in\mathbb R.
$$

Let $J=\begin{pmatrix}0&1\\1&0\end{pmatrix}$,
$M=\begin{pmatrix}0&1\\1&1\end{pmatrix}$, and
$H_4=(0,J,24,M,147/5,J,24,M,18)$. Starting with $A_0=I$ and
$A_i=E_iA_{i-1}$, the read at clock $i$ is
$d+g(i)\operatorname{tr}(A_iP)$. For real $(p,v)$, $p\ne24$, put

$$
C(p,v)=\mathcal F(H_4,M,p,M,v).
$$

The definition includes every lower-degree polynomial, every sampled or
repeated root, zero drift, singular source, and unbounded positive
off-diagonal. A world is in $C(p,v)$ only when every original read has
occurred; there is no reset, copy, skipped read, clock shift, or extra port.

For a world write

$$
j=b+\frac{r(1-r)}b,\qquad n=j+r,\qquad T=1+b,\qquad U=1+2b,\qquad x=\frac nU,\qquad H=Ug.
$$

At clocks $3,4,5,6$ the interpolating polynomial $H$ has samples

$$
h_3=\frac{24-d}{x},\quad h_4=18-d,\quad
h_5=\frac{p-d}{x+1},\quad h_6=\frac{v-d}{x+2}.
$$

The distinct-node interpolation used here is the classical formula of
Berrut–Trefethen, §2,
[primary text](https://people.maths.ox.ac.uk/trefethen/barycentric.pdf).
It assumes distinct nodes, with no restriction on sampled zeros.
Its values $H_i=H(i)$, $i=0,1,2,7$, are

$$
\begin{aligned}
H_0&=20h_3-45h_4+36h_5-10h_6,\\
H_1&=10h_3-20h_4+15h_5-4h_6,\\
H_2&=4h_3-6h_4+4h_5-h_6,\\
H_7&=-h_3+4h_4-6h_5+4h_6.
\end{aligned}
$$

The faithful reconstruction of F, Lemma 30.2, says that these coordinates,
the strict inequalities, and its two source equations are equivalent to one
whole legal world. Explicitly, with $C_2=147/5$ and
$B_0=2(C_2-d)-H_2$, they are

$$
\begin{gathered}
x>0,\quad d\ne24,\quad H_1\ne0,\quad C_0=d^2+B_0^2>0,\qquad
U=\frac{-dH_0+B_0H_2}{C_0}>1,\\
b=(U-1)/2,\quad j=\frac{U(24-d)}{H_1},\quad r=xU-j,\quad 0<r<1,\\
j=b+\frac{r(1-r)}b,\qquad dU=-H_0,\qquad B_0U=H_2,\qquad g=H/U.
\end{gathered}
$$

This is the cited reconstruction interface, not an additional theorem.
Distinct complete worlds are exactly distinct guarded pairs $(x,d)$.
The two terminal alternatives are

$$
f_{MJ}=d+\frac{T+2j+4r}{U}H_7,\qquad f_{MM}=d+(3+2x)H_7.
$$

**Definition 1.2 (Same-base joint incidence).** Define

$$
\begin{aligned}
D_J&=\{(p,v):\exists W\ne W'\in C(p,v),\ f_{MJ}(W)=f_{MJ}(W')\},\\
D_M&=\{(p,v):\exists W\ne W'\in C(p,v),\ f_{MM}(W)=f_{MM}(W')\}.
\end{aligned}
$$

The required local event is $D_J\cap D_M$. The two pairs may overlap, and
their common terminal values need not agree. Equivalently, four labels
$(W_0,W_1,W_2,W_3)$ at one and the same $(p,v)$ satisfy

$$
W_0\ne W_1, f_{MJ}(W_0)=f_{MJ}(W_1),\qquad
W_2\ne W_3, f_{MM}(W_2)=f_{MM}(W_3).
$$

No projected root, complex label, or diagonal limit is a label in this
definition.

**Assumption 1.3 (Owning results and quantified scopes).** The parent lift
and singular-source classification used below are O, Theorems 2.1–2.2
and 4.2, and Theorem 29.2. The coordinate interface and the fixed resultant
are F, Lemmas 30.2, 31.2–31.3; the finite-world premise is F,
Theorem 32.1. O, Theorem 9.1, already supplies a joint child at $p=24$.
F, Theorems 24.2–24.3, exclude the entire sixth-$M$ children only at their
specified exact $p_J$, and F, Theorem 29.1, classifies terminal-$M$
pairs at $p=24$. These restrictions are not extended to other $p$ here.
The [published off-$24$ collision](FIB_OFF_P24_UNEQUAL_RATIO_COLLISION_GEOMETRY.md)
supplies one terminal-$M$ pair; its existence alone is not membership
in $D_J\cap D_M$. No theorem from a different history is a premise
for a common-base collision in this volume.

## 2. A transverse common index zero that does not lift

**Definition 2.1 (A rational regular label chart).** Put $\tau=r/b$, so
$r=\tau b$, and define

$$
j=\tau+b(1-\tau^2),\qquad n=j+r,\qquad T=1+b,\qquad U=1+2b.
$$

Whenever $j,n,T,U,\Lambda$ are nonzero, put

$$
\Lambda=1+\frac6T+\frac1U-\frac4j-\frac4n,\qquad
\kappa=\frac6T-\frac2U,\qquad
\varepsilon=-\frac{24(b-1/8)\kappa}{5\Lambda},\qquad d=24+\varepsilon.
$$

Let $g$ be the unique polynomial of degree at most three whose first four
samples are

$$
\gamma_0=-d,\qquad \gamma_1=-\frac\varepsilon j,\qquad
\gamma_2=\frac{27/5-\varepsilon}{T},\qquad\gamma_3=-\frac\varepsilon n.
$$

The extrapolation values are

$$
g_5=-4\gamma_0+15\gamma_1-20\gamma_2+10\gamma_3,\quad
 g_6=-10\gamma_0+36\gamma_1-45\gamma_2+20\gamma_3,\quad
 g_7=-20\gamma_0+70\gamma_1-84\gamma_2+35\gamma_3.
$$

Define the response map

$$
\Psi(\tau,b)=(p,v,a,m)
=\bigl(d+(U+n)g_5, d+(2U+n)g_6,
 d+(T+2j+4r)g_7, d+(3U+2n)g_7\bigr).
$$

The inequalities $b>0$ and $0<\tau b<1$, together with the displayed
nonzero denominators, are the legal part of this chart. Extending the
rational formula beyond them creates algebraic labels, not worlds.

For $z=(\tau_0,b_0,\tau_1,b_1,\tau_2,b_2)$, write
$\Psi_i=(p_i,v_i,a_i,m_i)$ and set

$$
G(z)=(p_0-p_2,p_1-p_2,v_0-v_2,v_1-v_2,a_0-a_2,m_1-m_2).
$$

The first and third labels are the proposed terminal-$J$ pair; the second
and third are the proposed terminal-$M$ pair.

**Theorem 2.2 (Exact regular common zero and strict-real false lift).** There
is a unique $z^*$ in the rational box $B_z=\{\lVert z-c\rVert_\infty\le
10^{-55}\}$ for which $G(z^*)=0$. Its acquired base is an actual acquired off-$24$ base.
The two regular relative terminal indices defined in the proof vanish
there and have transverse locally isolated zero sets. This base belongs to

$$
B_{\rm base}=\{(p,v):|p-p_c|\le10^{-50},\ |v-v_c|\le10^{-50}\},
$$

where, with denominator $10^{65}$,

$$
p_c=830114690304052605379065950633208219220764205229572969320399564672/10^{65},
$$

$$
v_c=7637500654861612317458298012422660558955674211467789792017368943141/10^{65}.
$$

Every base in $B_{\rm base}$ is off $24$. The complete original child at
$(p^*,v^*)$, and indeed at every base in this box, has exactly three legal
worlds. Their terminal-$J$ and terminal-$M$ maps are both injective.
Thus the common algebraic zero is not a point of $D_J\cap D_M$.

**Proof.** The centre $c$, in the displayed coordinate order, has denominator
$10^{65}$ and numerators

$$
\begin{gathered}
209253126317152266860569287719788385342476850263440649921325416180,\\
32480988594140656182048224030513796627349982741363125313601294609,\\
4866650356751890016168586103798805324907717448539457005800921754501,\\
2008133747381927985929639839638245782643469554767892601204632707,\\
207682067127852702687655530882739460351799656971524625528868757246,\\
-443620843462099388633771062591789263853297174948995411225006297.
\end{gathered}
$$

Let $C=(DG(c))^{-1}$, computed exactly over $\mathbb Q$. Outward-rounded
rational interval arithmetic gives

$$
-163698926699<\det DG(c)<-163698926698,\qquad
\lVert CG(c)\rVert_\infty\le10^{-65},
$$

and, on $B_z$, the six absolute row sums of (I-CDG(z)) are bounded by

$$
(10,1,4368,2,1,2)\,10^{-45}.
$$

All interval endpoints are rounded outward to multiples of $10^{-100}$
after elementary operations; the centre and $C$ are exact rationals. Thus
$z\mapsto z-CG(z)$ has contraction factor at most $4368\cdot10^{-45}$,
and

$$
10^{-65}+(4368\cdot10^{-45})10^{-55}<10^{-55}.
$$

It maps the closed box strictly into itself. The classical contraction theorem applies here on the complete closed
sup-norm box (Banach, “Sur les opérations dans les ensembles abstraits
et leur application aux équations intégrales”, Fundamenta Mathematicae 3,
[pp. 133–181](https://doi.org/10.4064/fm-3-1-133-181)).
It gives a
unique fixed point, and nonsingularity of $C$ turns the fixed-point equation
into $G(z^*)=0$. Its distance from $c$ is at most
$10^{-65}/(1-4368\cdot10^{-45})<2\cdot10^{-65}$; evaluation of
$\Psi$ on this smaller box places the common base in $B_{\rm base}$.
All source-chart denominators are nonzero on $B_z$.

The full-fibre assertion uses the denominator-free equations of F,
$31.1$–$31.8$. Put \$D=x(x+1)(x+2)\$, and, with

$$
\begin{gathered}
z_3=(24-d)(x+1)(x+2),\quad z_4=(18-d)D,\quad
z_5=(p-d)x(x+2),\quad z_6=(v-d)x(x+1),\\
a_0=20z_3-45z_4+36z_5-10z_6,\quad
a_1=10z_3-20z_4+15z_5-4z_6,\\
a_2=4z_3-6z_4+4z_5-z_6,\qquad z_*=xa_1-D(24-d),
\end{gathered}
$$

define

$$
f=5dDa_2+a_0((294-10d)D-5a_2),
$$

$$
4k=4a_0^2z_*^2+2a_0(dD-a_0)z_*a_1
-(a_0+dD)(dD+(1-2x)a_0)a_1^2.
$$

Let \$f=a_fd^2+b_fd+c_f\$, and write
\$K=4k=A_4d^4+A_3d^3+A_2d^2+A_1d+A_0\$. The exact pseudo-remainder is

$$
\begin{aligned}
\alpha&=A_4(-b_f^3+2a_fb_fc_f)+A_3a_f(b_f^2-a_fc_f)-A_2a_f^2b_f+A_1a_f^3,\\
\beta&=A_4(-b_f^2c_f+a_fc_f^2)+A_3a_fb_fc_f-A_2a_f^2c_f+A_0a_f^3,
\end{aligned}
$$

with $f\mid a_f^3K-(\alpha d+\beta)$. On the regular quotient put
$d^*=-\beta/\alpha$, $H_i=a_i(x,d^*)/D$. The relative terminal
functions are

$$
\tau_M=d^*+(2x+3)H_7,\qquad
\tau_J=d^*+\left(\frac12+4x-\frac{d^*}{2H_0}-\frac{2(24-d^*)}{H_1}\right)H_7.
$$

The zero-safe formulas of F give the same functions on this regular chart.
Set $a_7=-z_3+4z_4-6z_5+4z_6$. All quotient operations in this
section are in the basis $1,x,\ldots,x^{17}$ of
$\mathbb Q(p,v)[x]/(\bar R)$, where $\bar R=R/[x^{18}]R$.
For either action, form the coefficient determinant $K_E$ with columns
$1,\tau_E,\ldots,\tau_E^{17}$. At distinct roots $x_i$,

$$
\det K_E=\prod_{i<j}\frac{\tau_E(x_j)-\tau_E(x_i)}{x_j-x_i}.
$$

The normalized polynomial (R(x,p,v)) is the F resultant quotient, so its
degree in $x$ is $18$. Set $R_0(x)=\bar R(x,p_c,v_c)$.
At the centre of $B_{\rm base}$, the eighteen
Gaussian-rational seeds (real part, imaginary part) are

$$
\begin{gathered}
(9.302352,0),(2.100946,0),(2.021472,0),(-1.695823,0),(-1.552604,0),
(-1.549383,0),(-1.352134,0),(-1.264680,0),(-1.213928,0),\\
(-0.371261,0),(1.157782,0),(1.073021,0),(1.015249,0),(0.961446,0),
(0.680999,0.094785),(0.680999,-0.094785),(0.543933,0),(0.337484,0).
\end{gathered}
$$

Eight Newton steps, with each component rounded by
$10^{-45}\lfloor10^{45}u+1/2\rfloor$, define the eighteen centres. The
closed rectangles of radius $10^{-35}$ around them are disjoint. With
$\gamma_i=1/R_0'(c_i)$, interval evaluation gives

$$
|\Re(1-\gamma_i\bar R'(x))|+|\Im(1-\gamma_i\bar R'(x))|<10^{-27},\qquad
\max(|\Re(\gamma_i\bar R(c_i))|,|\Im(\gamma_i\bar R(c_i))|)<10^{-42}.
$$

These bounds hold for every $x$ in the corresponding rectangle and
every base in $B_{\rm base}$. The complex sup norm is the maximum of the
absolute real and imaginary components; the displayed derivative sum
bounds its operator norm. The rectangles therefore contain one simple root each and exhaust the degree
eighteen polynomial. Coefficients are evaluated in increasing $(x,p,v)$
order and univariate polynomials by Horner evaluation; interval endpoints are
rounded outward to $10^{-300}$. For root-box evaluation reduce $\alpha,\beta$ modulo $\bar R$ first.
Define $B_0=294/5-2d^*-H_2$, $C_0=d^{*2}+B_0^2$,
$N_0=-d^*H_0+B_0H_2$. On every rectangle the leading coefficient,
$D,\alpha,a_f,d^*,H_0,H_1,d^{*2}+B_0^2$, and
$-d^*H_0+B_0H_2$ have a real or imaginary component of absolute value
greater than $1/10$. All quotient inverses and terminal charts are valid.

The zero-drift roots are independently isolated from seeds
$-2.651694,-0.853405,0.523730$, with the same eight-step and radius rules applied to the monic $F_0$
specialization. Their uniform derivative and displacement bounds are
$<10^{-27}$ and $<10^{-42}$, respectively; thus they exhaust all three
roots of $F_0$.
On each box $|\alpha|>10^{14}$, $|294D-5a_2(x,0)|>80$, and
$|L_0|>10^6$, where

$$
\begin{aligned}
u&=5a_2(x,0),\quad t=294D-5a_2(x,0),\quad z=xa_1(x,0)-24D,\\
L_0&=4u^2z^2-2(u+t)uz\,a_1(x,0)+(u-t)((2x-1)u+t)a_1(x,0)^2.
\end{aligned}
$$

If $F_0(x)=0$, then $f=K=0$ at $d=0$, hence $\beta=0$; the nonzero
$\alpha$ forces $d^*=0$. A legal zero-drift world would then satisfy
$L_0=0$, a contradiction. Thus no actual world is lost by the regular
resultant chart.

Conjugation fixes the unique root in each real-centred rectangle;
the two rectangles with nonzero imaginary centre have no real point.
Thus the roots have seven negative real values, nine positive real values
and one nonreal conjugate pair. Of the positive roots, the strict reconstruction
guards retain exactly the roots near $0.961446,1.015249,2.021472$. The other
positive roots fail respectively as follows:

| root near | failed guard |
|---|---|
| $0.337484$ | $r>4$ |
| $0.543933$ | $b<0, r<0$ |
| $1.073021$ | $b<0$ |
| $1.157782$ | $b<0, r<0$ |
| $2.100946$ | $b<0, r<0$ |
| $9.302352$ | $b<0, r>1$ |

The three retained worlds have

| root near | $r$ | $b$ | $f_{MJ}$ | $f_{MM}$ |
|---|---|---|---|---|
| $0.961446$ | $(115/1000,116/1000)$ | $(107/1000,109/1000)$ | ($266,267$) | ($408,409$) |
| $1.015249$ | label $0$ above | — | ($314,315$) | ($419,420$) |
| $2.021472$ | label $1$ above | — | ($419,420$) | ($427,428$) |

Every actual world projects to $F_0R=0$. At an $R$ root the fixed
Sylvester identity and the certified nonzero $a_f$ give a common
finite $f,K$ root. The pseudo-remainder makes it the unique $d^*$.
The equations $f=0$ and $d^*\ne0$ imply, for $U=-H_0/d^*$,
$B_0U=H_2$; $K=0$ then gives the rank-one identity after divisions by the
certified nonzero $d^*,H_1$. Thus the reconstruction equalities hold exactly.
At every root the pseudo-remainder
gives the unique drift and the remaining guards are necessary and sufficient
by F, Lemma 30.2. This proves that the entire child has exactly these three
worlds. Their response intervals are pairwise disjoint for each action, so
both terminal maps are injective.

It remains to verify that the index zero is a genuine regular intersection,
rather than a repeated-root artefact. On the three selected label boxes,

$$
\det\frac{\partial(p_i,v_i)}{\partial(\tau_i,b_i)}
\in(24779,24780),(4978,4979),(-4334,-4333),
$$

respectively. Thus each label is a local analytic section over the base.
For $A=a_0-a_2$ and $M=m_1-m_2$, exact interval differentiation gives

$$
-\frac{31}{100}<\det\frac{\partial(A,M)}{\partial(p,v)}<-\frac3{10}.
$$

Uniformly in the eighteen root boxes, every terminal-$J$ difference
except the pair near $2.100946,1.015249$ has a real or imaginary component
of absolute value $>1$. Every terminal-$M$ difference except the pair near
$2.100946,2.021472$ has the same separation. The common labels project
to roots near $1.015249,2.021472,2.100946$, respectively.
The Vandermonde factorisation shows that each relative index is a nonzero
analytic factor times the corresponding (A) or $M$. The displayed
determinant makes their common zero isolated and transverse. At the zero,
$p_0=p_1=p_2$, $v_0=v_1=v_2$, $a_0=a_2$, and $m_1=m_2$ hold exactly;
the third label is inadmissible, with

$$
-0.010<r_2<-0.009,\qquad -0.005<b_2<-0.004.
$$

The certified source and response intervals for the three labels are

| label | \$r\$ | \$b\$ | \$\Lambda\$ | \$f_{MJ}\$ | \$f_{MM}\$ | status |
|---|---|---|---|---|---|---|
| \$0\$ | \$(679/1000,680/1000)\$ | \$(324/1000,325/1000)\$ | \$(-273/1000,-272/1000)\$ | \$(314,315)\$ | \$(419,420)\$ | legal |
| \$1\$ | \$(977/1000,978/1000)\$ | \$(20/1000,21/1000)\$ | \$(2386/1000,2387/1000)\$ | \$(419,420)\$ | \$(427,428)\$ | legal |
| \$2\$ | \$(-10/1000,-9/1000)\$ | \$(-5/1000,-4/1000)\$ | \$(4202/1000,4203/1000)\$ | \$(314,315)\$ | \$(427,428)\$ | inadmissible |

The first two rows obey \$b>0\$ and \$0<r<1\$; the last row violates both
strict source inequalities. The interval table is compatible with, and
refines, the root-box response table above.

The common algebraic participant is therefore outside the original strict
source domain. This proves the theorem. ∎

## 3. Exceptional-world terminal-$M$ injectivity

**Definition 3.1 (The exceptional union).** Use the exact F31 cubic

$$
F_0=405x^3+(975-18p+5v)x^2+(90-36p+5v)x-480
$$

and the $\Lambda$ of Definition 2.1, interpreted through the source
(r,b). Define

$$
E(p,v)=\{W\in C(p,v):F_0(x(W),p,v)=0\ \text{or}\ \Lambda(W)=0\}.
$$

This is a subfamily of the entire child, not the set of all worlds above the
image of its base map.

**Theorem 3.2 (M-injectivity on the exceptional union).** For every real
$p\ne24,v$, the restriction of $f_{MM}$ to $E(p,v)$ is injective.
Consequently, each distinct terminal-$M$ pair in an entire child has at
least one endpoint outside $E(p,v)$, and that endpoint has $d\ne0$.

**Proof.** Write $C_2=147/5$ and $D=x(x+1)(x+2)$. The clock-zero
equation in the faithful reconstruction is

$$
DH_0=-2F_0+d(45x^3+89x^2-32x-40).
$$

Thus $F_0=0$ implies either $d=0$, or
$U=U_*(x)=-(45x^3+89x^2-32x-40)/D$. We treat these branches and the
$\Lambda=0$ branch, retaining their source guards.

For $d=0$, interpolation gives the necessary and sufficient source equation

$$
\frac1j+\frac1n=S(b):=\frac{147}{80T}+\frac3{16U}.
$$

Every strict solution has $b<1/2$. For $1/2\le b\le1$, the source
inequalities imply

$$
j\le\frac{4b^2+1}{4b},\qquad n\le\frac{5b^2+2b+1}{4b},
$$

and, after clearing the positive denominator, the difference between the two
sides has numerator

$$
-420b^5+4208b^4+2003b^3+484b^2+7b-162.
$$

With $t=b-1/2$, this is

$$
t^4(3158-420t)+9369t^3+\frac{18551}{2}t^2+3966t+\frac{1851}{4}>0.
$$

For $b\ge1$, use $n<b+1$; the cleared difference has numerator
$44b^3+632b^2+171b-82$, whose shift by $b=1$ has coefficients
$44,764,1567,765$, again positive. Hence $b<1/2$. Since $n>j$, the parent equation gives
$n>2/S$; also $US<211/80$. Thus
$x=n/U>160/211>3/4$, while

$$
g_5=\frac{120}{j}-\frac{147}{T}+\frac{45}{U}>\frac{78-69b}{4TU}>0.
$$

Therefore $p=(U+n)g_5>0$. For $p>0$, the coefficient of $x^2$ in
$F_0$ minus the coefficient of $x$ is $885+18p>0$; with negative
constant and positive leading coefficient, Descartes' rule gives exactly one
positive root. The reconstruction then forces $H_1>0$,
$C_2<H_2<2C_2$, $U=H_2/(2C_2-H_2)$, $b=(U-1)/2$, $j=24U/H_1$,
$r=xU-j$, and the whole gain $g=H/U$. Conversely, retaining these guards and
$j=b+r(1-r)/b$ reconstructs every original clock from the unique
interpolant of $(0,24/j,147/(5T),24/n)$ at $0,1,2,3$.
Thus the zero-drift branch is
injective.

For the source-family separation we retain inequation boundaries in the
sense of Lazard–Rouillier, Definition 1 and real-case Remark 1,
[primary report](https://inria.hal.science/inria-00070678/document).
The explicit computations below supply the source-specific result.
For $d\ne0$, set $U=U_*(x)$, $b=(U-1)/2$, and

$$
Q_x(r)=r^2-\frac{U+1}{2}r+b(xU-b).
$$

Put

$$
\begin{aligned}
A&=45x^4+66x^3-78x^2-25x+20,\\
B&=45x^4+67x^3-75x^2-23x+20,\\
Q&=23x^3+46x^2-15x-20.
\end{aligned}
$$

Then $Q_x(0)=QA/D^2$, $Q_x(1)=QB/D^2$, and
$U-1=-2Q/D$. Exact signed Sturm remainders give the positive root boxes

$$
a_1\in(4719/10000,4720/10000),\quad
b_1\in(5452/10000,5453/10000),\quad
b_2\in(6627/10000,6628/10000),\quad
a\in(7008/10000,7009/10000).
$$

Here $A$ has its second positive root in
$(7613/10000,7614/10000)$. The variations at $0,+\infty$ of the signed
Sturm chains of $A,B,Q$ are $(2,0),(2,0),(1,0)$. The cubic
$Q_3=24x^3+49x^2-13x-20$ has variations $(1,0)$ and its sole positive
root in $(6640/10000,6641/10000)$.
Use $S_0=P,S_1=P',S_{i+1}=-\operatorname{rem}(S_{i-1},S_i)$
and omit zeros in the sign variation. Each listed box has variation drop
one. For $x>0$, $U>1$ is exactly $0<x<a$. On $(0,a_1)$ both
$Q_x(0)$ and $Q_x(1)$ are negative, so convexity excludes a zero
between them. On $(a_1,b_1)$ and $(b_2,a)$, $Q_x(0)>0>Q_x(1)$;
there is exactly one zero in $(0,1)$ and the other is $>1$.
On $(b_1,b_2)$ both endpoint values are positive and $U>3$ makes
$Q_x'(r)=2r-(U+1)/2<0$ on $(0,1)$, so no strict root occurs.
At $a_1,b_1,b_2$ only the endpoint root can enter; the other is
outside $(0,1)$. At $a$ one has $b=0$. Thus all endpoints are excluded.

The complete strict source locus is exactly
$(a_1,b_1)\cup(b_2,a)$; each $x$ there has one strict root of $Q_x$,
the other root being $>1$. All these sources have $x<3/4$.
Every singular source admits a zero-drift lift by O, Theorem 2.1,
so would have $x>160/211$ by the preceding argument. Hence the arcs
have $\Lambda\ne0$, their parent lift is unique and its drift is nonzero.
This also proves uniqueness of the whole world at fixed $x$ on the arcs.
Let $P(x)$ be the fifth-$M$ response after
the displayed source reconstruction. In the quadratic field
$\mathbb Q(x)[r]/(Q_x)$, write its unique remainder as $c(x)+a(x)r$, and let $H$ be the
monic squarefree lcm of the reduced denominators of these two coefficients.
Let
$N_t$ be the monic squarefree numerator of the determinant of multiplication by
$P+t$. At the rational endpoints
$(4719,5453,6627,7009)/10000$, in this order, the exact
Sturm variations are

$$
\deg H=21,\quad V_H=(6,6,5,5),\quad
\deg N_0=23, V_{N_0}=(8,8,8,8),\quad
\deg N_{150}=24, V_{N_{150}}=(6,6,5,5).
$$

Hence $P\in(-150,0)$ on the first arc and $P>0$ on the second, as
shown by the exact samples

$$
P(1/2)=\frac{10179984-26282025\sqrt2}{292969}\in(-150,0),\quad
P(2/3)=\frac{5664215413800+32423788800\sqrt{157}}{94001117687}>0.
$$

At a positive-$p$ base the unique positive root of $F_0$ prevents two
F0-worlds. If $p<0$ supplied two roots $u,w<3/4$, the third root $t$
would be positive, with $uwt=32/27$. Since $u,w<3/4$,

$$
t(1+u+w)=\frac{32}{27}\left(\frac1{uw}+\frac1u+\frac1w\right)
>\frac{32}{27}\left(\frac{16}{9}+\frac83\right)=\frac{1280}{243}.
$$

Vieta would therefore give

$$
p=-\frac{45}{2}(u+w+t+uw+ut+wt)-\frac{295}{6}<-\frac{9055}{54}<-150,
$$

contradicting the first-arc bound. Thus the nonzero-drift F0 branch also has
at most one world at each base.

It remains to compare F0 worlds with singular worlds. The singular source
has $b=1/8$ and $r$ a strict root of

$$
\Phi(r)=438272r^4-931328r^3+540800r^2-50728r-853.
$$

The two strict roots lie in
$(134815/10^6,134816/10^6)$ and $(902449/10^6,902450/10^6)$. At either
root $p$ fixes $e=d-24=(p-24)/A_5$, so a singular world is fixed by its
base. Its two affine base lines have different slopes. Their only common
base satisfies

$$
1651/100<p_*<1653/100,\qquad 9687/100<v_*<9693/100,\qquad
-15<f_{MM}(S_-)-f_{MM}(S_+)<-14,
$$

These bounds follow by refining each strict root by sign bisection to
$(134815875067,134815875068)/10^{12}$ and
$(902449681772,902449681773)/10^{12}$, respectively. Substitution
into the affine formulas below gives slope difference in
$(-1729027,-1729026)/10^6$, intersection $p$ in
$(16521341,16521342)/10^6$, intersection $v$ in
$(96900546,96900547)/10^6$, and $M$-difference in
$(-14827251,-14827250)/10^6$.
Thus singular worlds are terminal-$M$ separated.

For completeness, the cross-family calculation is performed in
$K=\mathbb Q[\theta]/(\Phi(\theta))$. The quartic is irreducible modulo
$7$: its monic reduction is ([1,4,4,4,4]), and the reductions of
$X^{49}$ and $X^{2401}$ are respectively $X^3+X^2+X+5$ and (X),
with the required gcd tests equal to one. Put

$$
b_s=1/8, U_s=5/4, T_s=9/8, j_s=1/8+8\theta(1-\theta), n_s=j_s+\theta, x_s=n_s/U_s,
$$

and define $A_5,a_6,a_7,k,c,M_{0s},M_{1s}$ by

$$
\begin{gathered}
A_5=1+(n_s+U_s)(4-15/j_s+20/T_s-10/n_s),\\
a_6=50-36/j_s-20/n_s,\quad a_7=284/3-70/j_s-35/n_s,\\
k=\frac{1+(2U_s+n_s)a_6}{A_5},\quad
c=24+24(2U_s+n_s)-24k,\\
M_{0s}=24+\frac{384}{5}(3U_s+2n_s),\quad
M_{1s}=\frac{1+(3U_s+2n_s)a_7}{A_5}.
\end{gathered}
$$

The singular response is $v_s(p)=c+kp$ and
$m_s(p)=M_{0s}+M_{1s}(p-24)$. Write

$$
F_0(x,p,c+kp)=\ell(x)p+c_\ell(x),
$$

$$
\ell=(-18+5k)x^2+(-36+5k)x,\quad
c_\ell=405x^3+(975+5c)x^2+(90+5c)x-480.
$$

The gcd of $\ell,c_\ell$ in $K[x]$ is $1$. Thus an actual common
base has $\ell\ne0$ and $p=P_N/P_D$ with the fixed normalization
$P_N=-c_\ell$, $P_D=\ell$. Put

$$
\begin{gathered}
W=DP_D,\quad \zeta_3=24(x+1)(x+2)P_D,\quad \zeta_4=18W,\\
\zeta_5=x(x+2)P_N,\quad \zeta_6=x(x+1)(cP_D+kP_N),\\
A_1=10\zeta_3-20\zeta_4+15\zeta_5-4\zeta_6,\quad
A_2=4\zeta_3-6\zeta_4+4\zeta_5-\zeta_6,\\
A_7=-\zeta_3+4\zeta_4-6\zeta_5+4\zeta_6,\quad
S_M=M_{0s}P_D+M_{1s}(P_N-24P_D).
\end{gathered}
$$

In the zero-drift branch let

$$
\begin{gathered}
u=5A_2,\quad t=294W-5A_2,\quad z=xA_1-24W,\\
L_s=4u^2z^2-2(u+t)uzA_1+(u-t)((2x-1)u+t)A_1^2,\\
M_s=(2x+3)A_7-DS_M.
\end{gathered}
$$

Every legal companion with $d=0$ satisfies $L_s=M_s=0$.
In the nonzero-drift branch put $c_0=45x^3+89x^2-32x-40$, $N=-c_0$,
and

$$
\begin{gathered}
C_1=(20x^3+39x^2-16x-20)P_D,\quad
C_2'=(6x^3+11x^2-7x-8)P_D,\\
C_7=-(4x^3+9x^2-3x-2)P_D,\\
C_N=5(N+D)A_2-294NW,\quad C_D=5(N+D)C_2'+10NW,\\
B_1=A_1C_D-C_1C_N,\quad B_7=A_7C_D-C_7C_N,\quad
Z=xB_1-(24C_D+C_N)W.
\end{gathered}
$$

The clock-two equation forces $d=-C_N/C_D$. Its denominator is
$C_D=-10P_DL_6$, where

$$
L_6=177x^6+724x^5+542x^4-742x^3-629x^2+196x+160.
$$

The Sturm variations at $0,+\infty$ are $(1,1)$, so $L_6$ has no
positive root. Define

$$
\begin{aligned}
L_F&=4N^2Z^2-2N(N+D)ZB_1+(N-D)((2x-1)N+D)B_1^2,\\
M_F&=-C_NW+(2x+3)B_7-DS_MC_D.
\end{aligned}
$$

Every legal nonzero-drift companion satisfies $L_F=M_F=0$.
Exact polynomial division in $K[x]$ gives common divisors
$D(x-x_s)$ for $(L_s,M_s)$ and $D\ell$ for $(L_F,M_F)$, with zero
remainders. After making each cofactor monic, the degrees and nonzero
specialized resultants are

| pair | cofactor degrees | resultant at $101,\theta=53$ |
|---|---|---|
| $L_s/[D(x-x_s)],M_s/[D(x-x_s)]$ | $(18,2)$ | $46$ |
| $L_F/(D\ell),M_F/(D\ell)$ | $(29,9)$ | $39$ |
| monic $\ell,c_\ell$ | $(2,3)$ | $9$ |

For each row, polynomial remainder is computed in $K[x]$, reducing
$\theta$ modulo the displayed $\Phi$; the chosen $P_N,P_D$ are retained
without scaling until the cofactors are made monic. These conventions fix
the input polynomials and every normalization in the table.
For the last row the descending arrays are $(1,6,0)$ and
$(1,47,71,25)$. The specialization satisfies $\Phi(53)=0$ modulo $101$;
all coefficient denominators and displayed leading degrees survive.
Each nonzero residue proves the corresponding characteristic-zero
cofactor resultant is nonzero. These are exclusion certificates,
not finite-field legal witnesses.

Actual worlds have $D>0$, $P_D=\ell\ne0$, and in the zero-drift
branch $H_1>0$ and $2C_2-H_2>0$. In the nonzero branch
$C_D\ne0$ by the $L_6$ certificate. Thus its entire gcd $D\ell$ is
guarded out. A zero-drift common root must have $x=x_s$.
The field element $c_0(x_s)+U_sD(x_s)$ is nonzero (its residue is $16$
at this same specialization). Applying
$2F_0=d(c_0+UD)$ to the singular world forces its drift also to be
zero. F, Lemma 30.2, then identifies the whole worlds.
No distinct cross-family terminal-$M$ pair survives.

The three cases prove injectivity on $E(p,v)$. A terminal-$M$ pair must
therefore be mixed with $C(p,v)\setminus E(p,v)$, or lie wholly in that
ordinary complement. This is a restriction on the original joint problem,
not an exclusion of the whole child. ∎

## 4. The all-world carrier and the zero-drift finite outer set

**Theorem 4.1 (Every legal world lies on the F resultant carrier).** Let
(R(x,p,v)) be the uniquely normalized polynomial of F, $31.8$, determined by

$$
\det\mathsf S=16D^8F_0^2R,\qquad
\deg_xR=18,\quad\deg_pR=6,\quad\deg_vR=6,
$$

where $\mathsf S$ is the fixed six-by-six Sylvester matrix of (f,k), with
rows $d^3f,d^2f,df,f,dk,k$ as in F, $31.6$.
Every $W\in C(p,v)$ satisfies $R(x(W),p,v)=0$, including $d=0$,
$F_0=0$, and $\Lambda=0$.

**Proof.** On a regular strict source with $F_0\ne0$, the faithful equations
give $f=k=0$. Since $D>0$, the displayed determinant forces $R=0$.
The pullback of $F_0$ to the regular source surface is not identically zero:
at $r=1/2,b=1/4$, it has

$$
x=7/6,\qquad p=19224/515,\qquad v=464403/2575,\qquad
F_0=5736351/4120\ne0.
$$

Consequently the $F_0=0$ locus has empty interior in each regular source
neighbourhood. Continuity of the polynomial $R$ extends $R=0$ from its
complement to every regular point, including zero drift and $F_0=0$.

At a singular point, the complete singular-source theorem gives $b=1/8$,
$e=d-24\ne0$, and $r$ a strict root of $\Phi$. The discriminant of
$\Phi$ is

$$
3648425367354069653778543411200\ne0.
$$

Thus $\Lambda_r\ne0$. The parent equation
$e\Lambda+(24/5)(b-1/8)\kappa=0$ has nonzero $r$-derivative there, so the
implicit-function theorem gives strict regular worlds with $b\ne1/8$ tending
to the singular world, with the fixed-node interpolant varying continuously.
Their $p$-coordinate stays off $24$ locally. The already proved regular
identity $R=0$ therefore passes to the singular limit. ∎

**Definition 4.2 (The zero-drift carrier).** Put $a_i^0=a_i(x,0)$, where
$a_i$ are the denominator-free forms in F, (31.3), and set

$$
u=5a_2^0,\quad t=294D-5a_2^0,\quad z=xa_1^0-24D,
$$

$$
L_0=4u^2z^2-2(u+t)uz\,a_1^0+(u-t)((2x-1)u+t)(a_1^0)^2.
$$

Define $Q_{10}\in\mathbb Z[p,v]$ by the exact primitive identity

$$
\operatorname{Res}_x(F_0,L_0)
=-112844396298240000000000\,p^4v^4Q_{10}(p,v).
$$

The normalization is primitive, with $66$ monomials, total degree $10$,
and $v$-leading coefficient $-250000$.

**Theorem 4.3 (Finite outer restriction when a chosen label has zero drift).**
$Q_{10}$ is irreducible over $\mathbb Q[p,v]$. Every legal zero-drift
world satisfies $Q_{10}(p,v)=0$ and $R(x,p,v)=0$, including the axes
$p=0$ or $v=0$. With the exceptional-inclusive quotient relation below, the joint bases of
all four-label configurations in which at least one chosen label has $d=0$
are contained in the finite set
$Z=V_{\mathbb C}(Q_{10},E_0N_J,E_0N_M)$, with $E_0,N_J,N_M$
defined in the proof. This includes $V(Q_{10},E_0)$.
This set has not been real-filtered,
so the theorem is neither a witness nor an exclusion.

**Proof.** At $d=0$, $F_0=0$ is $H_0=0$, and for $x>0$ it gives

$$
v=\chi(x,p)=-\frac{3(x+2)(135x^2+55x-80-6px)}{5x(x+1)}.
$$

The full strict chart is
$p\ne24,t\ne0,a_1^0\ne0,U=u/t>1,b=(U-1)/2,j=24UD/a_1^0,
r=xU-j,0<r<1$, together with $L_0=0$. The exact clearing identity is
$$
4t^2(a_1^0)^2\bigl(r^2-(1+b)r+b(xU-b)\bigr)=L_0.
$$
Thus, without dividing by a response coordinate, these guards
are equivalent to the whole-world reconstruction. Substitution into $L_0$
gives

$$
L_0(x,p,\chi)=\frac{36(x+2)^4}{25}L(x,p),
$$

where $L$ has $p$-degree $4$ and $x$-degree $10$. Exact division
also gives polynomials $T,S\in\mathbb Z[x,p]$ with

$$
625x^{10}(x+1)^{10}Q_{10}(p,\chi)=-6561LT,\qquad
25x^6(x+1)^6R(x,p,\chi)=9LS,
$$

where $T$ has degrees $(p,x)=(6,20)$, $105$ monomials, and $S$ has
degrees $(2,24)$, $69$ monomials. No division by $p$ or $v$ occurs;
the factors $p^4v^4$ only clear the forbidden $x=-1,-2$ factors. Hence
every legal zero-drift label satisfies both carriers, including on either axis.

For irreducibility, specialize $p=2$ modulo $101$. The monic descending
coefficient array is

$$
(1,2,97,46,64,84,58,56,42,78,35).
$$

In ascending powers of $v$, the remainders of $v^{101^2}$ and
$v^{101^5}$ are respectively

$$
(90,21,97,91,89,85,63,3,69,67),\qquad
(30,65,3,100,13,55,5,43,0,31).
$$

The finite-field criterion used here is the classical degree-$10$
criterion of M. O. Rabin, “Probabilistic algorithms in finite fields”,
SIAM Journal on Computing 9, pp. 273–280,
[doi:10.1137/0209024](https://doi.org/10.1137/0209024).
Its prime-divisor exponents are $10/5=2$ and $10/2=5$.
The Rabin tests give $v^{101^{10}}=v$ modulo the specialization and gcd
one with each of the two displayed prime-divisor tests. The specialization is
therefore irreducible of degree ten. Since the $v$-leading coefficient of
$Q_{10}$ is the nonzero constant $-250000$, a factorization over
$\mathbb Q[p,v]$ would specialize to a nontrivial factorization. Thus
$Q_{10}$ is irreducible. The real zero-drift family is nonempty:
O, Theorem 4.2, gives strict singular sources with $A_5<0$.
The choice $e=-24$ gives $d=0$ and $p=24-24A_5>24$.
The parent derivative in Theorem 4.1 also yields a strict zero-drift arc.

For the finiteness assertion, finite-algebra evaluation separates
complex candidates from guarded real labels. Gaillard–Safey El Din,
Problem 1 and Theorem 2.4,
[primary text](https://arxiv.org/html/2402.07782v2),
has a dense-parameter scope and does not cover our exceptional strata.
Here all such strata are retained explicitly. Work in
$A=\mathbb Q(p,v)[x]/(R/\rho)$, where $\rho=[x^{18}]R$, and use
adjugates of multiplication matrices for every inverse. With
$\delta=-\beta/\alpha$, put

$$
H_i=a_i(x,\delta)/D,\quad B_0=294/5-2\delta-H_2,\quad
C_0=\delta^2+B_0^2,\quad N_0=-\delta H_0+B_0H_2.
$$

Define

$$
\tau_M=\delta+(2x+3)H_7,\qquad
\tau_J=\delta+\left(4x+\frac12+\frac{C_0}{2N_0}-\frac{2(24-\delta)}{H_1}\right)H_7.
$$

Let $E_0$ be the primitive squarefree product of $\rho$,
$\operatorname{Disc}_x(R)$, the reduced numerators and denominators of the
quotient-algebra norms of $\alpha,D,H_1,C_0,N_0$, the reduced coefficient
denominators of $\delta,H_0,H_1,H_2,H_7,C_0,N_0,\tau_J,\tau_M$
and of the two determinants with columns $1,\tau_E,\ldots,\tau_E^{17}$. Constant factors are omitted.
Neither $d=0$, $F_0=0$, $\beta=0$, nor $H_0=0$ is inserted as an
exception by definition. Let $N_J,N_M$ be the primitive reduced integer
numerators of these two determinants. For these reduced scalar rational
functions, cancel the polynomial gcd over $\mathbb Q[p,v]$, clear rational
scalar denominators and remove integer content. Scalar sign is chosen by
positive lexicographic leading coefficient in $(p,v)$ for $E_0,N_J,N_M$;
the zero sets and nondivisibility statements are independent of that sign.
$Q_{10}$ keeps its different, explicitly prescribed resultant normalization.

If $E_0(p,v)\ne0$, Theorem 4.1 and the pseudo-remainder identity give
$d=\delta(x)$ for every actual world, and the faithful reconstruction makes
distinct worlds have distinct $x$. For an action $E$, evaluation at the eighteen simple $R$ roots
is invertible. If two distinct actual worlds have the same terminal
response, the power matrix of their two evaluation rows is dependent;
the corresponding determinant vanishes. Equivalently use the
Vandermonde quotient in Theorem 2.2. Thus
$D_E\subset V(E_0N_E)$, and
$D_J\cap D_M\subset V(E_0)\cup V(N_J,N_M)$.
On $E_0=0$ this is only an outer condition; the full guarded $(x,d)$
system and its squared-distance distinctness remain in force. The exact modular certificate at
$101,p=88,v=55$ uses the monic $R$ and the following ascending arrays:

$$
\begin{aligned}
R&=(80,70,65,27,78,18,49,25,4,22,43,61,75,19,75,42,67,62,1),\\
\delta&=(72,10,12,90,85,49,24,26,56,0,80,27,94,8,44,96,47,54),\\
\tau_J&=(84,93,91,27,62,78,67,35,63,65,74,82,45,84,18,66,59,68),\\
\tau_M&=(87,37,26,78,31,5,98,88,97,31,85,59,92,7,18,60,94,10).
\end{aligned}
$$

Here $\rho=13$, the two indices are $39,59$, the five relevant gcd
degrees are all zero, and

$$
Q_{10}=0,\quad
(\operatorname{Norm}\alpha,\operatorname{Norm}D,\operatorname{Norm}H_1,
\operatorname{Norm}C_0,\operatorname{Norm}N_0)=(9,13,14,100,71),
$$

with monic discriminant $32$. The defining remainders of $f,K$, the
two clock equations, the source-rank equation, $R(18)$, and $\delta(18)$
are zero; $F_0(18,88,55)=0$, $\operatorname{Norm}\beta=0$, while
$\operatorname{Res}_x(F_0,\alpha)=35$. Thus the robust $C_0,N_0$ chart is
regular even at this zero-drift point.

For this table the discriminant $32$ is for the monic $R$;
the raw F31 normalization has discriminant $50$, also nonzero.
At this specialization $\rho$ and all five inversion norms are units,
as are $2,5$. Every inverse is its prescribed adjugate divided by
one of these norms, so all coefficient denominators used in $E_0$
are units. The norm numerators are units too. Primitive reduction and
squarefree extraction cannot add a vanishing factor. Therefore the
entire defined $E_0$ is nonzero here. The two primitive reduced index
numerators are also nonzero. If $Q_{10}$ divided one of these integer
polynomials over $\mathbb Q$, Gauss' lemma would give integer polynomial
divisibility and its reduction would vanish at this $Q_{10}$ point.
The certificate consequently proves that $Q_{10}$ divides none of
$E_0,N_J,N_M$.
Since $Q_{10}$ is irreducible, $Q_{10}$ and $E_0N_J$ are coprime, so

$$
I_0=\langle Q_{10},E_0N_J,E_0N_M\rangle
$$

has finite complex zero set: two coprime plane polynomials have no
common curve component and have finite affine intersection.
Set-theoretically this set is
$V(Q_{10},E_0)\cup V(Q_{10},N_J,N_M)$. Its exceptional
intersections have not been deleted. Every joint configuration with a chosen
zero-drift label has its base in this finite outer set. The modular label
$x=18$ is not a real legal source (it came from $r=2,b=55$ in $\mathbb F_{101}$); it is used only to prove nondivisibility. Real isolation
and all strict guards remain to be checked. ∎

## 5. Consequences and the remaining boundary

**Proposition 5.1 (What the three results imply).** The common regular index
zero of Theorem 2.2 is removed from the actual joint images. Theorem 3.2
forces every terminal-$M$ collision to use at least one ordinary-complement
world, while Theorem 4.1 places every legal world on the exact F carrier.
Theorem 4.3 reduces the branch with a zero-drift chosen label to the finite
outer set $V(I_0)$. None of these statements removes mixed pairs, ordinary
pairs, the remaining regular common components, or any $E_0=0$ stratum.

**Proof.** The first assertion is the exact three-world enumeration and
response separation in Theorem 2.2. The second is the contrapositive of
injectivity on $E(p,v)$. The third and fourth are the carrier and ideal
containment proved in Theorems 4.1 and 4.3. Each conclusion is at one fixed
acquired $(p,v)$; no worlds from different children are combined. ∎

**Definition 5.2 (Residual strict-real incidence problem).** The residual
problem is to decide the real guarded points of $D_J\cap D_M$ over all $p\ne24,v$, or prove that none
exist. On $E_0\ne0$, this requires the common components and isolated points
of $V(N_J,N_M)$ followed by full strict-real lifting. On $E_0=0$, it
requires the zero-safe reconstruction, including singular sources, zero drift,
repeated roots and unbounded positive off-diagonals. Every claimed pair must
retain
$(x_0-x_1)^2+(d_0-d_1)^2>0$ within the $J$ pair and the analogous
strict inequality within the $M$ pair, with one whole polynomial $g$
per label. For the zero-drift branch, within-pair relabelling gives
$d_{J0}=0$ or $d_{M0}=0$. No cross-pair distinctness is required.

A positive point would still be only one sixth-$M$ child. The sixth-$J$
condition at the same fifth response $p$, the fifth-$J$ and common-parent
conditions, and the ancestor obligations remain necessary before any $H_4$
$L_3$, root $L_7$, or eight-versus-nine conclusion.

## 6. Supplier assumptions and mathematical attribution

**Assumption 6.1 (Scoped supplier interpretation).** In the theorems above,
O and F have the meanings and transferred scopes in the following table.

| Source | Exact use and boundary |
|---|---|
| O, *FIB common-parent geometry and two exact mixed children*, Definitions 1.1–1.3, Sections 2, 4, 9, 17, 29 | `repo-derived`: parent, literal history, strict source domain, singular-source classification, and ancestor meanings. Its $p=24$ child is not used as an off-$24$ witness. |
| F, *FIB all-response finite-fibre geometry*, Sections 30–33 | `repo-derived`: faithful $(x,d)$ reconstruction, $f,k,F_0,R$, the fixed determinant normalization, and the uniform 24-world bound. The present results add the three scoped arguments and do not reprove that bound. |
| Berrut and Trefethen, “Barycentric Lagrange Interpolation”, §2, [PDF](https://people.maths.ox.ac.uk/trefethen/barycentric.pdf) | `literature-attested`: uniqueness of interpolation at distinct nodes. No nonzero-sample or exact-degree premise is imported. |
| Moreno Maza, “The resultant”, Definitions 4 and Propositions 5–7, [notes](https://www.csd.uwo.ca/~mmorenom/AM583/Lectures/ResultantGcd.html/node3.html) | `literature-attested`: Sylvester determinant and specialization use. It supplies no FIB-specific converse. |
| Lazard and Rouillier, “Solving Parametric Polynomial Systems”, Definition 1, Theorem 1 and real-case Remark 1, [report](https://inria.hal.science/inria-00070678/document) | `literature-attested`: separation of critical, nonproper and inequation boundaries; exceptional real sheets must still be treated explicitly. |
| Gaillard and Safey El Din, “Solving parameter-dependent semi-algebraic systems”, Problem 1 and Theorem 2.4, [arXiv](https://arxiv.org/html/2402.07782v2); Le and Safey El Din, Corollary 11, [arXiv](https://arxiv.org/html/2011.14136v2) | `literature-attested`: finite-algebra sign filtering and dense-parameter specialization. Their hypotheses do not decide this joint incidence or cover exceptional strata automatically. |
| Nuno-Ballesteros and Penafort-Sanchis, “Multiple point spaces of finite holomorphic maps”, Definition 2.1 and Example 2.2, [arXiv](https://arxiv.org/html/1509.04990v2) | `literature-attested`: a diagonal limit is not a distinct multiple point. Their holomorphic stability assumptions are not transferred. |
| The three scoped strict-real statements in Sections 2–4 | `repo-derived`: the source-specific deductions proved here; the classical tools remain attributed to their sources. |

**Assumption 6.2 (Classical tools and source-specific scopes).** The distinct-node
interpolation in Definitions 1.1 and 2.1 uses the conditions in the
Berrut–Trefethen citation above, with no sampled-value or degree-three
condition. The fixed Sylvester determinants use the cited construction
over their displayed coefficient rings, with nonzero denominators checked
before specialization. The rational contractions apply the classical
contraction theorem on the closed displayed boxes; the nonzero source
and collision Jacobians are the hypotheses of the implicit-function
theorem. The sign and multiple-point literature motivates retaining the
strict guards and exceptions; none supplies a FIB-specific incidence theorem.

## 追加锚（本行以下为增补区）
