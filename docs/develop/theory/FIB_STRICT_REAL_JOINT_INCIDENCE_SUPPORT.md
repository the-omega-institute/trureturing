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

## 7. The source at infinity and bounded collision endpoints

**Definition 7.1 (The analytic source coordinates).** All worlds, histories,
clocks and guards in Definition 1.1 remain in force. Throughout the
following sections $K=4k$, so the fixed F31 identity reads

$$
\operatorname{Res}_d(f,K)=256D^8F_0^2R.
$$

The forms $a_i$ and the polynomial pseudo-remainder $\alpha d+\beta$
retain their exact definitions in Section 2. Write

$$
e=d-24,\qquad
\eta=-\frac{24}{5}(b-1/8)\kappa,\qquad
\kappa=\frac6T-\frac2U.
$$

The full parent equation of O, Theorem 2.1, is $e\Lambda=\eta$.
At a regular source its one whole gain is the interpolant of

$$
(g_0,g_1,g_2,g_3)
=\left(-24-e,-\frac e j,\frac{27/5-e}{T},-\frac e n\right).
$$

This is an invocation of the full parent converse, including its
nonzeroness argument from the unequal original readings. It does not
assume that any particular gain sample is nonzero.

Put $t=1/b,w=r/b$. The strict source domain becomes $t>0,0<w<t$,
and the exact rational substitutions are

$$
j=\frac{1-w^2+wt}{t},\quad
n=\frac{1+w-w^2+wt}{t},\quad
T=\frac{1+t}{t},\quad U=\frac{2+t}{t}.
$$

In these substitutions the regular parent formula, and then all four
responses $(p,v,a,m)=(p,u_M,f_{MJ},f_{MM})$, extend analytically to an
open neighbourhood of $(t,w)=(0,0)$. Indeed $\Lambda(0,0)=1$ and
$e(0,0)=-24$. At $t=0$ the extended expression for $e$ is identically
$-24$ for all small $w$, so $d=24+e$ is divisible by $t$ in the local
analytic ring. Every displayed $g_i$ is likewise $t$ times an analytic
function. Interpolation preserves this divisibility, and the continuation
traces are $1/t$ times analytic functions. Thus their products have no
pole. The other denominator factors have nonzero values at the origin:
$1+t,2+t,1-w^2+wt,1+w-w^2+wt$ and $\Lambda$.

Direct substitution and first differentiation give

$$
(p,v,a,m)(0,0)=
\left(-\frac{216}{5},-225,-\frac{1224}{5},-\frac{3264}{5}\right),
$$

$$
\frac{\partial(p,v,a,m)}{\partial(t,w)}(0,0)=
\begin{pmatrix}
-2238/5&2088/5\\
-13293/5&2355\\
-18558/5&14568/5\\
-49569/5&42384/5
\end{pmatrix},\qquad
\det\frac{\partial(p,v)}{\partial(t,w)}=\frac{1403334}{25}\ne0.
$$

These entries can also be obtained by applying the extrapolation weights
of Definition 2.1 to the four samples above, followed by multiplication
by the original traces. In particular, uniformly for $0\le r\le1$,

$$
\begin{aligned}
p(r,b)&=-216/5+\frac{2088r-2238}{5b}+O(b^{-2}),\\
v(r,b)&=-225+\frac{11775r-13293}{5b}+O(b^{-2}).
\end{aligned}
$$

Uniformity follows by substituting $w=rt$ into an analytic function on
a fixed neighbourhood of the origin and using compactness of $[0,1]$.
Also $j,n\ge b$ gives $\Lambda\ge1-8/b$, so sufficiently large $b$
is regular without a source cutoff assumption. The inverse-function
theorem gives a neighbourhood of the origin on which $(t,w)\mapsto(p,v)$
is injective. All sufficiently large-$b$ strict sources lie in that
neighbourhood. These analytic coordinates are not acquired labels.

**Lemma 7.2 (A zero-safe limiting terminal filter).** Put
$q_\infty=(-216/5,-225)$ and use the $f,K=4k,F_0,R,a_i,\alpha,\beta$
of Sections 2–4 with their fixed F31 normalization. At this base, a finite
common label of $f=K=0$ with $x>0$ and either limiting terminal equality
must have $(x,d)=(1/2,0)$. That label is not an actual world.

**Proof.** Before specializing, set

$$
\begin{gathered}
a_7=-z_3+4z_4-6z_5+4z_6,\\
B_c=(294/5-2d)D-a_2,\quad C_c=d^2D^2+B_c^2,\quad
N_c=-dDa_0+B_ca_2.
\end{gathered}
$$

On every actual off-$24$ world, $a_1\ne0$, $C_c>0$ and
$N_c=UC_c>0$. The reconstruction gives the exact terminal identities

$$
\begin{aligned}
f_{MM}&=d+(2x+3)a_7/D,\\
f_{MJ}&=d+\left(\frac{1+8x}{2}+\frac{C_c}{2N_c}
                  -\frac{2(24-d)D}{a_1}\right)a_7/D.
\end{aligned}
$$

For the second, substitute $r=xU-j$, $T=(U+1)/2$,
$j/U=(24-d)/H_1$ and $1/U=C_c/N_c$ in the original trace.
At $q_\infty$ define the cleared polynomials

$$
\begin{aligned}
A_M&=D(d+3264/5)+(2x+3)a_7,\\
A_J&=2N_ca_1D(d+1224/5)\\
&\quad+\bigl((1+8x)N_ca_1+C_ca_1-4(24-d)DN_c\bigr)a_7.
\end{aligned}
$$

Thus each corresponding terminal equality implies $A_E=0$ without
cancelling drift or a gain sample. The same polynomial implication holds
under finite limits of actual labels.

Write $R^*=R(x,q_\infty)$. Its leading and constant coefficients are

$$
[x^{18}]R^*=225903042784485417600,\qquad
R^*(0)=1274988457855659470400.
$$

It is divisible by $2x-1$, and

$$
F_0(x,q_\infty)=405x^3+(3138/5)x^2+(2601/5)x-480,
\qquad F_0(1/2,q_\infty)=-99/8.
$$

Let $\operatorname{pp}$ clear rational denominators and remove integer
content, with positive leading coefficient, and form

$$
Q=\operatorname{pp}\left(\frac{F_0(x,q_\infty)R^*}{2x-1}\right),
\qquad S_E=\operatorname{pp}\operatorname{Res}_d(f,A_E).
$$

The degrees are $20,13,47$ for $Q,S_M,S_J$. Both $S_E$ vanish at
$1/2$. Here is an exact coprimality certificate modulo $101$; all arrays
in this paragraph are in ascending powers of $x$. The monic $Q$ is

$$
(77,15,90,49,32,28,0,76,13,37,92,29,2,46,67,69,13,36,61,5,1).
$$

The remainders of $S_M,S_J$ modulo this polynomial are

$$
(0,0,32,83,43,22,31,100,31,76,54,68,66,9),
$$

$$
(90,17,35,16,39,32,76,58,71,26,63,28,68,92,57,85,21,20,18,23).
$$

The leading coefficients of the unreduced $S_M,S_J$ are $9,21$ modulo
$101$, and the resultants with monic $Q$ are $40,29$, respectively.
The degrees survive reduction, so these nonzero residues prove
$\gcd(Q,S_E)=1$ in characteristic zero. A finite common $f,K$ root
with $x>0$ lies on $F_0^2R^*=0$ by the fixed Sylvester identity.
If $A_E=0$ as well, its $x$ must therefore be $1/2$.
At that value exact specialization gives

$$
f=-\frac{15}{32}d(1435d-3327),
$$

$$
K=-\frac{3645}{512}d(4685d^3-116815d^2+147632d-40128).
$$

Their monic gcd is $d$. Hence $d=0$. Interpolation then gives
$(H_0,H_1,H_2)=(66/5,48,294/5)$. The actual equation $dU=-H_0$
is impossible for any finite $U$. This last rejection uses an original
clock equation, not an inverse of the vanishing $C_0$ at that label. ∎

**Theorem 7.3 (One uniform bound for both collision endpoints).** There
exists a finite $B_*>0$ such that, for every real $p\ne24,v$, every
$E\in\{J,M\}$ and every distinct pair $W,W'\in C(p,v)$ with
$f_{ME}(W)=f_{ME}(W')$,

$$
b(W)<B_*,\qquad b(W')<B_*.
$$

This proof requires only the necessary $F_0^2R$ carrier and the
leading-drift noncollapse of F, Lemma 31.3, rather than Theorem 4.1's
stronger all-world $R$ statement.

**Proof.** Suppose the set of such endpoints were unbounded for one
fixed action. Relabel a sequence of pairs so $b(W_i)\to+\infty$.
Definition 7.1 gives convergence of their common bases to $q_\infty$
and of their common terminal response to $-1224/5$ or $-3264/5$.
The other endpoint has $x_i>0$ and satisfies $F_0^2R=0$.
At $q_\infty$ this polynomial has nonzero constant and leading
coefficients. The elementary root bounds for a polynomial and its
reciprocal therefore keep $x_i$ in a compact subinterval of $(0,\infty)$
for all sufficiently large $i$.

The other drift $d_i$ is bounded as well. Otherwise pass to a subsequence
with $|d_i|\to\infty$ and $x_i\to x_*$. Dividing $f=0$ by $d_i^2$
and $K=0$ by $d_i^4$ gives $L_f(x_*)=4L_k(x_*)=0$.
F, Lemma 31.3, excludes this. Pass to finite limits of $x_i,d_i$.
The two necessary source polynomials and the corresponding cleared
terminal polynomial remain zero. Lemma 7.2 forces the limit to be
$(1/2,0)$, and hence $H_0\to66/5$.

The actual equation $d_iU_i=-H_{0i}$ now forces $U_i\to+\infty$:
$|d_i|U_i\to66/5$ and $U_i>1$. Thus $b(W'_i)\to+\infty$ too.
Both sources eventually lie in the injective analytic source
neighbourhood of Definition 7.1 and have identical $(p_i,v_i)$.
They have identical sources. There $\Lambda\ne0$, so O, Theorem 2.1,
also makes their drifts and entire gains identical. This contradicts
within-pair distinctness. The endpoint sets for each of the two actions
are bounded; take a common bound and enlarge it to obtain the strict
inequalities stated. No numerical value of $B_*$ is supplied. ∎

**Theorem 7.4 (Empty limiting child and a whole-child singleton
neighbourhood).** The entire child $C(-216/5,-225)$ is empty. There is
an open real neighbourhood $\mathcal U$ of $q_\infty$, contained in
$p\ne24$, such that every entire $C(p,v)$ over $\mathcal U$ has at
most one complete world. Consequently there is $B_0>0$ such that every
complete $H_4$ world with $b>B_0$ has a singleton acquired sixth-$M$
child.

The stronger assertion uses Theorem 4.1 for every actual world, including
$F_0=0$, zero drift and $\Lambda=0$, as well as F's faithful reconstruction.
It is not inferred from injectivity on one regular source sheet.

**Proof.** Specialize $\alpha,\beta$ at $q_\infty$ as well. Let $R_z,A_z$
be the primitive integer versions of $R^*,\alpha^*$ with positive leading
coefficient. Their degrees modulo $101$ remain $18,32$ and

$$
\operatorname{Res}_x(R_z,A_z)=50,\qquad
\operatorname{Res}_x(R_z,R_z')=44\pmod {101}.
$$

Thus $R^*$ is squarefree and $\alpha^*$ is a unit at all its roots.
The pseudo-remainder identity of Section 2 fixes the only possible drift
as $-\beta^*/\alpha^*$, even if the quadratic coefficient of $f$ vanishes.
For $G=R^*/(2x-1)$ the signed Sturm sequence
$G,G',-\operatorname{rem}(G,G'),\ldots$ has variations $8$ at zero and
$5$ at positive infinity. Its three positive roots are isolated as follows.
All finite decimal endpoints in this and subsequent tables are exact
rationals.

| $x$ interval | $d$ interval | $r$ interval | $b$ interval | $H_1$ interval | $C_0$ interval |
|---|---|---|---|---|---|
| $(286201658,286201659)/10^9$ | $(15.710074,15.710075)$ | $(5.050258,5.050259)$ | $(3.310135,3.310136)$ | $(-23,-21)$ | $(256,258)$ |
| $(1241903126,1241903127)/10^9$ | $(27.259169,27.259170)$ | $(0.556711,0.556712)$ | $(-0.699536,-0.699535)$ | $(-2,-1)$ | $(793,795)$ |
| $(2882887525,2882887526)/10^9$ | $(18.949707,18.949708)$ | $(-0.258417,-0.258416)$ | $(-0.530518,-0.530517)$ | $(-4,-3)$ | $(854,856)$ |

For an exact evaluation rule, bisect each sign-changing rational bracket
until its width is at most $10^{-65}$, retaining its sign change.
Rational interval Horner evaluation of $\alpha^*,\beta^*$ followed by
Definition 1.1 gives the displayed enclosures. The nonzero $H_1,C_0$
intervals justify these divisions. Each row violates a strict source
guard. The only other positive $R^*$ root is $1/2$; there

$$
\alpha^*=-4859811144123638596875/8388608\ne0,\qquad\beta^*=0.
$$

Its forced drift is zero and it fails $dU=-H_0$ as in Lemma 7.2.
Theorem 4.1 and $x>0$ exhaust every possible world, so the child is empty.

The polynomial has four negative real roots, four positive real roots and
ten nonreal roots. Nonzero leading and constant coefficients, simplicity
and the $\alpha$ unit persist on a sufficiently small base neighbourhood.
The implicit-function theorem continues all eighteen roots separately.
Negative roots stay negative; roots off the real axis stay off it. On
the three rejected positive branches, $H_1,C_0$ remain nonzero, and the
strict rejection margins in the table persist. Hence every nearby actual
world must use the single branch near $1/2$, with its unique drift.
The injection $W\mapsto(x,d)$ of F, Lemma 30.2, gives at most one world
in the entire child. This argument does not invert $C_0$ on the half-root
branch, where it vanishes at the limiting base. Shrink the neighbourhood
to avoid $p=24$ and call it $\mathcal U$.

Uniform convergence in Definition 7.1 puts every sufficiently large-$b$
parent world over $\mathcal U$. Its source is regular, its whole parent
lift exists by O, Theorem 2.1, and that world belongs to the acquired child.
The child is therefore exactly a singleton. Neither a numerical $B_0$
nor a radius for $\mathcal U$ has been computed. ∎

**Corollary 7.5 (The scope of the tail removal).** The full individual-world
projection to the acquired base is nonproper and its image is not closed.
Nevertheless sufficiently large $b$ supplies no endpoint of either actual
terminal collision.

**Proof.** Take the legal regular parent worlds with $r=1/2$ and
$b\to\infty$. Their bases approach $q_\infty$, which is not in the
image by Theorem 7.4, and their matrix entry $P_{12}=b$ is unbounded.
The compact set consisting of this convergent base sequence and its limit
has a noncompact inverse image. The endpoint conclusion is Theorem 7.3.
It asserts no properness or nonproperness of either collision projection.
The bound on $b$ leaves $b\to0$, $r\to0,1$, the opposite offdiagonal,
and singular or denominator limits untreated. ∎

## 8. A mixed singular/ordinary pair and finite singular-endpoint incidence

**Definition 8.1 (Affine response coefficients).** For a strict source use
$\eta,\Lambda,e$ from Definition 7.1 and set

$$
\begin{aligned}
A_5&=1+(U+n)(4-15/j+20/T-10/n),\\
A_6&=1+(2U+n)(10-36/j+45/T-20/n),\\
A_7&=1+(3U+2n)(20-70/j+84/T-35/n),\\
K_5&=(U+n)(96-108/T),\\
K_6&=(2U+n)(240-243/T),\\
K_7&=(3U+2n)(480-2268/(5T)).
\end{aligned}
$$

The original-node interpolant of Definition 7.1 gives exactly

$$
(p,v,m)=24+(K_5,K_6,K_7)+e(A_5,A_6,A_7).
$$

For example the extrapolation weights at clock five are
$(-4,15,-20,10)$; substitution of the four gain samples yields the first
coordinate, and the clock-six and clock-seven weights yield the others.
These are responses of one whole gain and fixed drift, not three
independently chosen samples. Write $\mathcal S=\{\Lambda=0\}$ and
$\mathcal O=C\setminus E$ when a child is fixed. A singular source is
$(\theta,1/8)$ for one of the two strict roots of the $\Phi$ in Section 3.
At it $K_{5s}=0$, $K_{6s}=24(2U_s+n_s)$, and $A_{5s}\ne0$ by O,
Theorems 4.2 and 29.2. A subscript $s$ means evaluation at this source.

**Theorem 8.2 (An exact mixed pair in an entire three-world child).**
There is an exact off-$24$ base $(p^*,v^*)$ with exactly three legal
complete worlds. Its only unordered terminal-$M$ pair has one singular
endpoint and one endpoint in $\mathcal O$; terminal $J$ is injective on
the entire child. At this base $E$ contains only the singular world.
For orientation,

$$
p^*=7.2823451540532278139\ldots,\qquad
v^*=61.4934953917523253198\ldots,
$$

and the common terminal-$M$ response is
$m^*=351.0576359569134177504\ldots$.
The equations and rational boxes below, rather than these decimal
approximations, define the base.

**Proof.** With variables $(\theta,r,b)$, take the singular coefficients
at $(\theta,1/8)$ and unmarked coefficients at $(r,b)$. Define

$$
\begin{aligned}
G_1&=\Phi(\theta)/438272,\\
G_2&=\bigl[A_{5s}(K_6-K_{6s})-A_{6s}K_5\bigr]\Lambda
       +(A_{5s}A_6-A_{6s}A_5)\eta,\\
G_3&=\bigl[A_{5s}(K_7-K_{7s})-A_{7s}K_5\bigr]\Lambda
       +(A_{5s}A_7-A_{7s}A_5)\eta.
\end{aligned}
$$

Let $c$ have denominator $10^{85}$ and the three numerators

$$
\begin{gathered}
9024496817720562653778726512965428561862764994432208970726704110135602304768272095382,\\
8985464128804579764286285320828605861673266756916615038908975788924147409061131296493,\\
1301798836735591939924473343635928978897675040498100650126547073337701243975722117295.
\end{gathered}
$$

On $\|z-c\|_\infty\le10^{-75}$ use the rational preconditioner

$$
C=10^{-40}\begin{pmatrix}
-71105499762546593473552397909319503571166&0&0\\
22360556060954053941609340724224372062533570&-59932155240287489180860203660942459253512&4031350216683226377423322750781880119095\\
-29566949626909647713285426071704597647970119&80120803565884476282185112079016968485479&-5495580101268134824028947065907322164286
\end{pmatrix}.
$$

Rational interval forward differentiation, rounding every elementary
endpoint outward to a multiple of $10^{-125}$, gives

$$
\|I-CDG\|_\infty<10^{-34},\qquad
\|CG(c)\|_\infty<10^{-77},\qquad \det C\ne0.
$$

The determinant lies in $(-0.453,-0.452)$. The self-map inequality is
$10^{-77}+10^{-34}10^{-75}<10^{-75}$, so the contraction theorem gives
one exact zero in the box. Throughout it

$$
0.9024<\theta<0.9025,\quad0.8985<r<0.8986,\quad
0.1301<b<0.1303,\quad -0.028<\Lambda(r,b)<-0.027,
$$

and $A_{5s}\ne0$. All $j,n,T,U$ are positive.
The identity $\Lambda(\theta,1/8)=\Phi(\theta)/(960j_sn_s)$ makes
the first source singular without dividing by its $\Lambda$.
At the zero put

$$
e_o=\eta/\Lambda,\quad p^*=24+K_5+A_5e_o,\quad
e_s=(p^*-24)/A_{5s}.
$$

Both sources satisfy the full parent equation. The second and third
$G$ equations, divided only by $A_{5s}\Lambda\ne0$, say that their
$v$ and $m$ values agree exactly. O's parent converse constructs their
whole gains from the four original samples; each is nonzero, has degree
at most three, and uses the fixed drift $24+e_o$ or $24+e_s$ at every
clock. The distinct $b$ intervals prove that the worlds differ.

For full-child exhaustion, let the rational base centre $(p_c,v_c)$ have
denominator $10^{80}$ and numerators

$$
\begin{gathered}
728234515405322781392427523687852059030337027619922865813481904138164333636754569,\\
6149349539175232531978929063777956431989050342640124712781972803899406961927385838.
\end{gathered}
$$

The whole source box projects strictly inside
$\mathcal B=\{|p-p_c|\le10^{-65},|v-v_c|\le10^{-65}\}$;
the coordinate displacements are $<7.74\,10^{-71}$ and
$<2.93\,10^{-70}$. In particular the rectangle is off $24$.
Let $\bar R_0$ be the monic $R$ at its rational centre. The following
Gaussian-rational seeds are exact terminating decimals:

$$
\begin{gathered}
(-1.803568,0),(-1.654159,0),(-1.651605,0),(-1.454960,0),\\
(-1.363921,0),(-1.309482,0),(-0.367939,0),(0.332638,0),\\
(0.554906,0),(0.679556,-0.091281),(0.679556,0.091281),\\
(0.995981,0),(1.056543,0),(1.124004,0),(1.371826,0),\\
(1.385379,0),(1.807744,0),(3.613687,0).
\end{gathered}
$$

From each seed perform eight exact Gaussian-rational Newton steps for
$\bar R_0$, rounding each real and imaginary component after each step by
$\operatorname{Round}_{60}(u)=10^{-60}\lfloor10^{60}u+1/2\rfloor$.
Call the centres $c_i$ and put $\gamma_i=1/\bar R_0'(c_i)$.
On each complex rectangle of component radius $10^{-48}$, uniformly
for all bases in $\mathcal B$, rational interval evaluation gives

$$
|\Re(1-\gamma_i\bar R')|+|\Im(1-\gamma_i\bar R')|<10^{-30},
$$

$$
\max(|\Re(\gamma_i\bar R(c_i))|,|\Im(\gamma_i\bar R(c_i))|)<10^{-55}.
$$

Here coefficients are evaluated in increasing $(x,p,v)$ monomial order,
univariate evaluations use Horner's rule, and interval endpoints are
rounded outward to $10^{-125}$. The first displayed bound is the
operator norm for the real-imaginary sup norm. Thus each map
$z\mapsto z-\gamma_i\bar R(z)$ contracts its rectangle strictly into
itself. The rectangles are disjoint and the leading coefficient stays
nonzero, so they exhaust all eighteen roots. Conjugation and uniqueness
give seven negative roots, nine positive roots and a nonreal conjugate
pair throughout $\mathcal B$.

On every positive-root box, the quadratic coefficient $a_f$ of $f$,
$\alpha,D,d,H_1,U,C_0$ and $d-24$ exclude zero, with
$d=-\beta/\alpha$. Use these exact rational functions and the robust
formulas of Definition 1.1 for the guard evaluations. The fixed Sylvester
identity, $R=0$ and $a_f\ne0$ ensure a finite common $f,K$ root:
the fixed degree-$(2,4)$ resultant is zero, while the full quadratic
degree of $f$ excludes a common root at infinity. The pseudo-remainder fixes its
unique drift. Since $d\ne0$, $f=0$ restores the two clock equations with
$U=-H_0/d$, and $K=0$ restores the rank-one source equation. The robust
$U$ expression agrees with this one. The filtering is

| root near | strict guard outcome |
|---|---|
| $0.332638$ | $r>4.30$ |
| $0.554906$ | $b<0$ |
| $0.995981$ | $b>0,0<r<1$ |
| $1.056543$ | $b<0$ |
| $1.124004$ | $b<0$ |
| $1.371826$ | $b>0,0<r<1$ |
| $1.385379$ | $b>0,0<r<1$ |
| $1.807744$ | $b<0$ |
| $3.613687$ | $b<0$ |

All three retained boxes satisfy every equality and strict guard of
Definition 1.1. Theorem 4.1 ensures that no zero-drift, $F_0=0$ or
singular world lies outside this enumeration. Thus every child over
$\mathcal B$ has exactly three worlds, with terminal-$J$ intervals
separated as in the following table. At the constructed base their
identification and exceptional membership are

| world | root near | $r$ | $b$ | $d$ | $f_{MJ}$ | $f_{MM}$ |
|---|---|---|---|---|---|---|
| $Q$ | $0.995981$ | $(0.0484,0.0486)$ | $(0.0464,0.0465)$ | $(35.52,35.54)$ | $(220.96,220.98)$ | $(340.21,340.22)$ |
| $O_1$ | $1.371826$ | $(0.8985,0.8986)$ | $(0.1301,0.1303)$ | $(27.32,27.33)$ | $(312.87,312.88)$ | $m^*$ |
| $S_1$ | $1.385379$ | $\theta$ | $1/8$ | $(27.20,27.21)$ | $(314.23,314.25)$ | $m^*$ |

For $Q$, $\Lambda\in(0.127,0.129)$ and $F_0\in(1197,1198)$;
for $O_1$, $\Lambda\in(-0.028,-0.027)$ and $F_0\in(2917,2919)$;
for $S_1$, $\Lambda=0$ and $F_0\in(2994,2995)$.
The two prescribed sources identify $O_1,S_1$; the remaining root
and $d=-\beta/\alpha$, followed by $g=H/U$, define $Q$ exactly.
Thus $E(p^*,v^*)=\{S_1\}$. The $M$ equality is asserted at this exact
base. The uniform rectangle conclusions are the root count, source
guards and $J$ separation; they do not assert the $M$ equality throughout
the rectangle. The table proves both uniqueness of the unordered $M$
pair and whole-child $J$ injectivity. ∎

**Corollary 8.3 (The source-union restriction cannot be enlarged).**
The implication $E(p,v)\ne\varnothing\Rightarrow f_{MM}|_{C(p,v)}$
is injective is false. Theorem 3.2 remains an injectivity theorem on
$E(p,v)$ itself.

**Proof.** The child in Theorem 8.2 meets $E$ but contains the distinct
mixed $M$ pair $\{O_1,S_1\}$. This pair has only one endpoint in $E$,
so it does not contradict Theorem 3.2. At this child $M$ fails to
identify the complete world and $J$ identifies it; its $J$-pair count
is zero, so the child supplies no $L_1$ witness. ∎

**Theorem 8.4 (Finite nonempty singular-endpoint $M$ bases).** The set

$$
\mathcal B_{\mathcal S,M}=
\{(p,v)\in\mathbb R^2:p\ne24,\ \exists W\ne W'\in C(p,v),
\ f_{MM}(W)=f_{MM}(W'),\ \Lambda(W)\Lambda(W')=0\}
$$

is finite and nonempty. The finite outer construction below includes
all coefficient and denominator exceptions. A singular world unused by
an ordinary/ordinary $M$ pair does not put that pair under this theorem.

**Proof.** Work first in $K=\mathbb Q[\theta]/(\Phi)$, using the
irreducibility certificate in Section 3. The two strict embeddings are
those of O, Theorem 4.2. For each use the singular source $s=(\theta,1/8)$,
$x_s=n_s/U_s$ and its entire affine response line

$$
(p_s(t),v_s(t),m_s(t))
=24+(K_{5s},K_{6s},K_{7s})+t(A_{5s},A_{6s},A_{7s}).
$$

Here $t=e_s$, $K_{5s}=0$, and $p_s\ne24$ is exactly $t\ne0$.
Substitute this line in the cleared original-clock system. The terminal
condition for any companion is

$$
h=dD+(2x+3)a_7-m_s(t)D=\ell(x)d+N_s(x,t)=0,
$$

where $N_s=h|_{d=0}$ is an explicit polynomial affine in $t$, and

$$
\ell=-8x^4-29x^3-18x^2+15x+6.
$$

When $\ell\ne0$, eliminate $d$ and take the exact polynomial quotients

$$
F_s=\frac{\ell^2f(x,-N_s/\ell,p_s,v_s)}{D^2(x-x_s)},\qquad
G_s=\frac{\ell^4K(x,-N_s/\ell,p_s,v_s)}{D^4(x-x_s)}.
$$

These formulas, interpreted after multiplication by the displayed
powers of $\ell$, are polynomial divisions with zero remainder in
$K[x,t]$. Reduce coefficients in the power basis of $\theta$ modulo
$\Phi$; keep the displayed normalization rather than rescaling the
quotients. The $(t,x)$ degrees are $(2,6)$ and $(4,13)$.
Both gcds in $K[x]$ of their coefficients as polynomials in $t$ are
one after monic normalization. Also

$$
\gcd_x(\ell,[t]N_s)=1,\qquad \ell(x_s)\ne0,
\qquad P_s(x):=\operatorname{Res}_t(F_s,G_s)\ne0,\quad\deg P_s=50.
$$

All objects are fixed by the preceding rational circuits and exact
division rules. For explicit nonidentity checks, specialize modulo
$101$ at $\theta=53$; $\Phi(53)=0$ and all coefficient denominators
of $F_s,G_s,P_s$ are units. The residues are

$$
x_s=69,\quad A_{5s}=13,\quad \ell(x_s)=93,\quad
P_s(0)=97,\quad [x^{50}]P_s=62.
$$

The lowercase gain coefficients of Section 3 are $a_{6s}=46,a_{7s}=91$;
the full response slopes here are $A_{6s}=94,A_{7s}=6$.
The coefficient gcd and division assertions above are over $K[x]$;
the residues certify nonidentity and preserve the displayed degrees.
They do not designate a real source.

An explicit finite outer set of bases is obtained as follows. For each
strict embedding, include the projections of all solutions of
$F_s(x,t)=G_s(x,t)=0$ with $x>0$, $\ell(x)\ne0$, $x\ne x_s$,
$t\ne0$, using $d=-N_s/\ell$, and include the following exceptional
case as well. The first set is finite: $P_s\ne0$ leaves finitely many
$x$, and coefficient content one means that at no such $x$ can
$F_s(x,t)$ vanish identically in $t$. Indeed a Bézout identity for its
coefficient polynomials evaluates to one at every $x$. Thus there are
only finitely many $t$ for each $x$.

If $\ell(x)=0$, there are finitely many $x$, and
$\gcd(\ell,[t]N_s)=1$ says that the coefficient of $t$ in $N_s$ is
nonzero at each. The equation $h=0$ fixes one $t$. Include its base,
with every finite common drift root of $f,K$ still eligible for guarded
lifting. F, Lemma 31.3, ensures that these drift roots are finite in
number; no whole drift line was divided away.

If $x=x_s$, $\ell(x_s)\ne0$ and the singular world itself satisfies
$h=0$ at $d=24+t$. This is therefore the only possible companion drift.
The injection in F, Lemma 30.2, identifies the whole world, excluding
a distinct pair. Finally $D=0$ cannot occur at a legal $x>0$.
The field denominators are fixed nonzero elements: $j_s,n_s,T_s,U_s$
and $A_{5s}$ are nonzero at both strict embeddings, and every other
coefficient denominator is part of the displayed field computation.
No denominator depending on a candidate $x$ or $t$ remains unhandled.

O, Theorem 29.2, exhausts all singular endpoints by these two embeddings.
The union of the finite outer projections is finite and contains every
actual base in the statement. Actual membership still requires all of
Definition 1.1, including within-pair distinctness; no root of $P_s$
is automatically a world. Theorem 8.2 supplies an actual member, proving
nonemptiness. Zero drift, $F_0=0$, lower gain degree and sampled or
repeated gain roots were not cancelled from the companion equations. ∎

## 9. Finite outer joint bases whenever the entire child meets the exceptional union

**Definition 9.1 (The singular image quartic).** At $b=1/8$ put
$j_s=1/8+8r(1-r)$, $n_s=j_s+r$, $T_s=9/8$, $U_s=5/4$ and use
$A_{5s},A_{6s}$ from Definition 8.1. Let $\mathcal L_s(r,p,v)$ be
the reduced numerator of

$$
A_{5s}(v-84-24n_s)-A_{6s}(p-24).
$$

Take the primitive resultant

$$
S_4(p,v)=\operatorname{primitive}\operatorname{Res}_r(\Phi,\mathcal L_s),
$$

with positive leading coefficient in $v$. This fixes the integer
normalization: total degree four, fifteen monomials, and constant
$v$-leading coefficient $99133686444483896037925$.
The reduced numerator means cancellation of the polynomial gcd before
clearing rational scalar denominators; $j_s,n_s,T_s$ are retained as
source guards even when their factors cancel algebraically.

**Lemma 9.2 (Singular coverage and a nonidentity certificate).** Every
actual singular-source base lies on $S_4=0$. The polynomial $S_4$ is
irreducible over $\mathbb Q[p,v]$ and divides none of $E_0,N_J,N_M$
from Theorem 4.3.

**Proof.** O's exhaustive singular-source theorem gives $b=1/8$ and
$\Phi(r)=0$. Its whole gain has

$$
p=24+eA_{5s},\qquad v=84+24n_s+eA_{6s}.
$$

The expression defining $\mathcal L_s$ is zero, so its resultant with
$\Phi$ vanishes. Its source denominators are nonzero on every strict
singular source. No gain sample or drift was divided out.

For irreducibility, at $p=0$ modulo $109$ the monic specialization is

$$
q(v)=v^4+108v^3+38v^2+22v+46.
$$

Modulo $q$, $v^{109^2}=55+108v$,
$\gcd(q,v^{109^2}-v)=1$ and $v^{109^4}=v$.
The degree-four finite-field irreducibility criterion therefore applies.
Primitivity and the constant nonzero $v$-leading coefficient ensure that
a nontrivial rational factorization would specialize without degree loss,
contradicting this certificate.

For nondivisibility use the fixed F31 $R$, not a scalar multiple.
At prime $101$ the singular source $(r,b,e)=(53,38,1)$ has

$$
(p,v,x)=(37,26,69),\qquad \Phi=\Lambda=S_4=0.
$$

In the old quotient chart the exact residues are

$$
\begin{gathered}
\rho=[x^{18}]R=41,\qquad
\operatorname{Disc}(R/\rho)=21,\qquad\operatorname{Disc}(R)=54,\\
(\operatorname{Norm}\alpha,\operatorname{Norm}D,
\operatorname{Norm}H_1,\operatorname{Norm}C_0,
\operatorname{Norm}N_0)=(62,97,48,23,95),\\
\det K_J=79,\qquad\det K_M=52.
\end{gathered}
$$

The defining $f,K$, the two reconstruction clock equations and the
rank-one equation reduce to zero. The five norm units, $\rho$ and the
discriminant make every prescribed adjugate inverse and coefficient
denominator of Theorem 4.3 a unit here; constants $2,5$ are units too.
Thus $E_0$ and both reduced index numerators are nonzero at this
$S_4$ point. Gauss' lemma rules out divisibility of any of them by
$S_4$. The monic and raw discriminants have been distinguished because
the raw leading coefficient is part of the fixed normalization.
This is a nonidentity certificate, not a finite-field legal model. ∎

**Definition 9.3 (The nonzero-drift $F_0$ image).** Retain $\chi$ and
$L$ from the proof of Theorem 4.3. Substitute $v=\chi(x,p)$ into the
fixed source equations and form the exact polynomial quotients

$$
f_F=\frac{f(x,d,p,\chi)}d,\qquad
K_F=\frac{K(x,d,p,\chi)}{d^2}.
$$

They are polynomials in $\mathbb Q[x,p,d]$ of $d$-degrees one and two.
Define $S_\star$ with its exact scalar normalization by

$$
\operatorname{Res}_d(f_F,K_F)=16(x+2)^2S_\star(x,p).
$$

It has degrees $(x,p)=(24,2)$ and sixty-nine monomials. In the notation
of Theorem 4.3 it is exactly $S$:

$$
S=S_\star,\qquad
25x^6(x+1)^6R(x,p,\chi)=9L(x,p)S_\star(x,p).
$$

In particular no factor four is present in either identity. Define
$Q_{24}$ by the primitive integer identity

$$
\operatorname{Res}_x(F_0,S_\star)
=-72301961339136000000000000000000\,p^2Q_{24}(p,v).
$$

It has total degree $24$, $325$ monomials and constant positive
$v$-leading coefficient $5775468750000000000$. These resultant
identities and the fixed $f,K$ are usable coefficient specifications;
no expanded coefficient table for the later index determinants is needed.

**Lemma 9.4 (Irreducibility and coverage including the response axes).**
The polynomials $S_\star\in\mathbb Q[x,p]$ and
$Q_{24}\in\mathbb Q[p,v]$ are irreducible. Every actual world with
$F_0=0$ and $d\ne0$ has $Q_{24}(p,v)=0$, including $p=0$ or $v=0$.

**Proof.** The coefficient gcd of $S_\star$, viewed as a quadratic
in $p$, is one. Its discriminant is exactly

$$
-9x^4(x+1)^2c_0^2c_1^2c_2^2G_6^2H_7^\star,
$$

where

$$
\begin{aligned}
c_0&=45x^3+89x^2-32x-40,\\
c_1&=113x^3+224x^2-79x-100,\\
c_2&=185x^3+371x^2-118x-160,\\
G_6&=177x^6+724x^5+542x^4-742x^3-629x^2+196x+160,\\
H_7^\star&=4140x^7+13868x^6+376x^5-25313x^4\\
&\qquad-1018x^3+12851x^2+120x-2000.
\end{aligned}
$$

The odd degree of the last factor makes this rational-function
discriminant nonsquare: its valuation at infinity is odd after removal
of the displayed squares. Thus the quadratic is irreducible over
$\mathbb Q(x)$, and primitivity gives irreducibility over $\mathbb Q[x,p]$.

For $Q_{24}$, specialize $p=3$ modulo $109$. In ascending powers of
$v$ its monic array is

$$
\begin{gathered}
(12,6,38,15,104,11,88,34,34,12,36,93,56,37,44,31,19,51,\\
2,44,35,42,7,101,1).
\end{gathered}
$$

The remainders of $v^{109^8}$ and $v^{109^{12}}$ modulo this
polynomial, in the same order, are

$$
\begin{gathered}
(31,68,88,10,77,14,50,100,79,98,59,96,103,18,11,2,57,98,\\
73,42,83,21,23,91),\\
(5,15,49,44,54,47,63,108,72,17,69,102,49,91,53,59,94,107,\\
38,25,31,58,27,49).
\end{gathered}
$$

Both gcds with the corresponding remainder minus $v$ are one, and
$v^{109^{24}}=v$. These are precisely the prime-divisor tests for
$24$, so Rabin's criterion proves irreducibility of this specialization.
Its leading coefficient survives. The primitive polynomial has constant
nonzero $v$-leading coefficient, so Gauss' lemma and specialization
prove the asserted characteristic-zero irreducibility.

On an actual $F_0=0$ world, $x>0$ gives $v=\chi(x,p)$. If $d\ne0$,
the two quotients $f_F,K_F$ vanish; hence $S_\star(x,p)=0$.
The resultant identity gives $Q_{24}=0$ when $p\ne0$.
This conclusion also holds on the axis: in $\mathbb Q[x,p]$,

$$
S_\star\ \bigm|\ [5x(x+1)]^{24}Q_{24}(p,\chi(x,p)).
$$

The right side is a polynomial by the explicit denominator of $\chi$.
For instance this divisibility follows by reducing its numerator modulo
$S_\star$; the remainder is zero. Equivalently, the irreducible
$S_\star$ curve has a dense $p\ne0$ subset, so the rational identity
extends on the locus $x(x+1)\ne0$. These denominators are nonzero for
actual $x>0$. Thus $p=0$ was not discarded by the extraneous resultant
factor $p^2$, and no division by $v$ occurs anywhere. ∎

**Lemma 9.5 (The old drift inverse fails on a whole component).**
$Q_{24}$ divides the reduced numerator of the old
$\operatorname{Norm}_{R/\rho}(\alpha)$ and hence divides $E_0$.
The old $E_0$-based outer restriction alone is vacuous on this entire
image curve. Searching for another $E_0$ unit on $Q_{24}=0$ cannot
repair that chart.

**Proof.** At $F_0=0$, $f$ has zero constant term in $d$ and $K$ has
both zero constant and linear terms. Thus $d=0$ is a common root.
For an actual nonzero-drift $F_0$ label its actual $d$ is a second
common root. The linear pseudo-remainder $\alpha d+\beta$ must vanish
at both, forcing $\alpha=\beta=0$ at its $x$.
Algebraically, after substituting $\chi$, the cleared $\alpha$ numerator
is divisible by $S_\star$ and $\beta$ vanishes identically.
The $R$-on-$\chi$ identity in Definition 9.3 puts this source curve
on $R=0$. Its map $(x,p)\mapsto(p,\chi)$ has one-dimensional image:
$p$ is nonconstant on the irreducible $S_\star$ curve. Its image is
dense in the irreducible $Q_{24}$ curve by Lemma 9.4.
Consequently $R$ and $\alpha$ have a common root generically over
that image, so the old norm numerator is zero there. Irreducibility
forces divisibility by $Q_{24}$.

The legal nonzero-drift $F_0$ arcs of Section 3 provide the same geometric
interpretation, but no assumption that every complex point lifts is
needed. The obstruction is an identically vanishing factor on a component,
not an unlucky specialization. The drift chart must change there. ∎

**Definition 9.6 (Exact arithmetic circuits on the image curve).** Put

$$
B_{24}=\mathbb Q[p,v]/(Q_{24}),\qquad
K_{24}=\operatorname{Frac}(B_{24}),\qquad \bar R=R/\rho.
$$

The following rules specify polynomial representatives and every inverse
used below. They are also a way to evaluate the definitions without
expanding the final determinant polynomials.

For a monic polynomial $P\in K_{24}[x]$ of degree $s$ and a residue $u$,
let $M_P(u)$ be the matrix whose column $j$ is the coefficient vector of
$\operatorname{rem}_x(ux^j,P)$ in $1,x,\ldots,x^{s-1}$, for
$0\le j<s$. Define

$$
\operatorname{Norm}_P(u)=\det M_P(u),\qquad
u^{-1}=\frac{\operatorname{adj}(M_P(u))\,\mathbf e_0}
                  {\det M_P(u)}
$$

when the norm is nonzero; the vector in the second expression denotes
its polynomial in the power basis. Polynomial products are reduced by
monic long division. Determinants use their usual finite permutation
formula, introducing no pivot denominators.

For coefficient arithmetic, divide $Q_{24}$ by its constant
$v$-leading coefficient. Reduce polynomial representatives to degree
less than $24$ in $v$ over $\mathbb Q[p]$. Represent a field element
by a fraction of such polynomials. Addition, multiplication and inversion
use fraction arithmetic, followed by this normal-form reduction of
numerator and denominator and cancellation of their ordinary polynomial
gcd when present. Clear scalar rational denominators and remove integer
content when extracting a primitive numerator or denominator. Fix its
sign by positive lexicographic leading coefficient in $(p,v)$.
These rules select representatives in the coordinate ring; a denominator
which vanishes at a specialization is retained in the exceptional product,
not evaluated by cancellation at that point.

Let $S_1(x)$ be the degree-one subresultant in $x$ of $\bar R,F_0$.
Explicitly form the $19$ by $20$ coefficient matrix with rows
$x\bar R,\bar R,x^{16}F_0,x^{15}F_0,\ldots,F_0$ and descending
columns $x^{19},x^{18},\ldots,1$. Keep its first eighteen columns
(the degrees $19$ through $2$). Append the degree-one column to obtain
$A_1$, or the constant column to obtain $A_0$. Then
$S_1(x)=\det(A_1)x+\det(A_0)$. This fixes the subresultant scalar
and sign as well as its zero locus. Put $s_1=[x]S_1$ and

$$
G=S_1/s_1=\operatorname{monic}\gcd_x(\bar R,F_0),\qquad
T=\bar R/G.
$$

These identities hold over $K_{24}$ and $\deg G=1$. To see the lower
bound, the $R$-on-$\chi$ identity and the dense source/image map in
Lemma 9.5 give a common $R,F_0$ root over the generic image. The
specialization in Lemma 9.8 below has gcd degree one, so the generic
gcd has degree at most one. The same certificate makes $s_1$ and
$\operatorname{Res}(G,T)$ nonzero. Thus all divisions specified here
exist in $K_{24}$; their special failures will be retained explicitly.

Write $f=a_fd^2+b_fd+c_f$, retaining the fixed F31 coefficients.
In the indicated quotient algebras define

$$
\delta_T=-\beta\alpha^{-1}\pmod T,\qquad
d_F=-b_fa_f^{-1}\pmod G,
$$

$$
\widehat\delta=
\operatorname{rem}_{\bar R}\left[
\delta_T+T\bigl((d_F-\delta_T)T^{-1}\pmod G\bigr)\right].
$$

All inverses mean the preceding adjugate rule, in the quotient specified
by the modulus. The norm of $\alpha$ on $T$ is nonzero by Lemma 9.8;
there is no inverse of $\alpha$ on $G$.
This is the Chinese remainder construction: $\widehat\delta$ agrees
with $\delta_T$ modulo $T$ and with $d_F$ modulo $G$.

Use $\widehat\delta$ in place of $\delta$ in the following exact circuits
in $K_{24}[x]/(\bar R)$:

$$
\begin{gathered}
\widehat H_i=a_i(x,\widehat\delta)/D\quad(i=0,1,2,7),\\
\widehat B_0=294/5-2\widehat\delta-\widehat H_2,\quad
\widehat C_0=\widehat\delta^2+\widehat B_0^2,\quad
\widehat N_0=-\widehat\delta\widehat H_0+\widehat B_0\widehat H_2,\\
\widehat\tau_M=\widehat\delta+(2x+3)\widehat H_7,\\
\widehat\tau_J=\widehat\delta+
 \left(4x+\frac12+\frac{\widehat C_0}{2\widehat N_0}
       -\frac{2(24-\widehat\delta)}{\widehat H_1}\right)\widehat H_7.
\end{gathered}
$$

Let $\widehat K_E$ be the $18$ by $18$ coefficient matrix with columns
$1,\widehat\tau_E,\ldots,\widehat\tau_E^{17}$ in the power basis.
Define $n_{24,E}$ to be the primitive numerator of its determinant using
the coefficient rules above. This definition requires no selection or
ordering of real roots.

**Definition 9.7 (The exceptional product on $Q_{24}$).** For every
scalar field element in the following list take both its primitive
numerator and its primitive denominator under Definition 9.6:

$$
\begin{gathered}
Q_{10},\ p-24,\ \rho,\ \operatorname{Disc}_x(R),\ s_1,\\
\operatorname{Norm}_T(\alpha),\quad
\operatorname{Norm}_G(a_f),\quad\operatorname{Norm}_G(d_F),\quad
\operatorname{Res}_x(G,T),\\
\operatorname{Norm}_{\bar R}(D),\quad
\operatorname{Norm}_{\bar R}(\widehat H_1),\quad
\operatorname{Norm}_{\bar R}(\widehat C_0),\quad
\operatorname{Norm}_{\bar R}(\widehat N_0).
\end{gathered}
$$

Also take every nonconstant coefficient denominator in the displayed
subresultant, monic quotient, adjugate, CRT, terminal and power-determinant
circuits: in particular those of $G,T,\delta_T,d_F,\widehat\delta$,
all four $\widehat H_i$, $\widehat B_0,\widehat C_0,\widehat N_0$,
both $\widehat\tau_E$, their power columns and their determinants.
Let $e_{24}$ be the primitive squarefree product of these polynomial
representatives, omitting nonzero constants. All are nonzero in $K_{24}$
by the certificate below. This is an explicit finite circuit definition
of a polynomial in $\mathbb Z[p,v]$.

No $\operatorname{Norm}_{\bar R}(\alpha)$ factor is inserted: it is zero
on the whole component. Nor is any leading coefficient or root difference
of the gain polynomial inverted. The symbols $E_0,N_J,N_M$ retain the
ambient rational-circuit definitions of Theorem 4.3, including all of
its coefficient denominators and norm factors; they are not redefined
by this second chart.

**Lemma 9.8 (The CRT chart has a regular nonidentity point).** The
polynomials $e_{24},n_{24,J},n_{24,M}$ are nonzero modulo $Q_{24}$.
Every norm, denominator and subresultant condition used in their
construction has a nonzero specialization at the following certificate.

**Proof.** Work modulo $101$ at $(p,v)=(19,44)$. The original-source
substitution has

$$
(r,b,e,x,\Lambda)=(87,28,46,1,81),\qquad d=70.
$$

The fixed normalization gives

$$
Q_{24}=0,\quad Q_{10}=24,\quad\rho=46,\quad
\operatorname{Disc}(\bar R)=38,\quad\operatorname{Disc}(R)=69.
$$

The complete ascending array for $\bar R$ is

$$
(60,18,67,65,40,73,7,42,2,37,26,53,90,84,87,9,61,87,1).
$$

Both $\gcd(\bar R,F_0)$ and $\gcd(\bar R,\alpha)$ are $x-1$.
The nonzero subresultant degrees for the former are $18,3,2,1$,
and $s_1=75$. Furthermore

$$
\operatorname{Norm}_T(\alpha)=54,\quad
\operatorname{Norm}_G(a_f)=63,\quad
\operatorname{Norm}_G(d_F)=70,\quad\operatorname{Res}(G,T)=15.
$$

The CRT drift and the faithful terminal functions have ascending arrays

$$
\widehat\delta=(72,13,49,0,13,90,34,32,50,35,59,10,97,48,96,88,100,93),
$$

$$
\widehat\tau_J=(86,20,61,53,51,73,83,5,48,52,81,55,36,59,39,70,17,84),
$$

$$
\widehat\tau_M=(62,82,86,67,74,55,48,3,32,36,55,40,89,22,75,34,99,71).
$$

They give

$$
\begin{gathered}
(\operatorname{Norm}D,\operatorname{Norm}\widehat H_1,
 \operatorname{Norm}\widehat C_0,\operatorname{Norm}\widehat N_0)
=(46,72,37,74),\\
\det\widehat K_J=82,\qquad\det\widehat K_M=18.
\end{gathered}
$$

The remainders of $f,K$, $\widehat\delta U+\widehat H_0$,
$\widehat B_0U-\widehat H_2$, and
$r^2-(1+b)r+b(xU-b)$ are zero, where $U,r,b$ in these reductions
are reconstructed by the robust formulas. Also $\widehat\delta(1)=70$,
agreeing with the original-source drift.

Every listed norm and the final subresultant coefficient is a unit.
The other retained factors are $Q_{10}=24$, $p-24=96$, $\rho=46$
and raw discriminant $69$. Hence the prescribed adjugate and monic
operations, with constants $2,5$ invertible, have unit denominators.
The coefficient-normal-form rule divides only by the constant leading
coefficient of $Q_{24}$ in addition; that coefficient is a unit modulo
$101$. Reduction and ordinary gcd cancellation cannot introduce a
vanishing denominator at this regular point. Thus all the coefficient
denominators and reduced norm numerators or denominators included in
$e_{24}$ are units here. Both determinant numerators are units as well.
This proves nonidentity in the function field and nondivisibility by
$Q_{24}$ for the chosen polynomial representatives. The certificate
makes no ordered-real or legal-world assertion. ∎

**Lemma 9.9 (All-world faithful terminal bridge on each chart).** At
$p\ne24$, off $E_0$ every actual world is represented by the old chart
$\delta$. At a base on $Q_{24}=0$ off $e_{24}$, every actual world is
represented by $\widehat\delta$. In each case distinct worlds have
distinct $x$, and each terminal collision forces the corresponding
power determinant to vanish.

**Proof.** The old-chart assertion is the all-world argument of Theorem
4.3, using Theorem 4.1 and the linear pseudo-remainder. On the second
chart $\rho\ne0$ and the subresultant conditions specialize $G$ to
the complete common factor of $\bar R,F_0$, of degree one. Its
complement $T$ is coprime to it. Every actual world is an $R$ root by
Theorem 4.1. If its $x$ is a $T$ root, the retained
$\operatorname{Norm}_T\alpha$ gives $d=-\beta/\alpha=\delta_T(x)$.
If its $x$ is a $G$ root, then $F_0=0$. Since $Q_{10}\ne0$,
Theorem 4.3 excludes every actual zero-drift world at this base.
At $G$, $c_f=0$ and $f=d(a_fd+b_f)$. The retained $a_f$ norm and
$d\ne0$ force $d=-b_f/a_f=d_F(x)$. The CRT expression gives the
actual drift in both cases. This includes all actual worlds, with no
requirement that they be chosen endpoints or that their sources be regular.

F, Lemma 30.2, makes $W\mapsto(x,d)$ injective; a unique assigned drift
at each $x$ therefore makes different worlds have different $x$.
The $D,H_1,C_0,N_0$ norm factors and the coefficient denominators make
the displayed functions defined at every $R$ root. On an actual root
$N_0=UC_0$, and

$$
\frac{T+2j+4r}{U}
=4x+\frac12+\frac{C_0}{2N_0}-\frac{2(24-d)}{H_1}.
$$

Thus $\tau_J$ or $\widehat\tau_J$ equals exactly the original
$f_{MJ}$; the corresponding $M$ function equals $f_{MM}$.
No final read has been added to the acquired history.

Finally the nonzero discriminant gives eighteen distinct complex roots
$x_i$. Their Vandermonde evaluation matrix is invertible. Multiplying
it by the coefficient matrix of $1,\tau_E,\ldots,\tau_E^{17}$ gives
rows $(1,\tau_E(x_i),\ldots,\tau_E(x_i)^{17})$. If two actual distinct
worlds have equal terminal values, two of these rows coincide. Therefore
its determinant, and hence the coefficient determinant, is zero.
Equivalently it is the Vandermonde quotient of Section 2. This is only
a necessary implication; complex roots and determinant zeros do not
supply actual worlds. ∎

**Theorem 9.10 (Exceptional-inclusive finite outer joint bases).** Define

$$
\begin{aligned}
Z_E={}&V_{\mathbb C}(Q_{10},E_0N_J,E_0N_M)\\
&\cup V_{\mathbb C}(S_4,E_0N_J,E_0N_M)\\
&\cup V_{\mathbb C}(Q_{24},e_{24}n_{24,J},e_{24}n_{24,M}).
\end{aligned}
$$

This is an explicitly defined finite, possibly empty complex affine set.
For every real $p\ne24,v$, if the entire original child $C(p,v)$
merely meets $E(p,v)$ and supports both a distinct terminal-$J$ pair and
a distinct terminal-$M$ pair, then $(p,v)\in Z_E$.
The exceptional world need not occur in either selected pair. The pairs
may overlap or be disjoint, and their common terminal responses may differ.

**Proof.** Select any exceptional world solely to locate the base.
If it has zero drift, its base lies on $Q_{10}$ by Theorem 4.3.
If it has nonzero drift and $F_0=0$, Lemma 9.4 puts its base on
$Q_{24}$. The remaining exceptional case has $\Lambda=0$, so
Lemma 9.2 puts its base on $S_4$. These cases exhaust Definition 3.1.

At a $Q_{10}$ or $S_4$ base, if $E_0=0$ both product equations hold.
Otherwise the all-world bridge in Lemma 9.9 makes the actual $J$ pair
force $N_J=0$ and the actual $M$ pair force $N_M=0$. At a $Q_{24}$
base the identical argument uses $e_{24}$ and the CRT chart.
This proves containment. In particular it strengthens the quantified
application of Theorem 4.3: a zero-drift world unused by both pairs still
locates their shared base on $Q_{10}$, and the two pairs still force
its product equations. No rewriting of that earlier theorem is required.
The same reasoning does not use cross-pair distinctness or equality of
the two common terminal values.

For finiteness, Theorem 4.3 already proves that the first set is finite.
By Lemma 9.2 the irreducible $S_4$ divides none of $E_0,N_J,N_M$.
Consequently $S_4$ and $E_0N_J$ are coprime plane polynomials, so their
affine intersection is finite; imposing the third equation only reduces
it. By Lemmas 9.4 and 9.8 the same argument applies to
$Q_{24}$ and $e_{24}n_{24,J}$. Coprimality over $\mathbb Q$ here
also excludes a common complex curve component: a common factor over
$\overline{\mathbb Q}$ would give a rational common factor by its
conjugates. Thus absolute irreducibility is not required. The union of
these three finite sets is finite.

Every exceptional intersection has been retained. Set-theoretically,
for example, the third set is

$$
V(Q_{24},e_{24})\ \cup\ V(Q_{24},n_{24,J},n_{24,M}).
$$

It includes its intersections with $Q_{10}=0$, $p=24$, $\rho=0$,
the repeated-root locus, the subresultant degree-change locus,
$\operatorname{Norm}_T\alpha=0$, $\operatorname{Norm}_G a_f=0$,
$\operatorname{Norm}_G d_F=0$, $\operatorname{Res}(G,T)=0$,
the $D,H_1,C_0,N_0$ norm loci and every construction-denominator locus.
The first two sets likewise include $V(Q_{10},E_0)$ and $V(S_4,E_0)$.
Intersections among the three image carriers are included in their union;
the response axes are covered by the zero-drift and nonzero-drift carrier
proofs without cancellation of $p$ or $v$. No degree drop, repeated root
or intersection is being evaluated through a failed inverse. On those
points the product condition is an outer condition only, and the full
zero-safe world equations remain necessary for actual lifting. ∎

**Assumption 9.11 (Sources, tools and transferred scope).** The owning
ordinary source results remain O, Definitions 1.1–1.3 and Theorems 2.1,
4.2, 17.1, 29.2, and F, Sections 30–33. Fixed public references are
[O at the common source snapshot](https://github.com/the-omega-institute/trureturing/blob/033c1b370f2447aa20e191a6a3da609aba697e50/docs/develop/theory/FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md)
and [F at that snapshot](https://github.com/the-omega-institute/trureturing/blob/033c1b370f2447aa20e191a6a3da609aba697e50/docs/develop/theory/FIB_ALL_RESPONSE_FINITE_FIBRE_GEOMETRY.md).
The reconstruction, the 24-world bound and Sections 1–5 are reused;
these results are not new proofs of that bound or repetitions of the
published B collision. The different history of R supplies no theorem
about this $H_4$ merely by analogy.

Distinct-node interpolation, the contraction theorem, the implicit- and
inverse-function theorems, Sturm isolation, Sylvester resultants,
finite-field irreducibility, the Chinese remainder theorem and the
Vandermonde determinant are standard tools. The interpolation,
contraction, resultant and finite-field references in Sections 1–6 apply
with exactly their stated hypotheses. For the algebraic tools, see
Atiyah–Macdonald, *Introduction to Commutative Algebra*, Proposition 1.10
for the Chinese remainder theorem, and Fulton, *Algebraic Curves*,
[primary text](https://dept.math.lsa.umich.edu/~wfulton/CurveBook.pdf),
the resultant and plane-curve intersection arguments. For the analytic
tools, see Rudin, *Principles of Mathematical Analysis*, Theorems 9.24
and 9.28; the displayed nonzero Jacobians supply their hypotheses.
The Vandermonde identity is applied only to distinct roots; its
specialization failures are retained in the discriminant factors.

The bounded new deductions here are source-specific: the whole-child
singleton neighbourhood and both-endpoint bound, the exactly lifted mixed
pair with its entire-child enumeration and finite singular-endpoint
incidence, and the exceptional-inclusive finite outer reduction with
its component-specific CRT chart. The older $S$ carrier, standard
algebraic tools and bounded source-overlap evidence do not establish
worldwide novelty. All statements concern ordinary mathematics in the
specified model. They make no kernel-certification, physical-realization,
algorithmic-complexity or total-resource claim. Lower gain degrees,
sampled and repeated gain roots, zero drift and singular sources retain
their original meanings. Every original clock $0,\ldots,7$ and immediate
read remains; there is no reset, copy, skip, new port or acquired hidden
label. The two final actions remain counterfactual alternatives.

## 10. Current residual incidence and mathematical scope

**Proposition 10.1 (The remaining same-child problem).** The unchanged
strict-real off-$24$ common-base conjunction has the following reductions
and unresolved parts.

**Proof and residual map.** Theorem 7.3 removes the $b\to\infty$
endpoint tail for both terminal collision relations at once. The stronger
Theorem 7.4 gives empty or singleton entire children near $q_\infty$
and singleton children acquired from sufficiently large-$b$ worlds.
No numerical endpoint bound or neighbourhood radius is asserted.
The remaining source domain is not compact: $b\to0$, $r\to0,1$,
unbounded $r(1-r)/b$, and finite-source singular, ramified or denominator
limits remain. A bound on this one offdiagonal is neither a bound on all
world coefficients nor a finite cover of the acquired base plane.

Theorem 8.2 proves that mixed exceptional/ordinary $M$ pairs actually
occur, and that one entire such three-world child is $J$-injective.
Theorem 8.4 reduces bases of $M$ pairs with a singular endpoint to a
finite nonempty set, whose remaining legal lifts and joint incidences
are not classified. A singular world which is unused by an ordinary/
ordinary $M$ pair is outside that endpoint argument.
Theorem 9.10 has the wider hypothesis that the entire child merely
meets $E$; it reduces every joint base with that property to the finite
outer set $Z_E$, even when no exceptional world occurs in either pair.
No point of $Z_E$ has been isolated, lifted or classified. Neither
finiteness nor any modular nonidentity certificate makes an outer
candidate a legal model.

Children avoiding $E$ remain outside this finite-image reduction.
On their old regular chart the common index equations remain necessary;
their common components, isolated intersections and strict-real lifts
are unresolved, as are the relevant $E_0=0$ strata away from the three
covered image curves. The transverse false lift of Theorem 2.2 remains
a warning that even a real transverse common zero can have no actual
collision. Excluding every real candidate in $Z_E$ would settle only
the exceptional-meeting sector, not the original global question.

The original positive certificate still requires, at one real $p\ne24,v$,
two distinct legal worlds for each terminal action in the same entire
$C(p,v)$, with one whole nonzero gain of degree at most three and one
fixed drift per world. Within each pair the faithful coordinates retain
$(x-x')^2+(d-d')^2>0$; no cross-pair distinctness is required. An
exhaustive negative certificate would have to exclude every remaining
base and all original guards, including the remaining noncompact limits.
Neither certificate is supplied here.

A positive sixth-$M$ joint child would still leave the sixth-$J$ $L_1$
condition at the same fifth response $p$, the fifth-$J$ and common-parent
conditions, and all ancestor obligations. O, Theorem 17.1, requires both
sixth-action children at one $p$ for fifth-$M$ $L_2$. Nothing in these
supporting results proves $H_4$ $L_3$, root $L_7$, or an eight-versus-nine
conclusion. ∎

## 追加锚（本行以下为增补区）

## 11. Opposite-offdiagonal escape of the entire acquired child

**Definition 11.1 (The reciprocal opposite-offdiagonal chart).** Retain
the complete worlds and the literal history of Definition 1.1. Write
$c=r(1-r)/b$, and, in this section only, put

$$
t=1/c,\qquad q=r(1-r),\qquad b=qt,\qquad
j=t^{-1}+qt,\qquad n=t^{-1}+r+qt,\qquad
T=1+qt,\quad U=1+2qt.
$$

The legal chart has $t>0$ and $0<r<1$. On it use the parent equation
$e\Lambda=-(24/5)(b-1/8)\kappa$ and the single interpolant of
Definition 7.1. The segment $t=0$, $0\le r\le1$ is an auxiliary
analytic boundary, not a family of legal sources. After clearing the
$t$ poles, the denominator factors are

$$
1+qt^2,\quad 1+rt+qt^2,\quad 1+qt,\quad 1+2qt,\quad\Lambda,
\qquad \Lambda|_{t=0}=8.
$$

They are units on a neighbourhood of that compact segment. In particular
the entire gain has a coefficientwise analytic limit

$$
e\longrightarrow3/10,\qquad d\longrightarrow243/10,\qquad
g(s)\longrightarrow(s-1)(s-3)(3s/2-81/10).
$$

The first parent coefficients are

$$
\Lambda=8-8(q+1)t+O(t^2),\qquad
e=\frac3{10}+\left(\frac3{10}-\frac94q\right)t+O(t^2).
$$

Applying the fixed extrapolation rows of Definition 2.1 gives

$$
\begin{aligned}
p&=-\frac{24}{5t}-\frac{24}{5}(10r^2-9r-4)+O(t),\\
v&=\frac{27}{2t}-\frac34(141r^2-159r-68)+O(t),\\
a=f_{MJ}&=\frac{576}{5t}-\frac3{10}(1296r^2-2064r-271)+O(t),\\
m=f_{MM}&=\frac{576}{5t}-\frac3{10}(1296r^2-1680r-655)+O(t).
\end{aligned}
$$

Every remainder here is uniform with its first derivatives in $r$ on
$[0,1]$, by the analytic extension and compactness. Thus $p\to-\infty$
uniformly as $c\to\infty$.

**Theorem 11.2 (Both terminal maps separate the opposite-offdiagonal
collar).** There is $C_1>0$ such that, for each $E\in\{J,M\}$, the
map $W\mapsto(p(W),v(W),f_{ME}(W))$ is injective among all complete
parent worlds with $c>C_1$.

**Proof.** Define the following rational combinations of the indicated
response functions:

$$
\begin{gathered}
h=-\frac{24}{5p},\qquad Y=45p+16v,\\
Z_J=a+6p-\frac{32}{5}v+\frac{147}{10},\qquad
Z_M=m+6p-\frac{32}{5}v+\frac{147}{10},\\
T_M=\frac{Z_M}{h}+\frac{239}{1712}Y.
\end{gathered}
$$

These are analytic across $t=0$: $h=t+O(t^2)$, and the identically
vanishing constant term of $Z_M$ supplies its factor $t$. Exact
substitution gives

$$
\begin{gathered}
Y(0,r)=1680+3852r(1-r),\qquad
Z_J(0,r)=\frac{576}{5}(r-1),\\
\left.\frac{Z_M}{t}\right|_{t=0}
=\frac3{100}(17925r^2-17921r+28),\qquad
T_M(0,r)=\frac3{25}r+\frac{629622}{2675}.
\end{gathered}
$$

Since $h_t(0,r)=1$ uniformly, a common sufficiently small positive
$h$ interval admits a unique analytic $t=t(h,r)$ for every
$r\in[0,1]$. This follows either from the implicit-function theorem
and compactness, or from $h_t>1/2$ on a fixed smaller strip and
strict monotonicity in $t$. On a still smaller strip,

$$
\partial_r Z_J(t(h,r),r)>0,\qquad
\partial_r T_M(t(h,r),r)>0,
$$

because their limiting derivatives are $576/5$ and $3/25$.
Equality of $(p,v,a)$ fixes $h,Z_J$; equality of $(p,v,m)$ fixes
$h,Y,T_M$. In either case monotonicity fixes $r$, and then $t$.
The sources coincide. Here $\Lambda$ remains near eight, so the
parent converse fixes the drift and every coefficient of the one whole
gain as well. No separation from $r=1/2$ or from $r=0,1$ was assumed. ∎

**Theorem 11.3 (Uniform escape of every companion).** For every $K>0$
there is $L>0$ such that, whenever a complete parent world $W$ has
$c(W)>L$, its fifth response is off $24$ and

$$
c(W')>K\qquad\text{for every }W'\in C(p(W),v(W)).
$$

There is no terminal-equality hypothesis on $W'$.

**Proof.** Suppose the conclusion fails for a fixed $K$. There are
worlds $W_i$ with $c(W_i)\to\infty$ and companions $W'_i$ in the
same entire children with $c(W'_i)\le K$. Definition 11.1 gives
$p_i\to-\infty$ while $Y_i=45p_i+16v_i$ is bounded. The uniform
large-$b$ limit in Definition 7.1 rules out an unbounded subsequence of
$b(W'_i)$, since it would instead give $p_i\to-216/5$. The companion
sources therefore have a convergent subsequence in

$$
b,c\ge0,\quad0\le r\le1,\quad bc=r(1-r).
$$

A limit $j=b+c=0$ is impossible. Indeed, for $j\le1/4$,

$$
j\Lambda=j(1+6/T+1/U)-4-4j/n\le8j-4\le-2.
$$

The bounded parent numerator then gives $e=O(j)$ and bounded $e/j$,
$e/n$. All four original samples, and hence $p$, remain bounded.
Thus the limiting $j,n$ are positive, as is $x=n/U$.

Bounded companion drift would again give bounded original samples and
bounded $p$. Pass to a subsequence with $|d|\to\infty$. Dividing the
parent equation by $d$ gives $\Lambda\to0$. The whole normalized
polynomial $g/d$ tends to the unique cubic $q_s$ with samples

$$
(-1,-1/j,-1/T,-1/n)\quad\text{at }0,1,2,3.
$$

Set $A_5=1+(U+n)q_s(5)$ and $A_6=1+(2U+n)q_s(6)$ at the limiting
source. The common bounded $Y_i$, divided by the diverging drift, gives

$$
\Lambda=0,\qquad45A_5+16A_6=0,\qquad
r^2-(1+b)r+b(xU-b)=0.
$$

This uses neither a terminal equality nor a nonzero limiting $A_5$.
The following exact finite-source certificate excludes this system even
on the nonnegative source boundary.

Put

$$
q_0=xU^2+14xU+x-4U-4,\qquad
j=\frac{4xU(U+1)}{q_0},\quad r=xU-j,\quad b=\frac{U-1}{2}.
$$

The first equation $\Lambda=0$ gives the displayed expression for $j$.
Here $x>0,U\ge1,j>0$, so $q_0>0$. The only divisors in this
substitution are positive $x,U,U+1,j,q_0$ and rational constants.
Define the integer polynomials

$$
\begin{aligned}
L={}&109U^2x^2+173U^2x-3194Ux^2-2690Ux+2948U\\
&\quad-1251x^2+341x+2948,\\
S={}&4q_0^2\{r^2-(1+b)r+b(xU-b)\},
\end{aligned}
$$

where the rational $r,b$ just displayed are substituted in $S$.
All denominators cancel in $S$, whose degrees in $(U,x)$ are $(6,4)$,
and

$$
L=4x(U+1)(45A_5+16A_6),\qquad
\operatorname{Res}_U(L,S)=1179648x^4Q(x).
$$

The complete descending coefficient vector of $Q$ is

$$
\begin{gathered}
(91738605818880000,468000052761600000,-287776045449344000,\\
-4243016387674451200,-1949152889752436800,14795306352123710480,\\
10538868307289518842,-27294682116450017650,-18623139293789121581,\\
30898244403783565513,14466477630213266395,-21723230306826660213,\\
-3613832109665837004,8083225499684453800,-862616315778108600,\\
-889489442954112000,198720866364020000).
\end{gathered}
$$

To fix the reconstruction normalization, define $A_c,B_c$ by

$$
A_c(x)U+B_c(x)=\operatorname{rem}_U
\bigl([x(109x+173)]^5S,L\bigr).
$$

Both coefficients have degree fourteen and integer content $128$.
They are the unscaled pseudo-remainder coefficients. The degrees of
$Q,A_c$ survive modulo $101$, and

$$
\operatorname{Res}_x(Q,A_c)=97\pmod {101}.
$$

Equivalently, dividing both coefficients by $128$ gives primitive
coefficients and resultant residue $36$. Either normalization makes
$A_c$ a unit at every root of $Q$. For completeness the descending
vector of $Q$ modulo $101$ is

$$
(98,88,79,98,14,27,82,85,52,50,29,64,11,64,52,96,69).
$$

The Sturm sequence $Q,Q',-\operatorname{rem}(Q,Q'),\ldots$ has
variations $6$ at zero and $2$ at positive infinity. Its four positive
roots and the necessary $U=-B_c/A_c$ have the following rational
certificate. The signs are the signs of $Q$ at the left and right
endpoints.

| $x$ bracket | Endpoint signs | Necessary $U$ interval |
|---|---|---|
| $(360774328,360774329)/10^9$ | $+,-$ | $(-19,-18)$ |
| $(431319435,431319436)/10^9$ | $-,+$ | $(-4,-3)$ |
| $(1462716433,1462716434)/10^9$ | $+,-$ | $(9/100,1/10)$ |
| $(1929370586,1929370587)/10^9$ | $-,+$ | $(-2/25,-7/100)$ |

The enclosures have the following entirely rational specification.
Bisect each bracket two hundred times, retaining the sign-changing
half; an exact midpoint root is retained as a singleton. Every resulting
width is below $10^{-65}$. Interval Horner evaluation of $A_c,B_c$
on these intervals excludes zero from $A_c$ and encloses $-B_c/A_c$
strictly inside the indicated interval. Products use the minimum and
maximum of the four endpoint products, and inversion of an interval
excluding zero uses $[1/u,1/l]$. The four sign changes and the Sturm
count exhaust all positive roots. Every corresponding $U$ is below one,
contrary to the necessary $U\ge1$.

The companion sequence is impossible. Uniform $p\to-\infty$ also
ensures $p\ne24$ after increasing $L$. ∎

**Corollary 11.4 (Whole-child terminal injectivity and bounded companions
of collision pairs).** There is $C_\infty>0$ such that a complete parent
world with $c>C_\infty$ acquires an off-$24$ child on which both
$f_{MJ}$ and $f_{MM}$ are injective. There are finite $B,C>0$ such that

$$
(p,v)\in D_J\cup D_M\quad\Longrightarrow\quad
b(W)\le B,\quad c(W)\le C
\quad\text{for every }W\in C(p,v).
$$

This includes companions unused by either selected pair.

**Proof.** Choose $K>C_1$ in Theorem 11.3. A sufficiently large-$c$
world forces every companion into the collar of Theorem 11.2. Each
terminal map is therefore injective on the entire child. For the bound
on $b$, Theorem 7.4 says that any child containing a sufficiently
large-$b$ world is a singleton. A collision child can contain neither
such a world nor a sufficiently large-$c$ world. Enlarge the two
existential thresholds to obtain $B,C$. No numerical thresholds are
part of the assertion. ∎

**Proposition 11.5 (Two large-$c$ worlds at one acquired base).** For
every sufficiently small $\eta>0$ the exact acquired base

$$
p=-\frac{24}{5\eta},\qquad
v=\frac{9609/4-45p}{16}
$$

has two distinct legal complete worlds with $c\to\infty$ as
$\eta\downarrow0$. Thus the singleton-child strengthening of
Corollary 11.4 is false.

**Proof.** In Definition 11.1 solve
$h(t,r)=\eta$, $Y(t,r)=9609/4$. At $t=0$ the two solutions
$r=1/4,3/4$ have $h_t=1,h_r=0$ and Jacobian determinants

$$
3852(1-2r)=1926,\quad-1926,
$$

respectively. The implicit-function theorem gives two analytic branches
with $t/\eta\to1$ and these different limiting $r$ values. For small
positive $\eta$, $t>0$, $0<r<1$, $b=r(1-r)t>0$ and $\Lambda$ is
near eight. The complete parent converse supplies a single whole gain
and fixed drift for each branch; unequal original readings make each
gain nonzero. Both branches have exactly the displayed $p,v$ and are
distinct. Corollary 11.4 separates their terminal responses for either
final action. They supply no terminal pair. ∎

## 12. Finite fifth-response coercivity and relative nonproper values

**Theorem 12.1 (Coercivity with a $b$ cap and bounded $p$).** For
every $L,P>0$ there is $C(L,P)<\infty$ such that every complete
$H_4$ world with $0<b\le L$ and $|p|\le P$ satisfies

$$
c\le C(L,P),\qquad |d|\le C(L,P),\qquad
\max_{0\le k\le3}|[s^k]g|\le C(L,P).
$$

Its $v,f_{MJ},f_{MM}$ are bounded as well. This statement also allows
$p=24$ and all the gain and singular-source cases of Definition 1.1.

**Proof.** Write $\Delta=b-1/8$ and $V=U+n$. The parent equation
and the fixed extrapolation give the identities

$$
\begin{gathered}
e\Lambda=-\frac{24}{5}\Delta\kappa,\qquad
A_5=1+V\left(4-\frac{15}{j}+\frac{20}{T}-\frac{10}{n}\right),\\
g(5)=\frac{96\Delta}{T}
+e\left(4-\frac{15}{j}+\frac{20}{T}-\frac{10}{n}\right),\qquad
p=24+\frac{96\Delta V}{T}+eA_5.
\end{gathered}
$$

No drift or gain sample has been cancelled. If $c\to\infty$ while
$b\le L$, then $bc\le1/4$ forces $b\to0$; $j,n\to\infty$,
$T,U\to1$, $\Lambda\to8$ and $\kappa\to4$. Hence $e\to3/10$
and the gain samples tend to $(-243/10,0,51/10,0)$. Thus
$g(5)\to-24/5$ and $p\to-\infty$, a contradiction. The sources
are consequently bounded in the nonnegative rank-one closure.

Suppose $|e|\to\infty$ along a source-convergent subsequence. A
limit $j=0$ is impossible by $j\Lambda\le-2$ for $j\le1/4$;
the parent numerator is bounded there. Thus $j,n$ have positive limits.
Dividing the parent and fifth-response identities by $e$ forces
$\Lambda=A_5=0$ at the limit. For a strict source this is excluded by
O, Lemma 12.2, whose full-source no-common-zero premise includes
singular sources. At a nonstrict source with $j>0$, the four possible
faces give the following exact restrictions:

| Limiting $(r,b,c)$ | $\Lambda$ | $A_5$ when $\Lambda=0$ |
|---|---|---|
| $(0,t,0)$, $t>0$ | $2(t^3-8t-4)/(tTU)$ | $(2t^2+21t+23)/(t(1+t))>0$ |
| $(1,t,0)$, $t>0$ | $2(t^3-4t-2)/(tTU)$ | $(6t^2+2t-6)/(t(1+t))>0$ at its positive root, which has $t>2$ |
| $(0,0,t)$, $t>0$ | $8(t-1)/t$ | $-1$ at $t=1$ |
| $(1,0,t)$, $t>0$ | $4(2t^2-1)/(t(t+1))$ | $4-8\sqrt2$ at $t=1/\sqrt2$ |

None admits simultaneous vanishing. The rank-one equation
$bc=r(1-r)$ exhausts the boundary by these faces and the two $j=0$
corners, so $e$ is bounded.

Finally $j\Lambda\le-2$ for $j\le1/4$ bounds $e/j$ directly from
the parent equation, and $n\ge j$ also bounds $e/n$. On the remaining
part $j\ge1/4$ these ratios are bounded by the drift bound. All four
samples of Definition 7.1 are bounded. Fixed-node interpolation bounds
every coefficient of the same polynomial $g$, including degree drops.
Bounded source entries then bound the remaining original-clock traces
and responses. ∎

**Definition 12.2 (Relative target and boundary lifts).** Let $X$ be the
complete $H_4$ worlds with $p\ne24$, with their usual topology in
source entries, four padded gain coefficients and drift. Put

$$
Y=\{(p,v)\in\mathbb R^2:p\ne24\},\qquad
\pi:X\longrightarrow Y,\quad\pi(W)=(p(W),v(W)).
$$

A nonproper value is a limit in $Y$ of bases of a sequence escaping
every compact subset of $X$. For a nonnegative boundary source with
$j,n>0$, retain $j=b+c,n=j+r,T=1+b,U=1+2b$ and define its auxiliary
gain by the four samples in Definition 7.1. The four rational face lifts
are specified completely by

| Source $(r,b,c)$ | Parameter guard | $e=d-24$ |
|---|---|---|
| $(0,t,0)$ | $t>0$, $t^3-8t-4\ne0$ | $-\dfrac{24t(t-1/8)(2+5t)}{5(t^3-8t-4)}$ |
| $(1,t,0)$ | $t>0$, $t^3-4t-2\ne0$ | $-\dfrac{24t(t-1/8)(2+5t)}{5(t^3-4t-2)}$ |
| $(0,0,t)$ | $t>0$, $t\ne1$ | $\dfrac{3t}{10(t-1)}$ |
| $(1,0,t)$ | $t>0$, $2t^2\ne1$ | $\dfrac{3t(t+1)}{5(2t^2-1)}$ |

The auxiliary response vector is obtained from that one interpolant by

$$
(p,v,a,m)=\bigl(d+(U+n)g(5),\ d+(2U+n)g(6),\
d+(T+2j+4r)g(7),\ d+(3U+2n)g(7)\bigr).
$$

This is an explicit rational parametrization, not a declaration that
the boundary source is legal. The two corner limits are

| Source limit | $d$ | $(g(0),g(1),g(2),g(3))$ | $(p,v,a,m)$ |
|---|---|---|---|
| $(0,0,0)$ | $24$ | $(-24,3/10,27/5,3/10)$ | $(39/2,258/5,819/10,1977/10)$ |
| $(1,0,0)$ | $24$ | $(-24,3/5,27/5,0)$ | $(18,399/5,366,366)$ |

Let $\mathcal B_\partial\subset Y$ be the union of the four face
images and these two corner bases, retaining only $p\ne24$.

**Theorem 12.3 (All finite nonproper values relative to $Y$).** The
nonproper-value set of $\pi:X\to Y$ is exactly

$$
\mathcal B_\partial\ \cup\ \{q_\infty\},\qquad
q_\infty=(-216/5,-225).
$$

**Proof.** Let an escaping sequence have a finite base limit in $Y$.
An unbounded subsequence of $b$ forces that limit to be $q_\infty$
by Definition 7.1. Otherwise $b$ and $p$ are bounded, so Theorem 12.1
bounds $c,d$ and all gain coefficients. Extract a convergent tuple.
A strict limiting source would give all original clock equations by
continuity. Its gain cannot be zero, since the original readings zero
and $24$ differ. Its limiting $p$ is off $24$, so it is a point of $X$,
contrary to escape.

The remaining limiting sources are exactly the four faces and the two
corners. On an open face a zero of $\Lambda$ has nonzero parent
numerator $-(24/5)(b-1/8)\kappa$ and hence no finite-drift lift.
Solving the parent equation at every other face point gives exactly
the table in Definition 12.2. At the lower corner,

$$
\frac rj=\frac{bc}{(1-r)(b+c)}\longrightarrow0,\quad
\frac nj\longrightarrow1,\quad
j\Lambda\longrightarrow-8,\quad e/j\longrightarrow-3/10.
$$

At the upper corner $n\to1$, $j\Lambda\to-4$ and
$e/j\to-3/5$. The four samples and the prescribed traces give precisely
the two corner vectors. This proves exhaustion.

Conversely, approach a $c=0$ face with fixed $b=t$ and strict $r$
tending to the indicated endpoint. Approach a $b=0$ face with fixed
$c=t$, $b\downarrow0$, using the lower or upper root of
$r(1-r)=bt$. The nonzero $\Lambda$ guards give regular parent lifts
converging to the table. If the limiting $p$ is off $24$, all nearby
bases are off $24$. The corners are approached by $b=c\downarrow0$
on the two rank-one branches. All these sequences leave every compact
subset of the strict source domain. Finally $r=1/2,b\to\infty$
supplies $q_\infty$ by Theorem 7.4 and Corollary 7.5. ∎

**Proposition 12.4 (An omitted boundary on the ambient $p=24$ line).**
The relative target $Y$ in Theorem 12.3 cannot be silently replaced by
the whole ambient plane while retaining only the restricted set
$\mathcal B_\partial$. In particular, off-$24$ strict worlds can
approach the nonstrict lower face point with

$$
t=\sqrt{15}/4,\qquad
(p,v)=\left(24,\frac{303}{5}+\frac{231\sqrt{15}}{40}\right).
$$

**Proof.** Substitute $t=\sqrt{15}/4$ in the lower $b=0$ face.
Its response functions are $p_L,v_L$ in Theorem 13.1 below and give
the displayed base. On the exact strict chart $r=\alpha b$ the
responses extend analytically at $b=0$ near this parameter, and

$$
p_L'(\alpha)=-24/5+3/(10(\alpha-1)^2)\ne0
\quad\text{at }\alpha=\sqrt{15}/4.
$$

The implicit-function theorem therefore supplies $\alpha(b)$ tending
to this value with $p(\alpha(b),b)=24+b$. For small $b>0$ these are
strict sources, have nonzero $\Lambda$, and lift to off-$24$ complete
worlds. Their sources approach $b=0,r=0,c=t$, and their bases have
the stated ambient limit. Thus an ambient properness assertion must
also account for the omitted $p=24$ boundary. The assertion of
Theorem 12.3 is only relative to $Y$. ∎

## 13. Boundary rays, their crossing, and terminal separation

**Theorem 13.1 (Two nondegenerate $b$-to-zero response charts).**
On a strict source sequence $r=\alpha b$, $b\downarrow0$, with
fixed $\alpha>0$, bounded $p$ excludes $\alpha=1$. For
$\alpha\ne1$ its limiting drift offset and response functions are

$$
\begin{aligned}
e_L(\alpha)&=\frac{3\alpha}{10(\alpha-1)},\\
p_L(\alpha)&=-\frac{3(16\alpha^2-80\alpha+65)}{10(\alpha-1)},\\
v_L(\alpha)&=\frac{3(45\alpha^2+125\alpha-172)}{10(\alpha-1)},\\
a_L(\alpha)&=\frac{3(384\alpha^2-113\alpha-273)}{10(\alpha-1)},\\
m_L(\alpha)&=\frac{3(384\alpha^2+271\alpha-659)}{10(\alpha-1)}.
\end{aligned}
$$

On $r=1-\alpha b$, $b\downarrow0$, with fixed $\alpha>0$,
bounded $p$ excludes $2\alpha^2=1$. The corresponding functions are

$$
\begin{aligned}
e_R(\alpha)&=\frac{3\alpha(\alpha+1)}{5(2\alpha^2-1)},\\
p_R(\alpha)&=-\frac{6(8\alpha^3-24\alpha^2-2\alpha+15)}{5(2\alpha^2-1)},\\
v_R(\alpha)&=\frac{3(45\alpha^3+215\alpha^2-33\alpha-133)}{5(2\alpha^2-1)},\\
a_R(\alpha)=m_R(\alpha)
&=\frac{3(384\alpha^3+1039\alpha^2-232\alpha-610)}{5(2\alpha^2-1)}.
\end{aligned}
$$

The right formulas extend to $\alpha=0$ as the upper corner vector
of Definition 12.2; that endpoint is not a strict source ray.
Each acquired-base map $(p_L,v_L)$ and $(p_R,v_R)$ is injective on
its indicated nonnegative parameter domain, with its poles removed.

**Proof.** The first source has
$j=\alpha+(1-\alpha^2)b$ and
$n=\alpha+(1+\alpha-\alpha^2)b$. Its limiting $\Lambda$ is
$8(\alpha-1)/\alpha$. The second has $j\to\alpha$,
$n\to\alpha+1$ and limiting
$\Lambda=4(2\alpha^2-1)/(\alpha(\alpha+1))$.
The parent equation gives $e_L,e_R$. Substitution into the four original
gain samples, followed by the rows $(-4,15,-20,10)$,
$(-10,36,-45,20)$ and $(-20,70,-84,35)$, gives the displayed
responses of one whole polynomial.

The excluded poles cannot be reached by bounded-$p$ strict rays. With
$\mathsf S_p$ the exact source polynomial of O, Definition 12.1,
its expansions are

$$
\begin{aligned}
\mathsf S_p(\alpha b,b)
&=4\alpha b^3(48\alpha^2+10\alpha p-240\alpha-10p+195)+O(b^4),\\
\mathsf S_p(1-\alpha b,b)
&=4b^3(48\alpha^3+10\alpha^2p-144\alpha^2-12\alpha-5p+90)+O(b^4).
\end{aligned}
$$

At $\alpha=1$ the first leading coefficient is $12$. At
$2\alpha^2=1$ the bracket in the second line is $18+12\alpha$.
Both are nonzero independently of finite $p$. These expansions are
also uniform for bounded $p$ and $\alpha$ near the indicated pole.

For distinct left parameters $\alpha,\beta$, equal $p$ and equal $v$
would require

$$
16\alpha\beta-16\alpha-16\beta+15=0,\qquad
45\alpha\beta-45\alpha-45\beta+47=0.
$$

They assign the incompatible values $-15/16$ and $-47/45$ to
$\alpha\beta-\alpha-\beta$.
For the right chart the reduced numerators of the two differences
divided by $\alpha-\beta$ are

$$
\begin{aligned}
P_R={}&-12(8\alpha^2\beta^2-4\alpha^2-2\alpha\beta
                 -3\alpha-4\beta^2-3\beta+1),\\
V_R={}&9(30\alpha^2\beta^2-15\alpha^2+7\alpha\beta
                 +17\alpha-15\beta^2+17\beta+11).
\end{aligned}
$$

Their exact resultant and linear subresultant are

$$
\begin{gathered}
\operatorname{Res}_\beta(P_R,V_R)
=11664(2\alpha^2-1)^2(11087\alpha^2+377\alpha-4809),\\
-108(2\alpha^2-1)
 (58\alpha\beta+113\alpha+113\beta+29).
\end{gathered}
$$

Away from the forbidden pole, a common root would have
$\beta=-(113\alpha+29)/(58\alpha+113)<0$ for $\alpha\ge0$.
In particular the positive root of the quadratic, in
$(6418,6419)/10^4$, has its companion in $(-676,-675)/10^3$.
No two distinct allowed right parameters share a base. ∎

**Theorem 13.2 (A cross-chart acquired-base coincidence with separated
terminals).** The two charts of Theorem 13.1 have a positive algebraic
acquired-base crossing that lifts to two strict complete worlds in the
same $C(p,v)$ for every sufficiently small common $b>0$. These two
worlds form neither a terminal-$J$ nor a terminal-$M$ pair.

**Proof.** Write $t$ for the left parameter and $s$ for the right
parameter. Define

$$
\begin{aligned}
P={}&32t^2s^2-16t^2-32ts^3-64ts^2+8ts+20t
       +32s^3+34s^2-8s-5,\\
V={}&90t^2s^2-45t^2-90ts^3-180ts^2+66ts+141t
       +90s^3+86s^2-66s-94.
\end{aligned}
$$

The response differences are exactly

$$
p_L(t)-p_R(s)=\frac{-3P}{10(t-1)(2s^2-1)},\qquad
v_L(t)-v_R(s)=\frac{3V}{10(t-1)(2s^2-1)}.
$$

Thus the numerator resultant has the fixed normalization

$$
\operatorname{Res}_s(-3P,3V)=5832(t-1)^3q(t),
$$

$$
q(t)=865318176t^4-1266956640t^3-1221999600t^2
                      +2785386204t-1161858481.
$$

Equivalently $\operatorname{Res}_s(P,V)=-8(t-1)^3q(t)$.
There is a unique root $t_*$ in

$$
I=(1019013955,1019013956)/10^9,
$$

since $q$ is negative at the left endpoint, positive at the right
endpoint, and $q'>0$ throughout $I$. The degree-one subresultant gives

$$
s_*=-\frac{367476t_*^2-708156t_*+338601}
              {188616t_*^2-272820t_*+83819},\qquad
\frac{8610543}{10^7}<s_*<\frac{8610545}{10^7}.
$$

The denominator excludes zero on $I$. Substitution, or division by
$q$, gives $P(t_*,s_*)=V(t_*,s_*)=0$.
The Jacobian determinant of the actual difference functions is

$$
\frac{9\{696t^2s^2+2712t^2s+348t^2-1392ts^2-5424ts-696t
                 -154s^4+845s^2+2658s+307\}}
     {50(t-1)^2(2s^2-1)^2}.
$$

On the isolating box its absolute value is in $(129000,130000)$,
so it is nonzero. The exact finite-$b$ charts
$r_L=tb$, $r_R=1-sb$ extend analytically near $(0,t_*,s_*)$;
their limiting $\Lambda$ values are nonzero. The implicit-function
theorem supplies $t(b),s(b)$ with identical actual acquired responses
for small positive $b$. Both sources are strict, they lie near different
ends of the $r$ interval, and the parent converse supplies their complete
gains and drifts. The limiting $p$ is in $(-2,-1)$, so the common
base stays off $24$.

The same rational isolating box gives

$$
a_L(t_*)\in(167,168),\qquad m_L(t_*)\in(250,251),\qquad
a_R(s_*)=m_R(s_*)\in(255,256).
$$

These strict separation margins persist on the lifted branches. Thus
the crossing is a genuine same-child coincidence of acquired bases,
but neither terminal equality holds between these two labels. No
assertion about other labels in that entire child is needed. ∎

**Proposition 13.3 (Exact cross-chart terminal obstruction).** Two valid
opposite-chart boundary parameters cannot have both the same limiting
acquired base and equal limiting response for either terminal action.
Same-chart acquired-base equality forces equal limiting parameters;
it does not decide tangent lifts of a diagonal limit.

**Proof.** Retain $P,V$ from Theorem 13.2. The vanishing numerators
for the two cross-chart terminal differences are, up to nonzero rational
scalars,

$$
\begin{aligned}
F_J={}&768t^2s^2-384t^2-768ts^3-2304ts^2+464ts+1333t\\
&\quad+768s^3+1532s^2-464s-947,\\
F_M={}&768t^2s^2-384t^2-768ts^3-1536ts^2+464ts+949t\\
&\quad+768s^3+760s^2-464s-561.
\end{aligned}
$$

In the lexicographic order $s>t$ each of the ideals
$\langle P,V,F_J\rangle$ and $\langle P,V,F_M\rangle$ has
the Gröbner basis

$$
\{2s^2-1,\ t-1\}.
$$

Its only common zeros are forbidden chart poles. The same-chart claim
is Theorem 13.1. These conclusions concern finite nondegenerate ray
parameters. Ratios tending to zero or infinity, higher-order diagonal
lifts, and a boundary endpoint meeting a finite-$b$ world require their
own conditions; they are not excluded by this calculation. ∎

## 14. Legal analytic sheets over relative regular regions

**Definition 14.1 (Critical values of the complete-world projection).**
Use $X,Y,\pi$ from Definition 12.2. Let $\Sigma_{\rm crit}\subset Y$
be the image of points at which the differential of $\pi$ has rank
less than two on the complete parent surface. This is the differential
of the actual whole-world projection, not merely of a quotient chart.

**Theorem 14.2 (Regional legal sections and the two pair products).**
Let $\mathcal U$ be a connected contractible open subset of $Y$ with

$$
\mathcal U\cap
(\mathcal B_\partial\cup\{q_\infty\}\cup\Sigma_{\rm crit})
=\varnothing.
$$

Then $\pi$ is proper over compact subsets of $\mathcal U$. Its
entire fibres consist of $N$ distinct legal analytic sections
$W_1,\ldots,W_N$, with constant $0\le N\le24$. For empty products
interpreted as one, set

$$
\Delta_J=\prod_{i<j}(f_{MJ}(W_i)-f_{MJ}(W_j)),\qquad
\Delta_M=\prod_{i<j}(f_{MM}(W_i)-f_{MM}(W_j)).
$$

For each $q\in\mathcal U$,

$$
q\in D_J\cap D_M
\quad\Longleftrightarrow\quad
\Delta_J(q)=\Delta_M(q)=0.
$$

A sequence of distinct same-base pairs coalescing at a strict world
of $X$ can do so only at a critical point of $\pi$.

**Proof.** The whole parent is a real analytic surface over the strict
source domain with equation

$$
e\Lambda+(24/5)(b-1/8)\kappa=0.
$$

Where $\Lambda\ne0$, it solves analytically for $e$. At a singular
parent source the exhaustive singular-source theorem gives $b=1/8$
and a simple strict root of the source polynomial $\Phi$, so
$\Lambda_r\ne0$. Off $p=24$, one has $e\ne0$ by F, Lemma 30.2;
the displayed equation consequently has nonzero $r$ derivative there.
The one-polynomial reconstruction is analytic in these coordinates.
This establishes the surface also at the singular parent sources.

If an inverse image of a compact subset of $\mathcal U$ were not
compact, a sequence in it would have a subsequence escaping every
compact subset of $X$, and a further base-convergent subsequence.
Its base limit would be a nonproper value in $\mathcal U$, contrary
to Theorem 12.3. Thus the projection is proper there. Avoidance of
$\Sigma_{\rm crit}$ makes it a local analytic diffeomorphism.
F, Theorem 32.1, bounds each entire fibre by $24$.

A proper local diffeomorphism has evenly covered neighbourhoods: take
the local inverse neighbourhoods of the finitely many points in a fibre;
properness excludes additional inverse points entering from outside them
after shrinking the base neighbourhood. Its image is open and closed
in the connected $\mathcal U$. It is therefore either empty, giving
$N=0$, or a finite covering of constant degree. Contractibility
trivializes this covering, and its local analytic inverses give the
sections. This is the classical covering argument, applied here after
the explicit source-specific nonproper classification; compare
Lazard–Rouillier, Theorem 1 and real-case Remark 1, cited in
Assumption 6.1. Every section is an actual complete world, and they
exhaust the entire child.

Each product vanishes exactly when its own terminal action has a
distinct pair among those sections. The two products may vanish through
overlapping or disjoint pairs, and their common terminal values may
differ. Thus their simultaneous vanishing is exactly Definition 1.2.
The sections are mathematical labels, not acquired observations.

For the coalescence assertion, a noncritical $W$ has a neighbourhood
on which $\pi$ is
injective by the inverse-function theorem. Both convergent labels are
eventually in that neighbourhood and have equal acquired base, which
would make them equal. This contradicts their distinctness. This is a
necessary boundary condition for pair continuation, not an exclusion of
critical collisions or a guarantee that distinctness survives limits. ∎


## 15. An ordinary small-$b$ collision and its strict two-world limit

**Definition 15.1 (Three regular labels and an exact rational centre).**
Let $\Psi^\sharp(r,b,j)=(p,v,a,m)$ mean the regular parent lift of
Definition 7.1 and its four original response functions, with
$n=j+r,T=1+b,U=1+2b$. Here $j$ may first be an independent chart
variable; the source identity is imposed on legal labels. Thus the
one interpolant has samples

$$
(-24-e,-e/j,(27/5-e)/T,-e/n),\qquad
 e=-\frac{24(b-1/8)\kappa}{5\Lambda}.
$$

Define

$$
\begin{aligned}
\mathcal N(r,b)&=\Psi^\sharp(r,b,b+r(1-r)/b),\\
\mathcal A(u,t)&=\Psi^\sharp(1-ut,t,t+u-u^2t).
\end{aligned}
$$

For $t>0$, $\mathcal A$ is precisely the original strict-source chart
when $0<1-ut<1$; the third argument is
$b+r(1-r)/b=t+u-u^2t$. At $t=0$ it is an auxiliary analytic
boundary chart with $(r,b,c)=(1,0,u)$.
For $z=(u,r_B,b_B,r_Q,b_Q)$ write

$$
A=\mathcal A(u,t),\quad B=\mathcal N(r_B,b_B),\quad
Q=\mathcal N(r_Q,b_Q),
$$

and define the five-component rational function

$$
\mathcal E(z,t)=(p_A-p_B,\ v_A-v_B,\ m_A-m_B,\ p_A-p_Q,\ v_A-v_Q).
$$

Let $z_c$ have denominator $10^{95}$ and the following five numerators,
in that coordinate order:

$$
\begin{gathered}
100428761387816823696480171765441312044987893072648279126168973533098255816050448537824871433525\\
70716954727879839279480184367659045851078335574041753095114351262855582985017322755503173275409\\
30814988061236982635547616875755700750487136119740475471798671699545887071653908946326719388474\\
6104050961496413159205837486701483942203552259477108118661530488778466938075465071686482585820\\
5847642733657720862719432264186152695748000961996411761678819588053707155234072033938760516187
\end{gathered}
$$

Let $(p_c,v_c)$ have denominator $10^{95}$ and respective numerators

$$
\begin{gathered}
367068393378998395246026571982456711245305890922162694264197866224863529619880873392282957453850\\
5679629840728084907886878607821919633308547340517015332315858757685186396688860630206243979276432
\end{gathered}
$$

Define the closed base rectangle and parameter box

$$
\mathcal B_0=\{(p,v):|p-p_c|\le10^{-65},\ |v-v_c|\le10^{-65}\},
\qquad
\mathcal Z=\{z:\|z-z_c\|_\infty\le10^{-70}\}.
$$

Every base in $\mathcal B_0$ has $3<p<4$ and $56<v<57$.

**Theorem 15.2 (The parameterized exact regular lift).** For every
$t\in[0,10^{-80}]$ there is a unique $z(t)\in\mathcal Z$ with
$\mathcal E(z(t),t)=0$. It varies real analytically and has an analytic
extension near $t=0$. Its common base $q(t)=(p(t),v(t))$ is in the
interior of $\mathcal B_0$. For positive $t$ the three labels are
strict complete worlds in one acquired child, with a distinct
terminal-$M$ pair $\{A(t),B(t)\}$.

**Proof.** The following specifies the rational interval certificate.
For a real interval, every elementary operation is enclosed outward
with endpoints in $10^{-300}\mathbb Z$: the lower endpoint is rounded
by $10^{-300}\lfloor10^{300}y\rfloor$, the upper by
$10^{-300}\lceil10^{300}y\rceil$. Addition and subtraction use endpoint
bounds, multiplication takes the extremal four endpoint products, and
inversion uses $[1/u,1/l]$ only when zero is excluded. Derivatives are
propagated by

$$
D(xy)=y\,Dx+x\,Dy,\qquad
D(x/y)=\{Dx-(x/y)Dy\}/y.
$$

All centres below, including inverses of centre matrices, are exact
rationals before these interval enclosures are taken. Put

$$
C=(\partial_z\mathcal E(z_c,0))^{-1}\in\mathbb Q^{5\times5}.
$$

The rational Jacobian is invertible, and evaluation on the complete
box $\mathcal Z\times[0,10^{-80}]$ gives

$$
\|I-C\partial_z\mathcal E(z,t)\|_\infty<10^{-55},\qquad
\|C\mathcal E(z_c,t)\|_\infty<10^{-75}.
$$

All denominators in these evaluations exclude zero. In particular

$$
10^{-75}+10^{-55}10^{-70}<10^{-70}.
$$

The map $z\mapsto z-C\mathcal E(z,t)$ is therefore a strict contraction
of $\mathcal Z$ into itself for every parameter. The contraction theorem
on a closed complete box gives its unique fixed point, and invertibility
of $C$ turns that equation into $\mathcal E=0$. Moreover

$$
\|z(t)-z_c\|_\infty
\le\frac{10^{-75}}{1-10^{-55}}<2\cdot10^{-75}.
$$

The same derivative inequality makes the Jacobian invertible at every
solution. The analytic implicit-function theorem supplies local analytic
solutions, which coincide by uniqueness. Evaluation of the response
functions on this smaller solution box, with $0\le t\le10^{-80}$,
gives $|p(t)-p_c|<10^{-65}$ and $|v(t)-v_c|<10^{-65}$.

Here are the source and response enclosures for the whole parameter
interval; the $A$ source is strict only for $t>0$.

| Label | Source restrictions | $\Lambda$ | $d$ | $f_{MJ}$ | $f_{MM}$ |
|---|---|---|---|---|---|
| $A(t)$ | $b=t$, $r=1-ut$, $1<u<2$ | $(2,3)$ | $(25,26)$ | $(349,352)$ | $(350,351)$ |
| $B(t)$ | $r\in(707,708)/1000$, $b\in(308,309)/1000$ | $(-1/4,-6/25)$ | $(35,36)$ | $(268,271)$ | $(350,351)$ |
| $Q(t)$ | $r\in(61,62)/1000$, $b\in(58,59)/1000$ | $(7/100,8/100)$ | $(40,41)$ | $(221,223)$ | $(338,339)$ |

These are rational interval enclosures of the displayed functions, not
conditions restricting the original source domain. For $A$, $u>1$ and
$0<t\le10^{-80}$ prove $0<1-ut<1$ symbolically. All $j,n,T,U$
are positive. The three disjoint source boxes give distinct worlds;
$B,Q$ remain strict also at $t=0$. The complete parent converse gives
one fixed drift and one whole degree-at-most-three polynomial for each
positive-$t$ label. The unequal clock-zero and clock-one readings make
each polynomial nonzero. The equations $\mathcal E=0$ impose a single
common acquired $p,v$ on all three and impose $m_A=m_B$.

The same rational enclosures give, for each of these three labels,

$$
|\Lambda|>1/100,\qquad
1000<F_0(n/U,p(t),v(t))<10000
\quad(0\le t\le10^{-80}).
$$

Thus all three positive-$t$ worlds lie outside the exceptional union of
Definition 3.1. Their gains use the original interpolation nodes and
original clocks throughout. ∎

**Theorem 15.3 (A uniform entire-child certificate on $\mathcal B_0$).**
Every entire original child above a base in $\mathcal B_0$ has at most
three legal complete worlds, and $f_{MJ}$ is injective on that entire
child.

**Proof.** Use exactly the $f,K=4k,D,F_0,R,\alpha,\beta$ of Sections
2 and 7, with the fixed normalization

$$
\operatorname{Res}_d(f,K)=256D^8F_0^2R.
$$

Theorem 4.1 puts every legal world on $R=0$, including singular
sources, zero drift and $F_0=0$. Let $R_0(x)=R(x,p_c,v_c)$. The
following eighteen Gaussian-rational seeds are exact finite decimals:

$$
\begin{gathered}
(-1.85357241,0),\ (-1.71791792,0),\ (-1.71566920,0),\\
(-1.53914181,0),\ (-1.45573127,0),\ (-1.40341508,0),\\
(-0.376163194,0),\ (0.334468126,0),\ (0.531281700,0),\\
(0.683220700,-0.096682450),\ (0.683220700,0.096682450),\\
(0.984507130,0),\ (1.04394781,0),\ (1.10873466,0),\\
(1.19546576,0),\ (2.00428761,0),\ (2.13729919,0),\ (5.58085280,0).
\end{gathered}
$$

Define $\operatorname{Round}_{100}(y)=
10^{-100}\lfloor10^{100}y+1/2\rfloor$ on rational real numbers,
and componentwise on $\mathbb Q(i)$. For each seed $s_i$ define the
finite rational sequence

$$
c_{i,0}=s_i,\qquad
c_{i,k+1}=\operatorname{Round}_{100}
 \left(c_{i,k}-\frac{R_0(c_{i,k})}{R'_0(c_{i,k})}\right)
\quad(0\le k<8),
\qquad c_i=c_{i,8},\quad\gamma_i=1/R'_0(c_i).
$$

Every indicated denominator is nonzero. Let $\mathcal R_i$ be the
closed rectangle

$$
\max\{|\operatorname{Re}(x-c_i)|,
          |\operatorname{Im}(x-c_i)|\}\le10^{-50}.
$$

These eighteen rectangles are pairwise disjoint. For complex interval
evaluation use a pair of real intervals with the outward rounding of
Theorem 15.2. Multiplication by $a+ib$ has sup-component operator bound
$|a|+|b|$. The complete uniform root enclosures, for every
$(p,v)\in\mathcal B_0$ and $x\in\mathcal R_i$, are

$$
\begin{aligned}
&|\operatorname{Re}(1-\gamma_iR_x(x,p,v))|
 +|\operatorname{Im}(1-\gamma_iR_x(x,p,v))|<10^{-35},\\
&\max\{|\operatorname{Re}(\gamma_iR(c_i,p,v))|,
          |\operatorname{Im}(\gamma_iR(c_i,p,v))|\}<10^{-55},\\
&|[x^{18}]R(x,p,v)|>10^{19}.
\end{aligned}
$$

The root maps $x\mapsto x-\gamma_iR(x,p,v)$ are contractions of their
rectangles into themselves because

$$
10^{-55}+10^{-35}10^{-50}<10^{-50}.
$$

They give eighteen distinct roots. The leading-coefficient bound makes
the degree eighteen throughout the base box, so these exhaust all roots
and every root is simple. The sixteen real-centred rectangles have real
roots by conjugation and uniqueness. Seven are negative and nine are
positive. The two other rectangles stay off the real axis.

It remains to filter all roots by necessary whole-world conditions.
Write $f=a_fd^2+b_fd+c_f$ and
$K=A_4d^4+A_3d^3+A_2d^2+A_1d+A_0$. The exact forms in Section 2 are

$$
\begin{aligned}
\alpha={}&A_4(-b_f^3+2a_fb_fc_f)
 +A_3a_f(b_f^2-a_fc_f)-A_2a_f^2b_f+A_1a_f^3,\\
\beta={}&A_4(-b_f^2c_f+a_fc_f^2)
 +A_3a_fb_fc_f-A_2a_f^2c_f+A_0a_f^3,
\end{aligned}
$$

and $f$ divides $a_f^3K-\alpha d-\beta$ as a polynomial. Hence
$\alpha d+\beta=0$ at every actual common root even when $a_f=0$.
Put $d^*=-\beta/\alpha$, evaluate the interpolant $H_i$ of
Definition 1.1 at $d^*$, and put

$$
\mathfrak B=294/5-2d^*-H_2,\qquad
C_0=(d^*)^2+\mathfrak B^2,\qquad
N_0=-d^*H_0+\mathfrak B H_2.
$$

On every one of the eighteen rectangles, uniformly over
$\mathcal B_0$, the interval unit bounds are

$$
|\alpha|>10^{12},\qquad |H_1|>1/10,\qquad |C_0|>1,\qquad |N_0|>1.
$$

These modulus inequalities include the nonreal rectangles; no ordering
of their complex values is intended. The denominators $x,x+1,x+2$
also exclude zero. For an actual world, F, Lemma 30.2, then forces

$$
U=N_0/C_0,\quad b=(U-1)/2,\quad
j=U(24-d^*)/H_1,\quad r=xU-j.
$$

The same interval evaluation gives the following complete filter for
positive roots. The seed identifies a rectangle, not a legal label.

| Real seed | Necessary exclusion or candidate range | $f_{MJ}$ range when applicable | $f_{MM}$ range when applicable |
|---|---|---|---|
| $0.334468126$ | $r>5$ | — | — |
| $0.531281700$ | $b<-9$ | — | — |
| $0.984507130$ | $r\in(61,62)/1000$, $b\in(58,59)/1000$ | $(221,223)$ | $(338,339)$ |
| $1.04394781$ | $r\in(707,708)/1000$, $b\in(308,309)/1000$ | $(268,271)$ | $(350,351)$ |
| $1.10873466$ | $b<0$ | — | — |
| $1.19546576$ | $b<0$ | — | — |
| $2.00428761$ | $r\in(999,1001)/1000$, $b\in(-10^{-40},10^{-40})$ | $(349,352)$ | $(349,352)$ |
| $2.13729919$ | $b<0$ | — | — |
| $5.58085280$ | $b<0$ | — | — |

The terminal expressions used in these enclosures are the zero-safe
original-clock formulas

$$
\begin{aligned}
\tau_J&=d^*+
 \left(4x+\frac12+\frac{C_0}{2N_0}
                    -\frac{2(24-d^*)}{H_1}\right)H_7,\\
\tau_M&=d^*+(2x+3)H_7.
\end{aligned}
$$

They agree with the actual $f_{MJ},f_{MM}$ by Definition 1.1.
Every operation in this certificate has nonzero denominator on the stated
box. It uses no inverse of $H_0,d,F_0,H_7$ or of a leading gain
coefficient. The $H_1$ inverse has its explicit unit bound, and its
nonvanishing for actual off-$24$ worlds is also part of the faithful
reconstruction. Thus no allowed sampled root has been silently deleted.

Negative and nonreal roots cannot be actual $x=n/U>0$. Six of the nine
positive branches violate strict source guards. On each of the other
three, $\alpha$ fixes the only possible drift; F, Lemma 30.2, then
allows at most one complete world. There are at most three legal worlds,
and their three possible terminal-$J$ intervals are disjoint. This proves
injectivity on the entire child, including any unused or exceptional
worlds. A surviving algebraic branch is still not presumed legal. ∎

**Theorem 15.4 (Exactly three worlds, and the algebraic bridge at $t=0$).**
For $0<t\le10^{-80}$ the entire child at $q(t)$ consists exactly of
$A(t),B(t),Q(t)$. Its unique unordered terminal-$M$ pair is
$\{A(t),B(t)\}$, and $f_{MJ}$ is injective. The entire child at
$q_0=q(0)$ consists exactly of the two strict worlds $B(0),Q(0)$;
both terminal maps are injective there.

**Proof.** Theorem 15.2 supplies three distinct strict worlds for every
positive parameter. Theorem 15.3 permits at most three in the entire
child, so they exhaust it. The common $A,B$ terminal-$M$ value is in
$(350,351)$, whereas $Q$ has value in $(338,339)$. Thus there is exactly
one unordered $M$ edge. The three $J$ intervals are pairwise disjoint,
and the $\Lambda,F_0$ guards show that the entire positive-$t$ child
avoids $E$.

For the limiting assertion it is essential to identify the algebraic
boundary branch and then reject its strict source lift. At $t=0$ the
exact boundary identities of $\mathcal A$ are

$$
\begin{gathered}
p_A(u,0)=-\frac{6(8u^3-24u^2-2u+15)}{5(2u^2-1)},\qquad
v_A(u,0)=\frac{3(45u^3+215u^2-33u-133)}{5(2u^2-1)},\\
a_A(u,0)=m_A(u,0)
 =\frac{3(384u^3+1039u^2-232u-610)}{5(2u^2-1)},\\
d_A(u,0)=\frac{3(81u^2+u-40)}{5(2u^2-1)},\qquad
\Lambda_A(u,0)=\frac{4(2u^2-1)}{u(u+1)},\qquad x_A(u,0)=u+1.
\end{gathered}
$$

Let $u_0$ be the first coordinate of the unique $z(0)$, and let
$x_0=u_0+1$, $d_0=d_A(u_0,0)$. The positive-$t$ whole polynomials
have coefficientwise limits; $U_A=1+2t\to1$. Their necessary polynomial
identities $f=k=0$ therefore give

$$
f(x_0,d_0,q_0)=k(x_0,d_0,q_0)=0.
$$

The limiting guard $1000<F_0(x_0,q_0)<10000$ and $D(x_0)>0$,
together with the fixed determinant factorization, now imply
$R(x_0,q_0)=0$. This step uses limiting $f=k$ and the nonzero
$F_0$ factor; it does not merely presume that the boundary chart is a
world on the carrier.

The rational enclosures put $x_0$ in the rectangle identified by
$2.00428761$. There is exactly one root there at $q_0$ by Theorem 15.3.
Its $\alpha$ unit and $\alpha d+\beta=0$ fix its drift as $d_0$.
Consequently any purported actual world on this remaining candidate
branch has exactly $(x,d)=(x_0,d_0)$. The four-node interpolant $H$
is then the limiting $U_Ag_A=g_A$. The limiting original clock-zero
and clock-two equations give

$$
-d_0H_0+\mathfrak B H_2
=d_0^2+\mathfrak B^2=C_0,
\qquad U=N_0/C_0=1.
$$

Here $C_0$ is nonzero by the displayed certificate. Reconstruction
forces $b=0$, and the original source limits give $r=1,j=u_0$.
It violates the strict guards $U>1$, $b>0$, $r<1$, and contributes
no legal world. All other excluded roots remain excluded by the same
uniform filter. The two labels $B(0),Q(0)$ are still strict regular
worlds, so they exhaust the child. Their $J$ values are separated, and
so are their $M$ values by $(350,351)$ and $(338,339)$.
The boundary identity $a_A=m_A$ is an equality for one inadmissible
label, not a distinct pair or an acquired extra response. ∎

**Corollary 15.5 (Nonclosed terminal-$M$ image and no positive lower
endpoint bound).** The set $D_M$ is not closed relative to $Y$.
There is no uniform positive lower bound on $b$ for its collision
endpoints, even when both endpoints are required to have $b<1$.
The strict terminal-$M$ pair projection to $Y$ is nonproper.
Nevertheless $\mathcal B_0\cap D_J=\varnothing$.

**Proof.** Every positive $t$ gives $q(t)\in D_M$ with endpoint
$b(A(t))=t$, while $q(t)\to q_0\notin D_M$ by Theorem 15.4.
All bases are in the same off-$24$ rectangle. Both endpoints have
$b<1$, since $b(B(t))<309/1000$. Thus no positive lower endpoint
bound exists. In the space

$$
\mathcal P_M=\{(q,W,W'):q\in Y,\ W,W'\in C(q),\ W\ne W',\
 f_{MM}(W)=f_{MM}(W')\},
$$

choose any sequence $t_i\downarrow0$. Its bases and their limit form
a compact subset of $Y$, but the associated pair sequence has no
convergent subsequence in $\mathcal P_M$: its $A$ source tends to
$b=0,r=1$. The inverse image of this compact base set is therefore
noncompact. The last assertion is whole-child injectivity in Theorem
15.3. Nothing in this argument asserts nonproperness or existence of
points of the joint pair correspondence. ∎

## 16. Exact remaining incidence and supplier scope

**Definition 16.1 (The remaining guarded joint problem).** On the
complete original world space define, for $E\in\{J,M\}$,

$$
\mathcal P_E=\{(q,W_0,W_1):q\in Y,\ W_0,W_1\in C(q),\
 W_0\ne W_1,\ f_{ME}(W_0)=f_{ME}(W_1)\}.
$$

The original joint relation is the fibre product
$\mathcal P_J\times_Y\mathcal P_M$. Only distinctness within each
pair is required. Cross-pair reuse and unequal common terminal values
are allowed. By Corollary 11.4, bounding $b,c$ above for every world
in a collision child does not change this relation; it retains companions
unused by either pair. Theorems 12.1–12.3 give finite-$p$ bounds and
the explicit individual-world nonproper values relative to $Y$, not a
uniform bound as $|p|\to\infty$. The two-sheet example of Proposition
11.5 prevents replacing a legal child by a singleton, and Corollary
15.5 prevents using a positive lower endpoint-$b$ bound for $D_M$.

Theorem 9.10 still places every joint base whose entire child merely
meets $E$ in the finite outer union $Z_E$ on $Q_{10},S_4,Q_{24}$.
Every divisor intersection remains included, and its exceptional world
may be unused by both pairs. This outer restriction does not isolate,
strictly lift or classify its points. The drift chart on $Q_{24}$ is
the Chinese-remainder chart of Section 9; the old $\alpha$ inverse is
not an assumption there. The fixed F31 normalization, in particular
$S=S_\star$ and the residues $41,46$ used in that section, remains
unchanged.

For children avoiding $E$, the ordinary common components, isolated
carrier intersections, strict-real lifts, and relevant $E_0=0$ strata
outside the covered image curves still require a decision. On a region
satisfying Theorem 14.2 this decision is exactly the simultaneous zero
condition for the two products of legal sections. Neither that condition,
the boundary classification, nor the local $J$ exclusion in
$\mathcal B_0$ decides its truth on the remaining base domain.
Source-boundary losses, critical diagonal coalescences and unbounded
acquired-base limits retain their original strict guards. Boundary sources,
complex roots and unfiltered interval labels are never legal whole worlds.

The positive criterion remains four complete labels at one common real
$p\ne24,v$, with the two within-pair squared distances
$\,(x_0-x_1)^2+(d_0-d_1)^2>0$ and its $M$ analogue. The negative
criterion remains exclusion of all such labels over the entire $Y$.
These supporting statements supply neither criterion. Even a positive
sixth-$M$ child would still leave the sixth-$J$ condition at that same
fifth response $p$, the fifth-$J$ and common-parent conditions, and the
ancestor obligations of O, Theorem 17.1. No fifth-$M$ $L_2$, $H_4$
$L_3$, root $L_7$ or eight-versus-nine conclusion is imposed by these
reductions.

**Assumption 16.2 (Classical premises and source-specific deductions).**
The interpolation, contraction, implicit-function, Sturm, resultant and
covering principles used in Sections 11–15 are standard mathematical
premises, used inside the displayed source-specific arguments. Their
scopes are as follows.

| Premise | Use in these arguments |
|---|---|
| O, Theorems 2.1–2.2, Lemma 12.2 and Theorem 12.3 | Complete strict parent lift, one whole polynomial and one fixed drift, the full-source $\Lambda,A_5$ obstruction, and uniqueness including singular sources. |
| F, Lemmas 30.2, 31.2–31.3 and Theorem 32.1; this volume, Theorems 4.1 and 7.4 | Faithful whole-world reconstruction, the fixed $R$ normalization and all-world carrier, and the existing whole-child large-$b$ theorem. The bound $24$ is used without a new proof or optimization. |
| Berrut–Trefethen, §2, and Banach, pp. 133–181, cited in Sections 1–2 | Distinct-node interpolation and contraction on the specified complete boxes. Neither supplies any FIB collision or strict-source converse. |
| Lazard–Rouillier, Definition 1, Theorem 1 and real-case Remark 1, [primary report](https://inria.hal.science/inria-00070678/document) | Analytic covering after critical, nonproper and inequation boundaries are treated. Complex exceptional events need not be real events; the specific boundary set here is derived from the parent equations. |
| Gaillard–Safey El Din, Problem 1 and Theorem 2.4, [primary text](https://arxiv.org/html/2402.07782v2) | Finite-algebra signatures and strict-sign filtering under the stated finite-fibre hypotheses. The parameter classification in Problem 1 has a dense-cover conclusion, not automatic exceptional-inclusive coverage of this joint relation. |
| Nuno-Ballesteros–Peñafort-Sanchis, Definition 2.1 and Example 2.2, [primary text](https://arxiv.org/html/1509.04990v2) | Distinct multiple points must be separated from their diagonal specializations. No holomorphic stability hypothesis or four-distinct-label condition is transferred to this real pair fibre product. |
| Sections 11–15 | The particular reciprocal-chart invariants, guarded finite-source slope obstruction, four-face finite-base classification, cross-chart lift and terminal separation, and exact small-$b$ ordinary collision family with its whole-child filter. |

The existing $p=24$ joint child, exact-$p_J$ exclusion and published
single terminal-$M$ example retain the scopes in Assumption 1.3. No
result for a different literal history is a premise for this joint
relation. The analytic sections and all auxiliary algebraic coordinates
are mathematical descriptions of possible worlds; the only available
reads and actions are still those in Definition 1.1.

## 追加锚（本行以下为增补区）

## 17. Singular-line elimination with complete strict-real certificates

**Definition 17.1 (Actual singular-endpoint incidence and its coefficient field).**
Retain exactly the complete worlds and original-clock child of Definition
1.1, and write $q=(p,v)$ with $p\ne24$. In particular each world has one
whole nonzero real polynomial of degree at most three and one fixed real
drift, including lower degrees, sampled or repeated roots and zero drift.
Use the actual set $\mathcal B_{\mathcal S,M}$ of Theorem 8.4:

$$
\mathcal B_{\mathcal S,M}
=\{q:\exists W\ne W'\in C(q),\quad
 f_{MM}(W)=f_{MM}(W'),\quad\Lambda(W)\Lambda(W')=0\}.
$$

Thus membership includes the complete reconstruction equalities and strict
guards; the unfiltered outer projection in the proof of Theorem 8.4 is a
different set. Let

$$
\begin{gathered}
K=\mathbb Q[\theta]/(\Phi(\theta)),\qquad
\Phi(X)=438272X^4-931328X^3+540800X^2-50728X-853,\\
I_-=(134815875067,134815875068)/10^{12},\qquad
I_+=(902449681772,902449681773)/10^{12}.
\end{gathered}
$$

Irreducibility is supplied by the modulo-seven certificate in Theorem
3.2. The two strict real embeddings $\theta_-,\theta_+$ are its roots in
$I_-,I_+$; O, Theorems 4.2 and 29.2, exhaust all legal singular sources
by $(\theta_-,1/8),(\theta_+,1/8)$. Other embeddings are not strict
singular sources. All field coefficients below are reduced uniquely to
the power basis $1,\theta,\theta^2,\theta^3$ over $\mathbb Q$.

At the symbolic singular source put

$$
\begin{gathered}
b_s=1/8,\quad j_s=1/8+8\theta(1-\theta),\quad n_s=j_s+\theta,\\
T_s=9/8,\quad U_s=5/4,\quad x_s=n_s/U_s,\\
A_{5s}=1+(U_s+n_s)(4-15/j_s+20/T_s-10/n_s),\\
A_{6s}=1+(2U_s+n_s)(10-36/j_s+45/T_s-20/n_s),\\
A_{7s}=1+(3U_s+2n_s)(20-70/j_s+84/T_s-35/n_s),\\
K_{6s}=(2U_s+n_s)(240-243/T_s),\qquad
K_{7s}=(3U_s+2n_s)(480-2268/(5T_s)).
\end{gathered}
$$

These are Definition 8.1's coefficients, with $K_{5s}=0$. The full
singular line is

$$
p_s(t)=24+A_{5s}t,\qquad
v_s(t)=24+K_{6s}+A_{6s}t,\qquad
m_s(t)=24+K_{7s}+A_{7s}t.
$$

Here $t=d_s-24$ is the singular world's drift coordinate and
$A_{5s}\ne0$, so $p_s(t)\ne24$ is equivalent to $t\ne0$.
O's full parent converse supplies one complete singular world for each
$t$ at either strict embedding. These affine responses belong to that
same whole polynomial at the original clocks, rather than to independent
choices of gain samples.

**Definition 17.2 (Unscaled companion polynomials).** For independent
variables $x,d,t$, substitute $p=p_s(t),v=v_s(t)$ and put

$$
\begin{gathered}
D=x(x+1)(x+2),\quad z_3=(24-d)(x+1)(x+2),\quad z_4=(18-d)D,\\
z_5=(p_s(t)-d)x(x+2),\qquad z_6=(v_s(t)-d)x(x+1),\\
a_0=20z_3-45z_4+36z_5-10z_6,\\
a_1=10z_3-20z_4+15z_5-4z_6,\qquad
a_2=4z_3-6z_4+4z_5-z_6,\\
a_7=-z_3+4z_4-6z_5+4z_6,\qquad z_*=xa_1-D(24-d),\\
f=5dDa_2+a_0\bigl((294-10d)D-5a_2\bigr),\\
\mathscr K=4a_0^2z_*^2+2a_0(dD-a_0)z_*a_1
 -(a_0+dD)\bigl(dD+(1-2x)a_0\bigr)a_1^2,\\
h=dD+(2x+3)a_7-m_s(t)D=\ell d+N_0+N_1t,\\
\ell=-8x^4-29x^3-18x^2+15x+6,\qquad
N_0=h|_{d=t=0},\quad N_1=[t](h|_{d=0}).
\end{gathered}
$$

The symbol $\mathscr K$ is $4k$ in F, Definition 31.1, and is the
$K$ used in Theorem 8.4; it is not the coefficient field $K$.
These formulas fix all coefficient normalizations. Every actual world
in $C(p_s(t),v_s(t))$ with terminal-$M$ response $m_s(t)$ satisfies
$x>0$ and $f=\mathscr K=h=0$. Indeed $a_i=DH_i$ and $a_7=DH_7$,
so the terminal equation is exactly $h=0$; the two necessary source
equations are F, (31.4). No converse from these cleared equations to a
world is part of this definition.

**Lemma 17.3 (Fixed quadratic–quartic elimination inside the companion
system).** For coefficients in a commutative ring, write

$$
F=Ay^2+By+C,\qquad G=G_4y^4+G_3y^3+G_2y^2+G_1y+G_0
$$

and define the polynomial expressions

$$
\begin{aligned}
\alpha&=G_4(-B^3+2ABC)+G_3A(B^2-AC)-G_2A^2B+G_1A^3,\\
\beta&=G_4(-B^2C+AC^2)+G_3ABC-G_2A^2C+G_0A^3,\\
Z(F,G)&=A\beta^2-B\alpha\beta+C\alpha^2.
\end{aligned}
$$

Then, with the fixed degree-$(2,4)$ Sylvester determinant,

$$
\begin{gathered}
A^3G=HF+\alpha y+\beta,\\
H=A^2G_4y^2+(A^2G_3-ABG_4)y
  +A^2G_2-ABG_3+(B^2-AC)G_4,\\
Z(F,G)=A^3\operatorname{Res}_y(F,G).
\end{gathered}
$$

In particular every finite common root forces
$\alpha y+\beta=0$ and $Z(F,G)=0$, including specializations with
leading-degree drops.

**Proof.** Multiplication of $HF$ gives the first identity coefficient
by coefficient. The second is the fixed Sylvester determinant identity;
equivalently it is the quadratic norm of the linear remainder, first
over the universal coefficient fraction field and hence as a polynomial
identity over $\mathbb Z$. For a finite common root the evaluation vector
$(y^5,y^4,\ldots,1)^{\mathsf T}$ is in the kernel of the fixed Sylvester
matrix, regardless of the leading coefficients. No division by $A$ is
needed for either implication. This is the classical resultant method
of Moreno Maza, *The resultant*, Definition 4 and Propositions 5–7,
[primary text](https://www.csd.uwo.ca/~mmorenom/AM583/Lectures/ResultantGcd.html/node3.html),
applied here to the specified companion polynomials. ∎

**Lemma 17.4 (The terminal-equation pole and the self label).** At either
strict embedding there is no finite complex solution of
$\ell=0$, $h=f=\mathscr K=0$. If an actual companion instead has
$x=x_s$, it is the singular world itself.

**Proof.** In $L=K[x]/(\ell)$, $N_1$ is a unit. Define
$t_0=-N_0N_1^{-1}\in L$, with its unique representative of degree less
than four. Substitute this element into $f,\mathscr K$, reducing each
coefficient modulo $\ell$, and apply Lemma 17.3 with variable $d$.
Call its norm expression $Z_\ell\in L$, again represented in degree
less than four. The following complete modular data use descending
$x$-coefficient order; quotient-ring representatives have degree at most
three. Every rational coefficient denominator in these reductions is a
unit at the indicated prime.

| Object at $113,\theta=77$ | Descending coefficients or residue |
| --- | --- |
| $\ell$ | $(105,84,95,15,6)$ |
| $N_0\bmod\ell$ | $(111,56,99,77)$ |
| $N_1\bmod\ell$ | $(56,60,53,0)$ |
| $t_0$ | $(64,109,87,95)$ |
| $Z_\ell$ | $(64,67,87,21)$ |
| $\operatorname{Res}_x(\ell,N_1\bmod\ell)$ | $9$ |
| $\operatorname{Res}_x(\ell,Z_\ell)$ | $76$ |
| $x_s,\ell(x_s),A_{5s}$ | $91,24,86$ |

Here $\Phi(77)=0$ modulo $113$. The table is obtained by the circuits
of Definition 17.2, quotient-ring inversion of $N_1$, and Lemma 17.3,
without changing the scale of any polynomial. Thus the two nonzero
resultants prove

$$
\gcd_{K[x]}(\ell,N_1)=1,\qquad
\gcd_{K[x]}(\ell,Z_\ell)=1.
$$

The characteristic-zero inference uses a finite localization, not a map
from the whole field $K$ to $\mathbb F_{113}$. Specifically take the
subring of $K$ generated by the finitely many reduced power-basis
coefficients in the displayed calculation, inverting their rational
denominators. Because those denominators are prime to $113$ and
$\Phi(77)=0$, evaluation of the power-basis representatives defines the
required reduction on this subring. Determinants commute with reduction.
A nonzero reduced determinant cannot come from a zero element of $K$.
Since $K$ is a field, the two nonzero resultants give the stated gcds
and hence the units in $L$. Every real embedding is injective, so their
nonvanishing holds at both strict embeddings. The same argument applies
to each modular unit certificate below, with its stated prime and all
its coefficient denominators included in the finite localization.

If $\ell(x)=h(x,d,t)=0$, the first unit forces $t=t_0(x)$.
A finite common $d$ root of the remaining two polynomials would force
$Z_\ell(x)=0$ by Lemma 17.3. The second unit excludes this even if a
quadratic or quartic leading coefficient vanishes. Thus division by
$\ell$ loses no actual companion. This exclusion uses only necessary
equations and retains zero drift, lower gain degree, sampled or repeated
gain roots, and singular companions.

For the self case, exact substitution gives
$h(x_s,24+t,t)=0$, and $\ell(x_s)\ne0$, also certified by the table.
Since $h$ is linear in $d$, it fixes $d=24+t$. The singular world and
any actual companion then have the same $(x,d)$ at the same off-$24$
base. F, Lemma 30.2, identifies their entire polynomials and sources,
so they are the same complete world. Finally an actual $x>0$ has
$D>0$; none of the $D=0$ labels can enter this argument. ∎

**Lemma 17.5 (The exact degree-fifty factorization).** Form the exact
polynomial quotients in $K[x,t]$

$$
F_s=\frac{\ell^2 f(x,-(N_0+N_1t)/\ell,t)}{D^2(x-x_s)},\qquad
G_s=\frac{\ell^4\mathscr K(x,-(N_0+N_1t)/\ell,t)}{D^4(x-x_s)}.
$$

The arguments $t$ here include the substitutions $p_s(t),v_s(t)$ of
Definition 17.2. Each displayed division has zero remainder. Their
$(x,t)$ degrees are $(6,2),(13,4)$. Apply Lemma 17.3 in $t$, writing
$F_s=At^2+Bt+C$, and denote its linear remainder coefficients by
$\alpha_t,\beta_t$. Both have $x$-degree $31$. Let

$$
\begin{gathered}
P=\operatorname{Res}_t(F_s,G_s)
 =\frac{A\beta_t^2-B\alpha_t\beta_t+C\alpha_t^2}{A^3},\\
F_0(x,p_s(t),v_s(t))=F_{00}(x)+F_{01}(x)t,\\
W_2=\frac{F_{00}N_1-F_{01}N_0}{D(x-x_s)},\qquad
Q_{14}=\frac{P}{\ell^8W_2^2}.
\end{gathered}
$$

All three further divisions are exact polynomial divisions, not rational
equations restricted by $A\ne0$. They give

$$
\deg_x P=50,\qquad\deg_x W_2=2,\qquad\deg_x Q_{14}=14,\qquad
P=\ell^8W_2^2Q_{14},\qquad
\alpha_tN_0-\beta_tN_1\equiv0\pmod{W_2}.
$$

No monic, primitive, or nonzero scalar rescaling is made in these
definitions. Moreover

$$
\gcd(W_2,\ell)=\gcd(W_2,\alpha_t)=1,\qquad
\gcd(Q_{14},\alpha_t)=\gcd(Q_{14},\ell)
 =\gcd(Q_{14},Q_{14}')=1
$$

in $K[x]$ and at both strict embeddings.

**Proof.** Substitute the four linear sample forms of Definition 17.2,
multiply by the displayed powers of $\ell$, and divide in $K[x,t]$.
Reducing every field coefficient modulo $\Phi$ gives zero remainders
and the stated degrees. The quadratic–quartic expressions of Lemma 17.3
then give $P$ by exact division by $A^3$. In the same coefficient field,
division of $F_{00}N_1-F_{01}N_0$ by $D(x-x_s)$ gives $W_2$;
division of $P$ by $\ell^8W_2^2$ has zero remainder and degree fourteen.
Division of $\alpha_tN_0-\beta_tN_1$ by $W_2$ also has zero remainder.
These rational circuits and exact quotient rules specify every
characteristic-zero coefficient, including the scalar of $Q_{14}$.

For the coprimality assertions the complete descending arrays and fixed
Sylvester residues are

| Object | Prime and $\theta$ image | Array or residue |
| --- | --- | --- |
| $W_2$ | $113,77$ | $(33,32,112)$ |
| $\operatorname{Res}_x(W_2,\ell)$ | $113,77$ | $14$ |
| $\operatorname{Res}_x(W_2,\alpha_t)$ | $113,77$ | $95$ |
| $Q_{14}$ | $101,53$ | $(50,85,48,98,17,48,56,10,64,34,85,17,94,50,54)$ |
| $\operatorname{Res}_x(Q_{14},\alpha_t)$ | $101,53$ | $53$ |
| $\operatorname{Res}_x(Q_{14},\ell)$ | $101,53$ | $91$ |
| $\operatorname{Res}_x(Q_{14},Q_{14}')$ | $101,53$ | $17$ |
| $P(0),[x^{50}]P$ | $101,53$ | $97,62$ |
| $x_s,\ell(x_s),A_{5s}$ | $101,53$ | $69,93,13$ |

The $101$ specialization has $\Phi(53)=0$. All rational coefficient
denominators in each row are units at that row's prime; the $W_2$ and
$Q_{14}$ leading degrees survive. The localization argument of Lemma
17.4 therefore proves all five characteristic-zero gcd assertions.
The residues of $P$ also agree with Theorem 8.4's unscaled normalization.
These reductions certify nonvanishing, not finite-field worlds. ∎

**Lemma 17.6 (The degree-two factor has an actual exceptional consumer).**
An actual companion of a singular world at $p\ne24$ with
$x\ne x_s$ cannot give a distinct terminal-$M$ pair through $W_2(x)=0$.

**Proof.** Lemma 17.4 gives $D\ell\ne0$. At $x\ne x_s$, the
necessary equations give $F_s=G_s=0$. Lemma 17.3 gives
$\alpha_tt+\beta_t=0$ even when $A=0$. At a $W_2$ root, Lemma
17.5 gives $\alpha_t\ne0$, so $t=-\beta_t/\alpha_t$, and its last
congruence gives

$$
N_0+N_1t=(\alpha_tN_0-\beta_tN_1)/\alpha_t=0,\qquad d=0.
$$

For an actual world the clock-zero identity in Theorem 3.2 is

$$
2F_0=d\bigl(45x^3+89x^2-32x-40+UD\bigr).
$$

Thus $d=0$ implies $F_0=0$. The companion and the singular endpoint
are both in the actual exceptional union $E(p,v)$. Theorem 3.2 makes
$f_{MM}$ injective on that union, excluding their distinctness. This
uses the full original clock-zero equation of a world; it does not
assign a world to a root merely because it lies on $W_2$. ∎

**Lemma 17.7 (All roots of the residual factor at both strict embeddings).**
At each of $\theta_-,\theta_+$ the polynomial $Q_{14}$ has exactly
one negative real root, five positive real roots and four nonreal
conjugate pairs. The following rational prescription and inequalities
are a complete isolation certificate.

Bisect the corresponding sign-changing bracket $I_\pm$ exactly $1050$
times, always retaining the sign change of $\Phi$. Denote the resulting
closed interval by $I_\pm^{(1050)}$ and its exact rational midpoint by
$u_\pm$. For each reduced power-basis coefficient of $Q_{14}$ evaluate
at $u_\pm$, divide by the leading $x$ coefficient at that midpoint,
and round each normalized coefficient using

$$
\operatorname{Round}_{110}(a)=10^{-110}
 \left\lfloor10^{110}a+\tfrac12\right\rfloor.
$$

Call this rational monic polynomial $q_\pm^{\rm c}$. The rows below
are the fourteen exact Gaussian-rational seeds for each embedding;
all displayed decimals are terminating rational numbers, not root
definitions by approximation.

| Index | Seed at $\theta_-$: $(\Re,\Im)$ | Seed at $\theta_+$: $(\Re,\Im)$ |
| --- | --- | --- |
| $0$ | $(-.30194950,0)$ | $(-.32567481,0)$ |
| $1$ | $(.34673109,0)$ | $(.34403412,0)$ |
| $2$ | $(.62452039,0)$ | $(.61875101,0)$ |
| $3$ | $(3.6743264,0)$ | $(1.3718257,0)$ |
| $4$ | $(3.7043082,0)$ | $(1.7789920,0)$ |
| $5$ | $(37.031890,0)$ | $(3.6816386,0)$ |
| $6$ | $(.83008130,-.42683423)$ | $(.77443115,-.043518373)$ |
| $7$ | $(.83008130,.42683423)$ | $(.77443115,.043518373)$ |
| $8$ | $(1.0639158,-.10853218)$ | $(1.1245683,-.14944337)$ |
| $9$ | $(1.0639158,.10853218)$ | $(1.1245683,.14944337)$ |
| $10$ | $(1.2936296,-.27470908)$ | $(1.2179597,-.31713858)$ |
| $11$ | $(1.2936296,.27470908)$ | $(1.2179597,.31713858)$ |
| $12$ | $(1.3766565,-.35969277)$ | $(1.2660339,-.37047289)$ |
| $13$ | $(1.3766565,.35969277)$ | $(1.2660339,.37047289)$ |

Starting at each seed perform eight Newton recurrences for
$q_\pm^{\rm c}$, computing each recurrence over $\mathbb Q(i)$ and
then applying $\operatorname{Round}_{110}$ separately to its real and
imaginary components. Let $c_{\pm,i}$ be the resulting centres and
$\gamma_{\pm,i}=1/(q_\pm^{\rm c})'(c_{\pm,i})$ exactly. Put

$$
\rho=10^{-65},\qquad
\mathcal R_{\pm,i}
=\{z:|\Re(z-c_{\pm,i})|\le\rho,\quad
        |\Im(z-c_{\pm,i})|\le\rho\}.
$$

For the true embedded polynomial let
$q_\pm=Q_{14}/[x^{14}]Q_{14}$. Evaluate its reduced power-basis
coefficients on $I_\pm^{(1050)}$, normalize by the interval for the
true leading coefficient, and use descending-power Horner evaluation
in $\theta$ and $x$. Real interval arithmetic takes the outer minimum
and maximum of endpoint products and, for division, requires the divisor
interval to exclude zero. Complex arithmetic uses its real and imaginary
component intervals. Round each elementary interval endpoint outward to
a multiple of $10^{-400}$. The leading coefficient intervals exclude
zero. Every one of the twenty-eight rectangles satisfies the exact
rational inequalities

$$
\begin{aligned}
\sup_{z\in\mathcal R_{\pm,i}}
\bigl(|\Re(1-\gamma_{\pm,i}q_\pm'(z))|
     +|\Im(1-\gamma_{\pm,i}q_\pm'(z))|\bigr)&<10^{-50},\\
\max\bigl(|\Re(\gamma_{\pm,i}q_\pm(c_{\pm,i}))|,
          |\Im(\gamma_{\pm,i}q_\pm(c_{\pm,i}))|\bigr)&<10^{-100}.
\end{aligned}
$$

Uniform upper bounds, written as exact terminating rationals, are

| Embedding | Derivative row-sum bound | Centre displacement bound |
| --- | --- | --- |
| $\theta_-$ | $1.786\cdot10^{-57}$ | $8.547\cdot10^{-109}$ |
| $\theta_+$ | $7.665\cdot10^{-56}$ | $1.768\cdot10^{-106}$ |

The rectangles at each embedding are pairwise disjoint. Rectangles
$1,\ldots,5$ are strictly to the right of zero, rectangle $0$ is
strictly to its left, and rectangles $6,\ldots,13$ exclude the real
axis. The upper-embedding root in rectangle $3$ lies in the rational
interval

$$
I_*=(1.3718256939,1.3718256940),
$$

and no other upper-embedding root lies in that interval.

**Proof.** The coefficient divisions in Lemma 17.5 and the finite
rational rules just specified give the displayed bounds on every whole
rectangle. In particular none of the Newton-centre derivative inverses
is undefined. In the real-imaginary maximum norm the first bound is
the operator norm of the derivative of
$z\mapsto z-\gamma_{\pm,i}q_\pm(z)$. The second bounds its displacement
at the centre, and

$$
10^{-100}+10^{-50}\rho<\rho.
$$

Consequently this map contracts the complete closed rectangle strictly
into itself. Banach's contraction theorem, cited in Section 2, gives
one root in each rectangle and uniqueness there. Fourteen disjoint
rectangles exhaust a degree-fourteen polynomial, including complex roots
and multiplicities. The first six centres are real, so conjugation and
uniqueness make their roots real. The other eight rectangles exclude the
real axis. Their signs, disjointness, and the inclusion in $I_*$ follow
by the same rational endpoint comparisons. Thus the certificate does
not infer exhaustiveness from a real scan or a list of decimal roots. ∎

**Lemma 17.8 (All positive residual roots with strict source guards).**
For an actual distinct companion through $Q_{14}(x)=0$, the only
possible embedding and root are $\theta_+$ and the root $x_*$ in $I_*$.
At each positive root define necessarily

$$
\begin{gathered}
t=-\beta_t/\alpha_t,\qquad
p=p_s(t),\quad v=v_s(t),\quad m=m_s(t),\quad
d=-(N_0+N_1t)/\ell,\\
h_3=(24-d)/x,\quad h_4=18-d,\quad
h_5=(p-d)/(x+1),\quad h_6=(v-d)/(x+2),\\
H_0=20h_3-45h_4+36h_5-10h_6,\\
H_1=10h_3-20h_4+15h_5-4h_6,\qquad
H_2=4h_3-6h_4+4h_5-h_6,\\
B_0=294/5-2d-H_2,\quad C_0=d^2+B_0^2,\quad
U=(-dH_0+B_0H_2)/C_0,\\
b=(U-1)/2,\qquad j=U(24-d)/H_1,\qquad r=xU-j.
\end{gathered}
$$

On the real sections of all ten positive-root boxes
$\alpha_t,\ell,H_1$ exclude zero,
$|H_1|>1/10$ and $C_0>3/10$. With the coefficient and interval
rules of Lemma 17.7 the complete open rational guard enclosures are

| Embedding and root index | Enclosure of $r$ | Enclosure of $b$ | Necessary strict-source outcome |
| --- | --- | --- | --- |
| $-,1$ | $(2.0910,2.0911)$ | $(1.0965,1.0967)$ | $r>1$ |
| $-,2$ | $(-7.7081,-7.7078)$ | $(-13.513,-13.512)$ | $r<0,b<0$ |
| $-,3$ | $(1.1476,1.1479)$ | $(-.0856,-.0853)$ | $r>1,b<0$ |
| $-,4$ | $(-.2526,-.2523)$ | $(-.0945,-.0942)$ | $r<0,b<0$ |
| $-,5$ | $(1.2828,1.2831)$ | $(-.4791,-.4788)$ | $r>1,b<0$ |
| $+,1$ | $(2.8020,2.8024)$ | $(1.6912,1.6916)$ | $r>1$ |
| $+,2$ | $(21.835,21.836)$ | $(53.583,53.584)$ | $r>1$ |
| $+,3$ | $(.8985,.8986)$ | $(.1301,.1303)$ | Only possible strict companion |
| $+,4$ | $(-.0260,-.0258)$ | $(-.0152,-.0149)$ | $r<0,b<0$ |
| $+,5$ | $(1.1603,1.1606)$ | $(-.2982,-.2978)$ | $r>1,b<0$ |

**Proof.** Lemma 17.5 makes $\alpha_t$ and $\ell$ nonzero at every
$Q_{14}$ root. At a common $F_s,G_s$ root their polynomial linear
remainder fixes $t$, and $h=0$ fixes $d$, giving the displayed formulas
without any assumption on the leading coefficient $A$. Interpolation
and the robust formula of F, Lemma 30.2, fix $U,j,r,b$ for every actual
world. Evaluation on the real sections of the ten rectangles gives the
listed intervals and nonzero reconstruction denominators. The nine rejected rows contradict
$b>0$ or $0<r<1$. The negative and nonreal roots of Lemma 17.7 cannot
be actual $x>0$. The retained row is only a necessary candidate;
neither $Q_{14}=0$ nor the two inequalities alone assert a complete
world or its terminal equality. ∎

**Lemma 17.9 (Exact identification with the supplied actual pair).**
The actual singular/ordinary pair $\{S_1,O_1\}$ in Theorem 8.2 has
singular embedding $\theta_+$ and companion coordinate $x=x_*$.

**Proof.** Let $(c_\theta,c_r,c_b)$ be exactly the three rational
centre coordinates with denominator $10^{85}$ in Theorem 8.2, and let
$\mathcal Z_8$ be their closed box of component radius $10^{-75}$.
Evaluation on that entire rational box gives

$$
\theta(\mathcal Z_8)\subset I_+,\qquad
\frac{b+r(1-r)/b+r}{1+2b}(\mathcal Z_8)
 \subset(1.3718256939,1.3718256940)=I_*.
$$

Here $b$ and $1+2b$ exclude zero throughout the box. These inclusions
are rational interval inclusions for the displayed source expression,
using outward endpoint rounding to $10^{-400}$ as in Lemma 17.7.
The supplied pair is actual and distinct, so Lemma 17.4 excludes the
pole and the self case. Lemma 17.6 excludes $W_2$; Lemma 17.5 then
places its $x$ on $Q_{14}$. Lemma 17.7's root isolation identifies
it with $x_*$. Existence, every original-clock equality, the whole
nonzero gains, strict source guards and within-pair distinctness here
come from Theorem 8.2's actual construction, not from a converse to a
projected-root test. ∎

## 18. The unique actual singular-$M$ base and its same-child consumer

**Theorem 18.1 (All off-$24$ terminal-$M$ pairs with a singular endpoint).**
Use $\theta=\theta_+$, let $x_*$ be the unique $Q_{14}$ root in $I_*$,
and define the exact algebraic quantities

$$
t_*=-\frac{\beta_t(x_*)}{\alpha_t(x_*)},\qquad
q_*=(p_*,v_*)=
\bigl(24+A_{5s}t_*,\ 24+K_{6s}+A_{6s}t_*\bigr).
$$

Then $q_*$ is precisely Theorem 8.2's base $(p^*,v^*)$ and
$t_*\ne0$. For every real $p\ne24,v$ and every distinct pair of
complete worlds $W,W'\in C(p,v)$,

$$
\bigl[f_{MM}(W)=f_{MM}(W')\ \text{and}\
       \Lambda(W)\Lambda(W')=0\bigr]
\quad\Longleftrightarrow\quad
\bigl[(p,v)=q_*\ \text{and}\ \{W,W'\}=\{S_1,O_1\}\bigr],
$$

where $S_1,O_1$ are the exact whole worlds of Theorem 8.2.
In particular

$$
\mathcal B_{\mathcal S,M}=\{q_*\}.
$$

This equality concerns the actual guarded set, with no assertion that
the unfiltered outer projection of Theorem 8.4 is a singleton.

**Proof.** Choose a singular endpoint of any pair on the left. O,
Theorem 29.2, and Definition 17.1 put it on exactly one of the two
strict singular lines, at $t=(p-24)/A_{5s}\ne0$. Any actual companion
of any source type has finite real $x>0,d$ satisfying the unscaled
equations of Definition 17.2. Lemma 17.4 excludes $\ell=0$ and
$x=x_s$ for a distinct pair. At every other actual label
$D\ell(x-x_s)\ne0$, so $F_s=G_s=0$. Their fixed resultant vanishes,
and the exact factorization in Lemma 17.5 leaves $W_2=0$ or
$Q_{14}=0$. Lemma 17.6 excludes the former. Lemmas 17.7–17.8 exhaust
both strict embeddings and all roots of the latter, leaving exactly
$\theta_+,x_*$. Their unit certificates make $t=t_*$ and
$d=-(N_0+N_1t_*)/\ell$ unique, and hence fix the acquired base $q_*$.

Lemma 17.9 identifies Theorem 8.2's actual distinct pair with that
same root and embedding. The uniquely fixed $t$ identifies its singular
world by O's singular-line converse; the uniquely fixed companion
$(x,d)$ identifies its whole world by F, Lemma 30.2. Thus the original
pair is exactly $\{S_1,O_1\}$ and its base is Theorem 8.2's base.
That base is off $24$, so $t_*\ne0$. Conversely the supplied pair
satisfies all the equations and guards and has equal terminal-$M$
responses, proving the reverse implication and actual nonemptiness.

No gain coefficient, drift, or sampled value has been cancelled.
Candidate-dependent denominators have each been handled:
$D>0$ on actual worlds, $\ell=0$ by Lemma 17.4, $x=x_s$ by the self
case, $\alpha_t\ne0$ on both residual factors by Lemma 17.5, and
$H_1,C_0\ne0$ on every positive residual box by Lemma 17.8.
This proves the statement over all real off-$24$ bases, rather than a
bounded strip or a generic set of bases. ∎

**Corollary 18.2 (Entire-child exclusion of the chosen-$M$ singular sector).**
There are no real $p\ne24,v$ and four complete labels
$W_0,W_1,W_2,W_3\in C(p,v)$ satisfying

$$
\begin{gathered}
W_0\ne W_1,\qquad f_{MJ}(W_0)=f_{MJ}(W_1),\\
W_2\ne W_3,\qquad f_{MM}(W_2)=f_{MM}(W_3),\qquad
\Lambda(W_2)\Lambda(W_3)=0.
\end{gathered}
$$

Cross-pair overlaps or disjointness are unrestricted, and the two
terminal common values are not required to agree.

**Proof.** Theorem 18.1 forces $(p,v)=q_*$ and
$\{W_2,W_3\}=\{S_1,O_1\}$. Theorem 8.2 makes $f_{MJ}$ injective
on the entire $C(q_*)$, which has exactly its three supplied worlds.
It therefore excludes any distinct $J$ pair in that child, not only
the selected $M$ pair. This contradicts $W_0\ne W_1$ and their
terminal-$J$ equality, whether the two pairs share labels or are
disjoint. ∎

**Definition 18.3 (The residual original relation and ancestor conditions).**
Let $Y=\{(p,v)\in\mathbb R^2:p\ne24\}$ as in Section 16. Restrict
only the chosen-$M$ pair relation by

$$
\mathcal P_M^{\rm ns}
=\{(q,W_2,W_3)\in\mathcal P_M:
       \Lambda(W_2)\ne0,\ \Lambda(W_3)\ne0\}.
$$

Corollary 18.2 gives the exact equality of original joint relations

$$
\mathcal P_J\times_Y\mathcal P_M
=\mathcal P_J\times_Y\mathcal P_M^{\rm ns}.
$$

By Theorem 3.2 at least one chosen-$M$ endpoint in this residual
relation lies outside $E(q)$. The other may still be a nonsingular
$F_0=0$ world, including a zero-drift world. No restriction is placed
on singular worlds in the $J$ pair or elsewhere in the entire child.
Determining whether this residual relation has an actual point over
all $Y$, or proving it empty, is still the original same-child
alternative in Definition 1.2, with all original strict guards.

A positive sixth-$M$ joint child would additionally require the
sixth-$J$ joint child at that same fifth response $p$, the fifth-$J$
and common-parent conditions, and all eight-slot and ancestor conditions
of O, Theorem 17.1, for the corresponding fifth-$M$ $L_2$, $H_4$
$L_3$, root $L_7$ or eight-versus-nine conclusion. None of those
additional conditions is supplied by the chosen-$M$ singular-sector
classification.

**Assumption 18.4 (Supplier correspondence and mathematical attribution).**
Sections 17–18 use the following exact mathematical premises and
source-specific deductions.

| Premise | Precise use |
| --- | --- |
| O, Theorems 2.1–2.2, 4.2 and 29.2 | Complete zero-safe original parent, exactly two strict singular sources, nonzero $A_{5s}$, and their unique whole-world lift for each fifth response. |
| F, Lemma 30.2 and Definition 31.1 | Injective whole-world reconstruction and the two necessary cleared equations, with $\mathscr K=4k$. Cleared roots alone are not legal worlds. |
| This volume, Theorem 3.2 | Irreducible coefficient field and terminal-$M$ injectivity on the actual exceptional union; this supplies the consumer excluding $W_2$. |
| This volume, Definition 8.1 and Theorems 8.2, 8.4 | The unchanged affine clock-response lines, the already supplied actual pair and entire-child $J$ injectivity, and the unscaled degree-fifty elimination framework. |
| Moreno Maza, Definition 4 and Propositions 5–7, cited in Lemma 17.3 | Classical Sylvester determinant and coprimality method over the indicated coefficient field and finite localizations. |
| Banach, pp. 133–181, cited in Section 2 | Classical contraction on the specified complete rational rectangles, used internally for the strict-real isolation certificate. |
| Lemmas 17.4–17.9 and Theorem 18.1 | The pole exclusion, exact $\ell^8W_2^2Q_{14}$ factorization, actual exceptional consumer, both-embedding root and guard exhaustion, and exact identification of the unique actual singular-endpoint pair. |

The source-specific classification extends the finite actual-set
statement of Theorem 8.4; the actual supplier in Theorem 8.2 and its
whole-child separation are reused as premises. Resultants and
contraction are classical internal methods. This attribution is confined
to these named sources and this classification; it makes no claim of
worldwide novelty or a global literature classification. The existing
$p=24$ joint child, exact-$p_J$ exclusions, standalone off-$24$ $M$
pair, finite-world bound, false lifts, nonclosed collision image and
boundary results retain their own quantified scopes. All auxiliary
coordinates remain mathematical descriptions, with only Definition
1.1's original actions and acquired reads available.

## 追加锚（本行以下为增补区）
