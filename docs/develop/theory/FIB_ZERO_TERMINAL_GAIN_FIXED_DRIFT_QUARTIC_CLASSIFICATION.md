# Zero terminal gain at fixed drift: an exact guarded quartic classification

## 1. Domain and the restricted route

Use the original-world and literal-clock definitions in [FIB literal clock cubic matrix polynomial frame](FIB_LITERAL_CLOCK_CUBIC_MATRIX_POLYNOMIAL_FRAME.md), Definitions 1.1 and 6.3. Thus

$$
P=P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},\qquad
0<r<1,\quad b>0,\quad d\in\mathbb R,\quad
0\ne g\in\mathbb R[t],\quad\deg g\le3.
$$

The acquired word is $J,M,J,M,M,M$, with readings
$(0,24,147/5,24,18,p,v)$. Put $C(p,v)$ for the entire original child of Definition 6.3. After the full six-atom history, append $J$ or $M$ at clock $7$; the resulting responses are

$$
a(W)=d+g(7)\operatorname{tr}(JQ_6P),\qquad
m(W)=d+g(7)\operatorname{tr}(MQ_6P).
$$

The original independent-pair problem is the existence of $p\ne24$, $v$, and independently chosen distinct pairs in $C(p,v)$ with equal $a$-values and equal $m$-values. The results below classify the restricted route in which two worlds have one common drift and satisfy $g(7)=0$. This restriction is an additional condition for the route and is not imposed on the original problem.

The seven acquired traces are

$$
(1,j,T,n,u,u+n,2u+n),\qquad
j=b+\frac{r(1-r)}b,\quad n=j+r,\quad T=1+b,\quad u=1+2b.
$$

These are the literal products in the cited clock volume.

## 2. Polynomial coordinates

For $d\in\mathbb R\setminus\{0,24\}$ and $u\in\mathbb R$, define

$$
\begin{aligned}
 C&=24-d,&K&=4200u(u+1),\\
 A&=-225du^2+(33894-1310d)u+175d-3150,\\
 B&=75du^2+(46494-1710d)u+9450-525d,\\
 Z&=-225du^2-(14490+750d)u+47250-2625d,\\
 Y&=-600du^2+(240d-72576)u+75600-4200d,\\
 L&=12AB,&N&=CK(3A-2B).
\end{aligned}
\tag{2.1}
$$

Define

$$
\begin{aligned}
 R_d(u)&=4N^2-4NL+4(u-1)CKBL-(u-1)^2L^2,\\
 E_{d,p}(u)&=2100(p-d)(u+1)B-Z\{B+1050C(u+1)\},\\
 F_{d,v}(u)&=4200(v-d)(u+1)B-Y\{2B+1050C(u+1)\}.
\end{aligned}
\tag{2.2}
$$

For every $p,v\in\mathbb R$, put

$$
S(d,p,v)=\left\{u\in\mathbb R:\begin{array}{l}
u>1,\quad AB\ne0,\quad 0<N/L<1,\\
R_d(u)=E_{d,p}(u)=F_{d,v}(u)=0
\end{array}\right\}.
\tag{2.3}
$$

The inequalities in (2.3) are part of the definition; an unguarded root is not a world.

## 3. Classification theorem

**Theorem 3.1.** For all $p,v\in\mathbb R$ and all $d\in\mathbb R\setminus\{0,24\}$, there is a bijection

$$
S(d,p,v)\longleftrightarrow
\{W\in C(p,v):d(W)=d,\ g_W(7)=0\}.
\tag{3.1}
$$

The inverse map sends $u\in S(d,p,v)$ to

$$
\begin{gathered}
b=\frac{u-1}{2},\qquad j=\frac{CK}{6A},\qquad n=\frac{CK}{4B},\qquad r=\frac NL,\\
e_0=-\frac d7,\qquad e_2=\frac{294-10d}{25(u+1)},\qquad e_4=\frac{18-d}{3u},\\
h(t)=e_0\frac{(t-2)(t-4)}8-e_2\frac{t(t-4)}4+e_4\frac{t(t-2)}8,\\
g(t)=(7-t)h(t).
\end{gathered}
\tag{3.2}
$$

For each fixed $d\in\mathbb R\setminus\{0,24\}$, the first five acquired rows together with $g(7)=0$ have at most ten complete worlds. For each fixed $p,v\in\mathbb R$ and $d\in\mathbb R\setminus\{0,24\}$, the set in (3.1) has at most four complete worlds.

The classification and bounds of Theorem 3.1 are model-specific ordinary derivations in this repository (`repo-derived`), with no claim of literature priority.

**Proof.** Let $c=r(1-r)/b$, so $j=b+c$, $n=j+r$, $u=1+2b$, and $T=(u+1)/2$. If $g(7)=0$, the classical factor theorem gives a unique $h\in\mathbb R[t]$ of degree at most two with $g(t)=(7-t)h(t)$. The rows at clocks $0,2,4$ give

$$
h(0)=e_0=-d/7,\qquad h(2)=e_2=\frac{294-10d}{25(u+1)},\qquad
h(4)=e_4=\frac{18-d}{3u}.
$$

The three distinct nodes determine $h$, and the Lagrange formula is (3.2). Here classical finite fixed-node Lagrange interpolation is an intermediate input: Berrut–Trefethen, *[Barycentric Lagrange Interpolation](https://doi.org/10.1137/S0036144502417715)*, §2, as cited in Section 11 of the [common-parent volume](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md#11-mathematical-scope-and-predecessor-correspondence). Its values at the four odd or later clocks are

$$
\begin{aligned}
h(1)&=3e_0/8+3e_2/4-e_4/8=A/K,\\
h(3)&=-e_0/8+3e_2/4+3e_4/8=B/K,\\
h(5)&=3e_0/8-5e_2/4+15e_4/8=Z/K,\\
h(6)&=e_0-3e_2+3e_4=Y/K.
\end{aligned}
\tag{3.3}
$$

Multiplying each expression in (3.3) by $4200u(u+1)$ gives exactly the four displayed coefficients $A,B,Z,Y$ in (2.1).

Because $d\ne24$, the readings at clocks one and three force $h(1)\ne0$ and $h(3)\ne0$; hence $AB\ne0$. The same two rows give

$$
j=\frac{24-d}{6h(1)}=\frac{CK}{6A},\qquad
n=\frac{24-d}{4h(3)}=\frac{CK}{4B},\qquad
r=n-j=\frac{CK(3A-2B)}{12AB}=\frac NL.
\tag{3.4}
$$

The strict rank-one source identity is $r(1-r)=b(j-b)$. Substitution of (3.4) and $b=(u-1)/2$, followed by multiplication by $4L^2\ne0$, is equivalent to $R_d(u)=0$. Thus every world gives an element of $S(d,p,v)$ once its final two acquired rows are included.

For the clock-five row, $g(5)=2h(5)$ and $u+n=(4uB+CK)/(4B)$, so

$$
p-d=2h(5)(u+n)
=\frac{Z\{B+1050C(u+1)\}}{2100(u+1)B},
$$

which is equivalent to $E_{d,p}(u)=0$. For clock six, $g(6)=h(6)$ and $2u+n=(8uB+CK)/(4B)$, so

$$
v-d=h(6)(2u+n)
=\frac{Y\{2B+1050C(u+1)\}}{4200(u+1)B},
$$

which is equivalent to $F_{d,v}(u)=0$. This proves the forward map and verifies all seven original rows.

Conversely, let $u\in S(d,p,v)$. Then $b>0$ and $0<r<1$. Since $L\ne0$, the equality $R_d(u)=0$ reverses the preceding rank calculation and gives $r(1-r)=b(j-b)$. Hence $j=b+r(1-r)/b$, and $n=j+r$. Formula (3.2) supplies a polynomial of degree at most three with $g(7)=0$. The interpolation values give rows $0,2,4$; (3.4) gives rows $1,3$; and the two displayed quotient identities give rows $5,6$. Thus the constructed triple lies in $C(p,v)$. Its gain is not identically zero because the first two readings are different. The construction is unique because $u$ determines $b,h,j,n,r,g,d$, while every world determines $u=1+2b$. Therefore the correspondence is bijective.

For the bounds, when $d\ne0$, $A$ and $B$ have degree two with leading coefficients $-225d$ and $75d$. Therefore $L$ has degree four and leading coefficient $-202500d^2$. The last term of $R_d$ has degree ten and leading coefficient
$-(-202500d^2)^2=-41006250000d^4\ne0$, while the other terms have degree at most nine. Thus $R_d$ has at most ten real roots by classical polynomial root counting, and the first bound follows. The first term of $E_{d,p}$ has degree at most three; the product $ZB$ in the second term has leading coefficient $-16875d^2$, so $E_{d,p}$ has degree four with leading coefficient $16875d^2\ne0$. Every element of $S(d,p,v)$ is a root of $E_{d,p}$, proving the bound four by the same classical polynomial root count. ∎

## 4. The zero-drift layer

**Theorem 4.1.** No original world realizing the first five readings $(0,24,147/5,24,18)$ has both $d=0$ and $g(7)=0$.

The exclusion in Theorem 4.1 is a model-specific ordinary derivation in this repository (`repo-derived`), with no claim of literature priority.

**Proof.** The preceding factorization and interpolation remain valid at $d=0$. These are the same intermediate applications of the classical factor theorem and finite fixed-node Lagrange interpolation (Berrut–Trefethen, §2, cited above). For $u=1+2b>1$, (3.4) becomes

$$
j=\frac{400u(u+1)}{3(269u-25)},\qquad
n=\frac{200u(u+1)}{3(123u+25)},\qquad
r=\frac{200u(u+1)(23u-75)}{3(123u+25)(269u-25)}.
\tag{4.1}
$$

The denominators are positive. If $r>0$, then $u>75/23$. On that range,
$123u+25<131u$ and $269u-25<269u$, so

$$
r>\frac{200(23u-75)}{105717}.
\tag{4.2}
$$

For $u\ge27$, the right side is at least $109200/105717>1$, contradicting $r<1$. Hence $75/23<u<27$. The lower off-diagonal entry $c=j-b$ is

$$
c=\frac{-7u^2+1682u-75}{6(269u-25)}.
$$

Since $u<27$, its numerator is greater than $1493u-75$; since $u>75/23$, that is greater than $1470u$. The positive denominator is less than $1614u$, so $c>245/269$. Also $b=(u-1)/2>26/23$. Thus

$$
bc>\frac{6370}{6187}>1,
$$

whereas the source identity gives $bc=r(1-r)\le1/4$. This contradiction proves the claim. ∎

## 5. The nonzero exceptional drift

At the target parent, the fixed-drift exclusion at $d=24$ is the direct consequence of Theorem 2.2 in [FIB common-parent geometry and two exact mixed children](FIB_COMMON_PARENT_GEOMETRY_AND_MIXED_CHILDREN.md). That theorem gives $b=1/8$ and

$$
g(t)=\frac85(t-1)(t-3)(t-5).
$$

Consequently $g(7)=384/5\ne0$. Thus the fixed-drift, zero-terminal-gain class is empty at $d=24$. This cited exclusion is used as stated; no additional companion condition is introduced.

Combining this exclusion with Theorem 4.1 and Theorem 3.1 yields the complete fixed-drift classification for the route: the class is empty at $d=0$ and $d=24$, and is given by (3.1) for every $d\in\mathbb R\setminus\{0,24\}$ and every $p,v\in\mathbb R$.

## 6. Guards and the original problem

The guards in (2.3) have exact source meaning. $u>1$ is precisely $b>0$, and $0<N/L<1$ is precisely $0<r<1$. For $d\ne24$, the two nonzero odd readings force $A\ne0$ and $B\ne0$, so $AB\ne0$ removes no legal world. No leading coefficient of the gain, sampled gain value other than the explicitly fixed $g(7)=0$, root difference, direction coordinate, singularity coordinate, or companion denominator is divided out. Lower gain degrees, repeated roots, arbitrary signs, zero drift before the separate exclusion, and singular companions remain whenever the original source conditions hold. The only added condition is $g(7)=0$, together with the common-drift route used in the classification.

**Corollary 6.1.** The restricted route succeeds exactly when

$$
\exists p,v\in\mathbb R:\quad p\ne24\ \land\ \exists d\in\mathbb R\setminus\{0,24\}\ \exists u_0,u_1\in S(d,p,v):
\quad u_0\ne u_1.
$$

The criterion follows from Theorem 3.1 and the empty drift layers, with $p\ne24$ inherited from the original target. The two reconstructed worlds are distinct because their $b$-coordinates differ. Their terminal $J$ and $M$ responses both equal the common drift $d$, so the same pair can serve both terminal actions in this restricted route. Theorem 3.1 remains the universal classification for every $p,v\in\mathbb R$; only this route criterion carries the $p\ne24$ restriction.

The original independent-pair problem remains the following mathematical problem, with its full child and all original guards unchanged:

**Problem 6.2.** Determine whether there exist $p,v\in\mathbb R$ with $p\ne24$ and worlds
$W_0,W_1,W_2,W_3\in C(p,v)$ such that

$$
W_0\ne W_1,\quad W_2\ne W_3,
$$

and

$$
a(W_0)=a(W_1),\qquad m(W_2)=m(W_3).
$$

No equality between the two common terminal values is required, and the pairs may overlap. The classification above neither proves nor disproves this unrestricted problem.

## 追加锚（本行以下为增补区）
