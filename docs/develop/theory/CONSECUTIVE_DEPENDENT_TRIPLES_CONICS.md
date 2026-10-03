# Consecutive Dependent Triples: Rational Conic Exclusion

## 1. Consecutive multiplicative dependence

Ingrid Vukusic and Volker Ziegler ask whether there are infinitely many
pairwise distinct integers greater than one whose triples, before and after
adding one to each coordinate, are multiplicatively dependent of maximal rank
([arXiv:2103.08542v1](https://arxiv.org/pdf/2103.08542), Definition 1 and
Section 5, Question 4). The conic exclusion below concerns the resultant
reduction of Igor E. Shparlinski and Nicolas Sleiman
([arXiv:2609.29408v1](https://arxiv.org/html/2609.29408v1), Sections 3.1--3.4).

## 2. Definitions and normalization

**Definition 2.1 (maximal-rank positive lift).** A positive lift is a triple of
integers $a,b,c>1$ with $a,b,c$ pairwise distinct such that both
$(a,b,c)$ and $(a+1,b+1,c+1)$ are multiplicatively dependent and every
two-element subtuple of each triple is multiplicatively independent.

For a maximal-rank dependent triple, choose a primitive relation

$$
a^{r}b^{s}c^{t}=1,
\qquad (r,s,t)\in\mathbb Z^3\setminus\{(0,0,0)\},
\qquad \gcd(|r|,|s|,|t|)=1.
$$

Pairwise independence makes all three exponents nonzero. Exactly one exponent
has sign different from the other two. Permute the three coordinates so that
the exceptional exponent of the unshifted relation is the $c$ exponent, then
change the sign of the relation. This gives

$$
c^{n_1}=a^{k_1}b^{m_1},
\qquad k_1,m_1,n_1>0,
\qquad \gcd(k_1,m_1,n_1)=1.
$$

For the shifted relation, if its exceptional coordinate is also $c$, the same
permutation and sign convention give the $F$ branch. If its exceptional
coordinate is $a$ or $b$, interchange $a$ and $b$ if necessary; this gives the
$G$ branch. Thus the finite coverage is: three choices for the exceptional
coordinate of the first relation, a sign reversal, one possible $a,b$ swap,
and the two second-relation branches below. No other sign pattern is used.

**Definition 2.2 (the two resultant branches).** Put $X=a$, $Y=b$, and use
$Z$ for the first relation variable. For positive integers $k_i,m_i,n_i$,
define

$$
P=Z^{n_1}-X^{k_1}Y^{m_1},
$$

and define the two second-relation polynomials

$$
Q=(Z+1)^{n_2}-(X+1)^{k_2}(Y+1)^{m_2},
$$

$$
R=(Z+1)^{n_2}(Y+1)^{m_2}-(X+1)^{k_2}.
$$

Write $F_{\boldsymbol e}=\operatorname{Res}_Z(P,Q)$ and
$G_{\boldsymbol e}=\operatorname{Res}_Z(P,R)$, where
$\boldsymbol e=(k_1,m_1,n_1,k_2,m_2,n_2)$.

## 3. Main theorem: positive-lift conic exclusion

**Theorem 3.1 (positive-lift exclusion for rational quadratic factors).** Let
$q\in\mathbb Q[X,Y]$ be absolutely irreducible of total degree two. Suppose
$q$ divides $F_{\boldsymbol e}$ or $G_{\boldsymbol e}$ for primitive positive
exponent triples as in Definition 2.2. Then no point $(a,b)$ on $q$ can be the
first two coordinates of a positive lift with a common positive integer root
$c$, pairwise distinct coordinates, and pairwise multiplicative independence
in both the unshifted and shifted triples.

The conclusion is only a positive-lift exclusion. It does not say that every
such $q$ is absent from the resultant.

**Proof.** Write

$$
q=A X^2+BXY+C Y^2+D X+E Y+F_0.
$$

The boundary calculation in Section 4 leaves only the rational family
$q_e$ and the two indefinite conics recorded in Section 7. All other entries
are excluded directly at positive integer coordinates. The family and the
two exceptional conics are treated uniformly over their rational function
fields in Sections 5--7. Those arguments use only primitive divisibility,
nonzero poles, separability in characteristic zero, and exact local orders.
They show that a positive lift cannot occur on any survivor. This proves the
theorem. $\square$

## 4. Boundary classification and exact finite enumeration

**Lemma 4.1 (boundary polynomial alternatives).** If a rational quadratic
factor has a zero edge polynomial, the corresponding coordinate line divides
the conic and is impossible for an absolutely irreducible conic. Otherwise,
root specialization at $X=0$, $Y=0$, $X=-1$, and $Y=-1$ restricts the monic
edge polynomials to the following complete lists. Constants and repeated roots
are included.

$$
\begin{aligned}
S&=[1,T,T+2,T^2,(T+2)^2,T(T+2),T^2+3T+3,\\
&\qquad T^2+2T+2,T^2+T+1],\\
U&=[1,T-1,T+1,(T-1)^2,(T+1)^2,T^2-1,\\
&\qquad T^2+T+1,T^2+1,T^2-T+1],\\
V&=[1,T+1,(T+1)^2].
\end{aligned}
$$

Here $S$ is the shifted-root list, $U$ is the unshifted cyclotomic list,
and $V$ is the final $G$-branch edge list. The complete monic quadratic
coefficient pairs are

$$
S_2=[(0,0),(4,4),(2,0),(3,3),(2,2),(1,1)]
$$

and

$$
U_2=[(-2,1),(2,1),(0,-1),(1,1),(0,1),(-1,1)].
$$

**Proof.** At $X=0$ or $Y=0$, the first equation forces $Z=0$, and the
remaining shifted coordinate is a root of unity. At $X=-1$, the $Q$ branch
forces $Z=-1$ and the remaining coordinate is a root of unity; the $R$
branch has the same alternatives together with its displayed exceptional
root $-1$. The $Y=-1$ calculation is the coordinate-permuted version for
$F$. For $G$, substitution $Y=-1$ gives

$$
R(X,-1)=-(X+1)^{k_2},
$$

so the only zero is $X=-1$, including the degree-drop specialization. The
rational cyclotomic polynomials of degree at most two, after the indicated
shift, are exactly $S$, $U$, and $V$. $\square$

**Lemma 4.2 (linear-system enumeration).** After projective scaling, the
non-family conics obtained from the edge alternatives are exactly the 67
isolated $F$ candidates and the 28 isolated $G$ candidates before the
determinant filter. After removing determinant-zero conics, there are 50
isolated $F$ conics and 21 isolated $G$ conics. The $G$ list is the following
21 indices from the zero-based $F$ list:

$$
[0,2,3,4,5,6,7,8,11,12,13,14,17,18,20,22,23,25,28,29,32].
$$

In addition, both branches contain the unbounded family

$$
q_e=XY+(1-e)X+eY,
\qquad e\in\mathbb Q\setminus\{0,1\}.
$$

The determinant of $q_e$ is $2e(1-e)$ in the normalized conic matrix.

**Proof.** Solve the edge coefficient systems. For $AC\ne0$, scale $C=1$. Choose
$(E,F_0),(d,f)\in S_2$ and $(u,v),(w,h)\in U_2$, with $(w,h)=(2,1)$
for $G$, and solve

$$
A=\frac{1-E+F_0}{h},\quad B=E-u,\quad D=Ad,
$$

subject to

$$
F_0=Af,\quad A-D+F_0=v,\quad D-B=Aw.
$$

For $C=0$, $A\ne0$, scale $A=1$, choose $(D,F_0)\in S_2$ and the
corresponding $(w,h)\in U_2$ (restricted to $(2,1)$ for $G$), set

$$
B=D-w,\qquad E=F_0-h,
$$

and test the two remaining $Y$-edges against the constant and linear members
of $S$ and $U$. The $A=0$, $C\ne0$ case is the $F$-branch exchange of
$X,Y$. For $G$, the final edge is tested against $V$.

For $A=C=0$, scale $B=1$ and write

$$
q=XY+dX+eY+f.
$$

The edge equations are linear alternatives. They require $f/e\in\{0,2\}$
when $e\ne0$, the corresponding nonzero-constant condition when $e=0$,
and the analogous condition for $d$. The two shifted edge equations require

$$
\frac{f-d}{e-1}\in\{-1,1\},
\qquad
\frac{f-e}{d-1}\in\{-1,1\}
$$

for $F$, with the last set reduced to $\{1\}$ for $G$, with the stated
nonzero-denominator alternatives when a denominator vanishes. Solving these
linear alternatives gives the isolated entries and $q_e$. No bounded choice
of $e$, $k_i$, $m_i$, or $n_i$ is made. Finally remove the determinant-zero
cases. In characteristic zero, a nonzero determinant is exactly absolute
irreducibility for a plane conic. $\square$

**Table 4.3 (classification and positive-coordinate reduction).**

| branch | isolated before determinant filter | isolated after filter | nonnegative-coefficient entries | arithmetic entries | survivors before function-field proof | family |
| --- | ---: | ---: | ---: | ---: | ---: | --- |
| $F$ | 67 | 50 | 35 | 13 | indices 22 and 37 | $q_e$ |
| $G$ | 28 | 21 | 10 | 10 | index 22 | $q_e$ |

The 35 $F$ and 10 $G$ nonnegative-coefficient entries cannot vanish at a
positive point. The remaining arithmetic exclusions are as follows.

| indices or type | exact equation at a positive point | reason for exclusion |
| --- | --- | --- |
| $F$ indices 0, 1, 26, 28 | $X+1=(Y+1)^2$, $X=Y^2$, $Y=X^2$, or $Y+1=(X+1)^2$ | a pair is multiplicatively dependent |
| $F$ indices 4, 5, 24, 25 | $X=Y+1+1/Y$, $X=Y-1+1/(Y+1)$, or the exchanged formulas | the displayed rational value is nonintegral for $X,Y>1$ |
| $F$ indices 18, 23 | $X=Y^2/(2Y+1)$ or $Y=X^2/(2X+1)$ | $\gcd(T^2,2T+1)=1$ |
| $F$ indices 6, 7 | $X(Y-1)=2$ or $Y(X-1)=2$ | the only point with both coordinates greater than 1 is $(2,2)$ |
| $F$ index 8 | $XY=1$ | impossible for $X,Y>1$ |
| $F$ indices 22, 37 | indefinite conics | treated in Section 7 |
| $G$ entries not in the 21-index list | no $G$ edge compatibility | excluded by the boundary system |
| $G$ index 22 | $X^2-2XY-Y^2-2Y=0$ | treated in Section 7 |

The normalized 50 $F$ coefficient vectors, in the order
$(A,B,C,D,E,F_0)$, are:

```text
(0,0,-1,1,-2,0); (0,0,-1,1,0,0); (0,0,1,1,0,0); (0,0,1,1,2,2);
(0,1,-1,0,-1,-1); (0,1,-1,1,0,0); (0,1,0,-1,0,-2); (0,1,0,0,-1,-2);
(0,1,0,0,0,-1); (0,1,0,0,0,1); (0,1,0,0,1,2); (0,1,0,1,0,2);
(0,1,0,1,1,0); (0,1,0,1,1,2); (0,1,0,1,2,0); (0,1,0,2,1,0);
(0,1,1,0,1,1); (0,1,1,1,2,2); (0,2,-1,1,0,0); (0,2,0,1,1,2);
(0,2,1,1,2,0); (0,2,1,1,2,2); (1,-2,-1,0,-2,0); (1,-2,0,0,-1,0);
(1,-1,0,0,-1,0); (1,-1,0,1,0,1); (1,0,0,0,-1,0); (1,0,0,0,1,0);
(1,0,0,2,-1,0); (1,0,0,2,1,2); (1,0,1,0,2,0); (1,0,1,1,1,1);
(1,0,1,2,0,0); (1,1,0,1,0,1); (1,1,0,2,1,2); (1,1,1,1,1,1);
(1,1,1,2,2,2); (1,2,-1,2,0,0); (1,2,0,2,1,0); (1,2,0,2,1,2);
(1,3,1,1,1,1); (1,3,1,2,2,2); (1,3,1,3,3,3); (1,3,1,4,4,4);
(1,4,1,2,2,2); (1,4,1,3,3,3); (1,4,1,4,4,4); (1,5,1,3,3,3);
(1,5,1,4,4,4); (1,6,1,4,4,4).
```

## 5. Generic root, uniqueness, and descent

**Lemma 5.1 (generic common root).** Let $q$ be an absolutely irreducible
rational conic dividing one of the resultants. In $K=\mathbb Q(q)$, the
corresponding polynomials have a common root $z$ in an algebraic closure of
$K$. The leading coefficients are nonzero: $P$ is monic, $Q$ is monic, and
the leading coefficient of $R$ is $(Y+1)^{m_2}$, which is nonzero in $K$.

If $z'$ is another common root and $z$ is nonconstant, then

$$
z'=\zeta z,
\qquad z'+1=\eta(z+1),
$$

where $\zeta^{n_1}=1$ and $\eta^{n_2}=1$. Hence

$$
(\zeta-\eta)z=\eta-1.
$$

If $\zeta\ne\eta$, this makes $z$ algebraic over $\mathbb Q$, contrary to
the nonzero pole orders below. If $\zeta=\eta$, the same equation gives
$\zeta=\eta=1$. Thus the common root is unique. Every $K$-conjugate of it
is common, and separability in characteristic zero descends $z$ to $K$.

**Proof.** Resultant divisibility gives a common root after mapping the
resultant to the fraction field of the conic. The root equations give the two
root-of-unity relations. The displayed identity then proves uniqueness. A
nonconstant rational-function root has a nonzero pole on each parametrized
survivor, so it cannot be algebraic over the constant field. Finally, all
conjugates are common and uniqueness forces the minimal polynomial to have
degree one. $\square$

This is a generic-function-field statement. It does not assert that every
specialized zero of a resultant has the same root. The survivor arguments use
the generic statement only to rule out a factor, while the $e=1/2$ case is
excluded directly by positivity.

## 6. The rational family

**Lemma 6.1 (the $F$ family).** For $q_e$ use

$$
X=t,\qquad Y=\frac{(e-1)t}{t+e},\qquad
X+1=t+1,\qquad Y+1=\frac{e(t+1)}{t+e}.
$$

For $e\in\mathbb Q\setminus\{0,1\}$, the used poles are nonzero and
distinct. The first monomial has pole orders $m_1$ at $t=-e$ and $k_1$ at
infinity. Since it is an $n_1$-th power, $n_1$ divides both $m_1$ and $k_1$;
primitive normalization of the three exponents gives $n_1=1$. In the $F$
branch, the shifted monomial has pole orders $m_2$ at $-e$ and $k_2$ at
infinity, so the same argument gives $n_2=1$.

The equality of the two rational functions then forces

$$
m_1=m_2=m,\qquad k_1=k_2=k,
\qquad (e-1)^m=e^m.
$$

The ratio $(e-1)/e$ is rational and is a rational root of unity. It cannot be
$1$, so it is $-1$ and $e=1/2$, with $m$ even. But

$$
q_{1/2}(X,Y)=XY+\frac{X+Y}{2}>0
$$

for $X,Y>0$. Therefore no positive lift lies on an $F$-branch member of the
family.

**Lemma 6.2 (the $G$ family).** In the $G$ branch, after $n_1=1$ the first
monomial has a pole at $t=-e$, while

$$
\frac{(X+1)^{k_2}}{(Y+1)^{m_2}}
=e^{-m_2}(t+1)^{k_2-m_2}(t+e)^{m_2}.
$$

At $t=-e$, this ratio has a zero of order $m_2$, whereas $(z+1)^{n_2}$ has
a pole because $z=X^{k_1}Y^{m_1}$ has a pole there. All factors used here are
nonzero away from the indicated simple pole. This is a contradiction. Thus no
positive lift lies on a $G$-branch member of the family.

## 7. The two indefinite exceptions

**Lemma 7.1 (the $F$ indefinite conics).** For

$$
q_{37}=X^2+2XY-Y^2+2X,
$$

use

$$
D=t^2-2t-1,\qquad X=\frac{2}{D},\qquad Y=\frac{2t}{D},
$$

so that

$$
X+1=\frac{(t-1)^2}{D},\qquad
Y+1=\frac{(t-1)(t+1)}{D}.
$$

The roots of $D$ are simple and are distinct from $t=0,-1,1$. The orders of
$X^{k_1}Y^{m_1}$ at a root of $D$ and at $t=0$ are respectively
$-(k_1+m_1)$ and $m_1$. Therefore $n_1$ divides $k_1+m_1$ and $m_1$;
the primitive gcd of all three exponents gives $n_1=1$. In the $F$ branch,
the shifted orders at a root of $D$ and at $t=-1$ give divisibility by
$k_2+m_2$ and $m_2$, hence $n_2=1$.

At $t=1$, $X=Y=-1$. If $k_1+m_1$ is even, $z+1$ has order zero. If it
is odd, its logarithmic derivative is nonzero and it has order one. In either
case, the shifted monomial has order $2k_2+m_2\ge3$, a contradiction.

The exchanged conic is

$$
q_{22}=X^2-2XY-Y^2-2Y.
$$

Exchanging $X$ and $Y$ in the preceding parametrization gives the same
argument, with shifted order $k_2+2m_2\ge3$ and the nonzero derivative
coming from the $k_1$ term. Thus neither $F$ exception admits a positive lift.

**Lemma 7.2 (the $G$ exceptional conic).** Only $q_{22}$ is $G$-compatible.
Use

$$
D=t^2-2t-1,\qquad X=\frac{2t}{D},\qquad Y=\frac{2}{D}.
$$

At roots of $D$, and at $t=0$, the first relation gives
$n_1\mid(k_1+m_1)$ and $n_1\mid k_1$, hence $n_1\mid m_1$.
Primitive normalization therefore gives $n_1=1$. The shifted ratio is

$$
\frac{(X+1)^{k_2}}{(Y+1)^{m_2}}
=(t-1)^{k_2-2m_2}(t+1)^{k_2}D^{m_2-k_2}.
$$

Its orders at $t=-1$ and at a root of $D$ are $k_2$ and $m_2-k_2$.
Primitive normalization therefore gives $n_2=1$. At $t=-1$, $X=-1$, $Y=1$,
so $z=(-1)^{k_1}$ and the logarithmic derivative of $z$ is
$k_1+2m_1\ne0$. Hence $z+1$ has order at most one, forcing $k_2\le1$.
At a root of $D$, $z+1$ has pole order $k_1+m_1$. The ratio can have a
pole only if $k_2>m_2\ge1$, which contradicts $k_2\le1$. Thus the $G$
exception admits no positive lift.

## 8. Conditional counting deduction

**Theorem 8.1 (conditional $H^{1/3}$ upper bound).** Let $M(H)$ count
positive triples in $[1,H]^3$ having pairwise distinct coordinates, with both
the unshifted and shifted triples multiplicatively dependent of maximal rank.
Assume the reduction of Shparlinski and Sleiman
([arXiv:2609.29408v1](https://arxiv.org/html/2609.29408v1),
Lemmas 2.1--2.2 and Sections 3.1--3.4), including its finite sign and
permutation reduction, its
$O((\log H)^{12})$ exponent vectors with each exponent
$O((\log H)^2)$, and its $O(1)$ treatment of every complex linear factor in
both branches, including vertical factors. Then the positive-lift theorem
above implies

$$
M(H)\ll H^{1/3}(\log H)^{\kappa+20},
$$

where $\kappa$ is the absolute exponent in the source plane-curve bound.

**Proof.** First, the resultants are nonzero. At $X=0$,
$P=Z^{n_1}$, and direct specialization gives

$$
F_{\boldsymbol e}(0,Y)=\bigl(1-(Y+1)^{m_2}\bigr)^{n_1},
\qquad
G_{\boldsymbol e}(0,Y)=\bigl((Y+1)^{m_2}-1\bigr)^{n_1},
$$

up to the harmless global sign convention for the resultant. Both are
nonzero polynomials.

Take the squarefree part of each resultant and factor it over $\mathbb Q$:

$$
\operatorname{rad}(F_{\boldsymbol e})=\prod_i f_i,
\qquad
\operatorname{rad}(G_{\boldsymbol e})=\prod_j g_j,
$$

with $f_i,g_j$ distinct and irreducible over $\mathbb Q$. Repeated factors
do not create new points and are therefore not counted repeatedly. Every
absolute component not defined over $\mathbb Q$ is grouped with all of its
Galois conjugates into one of these rational irreducible factors. This is the
required grouping before applying a rational curve estimate.

If $E$ bounds all six exponents, the Sylvester determinant gives

$$
\deg F_{\boldsymbol e},\deg G_{\boldsymbol e}
\le n_2(k_1+m_1)+n_1(k_2+m_2)\le4E^2.
$$

Thus each resultant has total degree $O((\log H)^4)$. If $d_i$ are the
degrees of the rational factors of either squarefree part, then

$$
\sum_i d_i=O((\log H)^4),
\qquad
\sum_i d_i^2\le\left(\sum_i d_i\right)^2=O((\log H)^8).
$$

Degree-one factors contribute $O(1)$ genuine triples by the source Sections
3.2--3.3 argument. For completeness, vertical factors have no positive lifts:
for $x_0>1$,

$$
G(x_0,-1)=\bigl(-(x_0+1)^{k_2}\bigr)^{n_1}\ne0.
$$

For a vertical $F$ factor at $X=\alpha>1$, specialization at $Y=-1$
would force $Z=-1$ and hence $\alpha^{k_1}=(-1)^{n_1}$, which is impossible.
For degree two, an absolutely irreducible rational factor is excluded by Theorem 3.1. If a rational
quadratic is geometrically reducible, its components are lines. Rational lines
are already in the degree-one case; a pair of distinct conjugate non-rational
lines has only their intersection as a rational point, so contributes $O(1)$.

Every remaining rational factor has degree $d\ge3$. The coefficient-uniform
curve estimate of Binyamini, Cluckers, and Kato, as stated in
Shparlinski--Sleiman, Lemma 2.1 (reference [6]), gives

$$
N_i(H)\ll d_i^2 H^{1/d_i}(\log H)^\kappa
\le d_i^2 H^{1/3}(\log H)^\kappa.
$$

Summing the rational factors, both resultants, and the
$O((\log H)^{12})$ exponent vectors gives the exponent
$8+12=20$ in the logarithm. Finally, for fixed exponents and fixed $(a,b)$,
the equation $P=0$ is strictly increasing in $c>0$, so it has at most one
positive $c$. In the $R$ branch the shifted left side
$(c+1)^{n_2}(b+1)^{m_2}$ is also strictly increasing, so no multiplicity is
introduced by the second equation. The source transfer from curve points to
triples in its equations (3.8)--(3.9) now yields the claim. $\square$

## 追加锚（本行以下为增补区）
