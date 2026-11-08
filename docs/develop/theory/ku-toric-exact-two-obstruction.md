# The exact-two obstruction on Ku's toric board

## 1. Toric lines and the incidence condition

**Definition 1.1 (Toric board and signed directions).** For a positive integer
$k$, let $R_k=\mathbb Z/k\mathbb Z$ and let $T_k=R_k^2$. Put

$$
\mathcal D=\{-1,0,1\}^2\setminus\{(0,0)\}.
$$

For $p\in T_k$ and $\delta\in\mathcal D$, define the toric line

$$
L_k(p,\delta)=\{p+t\delta: t=0,1,\ldots,k-1\}\subseteq T_k,
\tag{1.1}
$$

where both coordinates are reduced modulo $k$. Let $\mathcal L_k$ be the
family of these subsets. This is the toric $k$-board of shape $(k,k)$ in
Ku's Definition 2.2 [1], with dimension $d=2$. Directions with one zero
coordinate give the axis-parallel lines, and directions with both coordinates
nonzero give the diagonal lines. In particular, the permitted directions are
the signed directions in $\mathcal D$.

**Definition 1.2 (Exact-two incidence).** A subset $A\subseteq T_k$ satisfies
the exact-two incidence condition if

$$
\lvert A\cap L_k(p,\delta)\rvert=2
\qquad\text{for every }p\in T_k\text{ and every }\delta\in\mathcal D.
\tag{1.2}
$$

Intersections in (1.2) are intersections of sets. Repeated parametrizations
of the same line impose the same condition.

## 2. The exact-two obstruction

**Theorem 2.1 (Ku's Conjecture 5.3).** For every positive integer $k$ such
that $3\mid k$ and every subset $A\subseteq T_k$, there exist $p\in T_k$
and $\delta\in\mathcal D$ such that

$$
\lvert A\cap L_k(p,\delta)\rvert\ne2.
\tag{2.1}
$$

Equivalently, no subset of $(\mathbb Z/k\mathbb Z)^2$ satisfies (1.2) for
any positive multiple $k$ of three. The statement is the exact incidence
formulation of [1, Section 5.1.1, Conjecture 5.3], using its Definition 2.2.

*Proof.* Fix a positive integer $k$ divisible by three, and suppose that
$A\subseteq T_k$ satisfies (1.2). Write $R=R_k$. For each $a\in R$,
consider the following four fibers:

$$
\begin{aligned}
C_a&=\{(a,t):t\in R\}=\{(x,y)\in R^2:x=a\},\\
H_a&=\{(t,a):t\in R\}=\{(x,y)\in R^2:y=a\},\\
E_a&=\{(a+t,-t):t\in R\}=\{(x,y)\in R^2:x+y=a\},\\
F_a&=\{(a+t,t):t\in R\}=\{(x,y)\in R^2:x-y=a\}.
\end{aligned}
\tag{2.2}
$$

These are respectively the lines with base points $(a,0)$, $(0,a)$,
$(a,0)$, $(a,0)$ and directions $(0,1)$, $(1,0)$, $(1,-1)$, $(1,1)$.
Every parametrization in (2.2) has $k$ distinct points: equality of the
second coordinates forces equality of the parameters in $R$, except for
$H_a$, where the first coordinate does so.

Conversely, up to sign every direction in $\mathcal D$ is one of these
four directions. Reversing the direction leaves the line set unchanged,
because negation permutes the parameter residues in $R$. A line through
$p=(p_1,p_2)$ in these four directions is respectively $C_{p_1}$,
$H_{p_2}$, $E_{p_1+p_2}$ or $F_{p_1-p_2}$. Thus (2.2), as $a$ ranges
over $R$, gives precisely the axis-parallel and diagonal toric line
families in (1.1). The assumption implies

$$
\lvert A\cap C_a\rvert=
\lvert A\cap H_a\rvert=
\lvert A\cap E_a\rvert=
\lvert A\cap F_a\rvert=2
\qquad(a\in R).
\tag{2.3}
$$

We use the modular square-sum method described by Alvis and Kinyon
[2, Section 2, Lemma 2.1 and the sentence preceding Theorem 2.1]. Their
Theorem 2.1 states that a panmagic permutation of degree $n$ exists if and
only if $\gcd(n,6)=1$. Such a permutation selects exactly one point in
every row, column and toric diagonal. Here we apply the square-sum
calculation directly to (2.3), with multiplicity two; no decomposition of
$A$ into panmagic permutations is assumed.

Let $\rho:R\longrightarrow\{0,1,\ldots,k-1\}$ select the integer
representative of a residue. For $P=(x,y)\in A$, put

$$
X(P)=\rho(x),\qquad Y(P)=\rho(y),\qquad
U(P)=\rho(x+y),\qquad V(P)=\rho(x-y).
\tag{2.4}
$$

All four quantities in (2.4) are integers. Define the integer

$$
S=\sum_{r=0}^{k-1}r^2=\frac{k(k-1)(2k-1)}6.
\tag{2.5}
$$

For completeness, the square-sum identity in (2.5) follows by induction:
it holds at $k=1$, and the difference between its right-hand sides at
$k+1$ and $k$ is

$$
\frac{k\bigl((k+1)(2k+1)-(k-1)(2k-1)\bigr)}6=k^2,
$$

which is exactly the additional summand on its left-hand side.

By (2.3), every residue occurs exactly twice as an $x$-coordinate of a
point of $A$, exactly twice as a $y$-coordinate, exactly twice as a value
of $x+y$, and exactly twice as a value of $x-y$. Grouping each sum by its
corresponding fiber therefore gives the integer equalities

$$
\sum_{P\in A}X(P)^2
=\sum_{P\in A}Y(P)^2
=\sum_{P\in A}U(P)^2
=\sum_{P\in A}V(P)^2
=2\sum_{r=0}^{k-1}r^2=2S.
\tag{2.6}
$$

The definitions of the representatives imply
$U(P)\equiv X(P)+Y(P)\pmod k$ and
$V(P)\equiv X(P)-Y(P)\pmod k$. Consequently, for each $P\in A$,

$$
\begin{aligned}
U(P)^2+V(P)^2
&\equiv (X(P)+Y(P))^2+(X(P)-Y(P))^2\\
&=2X(P)^2+2Y(P)^2\pmod k.
\end{aligned}
\tag{2.7}
$$

Summing (2.7) over $A$ and substituting (2.6) yields

$$
4S\equiv8S\pmod k,
\qquad\text{hence}\qquad k\mid4S.
\tag{2.8}
$$

Write $k=3m$ with $m$ a positive integer. Formula (2.5) is an equality
of rational numbers with integer left-hand side, so it gives the exact
integer identity

$$
4S=\frac{2k(k-1)(2k-1)}3
=2m(k-1)(2k-1).
\tag{2.9}
$$

By (2.8) there is an integer $q$ such that $4S=3mq$. Combining this
with (2.9) and cancelling the nonzero integer $m$ in the integer equality
gives

$$
2(k-1)(2k-1)=3q.
\tag{2.10}
$$

But $k\equiv0\pmod3$, and therefore

$$
2(k-1)(2k-1)\equiv2(-1)(-1)=2\pmod3,
$$

contradicting (2.10). This excludes (1.2) for every positive multiple
$k$ of three, and proves (2.1). The cancellation used only an integer
equality; it imposes no parity or squarefreeness condition on $k$.
$\square$

The problem is attributed to Ku [1], and the modular square-sum method to
the cited discussion of Alvis and Kinyon [2], which also cites earlier
work. No historical priority claim is made for the exact multiplicity-two
conclusion of Theorem 2.1.

## 3. Mathematical references

[1] Kuo-Han Ku, *Monochromatic k in a row*,
[arXiv:2606.12880v1](https://arxiv.org/html/2606.12880v1),
Definition 2.2 and Section 5.1.1, Conjecture 5.3.

[2] Dean L. Alvis and Michael K. Kinyon, *Birkhoff's Theorem for
Panstochastic Matrices*, **The American Mathematical Monthly** 108 (2001),
no. 1, 28–37,
[doi:10.1080/00029890.2001.11919718](https://doi.org/10.1080/00029890.2001.11919718).
The cited definitions and statements are in
[arXiv:math/9911109v4](https://arxiv.org/html/math/9911109v4), Sections 1–2,
especially Lemma 2.1, Theorem 2.1 and the square-sum observation preceding
that theorem.

## 追加锚（本行以下为增补区）
