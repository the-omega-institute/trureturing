# FIB MJM 临界第四 M 纤维的两新增世界排除

## 1. 完整世界、实际历史与指定支持

**定义 1.1（完整世界与失败递归）。** A world is a triple $W=(P,g,d)$, where $P$ is a strictly entrywise positive real $2\times2$ matrix of rank one and trace one, $g\in\mathbb R[t]\setminus\{0\}$ has degree at most three, and $d\in\mathbb R$. Put

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

For a chronological word $E_1\cdots E_k$, set $A_0=I$ and $A_i=E_iA_{i-1}$. The response at original clock $i$ is $g(i)\operatorname{tr}(A_iP)+d$. The set $\mathcal F(H)$ consists of every world realizing the entire literal history $H$. For $K\subseteq\mathcal F(H)$, write $K_{E,z}=K\cap\mathcal F(H,E,z)$ and define

$$
\begin{aligned}
L_0(K,H)&\iff |K|\ge2,\\
L_{s+1}(K,H)&\iff |K|\ge2\ \land\
 \forall E\in\{M,J\}\ \exists z\in\mathbb R:
 L_s(K_{E,z},(H,E,z)).
\end{aligned}                                                     \tag{1.1}
$$

Each world retains its same source, entire gain and drift at every shared prefix. There is one unresettable, uncopyable trajectory, each atomic action is immediately read, and the initial reading at clock zero counts. The remaining clocks at $H_4$ are exactly $5,6,7$. Actions, stopping and returned worlds may depend arbitrarily and deterministically on the entire actual history. The cardinality guard includes stopping. These are the whole-world and actual-history conventions of [VI, Definition 1.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VI.md).

**定义 1.2（临界第四 M 历史）。** Put

$$
\begin{gathered}
h(t)=(t-1)(t-3)(t-7),\qquad
P_r=\begin{pmatrix}1-r&12r(1-r)\\1/12&r\end{pmatrix},\qquad U_r=(P_r,h,0),\\
H_3=(-21,M,0,J,65/12,M,0),\qquad
H_4=(H_3,M,-93/2),\\
z_{1/2}=-76,\qquad z_{2/3}=-220/3,\qquad
H_5^r=(H_4,J,z_r)\quad(r\in\{1/2,2/3\}).
\end{gathered}                                                     \tag{1.2}
$$

Both $U_{1/2}$ and $U_{2/3}$ realize $H_4$. Their fifth-$J$ responses are the distinct values $z_r$. The cumulative matrices at clocks four and five are

$$
A_4=\begin{pmatrix}1&2\\1&3\end{pmatrix},\qquad
Q=JA_4=\begin{pmatrix}1&3\\1&2\end{pmatrix}.
\tag{1.3}
$$

The corresponding sixth responses are $-275/2$ after $M$ and $-155/2$ after $J$, for either $r$; every seventh response is zero. The common fourth history and the fifth responses are [V, Theorem 6.1 and Proposition 6.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md). The sixth values follow from the trace table in Definition 2.1 below and $h(6)=-15$.

## 2. 八读点纤维的有限整数证书

**定义 2.1（八种数据与正来源图）。** For each $z\in\{-76,-220/3\}$ and $w=EF\in\{MM,MJ,JM,JJ\}$, use independent variables $x,y$ and put

$$
R(x,y)=\begin{pmatrix}(3-2x)y&3-2x\\(x-1)y&x-1\end{pmatrix}.
\tag{2.1}
$$

Every legal source has a unique such representative: if $\eta=(QP)_{22}>0$, then $R=P/\eta$ and

$$
QR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
1<x<3/2,\quad y>0.
\tag{2.2}
$$

Conversely (2.2) makes $R$ strictly positive of rank one and $P=R/\operatorname{tr}R$ legal. This is the source chart of [VI, Definition 4.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VI.md), for the same cumulative matrix $Q$. Its trace polynomials at clocks zero through five are

$$
\begin{aligned}
T_0&=-2xy+x+3y-1,& T_1&=xy-x-y+2,\\
T_2&=-xy+x+2y-1,& T_3&=xy-y+1,\\
T_4&=x+y,&T_5&=xy+1.
\end{aligned}                                                     \tag{2.3}
$$

For the chronological sixth and seventh actions $EF$, complete the table by

| $w=EF$ | $T_6=\operatorname{tr}(EQR)$ | $T_7=\operatorname{tr}(FEQR)$ |
| --- | --- | --- |
| $MM$ | $x+y+1$ | $xy+x+y+2$ |
| $MJ$ | $x+y+1$ | $xy+y+1$ |
| $JM$ | $x+y$ | $xy+x+1$ |
| $JJ$ | $x+y$ | $xy+1$ |

Define the data vector

$$
v=(-21,0,65/12,0,-93/2,z,v_6,0),\qquad
v_6=\begin{cases}-275/2&E=M,\\-155/2&E=J.\end{cases}
\tag{2.4}
$$

The source coordinates of the prescribed world are

$$
u_z=(x_z,y_z)=
\begin{cases}(9/8,1/6)&z=-76,\\(7/6,1/8)&z=-220/3.\end{cases}
\tag{2.5}
$$

At either point, $\operatorname{tr}R=1/4$, $P=4R=P_r$, and the normalized gain $G=\eta g$ is $4h$.

**定义 2.2（消去漂移的六个多项式）。** Let

$$
\ell_j(t)=\prod_{\substack{0\le k\le3\\k\ne j}}\frac{t-k}{j-k}
\quad(0\le j\le3),\qquad D=T_0T_1T_2T_3.
$$

For $n=4,5,6,7$, define

$$
\bigl(\ell_0(n),\ell_1(n),\ell_2(n),\ell_3(n)\bigr)=
\begin{cases}
(-1,4,-6,4)&n=4,\\
(-4,15,-20,10)&n=5,\\
(-10,36,-45,20)&n=6,\\
(-20,70,-84,35)&n=7,
\end{cases}
$$

and

$$
\begin{aligned}
a_n&=D\left(1-T_n\sum_{j=0}^3\frac{\ell_j(n)}{T_j}\right),\\
b_n&=D\left(T_n\sum_{j=0}^3\frac{v_j\ell_j(n)}{T_j}-v_n\right),\\
f_{nm}&=\frac{12(a_nb_m-a_mb_n)}{D}\quad(4\le n<m\le7).
\end{aligned}                                                     \tag{2.6}
$$

All six $f_{nm}$ lie in $\mathbb Z[x,y]$ and have degree at most four in each variable. Order them as

$$
(f_{45},f_{46},f_{47},f_{56},f_{57},f_{67})=(f_0,\ldots,f_5).
\tag{2.7}
$$

Let $V$ be the $49$-dimensional real space spanned by $x^uy^v$, $0\le u,v\le6$. Define the integer matrix $C=C_{z,w}$ by

$$
C_{9k+3a+b,\,7u+v}=[x^uy^v](x^ay^bf_k),
\quad 0\le k\le5,\quad 0\le a,b\le2,\quad 0\le u,v\le6.
\tag{2.8}
$$

Thus $C$ has $54$ rows and $49$ columns, with all indices starting at zero. Its row space is identified with a polynomial subspace of $V$.

**定理 2.3（精确行空间证书）。** For $p\in V$, write $p_j(x)=[y^j]p(x,y)$ and define

$$
\Lambda_0(p)=p_6(1),\qquad
\Lambda_1(p)=p_5(1)-p_6'(1).
\tag{2.9}
$$

Set $\psi_\pm=(-1\pm\sqrt5)/2$ and

$$
S_{z,w}=\begin{cases}
\{u_z\},&w\ne JM,\\
\{u_z,(-\psi_+,\psi_+),(-\psi_-,\psi_-)\},&w=JM.
\end{cases}
$$

Then, for every one of the eight choices $(z,w)$,

$$
\operatorname{row}(C_{z,w})=
\ker\Lambda_0\cap\ker\Lambda_1\cap
\bigcap_{q\in S_{z,w}}\{p\in V:p(q)=0\}.
\tag{2.10}
$$

Proof. The expressions in (2.6) are polynomials: the factors $D/T_j$ are polynomial, and in the alternating expression for $a_nb_m-a_mb_n$ the terms with two equal denominator factors cancel. Every other product denominator divides $D$, leaving $D$ as a factor of that alternating expression. Expanding gives integral coefficients after the factor $12$, and bidegree at most $(4,4)$.

The following polynomial identities, together with the determinant table below, give a finite certificate for (2.10). For each of its six $f=f_k$, put $f_j(x)=[y^j]f$. Substitution in (2.6) gives

$$
\begin{gathered}
f(u_z)=0,\qquad f_4(1)=0,\qquad f_3(1)-f_4'(1)=0,\\
\text{if }w=JM:\quad f(-y,y)\equiv0\pmod{y^2+y-1}.
\end{gathered}                                                     \tag{2.11}
$$

These identities also show that all $x^ay^bf$, $0\le a,b\le2$, belong to the right side of (2.10). For the two functionals in (2.9), the only nontrivial case is $b=2$, when the last two identities at $x=1$ in the first line of (2.11) apply. For $b=1$ only $f_4(1)=0$ is needed, and for $b=0$ both functionals vanish by degree.

Here are square integer minors of (2.8). Use ascending row and column order and put

$$
\begin{aligned}
I_{46}&=\{0,\ldots,34\}\cup\{36,\ldots,43\}\cup\{45,46,47\},\\
I_{44}&=\{0,\ldots,34\}\cup\{36,\ldots,43\}\cup\{45\},\\
J_r&=\{0,\ldots,r-1\},\qquad N_{z,w}=C_{z,w}[I_r,J_r].
\end{aligned}                                                     \tag{2.12}
$$

The determinants, reduced modulo $1000003$, are

| $z$ | $w$ | $r$ | $\det N_{z,w}\pmod{1000003}$ |
| --- | --- | --- | --- |
| $-76$ | $MM$ | $46$ | $6010$ |
| $-76$ | $MJ$ | $46$ | $600600$ |
| $-76$ | $JM$ | $44$ | $176698$ |
| $-76$ | $JJ$ | $46$ | $372449$ |
| $-220/3$ | $MM$ | $46$ | $535142$ |
| $-220/3$ | $MJ$ | $46$ | $894382$ |
| $-220/3$ | $JM$ | $44$ | $358619$ |
| $-220/3$ | $JJ$ | $46$ | $518998$ |

All entries of these minors are specified by (2.3)–(2.8); the displayed congruences are obtained by integer determinant expansion. Their nonzero residues imply rank at least $r$ over $\mathbb R$.

The functionals defining the right side of (2.10) are independent. When there is one evaluation, restrict first to the constant polynomial. When there are three, restrict to $1,y,y^2$; their three $y$ coordinates are distinct, so the evaluation matrix is Vandermonde and invertible. Both $\Lambda_i$ vanish on these low degree polynomials. After eliminating the evaluation functionals, use $y^6,y^5$ to see that $\Lambda_0,\Lambda_1$ are independent. The right side therefore has dimension $46$ when $w\ne JM$ and $44$ when $w=JM$. Its inclusion of every row, and the matching lower rank bounds, prove (2.10). ∎

**推论 2.4（正域中的唯一共同零点）。** In the domain $1<x<3/2$, $y>0$, the simultaneous equations $f_k(x,y)=0$ for all $0\le k\le5$ have only the solution $u_z$.

Proof. If $w\ne JM$, both $x-x_z$ and $y-y_z$ belong to the right side of (2.10), and hence to the row space. Every common zero of the six $f_k$ annihilates every row polynomial and their linear combinations. Thus $x=x_z,y=y_z$.

For $w=JM$, the following two polynomials belong to the same row space:

| $z$ | first polynomial | second polynomial |
| --- | --- | --- |
| $-76$ | $58x+93y^2+151y-93$ | $(6y-1)(y^2+y-1)$ |
| $-220/3$ | $165x+248y^2+413y-248$ | $(8y-1)(y^2+y-1)$ |

Indeed they vanish at all three points in $S_{z,JM}$ and have zero $\Lambda_0,\Lambda_1$. At a common zero, the second polynomial gives $y=y_z$ or $y^2+y-1=0$. In the first case the first polynomial gives $x=x_z$. In the second, that polynomial reduces to $58(x+y)$ or $165(x+y)$, respectively. This contradicts $x>1,y>0$. ∎

## 3. 点纤维刚性与完整四世界排除

**定理 3.1（指定 U 的四条八读点纤维）。** Fix $r\in\{1/2,2/3\}$ and $E,F\in\{M,J\}$. If a legal complete world $W$ realizes $H_5^r$, has the same actual sixth response as $U_r$ after $E$, and has the same actual seventh response as $U_r$ after the chronological suffix $EF$, then $W=U_r$.

Proof. Apply the chart (2.1)–(2.2) to the source of $W$, and let $G=\eta g$. All $T_j$ at $j=0,1,2,3$ are strictly positive, so $D>0$. The entire gain $G$ has degree at most three. Its first four values therefore determine it by

$$
G(t)=\sum_{j=0}^3\frac{v_j-d}{T_j}\ell_j(t).
\tag{3.1}
$$

The four remaining actual response equations are exactly $a_nd+b_n=0$, $4\le n\le7$. Hence all six $f_{nm}$ vanish. Corollary 2.4 identifies the source coordinates as $u_{z_r}$, including every possible sign of the drift or gain and every lower degree.

At these coordinates, $b_4=0$ and

$$
a_4(u_{-76})=\frac{3936643}{2654208},\qquad
a_4(u_{-220/3})=\frac{3709457}{2654208}.
\tag{3.2}
$$

Both are nonzero, so $a_4d+b_4=0$ gives $d=0$. Formula (3.1) now gives $G=4h$. Since $\operatorname{tr}R=1/4$, the original normalized source and gain are $P=4R=P_r$ and $g=G/4=h$. This proves equality of the entire worlds. Only the single word $MJMMJEF$ is used in this point-fiber assertion. ∎

**定理 3.2（含指定 U 的三世界两读排除）。** For $r\in\{1/2,2/3\}$ and any pairwise distinct complete worlds $U_r,B,C\in\mathcal F(H_5^r)$,

$$
\neg L_2(\{U_r,B,C\},H_5^r).
\tag{3.3}
$$

Proof. Suppose the triple has $L_2$. For each sixth action $E$, choose its actual $L_1$ response child $S_E$. If $U_r\notin S_E$, the cardinality guard forces $S_E=\{B,C\}$. If $U_r\in S_E$, no terminal collision under either final action can involve $U_r$: another member in that collision would share the whole fifth history, the sixth response, and that seventh response with $U_r$, contrary to Theorem 3.1. Consequently the collision required for each final action must again be the pair $B,C$.

For both sixth actions, therefore, $B,C$ share the selected sixth response and both terminal responses after that sixth action. Thus the same pair $\{B,C\}$ has $L_2$ at $H_5^r$.

Apply [VI, Theorem 5.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VI.md) with $D_0=0$, $\lambda=1$, $\varepsilon=1/12$, $Y=-93/2$, and $z=z_r$. It excludes every distinct two-world $L_2$ in precisely this actual $MJMMJ$ fiber, without drift, root or gain-shape promises. This is a contradiction. The two terminal collision pairs were allowed to differ before Theorem 3.1 forced them to be $B,C$. ∎

**定理 3.3（两个新增完整世界不能补成临界 L3）。** For all legal complete worlds $B,C\in\mathcal F(H_4)$ such that $B,C,U_{1/2},U_{2/3}$ are pairwise distinct,

$$
\neg L_3(\{U_{1/2},U_{2/3},B,C\},H_4).
\tag{3.4}
$$

Proof. Write the four-world set as $K$ and suppose $L_3(K,H_4)$. Its fifth-$J$ branch has an actual response child $K_{J,z}$ with $L_2$. It has at least two worlds. VI, Theorem 5.1, with the same parameters just specified and this actual $z$, excludes cardinality two.

The two prescribed worlds have different fifth-$J$ responses, so $K_{J,z}$ contains at most one of them and hence at most three worlds. It must therefore be exactly $\{U_r,B,C\}$ for one $r\in\{1/2,2/3\}$, with $z=z_r$. Theorem 3.2 excludes $L_2$ on this same triple. This contradiction proves (3.4) for every allowed source, entire gain and drift of both additions. ∎

## 4. 复用范围与未决祖先

**约定 4.1（数学来源与结论范围）。** The literal histories, baseline root-seven inverse, and arbitrary-drift two-world exclusion are respectively IV, Theorem 3.1; V, Theorem 6.1 and Proposition 6.2; and VI, Theorem 5.1. VI, Lemma 18.1, concerns the four matrices $I,JM,MJ,M^2$ at one shared terminal clock; its subsequent injectivity theorem has a different parent history and is not used here. The extra first-response hypotheses of the mixed-prefix triple exclusion are not assumed.

The coefficient-space certificate in Section 2, the four point fibers of Theorem 3.1, and their consumption in Theorems 3.2–3.3 are model-specific deductions (repo-derived). Lagrange interpolation, finite-dimensional duality and integer determinants are classical intermediate tools. Li–Lee–Bresler, [arXiv:1501.06120v1](https://arxiv.org/html/1501.06120v1), Theorem 2.8, treats constrained bilinear identifiability modulo its specified ambiguity group; it does not identify the unknown source in this history. Van den Bos–Vaandrager, [arXiv:1907.11034v2](https://arxiv.org/html/1907.11034v2), Section 4, defines adaptive distinguishing graphs for suspension automata; its finite-state results supply no continuous-world response certificate here. No literature priority claim is made for these deductions.

**开放问题 4.2（其他支持与更早兄弟）。** The existence of another finite $K\subseteq\mathcal F(H_4)$ with $L_3(K,H_4)$ is not decided by (3.4). Larger losing supports need not contain a losing pair or a losing subset of size four. IV, Theorem 3.1, still supplies the fourth-$J$ $L_3$ sibling at $H_3$; an actual fourth-$M$ $L_3$ remains necessary for that route to a same-ancestor $L_4$.

Under the affine response translation by $+21$ of [V, Lemmas 9.2–9.3](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md), the corresponding third-clock history is

$$
\overline H_3=(0,M,21,J,317/12,M,21).
$$

The third-$J$ $L_4$ at $(0,M,21,J,317/12)$ and the second-$M$ $L_5$ at $(0,M,21)$ remain separate requirements for the indicated initial-$M$ $L_6$ route. Initial $J$, the original root, and a nine-reading upper bound are not decided by this fixed-support exclusion.

## 追加锚（本行以下为增补区）
