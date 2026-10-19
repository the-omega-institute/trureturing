# FIB 自校准关系数学 IV

## 1. 原子时钟、完整目标与失败纤维

**定义 1.1（完整采集域）。** Let

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

The domain $\mathcal W_3$ consists of all triples $W=(P,g,\delta)$ with $P$ a strictly entrywise positive real $2\times2$ matrix of rank one and trace one, $0\ne g\in\mathbb R[t]$ of degree at most three, and $\delta\in\mathbb R$. For a chronological action word $E_1\cdots E_i$, set

$$
A_0=I,\qquad A_i=E_iA_{i-1},\qquad
z_i(W)=g(i)\operatorname{tr}(A_iP)+\delta.
\tag{1.1}
$$

The initial read counts. Each action is one $M$ or one $J$, followed immediately by its read. Eight total reads have exactly the original clocks $0,\ldots,7$. There is one trajectory, with no reset, copy, skipped read, empty-action read, unread compound action, clock renumbering or additional sensor. A deterministic protocol may use the entire actual history to choose an action, stop, and return the complete target $(P,g,\delta)$; no regularity assumption is imposed on those functions. All coefficient signs, lower actual degrees, sampled roots, repeated roots and constant drifts belong to the domain.

The conventions agree with [II, Definitions 51.1–51.2](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md) and [III, Definition 1.1](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md). An unnormalized positive rank-one matrix $R$ and polynomial $G\ne0$ denote the target

$$
\left(\frac R{\operatorname{tr}R},\ (\operatorname{tr}R)G,\ \delta\right).
\tag{1.2}
$$

Indeed its read is $G(i)\operatorname{tr}(A_iR)+\delta$. Positive scaling preserves every gain sign and root. Two unnormalized representatives give the same target exactly when $(R',G',\delta')=(cR,G/c,\delta)$ for some $c>0$.

**定义 1.2（实际历史上的失败）。** Write $\mathcal F(H)$ for all complete targets realizing every action and every read of the literal history $H$. For $\mathcal K\subseteq\mathcal F(H)$, use the failure predicate of II, Definition 56.1:

$$
\begin{aligned}
L_0(\mathcal K,H)&\ \Longleftrightarrow\ |\mathcal K|\ge2,\\
L_s(\mathcal K,H)&\ \Longleftrightarrow\ L_0(\mathcal K,H)\ \land\
\bigwedge_{E\in\{M,J\}}\exists z\in\mathbb R:
L_{s-1}(\mathcal K\cap\mathcal F(H,E,z),(H,E,z)).
\end{aligned}
\tag{1.3}
$$

Here $s$ never exceeds the remaining original-clock budget. This is failure of every strategy with at most $s$ further reads, including early stopping. Its elementary recursion also gives upward monotonicity under inclusion of compatible target families. A response on an unchosen branch is a mathematical function of a fixed world, not an extra acquired read. In particular, a different pair for each terminal word is useful only when those pairs realize the common responses at all their shared ancestors.

## 2. 初始 J 一侧的完整三步失败子树

**定理 2.1（JMMM 的三个固定目标）。** For every $\lambda\ne0$ and $\delta\in\mathbb R$, the unrestricted fiber of

$$
H_J=(\delta,J,\delta+24\lambda,M,\delta+48\lambda,
M,\delta+312\lambda/5,M,\delta+252\lambda/5)
\tag{2.1}
$$

has $L_3$. A three-target subfamily suffices.

Proof. Use the same $G(t)=\lambda t(t-5)(t-7)$ and drift $\delta$ with

$$
R_1=\frac1{55}\begin{pmatrix}12&19\\36&57\end{pmatrix},\quad
R_2=\frac1{55}\begin{pmatrix}18&28\\27&42\end{pmatrix},\quad
R_3=\frac1{55}\begin{pmatrix}28&35\\20&25\end{pmatrix}.
\tag{2.2}
$$

Their determinants vanish by $12\cdot57=19\cdot36$, $18\cdot42=28\cdot27$ and $28\cdot25=35\cdot20$. All entries are positive, and the traces are $69/55,60/55,53/55$. Formula (1.2) therefore gives legal targets. Their left-factor ratios $R_{21}/R_{11}=3,3/2,5/7$ are different, so the targets are distinct.

Put $L=MJ=(\begin{smallmatrix}1&0\\1&1\end{smallmatrix})$. The cumulative matrices through $JMMM$ are

$$
I,\ J,\ L,\ J+L,\ J+2L.
$$

Every $R_i$ has $\operatorname{tr}(JR_i)=1$ and $\operatorname{tr}(LR_i)=8/5$. The corresponding gain samples are $\lambda(0,24,30,24,12)$. Thus every world realizes every read in (2.1), including clock zero.

Both fifth actions read $\delta$, since $G(5)=0$. At clock six the complete response table is as follows; the two letters are the chronological fifth and sixth actions.

| Fifth and sixth actions | $(z_6(R_1),z_6(R_2),z_6(R_3))-\delta(1,1,1)$ |
| --- | --- |
| $MM$ | $\lambda(-66,-66,-66)$ |
| $MJ$ | $\lambda(-2034/55,-2034/55,-426/11)$ |
| $JM$ | $\lambda(-1956/55,-1974/55,-1956/55)$ |
| $JJ$ | $\lambda(-126/5,-126/5,-126/5)$ |

For example these entries are obtained by taking the traces of $E_6E_5(J+2L)R_i$ and multiplying by $G(6)=-6\lambda$. Every final action reads $\delta$, since $G(7)=0$.

After fifth $M$, retain all three worlds at its actual read $\delta$. Sixth $M$ retains all three; sixth $J$ retains worlds $1,2$. After fifth $J$, likewise retain the actual read $\delta$. Sixth $M$ retains worlds $1,3$; sixth $J$ retains all three. Each selected sixth child contains two distinct targets, and either final action retains them. Hence each fifth child has $L_2$, and the parent has $L_3$. At every node used in this argument the retained distinct pair also rules out stopping. Upward monotonicity gives the unrestricted-fiber conclusion. ∎

**推论 2.2（JMM 历史上的条件强制）。** At the history obtained from (2.1) by deleting its last action and read, a correct protocol on all of $\mathcal W_3$ using at most eight total reads must continue with fourth action $J$.

Proof. The three worlds already agree on that preceding history, so stopping cannot recover all of them. Fourth $M$ reaches (2.1), after which only clocks $5,6,7$ remain and Theorem 2.1 defeats every continuation. This conclusion is conditional on reaching that literal preceding history. It does not close its fourth-$J$ subtree or the entire initial-$J$ alternative. ∎

## 3. 初始 MJ 一侧及 JMJMJ 的末两步边界

**定理 3.1（MJMJ 的参数失败族）。** Let $0<\varepsilon<1/6$, $\lambda\ne0$ and $\delta\in\mathbb R$. The unrestricted fiber of

$$
H_{MJ}=(\delta-21\lambda,M,\delta,J,\delta+5\lambda(1+\varepsilon),
M,\delta,J,\delta-9\lambda(1+2\varepsilon))
\tag{3.1}
$$

has $L_3$.

Proof. Put

$$
d_0=\tfrac12,\quad d_1=\tfrac12+3\varepsilon,\quad d_2=\tfrac12+2\varepsilon,
\qquad
P_d=\begin{pmatrix}1-d&d(1-d)/\varepsilon\\\varepsilon&d\end{pmatrix}.
\tag{3.2}
$$

All three $d$ are distinct and in $(0,1)$. These matrices are positive, trace one and determinant zero. Give them the same gain $g(t)=\lambda(t-1)(t-3)(t-7)$ and the same drift $\delta$.

Write $U=JM=(\begin{smallmatrix}1&1\\0&1\end{smallmatrix})$. Through $MJMJ$ the cumulative matrices are $I,M,U,MU,U^2$ and the gain samples are $\lambda(-21,0,5,0,-9)$. Since $\operatorname{tr}(UP_d)=1+\varepsilon$ and $\operatorname{tr}(U^2P_d)=1+2\varepsilon$, every target realizes the entire (3.1).

Define $f_k(d)=d(1-d)/\varepsilon+\varepsilon+kd$. At clock five, action $M$ has trace $f_3(d)$ and action $J$ has trace $f_2(d)$; $g(5)=-16\lambda$. For $d\ne d'$,

$$
f_k(d)-f_k(d')=(d-d')\left(\frac{1-d-d'}\varepsilon+k\right).
\tag{3.3}
$$

Consequently $f_3(d_0)=f_3(d_1)$ and $f_2(d_0)=f_2(d_2)$. The selected fifth-$M$ child contains $\{d_0,d_1\}$ at read

$$
m=\delta-16\lambda\left(\frac1{4\varepsilon}+\varepsilon+\frac32\right),
$$

and the selected fifth-$J$ child contains $\{d_0,d_2\}$ at read

$$
j=\delta-16\lambda\left(\frac1{4\varepsilon}+\varepsilon+1\right).
$$

All sixth traces on those respective pairs are given by

| Fifth and sixth actions | Sixth trace on its retained pair |
| --- | --- |
| $MM$ | $f_3(d)+1+2\varepsilon$ |
| $MJ$ | $1+3\varepsilon$ |
| $JM$ | $f_2(d)+1+\varepsilon$ |
| $JJ$ | $1+2\varepsilon$ |

Multiplication by $g(6)=-15\lambda$ and addition of $\delta$ give the actual sixth reads. Each displayed pair shares both possible sixth reads. Every seventh action reads $\delta$, because $g(7)=0$. Thus each selected fifth child has $L_2$, while the parent already contains three distinct targets. This proves $L_3$ with all stops included. The two fifth children use different pairs of the same three fixed worlds; a common fifth response on the whole triple is neither asserted nor needed. ∎

**推论 3.2（MJM 历史上的条件强制）。** A correct at-most-eight-read full-domain protocol reaching the history (3.1) without its last action and read must take fourth action $M$.

Proof. Stopping fails on the three targets, and fourth $J$ enters Theorem 3.1. The fourth-$M$ subtree remains a separate obligation. For instance $\varepsilon=1/12,\lambda=1,\delta=0$ gives the literal losing parent $(-21,M,0,J,65/12,M,0,J,-21/2)$; its selected fifth reads are $-220/3,-196/3$, and its selected sixth reads at $MM,MJ,JM,JJ$ are respectively $-345/4,-75/4,-155/2,-35/2$. All final reads are zero. ∎

**命题 3.3（JMJMJ 的完整两步边界）。** With $\lambda\ne0$, the targets with common gain $g(t)=\lambda(t-1)(t-3)(t-7)$, common drift $\delta$, and sources

$$
P_1=\begin{pmatrix}1/2&1/6\\3/2&1/2\end{pmatrix},\qquad
P_2=\begin{pmatrix}5/6&1/6\\5/6&1/6\end{pmatrix}
\tag{3.4}
$$

give $L_2$ at the entire history

$$
(\delta-21\lambda,J,\delta,M,\delta+35\lambda/6,
J,\delta,M,\delta-12\lambda,J,\delta-128\lambda/3).
\tag{3.5}
$$

Proof. Both sources are strictly positive, rank one, trace one and distinct. Direct multiplication along $JMJMJ$ gives the six reads in (3.5) for each source. Sixth $M$ reads $\delta-45\lambda/2$ in both worlds; sixth $J$ reads $\delta-20\lambda$ in both. All seventh reads are $\delta$. Thus the same pair covers both sixth actions, both final actions and stopping. At the preceding $JMJM$ history a correct full-domain eight-read protocol must choose fifth $M$. In particular a policy taking the fifth $J$ there cannot be extended to the full cubic domain merely by changing its sixth and seventh choices. This does not settle the complementary fifth-$M$ subtree. ∎

## 4. 指定 MMJM 父历史的共同坐标

**约定 4.1（原有坐标接口）。** In the rest of the local joint analysis fix the single literal parent

$$
H_4(Y)=(0,M,1,M,23/7,J,331/35,M,Y),\quad
B=JM^2=\begin{pmatrix}1&2\\1&1\end{pmatrix},\quad
D=MB=\begin{pmatrix}1&1\\2&3\end{pmatrix}.
\tag{4.1}
$$

Use II, Definitions 69.1–69.2: with $\eta=(DP)_{22}>0$, $R=P/\eta$ and $H=\eta g$,

$$
DR=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
R=\begin{pmatrix}(3x-1)y&3x-1\\(1-2x)y&1-2x\end{pmatrix},
\quad \frac13<x<\frac12,\quad y>0.
\tag{4.2}
$$

Put $s=x+y,p=xy$. The five parent trace factors are

$$
(T_0,T_1,T_2,T_3,T_4)
=(3p+1-s-x,\ s-2p,\ p+1-x,\ s-p,\ p+1).
\tag{4.3}
$$

All are positive. The entire parent requires

$$
H(i)T_i+\delta=h_i\quad(0\le i\le4),\qquad
h=(0,1,23/7,331/35,Y).
\tag{4.4}
$$

Let $\mathcal F(Y;m,j)$ be the joint fiber with fifth-$M$ response $m$ and fifth-$J$ response $j$. These are promise data about fixed worlds. Set $\kappa=m-j$. Then

$$
H(5)=\kappa,\qquad \delta=j-\kappa s.
\tag{4.5}
$$

The coordinates $(x,y)$ own the complete target within this fiber: they determine $R,\delta$ and the four values $H(i)=(h_i-\delta)/T_i$ for $i=0,1,2,3$, which determine the entire cubic-or-lower polynomial. The remaining equalities, including the same $Y$, are still required. No gain sample is divided out.

Write $v=H(6)$ and name the four sixth responses

$$
a=JJ=\delta+v(p+1),\quad b=JM=a+vx,\quad
c=MJ=a+vy,\quad d=MM=c+v(x+1).
\tag{4.6}
$$

Here $d$ is a response name and is never the drift. When $\kappa\ne0$, put $r=H(7)/\kappa$. The two final traces, ordered final $M,J$, are

| Sixth node | Final trace pair |
| --- | --- |
| $a=JJ$ | $(s+1,s)$ |
| $b=JM$ | $(p+2x+y+1,p+s)$ |
| $c=MJ$ | $(s+2,s+1)$ |
| $d=MM$ | $(p+2s+3,p+x+2y+1)$ |

For each listed trace $T$, the actual read is $\delta+\kappa rT$. These formulas follow from left multiplication on $DR$; each of the displayed nodes still consists of individual actions with immediate reads.

**约定 4.2（三目标消费者的继承条件）。** II, Theorem 73.1 applies to exactly three distinct targets already in one $\mathcal F(Y;m,j)$ with $\kappa\ne0$. Its necessary pattern for $L_3$ labels the targets so that

$$
r_1=r_2=1,\quad r_3\ne1,\quad
\delta_1\ne\delta_2,\quad a_1=a_2,\quad c_1=c_2,
\quad \frac89<r_3<\frac98.
\tag{4.7}
$$

If $d$ is nonconstant, that theorem gives $14/15<r_3<15/14$. Its proof uses II, Theorem 70.1 and Lemmas 71.1, 71.3, together with the matching interface of Theorem 72.1. Those results and II's root-five decoder are reused with their stated whole-family promises. No hypothesis that an arbitrary triple has common fifth responses is inserted into them. Sections 5–8 concern the exact joint fiber just defined; Sections 2–3 and 9–10 have the broader domains explicitly stated there.

## 5. 异漂移同端点对的来源与次数排除

**定义 5.1（所需例外对）。** A required pair consists of two targets in the same entire $\mathcal F(Y;m,j)$, $\kappa\ne0$, such that

$$
H_1(5)=H_2(5)=H_1(7)=H_2(7)=\kappa,\qquad
\delta_1\ne\delta_2,\qquad a_1=a_2,\quad c_1=c_2.
\tag{5.1}
$$

This is the pair appearing in (4.7). Neither $v_i=H_i(6)$ can vanish: $v_1y_1=v_2y_2$ would then force both to vanish, and the common $a$ would give equal drifts. A common original left source factor is equivalent to common $x$, since $D$ is invertible; a common right factor is equivalent to common $y$.

**定理 5.2（两个因子与两个二次增益均不足）。** Every required pair satisfies $x_1\ne x_2$, $y_1\ne y_2$; its two gains are linearly independent, and at least one has degree exactly three. The factor and two-quadratic exclusions already follow from common parent reads with action word $MMJM$; their proofs do not use the numerical values in (4.1).

Proof. Put

$$
Q(t)=(t-5)(t-7),\qquad C(t)=(t-5)(t-6)(t-7),\qquad K_i=H_i/\kappa.
\tag{5.2}
$$

First suppose $x_1=x_2=x$. Distinctness forces $y_1\ne y_2$. Define

$$
F=\frac{K_1-K_2}{y_1-y_2},\qquad
V=\frac{y_1K_1-y_2K_2}{y_1-y_2}.
$$

The common $c-a$ gives $V(6)=0$; the common $a$, using $\delta_1-\delta_2=-\kappa(y_1-y_2)$, gives $F(6)=1$. At $5,7$, $F=0,V=1$. Interpolation therefore gives

$$
F=-Q+\beta C,\qquad V=(t-6)^2+\alpha C.
\tag{5.3}
$$

Write the parent factors as $A_i y+B_i$, where

$$
A=(3x-1,1-2x,x,1-x,x),\qquad B=(1-2x,x,1-x,x,1).
$$

Equality of every parent read is exactly $A_iV(i)+B_iF(i)=1$. The equations at $3,4$ give, with $D_x=x^2+x-1$,

$$
\alpha=\frac{16x^2+x-8}{24D_x},\qquad
\beta=\frac{-x^2-24x+16}{24D_x}.
\tag{5.4}
$$

Here $D_x<0$ on $(1/3,1/2)$. Substitution at clock one gives $(91x^3-67x+16)/D_x=0$. For $x=1/3+z$, $0<z<1/6$, its numerator is

$$
-\frac{80}{27}-\frac{110}{3}z+91z^2+91z^3
\le-\frac{80}{27}-\frac{683}{36}z<0,
$$

using $z^2\le z/6,z^3\le z/36$. This is impossible.

Next suppose $y_1=y_2=y$, so $x_1\ne x_2$. The common $c-a$ gives $K_1(6)=K_2(6)$; the common $a$ makes that value $1/y$. Now define $F=(K_1-K_2)/(x_1-x_2)$ and $V=(x_1K_1-x_2K_2)/(x_1-x_2)$. Then

$$
F=\beta C,\qquad V=1+(1-1/y)Q+\alpha C.
\tag{5.5}
$$

The parent factors are $A_ix+B_i$ with

$$
A=(3y-2,1-2y,y-1,1-y,y),\qquad B=(1-y,y,1,y,1),
$$

and again $A_iV(i)+B_iF(i)=1$. Put $D_y=y^2+y-1$. If $D_y\ne0$, the equations at $3,4$ give

$$
\alpha=\frac{16y^3-7y^2-16y+8}{24yD_y},\qquad
\beta=\frac{7y^2-16y+8}{24D_y}.
\tag{5.6}
$$

If $D_y=0$, the same two linear equations require $7y^2-16y+8=0$, hence $23y-15=0$. But $D_y(15/23)=41/529\ne0$, so this singular case has no solution. In the nonsingular case, the residuals $y[A_iV(i)+B_iF(i)-1]$ at $0,1,2$ are $-P_0/(4D_y),P_1/D_y,-P_2/(2D_y)$, where

$$
\begin{aligned}
P_0&=1003y^4-770y^3-1166y^2+1248y-280,\\
P_1&=75y^4-48y^3-67y^2+64y-16,\\
P_2&=48y^4-48y^3-59y^2+66y-10.
\end{aligned}
$$

They cannot all vanish, by the exact identity

$$
(14872431+34476357y)P_0-(280185985+119533109y)P_1
+(26902153-533641727y)P_2=49673550.
\tag{5.7}
$$

Thus neither source factor can be common. Proportional gains would make $H_1=H_2$, because their fifth samples are the same nonzero $\kappa$. Their common nonzero sixth sample and $v_1y_1=v_2y_2$ would then give $y_1=y_2$, just excluded.

Finally set

$$
\ell=\frac{x_1-x_2}{y_1-y_2},\quad \mu=x_1-\ell y_1,\quad
\alpha=\mu+\ell(y_1+y_2),\quad \beta=-\ell y_1y_2,\quad L=1+\ell.
\tag{5.8}
$$

Then $x_i=\ell y_i+\mu$, $x_iy_i=\alpha y_i+\beta$. Unequal drifts force $L\ne0$. With the first definition of $F,V$, the common $a,c$ give $V(6)=0$ and $(1+\beta)F(6)=L$. Hence $1+\beta\ne0$ and

$$
V=(t-6)^2+uC,\qquad F=-\frac L{1+\beta}Q+wC.
\tag{5.9}
$$

If both gains were at most quadratic, $u=w=0$. Parent collision at clock four gives $\alpha=L$; at clock three it gives $\mu-\beta=-(\beta+1)/8$; clock one then gives $\beta=23,\mu=20$. Clock two gives $16-(5/2)L=L$, so $L=32/7$ and $\ell=25/7>0$. But $\beta=-\ell y_1y_2<0$, contradicting $\beta=23$. This argument covers lower degrees as well. ∎

## 6. 例外对的完整父历史割线系统

**定理 6.1（实际例外对的充要代数系统）。** A required pair exists at some literal $Y$ if and only if the following six-real-parameter system is feasible. The system makes no assertion of feasibility.

Choose $(\ell,\mu,\alpha,\beta,u,w)\in\mathbb R^6$ with $\ell\ne0$, $L=1+\ell\ne0$, $1+\beta\ne0$. Set

$$
S=\frac{\alpha-\mu}{\ell},\quad N=-\frac\beta\ell,
\qquad S>0,\quad N>0,\quad S^2-4N>0.
\tag{6.1}
$$

Let $y_1,y_2$ be the distinct positive roots of $z^2-Sz+N$, put $x_i=\ell y_i+\mu$, and require $1/3<x_i<1/2$ for both roots. Define

$$
\begin{aligned}
q&=L/(1+\beta),&V(t)&=(t-6)^2+uC(t),&F(t)&=-qQ(t)+wC(t),\\
A&=(3\alpha-2\ell-1,L-2\alpha,\alpha-\ell,L-\alpha,\alpha),\\
B&=(3\beta+1-2\mu,\mu-2\beta,\beta+1-\mu,\mu-\beta,\beta+1).
\end{aligned}
\tag{6.2}
$$

Require all five joint equations

$$
A_iV(i)+B_iF(i)=L\qquad(0\le i\le4).
\tag{6.3}
$$

Put $w_i=B_iV(i)-(A_iN+B_iS)F(i)-\mu$, $d_w=w_1-w_0$, and require

$$
d_w\ne0,\qquad 7(w_2-w_0)=23d_w,\qquad
35(w_3-w_0)=331d_w.
\tag{6.4}
$$

The corresponding numerical data and pair are

$$
\begin{gathered}
\kappa=1/d_w,\quad j=-\kappa w_0,\quad m=j+\kappa,
\quad Y=\kappa(w_4-w_0),\\
H_1=\kappa(V-y_2F),\quad H_2=\kappa(V-y_1F),\quad
\delta_i=j-\kappa(x_i+y_i),
\end{gathered}
\tag{6.5}
$$

with $R_i$ from (4.2) and targets from (1.2).

Proof. Given a required pair, Theorem 5.2 permits (5.8) and the two positive roots in (6.1). Reducing $y_i^2=Sy_i-N$ gives exactly $T_{i,k}=A_k y_i+B_k$. The definitions of $F,V$ in the preceding proof reconstruct $K_1=V-y_2F,K_2=V-y_1F$ and give (6.2). Subtracting the two parent reads, and dividing by the nonzero $\kappa(y_1-y_2)$, gives (6.3). Expanding either common read, the coefficient of $y_i$ cancels by (6.3), leaving $j+\kappa w_k$. The differences between the first four prescribed reads are exactly (6.4), and their scale fixes (6.5).

Conversely (6.1) and the bounds on both $x_i$ make the reconstructed sources legal and distinct. The same expansion shows every parent read is $j+\kappa w_k$, hence the common values are precisely $0,1,23/7,331/35,Y$. At $5,7$ one has $F=0,V=1$, so each $H_i$ is a nonzero polynomial of degree at most three with both samples $\kappa$. Equation (4.5) gives both fifth responses. At six,

$$
H_1(6)=-\kappa qy_2,\qquad H_2(6)=-\kappa qy_1,
$$

so $H_1(6)y_1=H_2(6)y_2=-\kappa qN\ne0$. Their $a$ difference is

$$
\kappa(y_1-y_2)[(1+\beta)q-L]=0.
$$

Thus both $a,c$ coincide, while $\delta_1-\delta_2=-\kappa L(y_1-y_2)\ne0$. Formula (1.2) preserves these statements for the complete normalized targets. This proves both directions without choosing a gain sign or deleting a root stratum. A solution gives only this pair; the third target and the other losing children are additional joint obligations. ∎

## 7. 三目标的恒定 JM 与 MM 联合排除

**定理 7.1（恒定第六 M 响应不能完成例外对）。** Let $\mathcal K=\{W_1,W_2,W_3\}$ consist of three distinct targets in one entire $\mathcal F(Y;m,j)$, $\kappa\ne0$. Suppose $W_1,W_2$ form a required pair and $r_3\ne1$. If either $b$ or $d$ is constant on all of $\mathcal K$, then $L_3(\mathcal K,H_4(Y))$ is false. The same conclusion allows $a$ or $c$ to be constant and allows different terminal collisions at a constant sixth node.

Proof. Assume $L_3$. The common $a,c$ give $v_1y_1=v_2y_2\ne0$. If $b$ is constant, also $v_1x_1=v_2x_2$. Thus for some $\lambda>0$,

$$
x_1=\lambda x_2,\quad y_1=\lambda y_2,\quad v_2=\lambda v_1,
\qquad \frac23<\lambda<\frac32,\quad\lambda\ne1.
\tag{7.1}
$$

The exclusion $\lambda\ne1$ follows from complete-target ownership. Here $d_1-d_2=v_1-v_2\ne0$, so $d$ is nonconstant. If instead $d$ is constant, the corresponding relations are

$$
x_1+1=\lambda(x_2+1),\quad y_1=\lambda y_2,\quad v_2=\lambda v_1,
\qquad \frac89<\lambda<\frac98,\quad\lambda\ne1,
\tag{7.2}
$$

and $b_1-b_2=-(v_1-v_2)\ne0$.

Call a pair bad at a sixth node when it shares that node's read and both possible final reads. At the nonconstant sixth node every actual child has at most two targets, so $L_3$ requires a bad pair there. The pair $\{1,2\}$ cannot be bad at $b$ or $d$: at $r=1$, the final values after subtracting $j$ and dividing by $\kappa$ are

$$
b:(p+x+1,p),\qquad d:(p+s+3,p+y+1).
\tag{7.3}
$$

Either ordered pair determines $x,y$ and hence the complete target. Relabel $1,2$ so the bad pair at the nonconstant node is $\{1,3\}$. Its final-response difference forces $r=r_3>0$. It cannot be bad also at the other node: the two difference equalities would give

$$
x_1+1=r(x_3+1),\qquad x_1+2=r(x_3+2),
$$

and hence $r=1$, contrary to the assumption.

At the constant node, $L_1$ requires a collision for each final action on the whole triple. The values of targets $1,2$ under each such final action are different. For constant $b$ this follows from (7.1) and (7.3), since $p$ scales by $\lambda^2$ and $p+x$ is strictly increasing with $\lambda>0$. For constant $d$, $p+y=(x+1)y$ scales by $\lambda^2$, and $p+s=(x+1)y+x$ is strictly increasing with $\lambda$. Thus both collisions involve target $3$.

Write an assignment $(h,k)$ when target $3$ matches target $h$ under final $M$ and target $k$ under final $J$ at the constant node. Assignment $(1,1)$ has just been excluded. It remains to exclude $(1,2),(2,1),(2,2)$ in each constant-node case, retaining both crossed assignments.

For a single common compatibility equation, set $x_2=x,y_2=y$, $p_i=x_iy_i,s_i=x_i+y_i$ and

$$
\begin{aligned}
A&=p_1+1-\lambda(p_2+1),\\
C_*&=(y_3+1)(p_1+x_1+1)-(y_1+1)(p_3+x_3+1),\\
E&=(s_1-s_2)C_*-(s_1-s_3)(y_3+1)A.
\end{aligned}
\tag{7.4}
$$

The mixed bad pair and the constant response give both $b_1=b_3$ and $d_1=d_3$, so $v_1(y_1+1)=v_3(y_3+1)$. Also $a_1=a_2$ gives $v_1A=\kappa(s_1-s_2)$. Substitution into $b_1=b_3$ gives $E=0$. This implication does not divide by $A$, a drift difference, or any possibly zero sixth sample of target $3$.

First let $b$ be constant. Then $x_1=\lambda x,y_1=\lambda y$, and the mixed bad pair at $d$ gives

$$
x_3=(\lambda x+2)/r-2,\qquad \Delta_p=(\lambda^2-1)xy.
\tag{7.5}
$$

For assignment $(1,2)$ the final equations give

$$
r=1-\Delta_p,\qquad y_3=(\lambda y+2\Delta_p)/r,
$$

and the remaining final equation requires

$$
xy(\lambda-1)(\lambda+1)(\lambda x+\lambda y+xy+1)=0.
$$

Every factor except $\lambda-1$ is positive, and $\lambda\ne1$.

For assignment $(2,1)$ the final equations give

$$
\begin{gathered}
r=1+(\lambda-1)x+\Delta_p,\qquad y_3=(\lambda y+1)/r-1,\\
D_*=\lambda+(2\lambda^2-1)x,\qquad D_*y=x(1-\lambda).
\end{gathered}
\tag{7.6}
$$

Since $D_*>\lambda-x>1/6$, positivity of $y$ forces $2/3<\lambda<1$. Put $N_*=D_*r\ne0$. Substitution in (7.4) yields

$$
E=\frac{\lambda x(\lambda-1)^2(\lambda x+1)
(\lambda^2x+\lambda x+\lambda-x)H_5(\lambda,x)}{D_*^2N_*^2}>0.
\tag{7.7}
$$

The polynomial $H_5$ and its positive coefficients are given below. The remaining factor is positive because $\lambda^2+\lambda-1>0$ for $\lambda>2/3$. This contradicts $E=0$.

For assignment $(2,2)$ the final equations give

$$
\begin{gathered}
r=1+(\lambda-1)x,\quad y=\frac{x(\lambda-1)}{\lambda x+1},\quad
x_3=\frac{x(2-\lambda)}r,\\
y_3=\frac{x(\lambda-1)Q_*}{(\lambda x+1)r},\qquad
Q_*=(\lambda-1)(\lambda x+1)-x.
\end{gathered}
\tag{7.8}
$$

Now $y>0$ forces $\lambda>1$. The bounds $x_3>1/3$ and $\lambda x<1/2$ imply

$$
\lambda-1<\frac{3x-1}{4x},\qquad
Q_*<-\frac{8x^2-9x+3}{8x}<0.
$$

The last quadratic is positive everywhere, since its leading coefficient is positive and its discriminant is $-15$. Thus $y_3<0$, impossible. This exhausts constant $b$.

Next let $d$ be constant. Write $x_1=\lambda(x+1)-1,y_1=\lambda y$, $\Delta_x=x_1-x$, $\Delta_y=y_1-y$, $\Delta_p=p_1-p_2$. The mixed bad pair at $b$ gives

$$
x_3=(x_1+1)/r-1.
\tag{7.9}
$$

For assignment $(1,2)$ the final equations give

$$
\begin{gathered}
r=1+\Delta_p+\Delta_y,\qquad y_3=(1+y-\Delta_p)/r-1,\\
y[(2\lambda^2-1)(x+1)-\lambda]+\lambda(x+1)-1=0.
\end{gathered}
\tag{7.10}
$$

Put $z=x+1,u=\lambda z=x_1+1$, both in $(4/3,3/2)$. Then

$$
y=\frac{z(1-u)}{2u^2-u-z^2},\qquad
r=\frac{-u^3+3u^2-u+(u-2)z^2}{2u^2-u-z^2}.
$$

Since $y>0$, the denominator is negative. The numerator of $r$ increases in $u$ and decreases in $z$ on the whole rectangle; its minimum at $(u,z)=(4/3,3/2)$ is $7/54>0$. Thus $r<0$, contradicting $r>0$.

For assignment $(2,1)$ the final equations give

$$
\begin{gathered}
r=1-\Delta_x-\Delta_p-\Delta_y,\qquad y_3=(\lambda y+1)/r-1,\\
xy+(1-\lambda)(x+y+1)=0.
\end{gathered}
\tag{7.11}
$$

Hence $\lambda>1$, and with $D_*=x+1-\lambda>5/24$,

$$
y=\frac{(\lambda-1)(x+1)}{D_*},\quad N_*=-D_*r\ne0,\quad
F_*=(x+1)(\lambda-1)^2+\lambda x>0.
$$

Substitution gives

$$
E=-\frac{\lambda(\lambda-1)^2(x+1)x_1F_*Q_3(\lambda,x)}{D_*^2N_*^2}<0,
\tag{7.12}
$$

where $Q_3>0$ on $1<\lambda<9/8$, $1/3<x<1/2$ by the coefficient bound below.

For assignment $(2,2)$ the equations give

$$
\begin{gathered}
r=1+(1-\lambda)(x+1),\qquad y=\frac{(1-\lambda)(x+1)}{x_1},\\
x_3=(x_1+1)/r-1,\qquad y_3=(p_2+y+1-p_1)/r-1.
\end{gathered}
\tag{7.13}
$$

Positivity forces $8/9<\lambda<1$. Substitution gives

$$
E=-\frac{(\lambda-1)^2(x+1)H_7(\lambda,x)}{x_1^3r^2}<0.
\tag{7.14}
$$

Again this contradicts $E=0$. All assignments at both constant nodes are excluded. ∎

**定义 7.2（完整正系数恒等式）。** Write $B_{i,n}(w)=\binom niw^i(1-w)^{n-i}$. The polynomials in the preceding proof are defined by

$$
H_5(\lambda,x)=\sum_{i=0}^5\beta_i(x)B_{i,5}(3\lambda-2),
\qquad
H_7(\lambda,x)=\sum_{i=0}^7\gamma_i(x)B_{i,7}(9\lambda-8).
\tag{7.15}
$$

The complete coefficient lists, in increasing index, are

$$
\begin{aligned}
\beta_0&=(-2x^4+11x^3+96x^2+162x+324)/243,\\
\beta_1&=(-3x^4+65x^3+311x^2+603x+648)/405,\\
\beta_2&=(11x^4+128x^3+414x^2+699x+513)/270,\\
\beta_3&=(16x^4+99x^3+257x^2+361x+201)/90,\\
\beta_4&=(x+1)(7x^3+26x^2+48x+39)/15,\\
\beta_5&=(x+1)^2(x^2+2x+3),
\end{aligned}
\tag{7.16}
$$

and

$$
\begin{aligned}
\gamma_0&=(78336x^6+3365576x^5+6418912x^4+6365249x^3
-1364644x^2+188284x+3536)/4782969,\\
\gamma_1&=(47296x^6+2718705x^5+5211188x^4+5184328x^3
-969789x^2+107015x+1266)/3720087,\\
\gamma_2&=(11416x^6+944123x^5+1819895x^4+1814864x^3
-287917x^2+24587x+151)/1240029,\\
\gamma_3&=(1377x^6+182821x^5+354607x^4+354189x^3
-45758x^2+2857x+6)/229635,\\
\gamma_4&=x(83x^5+21333x^4+41661x^3+41648x^2-4110x+168)/25515,\\
\gamma_5&=x(2x^5+1501x^4+2953x^3+2953x^2-198x+4)/1701,\\
\gamma_6&=x^2(59x^3+117x^2+117x-4)/63,\\
\gamma_7&=x^3(x^2+2x+2).
\end{aligned}
\tag{7.17}
$$

Expanding (7.15) with these lists gives the exact identities (7.7), (7.14). On $1/3\le x\le1/2$, every $\beta_i$ is positive: the only negative monomials, $-2x^4,-3x^4$, are smaller in magnitude than their respective positive constant terms. Thus $H_5>0$ for $2/3\le\lambda\le1$, since the Bernstein terms are nonnegative and sum to one.

For $x\ge1/3$, all $\gamma_i$ are positive. In the first four, absorb each negative $x^2$ term into the positive $x^3$ term, using

$$
6365249/3>1364644,\quad 5184328/3>969789,\quad
1814864/3>287917,\quad354189/3>45758.
$$

For $\gamma_4,\gamma_5$ use $41648/3>4110$ and $2953/3>198$; for $\gamma_6$ use $117x-4>0$. The remaining terms are positive. Hence $H_7>0$ for $8/9\le\lambda\le1$, $x\ge1/3$.

Finally, putting $t=\lambda-1$,

$$
\begin{aligned}
Q_3={}&(x^4+3x^3+4x^2+3x+1)t^3+(2x^4+3x^3+2)t^2\\
&+(2x^4+3x^3-x^2-4x)t+x^4+2x^3+2x^2.
\end{aligned}
\tag{7.18}
$$

For $0\le t\le1/8$ and $x\ge1/3$,

$$
Q_3\ge x\left(x^3+2x^2+\frac{15}8x-\frac12\right)>0.
$$

The bracket is increasing for $x>0$ and equals $83/216$ at $1/3$. These coefficient identities prove the signs on full intervals, including all possible degree drops in the terminal equations.

**推论 7.3（已知三目标的实际策略与稀疏必要形）。** Under Theorem 7.1's hypotheses the entire known triple has a strategy with at most three further reads. Moreover, any $L_3$ triple in a joint fifth fiber with $\kappa\ne0$ has both $b,d$ nonconstant. It can be labeled so that the bad pairs are $d:\{1,3\}$ and $b:\{2,3\}$, and, with $x=x_3,y=y_3,e=r_3-1$,

$$
\begin{gathered}
x_1=x+e(x+2),\qquad x_2=x+e(x+1),\\
y_1=y+\frac{e(x+1)}{x_1+1},\qquad
y_2=y+\frac{ex}{x_2},\qquad
-\frac1{15}<e<\frac1{14},\quad e\ne0.
\end{gathered}
\tag{7.19}
$$

Proof. If $b$ is constant, examine the nonconstant node $d$. If it has no bad pair, execute fifth $M$, read, execute sixth $M$, read, and at each nonsingleton child choose a final atom separating its pair; stop at singleton children. If $d$ has a bad pair, the proof of Theorem 7.1 implies that one final response at the constant $b$ node is injective on the entire triple. Execute $J,M$ and that final atom, reading after each. For constant $d$, interchange the two nodes in this rule. These predictions use the known triple, not acquired counterfactual readings.

For an $L_3$ triple, apply the inherited necessity (4.7) and Theorem 7.1. Both nonconstant nodes need mixed bad pairs. The same mixed pair cannot work at both nodes, by the two difference equations in the proof. Relabeling gives the two displayed pairs. Their final differences give the formulas for $x_1,x_2$; their final-$J$ equalities then give $y_1,y_2$. The sharper ratio bound in (4.7) applies since $d$ is nonconstant. All source inequalities and all parent equations remain necessary in addition to (7.19). No sufficiency is asserted. ∎

## 8. 混合第六根的联合结式排除

**定理 8.1（共同第五三目标的第六增益非零）。** Let exactly three distinct targets lie in the same entire $\mathcal F(Y;m,j)$, with $\kappa=m-j\ne0$. If this triple has $L_3$, then each target has $g(6)\ne0$.

Proof. Use the inherited pattern (4.7). Put $\nu=c_1-a_1=c_2-a_2=v_1y_1=v_2y_2$. This is nonzero, as noted in Definition 5.1, so only target $3$ could have $v_3=0$. Suppose it does. Theorem 7.1 excludes constant $b$ or $d$ without assuming anything about $a,c$. Alternatively, in this zero-sixth case the exclusion is direct: if $b$ is constant at $B_0=\delta_3$, then $x_1/y_1=x_2/y_2$ and $y_1\ne y_2$. Consequently

$$
d_i=B_0+\nu(1+1/y_i)\ (i=1,2),\qquad d_3=B_0
$$

are pairwise distinct. If $d$ is constant at $D_0=\delta_3$, the values $b_i=D_0-\nu(1+1/y_i)$ and $b_3=D_0$ are pairwise distinct instead. Either case identifies the entire triple by clock six and contradicts $L_3$.

We may therefore use (7.19). The $d$ collision for $1,3$ and the $b$ collision for $2,3$ give

$$
v_1(p_1+s_1+2)=\kappa(s_1-s_3),\qquad
v_2(p_2+x_2+1)=\kappa(s_2-s_3).
\tag{8.1}
$$

Subtracting the common-$a$ equality from their difference, and using $v_iy_i=\nu\ne0$, gives

$$
y_2(s_1+1)-x_2y_1=0.
\tag{8.2}
$$

Eliminating the common ratio $\nu/\kappa$ from (8.1) without dividing by $s_i-s_3$ also gives

$$
(s_1-s_3)y_1(p_2+x_2+1)-(s_2-s_3)y_2(p_1+s_1+2)=0.
\tag{8.3}
$$

Here all three worlds and both sixth collisions are simultaneous.

For the explicit elimination set

$$
\begin{aligned}
B_*&=x+e(x+1)=x_2,& C_*&=x+e(x+2)+1=x_1+1,\\
L_1&=C_*y+e(x+1),&L_2&=B_*y+ex,\\
A_1&=(x+2)C_*+x+1,&A_2&=(x+1)B_*+x.
\end{aligned}
\tag{8.4}
$$

Both $B_*,C_*$ are positive, $y_1=L_1/C_*$ and $y_2=L_2/B_*$. Define the two quadratics in $y$

$$
\begin{aligned}
f(y)&=L_2(C_*^2+L_1)-B_*^2L_1,\\
g(y)&=B_*^2A_1L_1(B_*y+ex+B_*+1)\\
&\qquad-C_*^2A_2L_2(C_*y+e(x+1)+C_*+1).
\end{aligned}
\tag{8.5}
$$

Their precise denominator clearings are

$$
\begin{aligned}
f&=B_*C_*[y_2(s_1+1)-B_*y_1],\\
eg&=B_*^2C_*^2[(s_1-s_3)y_1(p_2+B_*+1)
-(s_2-s_3)y_2(p_1+s_1+2)].
\end{aligned}
\tag{8.6}
$$

Since $e\ne0$, equations (8.2)–(8.3) imply $f=g=0$. The $4\times4$ Sylvester determinant of (8.5) is the polynomial identity

$$
\operatorname{Res}_y(f,g)
=-e^2(e+1)^2B_*^3C_*^3Q(e,x).
\tag{8.7}
$$

The following complete array $(C_{ij})_{0\le i\le5,\,0\le j\le6}$ defines its remaining factor by

$$
Q(e,x)=\sum_{i=0}^5\sum_{j=0}^6 C_{ij}
(e+1/15)^i(x-1/3)^j.
\tag{8.8}
$$

Each row below lists increasing $j$:

$$
\begin{aligned}
C_{0,\bullet}={}&(108146563/553584375,\ 16698349/6834375,\ 40306619/4100625,\\
&64251628/4100625,\ 9014404/759375,\ 133084/30375,\ 496468/759375),\\
C_{1,\bullet}={}&(46709666/7381125,\ 13573646/273375,\ 35337842/273375,\\
&43256632/273375,\ 1023898/10125,\ 334964/10125,\ 44996/10125),\\
C_{2,\bullet}={}&(3729724/98415,\ 3841387/18225,\ 8283152/18225,\\
&8946697/18225,\ 12812/45,\ 57659/675,\ 281/27),\\
C_{3,\bullet}={}&(2752618/32805,\ 160823/405,\ 919852/1215,\\
&898112/1215,\ 17689/45,\ 4864/45,\ 538/45),\\
C_{4,\bullet}={}&(166177/2187,\ 27895/81,\ 49627/81,\ 45392/81,\ 836/3,\ 214/3,\ 22/3),\\
C_{5,\bullet}={}&(18032/729,\ 2968/27,\ 5165/27,\ 4570/27,\ 81,\ 20,\ 2).
\end{aligned}
\tag{8.9}
$$

Expansion verifies (8.7); every coefficient in (8.9) is strictly positive. Since $e>-1/15$ and $x>1/3$, $Q(e,x)>0$. Also $e\ne0$, $e+1>14/15$, $B_*>1/3$ and $C_*>4/3$. Thus the resultant is strictly negative. A common real root of $f,g$ would make the Sylvester determinant zero, including a drop in either quadratic's degree. This contradicts (8.2)–(8.3), proving the assertion. ∎

**推论 8.2（三目标承诺的消费者与边界）。** In the joint fifth-response setting of Theorem 8.1, an $L_3$ triple has $g_i(5)g_i(6)g_i(7)\ne0$ for every target, both $b,d$ nonconstant, and at most one of $a,c$ constant. Its first two gains are linearly independent and at least one is cubic; the third gain is proportional to neither of them. A known triple in this setting containing a sixth root has an at-most-eight-total-read decoder.

Proof. Nonzero fifth and seventh samples and the third gain's different ratio are inherited from (4.7). Sixth nonvanishing is Theorem 8.1. The other restrictions follow from Theorems 5.2, 7.1 and II, Theorem 70.1. For the finite known triple, use backward recursion: a singleton node returns its target; at any other successful node choose an atom all of whose actual response children have successful remaining subtrees. The negation of $L_3$ ensures such choices, and only the actual selected atom is executed and read. This recovers the entire given triple, not an unrestricted fiber containing it. No common sign of all sixth gains is concluded. For a triple outside a common joint fifth fiber, these conclusions require additional hypotheses or a separate argument. ∎

## 9. 变响应整纤维的十六槽与原根二百五十六槽

**定义 9.1（零初读的完整多项式坐标）。** For

$$
\theta=(u,b,c,\delta,\beta_1,\beta_2,\beta_3)\in\mathbb R^7
$$

impose

$$
0<u<1,\quad b>0,\quad c>0,\quad bc=u(1-u),\qquad
\delta^2+\beta_1^2+\beta_2^2+\beta_3^2>0.
\tag{9.1}
$$

Set

$$
P_\theta=\begin{pmatrix}u&b\\c&1-u\end{pmatrix},\qquad
g_\theta(t)=-\delta+\beta_1t+\beta_2t^2+\beta_3t^3.
\tag{9.2}
$$

This is a bijection onto the entire initial-read-zero domain, denoted $\mathcal I_0$. In particular, initial read zero is not a zero-drift promise. For an integer matrix $A$, the original-clock response is the explicit degree-at-most-two polynomial

$$
O_i(A;\theta)=(-\delta+\beta_1i+\beta_2i^2+\beta_3i^3)
[A_{11}u+A_{12}c+A_{21}b+A_{22}(1-u)]+\delta.
\tag{9.3}
$$

For two slots define $\Delta(\theta,\theta')=\sum_{k=1}^7(\theta_k-\theta'_k)^2$. Its positivity means their complete targets differ.

**定理 9.2（同一实际 H4 的具体十六槽系统）。** Introduce a real $Y$, a response variable $z_v$ for each nonempty chronological word $v\in\{M,J\}^{\le3}$, and two slots $\theta_{w,0},\theta_{w,1}$ for each $w\in\{M,J\}^3$. For a nonempty prefix $v=E_1\cdots E_k$, let $A_v=E_k\cdots E_1D$. Impose the following simultaneous conditions:

1. Every slot satisfies (9.1), and each leaf pair has $\Delta(\theta_{w,0},\theta_{w,1})>0$.
2. Every slot satisfies

$$
O_1(M)=1,\quad O_2(M^2)=23/7,\quad O_3(B)=331/35,\quad O_4(D)=Y.
\tag{9.4}
$$

3. For each slot below a leaf $w$, and each nonempty prefix $v$ of $w$, require

$$
O_{4+|v|}(A_v;\theta_{w,\epsilon})=z_v\qquad(\epsilon=0,1).
\tag{9.5}
$$

Existential satisfaction of this rational polynomial system is equivalent to

$$
\exists Y\in\mathbb R:\quad L_3(\mathcal F(H_4(Y)),H_4(Y)).
\tag{9.6}
$$

There are $16\cdot7+14+1=127$ real coordinates and all constraints have total degree at most two after clearing fixed rational denominators. The sixteen slots need not represent sixteen distinct targets; no distinctness between different leaves is required.

Proof. Given a solution, take the union of its leaf pairs. At a prefix use the single response $z_v$ required of every descendant slot. Both action extensions have their specified descendant subfamilies, and each leaf contains a distinct pair. Induction upward therefore gives $L_3$ for this union and then for the unrestricted parent fiber. Every internal selected child contains a descendant distinct pair, so stopping there also fails.

Conversely unfold (1.3) three times and choose a distinct pair in each terminal child. Each chosen target is a fixed world already satisfying all its ancestor equalities. Use the selected actual response at each prefix as $z_v$. The target parametrization gives all slots and all equations (9.4)–(9.5). No independent terminal fitting is permitted by those shared prefix variables.

Equivalently, the elementary finite-horizon witness induction bounds a depth-$s$ binary failure certificate by $2^{s+1}$ fixed targets: two targets at depth zero; at greater depth take the union of certificates in one selected losing child for each action. Upward monotonicity preserves each child after taking the union. This standard finite-tree argument is used here only to explain the concrete slot bound, not as a distinct general result. Fifth responses need not be common across all sixteen slots; only descendants of the same chosen prefix share its actual response. The same holds for sixth responses. All cubic shapes, signs, roots and drifts remain in (9.1)–(9.5). ∎

**定理 9.3（原根全部动作与停止的具体系统）。** Use the same legal coordinates, but take two slots for each word $w\in\{M,J\}^7$, and one $z_v$ for each nonempty prefix of length at most seven. Starting at $A_\varnothing=I$, impose

$$
O_{|v|}(E_{|v|}\cdots E_1;\theta_{w,\epsilon})=z_v
\quad(v\text{ a nonempty prefix of }w),
\tag{9.7}
$$

together with legality and distinctness inside each leaf pair. This $256\cdot7+254=2046$ coordinate system is feasible if and only if there is no full-domain decoder with at most eight total reads.

Proof. The same unfolding proves equivalence to $L_7(\mathcal I_0,(0))$. It includes both first actions, both second actions after either first action, every later original-clock action and every stopping node.

For an arbitrary initial read $z_0$, the map

$$
(P,g,\delta)\longmapsto(P,g,\delta-z_0)
\tag{9.8}
$$

is a bijection from that entire initial fiber to $\mathcal I_0$. It subtracts $z_0$ from every subsequent read on every action word and preserves every original clock. A decoder on $\mathcal I_0$ therefore yields a full-domain decoder: subtract the actual initial $z_0$ from the history supplied to that decoder, follow its actions, and add $z_0$ back to its returned drift. The converse is restriction. Equation (1.3), with early stops included, now gives the stated equivalence. The system is not a certificate until its simultaneous equations and strict inequalities have a solution. ∎

**推论 9.4（实闭域工具在两个校准系统中的精确用途）。** If either of the rational systems in Theorems 9.2–9.3 is feasible over $\mathbb R$, it has a solution with all coordinates real algebraic. Their feasibility is decidable by real-closed-field quantifier elimination. If an arbitrary deterministic eight-read full-domain decoder exists, one can choose a semialgebraic decoder with the same budget. These conclusions supply neither an evaluated decision nor a feasible running-time bound for either system.

Proof. Apply quantifier elimination for real closed fields to the displayed finite formulas. The ordered field of real algebraic numbers is real closed, so a rational existential sentence holds there exactly when it holds over $\mathbb R$. In Theorem 9.2 this concerns existence over $Y$; it does not replace an already prescribed transcendental $Y$ by an algebraic value in the same literal history.

For the strategy assertion, fix each of the finitely many action words. Its compatible target relation is polynomial in the target and history coordinates. The assertion that two distinct compatible targets exist is first order, and (1.3) expresses every finite-depth losing-history region by first-order formulas. Quantifier elimination makes these regions semialgebraic. At a reachable nonlosing history, stop if the fiber is a singleton. Otherwise choose $M$ exactly when no $M$-child is losing for the remaining depth; if not, choose $J$. Nonloss ensures that the chosen atom has no losing reachable child. The unique-target answer relation at a stopping history is also semialgebraic, since it is precisely the compatible-target relation restricted to singleton fibers. Induction gives the strategy, and (9.8) transports it to all initial reads.

The general elimination theorem used here is Collins, *Quantifier Elimination for Real Closed Fields by Cylindrical Algebraic Decomposition*, §§1–3, especially the ordered-field formula definitions and the elimination construction. Its decision theorem applies to arbitrary finite formulas of this language; it gives no small resource bound for these particular dimensions. ∎

## 10. 完整三次域上的有限线性读出体系障碍

**定义 10.1（固定数据线性增益射线读出）。** For a chronological word $w$ of $N-1$ actions, $1\le N\le8$, let $Z_w(W)=(z_0,\ldots,z_{N-1})^{\mathsf T}$ and write $g(t)=\sum_{k=0}^3\beta_kt^k$, $\beta\ne0$. A fixed map $C:\mathbb R^N\to\mathbb R^4$ reads the gain ray on a set of inputs when $CZ_w(W)$ is a nonzero scalar multiple of $\beta$ on that set. The scalar may have either sign and may depend on the world.

A finite palette assigns finitely many such fixed real matrices to each possible terminal word. A deterministic protocol may choose its actions, stopping time and selected matrix from the actual history in any manner, without continuity or measurability assumptions. Only the final gain-ray readout is required to be linear in the data. Subsequent reconstruction may be arbitrary. A matrix whose coefficients depend on the observed data is outside this fixed-linear-map requirement.

**定理 10.2（有限线性读出不能给出完整八读协议）。** No correct protocol on all of $\mathcal W_3$ with at most eight total original-clock reads can, on every input, obtain a nonzero gain-ray readout by selecting from a finite palette.

Proof. First consider a fixed word containing both $M$ and $J$. We show that there are no fixed $C$ and nonzero linear functional $\ell$ on $\operatorname{Mat}_2(\mathbb R)$ such that

$$
CZ_w(P,g,\delta)=\ell(P)\beta
\quad\text{for every legal }P,\ \beta\ne0,\ \delta\in\mathbb R.
\tag{10.1}
$$

Let $V_{ik}=i^k$ for $0\le i<N,0\le k\le3$, and $a(S)=(\operatorname{tr}(A_iS))_i$. Varying the drift and coefficients in (10.1) gives

$$
C\mathbf1=0,\qquad C\operatorname{diag}(a(P))V=\ell(P)I_4.
\tag{10.2}
$$

Legal source matrices span all of $\operatorname{Mat}_2(\mathbb R)$: take two independent positive columns and two independent positive rows; their four outer products form a basis, and normalization by their positive traces preserves independence. Hence the second identity holds for every auxiliary matrix $S$. It is a linear identity, not an assertion that these auxiliary matrices are physical sources.

It forces $\operatorname{rank}C=4$. Write $\ell(S)=\operatorname{tr}(LS)$, $L\ne0$, and let $E=\ker\ell$. For $S\in E$, the image of $\operatorname{diag}(a(S))V$ lies in $\ker C$, as does $\mathbf1$. Set

$$
Q=\{i:A_i\text{ is proportional to }L\},\qquad q=|Q|.
$$

Choose $S\in E$ with $\operatorname{tr}(A_iS)\ne0$ for all $i\notin Q$. Such a choice exists: each prohibited zero is a proper linear hyperplane in $E$, and finitely many proper hyperplanes cannot cover it. At indices in $Q$ these traces are necessarily zero. Distinct original clocks make the image rank $\min(N-q,4)$ by polynomial evaluation.

If $q>0$, $\mathbf1$ is independent of this image, since every image vector vanishes on $Q$. Therefore

$$
N-4=\dim\ker C\ge\min(N-q,4)+1.
\tag{10.3}
$$

If $N-q\ge4$, this requires $N\ge9$. Otherwise it requires $q\ge5$. But adjacent cumulative matrices cannot be proportional: $A_{i+1}=cA_i$ would imply $E_{i+1}=cI$, and neither atom is scalar. Thus any one proportionality class occurs at most $\lceil N/2\rceil\le4$ times. Both alternatives contradict $N\le8$.

If $q=0$, the selected $S$ has every trace nonzero, so its image has rank four and $N-4\ge4$. Consequently $N=8$ and

$$
\ker C=\operatorname{diag}(a(S))\operatorname{range}V.
\tag{10.4}
$$

For every $T\in E$, the diagonal matrix with entries $\operatorname{tr}(A_iT)/\operatorname{tr}(A_iS)$ preserves $\operatorname{range}V$. Every diagonal matrix preserving cubic evaluation vectors at eight distinct nodes is scalar. Indeed take the monic cubic vanishing at any selected three nodes. Its diagonal image is the evaluation of a cubic vanishing at those same nodes and hence is the evaluation of a scalar multiple of the original cubic. The diagonal entries are therefore equal outside those three nodes. Given any two indices, choose the three nodes among the other six to see that their entries coincide. This includes a zero scalar.

It follows that the restricted trace functionals $\operatorname{tr}(A_i\,\cdot)|_E$ span at most one dimension. The kernel of restricting a linear functional to $E$ is $\operatorname{span}\{\ell\}$, so the unrestricted trace functionals, and hence the matrices $A_i$, span at most two dimensions.

Every mixed word instead has cumulative-matrix span at least three. If it starts with $M^k$ and first changes to $J$, then $I,M$ are present, while $JM^k$ is nonsymmetric: $M^k=F_{k-1}I+F_kM$, $F_k>0$, and its two off-diagonal entries differ by $F_k$. It is outside $\operatorname{span}\{I,M\}$. If the word starts with $J$'s and first changes to $M$, it contains $I,J$ and either $M$ or $MJ$; neither of the latter belongs to $\operatorname{span}\{I,J\}$. This contradiction proves the fixed-word assertion (10.1).

Next, a correct full-domain protocol cannot stop after using only one atom type, including no actions. For $A=M$ or $J$, all its powers lie in $\operatorname{span}\{I,A\}$. Every legal $P$ has a different legal $P'$ with $\operatorname{tr}(AP')=\operatorname{tr}(AP)$. To see this write $P=uv^{\mathsf T}$, $u,v>0$, $v^{\mathsf T}u=1$. If $u,Au$ are independent, vary $u$ slightly to a nonproportional positive $u'$ and solve

$$
(v')^{\mathsf T}u'=1,\qquad
(v')^{\mathsf T}Au'=\operatorname{tr}(AP).
$$

The unique solution is continuous near $u$ and remains positive there. If $Au=\lambda u$, keep $u$ and vary $v>0$ along $v^{\mathsf T}u=1$; the $A$ trace stays $\lambda$. In both cases $P'\ne P$. With the same $g,\delta$, all pure-word reads coincide. Determinism gives the same actions and stopping decision on both targets, so a common answer cannot be correct for both. With no actions, trace normalization alone makes the same argument immediate. Thus every actual terminal word of a correct full-domain protocol must contain both atoms.

It remains to justify the adaptive finite-palette conclusion, which does not follow merely by applying (10.1) to a restricted terminal branch. Parametrize the full source domain by

$$
P(x,r)=\frac1{1+xr}\begin{pmatrix}1&r\\x&xr\end{pmatrix},\qquad x,r>0.
\tag{10.5}
$$

Together with $\beta\in\mathbb R^4\setminus\{0\}$ and $\delta\in\mathbb R$, this is an open seven-dimensional parameter domain. For a terminal word $w$ and fixed map $C$, collinearity of $CZ_w$ with $\beta$ is expressed by the six equations

$$
\beta_j(CZ_w)_k-\beta_k(CZ_w)_j=0\qquad(0\le j<k\le3).
\tag{10.6}
$$

Multiplying by $1+xr>0$ makes each a polynomial in these seven parameters.

For any word-map pair actually selected on some input, these polynomials cannot all be identically zero. Otherwise collinearity holds for all legal sources, every coefficient vector and every drift. Varying $\delta$ implies $C\mathbf1=0$: a vector collinear with every nonzero $\beta\in\mathbb R^4$ must vanish. For fixed $P$, the linear map $C\operatorname{diag}(a(P))V$ then sends every $\beta$ into its own span. Applying it to basis vectors and their pairwise sums makes it a scalar matrix $\ell(P)I_4$. Its scalar is linear in $P$, for example by taking one diagonal entry. Since the readout is nonzero on a selected input, $\ell$ is nonzero. This contradicts the fixed-word assertion, because the terminal word is mixed.

Choose one nonzero polynomial from (10.6) for each actually used word-map pair. There are finitely many words of length at most seven and finitely many maps per word, even if all action and selection functions are discontinuous or nonmeasurable. Every input belongs to the zero set of one selected polynomial. Their product would vanish on the open full parameter domain. A finite product of nonzero real polynomials is nonzero and cannot vanish on an open set, a contradiction. This proves the theorem for adaptive protocols with the stated finite palette. ∎

**推论 10.3（已知因子恢复的精确延伸边界）。** The two fixed data-linear quantities used in III, Theorem 4.1 to recover the ratio in $g=(1+t^2)(a+bt)$ cannot be replaced, on the whole cubic domain and at the same eight-read budget, by four fixed linear quantities giving the full cubic coefficient ray, even with finite adaptive selection among words and readouts. An invertible fixed change of polynomial basis does not remove this obstruction.

Proof. Such a replacement is precisely a finite-palette gain-ray readout in Definition 10.1. A basis change can be absorbed into the fixed output matrix $C$, so Theorem 10.2 still applies. III's promise confines the coefficients to a two-dimensional subspace and does not satisfy the full four-dimensional hypothesis used in (10.6). Its decoder is therefore unaffected. A nonlinear invariant, inversion of a data-dependent matrix, or a formula restricted to one particular actual parent fiber is outside the theorem. In particular the theorem proves no unrestricted nine-read lower bound. ∎

## 11. 同一父历史中的未定联合条件

**开放问题 11.1（例外对与稀疏第三目标的共同实现）。** Determine feasibility of (6.1)–(6.4). If a pair exists, determine whether one can extend it to a third target in the same literal $\mathcal F(Y;m,j)$ so that (7.19), all source inequalities and all losing-child requirements hold. In the sparse labeling the simultaneous sixth equations include

$$
\begin{aligned}
v_1y_1&=v_2y_2,\\
v_1(p_1+1)-\kappa s_1&=v_2(p_2+1)-\kappa s_2,\\
v_1(p_1+s_1+2)-\kappa s_1&=v_3(p_3+s_3+2)-\kappa s_3,\\
v_2(p_2+x_2+1)-\kappa s_2&=v_3(p_3+x_3+1)-\kappa s_3.
\end{aligned}
\tag{11.1}
$$

Each $H_i$ must be a single nonzero real polynomial of degree at most three satisfying

$$
H_i(5)=\kappa,\quad
(H_1(7),H_2(7),H_3(7))=(\kappa,\kappa,(1+e)\kappa),\quad
H_i(6)=v_i\ne0,
\tag{11.2}
$$

and all five parent equations (4.4), with $\delta_i=j-\kappa s_i$ and one common literal $Y$. Both source factors vary in the exceptional pair; its gains are independent and at least one is cubic. Both $b,d$ must be nonconstant. One of $a,c$ may still be constant. These are necessary restrictions, not a realization or a proof of nonexistence. Whether every unrestricted three-target $L_3$ family must belong to a common joint fifth-response fiber also requires a bridge beyond the hypotheses of II, Theorem 73.1; the joint-fiber conclusions here do not assume such a bridge.

**开放问题 11.2（完整局部纤维与全部原根）。** Decide (9.6), equivalently the 127-coordinate system, or give a lawful at-most-three-further-read decoder for every unrestricted $\mathcal F(H_4(Y))$. Families with four or more targets can have varying fifth responses and different actual sixth children; their scope is the full system (9.1)–(9.5), not the three-target pattern. The finiteness of a witness and real-algebraic decidability do not decide its existence.

At the alternative parents of Sections 2–3, the complementary $JMMJ$ and $MJMM$ subtrees at the same preceding literal histories remain separate questions. The $JMJMJ$ certificate leaves the complementary fifth-$M$ subtree at its own $JMJM$ parent open. None of these histories is identified with (4.1), and avoiding a named descendant by an earlier action remains legal.

The unrestricted original-root question is still whether $n_{\rm det}(3,0)\ge9$ or there is a correct full-domain protocol using at most eight total reads. The 2046-coordinate system preserves every original-root branch and stop but has no established feasibility value here. The fixed-data-linear obstruction leaves nonlinear recovery open; the descendant certificates do not close an entire initial-$J$ or initial-$MJ$ alternative. The earlier $n_{\rm det}(3,0)\ge8$ bound retains its original scope.

## 12. 数学来源与对应范围

**约定 12.1（复用的数学接口）。** The direct matrix identities, full response tables, secant system, crossed-assignment identities, coefficient arrays and fixed-linear-readout argument above bear their stated calibration conclusions. Polynomial interpolation, elementary linear algebra, Bernstein convex combinations, the Sylvester resultant, finite-tree unfolding and real-closed-field elimination are existing tools used inside these applications.

| Mathematical source | Exact use and hypotheses |
| --- | --- |
| [FIB 自校准关系数学 II](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md), Definitions 51.1–51.2, 56.1, 69.1–69.2; Theorem 73.1 | Complete normalized target, original-clock contract, losing-history recursion, joint-response chart, and the three-target necessity with its explicit non-diagonal common-fifth hypothesis. Theorem 70.1 concerns an entire known common-$a,c$ fiber; it does not put arbitrary worlds in that fiber. The root promises and Lemmas 71.1, 71.3 retain their complete parent histories. |
| [FIB 自校准关系数学 III](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md), Theorem 4.1 and Proposition 7.1 | The fixed path $MMJMJJJ$ recovers the entire known-factor domain $g=(1+t^2)(a+bt)$, with unknown ratio and drift. Its full-cubic fixed-word collision concerns one word only. Section 10 examines the specified linear gain-ray mechanism on the larger full cubic coefficient space. |
| Yanjun Li, Kiryung Lee, Yoram Bresler, *A Unified Framework for Identifiability Analysis in Bilinear Inverse Problems with Applications to Subspace and Sparsity Models*, [Definition 2.7 and Theorem 2.8](https://arxiv.org/html/1501.06120v1) | Identifiability means that every compatible solution lies in the specified transformation orbit. Theorem 2.8 separates identification of one factor's orbit from its conditional fiber. Here the positive scaling quotient is (1.2); additive drift remains a separate coordinate. No bilinear sample threshold or adaptive acquisition theorem is imported. |
| Petra van den Bos, Frits Vaandrager, *State Identification for Labeled Transition Systems with Inputs and Outputs*, [Definition 11, Theorem 6.1, Example 7](https://arxiv.org/html/1907.11034v2) | A single adaptive distinguishing graph concerns the whole retained state set. Theorem 6.1 requires mutually incompatible distinct states in a suspension automaton and injective splits in its construction; Example 7 shows that its equivalence fails without the incompatibility premise. These automaton hypotheses are not asserted for $\mathcal W_3$. The finite trees here follow directly from (1.3). |
| Franz J. Király, Louis Theran, Ryota Tomioka, *The Algebraic Combinatorial Approach for Low-Rank Matrix Completion*, [§5.3, Theorem 34 and Remark 35](https://arxiv.org/html/1211.4116v4) | Rank-one cycle relations are the matrix-completion background for the displayed $2\times2$ determinant equalities. Remark 35's logarithmic form uses $\log|A_{ij}|$ and hence requires the entries being logged to be nonzero. It does not justify logging sampled calibration data, which may vanish or change sign, and supplies no atomic-clock budget. |
| George E. Collins, *Quantifier Elimination for Real Closed Fields by Cylindrical Algebraic Decomposition*, [§§1–3](https://link.springer.com/content/pdf/10.1007/3-540-07407-4_17.pdf) | Quantifier elimination applies to finite ordered-field formulas made from polynomial equalities and inequalities, including the rational formulas of Section 9. Sign-invariant cells and algebraic sample points give the decision and algebraic-witness consequences used there. Computational feasibility of either calibration system is a distinct question. |

## 追加锚（本行以下为增补区）

## 13. 原根完整目标的联合源秩投影

**定义 13.1（全部原根槽的源与响应矩阵）。** Retain exactly
$\mathcal W_3$, the original clocks and complete targets of Definition
1.1. Let

$$
\begin{aligned}
\mathcal S&=\{(w,e):w\in\{J,M\}^7,\ e\in\{0,1\}\},\\
\mathcal V&=\bigcup_{i=1}^7\{J,M\}^i,\\
\mathcal P&=\left\{\begin{pmatrix}a&b\\c&1-a\end{pmatrix}:
 0<a<1,\ b,c>0,\ bc=a(1-a)\right\}.
\end{aligned}
\tag{13.1}
$$

Thus $|\mathcal S|=256$, $|\mathcal V|=254$, and $\mathcal P$
is exactly the set of legal sources, without symmetry or boundedness
restrictions. Fix one source tuple
$\mathbf P=(P_q)_{q\in\mathcal S}\in\mathcal P^{\mathcal S}$.
Sources may coincide, including within a terminal pair. For a prefix
$v=E_1\cdots E_i$, put

$$
A_v=E_i\cdots E_1,\qquad
\mathcal D_v=\{(w,e)\in\mathcal S:v\text{ is a prefix of }w\},
\qquad
\mathcal D_\varnothing=\mathcal S.
\tag{13.2}
$$

Order slots lexicographically with $J<M$ and $0<1$, and let $q_v$
be the first slot in $\mathcal D_v$. For any legal source define

$$
\begin{aligned}
t_v(P)&=\operatorname{tr}(A_vP),\\
\ell_v(P)&=\bigl(t_v(P)-1,\ i\,t_v(P),\ i^2t_v(P),\ i^3t_v(P)\bigr).
\end{aligned}
\tag{13.3}
$$

For coefficient blocks $x_q=(x_{q0},x_{q1},x_{q2},x_{q3})^{\mathsf T}$,
the normalized complete world associated with a nonzero block is

$$
g_q(T)=\sum_{j=0}^3x_{qj}T^j,\qquad
\delta_q=-x_{q0},\qquad W_q=(P_q,g_q,\delta_q).
\tag{13.4}
$$

It has initial reading zero, and its reading at the original clock
$i=|v|$ is exactly $\ell_v(P_q)x_q$.
This is the coordinate change
$(\delta,\beta_1,\beta_2,\beta_3)=(-x_{q0},x_{q1},x_{q2},x_{q3})$
in Definition 9.1; it imposes no initial-root or zero-drift promise.

Define $B(\mathbf P)$ to have one row for each $v\in\mathcal V$
and $q\in\mathcal D_v\setminus\{q_v\}$. Its action on the single
stacked vector $x=(x_q)_{q\in\mathcal S}\in\mathbb R^{1024}$ is

$$
\bigl(B(\mathbf P)x\bigr)_{v,q}
 =\ell_v(P_q)x_q-\ell_v(P_{q_v})x_{q_v}.
\tag{13.5}
$$

All other blocks of this row are zero. At depth $i$ there are $2^i$
prefixes, each with $2^{8-i}$ descendant slots. The numbers of rows
at successive depths are therefore

$$
\bigl(2^i(2^{8-i}-1)\bigr)_{i=1}^7
 =(254,252,248,240,224,192,128),\qquad
\sum_{i=1}^7(256-2^i)=1538.
\tag{13.6}
$$

Hence $B(\mathbf P)$ has exactly $1538$ rows and $1024$ columns.
Writing $P_q=(\begin{smallmatrix}a_q&b_q\\c_q&1-a_q\end{smallmatrix})$,
its entries are integer affine polynomials in the $768$ ambient
source coordinates, since

$$
t_v(P_q)=(A_v)_{22}+
 ((A_v)_{11}-(A_v)_{22})a_q+(A_v)_{21}b_q+(A_v)_{12}c_q.
\tag{13.7}
$$

The $256$ equations $b_qc_q=a_q(1-a_q)$ and every strict source
inequality in (13.1) remain imposed. The count $768$ is an ambient
coordinate count, not the dimension of an unconstrained legal-source
space.

**定义 13.2（逐槽增益与完整同源差异）。** Let $G_q$ and $D_w$
be the constant $4\times1024$ matrices specified by

$$
G_qx=x_q\quad(q\in\mathcal S),\qquad
D_wx=x_{(w,0)}-x_{(w,1)}\quad(w\in\{J,M\}^7).
\tag{13.8}
$$

In particular $D_w$ retains all four coefficient differences. In
the zero-initial-reading coordinates, two complete terminal targets
are distinct exactly when

$$
P_{(w,0)}\ne P_{(w,1)}\quad\text{or}\quad D_wx\ne0.
\tag{13.9}
$$

A source difference alone already distinguishes complete targets.
When the sources agree, a gain difference is necessary and sufficient;
the drift difference is then minus the constant-coefficient difference.
The separation guard below uses this full four-component map, without
requiring a prescribed coefficient to differ.

Write $[B;T]$ for vertical row concatenation and use exact real rank.
For later polynomial notation set

$$
s_w(\mathbf P)=2(a_{(w,0)}-a_{(w,1)})^2
 +(b_{(w,0)}-b_{(w,1)})^2+(c_{(w,0)}-c_{(w,1)})^2.
\tag{13.10}
$$

This is $\|P_{(w,0)}-P_{(w,1)}\|_F^2$. For a real matrix $C$ let

$$
\mu_k(C)=\sum_{\substack{I,J\text{ row and column sets}\\|I|=|J|=k}}
                  \det(C_{I,J})^2,\qquad
\mu_0(C)=1,
\tag{13.11}
$$

and set $\mu_k(C)=0$ when $k$ exceeds its row or column count.
These are existing minor expressions used below to write the
source criterion as a finite polynomial formula.

**定理 13.3（完整原根障碍的精确源秩等价）。** For every fixed
$\mathbf P\in\mathcal P^{\mathcal S}$, there exist gains, drifts and
shared prefix responses solving the entire system of Theorem 9.3
with these prescribed slot sources if and only if, with
$r=\operatorname{rank}B(\mathbf P)$, both conditions hold:

$$
\begin{aligned}
\operatorname{rank}[B(\mathbf P);G_q]&>r
 &&\text{for every }q\in\mathcal S,\\
P_{(w,0)}\ne P_{(w,1)}\quad\text{or}\quad
\operatorname{rank}[B(\mathbf P);D_w]&>r
 &&\text{for every }w\in\{J,M\}^7.
\end{aligned}
\tag{13.12}
$$

Consequently there is no complete-target decoder on all of
$\mathcal W_3$ with at most eight total readings if and only if
one legal tuple of $256$ sources satisfies (13.12). The statement
retains both initial actions, all actual prefixes, all early stops
and arbitrary deterministic policies. It imposes no gain shape,
sign, degree-equality, root, common-drift or particular-ancestor
promise. Only the two slots of each leaf must give different complete
targets; targets at different leaves may repeat.

Equivalently the exact source-only condition, with no coefficient
or shared-response quantifiers, is

$$
\begin{aligned}
\Phi(\mathbf P)=\bigvee_{r=0}^{1024}\Bigl[&
 \mu_r(B)>0\ \land\ \mu_{r+1}(B)=0\\
 &\land\ \bigwedge_{q\in\mathcal S}\mu_{r+1}([B;G_q])>0\\
 &\land\ \bigwedge_{w\in\{J,M\}^7}
   \bigl(s_w(\mathbf P)>0\ \lor\ \mu_{r+1}([B;D_w])>0\bigr)
 \Bigr],
 \qquad B=B(\mathbf P).
\end{aligned}
\tag{13.13}
$$

The original-root obstruction is exactly
$\exists\mathbf P\in\mathcal P^{\mathcal S}:\Phi(\mathbf P)$.
This eliminates jointly the $1024$ free gain/drift coordinates of
Definition 9.1 and the $254$ shared responses of Theorem 9.3,
leaving $768$ ambient source coordinates with all $256$ rank-one
equations retained. These are exact counts of variables and matrix
sizes; they give no bound on the arithmetic work needed to decide
the displayed existence statement.

Proof, elimination of the actual shared responses. For a fixed source
tuple and a single vector $x$, the prefix equations of Theorem 9.3
are exactly

$$
\ell_v(P_q)x_q=z_v
\quad(v\in\mathcal V,\ q\in\mathcal D_v).
\tag{13.14}
$$

Subtracting the equation for $q_v$ from all the others gives
$B(\mathbf P)x=0$. Conversely every $x$ in this kernel gives all
of (13.14) by the one choice
$z_v=\ell_v(P_{q_v})x_{q_v}$. Thus (13.5) eliminates all shared
response variables without dropping any ancestor equation. Every
coefficient block must still be nonzero, and (13.9) is exactly the
remaining terminal complete-target distinction.

Proof, necessity of the guards. Put $U=\ker B(\mathbf P)$. For any
linear map $T$ on $\mathbb R^{1024}$, rank-nullity gives

$$
\begin{aligned}
\operatorname{rank}[B;T]-\operatorname{rank}B
 &=\dim U-\dim(U\cap\ker T)\\
 &=\operatorname{rank}(T|_U).
\end{aligned}
\tag{13.15}
$$

An actual solution of Theorem 9.3 supplies $x\in U$ with
$G_qx\ne0$ at every slot. If its leaf sources coincide,
(13.9) also requires $D_wx\ne0$. Each required restriction $T|_U$
is therefore nonzero, and (13.15) proves every corresponding strict
rank inequality in (13.12). A leaf with unequal sources already has
distinct targets; no additional coefficient inequality is necessary
for that leaf.

Proof, one simultaneous legal coefficient vector. Suppose (13.12)
holds. Form the finite list of maps

$$
\mathcal T=\{G_q:q\in\mathcal S\}
 \ \cup\ \{D_w:P_{(w,0)}=P_{(w,1)}\}.
\tag{13.16}
$$

List its members as $T_1,\ldots,T_m$, where $256\le m\le384$.
By (13.15), every $T_j|_U$ is nonzero. Choose $u_j\in U$ and one
scalar component $L_j$ of $T_j$ with $L_j(u_j)\ne0$. Consider

$$
u(t)=\sum_{j=1}^m t^{j-1}u_j\in U.
\tag{13.17}
$$

For each $j$, the scalar polynomial $L_j(u(t))$ is nonzero: its
coefficient of $t^{j-1}$ is exactly $L_j(u_j)\ne0$. Every one
has finitely many real roots. Their finite union omits an integer
$t_*$, and the single choice $x=u(t_*)$ satisfies all
$T_jx\ne0$ simultaneously. This is the finite-subspace avoidance
argument already used in Section 10, now applied to the gain and
complete-target guards of the full tree. It does not choose a
different coefficient vector for each map, action or leaf.
In particular $U=\{0\}$ cannot satisfy the gain guards, so no
zero-kernel exception has been omitted.

Reconstruct every $W_q$ by (13.4). Each gain is nonzero, every drift
is a real constant, and all leaf pairs are distinct by (13.9).
Set the $254$ responses as after (13.14). These are legal fixed
worlds satisfying every reading in their common actual histories.
They therefore solve exactly the system in Theorem 9.3. This proves
the asserted equivalence for each fixed source tuple.

Proof, actual children and stopping. The finite-tree equivalence
itself is the prior result of Theorem 9.3 and Definition 1.2. To
make explicit its use by the projection, for each prefix $v$ let

$$
H_v=(0,E_1,z_{E_1},\ldots,E_i,z_v),\qquad
K_v=\{W_q:q\in\mathcal D_v\},\qquad H_\varnothing=(0).
\tag{13.18}
$$

Every member of $K_v$ realizes every reading of $H_v$. Write
$i=|v|$. For $i<7$, each next atom $E\in\{J,M\}$ and every real
response $z$ define the actual child precisely by

$$
C_{v,E,z}=K_v\cap\mathcal F(H_v,E,z)
 =\{W\in K_v:g_W(i+1)\operatorname{tr}(EA_vP_W)+\delta_W=z\},
\tag{13.19}
$$

where $A_\varnothing=I$. At the selected response it satisfies

$$
K_{vE}\subseteq C_{v,E,z_{vE}}.
\tag{13.20}
$$

Equality is unnecessary; additional compatible worlds in the child
cannot remove a losing subfamily. At a leaf $w$, $K_w$ contains its
two distinct complete targets and hence has $L_0$. Upward induction,
using (13.20), upward monotonicity and both action conjuncts in
(1.3), gives
$L_{7-|v|}(K_v,H_v)$ at every prefix, including the empty one.
Every such node contains a descendant distinct pair, so early
stopping also fails. The root union lies in $\mathcal I_0$, and
upward monotonicity gives $L_7(\mathcal I_0,(0))$.
Conversely Theorem 9.3 unfolds this root predicate into fixed
terminal pairs and their shared actual ancestor responses, so the
necessity argument above applies to every original-root obstruction.
The two actions have separate response witnesses on the same fixed
collection of worlds. No unchosen response is acquired by a policy.

Proof, reversal of initial-reading translation. For each arbitrary
observed initial reading $a\in\mathbb R$, trace one implies
$a=g(0)+\delta$. The map

$$
(P,g,\delta)\longmapsto(P,g,\delta-a)
\tag{13.21}
$$

is a bijection from the entire initial-$a$ fiber to $\mathcal I_0$;
its inverse adds $a$ to the drift. On every action word it subtracts
$a$ from every reading, changes no clock and preserves all response
partitions. In particular the worlds constructed above translate to
$\delta_q=a-x_{q0}$ and keep every gain and source unchanged.
A decoder on the whole $\mathcal I_0$ transports to all of
$\mathcal W_3$ by subtracting the actual initial $a$ from its
history, executing the selected atoms with their immediate readings,
and adding $a$ to the returned drift. Actions and early stops
transport in exactly the same way. A full-domain decoder restricts
to $\mathcal I_0$. This is the reversible normalization of Theorem
9.3, so the fixed-source equivalence proves the stated original-root
equivalence without an initial-root promise.

Finally, for real matrices $\mu_r(C)>0$ and $\mu_{r+1}(C)=0$
express exactly $\operatorname{rank}C=r$; the vanishing of a sum
of squared real minors is the vanishing of every such minor.
On this rank stratum, (13.15) makes each guard equivalent to
$\mu_{r+1}([B;T])>0$. Equation (13.10) expresses source inequality
by $s_w>0$. This proves (13.13), including all rank drops. It is
a finite polynomial formula with rational coefficients by (13.7).
No gain sample has been divided out anywhere. Constant and
lower-degree gains, either sign, sampled and repeated roots, varying
drifts, nonsymmetric sources and repetitions between leaves all
remain in the equivalence. ∎

**命题 13.4（所有增益守卫成立仍不能删除同源分离守卫）。**
Set every one of the $256$ sources to

$$
P_* =\begin{pmatrix}1/2&1/2\\1/2&1/2\end{pmatrix}.
\tag{13.22}
$$

This is a legal source tuple for which every gain inequality in
(13.12) holds, while the separation inequality for $w_*=M^7$
fails. Thus retaining the gain guards alone is not an equivalent
source criterion for Theorem 9.3.

Proof. The matrix $P_*$ is strictly positive, has trace one and
has determinant zero. For every $h\in\mathbb R^4$, the diagonal
coefficient vector $x_q=h$ at all slots lies in $\ker B$, because
every descendant of a given prefix then has the same source and
coefficient block. Each $G_q|_{\ker B}$ is therefore surjective,
so every gain guard holds by (13.15); a nonzero $h$ makes all gains
nonzero at once.

For an arbitrary $x\in\ker B$, put $d=D_{w_*}x$. The two slots
of $w_*$ share the responses at every all-$M$ prefix, since both
are equal to its reference descendant's response in (13.5).
Subtract their equalities at clocks $1,2,3,4$. Direct multiplication
gives

$$
\begin{gathered}
M^2=\begin{pmatrix}1&1\\1&2\end{pmatrix},\quad
M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},\quad
M^4=\begin{pmatrix}2&3\\3&5\end{pmatrix},\\
\bigl(\operatorname{tr}(M^iP_*)\bigr)_{i=1}^4
 =\left(\frac32,\frac52,4,\frac{13}2\right).
\end{gathered}
\tag{13.23}
$$

Hence those four exact response-difference equations are $Rd=0$,
where

$$
R=\begin{pmatrix}
1/2&3/2&3/2&3/2\\
3/2&5&10&20\\
3&12&36&108\\
11/2&26&104&416
\end{pmatrix}
 =\frac12\begin{pmatrix}
1&3&3&3\\3&10&20&40\\6&24&72&216\\11&52&208&832
\end{pmatrix}.
\tag{13.24}
$$

Subtracting $3,6,11$ times the first row of $2R$ from its next
three rows leaves the lower-right block

$$
\begin{pmatrix}1&11&31\\6&54&198\\19&175&799\end{pmatrix}.
$$

Subtracting $6$ and $19$ times its first row from its other rows
leaves the last $2\times2$ determinant

$$
\det\begin{pmatrix}-12&12\\-34&210\end{pmatrix}
 =-2520+408=-2112.
$$

The two preceding pivots are one, so

$$
\det R=\frac{-2112}{2^4}=-132\ne0.
\tag{13.25}
$$

Therefore $d=0$ for every $x\in\ker B$. Equation (13.15) gives
$\operatorname{rank}[B;D_{w_*}]=\operatorname{rank}B$.
Its two sources are equal, so neither alternative in that leaf's
separation guard holds. Any kernel vector would give identical
complete targets at that leaf. This tuple is a counterexample to
omitting the separation conditions, not a losing-tree realization
and not a universal failure result for other source tuples. ∎

## 14. 源秩投影的数学对应与未定可行性

**定义 14.1（原根源可行域及其适用边界）。** Define

$$
\mathfrak S_7=\{\mathbf P\in\mathcal P^{\mathcal S}:
                         \Phi(\mathbf P)\}.
\tag{14.1}
$$

Theorem 13.3 identifies its nonemptiness with failure of every
full-domain at-most-eight-reading decoder, and its emptiness with
existence of such a decoder. Nonemptiness asserts the existence of
one legal source tuple satisfying every gain guard and every applicable
same-source separation guard; its one common coefficient vector
then exists by (13.17). An emptiness proof must show that every
legal source tuple fails at least one of those guards. Checking
only a specified history, source band, sign, gain shape or root
stratum cannot replace this universal source-tuple condition.
Neither alternative is determined by Proposition 13.4 or by the
rank equivalence itself. No feasible tuple, universal guard failure,
explicit eight-reading full-domain inverse or nine-reading upper
bound is supplied here.

The explicit $1538\times1024$ response matrix, its joint guarded
projection and the legal equal-source counterexample are
repository-derived deductions. Initial-reading translation, the
$256$-slot tree and its actual-history equivalence are the prior
results of Section 9. Finite-subspace avoidance, rank-nullity and
minor characterizations of rank are established tools within the
projection proof, not separate new general theorems.

| Mathematical source | Correspondence and retained hypotheses |
| --- | --- |
| This volume, Definitions 1.1–1.2 and 9.1; Theorem 9.3 | The full legal model, losing-history recursion, normalized complete-target coordinates and all $256$ terminal slots are reused. Equation (13.5) eliminates their common responses; (13.12) also eliminates the normalized gain/drift coordinates while retaining their legality and terminal distinctions. |
| This volume, Corollary 9.4 and proof of Theorem 10.2 | Real-closed-field elimination already gives abstract decidability, algebraic-witness transfer and semialgebraic policy existence. Finite hyperplane avoidance already occurs in the fixed-linear-readout proof. The present result is the explicit source-dependent formula (13.12)–(13.13), without an evaluated feasibility or complexity conclusion. |
| [FIB 自校准关系数学 IX](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IX.md), Theorem 3.1 and Definition 11.1 | On its prescribed six-reading $JMMJM$ ancestor, gain and drift are uniquely forced once a legal source is supplied. That source graph neither acquires an unknown source nor supplies losing responses on the other original-root actions. The tuple in (13.1) is an existential mathematical witness variable, not an observed class label. |
| [FIB JMMJM Terminal-Root Decoders and the Simultaneous Core](FIB_JMMJM_TERMINAL_ROOT_DECODERS_AND_SIMULTANEOUS_CORE.md), Theorems 8.1–9.1 | Its inclusion-minimal triple has root seven, common drift, nonzero ancestor and sixth samples and two different proper sixth collision pairs. Those restrictions define its own simultaneous core; they are not imposed on $\mathfrak S_7$. |
| [FIB JMMJM Nonzero-Terminal Collision Sparsity and Ratio Diversity](FIB_JMMJM_NONZERO_TERMINAL_COLLISION_SPARSITY_AND_RATIO_DIVERSITY.md), Definitions 1.2 and 7.1; Proposition 7.2 | The source chart and PP/PT/TP/TT conditions keep one literal $JMMJM$ ancestor and terminal nonvanishing. Their actual-child distinctions are consistent with (13.19), but a three-world conditioned system is not the unrestricted original-root source locus. |
| [FIB JMMJM Zero-Sixth Root Rigidity and Terminal Collision Geometry](https://github.com/the-omega-institute/trureturing/blob/7a5bd6a6bce1b3213422b7b3a1eca2d6c10ec707/docs/develop/theory/FIB_JMMJM_ZERO_SIXTH_ROOT_RIGIDITY_AND_TERMINAL_COLLISION_GEOMETRY.md), Theorems 2.1, 4.1 and Proposition 7.1 | Its whole-class rigidity, three-terminal-coordinate injections and exact TT system assume the specified ancestor, common drift, root six and terminal nonvanishing where stated. They neither eliminate the full original-root coefficient vector nor give an unknown class label. The guard formula retains the zero-sixth and terminal-root possibilities without any such promises. |

Yanjun Li, Kiryung Lee and Yoram Bresler, *A Unified Framework for
Identifiability Analysis in Bilinear Inverse Problems with Applications
to Subspace and Sparsity Models*,
[Definition 2.7 and Theorem 2.8, arXiv:1501.06120v1](https://arxiv.org/html/1501.06120v1),
require both first-factor orbit identification among all compatible
pairs and conditional second-factor identification for a nonzero pair
in the specified constrained bilinear problem and ambiguity group.
Only the conditional part resembles source-supplied recovery; it does
not supply unknown-source acquisition or an adaptive reading bound.
Theorem 13.3 instead constructs each original complete world and its
shared ancestors explicitly.

Choudhary and Mitra, *Identifiability Scaling Laws in Bilinear Inverse
Problems*,
[Proposition 1 and Remark 5, arXiv:1402.2637v2](https://arxiv.org/html/1402.2637v2),
retain the constrained realizable factor-product set in their
rank-two-nullspace intersection criterion. Remark 5 restricts the
necessity statement to observations realizable in the original
factor problem, rather than every freely chosen lifted observation.
Here the source equations, the common kernel vector and the guard
avoidance jointly supply realizability; independently fitted pair
responses or unconstrained lifted differences cannot replace them.
No bilinear sample threshold is imported.

Perrucci and Roy, *Elementary Recursive Quantifier Elimination Based
on Thom Encoding and Sign Determination*,
[Theorem 1, arXiv:1609.02879v2](https://arxiv.org/html/1609.02879v2),
concerns finite first-order formulas with polynomial atoms over a
subring of a real closed field and elimination of a quantified block.
The rational polynomial formulas (13.1), (13.7) and (13.13) are in
that language. This is the established elimination setting already
used in Corollary 9.4; the ranks and one-vector construction above
give a specific projection directly, without invoking that theorem
to decide $\mathfrak S_7$. These citations delimit the mathematical
correspondences and make no external-priority or exhaustive-literature
claim. The unrestricted eight-versus-nine original-root feasibility
question remains undetermined.

## 追加锚（本行以下为增补区）
