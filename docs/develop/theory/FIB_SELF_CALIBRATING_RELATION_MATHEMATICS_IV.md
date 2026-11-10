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

## 22. 五维及有限高维的严格正同容限覆盖障碍

本节把第 21 节的四维构造推进到五维，并给出一个带有统一有界不变量的有限维递归。这里的维数是来源矩阵的维数；它不是把四维矩阵补零，也不是假设覆盖数随维数单调。所有新坐标仍由严格正的两项外积产生。

### 定义 22.1（五维合同与共同来源系统）

沿用 III 定义 9.1、13.1、14.1 和 IV 定义 21.1，把来源域换成

$$
\mathcal M_5=\left\{\sum_{a=1}^{m}c_a\ell_a:
 m\in\{1,2\},\ c_a\in\mathbb R_{>0}^{5},\
 \ell_a\in\mathbb R_{>0}^{1\times5}\right\}.
$$

仍只允许一条不可复制、不可复位的轨迹，原子为

$$
Ne_j=e_{j+1}\ (j<4),\qquad Ne_4=0,\qquad
L_0=e_0\mathbf 1^{\mathsf T},
$$

初读和每个原子后的报告都计费，误差满足固定闭约束 $|\eta_i|\le\varepsilon$，并可任意相关、依赖全部历史。普通初始矩阵秩为目标；可靠性仍在完整的 $\mathcal M_5$ 上量化。

对纯 $N$ 前缀，置

$$
a_i(R)=\operatorname{tr}(N^iR),\qquad
b_j^{(q)}(R)=\sum_{h=0}^{4-q}R_{hj}
$$

其中 $0\le q<5$。在单位容限下，令 $B_q=\{0,\ldots,4\}$（$q\le3$），$B_4=\{0,\ldots,3\}$，并置

$$
A_i(x,v)=\sum_{h=0}^{4-i}x_hv_{h+i},\qquad
\sum_{h=0}^{4-q}x_h=1,\qquad x_h,v_j>0.
$$

设旧纯 $N$ 报告为 $y_0,\ldots,y_q$，规范补全的新报告为 $(w_j)_{j\in B_q}$。实际报告相容系统 $\mathsf D_q(y,w)$ 要求同一组 $x,v$ 满足上述归一化、严格正性及

$$
|A_i(x,v)-y_i|\le1\ (0\le i\le q),\qquad |v_j-w_j|\le1\ (j\in B_q).
$$

这是 III 引理 13.2 的 (13.5) 在 $k=5,\varepsilon=1$ 的实例，有解当且仅当一个严格正秩一来源与全部实际规范报告相容。$q=4$ 时 $x_0=1$、$v_4=A_4$，而 $b_4^{(4)}=a_4$ 只使用旧报告 $y_4$，没有第二份报告或误差变量。

辅助系统 $\mathsf C_q(R,y)$ 是 III 定义 14.3 的实例：保持同一归一化、严格正性和旧报告约束，将新报告约束换成 $|v_j-b_j^{(q)}(R)|\le2$（$j\in B_q$）。若 $(y,w)$ 是 $R$ 的允许报告，则 $\mathsf D_q(y,w)$ 的每个解也满足 $\mathsf C_q(R,y)$，因为 $|v_j-b_j^{(q)}(R)|\le|v_j-w_j|+|w_j-b_j^{(q)}(R)|\le2$。反之，对 $R$ 的允许旧前缀，$\mathsf C_q(R,y)$ 的一个解给出共同允许补全 $w_j=(v_j+b_j^{(q)}(R))/2$；$q=4$ 的共享坐标仍用 $y_4$。此中点构造不保证任意预先给定的 $w$ 与该解相容。末端判定只使用 $\mathsf D_q$。

### 引理 22.2（五维严格正族）

对 $0\le s\le1/2$，令

$$
\begin{aligned}
d_s&=\frac{37}{2}+s-\frac{125}{44+s},&
\lambda_s&=\frac12+s,&
c_s&=94-d_s-10s,\\
L_s&=\frac{39}{2}-\frac{125}{44+s},&
M&=\frac{39}{2},&
D_s&=\frac{125}{44+s},\\
\rho_s&=\frac{44+s}{50},&
\tau_s&=17+\frac{s}{4},&
K&=10000,\\
\mu_s&=K-1011-\lambda_s(3-s),\\
r_s&=(1000,c_s,3-s,10,1),\\
w_s&=(1,1,d_s,23/2,8),
\end{aligned}
$$

并定义

$$
Q_s=
\begin{pmatrix}
r_s\\ w_s\\ \lambda_sr_s\\ r_s\\ \mu_sr_s
\end{pmatrix}.
$$

则 $Q_s\in\mathcal M_5$，且 $\operatorname{rank}(Q_s)=2$。其纯 $N$ 数据与参数无关：

$$
(a_0,a_1,a_2,a_3,a_4)(Q_s)=(K,100,15,18,1).
$$

此外

$$
\begin{aligned}
b^{(0)}(Q_s)&=(2+\lambda_s+\mu_s)r_s+w_s,\\
b^{(1)}(Q_s)&=(2+\lambda_s)r_s+w_s,\\
b^{(2)}(Q_s)&=(1+\lambda_s)r_s+w_s,\\
b^{(3)}(Q_s)&=(1001,c_s+1,L_s+2,M+2,9),\\
b^{(4)}(Q_s)&=(1000,c_s,3-s,10,1)=r_s.
\end{aligned}
$$

**证明。** 在 $[0,1/2]$ 上有

$$
70<c_s<80,\qquad \frac{31}{2}<d_s<19,\qquad
\frac12\le\lambda_s\le1,\qquad
\frac{17973}{2}\le\mu_s\le\frac{17975}{2}.
$$

取 $\alpha=1/2000$，记 $C=(1,0,\lambda_s,1,\mu_s)^{\mathsf T}$、$e=(0,1,0,0,0)^{\mathsf T}$，则

$$
Q_s=\frac{(C+\alpha e)(r_s-\alpha w_s)}{1-\alpha^2}
 +\frac{(\alpha C+e)(w_s-\alpha r_s)}{1-\alpha^2}.
$$

两列因子严格正，且两行因子也严格正；新坐标的关键下界是
$1-1000/2000=1/2>0$。所以 $Q_s$ 是两项严格正外积之和。
前两行、末两列的子式为

$$
10\cdot8-\frac{23}{2}=\frac{137}{2}\ne0,
$$

故普通秩至少为二，而上述分解给出秩至多二。
上对角线逐项求和给出 $(K,100,15,18,1)$；各 $b^{(q)}$ 由定义直接得到。∎

### 命题 22.3（五维逐来源九报告协议）

对每个 $s\in[0,1/2]$，存在一个在完整 $\mathcal M_5$ 上 $\varepsilon=1$ 可靠的协议 $\Pi_s$，它在 $Q_s$ 的每条允许误差历史上恰以九个报告输出 $2$。协议先取得 $y_0$，连续执行三次 $N$ 并取得 $y_1,y_2,y_3$；随后

$$
\begin{cases}
L_0,N,N,N,N,&y_3\le\tau_s,\\
N,L_0,N,N,N,&y_3>\tau_s.
\end{cases}
$$

末端用全部实际取得的报告检查定义 22.1 的 $\mathsf D_3(y,w)$ 或 $\mathsf D_4(y,w)$；无严格正解时输出 $2$，有解时停止而不作秩断言。

**证明。** 对任意实际严格正秩一来源 $S=c\ell$，令 $d=\sum_{h=0}^{4-q}c_h$、$x=c/d$、$v=d\ell^{\mathsf T}$，则其每条允许历史都提供 $\mathsf D_q(y,w)$ 的同一个严格正解，故该报告规则在完整 $\mathcal M_5$ 上可靠。两条分支各执行八个原子，连同初读共有九个报告；$q=3$ 新取全部五个 $b$ 报告，$q=4$ 只新取 $b_0,\ldots,b_3$，末坐标沿用旧报告 $y_4$。

固定 $Q_s$ 的任意允许历史。由定义 22.1，$\mathsf D_q(y,w)$ 有解蕴含 $\mathsf C_q(Q_s,y)$ 有解，故只需排除所选切口的辅助系统。若 $y_3\le\tau_s$ 而 $\mathsf C_3$ 有解，写 $x_0=z,x_1=1-z$。由 $v_2\ge L_s$、$v_3\ge M$、$v_4\ge7$ 和 $x_2>0$：

$$
A_2=zv_2+(1-z)v_3+x_2v_4\ge zL_s+(1-z)M+7x_2>M-D_sz.
$$

同时 $A_2\le y_2+1\le17$，故 $z>\rho_s$。于是

$$
A_3\ge zM+(1-z)7
>7+\frac{25}{2}\rho_s=\tau_s+1,
$$

这与 $A_3\le y_3+1\le\tau_s+1$ 矛盾。

若 $y_3>\tau_s$，第四次 $N$ 后执行 $L_0$，且 $\mathsf C_4$ 有解，则 $x_0=1$、$0<v_4=A_4\le y_4+1\le3$、$1-s\le v_2$、$8\le v_3\le12$。由 $A_2\le y_2+1\le17$ 和 $x_2v_4>0$ 得

$$
x_1v_3<16+s,
$$

从而

$$
A_3=v_3+x_1v_4
<v_3+\frac{3(16+s)}{v_3}
\le16+\frac{s}{4}=\tau_s-1.
$$

最后一步由 $v\mapsto v+3(16+s)/v$ 在 $[8,12]$ 上的凸性及端点值 $14+3s/8\le16+s/4$ 得到。但 $A_3\ge y_3-1>\tau_s-1$，矛盾。等号 $y_3=\tau_s$ 归入第一分支；严格性由所有因子严格正提供。两支均排除 $\mathsf C_q(Q_s,y)$，从而排除实际报告系统 $\mathsf D_q(y,w)$，故每条允许历史均输出 $2$。∎

### 引理 22.4（五个切口的固定伴随）

对每个 $s$，$q=0,1,2$ 的共同来源系统分别有严格正秩一解：$q=0$ 取 $v=b^{(0)}(Q_s)$，利用 $v_4<K<v_0$ 与 III 命题 9.6；$q=1,2$ 把 IV 引理 21.4 的四维伴随 $(x,v)$ 提升为 $(x,x_4)$ 与 $(\beta_q,v)$，其中

$$
\beta_1=1000(2+\lambda_s)+1,\qquad
\beta_2=1000(1+\lambda_s)+1,
$$

并以 $A_0=K$ 解出最后一个正坐标 $x_4$。下面给出统一界，证明这些坐标严格正，并核对旧报告与全部新坐标的闭误差约束。

若 $0\le s<t\le1/2$ 且 $\tau_s<u<\tau_t$，共同纯 $N$ 前缀

$$
p=(K,100,16,u,2)
$$

同时属于 $Q_s,Q_t$ 的允许报告盒。对 $q=3$，取

$$
\begin{aligned}
h&=\frac{u-\tau_s}{25},&z&=\rho_s+h,\\
v&=(1001,c_s+1,L_s,M,7),&
x_0&=z,&x_1&=1-z,&x_2&=D_sh/7,\\
x_3&=\frac{100-z(c_s+1)-(1-z)L_s-Mx_2}{7},&
x_4&=\frac{K-\sum_{h=0}^{3}x_hv_h}{7}.
\end{aligned}
$$

则 $x,v>0$，并产生

$$
(A_0,A_1,A_2,A_3)=\left(K,100,17,\tau_s+1+\frac{u-\tau_s}{2}\right),
$$

其旧报告误差为 $(0,0,1,1-(u-\tau_s)/2)$，而
$v-b^{(3)}(Q_s)=(0,0,-2,-2,-2)$。

对 $q=4$，取

$$
\begin{aligned}
v&=(1000,c_t,1-t,12,3),&x_0&=1,\\
x_1&=\frac{u-13}{3},&x_2&=\frac{4(\tau_t-u)}{3},\\
x_3&=\frac{100-c_t-x_1(1-t)-12x_2}{3},&
x_4&=\frac{K-\sum_{h=0}^{3}x_hv_h}{3}.
\end{aligned}
$$

则 $x,v>0$，

$$
(A_0,A_1,A_2,A_3,A_4)=(K,100,17,u-1,3),
$$

旧报告误差为 $(0,0,1,-1,1)$，并且

$$
(v_j-b_j^{(4)}(Q_t))_{j=0}^{3}=(0,0,-2,2).
$$

末坐标不另取报告：$Q_t$ 的真实 $a_4$ 为 $1$，伴随来源的 $A_4$ 为 $3$，二者共同使用旧报告 $2$，误差端点分别为 $+1$ 与 $-1$。

**证明。** $q=0$ 的最小与最大坐标严格夹住 $K$，故正凸组合存在。为把早切口的正性写成显式界，$q=1$ 取四维引理 21.4 的 $q=0$ 见证，并令

$$
x_4=\frac{K-x_0\beta_1-x_1v_0-x_2v_1-x_3v_2}{v_3},
\qquad \beta_1=1000(2+\lambda_s)+1.
$$

四维界给出 $\beta_1\le3001$、$v_0<241$、$v_1<28$、$v_2<42$、$0<v_3\le11$，而 $x_0+x_1+x_2+x_3=1$；故该分子的下界大于 $10000-3001>0$。$q=2$ 取四维引理 21.4 的 $q=1$ 见证，并令

$$
x_4=\frac{K-x_0\beta_2-x_1v_0-x_2v_1-x_3v_2}{v_3},
\qquad \beta_2=1000(1+\lambda_s)+1.
$$

此时 $\beta_2\le2001$、$v_0<161$、$v_1<25$、$v_2<32$、$v_3\ge19/2$，且该四维见证满足 $x_0=1/4$、$x_1+x_2=3/4$、$x_3<200/19$。从而

$$
x_0\beta_2+x_1v_0+x_2v_1+x_3v_2
<\frac{2001}{4}+161\cdot\frac34+32\cdot\frac{200}{19}<1000<K,
$$

故 $x_4>0$。两次提升只新增一个首坐标和一个尾权重，$A_i$ 的旧部分逐项保持，新首坐标误差为零，旧约束与全部新坐标约束均保留。对两个晚切口，$0<h<1/200$、$0<z<1$，且

$$
z(c_s+1)+(1-z)L_s+Mx_2<82<100,
$$

以及

$$
c_t+x_1(1-t)+12x_2<80+11/8+2<100.
$$

这给出 $x_3>0$。在 $q=3$ 中，$x_3<100/7<15$、$x_2<1/400$、$L_s<20$，所以

$$
x_0v_0+x_1v_1+x_2v_2+x_3v_3<1001+81+1+300<1400<K,
$$

从而所定义的 $x_4$ 也严格正。在 $q=4$ 中 $x_1<11/8$、$x_2<1/6$、$x_3<100/3$，故

$$
x_0v_0+x_1v_1+x_2v_2+x_3v_3
<1000+80\cdot\frac{11}{8}+\frac16+12\cdot\frac{100}{3}<1600<K,
$$

其 $x_4$ 也严格正。所有闭误差约束由上面列出的差值直接验证。每个切口只固定一个 $S=xv^{\mathsf T}$；选定切口后它在完整前缀、补全和后续历史中不变。∎

### 定理 22.5（五维同容限无限预选覆盖障碍）

对每个有限实数 $\varepsilon>0$ 和有限集合 $T\subseteq[0,1/2]$，令

$$
Q_{\varepsilon,s}=\varepsilon Q_s.
$$

则

$$
Q_{\varepsilon,s}\in\mathcal I_5(\varepsilon),\qquad
\nu_{5,\varepsilon}(\{Q_{\varepsilon,s}:s\in T\})=|T|,\qquad
\nu_{5,\varepsilon}(\mathcal I_5(\varepsilon))=\infty.
$$

**证明。** 把命题 22.3 和引理 22.4 中的每个真实值、伴随的 $v$、阈值和报告都乘以 $\varepsilon$，保留 $x$ 与动作词。由于

$$
\operatorname{tr}(A\,\varepsilon R)=\varepsilon\operatorname{tr}(AR),
$$

这把单位闭误差区间双射到 $[-\varepsilon,\varepsilon]$，并保秩、保严格正性和全部动作历史。

若一个完整域可靠协议在两个不同参数上都全误差成功，按逐前缀归纳把报告除以 $\varepsilon$，只需证明单位尺度下不存在这种共同成功。取 $s<t$ 和 $\tau_s<u<\tau_t$，用共同纯 $N$ 前缀

$$
p=(K,100,16,u,2).
$$

这是 $Q_s,Q_t$ 两者的允许历史。若协议在首次 $L_0$ 前的任一纯 $N$ 前缀（包括 $q=0,1,2,3,4$）停止，III 引理 10.3 的正秩一回放来源使该停止历史不能在完整环境域上可靠；因此归一化正规形必须继续到某个首次 $L_0$。若在 $q=0,1,2$ 中首次执行 $L_0$，引理 22.4 的相应固定严格秩一伴随及 III 引理 14.4 给出一条共同合法补全历史，迫使该可靠正规形不能在这条历史上输出 $2$，故它必须继续到 $p$。在前三次 $N$ 后的前缀 $p_{\le3}=(K,100,16,u)$ 处若执行 $L_0$（切口 $q=3$），同一引理的 $q=3$ 见证固定一个伴随来源；用中点新报告及重复坐标的同一报告表，确定性逐前缀归纳使正规形在该伴随上作出与 $Q_s$ 相同的有限停止和输出，违反可靠性。若先执行一次 $N$，所取得报告可取为共享旧报告 $2$，于是到达 $p$；随后在 $q=4$ 执行 $L_0$，引理的 $q=4$ 见证对 $Q_t$ 给出同样矛盾。III 定理 14.2 的固定报告表只使用所选切口的共同补全坐标；$q=4$ 的末坐标沿用旧报告，零累计矩阵进入永久零状态，所以重读、再次 $L_0$、无限长尾均不产生新分支。故单位尺度下每个可靠成员至多覆盖缩放族中的一个参数。

逐来源九报告协议给出上界，参数条目 $(Q_s)_{0,2}=3-s$ 给出不同性和下界；任意有限族遗漏缩放族中的另一个参数，故全域覆盖数为无穷。∎

### 定理 22.6（有限维正性保持递归）

第 22.2 节的严格正族及其有限切口见证可递归推进到每个有限维 $k\ge5$，但递归必须携带统一有界不变量；这一本身不补足高维同容限覆盖下界所需的参数重叠与逐切口不相容性证明。

**递归假设。** 在维数 $n\ge4$，参数区间固定为 $[0,1/2]$，参数函数连续，已有族的行形为

$$
R_s^{(n)}=\begin{pmatrix}r_s\\w_s\\c_{2,s}r_s\\\vdots\\c_{n-1,s}r_s\end{pmatrix},
$$

其中 $r_s,w_s\in\mathbb R_{>0}^{n}$、$c_{j,s}>0$，$r_{n-1,s}=1$、$w_{n-1,s}=8$，纯 $N$ 数据与 $s$ 无关，首两行与末两列组成的 $2\times2$ 子式非零；每个切口的 $\mathsf C_q(R_s,u_{q,s})$ 都带有与其前缀配对的严格正见证，其坐标有统一上界 $X_n,V_n$，且最后 $v$ 坐标统一下界 $m_n>0$。另假设已有族具有连续的两项严格正外积分解，且其因子在参数区间上有统一正下界。

定义

$$
H_s=1+\sum_{j=2}^{n-1}c_{j,s},\qquad
T_s=w_{0,s}+\sum_{j=2}^{n-1}c_{j,s}r_{j-1,s},
$$

并令 $H_* ,T_*,W_*$ 分别为 $H_s,T_s,w_{n-1,s}$ 在参数区间上的上界。选择有限常数

$$
B>\max(2,H_*+W_*+1),\qquad
K'>\max\bigl(2(B+T_*),\ B H_*+1+(n-1)X_nV_n\bigr).
$$

由 $K'>2(B+T_*)$ 有 $\mu'_s=K'-B-T_s>B>0$。置

$$
r'_s=(B,r_s),\qquad w'_s=(1,w_s),\qquad
\mu'_s=K'-B-T_s,
$$

并在新矩阵最后追加行 $\mu'_sr'_s$，其余倍数行具体改为 $c_{j,s}r'_s$（$2\le j\le n-1$）。

则存在一个新的统一有界不变量 $X_{n+1},V_{n+1},m_{n+1}$，使同样的递归假设在维数 $n+1$ 成立，且新纯 $N$ 数据为 $(K',a_0,\ldots,a_{n-1})$。

**证明。** 因 $r_{n-1}=1$，新初读恰为

$$
B+T_s+\mu'_s=K'.
$$

对 $i\ge1$，新上对角和逐项等于旧的 $a_{i-1}$。旧切口 $q$ 提升为新切口 $q+1$：若旧伴随为 $(x,v)$，令

$$
v'=(\beta_{q,s},v),\qquad
x'=(x_0,\ldots,x_{n-1},x_n'),
$$

其中 $\beta_{q,s}$ 是新 $b^{(q+1)}$ 的首坐标，并取

$$
x_n'=\frac{K'-x_0\beta_{q,s}-\sum_{h=1}^{n-1}x_hv_{h-1}}{v_{n-1}}.
$$

按行移位直接有

$$
b^{(q+1)}_0=\beta_{q,s},\qquad
b^{(q+1)}_{j+1}=b^{(q)}_j.
$$

旧归一化正好成为新归一化，且对所有 $i\ge1$ 有 $A'_i=A_{i-1}$；新首坐标误差为零，旧约束全部保留。由 $\beta_{q,s}\le BH_*+1$、$x_h\le X_n$、$v_h\le V_n$ 和 $K'$ 的选择，$x_n'>0$。

新 $q=0$ 时，$b_n^{(0)}=K'-B-T_s+H_s+w_{n-1,s}<K'$，而

$$
b_0^{(0)}=B(K'-B-T_s+H_s)+1>K'.
$$

由 $K'>2(B+T_*)$ 及 $B>2$，并用 $H_s>0$，可得

$$
b_0^{(0)}-K'\ge (B-2)(B+T_s)+1>0.
$$

所以 III 命题 9.6 给出严格正的 $x$ 使 $\sum x_h=1$ 且 $A_0=K'$。连续正参数在紧区间上给出有限的 $V_{n+1}$，而新最后坐标保持正并有统一下界 $m_{n+1}>0$；取 $X_{n+1}=\max(1,X_n,K'/m_n)$ 即可。首两行末两列的子式只发生列移位，仍非零；在紧区间上取足够小的统一 $\alpha$，两项严格正外积分解继续成立。安全切口的共同来源判据由 $A'_i=A_{i-1}$ 的投影得到，逐维保持。归纳完成。∎

### 约定 22.7（边界与自校准读数）

第 22.5 节是一个具体五维定理；第 22.6 节的高维结论使用其明确递归假设，未宣称常数对 $k\to\infty$ 一致有界。严格正性、固定正容限、完整环境域可靠性、任意相关误差、单轨迹、共享末坐标和预选覆盖量词均不可删除。

“把四维矩阵补一行”不是自动有效的校准。若直接把最后一行取为 $r_s$ 而把初读常数保持为 $K$，末次切口会出现统一伴随，导致一个固定协议覆盖整族；这说明新增坐标必须同时保持纯 $N$ 数据、所有早切口和晚切口的共同来源障碍。第 22.2--22.6 节保存的是这种经过切口检查的正性保持构造，不是维数单调性的推论。

这些结论不推出非负闭包、$\varepsilon=0$、随机协议、在线选择器、有效实可行性、有限位复杂度或本族九报告的最优性。

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

## 15. 四世界原根障碍的两个恒定且不同的首响应

**定理 15.1（另一首响应恒定的三世界不能在首动作后失败六层）。**
Let $T$ consist of three complete worlds in the domain of Definition 1.1,
with pairwise different sources and a common initial reading $a_0$.
Suppose that, for each $E\in\{J,M\}$, the function

$$
W\longmapsto \delta_W+g_W(1)\operatorname{tr}(EP_W)
\tag{15.1}
$$

is constant on $T$, with possibly different constants for the two
actions. For either first action $F$, let $H_F$ be its resulting
two-reading history. Then $\neg L_6(T,H_F)$.

Proof. We use the actual-history pair and product results of
[*FIB 同父历史的采样零层坍缩与失效核心*, Lemmas 22.1–22.3](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md).
In particular a two-world $L_s$ at clock $k$, for $s\ge3$, has common
drift, different sources and gain roots at $k+2,\ldots,k+s$; a
two-world $L_5$ is impossible. The four length-two products

$$
\mathscr S_2=\{I,MJ,JM,M^2\}
\tag{15.2}
$$

linearly span all matrices, and their common-trace equations satisfy
$\operatorname{tr}(BH)=c$ for all $B\in\mathscr S_2$ exactly when
$H=cE_{11}$. Products of each fixed length at least three also
linearly span all matrices. These facts retain the actual prefix
matrix and the original clocks.

We also use the following polynomial consequence only after its
roots and drift have been established. A nonzero polynomial of
degree at most three with three distinct positive roots $r_1,r_2,r_3$
is $c(t-r_1)(t-r_2)(t-r_3)$. Its value $g(0)=a_0-\delta$
uniquely fixes $c$. If that value is zero, the polynomial would
have four distinct roots and the branch is impossible. Otherwise
its samples outside the three specified roots are nonzero. Thus
these uses of a common entire gain do not assume exact degree
three or exclude lower-degree gains in advance.

Assume $L_6(T,H_F)$. Each second action must retain the entire $T$
with $L_5$: a smaller nonempty losing child would be a forbidden
two-world $L_5$ or violate the cardinality guard. Thus all worlds
share both second responses after $F$.

Two members with the same entire gain $G$, the same drift and
$G(1)G(2)\ne0$ would consequently have equal traces against
$I,J,M,JF,MF$. These matrices span all matrices: use
$\{I,J,M,MJ\}$ when $F=J$ and $\{I,J,M,JM\}$ when $F=M$.
Hence their sources, and then their complete targets, would be equal.
We will use this consequence only after establishing the common
gain and its stated nonzero samples.

At either clock-two history, a two-world losing third child would
have $L_4$ at clock three. Its gains would have roots $5,6,7$ and
its drifts would agree. The common initial reading fixes the entire
gain to one scalar multiple of $(t-5)(t-6)(t-7)$. A zero scalar is
illegal; otherwise its first and second samples are nonzero. The
preceding trace argument excludes that pair. Each third action must
therefore retain the entire $T$, with $L_4$.

For distinct $W,Z\in T$, put

$$
D_3=g_W(3)P_W-g_Z(3)P_Z,\qquad c=\delta_Z-\delta_W.
\tag{15.3}
$$

The four retained length-three histories beginning with $F$ give
$FD_3=cE_{11}$ by (15.2). This equation forces $c=0$. Indeed set
$X=g_W(3)FP_W$ and $Y=g_Z(3)FP_Z$. The matrices $FP_W,FP_Z$
are strictly positive and rank one. If either scalar is zero,
$X_{22}=Y_{22}$ forces both to be zero. Otherwise their common
$(2,2)$ entry is nonzero, and their equal $(1,2),(2,1),(2,2)$
entries determine the $(1,1)$ entry by the rank-one identity.
Thus $X=Y$ in both cases. Since $F$ is invertible, $D_3=0$.
Taking traces and then using $P_W\ne P_Z$ gives

$$
\delta_W=\delta_Z=\delta,\qquad
g_W(3)=g_Z(3)=0.
\tag{15.4}
$$

Each fourth action now needs an $L_3$ child. A two-world child
would have gain roots $6,7$ in addition to the already proved root
$3$. Common drift and initial reading again fix one common entire
gain, nonzero at $1,2$, and the trace argument excludes the pair.
Thus all fourth children retain $T$. Their matrices are $BF$ for
all length-three products $B$. Common drift and the full matrix
span imply $g_W(4)P_W=g_Z(4)P_Z$, so all fourth samples are zero.

A two-world fifth child would have $L_2$ at clock five. Write $Q$
for its actual clock-five matrix. Equality on all its length-two
continuations, with the common drift already established, gives

$$
\operatorname{tr}\!\left(BQ[g_W(7)P_W-g_Z(7)P_Z]\right)=0
\quad(B\in\mathscr S_2).
\tag{15.5}
$$

The span in (15.2) first gives
$Q[g_W(7)P_W-g_Z(7)P_Z]=0$. Invertibility of $Q$ and the
trace-one sources give equal seventh samples; a nonzero common
sample would identify the two sources. Both samples therefore
vanish. Roots $3,4,7$ and the common initial value then fix a common
entire gain, again nonzero at $1,2$. This excludes the pair. Every
fifth action therefore retains $T$, with $L_2$. The retained
length-five histories beginning with $F$ and the full span of
length-four products force all fifth samples to vanish. Roots
$3,4,5$ now fix the same entire gain on all of $T$; its first two
samples are nonzero. The trace argument identifies all its sources,
contrary to their pairwise difference.

Every pair used above is a complete actual response child whose
cardinality is exactly two. Every other losing child has to be the
original three-world set. Thus all shared histories used in the
span arguments concern these same fixed worlds; no failure is
transferred to an arbitrarily selected nonterminal pair. ∎

**引理 15.2（首根三元层的两种完整排除）。**
Let $T$ consist of three worlds with pairwise different sources,
common drift $\delta$ and common initial reading $a_0$.

1. If $T$ realizes an entire history $H$ through clock two and every
   gain has root $1$, then $\neg L_5(T,H)$.
2. If $T$ realizes an entire history $H$ through clock three and
   every gain has roots $1,2$, then $\neg L_4(T,H)$.

Proof. Retain the pair and product facts cited in Theorem 15.1.
We first give three elementary trace consequences used inside the
proof. Put

$$
K=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\tag{15.6}
$$

The simultaneous kernel of $S\mapsto
(\operatorname{tr}S,\operatorname{tr}(JS),\operatorname{tr}(MS))$
is $\mathbb RK$: the first equation fixes the diagonal sum, the
second the off-diagonal sum, and subtracting the second from the
third gives $S_{22}=0$. In a fixed affine fiber of these three
traces, rank-one members have the form $S_0+tK$ and satisfy

$$
\det(S_0+tK)=\det S_0+((S_0)_{12}-(S_0)_{21})t+t^2=0.
\tag{15.7}
$$

The coefficient of $t^2$ is one, so there are at most two such
matrices, including repeated-root cases. Consequently, for
$n\in\{2,3\}$, if one entire gain $G$ and drift are fixed and
$G(n)G(n+1)\ne0$, at most two
different sources can share the clock-$n$ response at a matrix $Q$
and both clock-$(n+1)$ responses. Here $Q$ is any actual prefix,
and the three traces are those of $QP$. The actual $Q$ is
invertible, so distinct sources give distinct matrices $QP$.

If $G(n),G(n+1),G(n+2)$ are all nonzero, two worlds with this
common gain and drift are identical whenever they share the
clock-$n$ reading, both next-action readings, and both readings
after one fixed next action. The relevant matrices, after right
multiplication by $Q$, contain $I,J,M$ and either $MJ$ or $JM$,
so span all matrices. The case $n=2$ is the four-trace argument of
[the same source, Lemma 28.1](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md).
The displayed span also proves the case $n=3$ using its actual
clock-three $Q$ and the nonzero samples $G(3),G(4),G(5)$;
no history or clock is reset.

Finally, a different-source pair with common drift and $L_2$ at
clock five has seventh roots. Equation (15.5), with its own actual
$Q$, proves this without invoking the $s\ge3$ pair restriction.

For part 1, assume $L_5(T,H)$ and let $Q$ be the clock-two matrix.
Every third action retains all of $T$: a two-world $L_4$ child
would require roots $5,6,7$ in addition to root $1$, impossible for
a nonzero cubic-or-lower gain.

Suppose a fourth child were a two-world $L_3$. Its gains have
roots $1,6,7$ and, by the common initial value and drift, are one
common entire polynomial $G$. A zero scalar is illegal. Otherwise
$G(2)G(3)G(4)\ne0$. Every possible two-world $L_3$ fourth child
must use this same $G$, since its roots $1,6,7$, drift and initial
value are fixed independently of the action. The shared clock-two
and both clock-three responses and (15.7) show that at most two
members of $T$ can have this $G$. Therefore there is at most one
possible two-world $L_3$ fourth-child pair in $T$. At the chosen
clock-three history the other fourth action retains either that
same pair or all of $T$.
The pair thus shares both fourth responses after that third action.
The four-trace consequence with $n=2$ identifies the pair, a
contradiction. All fourth children consequently retain $T$.
At clock four the full length-two span from $Q$, with common
drift and different sources, forces $g_W(4)=0$ for every $W\in T$.

If a fifth child were a two-world $L_2$, its seventh roots would
combine with roots $1,4$ to fix a common entire $G$, nonzero at
$2,3,5,6$. For this pair write $S=Q(P_W-P_Z)$. The common
clock-two and both clock-three readings give $S=hK$, with $h\ne0$.
Let $B$ be the actual three-action product from clock two to clock
five along this child. Its clock-five reading and both clock-six
readings give $BS=h'K$. Since $B$ and $S$ are invertible, $h'\ne0$,
and therefore

$$
B=(h'/h)I.
\tag{15.8}
$$

This is impossible: three atoms have determinant $-1$, whereas
a nonzero scalar matrix has positive determinant. Thus no fifth
child is a pair, and every fifth action retains all of $T$.
The full length-three span from $Q$ forces all fifth samples to
vanish. Roots $1,4,5$ now fix a common entire gain on $T$, nonzero
at $2,3$. Its shared three traces contradict the at-most-two
bound (15.7). This proves part 1.

For part 2, assume $L_4(T,H)$ and now let $Q$ be its clock-three
matrix. A fourth pair would have $L_3$ and roots $6,7$ in addition
to roots $1,2$, so every fourth action retains $T$. A fifth pair
would have $L_2$ and hence root $7$. Roots $1,2,7$ fix a common
entire $G$, nonzero at $3,4,5$. The clock-three and both clock-four
readings, together with (15.7), permit at most two members with
this $G$. Every possible fifth pair must use that same polynomial,
because the roots $1,2,7$, drift and initial value are fixed.
Hence there is at most one such fifth pair. At its clock-four
parent the other fifth action retains the same pair or all of
$T$. Thus both fifth responses after that fourth action agree
on the pair. The four-trace consequence with $n=3$ identifies it,
a contradiction. Every fifth action retains all of $T$.
The full length-two span from $Q$ then forces all fifth samples
to vanish. Roots $1,2,5$ fix a common entire gain on $T$, nonzero
at $3,4$, and (15.7) again excludes three different sources.

In each use of three specified roots, the scalar is fixed by
$g(0)=a_0-\delta$. If that value is zero, the three positive
roots would force a fourth root and the zero polynomial, so the
corresponding pair or triple is already impossible. Otherwise
the displayed nonzero samples follow from the specified roots.
All divisions above are confined to these nonzero branches. ∎

**定理 15.3（恰四世界原根失败的双恒定非对角首响应）。**
For any $a_0\in\mathbb R$, let $K$ be a set of exactly four
different complete worlds in the entire initial-$a_0$ fiber.
If $L_7(K,(a_0))$, there are real numbers $j,m$, with $m\ne j$,
such that

$$
\begin{aligned}
\delta_W+g_W(1)\operatorname{tr}(JP_W)&=j,\\
\delta_W+g_W(1)\operatorname{tr}(MP_W)&=m
\end{aligned}
\qquad(W\in K).
\tag{15.9}
$$

The sources are pairwise different. Writing $\ell=m-j$, every
member has unique $x_W,y_W>0$ satisfying

$$
\begin{gathered}
P_W=\frac1{1+x_Wy_W}
 \begin{pmatrix}x_Wy_W&x_W\\y_W&1\end{pmatrix},\qquad
g_W(1)=\ell(1+x_Wy_W),\\
\delta_W=j-\ell(x_W+y_W),\qquad
g_W(0)=a_0-j+\ell(x_W+y_W).
\end{gathered}
\tag{15.10}
$$

In particular all first gain samples are nonzero and have the
same sign. The assertion concerns the whole fixed four-world
support, including members not assigned to a particular subtree
in a terminal-slot representation.

Proof. The necessary source difference is
[the same source, Theorem 30.1](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md).
Its Theorem 25.2 gives at least one first action whose response
is constant on all of $K$, with an $L_6$ child equal to $K$.
If the other first action were nonconstant, its losing child
would have exactly three worlds: the pair restriction excludes
two, and nonconstancy excludes four. This triple has $L_6$ at
that actual first history, pairwise different sources, and both
first response functions constant on it. Theorem 15.1 excludes
it. Hence both first responses are constant on $K$. Their only
nonempty first response children are $K$, each with $L_6$.

Suppose their constants were equal, $j=m$. Their difference is
$g_W(1)(P_W)_{22}$, so positivity forces

$$
g_W(1)=0,\qquad\delta_W=j\quad(W\in K).
\tag{15.11}
$$

At each first history, every losing second child has $L_5$.
It cannot be a pair by the pair restriction, or a triple by
Lemma 15.2(1). It is therefore all of $K$. Thus all four
length-two histories retain $K$. Their full matrix span and
common drift force $g_W(2)P_W$ to be independent of $W$.
Different trace-one sources force all these samples to be zero.

Every losing third child has $L_4$. A pair would have roots
$5,6,7$ in addition to roots $1,2$; a triple is excluded by
Lemma 15.2(2). Hence every third action also retains all of $K$.
The full length-three matrix span forces all third gain samples
to vanish. Roots $1,2,3$ and the common initial value then fix
one common nonzero entire gain

$$
G(t)=\frac{j-a_0}{6}(t-1)(t-2)(t-3)
\tag{15.12}
$$

on $K$; if $j=a_0$, legality has already been contradicted.
This gain is nonzero at $4,5,6,7$. After any clock-four
reading, the next three actual actions $J,M,J$ distinguish all
sources compatible with that reading: after factoring out the
known nonzero samples and common drift, the four matrices are

$$
Q,\quad JQ,\quad MJQ,\quad JMJQ,
\tag{15.13}
$$

where $Q$ is the actual clock-four matrix. They span all
matrices, since $\{I,J,MJ,JMJ\}$ does and $Q$ is invertible.
For completeness, the span follows from $MJ-I=E_{21}$,
$J-E_{21}=E_{12}$, $JMJ-J=E_{11}$ and $I-E_{11}=E_{22}$.
If a clock-four child had $L_3$, its recursion along these three
fixed next actions would retain a terminal pair agreeing at clocks
$4,5,6,7$ and on all earlier ancestors. Dividing only by the
already nonzero values of $G$ gives equal traces against (15.13),
so the sources agree. The common entire gain and drift then make
the complete worlds equal, contradicting the terminal guard.
Thus no clock-four child has $L_3$, contradicting the retained
$L_4$ at clock three and proving $m\ne j$.

Finally $\ell=g_W(1)(P_W)_{22}\ne0$, so
$g_W(1)/\ell=1/(P_W)_{22}>0$. The rank-one matrix
$(g_W(1)/\ell)P_W$ is strictly positive and has bottom-right
entry one. It therefore has the unique form
$\left(\begin{smallmatrix}xy&x\\y&1\end{smallmatrix}\right)$,
$x,y>0$. Taking traces gives $g_W(1)/\ell=1+xy$;
the first-$J$ equation and the initial reading give the other
identities in (15.10).

This is a repository-derived necessary condition. The two inherited
necessary conditions cited above are used with their exact
four-world hypotheses. The added conclusions
are simultaneous constancy of both first functions and inequality
of their constants, obtained by excluding their actual three-world
children and equal-response case. No subset of a larger failing
family is asserted to inherit $L_7$. In particular (15.9)–(15.10)
are necessary conditions on four-world original-root obstructions,
not a source tuple satisfying all guards of Theorem 13.3 and not
an eight-reading decoder on the unrestricted domain. ∎

## 追加锚（本行以下为增补区）
## 16. 混合二步历史的三世界排除与四世界恒定性

**定理 16.1（双首响应约束下的混合时钟二三元排除）。**
Fix arbitrary $a_0,j,m,b\in\mathbb R$, with $\ell=m-j\ne0$,
and a chronological word $v=E_1E_2\in\{JM,MJ\}$. Let $T$ consist
of exactly three complete worlds in the entire domain of Definition
1.1, with pairwise different sources. Suppose every $W\in T$ has
initial reading $a_0$, first-$J$ response $j$, first-$M$ response $m$,
and clock-two response $b$ at the actual matrix $Q=E_2E_1$.
Writing $r_J=j$, $r_M=m$ and

$$
H_v=(a_0,E_1,r_{E_1},E_2,b),
\tag{16.1}
$$

one has $\neg L_5(T,H_v)$, with all descendants on the original
clocks three through seven. Both first-response equations are
hypotheses about the same three fixed worlds, not two observations
acquired by a protocol.

Proof. We use the pair and product facts of
[*FIB 同父历史的采样零层坍缩与失效核心*, Lemmas 22.1–22.3](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md),
with the actual prefix matrix retained. A two-world $L_4$ at clock
three has common drift and gain roots $5,6,7$; a two-world $L_3$
at clock four has common drift and gain roots $6,7$. The products
$\mathscr S_2=\{I,MJ,JM,M^2\}$ span all matrices, their equal-trace
certificate is $\operatorname{tr}(BS)=c$ for every
$B\in\mathscr S_2$ if and only if $S=cE_{11}$, and the length-three
products have full affine span. All these statements concern
actual left products and the stated original clocks.

The calculation giving (15.10) uses only the two first-response
equations and $\ell\ne0$, so it applies to each member here without
a four-world hypothesis. More explicitly, their difference gives
$g_W(1)(P_W)_{22}=\ell$. Positivity and rank one therefore give
unique coordinates

$$
\begin{gathered}
R_W=\begin{pmatrix}x_Wy_W&x_W\\y_W&1\end{pmatrix},\qquad
q_W=1+x_Wy_W>0,\qquad s_W=x_W+y_W,\qquad x_W,y_W>0,\\
P_W=R_W/q_W,\qquad h_W(t)=g_W(t)/q_W,\qquad
h_W(1)=\ell,\\
\delta_W=j-\ell s_W,\qquad
h_W(0)=(a_0-\delta_W)/q_W.
\end{gathered}
\tag{16.2}
$$

Each $h_W$ is one entire nonzero real polynomial of degree at most
three. At every actual matrix $A$ and original clock $i$ the read
is exactly $\delta_W+h_W(i)\operatorname{tr}(AR_W)$.
Set

$$
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\qquad
U=JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad
\Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix}.
\tag{16.3}
$$

Thus chronological $JM$ has matrix $L$ and chronological $MJ$
has matrix $U$. Suppressing the world subscript and putting
$w=xy=q-1$, the needed traces are

$$
\begin{array}{c|ccc}
Q&\operatorname{tr}(QR)&\operatorname{tr}(JQR)&\operatorname{tr}(MQR)\\ \hline
L&q+x&w+s&w+s+x+1\\
U&q+y&s+1&s+2
\end{array}.
\tag{16.4}
$$

We also use the kernel calculation (15.6): the three equations
$\operatorname{tr}S=\operatorname{tr}(JS)=\operatorname{tr}(MS)=0$
are equivalent to $S\in\mathbb R\Omega$. For a common nonzero
entire gain $G$, common drift, and $G(1)G(2)\ne0$, equality of
the initial, both first, and the selected mixed second reads
identifies the source. Indeed those equalities give equal traces
against $I,J,M,Q$, which span all matrices for either $Q=L$ or
$Q=U$, as in the proof of Theorem 15.1. This observation will be
used only after its common gain and nonzero samples are established.

Assume $L_5(T,H_v)$. A selected losing third child has $L_4$ and
cardinality at least two. If it were a pair, its roots $5,6,7$
and common initial value and drift would fix one common entire
gain $G$. If $G(0)=0$, four roots would make that gain illegal;
otherwise $G(1)G(2)\ne0$. The preceding four-trace observation
identifies the pair, contrary to the guard. Hence each third action
retains the entire $T$ with $L_4$. In particular both third-response
functions at $JQ,MQ$ are constant on these same three worlds.

We next exclude every selected two-world fourth child. Such a
child would have $L_3$, common drift $\delta$, and roots $6,7$.
For its two members write $c=a_0-\delta$. Their sums
$s=(j-\delta)/\ell$ agree by (16.2); the third member is not
assumed to have this drift. Let $E$ be the third action and $F$
the fourth action of this child, so its actual matrix is $FEQ$.

First take $Q=L$. By (16.4), the difference of the two shared
third responses is $h_W(3)(x_W+1)$. If this difference is nonzero,
the ratio of the third-$J$ response minus $\delta$ to this
difference is, for both endpoints,

$$
\frac{x_W(s-x_W)+s}{x_W+1}
=s+1-x_W-\frac1{x_W+1}.
\tag{16.5}
$$

As a function of $x>0$ with $s$ fixed, its derivative is
$-1+(x+1)^{-2}<0$. Thus the endpoints have the same $x$, then the
same $y=s-x$, contradicting different sources. If the difference
is zero, both gains have the additional root $3$. Roots $3,6,7$
and their common value $g(0)=c$ fix a common entire gain; $c=0$
is already illegal and otherwise its samples at $1,2$ are nonzero.
The four-trace observation again identifies the pair. This excludes
all fourth pairs for $Q=L$.

Now take $Q=U$. The shared third-response difference and (16.4)
give a common value $h_W(3)=k$ for the two endpoints. Both
normalized polynomials have the same values at $1,3,6,7$, namely
$\ell,k,0,0$. Uniqueness of cubic-or-lower interpolation makes
them one common entire polynomial $H$.

If $c\ne0$, the equations $q_WH(0)=c$ give the same $q$ at both
endpoints. Their common $s,q$ imply
$R_W-R_Z=\eta\Omega$ with $\eta\ne0$, since the sources differ.
If $H(2)\ne0$, the shared clock-two reading and (16.4) give the
same $q+y$, hence the same $y,x$ and source, a contradiction.
If $H(2)=0$, the nonzero polynomial $H$ has roots $2,6,7$, so
$H(4)H(5)\ne0$. Equality at clock four and both clock-five
actions in this pair's $L_3$ gives

$$
FEU(R_W-R_Z)\in\mathbb R\Omega.
\tag{16.6}
$$

Since $R_W-R_Z=\eta\Omega$ is invertible, (16.6) forces $FEU$
to be a scalar matrix. This is impossible. For any nonnegative
invertible matrix $B$, $(BU)_{12}=B_{11}+B_{12}>0$; every actual
left product $B$, including $FE$, has these properties.

If $c=0$, then $H$ has roots $0,6,7$ and $H(1)=\ell\ne0$.
In particular $H(2)H(4)H(5)\ne0$. Write $t=y_W-y_Z$. Equality
of $s$ and of the clock-two traces $q+y$ gives

$$
R_W-R_Z=t\begin{pmatrix}-1&-1\\1&0\end{pmatrix},\qquad
U(R_W-R_Z)=-t\Omega,\qquad t\ne0.
\tag{16.7}
$$

The last inequality follows because $t=0$ would also fix $x$.
Equality at clock four and both fifth actions, divided only by
the already nonzero $H(4),H(5)$, now forces $FE$ to be a scalar
matrix. Among $\mathscr S_2$ only $I=JJ$ is scalar. Thus any
possible fourth pair for $Q=U$ must occur with third action $J$
and fourth action $J$.

At that same third-$J$ history, recursion also requires a losing
fourth-$M$ child. It cannot be a pair by the preceding necessary
condition, so its full response intersection is the entire $T$.
The putative fourth-$J$ pair therefore also shares the fourth-$M$
response. This contradicts (16.7), because

$$
\operatorname{tr}\bigl(MJU(R_W-R_Z)\bigr)
=-t\operatorname{tr}(MJ\Omega)=-t\ne0,
\tag{16.8}
$$

and $H(4)\ne0$. No drift assumption on the third member was used.
This excludes the final fourth-pair possibility.

Consequently each third action and each subsequent fourth action
has its selected losing child equal to $T$, the latter with $L_3$.
For different $W,Z\in T$ put
$D_4=g_W(4)P_W-g_Z(4)P_Z$ and $c_{WZ}=\delta_Z-\delta_W$.
The four retained clock-four histories give

$$
\operatorname{tr}(BQD_4)=c_{WZ}\quad(B\in\mathscr S_2),\qquad
QD_4=c_{WZ}E_{11}.
\tag{16.9}
$$

The positivity argument in the proof of Theorem 15.1 applies here
as well. The matrices $X=g_W(4)QP_W$ and $Y=g_Z(4)QP_Z$ have
rank at most one and agree in entries $(1,2),(2,1),(2,2)$. Since
$QP_W,QP_Z$ are strictly positive, a zero common $(2,2)$ entry
makes both scalars zero. Otherwise the rank-one identity determines
the remaining $(1,1)$ entry, so again $X=Y$. Thus $c_{WZ}=0$
and $D_4=0$. Taking traces and using different trace-one sources
forces both fourth samples to be zero. Varying the pair proves

$$
\delta_W=\delta\quad(W\in T),\qquad g_W(4)=0\quad(W\in T).
\tag{16.10}
$$

From now on $s=(j-\delta)/\ell$ and $c=a_0-\delta$ are common
to all three members, and $h_W(0)=c/q_W$.

A selected fifth child has $L_2$. If it is a pair, write $A$ for
its actual clock-five matrix. Common drift and the exact pair
recursion give

$$
\operatorname{tr}\bigl(BA[g_W(7)P_W-g_Z(7)P_Z]\bigr)=0
\quad(B\in\mathscr S_2).
\tag{16.11}
$$

The linear span, invertibility of $A$, and the different trace-one
sources imply $g_W(7)=g_Z(7)=0$. This use of $L_2$ is separate
from the $s\ge3$ pair lemma.

For $Q=L$, the argument (16.5) now applies to every pair in $T$.
A nonzero common third-response difference would identify all
sources, so that difference must be zero and all gains have root
$3$. A fifth pair would therefore have roots $3,4,7$, common drift
and common initial value. Its entire gain is common, illegal if
$c=0$, and otherwise nonzero at $1,2$; the four-trace observation
excludes it. Hence all fifth actions retain the whole $T$ with
$L_2$. Their eight actual clock-five matrices are $BQ$ for all
length-three products $B$. Common drift and the full span force
all fifth samples to be zero, by the same trace-one argument used
in (16.10). Roots $3,4,5$ and the common initial value then fix
one common entire gain on $T$, nonzero at $1,2$ unless already
illegal. The four-trace observation identifies every pair. This
contradicts the three different sources and finishes the case $Q=L$.

For $Q=U$, (16.4) gives one common value $h_W(3)=k$ on all of
$T$. Suppose a fifth pair exists. Its normalized polynomials agree
at $1,3,4,7$, so they are one common entire $H$.
If $c\ne0$, the same equations $q_WH(0)=c$ fix $q$ for this pair,
and its matrix difference is $\eta\Omega$, $\eta\ne0$.
If $H(2)\ne0$, the clock-two reading identifies its source as
before. If $H(2)=0$, roots $2,4,7$ give $H(5)H(6)\ne0$.
The clock-five reading and both sixth readings give
$A(R_W-R_Z)\in\mathbb R\Omega$, forcing $A$ scalar. But
$A=BU$ for a nonnegative invertible actual product $B$, so its
$(1,2)$ entry is positive, a contradiction.

If $c=0$, all three normalized polynomials already agree at
$0,1,3,4$. They are one common entire $H$. The root $7$ of the
putative pair is therefore a root of this same $H$ for all three
worlds. Its roots $0,4,7$ and $H(1)=\ell\ne0$ give $H(2)\ne0$.
The common clock-two reading fixes $q_W+y_W$ on $T$. With
$x_W=s-y_W$, every $y_W$ satisfies one fixed quadratic equation

$$
q_W+y_W=1+(s+1)y_W-y_W^2=C.
\tag{16.12}
$$

There are at most two such real $y_W$ and each fixes $x_W$ and
the source. This contradicts three different sources. Thus no
fifth pair exists in either $c$ case.

All fifth actions consequently retain the entire $T$. As in the
$Q=L$ case, the length-three span forces $g_W(5)=0$ for every
member. If $c\ne0$, the normalized polynomials now agree at
$1,3,4,5$, so are one common $H$. The initial equations
$q_WH(0)=c$ fix $q$ on $T$. The common $s,q$ leave at most two
ordered positive solutions of $x+y=s$, $xy=q-1$, again too few.
If $c=0$, the normalized polynomials agree at $0,1,3,4$ and their
common $H$ also has root $5$. Roots $0,4,5$ give $H(2)\ne0$,
and (16.12) again leaves at most two sources. This final
contradiction proves the theorem.

At each nonterminal node above, a selected losing response is an
entire intersection with the current support. Its cardinality
forces either an actual pair or all three worlds; no arbitrary
nonterminal pair is extracted. A fourth sibling retained on all
three worlds contains the pair being compared, which is the exact
reason it constrains that pair in (16.8). All polynomials remain
the original entire gains, or their fixed positive rescalings in
(16.2), across every ancestor and descendant. Three specified
roots force exact degree three only within the corresponding
nonzero branch; no initial sign, degree or root restriction is
imposed. ∎

**推论 16.2（恰四世界原根失败的两个混合二步响应都恒定）。**
For any $a_0\in\mathbb R$, let $K$ consist of exactly four distinct
complete worlds in the entire initial-$a_0$ fiber. If
$L_7(K,(a_0))$, then for each chronological word
$v=E_1E_2\in\{JM,MJ\}$ there is a real $b_v$ such that

$$
\delta_W+g_W(2)\operatorname{tr}(E_2E_1P_W)=b_v
\qquad(W\in K).
\tag{16.13}
$$

Moreover $L_5(K,(a_0,E_1,r_{E_1},E_2,b_v))$ holds for both
words, with $r_J=j$, $r_M=m$ the unequal constants of Theorem
15.3. No equality or inequality between $b_{JM}$ and $b_{MJ}$
is asserted.

Proof. Theorem 15.3 supplies pairwise different sources and both
constant first responses $j\ne m$ on $K$. For each first action
$E_1$, its only nonempty response intersection within $K$ is
exactly $K$, so recursion gives
$L_6(K,H_{E_1})$, where $H_{E_1}=(a_0,E_1,r_{E_1})$.
For the selected mixed second action $E_2$, recursion supplies a
real $b$ with the full intersection

$$
C=K\cap\mathcal F(H_{E_1},E_2,b),\qquad
L_5(C,(H_{E_1},E_2,b)).
\tag{16.14}
$$

The stopping guard gives $|C|\ge2$. A two-world $L_5$ at clock
two is impossible by the same source, Lemma 22.3. If $|C|=3$,
this literal $C$ has all the hypotheses of Theorem 16.1: its
sources differ, it inherits both first-response equations and the
initial reading, and every member realizes the same mixed second
history with response $b$. That theorem excludes its $L_5$.
Thus $|C|=4$ and $C=K$. Set $b_v=b$. This proves (16.13) and
the stated retained $L_5$ for each word separately. The full
ambient fiber may contain other worlds; only its displayed
intersection with $K$ is used. ∎

The mixed-prefix triple exclusion and its four-world consequence
are repository-derived model-specific deductions. The pair root
classification, actual-product certificates, finite-game recursion,
polynomial interpolation and positive-source chart are reused
suppliers, not separate new general results. Theorem 15.3 and
its source-injection supplier, the cited core's Theorem 30.1,
retain their exact four-world original-root hypotheses in the
corollary. These conclusions do not decide whether any exactly-four
original-root $L_7$ support exists, do not extract one from a larger
or infinite support, and do not prove or refute an unrestricted
eight-read decoder. No gain direction, known gain plane, promise
detector or union inverse is supplied. No external-priority claim
is made.

## 追加锚（本行以下为增补区）
## 17. 双混合二步约束下的完整原根四世界排除

**定理 17.1（完整域的恰四世界原根排除）。** For every real
$a_0$ and every set $K$ of exactly four distinct complete worlds
in the initial-$a_0$ fiber of Definition 1.1,

$$
\neg L_7(K,(a_0)).
\tag{17.1}
$$

The assertion uses the guarded full-intersection recursion (1.3),
the original clocks zero through seven, and the entire domain
$\mathcal W_3$. In particular the gains may have any permitted
signs, lower degrees, sampled roots or repeated roots. No restriction
on deterministic policies is added.

Proof. Suppose that the displayed $L_7$ holds. Theorem 15.3 and
Corollary 16.2 supply four different sources, two constant first
responses $j,m$ with $\ell=m-j\ne0$, and constant responses at
both chronological mixed words $JM,MJ$. Each of those mixed
histories retains this same entire $K$ with $L_5$.

Apply the affine response change $z\mapsto(z-j)/\ell$ to every
history and world. This is a bijection of responses even when
$\ell<0$, preserves every actual action, original clock and full
response intersection, and replaces each world by
$(P,g/\ell,(\delta-j)/\ell)$. It preserves legality and $L_s$.
In the rest of the proof write $g,\delta$ for these transformed
gain and drift, and set $a=(a_0-j)/\ell$. The first-$J$ and
first-$M$ responses are now zero and one. The positive chart of
(15.10), with $q=1+xy$ and $s=x+y$, becomes

$$
\begin{gathered}
R=\begin{pmatrix}xy&x\\y&1\end{pmatrix},\qquad
P=R/q,\qquad x,y>0,\qquad h=g/q,\\
\delta=-s,\qquad h(1)=1,\qquad h(0)=(a+s)/q.
\end{gathered}
\tag{17.2}
$$

Each $h$ is one fixed entire polynomial of degree at most three.
A read at the actual matrix $A$ and clock $i$ is
$-s+h(i)\operatorname{tr}(AR)$. Let $u,v$ be the two normalized
mixed constants, with $u$ for chronological $JM$ and $v$ for
chronological $MJ$. With $L=MJ$ and $U=JM$ as in (16.3), all
four worlds satisfy

$$
u+s=h(2)(q+x),\qquad v+s=h(2)(q+y).
\tag{17.3}
$$

These are properties of the potential fixed support. Their use
does not acquire two mutually exclusive responses on a trajectory.

*Common drifts and two-step trace equations.* We first record two
consequences used below, always for members of this fixed $K$.
For two positive sources with the same $s$, write their coordinates
as $(x,y)$ and $(X,Y)$, where $x+y=X+Y=s$, and put
$q=1+xy$, $Q=1+XY$. Direct expansion gives

$$
(q+x)(Q+Y)-(Q+X)(q+y)
=(x-X)(2+s+xX+yY).
\tag{17.4}
$$

The last factor is strictly positive. If two different sources
have the same drift, they have this same $s$. If either second
gain sample is zero, (17.3) and positivity of its trace factors
make both samples zero and give $u=v=-s$. If neither is zero,
(17.3) gives equality of the two ratios $(q+x)/(q+y)$; (17.4)
would identify $x,X$ and then $y,Y$, contrary to different
sources. Consequently every equal-drift pair satisfies

$$
h_W(2)=h_Z(2)=0,\qquad u=v=\delta_W=\delta_Z.
\tag{17.5}
$$

For the second consequence reuse the actual-product certificate
of [the sampled-root core, Lemma 22.2](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md).
If two worlds share the four responses at clock $k+2$ following
all two-action continuations of an actual clock-$k$ matrix $A$,
put $D=g_W(k+2)P_W-g_Z(k+2)P_Z$ and
$d=\delta_Z-\delta_W$. That certificate gives

$$
AD=dE_{11}.
\tag{17.6}
$$

In this application the rank-one and positivity hypotheses force
$d=0$ and $D=0$. Indeed the matrices
$X=g_W(k+2)AP_W$ and $Y=g_Z(k+2)AP_Z$ have rank at most one
and equal entries in positions $(1,2),(2,1),(2,2)$. Every entry
of $AP_W,AP_Z$ is positive: an actual product is nonnegative
and invertible and has no zero row. If the common $(2,2)$ entry
of $X,Y$ is zero, both gain samples are zero. Otherwise
$X_{11}=X_{12}X_{21}/X_{22}$ and the same identity for $Y$
give $X=Y$. Thus (17.6) gives $d=0$ in either case; invertibility
of $A$ then gives $D=0$. Since the two trace-one sources differ,
taking traces of $D=0$ also forces both gain samples to be zero.
In particular an actual two-world $L_2$ at clock five has common
drift and seventh gain roots. Here the four continuation
responses need agree between the two worlds for each word;
the response for one word need not equal that for another word.

We also reuse [the same core, Lemmas 22.1 and 22.3](FIB_SAMPLED_ROOT_COLLAPSE_AND_SAME_PARENT_FAILURE_CORE.md):
a two-world $L_s$, $s\ge3$, has common drift and roots at its
original clocks $k+2,\ldots,k+s$. No such property is assigned
to an arbitrary pair inside a larger nonterminal losing set.

*A distinct-drift exclusion.* Three worlds with pairwise different
drifts cannot have $L_4$ at clock three. A selected fourth child
would have $L_3$; its cardinality cannot be two, by the preceding
pair result, so it must retain all three worlds. A selected fifth
child would have $L_2$; it likewise cannot be a pair, by (17.6),
so again retains all three. The four clock-five histories obtained
from the clock-three matrix therefore retain all three. Applied
to any two of them, (17.6) forces equal drifts, a contradiction.
All empty and singleton possibilities are excluded by the guards.

The original quartet cannot have pairwise different drifts either.
If it did, each selected third child after either mixed history
would have $L_4$ and cardinality four: two is excluded by the
pair result, and three by the preceding argument. Thus all four
mixed-prefix clock-three response functions are constant on $K$.
Their actual matrices and trace factors are

$$
\begin{array}{c|c|c}
\text{chronological word}&A&\operatorname{tr}(AR)\\ \hline
JMJ&JL=\left(\begin{smallmatrix}1&1\\1&0\end{smallmatrix}\right)&xy+s\\
JMM&ML=\left(\begin{smallmatrix}1&1\\2&1\end{smallmatrix}\right)&xy+s+x+1\\
MJJ&JU=M& s+1\\
MJM&MU=\left(\begin{smallmatrix}0&1\\1&2\end{smallmatrix}\right)&s+2
\end{array}.
\tag{17.7}
$$

Subtracting the last two constant responses makes $h(3)=k$
constant. If $k=0$, their reads make $s$ constant, contradicting
the different drifts. Otherwise comparison with the first response
makes $xy=w>0$ constant. The last two responses include
$k+(k-1)s$; different drifts therefore force $k=1$.
Eliminating $h(2)$ from (17.3) gives

$$
(u-v)(1+xy)+uy-vx+y^2-x^2=0.
\tag{17.8}
$$

With $xy=w$, each of the four different positive $x$ values is a
root of the monic quartic

$$
X^4+vX^3-(u-v)(1+w)X^2-uwX-w^2.
\tag{17.9}
$$

Four distinct positive roots would make its constant coefficient
their positive product, contradicting $-w^2<0$. Different sources
with $xy=w$ have different $x$, so this is a contradiction.

Hence $K$ has an equal-drift pair. By (17.5), there is $S>0$ with
$u=v=-S$. Define the following subset of the same quartet:

$$
Z=\{W\in K:s_W=S\}=\{W\in K:\delta_W=-S\},\qquad
c=a+S.
\tag{17.10}
$$

It has at least two members. On $Z$, $h(2)=0$ and $h(0)=c/q$.
For every member of $K\setminus Z$, equation (17.3) has
$h(2)\ne0$ and gives $x=y$. Different members outside $Z$ have
different $s=2x$, so have different drifts; none has the drift of
$Z$. Thus $Z$ is the only possible repeated-drift class.

*Pair children after either mixed history.* A third child of size
two with $L_4$ is impossible. Its common drift places both worlds
in $Z$; their root $2$ would join the three roots $5,6,7$ supplied
by the pair result, making a nonzero gain impossible.

A fourth child of size two with $L_3$ is also impossible. Such a
pair lies in $Z$ and has gain roots $2,6,7$. Its common initial
value and drift fix its entire gain to one common polynomial $G$;
if $c=0$, those three roots and root zero already contradict
legality. Otherwise $G(1),G(4),G(5)$ are nonzero. Equation (17.2)
gives $q=G(1)$ on this pair, hence a common $q$ and common $s=S$.
Its distinct matrices therefore satisfy

$$
R_W-R_Z=\eta\Omega,\qquad
\Omega=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad \eta\ne0.
\tag{17.11}
$$

Write $A=FEQ$ for its actual clock-four matrix, where $Q=L$ or
$U$. Its clock-four read and both clock-five predictions, divided
only by the established nonzero samples, imply
$A\Omega\in\mathbb R\Omega$, by the three-trace kernel (15.6).
Thus $A$ would be scalar. This is impossible for an actual
$A=BL$ or $BU$ with $B=FE$: $(BL)_{21}=B_{21}+B_{22}>0$
and $(BU)_{12}=B_{11}+B_{12}>0$. Here $B$ is nonnegative,
invertible and has no zero row. This excludes every such actual
pair child, without requiring its sibling to retain the pair.

*Three-world third children after chronological $MJ$.* At clock
three following $U$, the two matrices are

$$
A_e=\begin{pmatrix}0&1\\1&e\end{pmatrix},\qquad e=1,2.
\tag{17.12}
$$

Suppose a selected third child $T$ has three worlds and $L_4$.
Both fourth actions retain all of $T$ with $L_3$, since fourth
pair children have just been excluded. If $T$ contains at most
one member of $Z$, its drifts are pairwise different and the
distinct-drift exclusion applies. Otherwise take two of its
members in $Z$. Their two fourth responses are constant on this
pair. The difference of those responses is $h(4)(x+e)$. If that
common difference is nonzero, their common ratio of fourth-$J$
response plus $S$ to that difference is

$$
\frac{q+ey}{x+e}=S-x+\frac1{x+e}.
\tag{17.13}
$$

This is strictly decreasing for $0<x<S$, since its derivative
is $-1-(x+e)^{-2}$. It would identify the two sources. The
difference must therefore be zero: both fourth responses on
this pair equal $-S$, and both fourth gain samples vanish.
A member outside $Z$ sharing these two responses would also have
$h(4)=0$, because $x+e>0$, and then drift $-S$, a contradiction.
Hence $T\subseteq Z$, and applying the same argument to its
pairs gives $h(4)=0$ throughout $T$.

The third trace on $Z$ is $S+e$, so $h(3)=k_T$ is constant on
$T$. Cubic finite differences, with $h(1)=1,h(2)=0$, give

$$
0=h(4)=4k_T+4-h(0),\qquad h(0)=c/q.
\tag{17.14}
$$

If $c\ne0$, all three $q$ are equal. Fixed $x+y=S$ and $xy=q-1$
allow at most two ordered positive sources, a contradiction.
If $c=0$, then $k_T=-1$ and all three normalized polynomials are

$$
H(t)=\frac{t(t-2)(t-4)}3.
\tag{17.15}
$$

In particular $H(5)H(7)\ne0$. No fifth child can be a two-world
$L_2$, since (17.6) would force seventh roots. Thus every fifth
action retains all of $T$. Applying (17.6) at clock five to the
four continuations from $A_e$ would force fifth gain roots,
contrary to $g_W(5)=q_WH(5)\ne0$. This excludes $T$.

The selected third children after $U$ are therefore all four
worlds, each with $L_4$. Both third responses on $K$ are constant,
so subtraction and (17.12) give

$$
h_W(3)=k,\qquad k+(k-1)s_W\text{ is constant on }K.
\tag{17.16}
$$

If $K\setminus Z$ is nonempty, its $s$ differs from $S$ and
(17.16) forces $k=1$.

*The case $|Z|=4$.* Work at $A_1$ and its $L_4$ on $K$. Each
selected fourth child has $L_3$ and at least three worlds, because
pairs have been excluded. The two children intersect in at least
two worlds. Formula (17.13) on that pair makes both selected
responses equal $-S$. Since every member has drift $-S$ and
positive fourth trace factors, the two full response intersections
are consequently the same set $\{W\in K:h_W(4)=0\}$, of size
at least three. On all of $K$, finite differences give

$$
h_W(4)=4k+4-c/q_W.
\tag{17.17}
$$

If $c\ne0$, three zero samples would require three sources with
the same $S,q$, impossible. If $c=0$, a zero sample makes
$k=-1$, so the entire $K$ has the common normalized gain (17.15).
The fourth-$M$ child is then all of $K$, with $L_3$. Take fifth
$M$. Its actual matrix is $M^2A_1=M^3$, and its trace on $Z$ is

$$
\operatorname{tr}(M^3R)=q+2S+2
=3+2S+Sy-y^2.
\tag{17.18}
$$

Because $H(5)\ne0$, every fifth-$M$ response fiber has at most
two sources. None can have $L_2$: a pair would require seventh
gain roots by (17.6), whereas $H(7)\ne0$. Empty and singleton
fibers fail the guard. This contradicts the retained $L_3$.

*The case $|Z|=2$.* Now (17.16) gives $h(3)=1$ throughout $K$.
Consider a selected third child after $L$. A pair is impossible.
A triple $T$ with $L_4$ would have to contain both members of
$Z$, by the distinct-drift exclusion. Both fourth children retain
$T$, because fourth pairs are impossible. At clock five a selected
$L_2$ child is either all of $T$ or a pair. By (17.6), that pair
can only be the two members of $Z$. Thus these same two worlds
belong to every selected fifth child along the four length-two
continuations of this clock-three history. Their four clock-five
responses agree, so (17.6) gives fifth gain roots for both.

For these two worlds the four values $h(1)=h(3)=1$ and
$h(2)=h(5)=0$ determine the common entire polynomial

$$
H_*(t)=\frac{(t-2)(t-5)(5-3t)}8,\qquad
H_*(0)=\frac{25}4,\qquad H_*(4)=\frac74.
\tag{17.19}
$$

The initial equations $c/q=25/4$ fix a common $q$, so their
matrix difference is (17.11). Let $A$ be this actual clock-three
matrix, either $JL$ or $ML$. Its entry $A_{21}$ is $1$ for $JL$ and $2$ for $ML$, hence positive. Both
fourth responses on this pair agree, while $H_*(4)\ne0$;
subtracting their $M$ and $J$ trace equations gives
$\eta(A\Omega)_{22}=\eta A_{21}=0$, a contradiction.
No such triple exists. Consequently both third actions after $L$
also retain the full $K$.

All four responses in (17.7) are now constant on $K$, and
$h(3)=1$. Their comparison gives a common $xy=w>0$. But the two
members outside $Z$ have $x=y>0$, so both would have
$x=y=\sqrt w$ and the same source. This contradicts source
injectivity.

*The case $|Z|=3$.* There is a single remaining world $D\notin Z$,
and it has $x_D=y_D$. Again $h(3)=1$ on the entire $K$. Parametrize
members of $Z$ by their distinct $y\in(0,S)$, with $x=S-y$ and

$$
q(y)=1+Sy-y^2,\qquad C(y)=h(4)=8-c/q(y).
\tag{17.20}
$$

The four fourth actions, after the two full third children
$A_1,A_2$, have the following trace factors on $Z$:

$$
\begin{array}{c|c}
\text{actual matrix}&\text{trace factor}\\ \hline
JA_1&T_1=q+y\\
JA_2&T_2=q+2y\\
MA_1&T_3=q+S+1\\
MA_2&T_4=q+y+S+2.
\end{array}
\tag{17.21}
$$

Their reads are $-S+C(y)T_r(y)$. Each selected fourth child has
$L_3$ and at least three worlds, hence contains at least two
members of $Z$. Thus each of these four functions must have a
collision on a pair among the same three $Z$ members.

Suppose first that $c\ne0$. A pair of distinct $Z$ members can
collide at two of these functions only if both have $C=0$.
To check this, if one $C$ is zero then positivity of all the
$T_r$ makes the other zero. Otherwise a double collision requires
equal trace ratios. For the five index pairs other than $(1,4)$,
those ratios are injective on $(0,S)$, as the following identities
and derivatives show:

$$
\begin{gathered}
\frac{T_2}{T_1}=1+\frac y{T_1},\qquad
\left(\frac y{T_1}\right)'=\frac{1+y^2}{T_1^2}>0,\\
\frac{T_1}{T_3-T_1}=y+\frac1{S+1-y},\qquad
\frac{T_2}{T_4-T_2}=y+\frac1{S+2-y},\\
\left(\frac{T_2}{T_3}\right)'
=\frac{2\bigl(y-(S+1)/2\bigr)^2+(S^2+4S+7)/2}{T_3^2}>0,\\
\frac{T_4}{T_3}=1+\frac{y+1}{T_3},\qquad
\left(\frac{y+1}{T_3}\right)'
=\frac{(y+1)^2+1}{T_3^2}>0.
\end{gathered}
\tag{17.22}
$$

The middle two functions are strictly increasing, with positive
denominators; passing from $T_i/(T_j-T_i)$ to $T_i/T_j$
preserves injectivity. For the exceptional pair $(1,4)$, use
$T_4-T_1=S+2$. A double collision gives equal $C$ at the two
worlds. Since $c\ne0$, (17.20) gives equal $q$; a nonzero $C$
then gives equal $T_1$ and equal $y$, again impossible.

There are only three pairs among the three $Z$ members. If none
has two zero $C$ values, each pair can collide at at most one
function, so cannot supply all four required collisions. If a
zero pair exists, it is the only possible colliding pair for
any function: $C=0$ fixes $q=c/8$ and allows at most two
sources, and the third member's nonzero $C$ cannot collide with
either zero member. All four selected responses must then be
$-S$, and their children must contain $D$. Already its two
fourth responses after $A_1$ being $-S$ force $h_D(4)=0$
and $\delta_D=-S$, contrary to $D\notin Z$.

It remains to consider $c=0$. Now $C=8$ on $Z$. Each function
$T_r$ is a nonconstant quadratic in $y$, so a fiber on the three
sources has at most two members. Every selected fourth child
must therefore contain $D$ and its colliding $Z$ pair. For two
distinct values $y,Y$, the three different collision conditions
are

$$
\begin{aligned}
T_3(y)=T_3(Y)&\iff y+Y=S,\\
T_1(y)=T_1(Y)\quad\text{or}\quad T_4(y)=T_4(Y)
&\iff y+Y=S+1,\\
T_2(y)=T_2(Y)&\iff y+Y=S+2.
\end{aligned}
\tag{17.23}
$$

Ordering the three coordinates $y_1<y_2<y_3$, their pair sums
are ordered in the same way. Thus all three requirements in
(17.23) force

$$
\begin{gathered}
y_1+y_2=S,\quad y_1+y_3=S+1,\quad y_2+y_3=S+2,\\
(y_1,y_2,y_3)=\left(\frac{S-1}2,\frac{S+1}2,\frac{S+3}2\right).
\end{gathered}
\tag{17.24}
$$

Their colliding trace values for $T_2,T_3$ are both
$(S^2+4S+7)/4$; that for $T_1$ is $(S+1)^2/4$. In particular
$D$ must have equal fourth responses at $JA_2$ and $MA_1$.
For its diagonal coordinates $x_D=y_D$, the difference of these
trace factors is

$$
\operatorname{tr}(MA_1R_D)-\operatorname{tr}(JA_2R_D)
=(q_D+s_D+1)-(q_D+2y_D)=1.
\tag{17.25}
$$

The equal responses therefore force $h_D(4)=0$. All four fourth
responses of $D$ are then its same drift. But its required
responses at $JA_1$ and $JA_2$ differ by

$$
8\left(\frac{S^2+4S+7}4-\frac{(S+1)^2}4\right)
=4(S+3)>0,
\tag{17.26}
$$

a contradiction.

The three cases $|Z|=2,3,4$ exhaust the potential quartet and
have all been excluded. Every selected child used above is the
full intersection with its parent support at an actual response.
A pair is used as a losing set only when that full child has
cardinality two. In the $|Z|=2$ argument the distinguished pair
is instead explicitly retained by every selected fifth child;
only its resulting response equalities are used. All gains and
sources remain those of the same four original worlds throughout.
The contradiction proves (17.1). ∎

Theorem 17.1 excludes exactly-four-world original-root supports.
Its new inference is joint continuation under both mixed constants:
equal-drift source separation, exclusion of the actual three-world
third children, and the common four-world response constraints
(17.20)–(17.26) complete the exclusion. Theorem 15.3, Corollary
16.2, and the cited actual-history pair and product results are
reused with their original hypotheses. The polynomial identities,
monotonicity and pair counting are the explicit ordinary deductions
above; no external-priority claim is made.

The unrestricted assertion $U$ remains unresolved here. Theorem
9.2 already supplies finite failure certificates of at most
$2^{s+1}$ fixed worlds, and Theorem 9.3 supplies the original-root
bound of 256. To use the exclusion (17.1) to prove $U$ still
requires a failure-preserving reduction to at most four worlds,
or a sufficient larger-support exclusion. Neither is asserted.
No protocol has acquired both first responses or both mixed
responses on a single trajectory; those equations remain
conditional properties of the potential witness throughout.

## 追加锚（本行以下为增补区）

## 18. beta 零秩二层的回返传播与完整守卫排除

**定义 18.1（完整核上的 beta 零秩二来源层）。** Fix an arbitrary
legal source tuple of Definition 13.1, retaining its full
$1538\times1024$ matrix $B$, all $254$ prefixes, all $256$ maps
$G_q$ and all $128$ four-component maps $D_w$ of Definition 13.2.
Write $V=\ker B$ and $j_e=(J^7,e)$. Use exactly the scalar maps
$E_J,\alpha,\Delta,\beta$ of
[E-zero, Definition 7.1](FIB_ORIGINAL_ROOT_EZERO_FIBER_AND_GAIN_RANK_REDUCTION.md).
The source layer considered here is

$$
\begin{gathered}
\sigma(P_{j_0})=\sigma(P_{j_1})=s>0,\qquad s\ne1,\\
E_J|_V=0,\qquad \beta|_V=0,\qquad
\operatorname{rank}(G_{j_0}|_V)=2.
\end{gathered}
\tag{18.1}
$$

These are identities and a rank condition on the entire $V$.
For each slot write

$$
P_q=\begin{pmatrix}a_q&b_q\\c_q&1-a_q\end{pmatrix},\qquad
 d_q=1-a_q\in(0,1),\qquad t_q=b_q+c_q>0,
\qquad T_q=t_q+d_q=\operatorname{tr}(MP_q)>0.
\tag{18.2}
$$

The gain $g_q$ and $k_q=g_q(0)$ are polynomial-valued and
scalar-valued linear maps on $V$, respectively; their normalized
drift is $-k_q$. Zero blocks are allowed in these linear identities.
For every nonempty prefix $v$, let $R_v$ denote its common response
map on $V$, as supplied by all the rows (13.5). Thus every descendant
slot realizes all of its ancestor response maps on the same $V$.
Set $r_i=R_{J^i}$ for $1\le i\le4$ and $y=R_{J^4M}$.

**引理 18.2（四个 J 祖先对全部后代的约束）。** Under (18.1),
$\alpha,\Delta\in V^*$ are linearly independent. Reuse the
polynomials of E-zero, Definition 4.1,

$$
u(T)=\frac{T^3-9T^2+23T}{15},\qquad
v(T)=\frac{T(T-2)(T-4)}6.
\tag{18.3}
$$

Every slot $q\in\mathcal D_{J^4}$ satisfies, as identities on $V$,

$$
g_q=k_q+\alpha u-\frac{\Delta}{t_q}v,\qquad
(t_q-1)(k_q+\alpha)=0.
\tag{18.4}
$$

In particular $k_q=-\alpha$ when $t_q\ne1$, whereas $t_q=1$
does not by itself fix $k_q$.

Proof. E-zero, Lemma 7.2 gives
$\operatorname{rank}(G_{j_0}|_V)
=\operatorname{rank}((\alpha,\Delta,\beta)|_V)$ under the common
nonunit signature and $E_J|_V=0$. Hence (18.1) makes
$\alpha,\Delta$ independent. The same history coordinates give

$$
r_2=\frac65\alpha,\qquad r_4=\frac45\alpha,\qquad
r_1=\alpha-\frac\Delta2,\qquad r_3=\alpha+\frac\Delta2.
\tag{18.5}
$$

Indeed $E_J=3r_4-2r_2$, $\alpha=5r_2/6$,
$\Delta=r_3-r_1$, and $\beta=(r_1+r_3)/2-\alpha$.
For any $q\in\mathcal D_{J^4}$ put $p_q=g_q-k_q$.
The even ancestor reads give $p_q(2)=6\alpha/5$ and
$p_q(4)=4\alpha/5$. The polynomial $p_q-\alpha u$ has roots
$0,2,4$ and degree at most three, so is a scalar multiple of $v$,
including the zero multiple. Since $u(1)=u(3)=1$ and
$v(3)-v(1)=-1$, the odd ancestor difference
$\Delta=t_q(p_q(3)-p_q(1))$ makes this multiple $-\Delta/t_q$.
The average of the two odd ancestor reads is then
$(t_q-1)k_q+t_q\alpha$. By (18.5) it equals $\alpha$, giving
the second identity (18.4). All these arguments apply to each
$x\in V$, including its zero blocks, and therefore establish map
identities on $V$. The interpolation step divides only by $t_q>0$;
the conclusion $k_q=-\alpha$ uses the stated $t_q\ne1$ branch.
No fifth read or unit-signature exclusion was used. ∎

**定理 18.3（beta 零秩二完整来源层的原守卫失败）。** For every
complete legal source tuple satisfying (18.1), put

$$
w_A=J^4MJJ,\qquad w_B=J^4MMJ,\qquad
q_{Ae}=(w_A,e),\quad q_{Be}=(w_B,e).
\tag{18.6}
$$

Then

$$
D_{w_A}|_V=0,
\tag{18.7}
$$

and at least one of the following two alternatives holds:

$$
\begin{aligned}
&P_{q_{A0}}=P_{q_{A1}},\\
& P_{q_{B0}}=P_{q_{B1}}\quad\hbox{and}\quad D_{w_B}|_V=0.
\end{aligned}
\tag{18.8}
$$

Thus an original same-source separation guard of Theorem 13.3
fails at $w_A$ or $w_B$. In particular the source layer (18.1)
has empty intersection with the complete guarded source locus of
that theorem. No assumption on any other source equality, gain
map or leaf difference is required.

Proof. All calculations below are on the original whole $V$.
Along $J^4MJJ$ the cumulative matrices at clocks $5,6,7$ are

$$
M,\qquad JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\qquad M,
\tag{18.9}
$$

with trace factors $T_q,1+c_q,T_q$. By (18.3),
$u(7)-u(5)=16/5$ and $v(7)-v(5)=15$. For the two slots of this
leaf, subtracting their common clock-five read from their common
clock-seven read and using (18.4) gives

$$
\frac{16}{5}(T_{q_{A0}}-T_{q_{A1}})\alpha
-15\left(\frac{T_{q_{A0}}}{t_{q_{A0}}}
        -\frac{T_{q_{A1}}}{t_{q_{A1}}}\right)\Delta=0.
\tag{18.10}
$$

Independence of $\alpha,\Delta$ makes both fixed coefficients
zero. Since $T_q,t_q>0$, the two slots have the same $T$, the
same $t$ and hence the same $d=T-t$. Their nonconstant gain
parts in (18.4) coincide. If $t\ne1$, their constant terms both
are $-\alpha$. If $t=1$, their clock-five read difference is
$(T-1)(k_{q_{A0}}-k_{q_{A1}})=d(k_{q_{A0}}-k_{q_{A1}})$;
$d>0$ again makes their constant terms equal. Their entire gains
and normalized drifts therefore coincide as maps, proving the
full four-component identity (18.7).

If these two fixed sources are equal, the first alternative in
(18.8), together with (18.7), already gives a failing original
guard. Suppose instead that they differ. Their common $d,t$
then imply $c_{q_{A0}}\ne c_{q_{A1}}$, since $a=1-d$ and
$b=t-c$. The clock-six equality, its trace factor $1+c_q$ and
their already common gain give

$$
(c_{q_{A0}}-c_{q_{A1}})g_{q_{A0}}(6)=0
\quad\hbox{on }V.
\tag{18.11}
$$

Consequently their common $g(6)$ is the zero map. A nonunit
$t$ is impossible: (18.4), $u(6)=2$ and $v(6)=8$ would give
$g(6)=\alpha-8\Delta/t\ne0$. Thus $t=1$, and (18.4) gives

$$
k_{q_{A0}}=k_{q_{A1}}=-2\alpha+8\Delta.
\tag{18.12}
$$

Write their common $d$ as $d_*\in(0,1)$ and introduce

$$
\kappa=\alpha-\frac{11}{2}\Delta,\qquad
\lambda=\frac{16}{5}\alpha-15\Delta,\qquad
Y=y-\alpha+\frac52\Delta.
\tag{18.13}
$$

The two forms $\kappa,\lambda$ are independent, since their
coefficient determinant relative to $\alpha,\Delta$ is
$-15+(11/2)(16/5)=13/5\ne0$. At clock five,
$u(5)=1$, $v(5)=5/2$ and (18.12) give $g(5)=-\kappa$.
Its trace factor is $1+d_*$, so the common response satisfies

$$
y=\alpha-\frac52\Delta-d_*\kappa,\qquad Y=-d_*\kappa.
\tag{18.14}
$$

This forces every one of the eight slots below $J^4M$ to have
unit signature. Indeed, if such a slot $q$ had $t_q\ne1$,
(18.4) would instead give

$$
y=\alpha-\frac52\left(1+\frac{d_q}{t_q}\right)\Delta.
\tag{18.15}
$$

Its $\alpha$ coefficient is $1$, whereas the coefficient in
(18.14) is $1-d_*$. Their equality contradicts independence
and $d_*>0$. This uses the shared fifth response of the entire
subtree, not separate choices of gains on different branches.

For any of its now unit-signature slots, the same fifth read is

$$
y=d_qk_q+(1+d_q)\alpha-\frac52(1+d_q)\Delta.
\tag{18.16}
$$

Solving only by the positive fixed scalar $d_q$ yields

$$
k_q=\frac{Y}{d_q}-\alpha+\frac52\Delta,\qquad
g_q(6)=\frac{Y}{d_q}+\kappa,\qquad
g_q(7)=\frac{Y}{d_q}+\lambda.
\tag{18.17}
$$

These are identities for the whole original polynomials in their
slots; no final coefficient vector has been selected.

Now use the other leaf $w_B=J^4MMJ$. Its cumulative matrices
at clocks $5,6,7$ are $M,M^2,JM^2$, with trace factors
$1+d_q,2+d_q,2+c_q$ because $t_q=1$. Write
$d_e=d_{q_{Be}}$. The common sixth read, (18.17) and (18.14)
give

$$
\begin{aligned}
0&=(d_0-d_1)\kappa+
        \left(\frac1{d_0}-\frac1{d_1}\right)Y\\
 &= (d_0-d_1)\left(1+\frac{d_*}{d_0d_1}\right)\kappa.
\end{aligned}
\tag{18.18}
$$

Here $d_*,d_0,d_1>0$ and $\kappa\ne0$, so $d_0=d_1=d$.
Equation (18.17) makes the two entire gains and drifts equal.
Their common final gain map is

$$
g(7)=\lambda-\frac{d_*}{d}\kappa\ne0,
\tag{18.19}
$$

by independence of $\kappa,\lambda$. The common final read
with trace factor $2+c_q$ therefore forces
$c_{q_{B0}}=c_{q_{B1}}$. Together with $t=1$ and the common
$d$, this gives the same $a,b,c$ and hence the same complete
source. The already equal entire gains prove $D_{w_B}|_V=0$,
which is the second alternative in (18.8).

Every case has produced a same-source leaf with its full
four-component difference zero on $V$. Equivalently its original
rank guard has $\operatorname{rank}[B;D_w]=\operatorname{rank}B$
by (13.15), while its source-inequality alternative is false.
Theorem 13.3 therefore excludes a complete guarded realization
in (18.1). All source repetitions and all other slots remain in
the quantifier. All inversions and cancellations above involve fixed
source scalars with the stated positive or nonzero conditions. No
gain sample or value of a history coordinate is divided out. ∎

**推论 18.4（beta 零平面的完整源增益秩一必要性）。** Fix a
complete legal source tuple satisfying every original guard of
Theorem 13.3. If its two $J^7$ sources have a common nonunit
signature and $E_J|_V=\beta|_V=0$, then

$$
\operatorname{rank}(G_{j_0}|_V)=1.
\tag{18.20}
$$

This is a necessary condition, asserting neither a realization of
this rank-one locus nor exclusion of the other original source
strata or a decision of the unrestricted eight-read problem.

Proof. The original $G_{j_0}$ guard makes the rank positive.
E-zero, Theorem 8.1 bounds it by two, and Theorem 18.3 excludes
two when $\beta|_V=0$. Thus it equals one. ∎

## 追加锚（本行以下为增补区）

## 19. 单位签名的回返叶、完整守卫排除与例外局部构造

**定义 19.1（完整单位来源核与非恒定增益像）。** Let

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
\mathcal P=\left\{\begin{pmatrix}a&b\\c&1-a\end{pmatrix}:
0<a<1,\ b,c>0,\ bc=a(1-a)\right\}.
$$


Set $S=\{(w,e):w\in\{J,M\}^7,\ e\in\{0,1\}\}$, and fix an arbitrary complete tuple $\mathbf P\in\mathcal P^S$. Repetitions are allowed. For a nonempty chronological prefix $v=E_1\cdots E_i$, put $A_v=E_i\cdots E_1$, let $S_v$ be its descendant slots, and let $q_v$ be the first descendant under $J<M$, $0<1$. Define

$$
t_v(P)=\operatorname{tr}(A_vP),\qquad
\ell_v(P)=(t_v(P)-1,\ it_v(P),\ i^2t_v(P),\ i^3t_v(P)).
$$


The matrix $B$ has all rows

$$
(Bx)_{v,q}=\ell_v(P_q)x_q-\ell_v(P_{q_v})x_{q_v},
\qquad q\in S_v\setminus\{q_v\},\quad 1\le |v|\le7.
$$


Thus $B$ is the original $1538\times1024$ matrix, containing all $254$ prefixes. Throughout,

$$
V=\ker B\subseteq\mathbb R^{1024},\qquad
G_qx=x_q,\qquad D_wx=x_{(w,0)}-x_{(w,1)}\in\mathbb R^4.
$$


There is no restriction to a subspace of this kernel. Write

$$
g_q(T)=\sum_{r=0}^3x_{qr}T^r,\qquad k_q=g_q(0),\qquad\delta_q=-k_q.
$$


These are polynomial-valued or scalar-valued linear maps on $V$. Zero blocks are permitted in every linear identity below. A nonzero block represents the original legal gain and its normalized drift. For any prefix, the equations defining $V$ give a common response map $R_v$, realized by every descendant:

$$
R_v=t_v(P_q)g_q(|v|)-k_q\qquad(q\in S_v).
$$


Assume only the unit-signature source condition

$$
\sigma(P_{j_0})=\sigma(P_{j_1})=1,
\qquad \sigma(P)=b+c,\qquad j_e=(J^7,e).
\tag{19.1}
$$


No condition is imposed on the other $254$ sources.

Let $\mathcal C_3=\{p\in\mathbb R[T]:\deg p\le3,\ p(0)=0\}$. The complete $J^7$ coupling of [J-signature, Theorem 4.1](FIB_ORIGINAL_ROOT_J_SIGNATURE_COUPLING_AND_HISTORY_FIBER_DECODER.md) gives the well-defined linear map

$$
\mathscr H:V\longrightarrow\mathcal C_3,\qquad
p=\mathscr Hx=g_{j_0}-g_{j_0}(0)=g_{j_1}-g_{j_1}(0).
\tag{19.2}
$$


Indeed, the differences of the two gains minus their constant difference vanish at the four even clocks $0,2,4,6$. Since both sources have unit signature, every pure-$J$ common response is $R_{J^i}=p(i)$. This also allows independent constant offsets in the two gains; no equality of their constants is asserted.

Define scalar linear maps on this same $V$:

$$
m=\frac{p(1)+p(3)}2,\qquad
\Delta=p(3)-p(1),\qquad E=3p(4)-2p(2),
$$


$$
\kappa=p(6)-p(5),\qquad \lambda=p(7)-p(5).
\tag{19.3}
$$


All ranks below are ranks of maps on $V$.


**定理 19.2（单位像秩三与非例外比例秩二的完整守卫排除）。** Under Definition 19.1, put

$$
w_A=J^4MJJ,\qquad w_B=J^4MMJ.
$$


Suppose either

1. $\operatorname{rank}\mathscr H=3$; or
2. $\operatorname{rank}\mathscr H=2$ and, for a real constant $\gamma\ne13/4$, the map identity $E=\gamma\Delta$ holds on $V$.

Then

$$
D_{w_A}|_V=0,
\tag{19.4}
$$


and at least one of the following holds:

$$
P_{(w_A,0)}=P_{(w_A,1)},
\tag{19.5a}
$$


$$
P_{(w_B,0)}=P_{(w_B,1)}
\quad\hbox{and}\quad D_{w_B}|_V=0.
\tag{19.5b}
$$


Consequently a required original full same-source separation guard fails at $w_A$ or $w_B$. The conclusion concerns the original complete tuple and its whole kernel; it has no assumptions on the gain guards, source equalities, sample roots, or other branches.

Proof.

Write $p(T)=rT+sT^2+hT^3$. The coefficient rows of $m,E,\Delta$, in that order, are

$$
(2,5,14),\qquad(8,40,176),\qquad(2,8,26),
$$


whose determinant is $-240$. Direct coefficient comparison also gives

$$
\begin{aligned}
p(5)&=m+E-\frac52\Delta,\\
p(6)&=2m+\frac94E-8\Delta,\\
p(7)&=\frac{21}{5}m+\frac{21}{5}E-\frac{35}{2}\Delta,\\
\kappa&=m+\frac54E-\frac{11}{2}\Delta,\\
\lambda&=\frac{16}{5}m+\frac{16}{5}E-15\Delta.
\end{aligned}
\tag{19.6}
$$


In case 1, $m,E,\Delta$ are independent on $V$. Moreover, each of the pairs

$$
(\lambda,\Delta),\qquad(p(6)-m,\Delta),\qquad(\lambda,\kappa)
\tag{19.7}
$$


is independent: their first two coefficient minors in the $(r,s,h)$ coordinates are respectively $-32,-30,-2$.

In case 2, $m,\Delta$ are independent. Otherwise $m,E,\Delta$, and hence $\mathscr H$, would have rank at most one. Formula (19.6) then shows that the first two pairs in (19.7) are independent, and that $\kappa\ne0$. Relative to $(m,\Delta)$, the determinant for the last pair is

$$
\det\begin{pmatrix}
16/5&16\gamma/5-15\\
1&5\gamma/4-11/2
\end{pmatrix}=\frac{4\gamma-13}{5}\ne0.
\tag{19.8}
$$


Thus all three pairs in (19.7) are independent in either case.

We first obtain identities for every one of the $16$ slots below $J^4$. For such a slot put

$$
t_q=b_q+c_q>0,\quad d_q=1-a_q\in(0,1),\quad
T_q=t_q+d_q=\operatorname{tr}(MP_q)>0,
$$


and write $p_q=g_q-k_q$. Its even ancestors give $p_q(2)=p(2)$ and $p_q(4)=p(4)$. Therefore

$$
p_q-p=\rho_q v,\qquad v(T)=\frac{T(T-2)(T-4)}6,
$$


for a scalar-valued linear map $\rho_q$. Its two odd ancestors have response difference $\Delta$. Since $v(3)-v(1)=-1$,

$$
\Delta=t_q\bigl(\Delta-\rho_q\bigr),
\qquad \rho_q=(1-1/t_q)\Delta.
$$


Also $v(1)+v(3)=0$, so averaging these odd ancestors gives

$$
(t_q-1)(k_q+m)=0.
$$


We have proved, on the whole $V$,

$$
g_q=k_q+p+(1-1/t_q)\Delta v,
\qquad (t_q-1)(k_q+m)=0.
\tag{19.9}
$$


In particular, $k_q=-m$ for a fixed nonunit source; for a unit source its constant is still unrestricted by these four ancestors.

Consider the two slots of $w_A$. At clocks $5,6,7$ their cumulative matrices are

$$
M,\quad JM=\begin{pmatrix}1&1\\0&1\end{pmatrix},\quad M,
$$


with trace factors $T_q,1+c_q,T_q$. The clock-seven response minus the clock-five response equals

$$
T_q\bigl(g_q(7)-g_q(5)\bigr)
=T_q\bigl(\lambda+15(1-1/t_q)\Delta\bigr),
\tag{19.10}
$$


because $v(7)-v(5)=15$. Comparing the two slots and using the independence of $\lambda,\Delta$ proves that they have the same $T$, then the same $t$, and hence the same $d=T-t$. Their nonconstant gain parts in (19.9) agree.

If $t\ne1$, their constants are both $-m$. If $t=1$, their common fifth response gives

$$
(T-1)(k_0-k_1)=d(k_0-k_1)=0,
$$


and $d>0$ again identifies the constants. This proves (19.4), including its constant component.

If the two sources at $w_A$ coincide, (19.5a) completes the proof. Assume that they differ. Their common $t,d$ then imply different $c$. Their common sixth response, with their already equal entire gains, forces

$$
g_{(w_A,0)}(6)=g_{(w_A,1)}(6)=0
\quad\hbox{as maps on }V.
\tag{19.11}
$$


For $t\ne1$, formula (19.9) would instead give

$$
g(6)=p(6)-m+8(1-1/t)\Delta\ne0
$$


by (19.7). Thus these two sources have $t=1$. Write their common $d$ as $d_*\in(0,1)$. Equation (19.11) gives $k=-p(6)$. Consequently the common fifth response of the entire $J^4M$ subtree is

$$
y=R_{J^4M}=(1+d_*)\bigl(p(5)-p(6)\bigr)+p(6)
=p(5)-d_*\kappa.
\tag{19.12}
$$


We next show that all eight slots in this subtree have unit signature. If a slot $q\in S_{J^4M}$ had $t_q\ne1$, then (19.9), $v(5)=5/2$, and (19.6) would give

$$
y=m+T_qE-\frac52\frac{T_q}{t_q}\Delta.
\tag{19.13}
$$


But (19.12) gives

$$
y=(1-d_*)m+\left(1-\frac54d_*\right)E
+\left(-\frac52+\frac{11}{2}d_*\right)\Delta.
\tag{19.14}
$$


In case 1 independence of $m,E,\Delta$ makes the coefficients of $m$ in (19.13) and (19.14) incompatible, since $d_*>0$. In case 2 substitute $E=\gamma\Delta$; independence of $m,\Delta$ gives exactly the same contradiction. Therefore

$$
t_q=1\qquad(q\in S_{J^4M}).
\tag{19.15}
$$


This uses one shared fifth response on the original whole kernel, simultaneously for both sixth-action branches.

For each such slot, its fifth response now determines its whole gain:

$$
k_q=-p(5)-\frac{d_*}{d_q}\kappa,\qquad
 g_q(6)=\left(1-\frac{d_*}{d_q}\right)\kappa,\qquad
 g_q(7)=\lambda-\frac{d_*}{d_q}\kappa.
\tag{19.16}
$$


Only the positive fixed source scalar $d_q$ was inverted.

Finally consider the two slots of $w_B$, writing their $d$'s as $d_0,d_1$. Their cumulative matrices at clocks $5,6,7$ are

$$
M,\quad M^2,\quad JM^2=\begin{pmatrix}1&2\\1&1\end{pmatrix}.
$$


By (19.15) their traces are $1+d_q,2+d_q,2+c_q$. Substituting (19.16) into their common sixth response yields

$$
0=(d_0-d_1)\left(1+\frac{d_*}{d_0d_1}\right)\kappa.
\tag{19.17}
$$


Here $\kappa\ne0$ as a linear map, and the scalar factor in parentheses is strictly positive. Thus $d_0=d_1=d$. Formula (19.16) then identifies their entire gains and constants, proving $D_{w_B}|_V=0$. Their common seventh gain map is nonzero:

$$
g(7)=\lambda-\frac{d_*}{d}\kappa\ne0
\tag{19.18}
$$


by the independence of $\lambda,\kappa$. Their seventh response equality, with trace $2+c_q$, therefore forces $c_0=c_1$. The common $d$ and $t=1$ give identical $a,b,c$, so the sources also coincide. This proves (19.5b).

In both alternatives, a fixed same-source leaf has its full four-component difference zero on all of $V$. It is therefore an applicable original separation guard that fails. No polynomial sample or value of a linear map at a selected vector was divided out. All claims of nonzero maps used linear independence on the entire kernel. ∎


**定理 19.3（完整单位来源域的必要像维数）。** For a complete legal unit-signature tuple as in Definition 19.1, simultaneous satisfaction of every original gain guard and every applicable full same-source guard of Theorem 13.3 implies

$$
1\le\operatorname{rank}\mathscr H\le2,\qquad
\operatorname{rank}(G_{j_e}|_V)=1+\operatorname{rank}\mathscr H
\quad(e=0,1).
\tag{19.19}
$$


If the rank is two, $\Delta\ne0$, and $E=\gamma\Delta$ for a real scalar $\gamma$, then necessarily

$$
E=\frac{13}{4}\Delta.
\tag{19.20}
$$


In particular rank two with $E=0$ is excluded. These are derived exclusions on the original source domain, with no additional rank promise.

Proof. Theorem 19.2 excludes rank three by exhibiting an applicable full $D$ guard that vanishes on the entire original $V$. The rank cannot exceed three because $\mathcal C_3$ has dimension three. If every required restriction is nonzero, Theorem 13.3's finite-subspace argument supplies one vector in this same $V$ satisfying all guards simultaneously. [J-signature, Theorem 7.1](FIB_ORIGINAL_ROOT_J_SIGNATURE_COUPLING_AND_HISTORY_FIBER_DECODER.md) makes its common nonconstant part nonzero, excluding rank zero.

The projection from $G_{j_e}(V)$ to the nonconstant coefficients has image $\mathscr H(V)$. Its kernel consists of constant polynomials and has dimension at most one; [J-signature, Proposition 7.3](FIB_ORIGINAL_ROOT_J_SIGNATURE_COUPLING_AND_HISTORY_FIBER_DECODER.md) supplies the nonzero localized constant direction at this same slot, so its dimension is exactly one. Rank-nullity proves the second identity in (19.19). If rank two and $\Delta\ne0$, Theorem 19.2 excludes every proportionality except (19.20). If rank two and $E=0$, $\Delta=0$ would make $(m,E,\Delta)$, hence $\mathscr H$, have rank at most one; otherwise $E=0\Delta$ is the excluded proportional case. ∎

**定义 19.4（例外平面的四个固定目标与八槽）。** Fix any
$p\in\mathcal C_3\setminus\{0\}$ with $E=(13/4)\Delta$, where the scalar values are those of (19.3). Formula (19.6) gives $\lambda=(16/5)\kappa$, including $\kappa=0$. For $0<d<1$ set

$$
Q_0(d)=\begin{pmatrix}1-d&1-d\\d&d\end{pmatrix},\qquad
Q_1(d)=\begin{pmatrix}1-d&d\\1-d&d\end{pmatrix}.
\tag{19.21}
$$


Define the four complete targets, before selecting any continuation, by

$$
\begin{aligned}
W_e^J&=\bigl(Q_e(4/5),\ p-p(6),\ p(6)\bigr),\\
W_e^M&=\bigl(Q_e(1/4),\ p-p(7),\ p(7)\bigr)
\qquad(e=0,1).
\end{aligned}
\tag{19.22}
$$


Each triple records source, gain and drift. In the eight slots below the chronological prefix $J^4M$, assign $W_e^J$ to both $(J^4MJJ,e)$ and $(J^4MJM,e)$, and $W_e^M$ to both $(J^4MMJ,e)$ and $(J^4MMM,e)$. The repeated sources and repeated targets across different leaves are intentional; only each terminal pair must consist of distinct complete targets.

**定理 19.5（例外系数的四目标局部两步失败）。** All four targets of Definition 19.4 are legal, distinct complete targets. Their eight-slot assignment shares every actual ancestor of its assigned slots, retains a collision for either final action after each of the two selected sixth-action responses, and has $L_2$ at the common actual prefix $J^4M$, including stopping at that prefix or at either selected child. No condition $\kappa\ne0$ is required.

Proof. Each $Q_e(d)$ has trace one, strictly positive entries, $a=1-d\in(0,1)$ and $bc=d(1-d)=a(1-a)$, and has unit signature. At each of $d=4/5,1/4$ the two sources are different since $d\ne1/2$; sources across the two groups have different $a$. Thus the four targets are distinct. A nonzero $p$ with $p(0)=0$ is nonconstant, so neither constant shift $p-p(6)$ nor $p-p(7)$ is the zero polynomial. These remain legal gains of degree at most three, with arbitrary coefficient signs and possible sample or repeated roots.

The normalized initial readings are all zero. At clocks $i=1,2,3,4$, every target has response $p(i)$, since each pure-$J$ trace is one. At clock five the cumulative matrix is $M$ and its trace is $1+d$. The two groups have responses

$$
p(5)-\frac45\kappa,\qquad
p(5)-\frac14\lambda=p(5)-\frac45\kappa.
\tag{19.23}
$$


Thus all four targets share the same complete history through the fifth action; the gain shifts do not change their earlier readings or impose zero drift.

If the sixth action is $J$, select the child response realized by $W_0^J,W_1^J$. Their cumulative matrix is $JM$ and their gain at clock six is zero, so both responses equal $p(6)$, regardless of their different $c$ entries. For their two possible final actions the exact cumulative matrices are

$$
M,\qquad MJM=\begin{pmatrix}0&1\\1&2\end{pmatrix}.
\tag{19.24}
$$


For a unit source their traces are respectively $1+d$ and $b+c+2d=1+2d$. In particular the latter trace is $1+2d$; $2+d$ is instead the trace of $M^2$. At the fixed $d=4/5$, these traces agree between $Q_0(d)$ and $Q_1(d)$. Therefore the two final $J$ responses agree and the two final $M$ responses agree, being respectively

$$
(1+d)\bigl(p(7)-p(6)\bigr)+p(6),\qquad
(1+2d)\bigl(p(7)-p(6)\bigr)+p(6).
\tag{19.25}
$$


Both collisions use the same two already fixed targets and their actual shared ancestors. The two responses in (19.25) need not equal one another.

If the sixth action is $M$, select the child response realized by $W_0^M,W_1^M$. Their cumulative matrix is

$$
M^2=\begin{pmatrix}1&1\\1&2\end{pmatrix},
\qquad \operatorname{tr}(M^2P)=2+d
\quad(\sigma(P)=1).
\tag{19.26}
$$


Their shared sixth response is $(2+d)(p(6)-p(7))+p(7)$ at the fixed $d=1/4$. At clock seven the two cumulative matrices are

$$
JM^2=\begin{pmatrix}1&2\\1&1\end{pmatrix},\qquad
M^3=\begin{pmatrix}1&2\\2&3\end{pmatrix},
\qquad
\operatorname{tr}(JM^2P)=2+c,\quad
\operatorname{tr}(M^3P)=3+2d
\quad(\sigma(P)=1).
\tag{19.27}
$$


The first trace can differ between the two sources. Their common gain at clock seven is zero, however, so either final action gives response $p(7)$ for both targets. This proves both collisions on this child as well, without identifying sources or dividing by a gain value.

For either sixth action, a selected actual response therefore leaves two distinct targets sharing their full acquired history. Stopping at that child fails; either final action still leaves a distinct pair, so one remaining reading also fails. At the fifth-action history all four targets are already present, so stopping there fails and either sixth action has a failing selected child. This is precisely its local $L_2$ conclusion. When $\kappa=0$, also $\lambda=0$; all formulas remain valid and the two gains are still nonzero by nonconstancy of $p$. No root, sign or nonzero future-sample promise was used. ∎

Theorem 19.5 supplies exactly the eight slots below one fifth-action prefix. It supplies neither the opposite fifth action after $J^4$, earlier sibling branches, nor any extension to a complete source tuple or its full kernel. It gives no full-root bound or nine-read conclusion.

The sources for Section 19 are the mathematical version `1eef3601bb81023352394a59bcb682b0c9b57cd8` of this volume, Definitions 13.1–13.2 and Theorem 13.3; [J-signature, Theorems 4.1, 7.1 and Proposition 7.3](FIB_ORIGINAL_ROOT_J_SIGNATURE_COUPLING_AND_HISTORY_FIBER_DECODER.md); and [J5, Theorem 6.2, Definition 8.2 and Conclusion 14.3](FIB_ORIGINAL_ROOT_J5_FIBER_DICHOTOMY_AND_RANK_TRICHOTOMY.md). The $B/G/D$ interface, initial-reading translation, finite-subspace avoidance, unit $J^5$ fiber result and localized constant directions are suppliers. Sections 17–18 of this volume and [E-zero, Section 13](FIB_ORIGINAL_ROOT_EZERO_FIBER_AND_GAIN_RANK_REDUCTION.md) provide the preceding four-world and nonunit return arguments; the nonunit hypotheses of those arguments remain in force there and are not assumed here. The new model-specific synthesis is the unit return comparison, shared fifth-response propagation, full source/gain/drift exclusion and its exceptional local construction. No global novelty or exhaustive literature claim is made.

Rank-one unit tuples, rank-two tuples with $\Delta=0$, rank-two tuples with independent $E,\Delta$, and the exceptional rank-two plane $E=(13/4)\Delta$ remain unresolved by these results. A complete-root exclusion still requires an original failed guard for every remaining tuple; a surviving realization still requires one complete legal $256$-source tuple and all original guards on its same full $V$, or one simultaneous legal full coefficient vector. All $254$ prefixes, clocks zero through seven, the $1538\times1024$ matrix, coefficient signs, degree drops, roots, source repetitions, strict positivity, arbitrary real constant drifts, both actions and early stops remain in that obligation. No narrower branch kernel or independent branch/source choices discharge it.

## 追加锚（本行以下为增补区）

## 20. 固定严格正一参数族的匹配线性覆盖数

### 定义 20.1（同一连续来源族与预选覆盖）

固定有限实数 $\varepsilon,\delta>0$，置

$$
 \gamma=\varepsilon+\delta,\qquad
 h=\frac{\delta}{\gamma}\in(0,1),\qquad
 X=\frac{\gamma}{\delta}=1+\frac{\varepsilon}{\delta},\qquad
 K_\gamma=\{\gamma R_s:0\le s\le1/2\},
\tag{20.1}
$$

其中 $R_s$ 严格取 [III 卷](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md)
定义 17.1 的 (17.2)，严格正两项实现取其引理 17.2 的 (17.5)。
环境仍是 III 定义 9.1、13.1 的完整 $\mathcal M_3$：来源为一项或两项
严格正外积之和，目标为普通初始实秩；只有 $N,L_0$ 原子和一条不可复制、
不可复位的实际轨迹。初读及每个原子后的必读均收费。
容限 $\varepsilon$ 的每次误差满足闭约束 $|\eta_i|\le\varepsilon$，
可任意相关并依赖全部历史。协议是完整动作—报告历史的任意确定性函数，
不附加连续、可测、可计算或共同停止预算条件。

成功集合 $\operatorname{Succ}_\varepsilon(\Pi)$、完整环境域可靠性及
$\nu_{3,\varepsilon}$ 均取 III 定义 14.1、推论 14.6。
若 $\mathscr H_\varepsilon(S,\Pi)$ 表示协议 $\Pi$ 在同一个固定来源
$S$ 上的全部允许误差历史，覆盖 $K_\gamma$ 的量词是

$$
 \exists\text{有限预选族 }F\quad
 \forall s\in[0,1/2]\quad\exists\Pi_s\in F\quad
 \forall H\in\mathscr H_\varepsilon(\gamma R_s,\Pi_s)
 \quad\Pi_s\text{ 在 }H\text{ 上有限输出 }2.
\tag{20.2}
$$

每个成员须在完整 $\mathcal M_3$ 上 $\varepsilon$-可靠。
$F$ 在来源未知前固定，同一个 $\Pi_s$ 覆盖该来源的全部历史。

### 定理 20.2（整个连续族的显式双边线性界）

对定义 20.1 的每一对有限 $\varepsilon,\delta>0$，有

$$
 \frac1{1024}\left(1+\frac{\varepsilon}{\delta}\right)
 \le\nu_{3,\varepsilon}(K_\gamma)
 \le\left\lceil\frac52\left(1+\frac{\varepsilon}{\delta}\right)\right\rceil
 \le\frac72\left(1+\frac{\varepsilon}{\delta}\right).
\tag{20.3}
$$

上界可用 III 命题 17.3 的原有五报告协议组成的预选族达到；每个成员还在
完整 $\mathcal M_3$ 上 $\gamma$-可靠，并在每个来源的每条允许
$\varepsilon$ 误差历史上恰以五次报告停止。
下界比较全部允许的确定性完整历史协议，不限制其预算或正则性。

**证明。** 先由 III 引理 17.2 得到每个 $\gamma R_s$ 的严格正两项实现
和普通初始秩二：只须将 (17.5) 的两个行因子同乘 $\gamma>0$。
III 命题 17.3 给出其全域 $\gamma$-可靠、全 $\gamma$ 误差成功的协议
$\Pi_{\gamma,s}$。限制为闭 $\varepsilon$ 误差历史后，同一协议仍可靠且成功。
故 $K_\gamma\subseteq\mathcal I_3(\gamma)\subseteq\mathcal I_3(\varepsilon)$，
且 $K_\gamma$ 非空；这也使定义 20.1 的覆盖数有意义。

先计算 III 定义 18.1 的操作距离在这个具体族上的值。
III (17.4) 给出 $a_0=15,a_1=18$ 恒定，且

$$
 \begin{aligned}
 b^{(0)}(R_s)
 &=\left(23+\frac52s-s^2-\frac{125}{44+s},
           \frac{53}{2}+10s,\ \frac{19}{2}+s\right),\\
 b^{(1)}(R_s)
 &=\left(\frac{43}{2}-\frac{125}{44+s},\ \frac{43}{2},\ 9\right),\\
 b^{(2)}(R_s)&=(3-s,10,1).
 \end{aligned}
\tag{20.4}
$$

对任意 $s,t\in[0,1/2]$，第一行首坐标之差为

$$
 (s-t)\left(\frac52-s-t+\frac{125}{(44+s)(44+t)}\right).
\tag{20.5}
$$

括号内严格介于 $3/2$ 与 $3$ 之间，因为 $0\le s+t\le1$ 且
$0<125/((44+s)(44+t))\le125/44^2<1/2$。
第二行首坐标之差为 $125(s-t)/((44+s)(44+t))$。
因此 (20.4) 的所有坐标差绝对值均至多 $10|s-t|$，而
$b_1^{(0)}$ 的差恰为 $10|s-t|$。按 III (18.1)--(18.2)，包括
$a_2=b_2^{(2)}$ 的同一重复真值坐标，有

$$
 d_{\mathrm{op}}(\gamma R_s,\gamma R_t)
       =10\gamma|s-t|.
\tag{20.6}
$$

III 引理 18.2 同时保证此距离控制每个实际原子字的读数差；
使用这些坐标比较来源不表示在一次运行中取得不同切口的数据。

令

$$
 n=\left\lceil\frac{5\gamma}{2\delta}\right\rceil,
 \qquad t_j=\frac{2j+1}{4n}\quad(0\le j<n),\qquad
 F=\{\Pi_{\gamma,t_j}:0\le j<n\}.
\tag{20.7}
$$

这是只依赖 $\varepsilon,\delta$ 的有限预选族。对所有
$s\in[j/(2n),(j+1)/(2n)]$，都有

$$
 |s-t_j|\le\frac1{4n},\qquad
 d_{\mathrm{op}}(\gamma R_s,\gamma R_{t_j})
       \le\frac{5\gamma}{2n}\le\delta.
\tag{20.8}
$$

这些闭小区间覆盖整个 $[0,1/2]$，包括两个端点和全部交界点。
它们给出通常闭半径有限网的显式中点构造；有限网及覆盖数的约定见
Vershynin，[*High-Dimensional Probability*，第一版，§4.2，
Definitions 4.2.1--4.2.2](https://www.math.uci.edu/~rvershyn/papers/HDP-book/HDP-1.pdf)。
这里对网的计数只是一维区间计数。

对每个 $j$，保持 $\Pi_{\gamma,t_j}$ 的所有规则不变。
具体地，取得 $u_0$ 后执行 $N$ 并取得 $u_1$，
当 $u_1\le\gamma\tau_{t_j}$ 时执行 $L_0,N,N$，否则执行 $N,L_0,N$，
其中 $\tau_t=17+t/4$。每个原子后立即必读；两分支均为四原子加初读，
恰有五报告。在后一分支，$a_2=b_2^{(2)}$ 始终共用原先取得的同一报告，
不增加报告或误差变量。末端仍使用容限 $\gamma$ 的 III (13.5)
严格正共同来源系统，只在无解时输出 $2$。
这正是 III 命题 17.3 的协议，故其完整环境域 $\gamma$-可靠性保留，
从而也在完整环境域上 $\varepsilon$-可靠。

将 III 定理 18.3 直接用于中心 $C_j=\gamma R_{t_j}$、实际来源
$S=\gamma R_s$ 及 (20.8)，得到

$$
 \{\gamma R_s:s\in[j/(2n),(j+1)/(2n)]\}
       \subseteq\operatorname{Succ}_\varepsilon(\Pi_{\gamma,t_j}).
\tag{20.9}
$$

该定理的实际历史对应在这里取如下精确参数：对这个固定 $S$ 的任意
允许报告历史 $y_i$，以其实际累计矩阵 $A_i$ 定义中心误差

$$
 \eta_i^{C_j}
   =\eta_i^S+\operatorname{tr}(A_i(S-C_j)),\qquad
 |\eta_i^{C_j}|\le\varepsilon+\delta=\gamma.
\tag{20.10}
$$

初读也包含在内。相同的完整父历史使同一个确定性成员执行同一下一原子，
所以 III (18.5) 的归纳给出中心上的同一完整合法历史；
并非只比较未执行分支的数值。中心在全部闭 $\gamma$ 误差历史上成功，
故同一成员在 $S$ 的原始历史上以同一末端判定输出 $2$。
这里固定 $j$ 后才量化 $S$ 的全部历史，误差可任意相关并依赖历史，
等号 $d_{\mathrm{op}}=\delta$ 和全部闭误差端点均被包含。
于是 (20.9) 对每个小区间成立，给出 (20.2) 和
$\nu_{3,\varepsilon}(K_\gamma)\le|F|\le n$。
由 $X>1$，还有 $n\le5X/2+1\le7X/2$，证明上界。

下界先取 $h\le1/1024$。置

$$
 m=\left\lfloor\frac1{512h}\right\rfloor,\qquad
 s_j=256hj\quad(0\le j\le m),\qquad
 P_h=\{\gamma R_{s_j}:0\le j\le m\}\subseteq K_\gamma.
\tag{20.11}
$$

因为 $256hm\le1/2$，全部参数合法；
$|s_i-s_j|\ge256h$ 对 $i\ne j$ 成立。
条目 $(\gamma R_s)_{00}=\gamma(3-s)$ 区分参数，故 $|P_h|=m+1$。

若一个全域 $\varepsilon$-可靠协议同时全误差覆盖其中两个来源，
在单位尺度来源的每份实际报告上同乘 $\gamma$ 再交给该协议，
并执行其同一动作、停止和输出，便得到一个全域
$\alpha$-可靠协议，其中 $\alpha=\varepsilon/\gamma=1-h$。
确切地，对每个固定 $T\in\mathcal M_3$ 和每个实际累计字 $A_i$，
$\operatorname{tr}(A_i\gamma T)=\gamma\operatorname{tr}(A_iT)$，
而 $[-\alpha,\alpha]$ 恰同乘 $\gamma$ 成为 $[-\varepsilon,\varepsilon]$。
确定性完整历史规则使此对应逐动作成立，包括初读、每次必读、停止和无限历史。
$T\mapsto\gamma T$ 是完整 $\mathcal M_3$ 上的保秩双射，
所以环境域可靠性没有缩小，严格正因子和同一个固定来源也保留。
因此所得协议将同时在两个单位来源 $R_{s_i},R_{s_j}$ 上
全 $\alpha$ 误差成功。

这正违反 III 引理 21.2：其条件为
$0<h\le1/1024$、$\alpha=1-h$ 及参数间距至少 $256h$，
全部由 (20.11) 满足。该引理已比较任意确定性完整历史协议，
包括任意长尾及无共同预算者，其共同伴随是实际严格正秩一来源。
这里仅作正比例缩放，不更换来源族、切口或闭端点的语义。
故每个全域 $\varepsilon$-可靠成员至多全误差覆盖 $P_h$ 的一个元素。
覆盖整个 $K_\gamma$ 的任何有限族也须覆盖 $P_h$，从而

$$
 \nu_{3,\varepsilon}(K_\gamma)
   \ge m+1
   =\left\lfloor\frac X{512}\right\rfloor+1
   >\frac X{512}\ge\frac X{1024}
       \qquad(h\le1/1024).
\tag{20.12}
$$

若 $h>1/1024$，则 $X<1024$，而 $K_\gamma$ 非空使空菜单不能覆盖，
故 $\nu_{3,\varepsilon}(K_\gamma)\ge1>X/1024$。
这补齐全部 $h\in(0,1)$，连同上界得到 (20.3)。∎

本定理复用的数学供应是 III 引理 17.2、命题 17.3、引理 18.2、
定理 18.3 及引理 21.2；有限网只作为上述中间步骤。
具体族的操作距离 (20.6)、连续参数菜单 (20.7)--(20.9) 与
全参数打包桥 (20.11)--(20.12) 给出这里的双边数量结论，属于本模型内推导
（repo-derived）。有限状态区分的相关文献为 van den Bos--Vaandrager，
[*State Identification for Labeled Transition Systems with Inputs and Outputs*，
Definitions 11、16 及 Theorem 6.1](https://arxiv.org/html/1907.11034v2)；
其有限状态模型和 Theorem 6.1 的两两不相容前提不供应本定理的连续族速率。

式 (20.3) 只对给定的 $K_\gamma$ 成立，完整环境域上未附加来源幅度界。
其量词仍为 (20.2)，不构造未知来源上的在线成员选择器；
不同时执行或拼接不同成员的轨迹。常数仅为充分的绝对常数。
本定理不对整个 $\mathcal I_3(\gamma)$ 给出线性界，
也不涉及最优常数、有效实数可行性判定或位复杂度。

## 追加锚（本行以下为增补区）

## 21. 四维严格正来源的同容限无限覆盖障碍

### 定义 21.1（四维合同、共同来源系统与参数族）

本节采用 [续卷 III](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_III.md)
定义 9.1、13.1、14.1 及推论 14.6 在 $k=4$ 的原合同。
来源域恰为

$$
 \mathcal M_4=
 \left\{\sum_{a=1}^{m}c_a\ell_a:
 m\in\{1,2\},\quad c_a\in\mathbb R_{>0}^{4},\quad
 \ell_a\in\mathbb R_{>0}^{1\times4}\right\}.
\tag{21.1}
$$

各因子在运行前固定，目标为初始矩阵的普通实秩。
原子满足 $Ne_j=e_{j+1}$（$j<3$）、$Ne_3=0$、
$L_0=e_0\mathbf1^{\mathsf T}$。只有一条不可复制、不可复位的轨迹；
$A_0=I$，初读与每个原子 $E_i\in\{N,L_0\}$ 后的报告均必须取得并计费：

$$
 A_i=E_iA_{i-1},\qquad
 y_i=\operatorname{tr}(A_iR)+\eta_i,\qquad
 |\eta_i|\le\varepsilon.
\tag{21.2}
$$

这里 $\varepsilon>0$ 为事先给定的有限实数，误差可任意相关并依赖全部历史，
包括闭区间的所有端点。动作、停止和输出是完整动作—报告历史的任意确定性函数，
不要求连续、可测、可计算或共同停止预算。
$\varepsilon$-可靠性在完整 $\mathcal M_4$ 上量化：对每个固定来源
$S\in\mathcal M_4$ 的每条允许历史，有限输出 $2$ 都蕴含
$\operatorname{rank}(S)=2$。记成功集合和逐来源成功域为
$\operatorname{Succ}_{\varepsilon}(\Pi)$、$\mathcal I_4(\varepsilon)$，
含义分别为该协议在同一来源的每条允许历史上有限输出 $2$，以及存在这样的可靠协议。
若 $\mathscr H_\varepsilon(R,\Pi)$ 为同一固定来源的全部允许历史，
一个预选族 $F$ 覆盖 $D\subseteq\mathcal I_4(\varepsilon)$ 的量词为

$$
 \forall R\in D\quad\exists\Pi_R\in F\quad
 \forall H\in\mathscr H_\varepsilon(R,\Pi_R)\quad
 \Pi_R\text{ 在 }H\text{ 上有限输出 }2,
\tag{21.3}
$$

其中 $F$ 在来源未知前固定，且每个成员在完整环境域上可靠。
$\nu_{4,\varepsilon}(D)$ 是此类有限族的最小基数，无有限族时记为 $\infty$。
同一个 $\Pi_R$ 须负责 $R$ 的全部误差历史。

为写出单位容限的证明，按 III 定义 12.1、14.3 置

$$
 \begin{aligned}
 a_i(R)&=\operatorname{tr}(N^iR),&
 b_j^{(q)}(R)&=\sum_{h=0}^{3-q}R_{hj},\\
 A_i(x,v)&=\sum_{h=0}^{3-i}x_hv_{h+i},&
 B_q&=\begin{cases}\{0,1,2,3\},&0\le q\le2,\\
                       \{0,1,2\},&q=3.
       \end{cases}
 \end{aligned}
\tag{21.4}
$$

下文 $\mathsf C_q(R,u)$ 恰为 III (14.4) 的 $k=4,\varepsilon=1$ 实例：

$$
 \exists x,v\in\mathbb R_{>0}^{4}\quad
 \sum_{h=0}^{3-q}x_h=1,\qquad
 |A_i(x,v)-u_i|\le1\ (0\le i\le q),\qquad
 |v_j-b_j^{(q)}(R)|\le2\ (j\in B_q).
\tag{21.5}
$$

其见证给出一个实际严格正秩一来源 $S=xv^{\mathsf T}$。
$q=3$ 时 $x_0=1$，$A_3=v_3$，$a_3=b_3^{(3)}$ 共享原先取得的同一个报告；
没有第二份 $b_3$ 报告或第二个误差变量。

对 $0\le s\le1/2$，定义

$$
 \begin{aligned}
 d_s&=\frac{37}{2}+s-\frac{125}{44+s},&
 \lambda_s&=\frac12+s,& c_s&=94-d_s-10s,\\
 r_s&=(c_s,3-s,10,1),&
 w_s&=(1,d_s,23/2,8),&
 Q_s&=\begin{pmatrix}r_s\\w_s\\\lambda_sr_s\\r_s\end{pmatrix},\\
 \tau_s&=17+s/4,&
 L_s&=\frac{39}{2}-\frac{125}{44+s},& M&=\frac{39}{2},\\
 \rho_s&=\frac{44+s}{50},&
 D_s&=M-L_s=\frac{125}{44+s},&
 Q_{\varepsilon,s}&=\varepsilon Q_s.
 \end{aligned}
\tag{21.6}
$$

### 引理 21.2（实际严格正实现与规范数据）

每个 $Q_{\varepsilon,s}$ 都属于 $\mathcal M_4$，普通初始秩恰为二。
单位尺度的真实数据满足

$$
 \begin{aligned}
 (a_0,a_1,a_2,a_3)(Q_s)&=(100,15,18,1),\\
 b^{(0)}(Q_s)&=(2+\lambda_s)r_s+w_s,\\
 b^{(1)}(Q_s)&=(1+\lambda_s)r_s+w_s,\\
 b^{(2)}(Q_s)&=r_s+w_s=(c_s+1,L_s+2,M+2,9),\\
 b^{(3)}(Q_s)&=r_s,\\
 P_1(Q_s)&=[99,101]\times[14,16]\times[17,19]\times[0,2].
 \end{aligned}
\tag{21.7}
$$

此外有

$$
 M-D_s\rho_s=17,\qquad
 7+\frac{25}{2}\rho_s=\tau_s+1.
\tag{21.8}
$$

**证明。** 直接由 (21.6) 得
$31/2<d_s<19$、$70<c_s<80$、$5/2\le3-s\le3$、
$1/2\le\lambda_s\le1$。取 $\alpha=1/1000$，则

$$
 Q_s=
 \begin{pmatrix}1\\\alpha\\\lambda_s\\1\end{pmatrix}
       \frac{r_s-\alpha w_s}{1-\alpha^2}
 +\begin{pmatrix}\alpha\\1\\\alpha\lambda_s\\\alpha\end{pmatrix}
       \frac{w_s-\alpha r_s}{1-\alpha^2}.
\tag{21.9}
$$

展开四行分别为 $r_s,w_s,\lambda_sr_s,r_s$。
两个列因子严格正；两个行因子分子的逐坐标下界可分别取为

$$
 \begin{aligned}
 &(70-\alpha,\ 5/2-19\alpha,\ 10-23\alpha/2,\ 1-8\alpha)>0,\\
 &(1-80\alpha,\ 31/2-3\alpha,\ 23/2-10\alpha,\ 8-\alpha)>0.
 \end{aligned}
\tag{21.10}
$$

分母也严格正，故这是真正的两项严格正外积分解。
行 $0,1$、列 $2,3$ 的子式为
$10\cdot8-23/2=137/2\ne0$；两项分解又给出秩至多二，故普通秩恰为二。
正比例缩放只须把两个行因子同乘 $\varepsilon$。

四个上对角和依次为
$c_s+d_s+10\lambda_s+1=100$、
$(3-s)+23/2+\lambda_s=15$、$10+8=18$ 和 $1$。
前 $4-q$ 行之和给出全部 $b^{(q)}$。
特别地，$3-s+d_s=L_s+2$，不是 $L_s$；这一差值参与下面的闭误差计算。
最后 $D_s\rho_s=5/2$ 以及
$(25/2)\rho_s=11+s/4$ 给出 (21.8)。∎

### 命题 21.3（逐来源的七报告全误差成功）

对每个 $s\in[0,1/2]$，存在一个在完整 $\mathcal M_4$ 上单位容限可靠的协议
$\Pi_s$，在 $Q_s$ 的每条允许误差历史上恰以七报告输出 $2$。

**证明。** 先取得初读 $u_0$，连续执行 $N,N$ 并分别取得 $u_1,u_2$。
接着执行

$$
 \begin{cases}
 L_0,N,N,N,&u_2\le\tau_s\quad(q=2),\\
 N,L_0,N,N,&u_2>\tau_s\quad(q=3).
 \end{cases}
\tag{21.11}
$$

末端当且仅当 III 引理 13.2 的系统 (13.5) 在 $k=4,\varepsilon=1$
无严格正共同解时输出 $2$，否则停止不作秩断言。
这里对应的 $x,v$、$A_i$ 和归一化正是 (21.4)--(21.5)；
末端用全部已取得报告约束 $|A_i-y_{a_i}|\le1$ 及 $|v_j-y_{b_j}|\le1$。
任一实际秩一来源在其允许历史上自身提供同一组严格正解，
故不会输出 $2$。完整 $\mathcal M_4$ 的普通秩只有一或二，因而该规则全域可靠。
此定义也适用于其他来源上的所有报告历史。

两分支都执行六个原子，初读计入恰为七报告。
$q=2$ 取得全部四个新 $b_j$；$q=3$ 仅新取 $b_0,b_1,b_2$，
$b_3=a_3$ 使用刚才第三次 $N$ 后的旧报告 $u_3$。

固定 $Q_s$ 的任意允许前缀。若 $u_2\le\tau_s$ 且 $\mathsf C_2$ 成立，
将同一正解写成 $x_0=z$、$x_1=1-z$、$x_2,x_3>0$，其中 $0<z<1$。
由 (21.7) 和 (21.5) 有 $v_1\ge L_s$、$v_2\ge M$、$v_3\ge7$，所以

$$
 \begin{aligned}
 A_1&=zv_1+(1-z)v_2+x_2v_3>M-D_sz,\\
 A_1&\le u_1+1\le17
       \quad\Longrightarrow\quad z>\rho_s,\\
 A_2&=zv_2+(1-z)v_3
       \ge7+\frac{25}{2}z>\tau_s+1\ge u_2+1.
 \end{aligned}
\tag{21.12}
$$

这与旧报告约束矛盾。因此整个闭分支都有 $\neg\mathsf C_2$，
而且只用了实际取得的 $u_1,u_2$，未使用 $u_3$。

若 $u_2\ge\tau_s$ 且在第三次 $N$ 后 $\mathsf C_3$ 成立，
则 $x_0=1$，并由共享旧报告及同一组参数得到

$$
 \begin{aligned}
 v_1&\ge1-s,& 8\le v_2&\le12,&
 0<v_3=A_3&\le u_3+1\le3,\\
 A_1&=v_1+x_1v_2+x_2v_3\le u_1+1\le17
       &&\Longrightarrow\quad x_1v_2<16+s.
 \end{aligned}
\tag{21.13}
$$

于是

$$
 A_2=v_2+x_1v_3
       <v_2+\frac{3(16+s)}{v_2}
       \le16+s/4=\tau_s-1\le u_2-1.
\tag{21.14}
$$

中间不等式由函数 $v\mapsto v+3(16+s)/v$ 在 $[8,12]$ 上的凸性得到：
端点值为 $14+3s/8$ 和 $16+s/4$，后者较大，差为 $2-s/8>0$。
这又违反旧报告约束，故整个闭分支都有 $\neg\mathsf C_3$。
特别地，等号 $u_2=\tau_s$ 时两个切口都安全，(21.11) 将它分给 $q=2$。

III 引理 14.4 在这里的对应为 $R=Q_s$、$k=4$、$\varepsilon=1$，
以及实际选定的 $q=2$ 或 $3$ 和其原旧前缀。
该引理保证每份允许补全报告均无严格正秩一相容来源。
因此上述可靠末端规则对 $Q_s$ 的全部允许误差历史均输出 $2$；
没有对误差相关性增加条件，所有端点也均包含在内。∎

### 引理 21.4（两个早切口的实际秩一伴随）

对每个 $s\in[0,1/2]$，均有
$\mathsf C_0(Q_s,(100))$ 和 $\mathsf C_1(Q_s,(100,16))$。
它们各有一个严格正秩一来源实现，且全部新坐标满足 $v=b^{(q)}(Q_s)$。

**证明。** 对 $q=0$，置 $v=b^{(0)}(Q_s)$。由 (21.7) 得
$v_0>176$，而 $v_1<28$、$v_2<42$、$v_3\le11$。
取

$$
 m=\frac{v_1+v_2+v_3}{3},\qquad
 z=\frac{100-m}{v_0-m},\qquad
 x=\left(z,\frac{1-z}{3},\frac{1-z}{3},\frac{1-z}{3}\right).
\tag{21.15}
$$

因为 $m<42<100<v_0$，有 $0<z<1$。
所以 $x,v$ 严格正，$\sum_{h=0}^3x_h=1$，$A_0=100$，
且所有 $j\in B_0$ 均有 $v_j-b_j^{(0)}=0$。

对 $q=1$，置 $v=b^{(1)}(Q_s)$。现在
$0<v_0<161$、$0<v_1<25$、$53/2\le v_2\le63/2<32$、
$19/2\le v_3\le10$。定义

$$
 \begin{aligned}
 x_0&=\frac14,&
 x_1&=\frac{16-v_1/4-3v_3/4}{v_2-v_3},&
 x_2&=\frac34-x_1,\\
 x_3&=\frac{100-v_0/4-x_1v_1-x_2v_2}{v_3}.
 \end{aligned}
\tag{21.16}
$$

分母 $v_2-v_3>0$；分子严格大于
$16-25/4-30/4=9/4>0$，故 $x_1>0$。
又有 $v_1/4+3v_2/4\ge159/8>16$，故 $x_1<3/4$，从而 $x_2>0$。
最后

$$
 \frac{v_0}{4}+x_1v_1+x_2v_2
       <\frac{161}{4}+32\left(x_1+x_2\right)
       =\frac{257}{4}<100,
\tag{21.17}
$$

所以 $x_3>0$。这些参数满足
$x_0+x_1+x_2=1$、$(A_0,A_1)=(100,16)$，
且对全部 $j\in B_1$ 有 $v_j-b_j^{(1)}=0$。
两种情形的 $S=xv^{\mathsf T}$ 均为实际严格正秩一来源。
其新报告直接取共同真值 $v_j$；旧报告分别取 $100$ 或 $(100,16)$，
在 $Q_s$ 上的误差分别为 $0$ 或 $(0,1)$，在伴随来源上均为零。∎

### 引理 21.5（两个晚切口的实际秩一伴随）

固定 $0\le s<t\le1/2$，选定 $\tau_s<u<\tau_t$，并置

$$
 p=(100,16,u,2).
\tag{21.18}
$$

这是 $Q_s,Q_t$ 的共同合法纯 $N$ 报告向量。
此外，$\mathsf C_2(Q_s,p_{\le2})$ 和 $\mathsf C_3(Q_t,p)$ 均有实际严格正解。

**证明。** $17<u<137/8$，故由 (21.7)，$p$ 属于两来源的 $P_1$。
对 $q=2$，定义

$$
 \begin{aligned}
 h&=\frac{u-\tau_s}{25},&z&=\rho_s+h,&
 v&=(c_s+1,L_s,M,7),\\
 x_0&=z,&x_1&=1-z,&x_2&=\frac{D_sh}{7},\\
 x_3&=\frac{100-z(c_s+1)-(1-z)L_s-MD_sh/7}{7}.
 \end{aligned}
\tag{21.19}
$$

有 $0<h<1/200$、$22/25\le\rho_s\le89/100$，所以 $0<z<1$。
又有 $0<D_s<3$、$0<L_s<M<20$、$c_s+1<81$，从而

$$
 z(c_s+1)+(1-z)L_s+MD_sh/7<81+1=82<100.
\tag{21.20}
$$

故全部参数严格正，且 $x_0+x_1=1$。
代入 (21.8) 后得到

$$
 \begin{aligned}
 A_0&=100,& A_1&=M-D_s(\rho_s+h)+D_sh=17,\\
 A_2&=7+\frac{25}{2}(\rho_s+h)
       =\tau_s+1+\frac{u-\tau_s}{2},\\
 (A_0-p_0,A_1-p_1,A_2-p_2)
       &=\left(0,1,1-\frac{u-\tau_s}{2}\right),\\
 v-b^{(2)}(Q_s)&=(0,-2,-2,-2).
 \end{aligned}
\tag{21.21}
$$

第三个旧报告差在 $(0,1)$ 内；全部 $B_2$ 约束也都满足。
因此一个固定 $S=xv^{\mathsf T}$ 实现整个 $\mathsf C_2$，
共同完整补全报告可取为

$$
 (100,16,u,\ c_s+1,L_s+1,M+1,8).
\tag{21.22}
$$

四个新报告分别为两来源对应真值的中点；特别是第二个使用
$b_1^{(2)}(Q_s)=L_s+2$ 和伴随真值 $L_s$。

对 $q=3$，另取

$$
 \begin{aligned}
 v&=(c_t,1-t,12,3),&x_0&=1,\\
 x_1&=\frac{u-13}{3},&x_2&=\frac{4(\tau_t-u)}{3},&
 x_3&=\frac{100-c_t-x_1(1-t)-12x_2}{3}.
 \end{aligned}
\tag{21.23}
$$

这里 $v>0$、$0<x_1<11/8$、$0<x_2<1/6$，并且
$c_t+x_1(1-t)+12x_2<80+11/8+2<100$，故 $x_3>0$。
同一组参数直接给出

$$
 \begin{aligned}
 (A_0,A_1,A_2,A_3)&=(100,17,u-1,3),\\
 (A_0-p_0,A_1-p_1,A_2-p_2,A_3-p_3)&=(0,1,-1,1),\\
 (v_j-b_j^{(3)}(Q_t))_{j\in B_3}&=(0,-2,2).
 \end{aligned}
\tag{21.24}
$$

其中 $A_1=1-t+4(u-13)+4(\tau_t-u)=17$。
首坐标 $v_0=c_t$ 满足实际 $B_3$ 约束，并由 $x_3$ 保持初读方程。
因此 $S=xv^{\mathsf T}$ 是满足整个 $\mathsf C_3$ 的一个固定严格正秩一来源。
共同完整补全报告为

$$
 (100,16,u,2,\ c_t,2-t,11).
\tag{21.25}
$$

三个新报告是相应中点；末坐标沿用旧报告 $2$。
同一个 $a_3=b_3^{(3)}$ 真值在 $Q_t$ 上为 $1$，在伴随来源上为 $3$，
所以该旧报告在两者上恰用相反误差端点。没有补读该坐标。∎

### 定理 21.6（任意完整历史协议的两两取得不相容）

任何在完整 $\mathcal M_4$ 上单位容限可靠的确定性完整历史协议，
至多在一个 $Q_s$（$0\le s\le1/2$）上全误差成功。

**证明。** 反设同一协议 $\Pi$ 在 $Q_s,Q_t$ 上均成功，其中 $s<t$。
III 定理 14.2 在 $k=4,\varepsilon=1$ 给出由同一个 $\Pi$ 确定的单个可靠正规形
$\widehat\Pi$，且

$$
 \operatorname{Succ}_1(\Pi)
       \subseteq\operatorname{Succ}_1(\widehat\Pi).
\tag{21.26}
$$

该包含同时保留全部成功来源，没有按 $s,t$ 分别选择替代协议。
按引理 21.5 选定 $u$，使用共同合法纯 $N$ 前缀 (21.18) 驱动这个正规形。
首次 $L_0$ 前停止不作断言已经违反全误差成功。
在 $q=0$ 或 $q=1$ 选择 $L_0$ 时，引理 21.4 与 III 引理 14.4
给出允许补全报告及其固定秩一伴随，使正规形不能输出 $2$。
因此它必须继续到共同前缀 $(100,16,u)$。

若在此选择 $q=2$，(21.19)--(21.22) 使它遗漏 $Q_s$ 的一条合法历史。
若继续一次 $N$，下一报告可取 $2$，而在 $q=3$ 的
(21.23)--(21.25) 使它遗漏 $Q_t$ 的一条合法历史。
正规形在 $q=3$ 不再选择 $N$，上述情况穷尽全部决定，故矛盾。

这里对每个实际选定的切口仅固定一个 $S=xv^{\mathsf T}$。
它在整个所选前缀和补全历史中不变；不同切口不要求共用一个 $S$。
为明确任意原协议长尾的范围，III 定理 14.2 的固定报告表在本构造中如下：
首次 $L_0$ 前使用同一个 $p_{\le q}$；此后累计矩阵若为
$N^jL_0N^q$，就使用该切口上述共同补全报告的对应 $b_j$ 值；
累计矩阵为零则报告零。
III 引理 10.1 保证任意后继动作只会重复这些坐标或进入永久零状态。
对 $q=3,j=3$ 一直使用原旧报告 $2$。
每次报告在选定的 $Q_s$ 或 $Q_t$ 与同一个固定 $S$ 上都合法，
重复给出相同报告也符合任意相关、依赖历史的误差合同。
确定性逐前缀迫使动作、停止和输出一致；若原协议在该来源上全误差成功，
它就会在这个秩一伴随上也有限输出 $2$，违反可靠性。
因此正规形归约没有留下任意长尾、重读、再次 $L_0$ 或无限运行的例外。∎

### 定理 21.7（每个正容限的四维无限覆盖数）

对每个事先给定的有限实数 $\varepsilon>0$ 和每个有限集合
$T\subseteq[0,1/2]$，有

$$
 \begin{aligned}
 &Q_{\varepsilon,s}\in\mathcal I_4(\varepsilon)
       \quad(0\le s\le1/2),\\
 &\nu_{4,\varepsilon}
       (\{Q_{\varepsilon,s}:s\in T\})=|T|,\\
 &\nu_{4,\varepsilon}(\mathcal I_4(\varepsilon))=\infty.
 \end{aligned}
\tag{21.27}
$$

逐来源成功可由恰七报告的全域可靠协议达到；下界比较任意确定性完整历史协议，
不附加共同预算或正则性条件。

**证明。** 固定上述 $\varepsilon$。
把单位构造的来源 $Q_s$、伴随 $xv^{\mathsf T}$、每份旧新报告和阈值
分别同乘 $\varepsilon$：伴随参数取 $x$ 不变、$v$ 换为 $\varepsilon v$，
阈值成为 $\varepsilon\tau_s$。
因任意实际累计字 $A_i$ 都满足

$$
 \operatorname{tr}(A_i\varepsilon S)
       =\varepsilon\operatorname{tr}(A_iS),
\tag{21.28}
$$

所有旧报告差由 $1$ 缩放为 $\varepsilon$，
新真值差由 $2$ 缩放为 $2\varepsilon$，中点和共享旧报告也准确缩放。
闭区间 $[-1,1]$ 恰变为 $[-\varepsilon,\varepsilon]$，正性和普通秩保留。
式 (21.11) 的协议对每份实际报告除以 $\varepsilon$ 后执行同一规则，
末端改用容限 $\varepsilon$ 的严格正相容系统。
由命题 21.3，它在 $Q_{\varepsilon,s}$ 的全部允许历史上恰以七报告成功。
$S\mapsto\varepsilon S$ 是完整 $\mathcal M_4$ 上的保秩双射，
所以可靠性仍量化完整环境域，得到第一式。

反之，若某个全域 $\varepsilon$-可靠协议同时成功于两个不同的
$Q_{\varepsilon,s},Q_{\varepsilon,t}$，就在单位尺度实际运行中，
将每份报告同乘 $\varepsilon$ 后交给它，并照做它指定的动作、停止及输出。
式 (21.28) 和确定性逐前缀归纳给出整个历史的对应，包括初读、每步必读和无限历史。
所得协议全域单位容限可靠且同时成功于 $Q_s,Q_t$，违反定理 21.6。
故任一允许的覆盖成员至多覆盖缩放族中的一个参数。

条目 $(Q_{\varepsilon,s})_{01}=\varepsilon(3-s)$ 区分参数，
所以有限来源集恰有 $|T|$ 个元素。每个元素各取上述一个七报告成员，
得到覆盖数至多 $|T|$；两两不相容给出反向界。
$T=\varnothing$ 时空族达到零。
若有 $n\ge1$ 个成员覆盖全部 $\mathcal I_4(\varepsilon)$，
取参数 $s_j=j/(2n)$（$0\le j\le n$），便有 $n+1$ 个属于该域的来源，
而每个成员至多覆盖其中一个，矛盾。空族也遗漏 $Q_{\varepsilon,0}$。
因此无有限族满足 (21.3)，证明最后一式。∎

### 定义 21.8（数学供应与结论边界）

本节复用 III 引理 13.2、定义 14.3、引理 14.4 的严格正共同来源接口，
以及 III 定理 14.2、14.5、推论 14.6 对任意历史、逐来源成功和覆盖的解释。
与 III 定理 17.5 相比，(21.27) 在完整四维严格正环境域成立：
(21.9) 是四维实际两项正分解，(21.15)--(21.16) 处理新增的两个早切口，
(21.19)、(21.23) 在同一组四维参数中同时满足初读与全部旧新坐标。
这不是从三维结论假设覆盖数的维数单调性，也不是零填充。

III 定理 20.3 在任意维数以 $\varepsilon$-可靠有限族覆盖
$\mathcal I_k(\varepsilon+\delta)$，其条件为 $\delta>0$。
本节始终覆盖同一个容限的 $\mathcal I_4(\varepsilon)$，
不把正容限差的结论代入 $\delta=0$。
本卷定理 20.2 的线性界只比较特定三维连续族在正容限差下的覆盖数；
(21.27) 则给出四维同容限下的无限障碍，没有由该线性界取极限。
这些结论各保留原成功集合和误差量词。

严格正性在 (21.12)、(21.13) 的严格不等式中承重。
例如把 (21.19) 形式地置 $h=0$，就出现 $x_2=0$，
其 $A_1=17$、$A_2=\tau_s+1$ 不再被 (21.12) 排除，
但它并非允许来源。非负闭包的覆盖结论不在本节范围内。
正缩放也不包含 $\varepsilon=0$；本节不改写精确读数结果，
不决定 $k\ge5$ 的同容限覆盖数，也不声称七报告对每个来源都最优。
预选族的存在量词不提供未知来源上的在线成功成员选择器，
不合并不同成员的轨迹或报告，不给出有效实可行性、有限位存储或位复杂度结论。

共同报告的中点步骤与 set-membership 背景沿用 III 定义 14.7、定理 17.5
所引的 Casini--Garulli--Vicino §4 式 (7)--(9) 及
van den Bos--Vaandrager Definitions 11、16、Theorem 6.1；
这些文献的线性回归或有限状态假设不供应本节的四维严格正伴随。
承重增量为 (21.6) 的显式四维族、七报告全误差成功及四切口的实际正见证，
属于既定模型内的推导（repo-derived），不宣称 Lean 验证或外部原创性。

## 追加锚（本行以下为增补区）

## 23. 四维固定来源族的精确七报告费用

### 定义 23.1（逐来源全误差费用）

本节严格采用定义 21.1 的完整 $\mathcal M_4$ 和 (21.2) 的观察合同：
来源在运行前固定，是一项或两项严格正外积之和，目标为初始矩阵的普通实秩；
仅允许 $N,L_0$，只有一条不可复制、不可复位的轨迹。
初读及每个原子后的报告均必须取得并计费。
给定有限实数 $\varepsilon>0$，每份报告的误差满足闭约束
$|\eta_i|\le\varepsilon$，可任意相关并依赖全部历史。
协议是完整动作—报告历史的任意确定性函数，不附加正则性或全域停止预算。
可靠性始终量化完整 $\mathcal M_4$ 的每个固定来源及其全部允许误差历史。

沿用 III 定义 16.1 在 $k=4$ 的费用，明确写为

$$
 \begin{aligned}
 c_{4,\varepsilon}(R)=\min\{B\in\mathbb N_{\ge1}:\;&
  \exists\Pi\quad\Pi\text{ 在完整 }\mathcal M_4
                          \text{ 上 }\varepsilon\text{-可靠},\\
 &\forall H\in\mathscr H_\varepsilon(R,\Pi)\quad
       \Pi\text{ 在 }H\text{ 上至多 }B\text{ 报告内有限输出 }2\}.
 \end{aligned}
\tag{23.1}
$$

空集的最小值为 $\infty$。协议可按固定 $R$ 存在选择；同一个协议须负责
该 $R$ 的全部误差历史，在其他来源上只要求可靠，不要求成功或停止。
本节只计算 (21.6) 的四维 $Q_{\varepsilon,s}=\varepsilon Q_s$ 的这个费用。
以下的 $A_i(x,v)$、$c_s,L_s,M,D_s$ 全部保持 (21.4)、(21.6) 的含义。

### 引理 23.2（两个晚切口的部分报告正伴随）

在定义 23.1 的合同下取 $\varepsilon=1$。对每个 $s\in[0,1/2]$，置

$$
 p=(100,16,18,2),\qquad
 J_2=\{0,1,2\},\qquad J_3=\{0,1\}.
\tag{23.2}
$$

这是 $Q_s$ 的允许纯 $N$ 报告向量。对每个 $q\in\{2,3\}$，
存在一个固定 $S_s^{[q]}=x^{[q]}(v^{[q]})^{\mathsf T}\in\mathcal M_4$，
其因子严格正、普通秩为一，并满足

$$
 \sum_{h=0}^{3-q}x_h^{[q]}=1,\qquad
 |A_i(x^{[q]},v^{[q]})-p_i|\le1\quad(0\le i\le q),\qquad
 |v_j^{[q]}-b_j^{(q)}(Q_s)|\le2\quad(j\in J_q).
\tag{23.3}
$$

这里只约束 $J_q$ 内的后切口坐标，不断言完整 $\mathsf C_q$ 成立。

**证明。** 引理 21.2 给出实际纯 $N$ 真值 $(100,15,18,1)$，
所以 $p$ 的误差为 $(0,1,0,1)$，属于允许闭区间。

先取 $q=2$，定义

$$
 \begin{aligned}
 v^{[2]}&=(c_s+1,L_s,M,1),&
 x_0^{[2]}&=9/10,&x_1^{[2]}&=1/10,\\
 x_2^{[2]}&=\frac9{10}D_s-\frac52,&
 x_3^{[2]}&=100-\frac9{10}(c_s+1)-\frac1{10}L_s-Mx_2^{[2]}.
 \end{aligned}
\tag{23.4}
$$

由 $0\le s\le1/2$，
$250/89\le D_s\le125/44$，从而

$$
 0<\frac5{178}\le x_2^{[2]}\le\frac5{88}<\frac1{16}.
\tag{23.5}
$$

引理 21.2 的 $70<c_s<80$、$0<L_s<M<20$ 使 $v^{[2]}$ 严格正，且

$$
 \frac9{10}(c_s+1)+\frac1{10}L_s+Mx_2^{[2]}
       <81+\frac{20}{16}<100.
\tag{23.6}
$$

故 $x_3^{[2]}>0$。同一组参数直接给出

$$
 \begin{aligned}
 (A_0,A_1,A_2)&=(100,17,353/20),\\
 (A_0-p_0,A_1-p_1,A_2-p_2)&=(0,1,-7/20),\\
 (v_j^{[2]}-b_j^{(2)}(Q_s))_{j\in J_2}&=(0,-2,-2).
 \end{aligned}
\tag{23.7}
$$

其中 $A_1=M-(9/10)D_s+x_2^{[2]}=17$，
$A_2=(9/10)M+1/10=353/20$。
三个新共同报告可固定取为 $(c_s+1,L_s+1,M+1)$。
未约束的 $v_3^{[2]}=1$ 与实际 $b_3^{(2)}(Q_s)=9$ 不相容，
所以这个见证没有提供完整补全的共同来源。

再取 $q=3$，定义

$$
 \begin{aligned}
 v^{[3]}&=(c_s,1-s,14,3),&
 x^{[3]}&=\left(1,1,\frac16,
              \frac{100-c_s-(1-s)-7/3}{3}\right).
 \end{aligned}
\tag{23.8}
$$

$1-s\ge1/2$，且
$c_s+(1-s)+7/3<80+1+7/3<100$，所以全部因子严格正；
归一化为 $x_0^{[3]}=1$。逐式代入得到

$$
 \begin{aligned}
 (A_0,A_1,A_2,A_3)&=(100,31/2-s,17,3),\\
 (A_0-p_0,A_1-p_1,A_2-p_2,A_3-p_3)&=(0,-1/2-s,-1,1),\\
 (v_j^{[3]}-b_j^{(3)}(Q_s))_{j\in J_3}&=(0,-2).
 \end{aligned}
\tag{23.9}
$$

全部旧报告差均在 $[-1,1]$ 内，包括 $s=0,1/2$。
两个新共同报告可固定取为 $(c_s,2-s)$。
旧报告 $p_3=2$ 同时兼容实际 $a_3=1$ 与伴随 $A_3=v_3^{[3]}=3$，
仍是同一份报告，不再产生第二个末坐标误差。
未约束的 $v_2^{[3]}=14$ 与实际 $b_2^{(3)}(Q_s)=10$ 相差 $4$，
故这里也未断言完整补全相容。
两种情形均以同一个严格正外积实现全部所列约束，证明 (23.3)。∎

### 定理 23.3（每个参数的精确七报告费用）

在定义 23.1 的完整来源、操作、误差及确定性历史合同下，对每个有限实数
$\varepsilon>0$ 和每个 $s\in[0,1/2]$，均有

$$
                  c_{4,\varepsilon}(Q_{\varepsilon,s})=7.
\tag{23.10}
$$

上界由命题 21.3 的协议达到。下界比较所有全域可靠完整历史协议：
每个这样的协议在该固定来源上都有一条允许历史，不能在六报告内输出 $2$。
这不声称每条允许历史都需要七报告。

**证明。** 先取单位容限。命题 21.3 已给出在 $Q_s$ 全误差成功的七报告
全域可靠协议，因此只须排除六报告保证。

固定任意全域单位容限可靠协议 $\Pi$。
在首次 $L_0$ 前，依次选择 (23.2) 的纯 $N$ 报告；
若已执行四次 $N$，累计矩阵为零，此后始终报告零。
这些报告对同一个实际来源 $Q_s$ 均合法。
III 引理 10.3 为真实数据 $(100,15,18,1)$ 提供一个固定严格正秩一来源
$S^{[N]}$，匹配全部四个纯 $N$ 真值。
故任何尚未执行 $L_0$ 的停止前缀均有该同一个来源相容，可靠性排除输出 $2$。
这也处理从初读起停止，以及先达到 $N^4=0$ 再执行任意原子的永久零尾部。

若在湮灭前首次选择 $L_0$，记其前的 $N$ 数为 $q\in\{0,1,2,3\}$。
在六报告预算内一共至多执行五个原子。
对首次 $L_0$ 后的任意非零累计矩阵，III 引理 10.1 给出
$N^jL_0N^q$；其取得至少需要 $q+1+j$ 个原子，故

$$
 j\le4-q,\qquad 0\le j<4.
\tag{23.11}
$$

再次执行 $L_0$ 只重复相应坐标并消耗一个原子，不能扩大这个范围；
一旦累计矩阵为零，所有后继仍为零。
因此所有不超过六报告的后继字只会取得下表列出的非零坐标：

| 首切口 $q$ | 六报告内的全部可能 $b$ 指标 | 固定秩一伴随 | 对应指标的共同报告 |
| --- | --- | --- | --- |
| $0$ | $0,1,2,3$ | 引理 21.4 的 $q=0$ 来源 | $b_j^{(0)}(Q_s)$ |
| $1$ | $0,1,2,3$ | 引理 21.4 的 $q=1$ 来源 | $b_j^{(1)}(Q_s)$ |
| $2$ | $0,1,2$ | (23.4) 的 $S_s^{[2]}$ | $(c_s+1,L_s+1,M+1)_j$ |
| $3$ | $0,1$ | (23.8) 的 $S_s^{[3]}$ | $(c_s,2-s)_j$ |

在实际选定的切口一次性固定表中的来源 $S$，以后不再更换它。
前两个切口的旧前缀分别为 $(100)$、$(100,16)$，正是引理 21.4 的前缀；
后两个切口使用引理 23.2 的 $p_{\le q}$。
故所选 $S$ 与整个旧前缀相容。此后每次非零读数按表中对应指标报告，
零矩阵报告零，重复坐标始终报告同一个表值。
引理 21.4 或 (23.7)、(23.9) 保证每份报告对 $Q_s$ 与这个固定 $S$
各自只需绝对值至多 $1$ 的误差。两来源的误差值可不同，
重复误差和闭区间端点均符合原合同。

对实际前缀归纳，两个来源得到相同完整动作—报告历史，
确定性迫使 $\Pi$ 作相同下一动作、停止及输出决定。
因此可靠性排除它在任一不超过六报告的所选前缀输出 $2$。
若它提前停止而不作断言，已违反六报告成功保证；
若继续到第六报告，再为 $Q_s$ 任意合法延长报告历史，仍不可能追溯地产生
六报告内的成功。这穷尽无 $L_0$、四个非零切口、重复 $L_0$ 及零尾部。
每条用于反驳的有限实际历史都只使用一个固定伴随，未拼接不同来源的报告。
所以 $c_{4,1}(Q_s)\ge7$，与上界合得等号。

最后固定任意 $\varepsilon>0$。对完整 $\mathcal M_4$，
$T\mapsto\varepsilon T$ 是保秩、保严格正性的双射，且每个实际累计字均满足

$$
 \operatorname{tr}(A_i\varepsilon T)=\varepsilon\operatorname{tr}(A_iT).
\tag{23.12}
$$

将上述同一伴随的 $v$、所有旧新报告及误差同乘 $\varepsilon$，
保持 $x$ 和动作字不变，就得到完整闭 $\varepsilon$ 误差合同的相同反驳。
等价地，若有六报告的全域 $\varepsilon$-可靠协议，在单位尺度运行时把每份
实际报告乘以 $\varepsilon$ 后交给它，照做其动作、停止和输出，
便得到六报告的全域单位容限可靠协议，违反刚证的下界。
此对应由相同父历史逐步建立，不只比较某个预定词。
上界则把实际报告除以 $\varepsilon$ 后执行命题 21.3 的同一规则。
初读、每步报告、共享旧报告和停止费用全部保留，故 (23.10) 成立。∎

### 约定 23.4（供应、增量与未决范围）

| 数学来源 | 本节使用的内容与边界 |
| --- | --- |
| III 定义 16.1 | 逐来源全误差统一预算及完整域可靠性，专门化为 (23.1)。 |
| 引理 21.2、命题 21.3 | 原有四维严格正秩二族、真实数据及七报告上界，不重新构造实际来源。 |
| 引理 21.4 | $q=0,1$ 的完整严格正伴随，使用原来的相同旧前缀。 |
| III 引理 10.1、10.3 | 任意原子字归约、永久零状态及全部纯 $N$ 数据的正秩一实现。 |
| III 定理 14.2 | 只提供保成功集合的正规形，不保原费用；本节下界直接使用 (23.11)，不从正规形推断原协议费用。 |
| 本节 (23.4)--(23.11) | 两个晚切口的部分报告严格正伴随及其任意历史费用下界。 |
| van den Bos--Vaandrager，[*State Identification for Labeled Transition Systems with Inputs and Outputs*，Definition 11、Theorem 6.1](https://arxiv.org/html/1907.11034v2) | 自适应区分的文献背景；其悬挂自动机和单射分裂条件不供应本节连续正矩阵的七报告下界。 |

本节补足定义 21.8 留出的该固定四维族的逐来源最优费用。
六报告下界需要新证明的部分报告伴随，不能从定理 21.7 的有限预选覆盖数推出。
它也不计算其他四维来源的最优费用，不给出 $k\ge5$ 或递归结论，
不改变第 22 节的条件或未决边界。
严格正性、$\varepsilon>0$ 和任意相关闭误差均保留；
非负闭包、零误差、随机协议及有效实数判定或位复杂度不由本节解决。
认证初始秩关系不等于恢复初始矩阵或辨认其一项、两项来源分解；
逐来源协议的存在不提供未知来源的在线选择器或有限预选覆盖。

## 24. 五维固定来源族的精确九报告费用

### 定义 24.1（五维逐来源全误差费用）

在定义 22.1 的完整 $\mathcal M_5$、$N,L_0$、单条不可复制不可复位轨迹和初读及每个原子后必读的收费合同下，定义

$$
 \begin{aligned}
 c_{5,\varepsilon}(R)=\min\{B\in\mathbb N_{\ge1}:\;&
 \exists\Pi\quad \Pi\text{ 在完整 }\mathcal M_5
                          \text{ 上 }\varepsilon\text{-可靠},\\
 &\forall H\in\mathscr H_\varepsilon(R,\Pi)\quad
       \Pi\text{ 在 }H\text{ 上至多 }B\text{ 报告内有限输出 }2\}.
 \end{aligned}
\tag{24.1}
$$

这里的可靠性仍量化完整来源域的一项或两项严格正外积之和，误差可任意相关并依赖全部历史；协议是任意确定性完整动作—报告函数。空集的最小值为 $\infty$。费用是单个固定来源的统一报告预算，不是预选覆盖基数，也不是未知来源上的在线选择器。

### 定理 24.2（五维族的精确九报告费用）

对每个有限实数 $\varepsilon>0$ 和每个 $s\in[0,1/2]$，令 $Q_{\varepsilon,s}=\varepsilon Q_s$。则

$$
                         c_{5,\varepsilon}(Q_{\varepsilon,s})=9.
\tag{24.2}
$$

**证明。** 上界由命题 22.3：把实际报告除以 $\varepsilon$ 后运行其分支规则和实际报告系统 $\mathsf D_q$。原尺度的约束为 $|A_i-y_i|\le\varepsilon$、$|v_j-w_j|\le\varepsilon$；对目标来源的允许报告，其解由三角不等式满足辅助约束 $|v_j-b_j^{(q)}(Q_{\varepsilon,s})|\le2\varepsilon$。共享末坐标只用同一旧报告 $y_4$。初读加上八次原子后的报告数为九，严格正性、普通秩和完整 $\mathcal M_5$ 可靠性均保持。

下面证明单位容限下的下界。设 $\Pi$ 是完整 $\mathcal M_5$ 上可靠的确定性协议，且在 $Q_s$ 的每条允许误差历史上至多八次报告输出 $2$。记

$$
 u=\tau_s+\frac1{16},\qquad p=(K,100,16,u,2).
\tag{24.3}
$$

因为 $17\le\tau_s\le17+1/8$，且 $u=\tau_s+1/16$，$p$ 与 $Q_s$ 的纯 $N$ 真值 $(K,100,15,18,1)$ 的逐坐标差均不超过一；故 $p$ 是一条合法的纯 $N$ 报告前缀。若协议在首次 $L_0$ 前停止并输出 $2$，III 引理 10.3 以正数据 $(p_0,\ldots,p_q)$ 给出固定严格正秩一来源，逐前缀重放产生同一历史，违反可靠性。这也覆盖初读即停。若它在取得 $p_0,\ldots,p_4$ 后继续执行一次 $N$，累计矩阵为 $N^5=0$；以后报告恒为零，III 引理 10.3 的同一来源仍给出相同历史，故八报告内也不能输出 $2$。所以在本历史上协议必在某个 $q\in\{0,1,2,3,4\}$ 次纯 $N$ 之后首次执行 $L_0$。

对这个 $q$ 固定一个严格正秩一伴随 $S_q=x^{[q]}(v^{[q]})^{\mathsf T}$。当 $q=0,1,2$ 时取引理 22.4 的三个早切口伴随；它们的旧坐标满足 $(A_0,\ldots,A_q)=(K,100,16,\ldots)$ 的闭一误差约束，且全部 $b_j^{(q)}$ 坐标逐项满足闭二误差约束。这里的 $q=1,2$ 正是把 IV 引理 21.4 的伴随提升一个首坐标并由 $A_0=K$ 解出尾权重，因而仍是五维严格正外积。

当 $q=3$，取

$$
 \begin{aligned}
 h&=\frac{u-\tau_s}{25}=\frac1{400},&z&=\rho_s+h,\\
 v^{[3]}&=(1001,c_s+1,L_s,M,7),&x^{[3]}_0&=z,&x^{[3]}_1&=1-z,\\
 x^{[3]}_2&=D_sh/7,\\
 x^{[3]}_3&=\frac{100-z(c_s+1)-(1-z)L_s-Mx^{[3]}_2}{7},\\
 x^{[3]}_4&=\frac{K-\sum_{h=0}^{3}x^{[3]}_hv^{[3]}_h}{7}.
 \end{aligned}
\tag{24.4}
$$

这是 22.4 中晚切口伴随的五维形式；八报告预算只使用其 $b_0,b_1,b_2,b_3$ 四个坐标，与 23.2 的部分伴随接口相同。由 $22/25\le\rho_s\le89/100$、$0<D_s<3$、$0<L_s<M<20$ 及 $c_s+1<81$，并有 $z<0.9$、$x^{[3]}_2<1/400$，所以

$$
z(c_s+1)+(1-z)L_s+Mx^{[3]}_2<82<100.
$$

故 $0<x^{[3]}_3<100/7$；各 $v^{[3]}_j$ 也严格正，且 $x^{[3]}_2<1/400$，从而 $\sum_{h=0}^3x^{[3]}_hv^{[3]}_h<1400<K$，所以 $x^{[3]}_4>0$。直接代入给出

$$
 (A_0,A_1,A_2,A_3)=\left(K,100,17,\tau_s+1+\frac{u-\tau_s}{2}\right),
\tag{24.5}
$$

所以与 $p_0,p_1,p_2,p_3$ 的差分别为 $0,0,1,1-(u-\tau_s)/2$，均在 $[-1,1]$ 内；并且

$$
 v^{[3]}-b^{(3)}(Q_s)=(0,0,-2,-2,-2).
\tag{24.6}
$$

八报告预算在 $q=3$ 首次 $L_0$ 后至多取得 $b_0,b_1,b_2,b_3$，故 (24.6) 已覆盖全部实际可见的新坐标。

当 $q=4$，八报告预算在首次 $L_0$ 后至多取得 $b_0,b_1,b_2$。取

$$
 \begin{aligned}
 v^{[4]}&=(1000,c_s,3-s,u-\tfrac32,2),\\
 x^{[4]}_0&=1,&x^{[4]}_1&=\frac34,\\
 x^{[4]}_2&=\frac{16-(3-s)-\frac34(u-\frac32)}{2},\\
 x^{[4]}_3&=\frac{100-c_s-\frac34(3-s)-x^{[4]}_2(u-\frac32)}{2},\\
 x^{[4]}_4&=\frac{K-v^{[4]}_0-x^{[4]}_1v^{[4]}_1-x^{[4]}_2v^{[4]}_2-x^{[4]}_3v^{[4]}_3}{2}.
 \end{aligned}
\tag{24.7}
$$

Here $v^{[4]}_3=(4s+249)/16$, $x^{[4]}_2=(52s+85)/128\in(0,1)$, and $70<c_s<80$ gives $0<x^{[4]}_3<6$ by the defining numerator bounds. Since $c_s<80$, $v^{[4]}_2\le3$, and $v^{[4]}_3<16$, we have

$$
 v^{[4]}_0+x^{[4]}_1v^{[4]}_1+x^{[4]}_2v^{[4]}_2+x^{[4]}_3v^{[4]}_3<1000+60+3+96<2000<K,
$$

so $x^{[4]}_4>4000$. The equations in (24.7) give

$$
 (A_0,A_1,A_2,A_3,A_4)=(K,100,16,u,2),
\tag{24.8}
$$

and $v^{[4]}_0,v^{[4]}_1,v^{[4]}_2$ equal the first three coordinates of $b^{(4)}(Q_s)$; the shared old terminal report is $p_4=2=A_4$. Thus this companion matches every new coordinate visible within the eight-report budget. It is valid also at $s=0$ and $s=1/2$; no overlap parameter or strict inequality between two members is used.

For any selected cut $q$, after the first $L_0$ choose each newly reported coordinate to be the midpoint of the corresponding true value for $Q_s$ and for $S_q$. The old prefix is already within one of both sources, and the displayed $b$ differences are at most two, so each midpoint is within one of both. The number of distinct nonzero coordinates that can be reached with at most eight reports is

$$
\begin{array}{c|ccccc}
q&0&1&2&3&4\\ \hline
\text{largest visible }b_j&4&4&4&3&2 .
\end{array}
\tag{24.9}
$$

This is the budget identity $1+q+1+j\le8$; for $q=4$ the old $a_4$ report is shared and the two subsequent $N$ steps expose $b_1,b_2$ after the initial $b_0$. Repeated $L_0$ only repeats $b_0$, and after $j=4$ every further $N$ enters the permanent zero state; hence the same fixed $S_q$ and the same report table cover every repeated-reset and zero-tail continuation allowed before report eight. Determinism now forces $\Pi$ to make identical actions, stopping decisions and output on $Q_s$ and on $S_q$. If it outputs $2$ within eight reports on the former, it does so on the rank-one latter, contradicting full-domain reliability. Therefore $c_{5,1}(Q_s)\ge9$.

Finally let $\varepsilon>0$. The map $R\mapsto\varepsilon R$ is a bijection of $\mathcal M_5$ preserving strict positivity and ordinary rank, and $\operatorname{tr}(A\varepsilon R)=\varepsilon\operatorname{tr}(AR)$. If an $\varepsilon$-reliable protocol achieved $Q_{\varepsilon,s}$ in at most eight reports, construct a unit protocol by multiplying each unit-scale report by $\varepsilon$ before feeding it to the original decision function. This would be a unit-reliable protocol achieving $Q_s$ in at most eight reports, contradicting the preceding paragraph. The scaled version of the nine-report protocol gives the matching upper bound, proving (24.2). ∎

### 约定 24.3（费用边界）

定理 24.2 只计算固定五维族 $Q_{\varepsilon,s}$ 的逐来源费用。它不推出其余 $\mathcal M_5$ 来源的统一最优费用，不把维数递归推广到 $k\ge6$，也不改变第 22.6 节的条件性递归。严格正性、$\varepsilon>0$、任意相关闭误差、单轨迹、共享末坐标、重复 $L_0$ 与永久零尾均保留；预选覆盖、来源分解恢复、未知来源在线选择、随机协议、有效实数判定和位复杂度均不在结论内。

## 追加锚（本行以下为增补区）
