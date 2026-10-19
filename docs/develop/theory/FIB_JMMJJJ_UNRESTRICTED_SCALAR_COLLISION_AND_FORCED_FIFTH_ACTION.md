# FIB JMMJJJ 不受限 R 恒等式与同漂移异 k 碰撞必要轨迹

本卷研究同一字面 $JMMJJJ$ 实际历史上的完整不受限纤维。相对于下列既有结果，额外推导是第 5 节的无根承诺末端标量 $R$ 恒等式，以及第 6 节对已经实现的同漂移、异 $k$ 的 $R$ 碰撞给出的必要联合条件。后者不是碰撞存在或充分性的判据，也没有完成联合 $R,S$ 碰撞分类。

第 3、4 节的显式二世界、互补第四 $J$ 历史上的第五 $J$ 失败和条件第五 $M$ 必要性，是 [V](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md) 定理 10.1、11.1、12.1 及命题 11.3 的实例与应用。保留它们的完整逐项证明和表格，以说明不受限实际纤维怎样包含固定失败对子集；不把这些既有结论计作新增内容。V 定理 12.2、12.3 的任意基数同父粘合接口也按完整条件列出；V 第 13–15 节的有理收缩盒定理、同一 $JMMJMM$ 实际历史上的精确三目标与五目标父失败族，作为既有结果完整复用。该族在一个精确 $y_*$ 上提供粘合所需的实际第五 $M$ 失败族，不是本卷另行构造的见证，也不属于本卷 $JMMJJJ$ 的 $\mathcal U_{x,w}$。原根全域八读恢复与 $n_{\mathrm{det}}(3,0)\ge9$ 的二择仍未解决。

## 1. 完整目标、原时钟与失败递归

**定义 1.1（完整采集域）。** 令

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
$$

$\mathcal W_3$ 是全部三元组 $W=(P,g,\delta)$ 的集合，其中 $P$ 是严格逐项正的实 $2\times2$ 矩阵，秩一且迹一；$g\in\mathbb R[T]\setminus\{0\}$，$\deg g\le3$；$\delta\in\mathbb R$。完整恢复要求给出整个 $(P,g,\delta)$，包括增益的全部系数和漂移。源不要求对称，增益不要求恰为三次，也不要求任何系数符号、采样非零性、单根性或共同漂移。

对按时间排列的动作 $E_1\cdots E_i$，规定

$$
A_0=I,\qquad A_i=E_iA_{i-1},\quad E_i\in\{M,J\},\qquad
z_i(W)=g(i)\operatorname{tr}(A_iP)+\delta.                 \tag{1.1}
$$

这里是按时间左乘。初读计入总读数；每个动作恰为一个 $M$ 或 $J$，随后立即读数。只有一条不可重置、不可复制的实际轨迹。不允许跳读、空动作读数、未读的复合动作、重编号时钟或增加端口。八次总读数使用原时钟 $0,\ldots,7$。确定性协议可依据整个实际历史选择动作、提前停止和完整答案，不对这些函数加连续性、可测性或可计算性假设。

**定义 1.2（整个实际纤维与停止）。** $\mathcal F(H)$ 保留字面历史 $H$ 的全部动作及读数。对 $K\subseteq\mathcal F(H)$，定义

$$
\begin{aligned}
L_0(K,H)&\Longleftrightarrow |K|\ge2,\\
L_{s+1}(K,H)&\Longleftrightarrow |K|\ge2\ \land\
\bigwedge_{E\in\{M,J\}}\exists z\in\mathbb R:\
 L_s\bigl(K\cap\mathcal F(H,E,z),(H,E,z)\bigr).
\end{aligned}                                                   \tag{1.2}
$$

$s$ 不超过剩余原时钟数。这个递归表达在至多 $s$ 次后续读数内无法恢复整个已知候选集，包括所有提前停止。若 $|K|\ge2$，同一历史上的单个答案不能恢复其中两个不同完整目标；若某动作的一个实际响应子纤维仍然失败，选择该动作就不能保证成功。反过来，在非单点且非失败的节点，至少有一个动作的每个实际响应子纤维均可在剩余预算恢复；对这些子纤维分别选定策略即可。对有限时限归纳，得到该递归与确定性恢复的对应。

还将使用向上单调性：若 $K\subseteq K'\subseteq\mathcal F(H)$ 且 $L_s(K,H)$，则 $L_s(K',H)$。在 $s=0$ 时由基数成立；归纳时，对每个动作沿用 $K$ 的响应见证，其实际子集包含于 $K'$ 的同响应子集，再用归纳假设。这里不要求整个纤维有限。未选动作的响应仅是固定世界的数学函数，并非同时采集的数据。

**定义 1.3（任意偏置及两种尺度符号）。** 固定任意 $D_0\in\mathbb R$ 和 $\lambda\in\mathbb R\setminus\{0\}$，置

$$
f=g/\lambda,\qquad d=(\delta-D_0)/\lambda,\qquad
\widehat z_i=(z_i-D_0)/\lambda.
                                                               \tag{1.3}
$$

于是 $\widehat z_i=f(i)\operatorname{tr}(A_iP)+d$，逆映射为 $(P,f,d)\mapsto(P,\lambda f,D_0+\lambda d)$。这对两种非零尺度符号都为双射，保留所有响应相等关系、完整目标差异、实际子纤维与 $L_s$。$D_0$ 是历史偏置，不是对整个纤维的真实漂移承诺。

## 2. 字面 JMMJ 父历史及不受限的 J、J 子纤维

**定义 2.1（同一祖先与原时钟延续）。** 对任意 $Y\in\mathbb R$，令

$$
\begin{aligned}
H_p(Y)&=(D_0,J,D_0+24\lambda,M,D_0+48\lambda,
 M,D_0+312\lambda/5,J,Y),\\
y&=(Y-D_0)/\lambda,\\
H_x&=(H_p(Y),J,D_0+\lambda x),\\
H_{x,w}&=(H_x,J,D_0+\lambda w),\qquad
\mathcal U_{x,w}=\mathcal F(H_{x,w}).
\end{aligned}                                                   \tag{2.1}
$$

$\mathcal U_{x,w}$ 始终取遍整个 $\mathcal W_3$。令

$$
L=MJ=\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
B=J+L=\begin{pmatrix}1&1\\2&1\end{pmatrix},\quad
C=JB=\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad
Q=MC=\begin{pmatrix}1&1\\3&2\end{pmatrix}.                    \tag{2.2}
$$

有 $ML=B$、$JC=B$。因此 $H_{x,w}$ 的原时钟 $0,\ldots,6$ 的累计矩阵为

$$
(I,J,L,B,C,B,C),                                             \tag{2.3}
$$

且它的全部祖先方程恰为

$$
f(i)\operatorname{tr}(A_iP)+d
 =(0,24,48,312/5,y,x,w)_i\qquad(0\le i\le6).                 \tag{2.4}
$$

定义没有附加 $d=0$、$f(6)=0$、$f(7)=0$、共同增益射线、源标签或基数上界。所有其他相容世界均保留。

**定义 2.2（完整正源坐标与两个标量动作）。** 写

$$
\begin{gathered}
P=\begin{pmatrix}r&u\\v&1-r\end{pmatrix},\qquad
\ell=1+u>1,\qquad k=(u+v)/\ell>0,\\
u=\ell-1,\quad v=(k-1)\ell+1>0,\quad 0<r<1,\quad
(\ell-1)((k-1)\ell+1)=r(1-r).
\end{gathered}                                                   \tag{2.5}
$$

这些条件与正源、秩一、迹一等价：正性给出各严格不等式，行列式零给出末式；逆向代入即可恢复全部四个正条目、迹与秩。有关的正迹为

$$
\begin{array}{c|cccccc}
A&I&J&L&B&C&Q\\ \hline
\operatorname{tr}(AP)&1&k\ell&\ell&(k+1)\ell&1+r+k\ell&(k+2)\ell-r.
\end{array}                                                     \tag{2.6}
$$

它们也可从对应非负累计矩阵与严格正的 $P$ 直接看出严格为正。特别地，实际第五、六读数满足

$$
x=d+f(5)(k+1)\ell,\qquad w=d+f(6)(1+r+k\ell).              \tag{2.7}
$$

在已读的第六 $J$ 状态 $C$，最后第七 $J$ 或 $M$ 的归一化标量预测分别为

$$
R(W)=d+f(7)(k+1)\ell,\qquad
S(W)=d+f(7)((k+2)\ell-r).                                  \tag{2.8}
$$

它们定义在同一个整个 $\mathcal U_{x,w}$ 上。一次合法末读只能取得所选的一个标量。

若在同一第四状态 $C$ 后第五选 $M$，归一化第五响应是

$$
m_5=d+f(5)((k+2)\ell-r).
$$

因此 $m_5=0$ 只给出 $f(5)((k+2)\ell-r)=-d$。该迹严格为正，但只有独立知道 $d=0$ 时，零响应才强制 $f(5)=0$；零响应本身不能给出漂移或第五根。物理读数等于 $D_0$ 与归一化响应为零等价，仍不把历史偏置 $D_0$ 认证为整个实际纤维的真实漂移。

## 3. 同一不受限实际子纤维上的精确双标量碰撞

**定义 3.1（规范窗口中的两个既有固定世界）。** 置

$$
h(T)=T(T-5)(T-7),\qquad
R_a=\frac1{55}\begin{pmatrix}12&19\\36&57\end{pmatrix},\qquad
R_b=\frac1{55}\begin{pmatrix}28&35\\20&25\end{pmatrix},       \tag{3.1}
$$

并定义完整目标

$$
\begin{aligned}
W_a&=\left(\frac1{69}\begin{pmatrix}12&19\\36&57\end{pmatrix},
                \frac{69\lambda}{55}h,D_0\right),\\
W_b&=\left(\frac1{53}\begin{pmatrix}28&35\\20&25\end{pmatrix},
                \frac{53\lambda}{55}h,D_0\right).
\end{aligned}                                                   \tag{3.2}
$$

$R_a,R_b$ 是 [IV](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_IV.md) 定理 2.1 的 $R_1,R_3$，也是 V 命题 5.3、11.3 已在互补第四 $J$ 历史上使用的同一对；未归一化多项式为 $\lambda h$。在 V 定理 10.1、11.1 的参数中，它们对应

$$
y=1632/55,\qquad t=81/88,\qquad
\ell_a=88/69,\quad \ell_b=88/53.
$$

这里保留这些既有世界在该同一互补历史上的精确证明，不将它们的互补臂响应另计为新构造。

**引理 3.2（合法性、区别及单一世界恒等式）。** 两个目标均属于 $\mathcal W_3$ 且不同。对任意原时钟、任意动作字及 $j\in\{a,b\}$，恒有

$$
g_j(i)\operatorname{tr}(A_iP_j)+D_0
 =D_0+\lambda h(i)\operatorname{tr}(A_iR_j).                \tag{3.3}
$$

证明。源条目全部严格为正，且

$$
12\cdot57=19\cdot36=684,\qquad
28\cdot25=35\cdot20=700.
$$

两个非零源矩阵因而秩一；分子的迹为 $69,53$，故所示归一化源迹一。$\operatorname{tr}R_a=69/55$、$\operatorname{tr}R_b=53/55$。$\lambda\ne0$ 使两个增益都是非零三次多项式，漂移均为固定的 $D_0$。源比值 $(P_a)_{21}/(P_a)_{11}=3$、$(P_b)_{21}/(P_b)_{11}=5/7$ 不同，故完整目标不同。代入 $P_j=R_j/\operatorname{tr}R_j$、$g_j=\lambda(\operatorname{tr}R_j)h$ 即得 (3.3)。此式对所有时钟成立，源、增益和漂移不随节点更换。∎

**定理 3.3（既有窗口实例：整个实际 $\mathcal U_{0,-816/55}$ 的两个标量均非单射）。** 对每个 $D_0$ 和每个非零 $\lambda$，固定

$$
Y_\dagger=D_0+\frac{1632}{55}\lambda,\qquad
H_p=H_p(Y_\dagger),\qquad
H_x=(H_p,J,D_0),\qquad
H=(H_x,J,D_0-816\lambda/55).                                \tag{3.4}
$$

则 $W_a,W_b\in\mathcal U_{0,-816/55}=\mathcal F(H)$，且

$$
R(W_a)=R(W_b)=0,\qquad S(W_a)=S(W_b)=0,\qquad
L_1(\mathcal U_{0,-816/55},H).                              \tag{3.5}
$$

证明。$h$ 在原时钟 $0,\ldots,7$ 的值为

$$
(0,24,30,24,12,0,-6,0).                                    \tag{3.6}
$$

完整实际祖先及两个第七替代动作的精确表为

| 原时钟 | 本次动作 | 累计矩阵 | $h(i)$ | $\operatorname{tr}(A_iR_a)$ | $\operatorname{tr}(A_iR_b)$ | 两世界共同的归一化读数 |
| --- | --- | --- | --- | --- | --- | --- |
| $0$ | 初读 | $I$ | $0$ | $69/55$ | $53/55$ | $0$ |
| $1$ | $J$ | $J$ | $24$ | $1$ | $1$ | $24$ |
| $2$ | $M$ | $L$ | $30$ | $8/5$ | $8/5$ | $48$ |
| $3$ | $M$ | $B$ | $24$ | $13/5$ | $13/5$ | $312/5$ |
| $4$ | $J$ | $C$ | $12$ | $136/55$ | $136/55$ | $1632/55$ |
| $5$ | $J$ | $B$ | $0$ | $13/5$ | $13/5$ | $0$ |
| $6$ | $J$ | $C$ | $-6$ | $136/55$ | $136/55$ | $-816/55$ |
| $7$ 替代 | $J$ | $B$ | $0$ | $13/5$ | $13/5$ | $0$ |
| $7$ 替代 | $M$ | $Q$ | $0$ | $219/55$ | $203/55$ | $0$ |

为逐项核对该表，对 $N=\left(\begin{smallmatrix}a&b\\c&e\end{smallmatrix}\right)$ 有

$$
\begin{aligned}
\operatorname{tr}(JN)&=b+c,&\operatorname{tr}(LN)&=a+b+e,\\
\operatorname{tr}(BN)&=a+2b+c+e,&\operatorname{tr}(CN)&=2a+b+c+e,\\
\operatorname{tr}(QN)&=a+3b+c+2e.
\end{aligned}                                                   \tag{3.7}
$$

将 (3.1) 的两个整数分子代入并除以 $55$，得到全部迹条目；再与 (3.6) 相乘，由 (3.3) 得到全部读数。$JC=B$、$JB=C$ 保证表中重复状态的原时钟顺序。实际读数始终是 $D_0$ 加上 $\lambda$ 倍表中读数。

表的 $0,\ldots,6$ 行验证两世界同时满足 (2.4) 的每一个方程，其中 $(y,x,w)=(1632/55,0,-816/55)$。整个纤维并未被替换为两世界集合。两世界的坐标及相关样本为

| 世界 | $r$ | $u$ | $v$ | $\ell$ | $k$ | $d$ | $f(6)$ | $f(7)$ | $\operatorname{tr}(BP)$ | $\operatorname{tr}(CP)$ | $\operatorname{tr}(QP)$ |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| $W_a$ | $12/69$ | $19/69$ | $36/69$ | $88/69$ | $5/8$ | $0$ | $-414/55$ | $0$ | $143/69$ | $136/69$ | $219/69$ |
| $W_b$ | $28/53$ | $35/53$ | $20/53$ | $88/53$ | $5/8$ | $0$ | $-318/55$ | $0$ | $143/53$ | $136/53$ | $203/53$ |

因此 (2.8) 的两个标量均在同一不同目标对上取值零。VII 定义 14.2 的两对见证可取 $W_1=W_3=W_a$、$W_2=W_4=W_b$，无需四个不同世界。

令 $K=\{W_a,W_b\}$。它在 $H$ 上有 $L_0$，所以不能提前停止。对每个最后动作 $E\in\{J,M\}$，实际响应 $D_0$ 都保留同一对：

$$
K\cap\mathcal F(H,E,D_0)=K.
$$

由 (1.2) 得 $L_1(K,H)$，再由向上单调性得 (3.5)。确定性协议在两世界上看见相同历史，选择同一最后动作、得到同一最后读数，不能返回两个不同的正确答案。这里执行的始终只有一个最后动作。∎

**推论 3.4（实际第六读数没有给出真实漂移）。** 两个见证都有 $f(6)\ne0$，归一化实际第六响应 $w=-816/55$ 与它们的 $d=0$ 不同；实际读数 $D_0-816\lambda/55$ 与真实漂移 $D_0$ 不同。

证明。由表中非零的第六增益和严格正的 $C$ 迹，将 (2.7) 代入即得；$\lambda\ne0$ 保证物理单位下也不同。根 $0,5,7$ 和共同漂移只属于所展示见证，不是整个实际纤维的条件。∎

## 4. 规范窗口、实际强制动作与同父粘合的复用

**定理 4.1（既有结果的显式实例：同一字面父节点的整个第五 J 子纤维有 $L_2$）。** 对 (3.4) 的 $H_p$ 和 $H_x$，有

$$
L_2(\{W_a,W_b\},H_x),\qquad L_2(\mathcal F(H_x),H_x).
                                                               \tag{4.1}
$$

任何在整个 $\mathcal W_3$ 上正确、总读数至多八次且到达这个字面 $H_p$ 的协议，必须选第五 $M$。这是 V 定理 10.1、11.1、12.1 与命题 11.3 在上述参数处的应用；以下保留完整显式证明。

证明。在 $H_p$ 的第四状态 $C$ 后，第五 $J$ 给出 $B$，第五 $M$ 给出 $Q$。虽然这两个第五状态的迹可能不同，$h(5)=0$ 使两个世界在两种第五动作下都实际读到 $D_0$。从这个父节点出发，全部第五、第六组合的表为

| 按时间的第五、第六动作 | 第六累计矩阵 | $\operatorname{tr}(A_6R_a)$ | $\operatorname{tr}(A_6R_b)$ | $W_a$ 的归一化第六响应 | $W_b$ 的归一化第六响应 |
| --- | --- | --- | --- | --- | --- |
| $JJ$ | $JB=C=\left(\begin{smallmatrix}2&1\\1&1\end{smallmatrix}\right)$ | $136/55$ | $136/55$ | $-816/55$ | $-816/55$ |
| $JM$ | $MB=J+2L=\left(\begin{smallmatrix}2&1\\3&2\end{smallmatrix}\right)$ | $21/5$ | $21/5$ | $-126/5$ | $-126/5$ |
| $MJ$ | $JQ=\left(\begin{smallmatrix}3&2\\1&1\end{smallmatrix}\right)$ | $184/55$ | $184/55$ | $-1104/55$ | $-1104/55$ |
| $MM$ | $MQ=\left(\begin{smallmatrix}3&2\\4&3\end{smallmatrix}\right)$ | $355/55$ | $339/55$ | $-2130/55$ | $-2034/55$ |

这些矩阵来自分别左乘单个原子。对一般 $A$，

$$
\operatorname{tr}(AN)=A_{11}a+A_{12}c+A_{21}b+A_{22}e,        \tag{4.2}
$$

故代入两个固定分子即可得到全部迹；每个第六响应由乘 $h(6)=-6$ 得出。特别地，$JJ$ 行的完整时序是时钟四的 $C$、时钟五的 $B$、时钟六的 $C$。

在实际第五 $J$ 子节点，两种第六动作之后的全部最后动作也可逐项列出：

| 第六动作 | 最后动作 | 第七累计矩阵 | $\operatorname{tr}(A_7R_a)$ | $\operatorname{tr}(A_7R_b)$ | 两世界共同归一化末读 |
| --- | --- | --- | --- | --- | --- |
| $J$ | $J$ | $B$ | $13/5$ | $13/5$ | $0$ |
| $J$ | $M$ | $Q$ | $219/55$ | $203/55$ | $0$ |
| $M$ | $J$ | $J(MB)=2C-I=\left(\begin{smallmatrix}3&2\\2&1\end{smallmatrix}\right)$ | $203/55$ | $219/55$ | $0$ |
| $M$ | $M$ | $M(MB)=2J+3L=\left(\begin{smallmatrix}3&2\\5&3\end{smallmatrix}\right)$ | $34/5$ | $34/5$ | $0$ |

该表同样由 (4.2) 得出；所有末读为零是因为 $h(7)=0$，无需末端迹相等。

令 $K=\{W_a,W_b\}$。在 $H_x$，第六 $J$ 的响应 $D_0-816\lambda/55$ 保留 $K$，第六 $M$ 的响应 $D_0-126\lambda/5$ 也保留 $K$。每个这样的实际第六子节点，无论最后选 $M$ 还是 $J$，都在实际响应 $D_0$ 保留 $K$，因此都有 $L_1$。$H_x$ 本身保留不同目标对，排除停止，于是 (1.2) 给出 $L_2(K,H_x)$。向上单调性给出整个实际第五 $J$ 纤维的结论，新增相容世界不能消去失败子集。

在 $H_p$ 已有五次总读数，停止也失败于同一对。第五 $J$ 将实际到达有 $L_2$ 的 $H_x$，而只剩原时钟六、七。因此到达此历史且要求全域正确的八读协议必须取第五 $M$。这是一条以到达该字面历史为前提的必要性，不断言每个协议都到达它，也不断言每个 $Y$ 都有该必要性。∎

**命题 4.2（既有配对的边界：同一对不能证明父节点的 $L_3$）。** $K=\{W_a,W_b\}$ 在 $H_p$ 没有 $L_3$；上述结论没有判定整个 $\mathcal F(H_p)$ 是否有 $L_3$。

证明。取第五 $M$ 并读到共同的 $D_0$，再取第六 $M$。上表的 $MM$ 行给出两个不同实际读数，其差为

$$
\left(D_0-\frac{2130}{55}\lambda\right)
-\left(D_0-\frac{2034}{55}\lambda\right)
=-\frac{96}{55}\lambda\ne0.                                \tag{4.3}
$$

故这个已知对在原时钟六、七次总读数时已经恢复，允许立即停止。这个分离也是 V 命题 11.3 对同一配对的结论。整个第五 $M$ 纤维可能含其他世界，不能由该对的分离得到其完整逆。VII 定理 4.1 已排除任意实际第五 $M$ 纤维内的二目标 $L_2$，所以若整个父纤维有 $L_3$，第五 $M$ 臂仍须在某个实际响应处保留至少三个完整目标的 $L_2$ 子集。对本命题固定的 $y=1632/55$，这里没有构造或排除这样的子集，也没有给整个第五 $M$ 纤维加上基数限制。V 定理 15.1 在另一个精确 $y_*$ 上给出了这样的实际失败族及父层 $L_3$；第 4.7 小节复用该结果，不能把它移到本命题的不同第四读数。∎

**既有结果 4.3（V 的全部第五 J 二目标刻画与精确窗口）。** 记定义 1.3 的逆归一化为

$$
\Phi_{D_0,\lambda}(P,f,d)=(P,\lambda f,D_0+\lambda d).
$$

对任意 $y=(Y-D_0)/\lambda$，令

$$
\begin{gathered}
t=\frac5{96}(y-12),\qquad
Q_t(\ell)=\left(t^2-\frac38\right)\ell^2+
                 \left(\frac{11}8-3t\right)\ell+1,\\
\mathcal R_t=\{\ell:Q_t(\ell)=0,\ 1<\ell<8/3,\ 0<t\ell-1<1\},\\
P_\ell=\begin{pmatrix}
t\ell-1&\ell-1\\1-3\ell/8&2-t\ell
\end{pmatrix},\qquad
\widetilde W_\ell=\left(P_\ell,\frac8{5\ell}h,0\right).
\end{gathered}                                                    \tag{4.4}
$$

这里 $Q_t$ 是一元多项式，不是 (2.2) 的累计矩阵 $Q$。对同一实际第五 $J$ 子纤维中的两个不同世界，有

$$
\begin{aligned}
&W_1,W_2\in\mathcal F((H_p(Y),J,D_0+\lambda\xi)),\\
&L_2(\{W_1,W_2\},(H_p(Y),J,D_0+\lambda\xi))\\
&\quad\Longleftrightarrow\quad
\xi=0\ \text{且存在不同的 }\ell_1,\ell_2\in\mathcal R_t:
 W_i=\Phi_{D_0,\lambda}(\widetilde W_{\ell_i}).
\end{aligned}                                                    \tag{4.5}
$$

存在这样的配对恰好等价于

$$
\begin{gathered}
t\in(3/4,31/40)\ \cup\ (7/8,1),\\
y\in\mathcal I:=(132/5,672/25)\ \cup\ (144/5,156/5).
\end{gathered}                                                    \tag{4.6}
$$

四个排除端点的全部根与障碍为

| $t$ | $Q_t$ 的根 | 不能构成不同合法配对的原因 |
| --- | --- | --- |
| $3/4$ | $2,8/3$ | $\ell=8/3$ 具有零源条目 |
| $31/40$ | $40/19$，重根 | 只有一个完整目标 |
| $7/8$ | $8/5$，重根 | 只有一个完整目标 |
| $1$ | $1,8/5$ | $\ell=1$ 具有零源条目 |

证明。对实际历史和两个完整目标应用定义 1.3 的双射。其归一化父节点正是 V 定义 9.1 的 $H_p(y)$，第五响应正是 $\xi$；本卷 $L,B,C$ 分别对应 V 的 $L_0,Q,C_0$。V 定理 10.1 给出 (4.5) 的双向刻画，包含其零增益样本、次数下降和非基线漂移排除；漂移为零与增益射线是该二目标 $L_2$ 的结论，并非在原实际子纤维上预加的承诺。V 定理 11.1 给出 (4.6) 及端点表。

具体而言，(4.4) 的源迹恒为一，行列式为 $-Q_t(\ell)$，其严格正性恰由 $1<\ell<8/3$ 和 $0<t\ell-1<1$ 给出。$Q_t$ 的常数项为一，故不恒零；若首项系数为零则至多一个根。其判别式为

$$
\Delta_t=5(t-31/40)(t-7/8).
$$

在 (4.6) 的两个开区间内恰有两个满足严格源条件的不同根；端点的重根或零条目均不允许以极限代替不同严格正源。仿射关系 $y=12+96t/5$ 给出响应窗口。对任意符号的 $\lambda$，归一化和反归一化均保持每个实际响应子纤维、区别、两个动作及 $L_2$，所以物理参数下得到相同等价，而不需对物理 $Y$ 端点作符号假设。$t=81/88$ 时 V 命题 11.3 指定的两根为 $88/69,88/53$，(4.4) 及其反归一化恰给出 (3.2)。∎

当 $y\in\mathcal I$ 时，以下始终使用同一个绑定的二目标族

$$
\mathcal A_y=\{\Phi_{D_0,\lambda}(\widetilde W_\ell):
                         \ell\in\mathcal R_t\}.
                                                               \tag{4.7}
$$

它恰有两个元素，全部位于同一个完整字面父纤维 $\mathcal F(H_p(Y))$。更换动作或取响应子纤维时不重新选择这个族。(4.5) 仅刻画同一对在整个第五 $J$ 节点的 $L_2$；只要求在某一个已指定第六动作后末端碰撞的配对，或更大失败族，不由它分类。

**既有结果 4.4（V 的同一族全部实际分支与强制动作）。** 对固定 $y\in\mathcal I$，(4.7) 的每个世界在时钟 $5,6,7$ 的归一化预测为

| 第五动作 | 第六动作 | 第五响应 | 第六响应 | 任一最后原子的第七响应 |
| --- | --- | --- | --- | --- |
| $J$ | $J$ | $0$ | $-y/2$ | $0$ |
| $J$ | $M$ | $0$ | $-126/5$ | $0$ |
| $M$ | $J$ | $0$ | $48/5-y$ | $0$ |
| $M$ | $M$ | $0$ | $-156/5-48/(5\ell)$ | $0$ |

实际物理响应是 $D_0$ 加上 $\lambda$ 倍相应表项。因此

$$
\begin{gathered}
L_2(\mathcal A_y,(H_p(Y),J,D_0)),\\
L_1(\mathcal A_y,(H_p(Y),M,D_0,J,D_0+\lambda(48/5-y))),\\
\neg L_2(\mathcal A_y,(H_p(Y),M,D_0)),\qquad
\neg L_3(\mathcal A_y,H_p(Y)).
\end{gathered}                                                    \tag{4.8}
$$

任何要求在整个父纤维 $\mathcal F(H_p(Y))$ 上以至多八次总读数成功的确定性解码器，必须选第五 $M$；在其实际第五响应 $D_0$ 后必须选第六 $M$。同一第六动作必要性适用于已处在整个实际 $\mathcal F((H_p(Y),M,D_0))$ 上、仅余两读且要求完整恢复的解码器。此结论没有断言这样的全纤维解码器存在。

证明。这是 V 命题 11.3、定理 12.1 的相同参数应用，也可直接核对。归一化增益为 $8h/(5\ell)$，故第五、第七样本为零，第六样本为 $-48/(5\ell)\ne0$。两种第五动作之后的四个第六迹依次为

$$
\begin{array}{c|c}
JJ&(t+5/8)\ell\\
JM&21\ell/8\\
MJ&(2t+1/4)\ell\\
MM&1+13\ell/4.
\end{array}
$$

将第六增益乘这些迹，并用 $y=12+96t/5$，得到全部表项。第七增益为零使任一最后原子的读数都等于漂移；这一步只在已经按 (4.7) 固定的两个世界上使用，不扩成对整个实际纤维的根承诺。

第五 $J$ 后两种第六动作都保留同一对，且每个最后动作仍保留它，所以由 (1.2) 得第一个 $L_2$。第五 $M$、第六 $J$ 也保留同一对，所以该实际子节点有 $L_1$。第五 $M$、第六 $M$ 的响应是 $\ell>0$ 的单射；两个不同根已在时钟六被分开，允许立即停止，得两个否定结论。这个恢复仅针对该对。

父节点和实际第五 $M$ 响应 $D_0$ 子节点都不能在这对上停止。若选择第五 $J$，存在包含该对的实际响应 $D_0$ 子纤维有 $L_2$；向上单调性表明它不能在剩余两读恢复。第五必须选 $M$。在其实际响应 $D_0$ 后，若第六选 $J$，实际响应 $D_0+\lambda(48/5-y)$ 的子纤维包含同一对的 $L_1$，任一末动作或停止都不能恢复。故第六必须选 $M$。每条失败路径使用同一个父历史和同一对固定世界，且每个执行原子都立即读数。∎

**既有结果 4.5（V 的任意基数同父粘合与精细消费者）。** 固定同一个 $y\in\mathcal I$、$Y=D_0+\lambda y$ 及 (4.7) 的 $\mathcal A_y$。记

$$
\begin{gathered}
\mathcal P_Y=\mathcal F(H_p(Y)),\qquad
\mathcal F_Y^E(\zeta)=\mathcal F((H_p(Y),E,\zeta)),\\
H_{M0}=(H_p(Y),M,D_0),\qquad
\beta_Y=D_0+\lambda(48/5-y)=2D_0+48\lambda/5-Y.
\end{gathered}                                                    \tag{4.9}
$$

下标 $M0$ 的零指归一化第五响应；其实际读数是 $D_0$。对任意实 $\zeta$ 和任意基数的

$$
\mathcal B\subseteq\mathcal F_Y^M(\zeta),\qquad
L_2(\mathcal B,(H_p(Y),M,\zeta)),
$$

固定世界族 $\mathcal U=\mathcal A_y\cup\mathcal B$ 满足

$$
L_3(\mathcal U,H_p(Y)).                                      \tag{4.10}
$$

更一般地，对每个 $\mathcal A_y\subseteq K\subseteq\mathcal P_Y$，有完整条件等价

$$
\begin{aligned}
L_3(K,H_p(Y))\quad\Longleftrightarrow\quad
\exists\zeta\in\mathbb R:\ 
L_2(K\cap\mathcal F_Y^M(\zeta),(H_p(Y),M,\zeta)).
\end{aligned}                                                    \tag{4.11}
$$

特别地可取 $K=\mathcal P_Y$。在实际第五响应 $D_0$ 子纤维内，对每个
$\mathcal A_y\subseteq K_0\subseteq\mathcal F_Y^M(D_0)$，又有

$$
\begin{aligned}
L_2(K_0,H_{M0})\quad\Longleftrightarrow\quad
\exists v\in\mathbb R:\
L_1(K_0\cap\mathcal F((H_{M0},M,v)),(H_{M0},M,v)).
\end{aligned}                                                    \tag{4.12}
$$

于是任意实 $v$ 与任意基数的族

$$
\mathcal T\subseteq\mathcal F((H_p(Y),M,D_0,M,v)),\qquad
L_1(\mathcal T,(H_p(Y),M,D_0,M,v))                             \tag{4.13}
$$

给出同一个绑定并集 $\mathcal U_0=\mathcal A_y\cup\mathcal T$，满足

$$
L_2(\mathcal U_0,H_{M0}),\qquad L_3(\mathcal U_0,H_p(Y)).       \tag{4.14}
$$

这些是 V 定理 12.2、12.3 的物理参数版本。$\mathcal B,\mathcal T$ 必须包含于所写的整个同一实际历史纤维，但不要求有限、共同漂移、共同增益射线或另一个第五动作的共同响应；不要求它们包含一个二目标失败子集。$v$ 不必等于 $\beta_Y$。$\mathcal T$ 的 $L_1$ 必须同时覆盖两个最后动作，但各自的碰撞对可以不同、可以没有共同端点。

证明。$\mathcal B$ 的实际子纤维成员资格确保每个世界满足完整的同一个 $H_p(Y)$，而 $\mathcal A_y$ 已由 (4.7) 固定在该父历史上。并集的第五 $J$ 响应 $D_0$ 子纤维包含 $\mathcal A_y$ 的 $L_2$；第五 $M$ 响应 $\zeta$ 子纤维包含 $\mathcal B$ 的 $L_2$。由向上单调性及 (1.2) 的两个动作合取得 (4.10)。两个第五响应值无需相同。

(4.11) 的正向正是 (1.2) 的第五 $M$ 子句。反向中，所假设的第五 $M$ 子句加上第五 $J$ 响应 $D_0$ 处所包含的 $\mathcal A_y$，给出两个子句；$K$ 本身也包含两个不同完整目标，排除停止，因此得 $L_3$。这不从任意失败族中抽取一个共同碰撞对。

在 $H_{M0}$，(4.8) 保证 $\mathcal A_y$ 属于第六 $J$ 响应 $\beta_Y$ 的实际子纤维且有 $L_1$。故包含它的每个 $K_0$ 已有第六 $J$ 子句；第六 $M$ 子句恰为 (4.12) 的右侧。这给出双向等价。

最后，(4.13) 的所有世界与 $\mathcal A_y$ 共享完整 $H_{M0}$。并集的第六 $J$ 响应 $\beta_Y$ 子纤维包含 $\mathcal A_y$，第六 $M$ 响应 $v$ 子纤维包含 $\mathcal T$，各有 $L_1$，所以递归给出 $L_2(\mathcal U_0,H_{M0})$。回到原父节点，第五 $M$ 响应 $D_0$ 子纤维含该 $L_2$，第五 $J$ 响应 $D_0$ 子纤维含 $\mathcal A_y$ 的 $L_2$，再次递归得到 $L_3$。每次包含关系都保留同一实际祖先、同一 $Y$ 和不随分支变化的完整世界；两个最后动作的见证响应可以分别选择。∎

**边界 4.6（规范刻画与实际族存在性的不同量词）。** (4.5) 的共同漂移与根型由完整二目标 $L_2$ 推出，不能仅从一次第五 $M$ 零响应或第五 $J$ 零响应推出。第 2 节的整个不受限实际纤维始终没有插入这些承诺。窗口外没有这样的第五 $J$ 二目标 $L_2$，并不等价于窗口外的整个第五 $J$ 纤维可恢复；更大失败族仍需单独处理。

(4.10)–(4.14) 是条件式，自身不构造满足前提的 $\mathcal B$ 或 $\mathcal T$。V 第 13–15 节已在一个精确 $y_*$ 上共同实现三目标 $\mathcal T$，并与同一个 $\mathcal A_{y_*}$ 粘成五目标父层 $L_3$；其完整定义、收缩盒存在定理及失败递归在第 4.7 小节作为复用列出。这个精确参数处的实际第五 $M$ 失败族及父层失败由该规范定理给出。一般所有 $y,v$ 的分类、其他精确 $y$ 及更早原根子节点仍未由此判定。所有待粘合世界必须在同一 $Y$、同一完整祖先和所写的实际子纤维中共同实现；不同父读数或孤立末端配对不能代替该条件。

### 4.7. V 第 13–15 节的精确联合实现与五目标父失败族（复用）

本小节完整复用 [V](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md) 第 13–15 节的定义、有限有理证书、定理与证明。下列独立编号块保留 V 的原编号：其中的定义 1.1、9.1、定理 10.1–12.3、族 (11.6) 及其余内部编号均指 V。本卷的对应是定义 1.1、(2.1)、(4.4)–(4.14)；归一情形取 $D_0=0,\lambda=1$，V 的 $H_p(y)$ 就是本卷 $H_p(Y)$ 在 $Y=y$ 时的完整字面历史。

在下列复用块中，$A,B$ 是迹标量，V 的末端 $R,S$ 在本卷其他段落记为 $R_V,S_V$。它们分别属于实际字 $JMMJMM$ 的最后 $J,M$，不是 (2.8) 定义在 $JMMJJJ$ 的 $\mathcal U_{x,w}$ 上的 $R,S$。两条路径的原时钟 $0,1,2,3,4$ 累计矩阵相同；时钟 $5,6$ 在这里分别为 $Q,MQ$，在 (2.3) 则分别为 $B,C$。三目标的 $Z_i=0,V_i=v_*$ 不能改名成 (2.7) 的第五、第六 $J$ 方程。

精确存在性依据是 V 定理 14.2 的有理收缩盒定理；中心 $x_0$ 不是精确零点。以下端点比较及其界作为该定理的完整证书数据引用，不另作本卷的独立算术认证。响应相等来自 $F(x_*)=0$，不来自舍入数或相交区间。所有这些内容均为复用及应用，不计作本卷的新见证、独立有限证书核验或一般纤维分类。

#### V 第 13 节：同一 JMMJMM 历史的联合实现方程

**定义 13.1（三个固定目标的有理参数）。** Work in the complete-target domain $\mathcal W_3$ and the original-clock history convention of Definitions 1.1 and 9.1. For $\alpha,\beta>0$ and $d\in\mathbb R$, put

$$
\begin{gathered}
h=1+\alpha\beta,\qquad
P(\alpha,\beta)=\frac1h
\begin{pmatrix}1&\beta\\\alpha&\alpha\beta\end{pmatrix},\\
a=\frac1h,\qquad j=\frac{\alpha+\beta}{h},\qquad
\ell=1+\frac\beta h,\qquad
\tau=(1,j,\ell,j+\ell),\qquad b=(0,24,48,312/5),\\
q_i=\frac{b_i-d}{\tau_i}\quad(0\le i\le3),\qquad
f(T)=\sum_{i=0}^3q_i
\prod_{\substack{0\le m\le3\\m\ne i}}\frac{T-m}{i-m}.
\end{gathered}                                                     \tag{13.1}
$$

There is one polynomial $f$ for this target throughout all continuations. Denote its later samples by

$$
\begin{pmatrix}f_4\\f_5\\f_6\\f_7\end{pmatrix}=
\begin{pmatrix}
-1&4&-6&4\\
-4&15&-20&10\\
-10&36&-45&20\\
-20&70&-84&35
\end{pmatrix}
\begin{pmatrix}q_0\\q_1\\q_2\\q_3\end{pmatrix}.                 \tag{13.2}
$$

Define the trace factors and response functions

$$
\begin{gathered}
A=1+a+j,\qquad B=j+2\ell-a,\\
Y=d+f_4A,\qquad Z=d+f_5B,\qquad V=d+f_6(A+B),\\
R=d+f_7(2A+j),\qquad S=d+f_7(A+2B).
\end{gathered}                                                     \tag{13.3}
$$

For $x=(\alpha_1,\beta_1,d_1,\alpha_2,\beta_2,d_2,
\alpha_3,\beta_3,d_3)$, attach subscript $i$ to these functions evaluated on its $i$th coordinate triple. The jointly constrained map is

$$
F(x)=
\begin{pmatrix}
Z_1\\ Z_2\\ Z_3\\
Y_1-Y_2\\ Y_1-Y_3\\
V_1-V_2\\ V_1-V_3\\
R_1-R_2\\ S_1-S_3
\end{pmatrix}.                                                    \tag{13.4}
$$

In particular, the two terminal equalities concern the pairs $\{1,2\}$ and $\{1,3\}$ within the same three targets. All equations in (13.4), including the ancestor equalities, are simultaneous.

#### V 第 14 节：联合零点的完整有理盒证书

**定义 14.1（中心、矩阵与区间运算）。** Let $\rho=10^{-8}$ and set

$$
x_0=\frac1{10^{15}}
\begin{pmatrix}
648261282725604\\
1661406963929015\\
2963341227084761\\
267996473307519\\
1637499998610191\\
4652954721959948\\
576125340775968\\
10453577045282132\\
15807600936593863
\end{pmatrix},\qquad
X=\{x\in\mathbb R^9:\|x-x_0\|_\infty\le\rho\}.                \tag{14.1}
$$

Use the rational matrix

$$
C=\frac1{10^6}
\begin{pmatrix}
1023801&217453&-1001127&168959&-262908&78207&-721314&-16353&132738\\
391102&-378813&-8273&-294334&-2173&-136240&-5961&28487&1097\\
864656&-1063712&44044&-826493&11566&-382564&31734&79992&-5840\\
147048&-359545&162474&-20132&42668&-386529&117063&165543&-21542\\
-65905&-1886&53887&5189&14152&33283&38826&-18326&-7145\\
718648&4820697&-4559578&63606&-1197400&4024327&-3285186&-1551509&604549\\
24068&-20689&-480&-16075&6305&-7441&-14419&1556&4154\\
-858169&-695624&1582086&-540493&945650&-250181&935725&52312&-180525\\
1329025&2475184&-3103628&1923192&-2606045&890200&-1860321&-186137&311185
\end{pmatrix}.                                                    \tag{14.2}
$$

Every interval endpoint below is rational. For $U=[u_-,u_+]$ and $V=[v_-,v_+]$, the operations are

$$
\begin{aligned}
U+V&=[u_-+v_-,u_++v_+],&
-U&=[-u_+,-u_-],\\
UV&=\bigl[\min_{\epsilon,\eta\in\{-,+\}}u_\epsilon v_\eta,
          \max_{\epsilon,\eta\in\{-,+\}}u_\epsilon v_\eta\bigr],&
V^{-1}&=[1/v_+,1/v_-]\quad(0\notin V),\\
U/V&=UV^{-1},&
\operatorname{mag}(U)&=\max(|u_-|,|u_+|).
\end{aligned}                                                     \tag{14.3}
$$

Real constants are singleton intervals, subtraction is addition of the negative, and squares are products of the interval with itself. Evaluate (13.1)–(13.4) with the displayed parentheses, starting from $[x_{0i}-\rho,x_{0i}+\rho]$. In particular $\ell=1+\beta/h$, rather than an algebraically expanded expression. Linear combinations use the displayed terms; (13.2) uses its four columns in order.

Here is an explicit derivative specification for the interval matrix $[DF](X)$. Gradients are row vectors in coordinate order $(\alpha,\beta,d)$; put $e_d=(0,0,1)$. Use

$$
\begin{gathered}
Da=\frac{(-\beta,-\alpha,0)}{h^2},\qquad
Dj=\frac{(1-\beta^2,1-\alpha^2,0)}{h^2},\qquad
D\ell=\frac{(-\beta^2,1,0)}{h^2},\\
D\tau=(0,Dj,D\ell,Dj+D\ell),\\
Dq_i=-\frac{(b_i-d)D\tau_i}{\tau_i^2}
      -\frac{e_d}{\tau_i}\quad(0\le i\le3),\\
Df_s=\sum_{i=0}^3w_{si}Dq_i\quad(4\le s\le7),
\end{gathered}                                                     \tag{14.4}
$$

where $w_{si}$ are the entries of (13.2). For each response in (13.3), use

$$
D(d+f_sT)=e_d+T Df_s+f_sDT,\qquad
(s,T)=(4,A),(5,B),(6,A+B),(7,2A+j),(7,A+2B),                    \tag{14.5}
$$

with $DA=Da+Dj$ and $DB=Dj+2D\ell-Da$. Assemble the nine rows according to (13.4); a response has zero derivatives in the other two targets' coordinates. The notation $[DF](X)$ means precisely evaluation of (14.4)–(14.5) by (14.3), without algebraic substitution for the displayed gradients. Define

$$
\mathcal D_{ij}=[\delta_{ij},\delta_{ij}]
                  -\sum_{k=1}^9 C_{ik}[DF]_{kj}(X),
\qquad m_i=\sum_{j=1}^9\operatorname{mag}(\mathcal D_{ij}),      \tag{14.6}
$$

where $\delta_{ij}$ is the Kronecker symbol. Thus (13.1)–(14.6) specify the entire finite rational certificate.

**定理 14.2（精确联合零点与投影）。** The map $F$ has exactly one zero $x_*$ in $X$. It is defined without a rounded equality by

$$
x^{(0)}=x_0,\qquad
x^{(n+1)}=x^{(n)}-CF(x^{(n)}),\qquad
x_*=\lim_{n\to\infty}x^{(n)}.                                  \tag{14.7}
$$

All these iterates lie in $X$, and

$$
\|x_*-x_0\|_\infty<\frac{40}{39}\,10^{-14}<2\cdot10^{-14}.
                                                                  \tag{14.8}
$$

For $y_*=Y_1(x_*)$ and $v_*=V_1(x_*)$,

$$
\frac{29286821}{10^6}<y_*<\frac{29286822}{10^6},\qquad
-\frac{45328099}{10^6}<v_*<-\frac{45328097}{10^6}.               \tag{14.9}
$$

Proof. All $\alpha_i,\beta_i$ are strictly positive throughout $X$. Therefore $h_i,j_i,\ell_i,j_i+\ell_i$ and their squared denominators in (14.4) are positive; their interval lower endpoints under (14.3) are positive as well. Product and quotient differentiation of (13.1) gives exactly (14.4), and (14.5) is the product rule for (13.3). Thus $F$ is continuously differentiable on a neighborhood of $X$, and every actual derivative matrix $DF(x)$ is enclosed by $[DF](X)$.

The endpoint operations (14.3) give the following finite comparisons:

$$
\|CF(x_0)\|_\infty<\frac{37711955}{10^{23}}<10^{-14},            \tag{14.10}
$$

and, for each row, $m_i<n_i/10^{12}<c_i/10^6$, with all nine entries specified here:

$$
\begin{array}{c|r|r}
i&n_i&c_i\\ \hline
1&2619848233&2620\\
2&654912347&655\\
3&1903547437&1904\\
4&2007031636&2008\\
5&571807883&572\\
6&19941425792&19942\\
7&151118857&152\\
8&3726043872&3727\\
9&7932801408&7933
\end{array}                                                       \tag{14.11}
$$

These inequalities follow by rational endpoint addition, multiplication, reciprocal and comparison from the integers in (14.1)–(14.2) and formulas (13.1)–(14.6). In particular they concern the whole box $X$. Since $19942/10^6<1/40$, they imply

$$
\sup_{x\in X}\|I-CDF(x)\|_\infty<\frac1{40}.                   \tag{14.12}
$$

Put $G(x)=x-CF(x)$. Integration of its derivative along the segment between two points of the convex box $X$ gives Lipschitz constant $1/40$. Also, for every $x\in X$,

$$
\begin{aligned}
\|G(x)-x_0\|_\infty
&\le\|G(x)-G(x_0)\|_\infty+\|CF(x_0)\|_\infty\\
&<\frac1{40}\,10^{-8}+10^{-14}<10^{-8}.
\end{aligned}                                                     \tag{14.13}
$$

Thus $G$ is a self-map and a contraction of the complete closed box $X$. The Banach contraction principle applies: the iterates (14.7) converge to its unique fixed point. The geometric-series error estimate is

$$
\|x_*-x_0\|_\infty
\le\sum_{n=0}^\infty(1/40)^n\|CF(x_0)\|_\infty
<\frac{40}{39}\,10^{-14}.
$$

At $x_0$, (14.12) makes $CDF(x_0)$ invertible, as is seen from the convergent series for $(I-(I-CDF(x_0)))^{-1}$. Since these are square matrices, $C$ is nonsingular. Hence $CF(x_*)=0$ is equivalent to $F(x_*)=0$. Every zero of $F$ in $X$ is a fixed point of $G$, proving the asserted uniqueness within $X$.

For completeness the projections and terminal separations use the same endpoint rules, on $X'=\{x:\|x-x_0\|_\infty\le2\cdot10^{-14}\}$ or on $X$ as indicated:

$$
\begin{array}{c|c|c}
\text{function}&\text{box}&\text{strict containing interval}\\ \hline
Y_1&X'&(29286821500/10^9,\ 29286821501/10^9)\\
V_1&X'&(-45328098035/10^9,\ -45328098033/10^9)\\
R_1,\ R_2&X&(-22,-21)\\
R_3&X&(-10,-9)\\
S_1,\ S_3&X&(-41,-40)\\
S_2&X&(-42,-41).
\end{array}                                                       \tag{14.14}
$$

Each entry follows by substituting the coordinate endpoints in (13.1)–(13.3) with (14.3); no equality of responses is inferred from these containing intervals. Estimate (14.8) places $x_*$ in $X'$, so the first two rows imply (14.9). The equalities themselves are the exact equations $F(x_*)=0$. ∎

#### V 第 15 节：一个精确父历史的五目标失败族

**定理 15.1（三目标实际子历史与五目标同父障碍）。** Use the exact limit $x_*$ of Theorem 14.2, and let

$$
\begin{gathered}
W_i=(P(\alpha_{i*},\beta_{i*}),f_i,d_{i*})\quad(1\le i\le3),
\qquad \mathcal T=\{W_1,W_2,W_3\},\\
y_*=Y_1(x_*),\qquad v_*=V_1(x_*),\qquad
\mathcal K=\mathcal A_{y_*}\cup\mathcal T,
\end{gathered}                                                     \tag{15.1}
$$

where each $f_i$ is the single polynomial (13.1) at that coordinate triple, and $\mathcal A_{y_*}$ is exactly the already bound family (11.6), with complete targets (10.3). Then $y_*\in(144/5,156/5)$, all five elements of $\mathcal K$ are distinct legal complete targets, and

$$
\begin{gathered}
\mathcal K\subseteq\mathcal F((H_p(y_*),M,0)),\qquad
|\mathcal K|=5,\\
\mathcal T\subseteq\mathcal F((H_p(y_*),M,0,M,v_*)),\qquad
L_1(\mathcal T,(H_p(y_*),M,0,M,v_*)),\\
L_2(\mathcal K,(H_p(y_*),M,0)),\qquad
L_3(\mathcal K,H_p(y_*)).
\end{gathered}                                                     \tag{15.2}
$$

In the displayed $L_1$ child, the final-$J$ collision pair is exactly $\{W_1,W_2\}$, and the final-$M$ collision pair is exactly $\{W_1,W_3\}$. In particular (15.2) obstructs every deterministic policy recovering this known five-target family from the stated parent within the remaining three original-clock readings, including policies with early stopping.

Proof. The source in (13.1) has four strictly positive entries, trace one and determinant zero. Its rank is therefore one, with no symmetry requirement. The exact cumulative matrices along clocks $0,\ldots,6$ for the literal word $JMMJMM$ are

$$
I,\quad J,\quad
\begin{pmatrix}1&0\\1&1\end{pmatrix},\quad
\begin{pmatrix}1&1\\2&1\end{pmatrix},\quad
\begin{pmatrix}2&1\\1&1\end{pmatrix},\quad
\begin{pmatrix}1&1\\3&2\end{pmatrix},\quad
\begin{pmatrix}3&2\\4&3\end{pmatrix}.                           \tag{15.3}
$$

Their traces against $P(\alpha,\beta)$ are respectively

$$
1,\quad j,\quad\ell,\quad j+\ell,\quad A,\quad B,\quad A+B.
                                                                  \tag{15.4}
$$

The two possible final matrices are, in final-$J$ and final-$M$ order,

$$
\begin{pmatrix}4&3\\3&2\end{pmatrix},\qquad
\begin{pmatrix}4&3\\7&5\end{pmatrix},
$$

with trace factors $2A+j$ and $A+2B$. Thus the response functions (13.3) are the actual fourth-$J$, fifth-$M$, sixth-$M$ and two final responses of the same fixed target. There is no change of source or gain between them.

Lagrange interpolation at original clocks $0,1,2,3$ gives (13.2); multiplying $q_i$ by the first four traces in (15.4) and adding the same drift gives exactly the readings $0,24,48,312/5$. Every $f_i$ has degree at most three and is nonzero: if it were zero, these four readings would all be its constant drift. The coordinate box gives

$$
d_{1*}\in(2,3),\qquad d_{2*}\in(4,5),\qquad d_{3*}\in(15,16),
                                                                  \tag{15.5}
$$

so the three complete targets are distinct. The single simultaneous equality $F(x_*)=0$ now gives

$$
\begin{gathered}
Y_1=Y_2=Y_3=y_*,\qquad Z_1=Z_2=Z_3=0,\\
V_1=V_2=V_3=v_*,\qquad R_1=R_2,\qquad S_1=S_3.
\end{gathered}                                                     \tag{15.6}
$$

Consequently all three worlds realize the entire history

$$
(0,J,24,M,48,M,312/5,J,y_*,M,0,M,v_*).
                                                                  \tag{15.7}
$$

The last four rows of (14.14) separate $R_3$ from $R_1=R_2$ and $S_2$ from $S_1=S_3$. For final $J$, the actual response $R_1$ retains exactly the two distinct targets $W_1,W_2$ in $\mathcal T$; for final $M$, response $S_1$ retains exactly $W_1,W_3$. Each child has $L_0$. This proves the $L_1$ assertion by the actual recursion (1.1), with different terminal collision pairs on this same $\mathcal T$.

For the complementary two worlds, (14.9) places $y_*$ in the second window of Theorem 11.1. To specify the roots more narrowly, put $t_*=5(y_*-12)/96$. Then $9/10<t_*<901/1000$. Direct endpoint operations on $t\in[9/10,901/1000]$ give the following containing intervals for the quadratic (10.1):

$$
\begin{array}{c|c}
\ell&\text{interval containing }Q_t(\ell)\\ \hline
4/3&[2666666/10^9,\ 9868445/10^9]\\
3/2&[-13250000/10^9,\ -4697750/10^9]\\
8/5&[-11200000/10^9,\ -1789440/10^9]\\
9/5&[19000000/10^9,\ 30235240/10^9].
\end{array}                                                       \tag{15.8}
$$

The positive leading coefficient and the two sign changes isolate one root $\ell_-$ in $(4/3,3/2)$ and the other $\ell_+$ in $(8/5,9/5)$. These are precisely the two roots used by $\mathcal A_{y_*}$ in (11.6). On both root intervals, $1<\ell<8/3$ and $0<t_*\ell-1<1$; hence the sources (10.3) are strictly positive, trace one and rank one. Their gains $8T(T-5)(T-7)/(5\ell)$ are nonzero cubics, and their drifts are zero. Their different $\ell$ values give different sources, and (15.5) separates both complete targets from $\mathcal T$. Thus $|\mathcal K|=5$.

Theorem 10.1 and Proposition 11.3 give these two worlds' whole parent history $H_p(y_*)$ and their following actual responses:

$$
\begin{array}{c|c|c|c|c}
E_5&E_6&z_5&z_6&z_7\text{ for either final atom}\\ \hline
J&J&0&-y_*/2&0\\
J&M&0&-126/5&0\\
M&J&0&48/5-y_*&0\\
M&M&0&-156/5-48/(5\ell)&0.
\end{array}                                                       \tag{15.9}
$$

This uses exactly the same $y_*$ as (15.7). After fifth $M$, all five worlds have the actual response $0$. In this child, sixth $J$ has the response $48/5-y_*$ retaining $\mathcal A_{y_*}$ with $L_1$, whereas sixth $M$ has response $v_*$ retaining $\mathcal T$ with $L_1$. The pair alone has different sixth-$M$ responses, as is also explicit in (15.9); it is the jointly realized triple that supplies this second sixth-action clause. Lemma 9.3 and (1.1), or equivalently the finer gluing implication of Theorem 12.3, give $L_2(\mathcal K,(H_p(y_*),M,0))$.

At the parent, fifth $J$ has a response-$0$ child containing the same $\mathcal A_{y_*}$ with $L_2$, and fifth $M$ has the response-$0$ child $\mathcal K$ with the just established $L_2$. Applying (1.1) gives $L_3(\mathcal K,H_p(y_*))$. All inclusions concern fixed complete targets and their entire literal histories. Arbitrary discontinuous deterministic choices and early stopping are covered by that recursion. ∎

**推论 15.2（两种符号的输运与原根边界）。** For every $D_0\in\mathbb R$ and $\lambda\ne0$, set $Y_*=D_0+\lambda y_*$. The transported family $\Phi_{D_0,\lambda}(\mathcal K)$ has exactly five distinct complete targets at the parent $H_J(Y_*)$ of (5.1), and

$$
\begin{gathered}
L_1\bigl(\Phi_{D_0,\lambda}(\mathcal T),
(H_J(Y_*),M,D_0,M,D_0+\lambda v_*)\bigr),\\
L_2\bigl(\Phi_{D_0,\lambda}(\mathcal K),(H_J(Y_*),M,D_0)\bigr),\\
L_3\bigl(\Phi_{D_0,\lambda}(\mathcal K),H_J(Y_*)\bigr).
\end{gathered}                                                     \tag{15.10}
$$

The three failure predicates in (15.10) also hold on the respective whole compatible fibers by inclusion. They concern this one exact normalized $y_*$ and its affine images. An original-root lower bound additionally requires losing actual children for both actions throughout the necessary earlier histories, with one consistent realization along each selected path. A policy beginning at the original root need not reach $H_p(y_*)$ or any of these transported parents. Thus (15.2)–(15.10) do not settle the unrestricted eight-reading question of Open Problem 8.2, provide a nine-reading upper bound, or classify other $y$ values or all fifth-$M$ fibers.

Proof. Apply the bijection in Lemma 9.2 to each fixed target, each full history and each selected actual response in Theorem 15.1. Its inverse preserves target distinction and the recursion for either sign of $\lambda$; in particular the sixth-$J$ response after fifth $M$ is $D_0+\lambda(48/5-y_*)$, and the triple's sixth-$M$ response is $D_0+\lambda v_*$. The whole-fiber implications follow from Lemma 9.3. These applications start at the displayed parents and supply no losing children at earlier nodes, which is the remaining hypothesis needed for a conclusion at the original root. ∎

**复用块的本卷接口。** 令 $\widetilde{\mathcal T},\widetilde{\mathcal K}$ 表示上述 V 的归一族，并对任意 $D_0$ 与任意非零 $\lambda$ 固定

$$
\begin{gathered}
Y_*=D_0+\lambda y_*,\\
\mathcal T_*=\Phi_{D_0,\lambda}(\widetilde{\mathcal T}),\qquad
\mathcal K_*=\Phi_{D_0,\lambda}(\widetilde{\mathcal K})
=\mathcal A_{y_*}\cup\mathcal T_*,\\
H_{M0,*}=(H_p(Y_*),M,D_0),\qquad
H_{MM,*}=(H_{M0,*},M,D_0+\lambda v_*).
\end{gathered}                                                    \tag{4.15}
$$

这里右侧 $\mathcal A_{y_*}$ 采用本卷 (4.7) 已固定的物理参数版本，故并集的五个世界全部共享同一个 $H_p(Y_*)$。V 定理 15.1、推论 15.2 给出

$$
\begin{gathered}
|\mathcal T_*|=3,\qquad |\mathcal K_*|=5,\qquad
\mathcal T_*\subseteq\mathcal F(H_{MM,*}),\\
L_1(\mathcal T_*,H_{MM,*}),\qquad
L_2(\mathcal K_*,H_{M0,*}),\qquad
L_3(\mathcal K_*,H_p(Y_*)).
\end{gathered}                                                    \tag{4.16}
$$

每项也由向上单调性传到其整个实际纤维。末读 $J$ 在 $\mathcal T_*$ 内恰由标签 $1,2$ 碰撞，末读 $M$ 恰由标签 $1,3$ 碰撞；归一响应分别是 V 的 $R_1=R_2$ 与 $S_1=S_3$，物理响应分别为 $D_0+\lambda R_1$ 与 $D_0+\lambda S_1$。第六 $J$ 臂保留同一个 $\mathcal A_{y_*}$，实际读数是 $D_0+\lambda(48/5-y_*)$；第六 $M$ 臂保留 $\mathcal T_*$，实际读数是 $D_0+\lambda v_*$。两个臂各自只有所选原子及其立即读数，所有提前停止由同一失败递归排除。

这提供的是一个精确归一 $y_*$ 及其两种非零尺度符号的仿射副本，不是所有 $y,v$ 的存在性或分类。三目标各自的漂移、增益、根和射线信息只属于这些固定世界及其原历史；没有把它们输送到 $\mathcal U_{x,w}$ 的证明。定理 5.1、6.1 仍只在 (2.1) 的实际 $JMMJJJ$ 纤维上使用。本卷不另行构造 V 的族，亦不由该父层 $L_3$ 补出更早两个动作的实际失败子节点；原根问题仍须第 7 节的全部共同实现条件。

## 5. 任意不受限子纤维上的末端插值恒等式

**定理 5.1（无根承诺的 $R$ 公式）。** 取定义 2.1 的任意 $D_0,\lambda\ne0,Y,x,w$。每个 $W\in\mathcal U_{x,w}$ 都满足

$$
\boxed{\ R=5x-288+16(48-d)k+\frac{5(d-24)}k\ }.            \tag{5.1}
$$

这里 $y$、$x$、$w$ 是同一字面实际历史的响应；$d$ 仍是每个世界自己的漂移。公式不需要 $f(6)=0$、$f(7)\ne0$ 或 $w=d$。

证明。对一个任意相容世界，置

$$
b=(k+1)\ell=\operatorname{tr}(BP)>0,\qquad H(T)=bf(T).
                                                               \tag{5.2}
$$

由初读和前三个动作的全部祖先方程，以及实际第五读和第七 $J$ 预测，得

$$
\begin{aligned}
H(0)&=-bd, &H(1)&=\frac{(24-d)(k+1)}k,\\
H(2)&=(48-d)(k+1), &H(3)&=312/5-d,\\
H(5)&=x-d, &H(7)&=R-d.
\end{aligned}                                                   \tag{5.3}
$$

对整个次数至多三的多项式空间，节点 $0,1,2,3$ 的拉格朗日基为

$$
\begin{aligned}
\ell_0(T)&=-\frac{(T-1)(T-2)(T-3)}6,&
\ell_1(T)&=\frac{T(T-2)(T-3)}2,\\
\ell_2(T)&=-\frac{T(T-1)(T-3)}2,&
\ell_3(T)&=\frac{T(T-1)(T-2)}6.
\end{aligned}                                                   \tag{5.4}
$$

因此 $H(T)=\sum_{i=0}^3H(i)\ell_i(T)$，直接取值给出

$$
\begin{aligned}
H(5)&=-4H(0)+15H(1)-20H(2)+10H(3),\\
H(7)&=-20H(0)+70H(1)-84H(2)+35H(3),\\
H(7)-5H(5)&=-5H(1)+16H(2)-15H(3).
\end{aligned}                                                   \tag{5.5}
$$

最后一式左边为 $R-5x+4d$，右边代入 (5.3) 为

$$
-\frac{5(24-d)(k+1)}k+16(48-d)(k+1)-15(312/5-d)
=-288+4d+16(48-d)k+\frac{5(d-24)}k.
$$

消去 $4d$ 即得 (5.1)。除固定整数外，只使用了正数 $k$ 作分母；$b$ 的定义也严格为正。没有除以任何增益样本或首项系数。整个推导对任意较低次数、变号、采样根和重复根同时成立，不丢弃第四或第六实际方程；它们仍是 $W\in\mathcal U_{x,w}$ 的条件，只是 (5.1) 的消元没有用到它们。∎

## 6. 异 k、同漂移 R 碰撞的必要联合条件

**定理 6.1（乘积、漂移范围与对称节点约束）。** 设同一个整个 $\mathcal U_{x,w}$ 中两个已实际实现的世界 $W_1,W_2$ 满足

$$
d_1=d_2=d,\qquad k_1\ne k_2,\qquad R(W_1)=R(W_2)=R.
                                                               \tag{6.1}
$$

则必有

$$
\boxed{\
24<d<48,\quad k_1k_2=\frac{5(d-24)}{16(48-d)},\quad
 y+w=2d,\quad y\ne w,\quad R=8d-\frac{312}{5}-6x.
\ }                                                            \tag{6.2}
$$

这些是相同实际历史上的必要条件，不是碰撞存在或充分性的判据。

证明。先相减两个世界的 (5.1)，用 $k_1-k_2\ne0$ 得

$$
16(48-d)+\frac{5(24-d)}{k_1k_2}=0.                          \tag{6.3}
$$

在奇异漂移 $d=24$，左边为 $384$；在 $d=48$，左边为 $-120/(k_1k_2)$。两者都不为零，故排除这两层后才可解得乘积式。$k_1k_2>0$ 强制 $(d-24)/(48-d)>0$，等价于 $24<d<48$；小于 $24$ 或大于 $48$ 时比值为负。这一步没有除以采样增益。

对每个世界置

$$
b_i=(k_i+1)\ell_i>0,\qquad H_i(T)=b_if_i(T),\qquad
 t_i=\frac{\operatorname{tr}(CP_i)}{b_i}>0.                 \tag{6.4}
$$

共同的第三、第五响应及 $R$ 给出

$$
H_i(3)=312/5-d,\qquad H_i(5)=x-d,\qquad H_i(7)=R-d.
$$

两个次数至多三的多项式之差因而为

$$
H_1(T)-H_2(T)=c(T-3)(T-5)(T-7).                            \tag{6.5}
$$

第二时钟的差为 $(48-d)(k_1-k_2)\ne0$，于是

$$
c=-\frac{(48-d)(k_1-k_2)}{15}\ne0,\qquad
H_1(4)-H_2(4)=3c,\qquad H_1(6)-H_2(6)=-3c.                \tag{6.6}
$$

这个因式分解包括次数下降；非零的第二时钟差已经排除了零差多项式。

所需的另一插值恒等式是：对任意次数至多三的 $H$，

$$
\boxed{\ H(4)+H(6)=\frac{H(3)+6H(5)+H(7)}4\ }.            \tag{6.7}
$$

证明该式只须在线性基 $1,T,T^2,T^3$ 上验证；左右的共同值依次为 $2,10,52,280$。由此，$H_1,H_2$ 在四、六两点的和都是

$$
K=\frac{312/5+6x+R-8d}{4}.                                \tag{6.8}
$$

同一个世界在第四、六时钟的累计矩阵均为 $C$，因此不能独立拟合它们；全部实际方程给出

$$
y-d=t_iH_i(4),\qquad w-d=t_iH_i(6),\qquad
 y+w-2d=t_iK\quad(i=1,2).                                 \tag{6.9}
$$

若 $K\ne0$，求和式强制两个 $t_i$ 同为 $(y+w-2d)/K$。这个共同值严格为正，因为每个 $t_i$ 都来自正迹与正的 $b_i$。第四方程就强制 $H_1(4)=H_2(4)$，与 $3c\ne0$ 矛盾。若分子为零，同一求和式已经与 $t_i>0,K\ne0$ 矛盾，所以没有遗漏该情形。

因此只能 $K=0$。在这一层不除以 $K$；直接由 (6.8)–(6.9) 得 $y+w=2d$ 和 $R=8d-312/5-6x$。若再有 $y=w$，则 $y=w=d$，第四方程与 $t_i>0$ 给出 $H_1(4)=H_2(4)=0$，又与 (6.6) 矛盾。故 $y\ne w$。整个证明没有除以 $y-d,w-d,H_i(4),H_i(6)$ 或 $c$。∎

**边界 6.2（必要轨迹不生成见证）。** 若 $y=w$，定理仅排除同漂移且异 $k$ 的 $R$ 碰撞。同 $k$ 的情况、异漂移的情况、(6.2) 是否足以实现某个合法碰撞，以及额外的 $S$ 相等条件，仍须分别处理。各世界的源正性、秩一、迹一、单一完整增益与每个祖先方程都不可删除。

定理 3.3 的碰撞恰在 $k_1=k_2=5/8,d=0$ 上，所以 (6.3) 的除法在那里不可用。它的存在由原世界及全历史表证明，绝非由 (6.2) 的必要轨迹认证。两种结果的量词和用途不同。

## 7. 保留全部原根动作与 G、D 守卫的既有等价

本节完整保留 IV 定理 9.3、13.3 的原根判据，作为原目标的接口；它不是本卷新增的原根解答。一个局部强制动作链没有为这个系统给出可行元，也没有证明其为空。

**定义 7.1（全部原根槽与共享祖先）。** 令

$$
\begin{aligned}
\mathcal S&=\{(w,e):w\in\{J,M\}^7,\ e\in\{0,1\}\},\\
\mathcal V&=\bigcup_{i=1}^7\{J,M\}^i,\\
\mathcal P&=\left\{\begin{pmatrix}a&b\\c&1-a\end{pmatrix}:
0<a<1,\ b,c>0,\ bc=a(1-a)\right\}.
\end{aligned}                                                   \tag{7.1}
$$

共有 $256$ 个槽、$254$ 个非空前缀和 $128$ 个叶对。固定一个合法源元组 $\mathbf P=(P_q)_{q\in\mathcal S}\in\mathcal P^{\mathcal S}$，保留其全部 $256$ 个秩一方程及严格正性。源可以重复；不同叶之间的目标也可以重复。对前缀 $v=E_1\cdots E_i$，令

$$
A_v=E_i\cdots E_1,\qquad
\mathcal D_v=\{(w,e):v\text{ 是 }w\text{ 的前缀}\},
$$

并令 $q_v$ 是按 $J<M,0<1$ 排序的首个后代槽。根的后代集为 $\mathcal S$，累计矩阵为 $I$。置

$$
t_v(P)=\operatorname{tr}(A_vP),\qquad
\ell_v(P)=(t_v(P)-1,\ i t_v(P),\ i^2t_v(P),\ i^3t_v(P)).
                                                               \tag{7.2}
$$

一个非零四维系数块 $x_q$ 对应完整的初读零世界

$$
g_q(T)=\sum_{j=0}^3x_{qj}T^j,\qquad \delta_q=-x_{q0}.
                                                               \tag{7.3}
$$

这是 $g_q(0)+\delta_q=0$，不是对 $g_q(0)$ 或 $\delta_q$ 各自为零的承诺。其前缀响应恰为 $\ell_v(P_q)x_q$。

令 $B(\mathbf P)$ 作用于 $x=(x_q)_{q\in\mathcal S}\in\mathbb R^{1024}$，其全部行是

$$
(Bx)_{v,q}=\ell_v(P_q)x_q-\ell_v(P_{q_v})x_{q_v},
\quad v\in\mathcal V,\ q\in\mathcal D_v\setminus\{q_v\}.
                                                               \tag{7.4}
$$

它为 $1538\times1024$ 矩阵，各深度的行数依次为

$$
(254,252,248,240,224,192,128).                               \tag{7.5}
$$

这些行数为 $2^i(2^{8-i}-1)$，保留每个后代与同一参考后代之间的响应相等。所有共享祖先方程与下式等价：

$$
\ell_v(P_q)x_q=z_v\ (q\in\mathcal D_v)
\quad\Longleftrightarrow\quad
 Bx=0,\quad z_v=\ell_v(P_{q_v})x_{q_v}.                     \tag{7.6}
$$

因此 $254$ 个共同响应不是逐叶独立拟合的量。对于 $P_q=\left(\begin{smallmatrix}a_q&b_q\\c_q&1-a_q\end{smallmatrix}\right)$，

$$
t_v(P_q)=(A_v)_{22}+((A_v)_{11}-(A_v)_{22})a_q
 +(A_v)_{21}b_q+(A_v)_{12}c_q,                              \tag{7.7}
$$

故矩阵条目是 $768$ 个环境源坐标的整数仿射式；$768$ 不是删除源方程后的自由维数。

**定义 7.2（所有增益及完整同源区别）。** 定义完整四维块映射

$$
G_qx=x_q\quad(q\in\mathcal S),\qquad
D_wx=x_{(w,0)}-x_{(w,1)}\quad(w\in\{J,M\}^7).              \tag{7.8}
$$

每个 $G_qx\ne0$ 是该槽增益非零的必要条件。叶对完整目标不同恰为

$$
P_{(w,0)}\ne P_{(w,1)}\quad\text{或}\quad D_wx\ne0.         \tag{7.9}
$$

若源相同，$D_w$ 必须保留全部四个系数差，包括由常数项决定的漂移差；不能只要求某个指定系数不同。

**命题 7.3（复用的精确源秩判据）。** 对每个固定合法源元组，存在满足全部共同祖先、全部非零增益及全部叶对区别的一个系数向量，当且仅当令 $\rho=\operatorname{rank}B(\mathbf P)$ 后有

$$
\begin{aligned}
\operatorname{rank}[B;G_q]&>\rho &&\text{对全部 }q\in\mathcal S,\\
P_{(w,0)}\ne P_{(w,1)}\quad\text{或}\quad
\operatorname{rank}[B;D_w]&>\rho &&\text{对全部 }w\in\{J,M\}^7.
\end{aligned}                                                   \tag{7.10}
$$

证明。共享响应由 (7.6) 全部消去。令 $U=\ker B$；对任意线性块映射 $T$，秩与零度公式给出

$$
\operatorname{rank}[B;T]-\operatorname{rank}B
=\dim U-\dim(U\cap\ker T)=\operatorname{rank}(T|_U).        \tag{7.11}
$$

一个合法 $x\in U$ 必须使每个 $G_qx$ 非零，也必须使每个同源叶的 $D_wx$ 非零，所以每个适用限制映射均非零，得必要性。

反之，将全部 $G_q$ 与全部同源叶的 $D_w$ 列为 $T_1,\ldots,T_m$，其中 $256\le m\le384$。(7.10) 保证每个 $T_j|_U$ 非零。各选 $u_j\in U$ 及 $T_j$ 的一个标量分量 $L_j$ 使 $L_j(u_j)\ne0$，并考虑

$$
u(t)=\sum_{j=1}^m t^{j-1}u_j\in U.                         \tag{7.12}
$$

$L_j(u(t))$ 的 $t^{j-1}$ 系数正是 $L_j(u_j)\ne0$，所以每个都是非零多项式。取一个实数避开它们有限个根的并，单一向量 $x=u(t)$ 就同时满足所有 $T_jx\ne0$。这不是为每个动作或叶选择不同向量。$U=\{0\}$ 会使所有增益守卫失败，因而没有零核例外。由 (7.3) 重构每个固定完整世界，再由 (7.6) 给出同一前缀共享的 $z_v$，即得全部相容性及区别。∎

为明确保留全部秩下降层，令

$$
\begin{aligned}
s_w&=2(a_{(w,0)}-a_{(w,1)})^2
 +(b_{(w,0)}-b_{(w,1)})^2+(c_{(w,0)}-c_{(w,1)})^2,\\
\mu_j(A)&=\sum_{\substack{I,J\text{ 为行、列指标集}\\|I|=|J|=j}}
             \det(A_{I,J})^2,\qquad \mu_0(A)=1.
\end{aligned}                                                   \tag{7.13}
$$

$j$ 超过矩阵任一维时取 $\mu_j=0$。$s_w$ 为源差的 Frobenius 范数平方。既有的完整源公式是

$$
\begin{aligned}
\Phi(\mathbf P)=\bigvee_{\rho=0}^{1024}\Bigl[&
\mu_\rho(B)>0\ \land\ \mu_{\rho+1}(B)=0\\
&\land\bigwedge_{q\in\mathcal S}\mu_{\rho+1}([B;G_q])>0\\
&\land\bigwedge_{w\in\{J,M\}^7}
 \bigl(s_w>0\ \lor\ \mu_{\rho+1}([B;D_w])>0\bigr)\Bigr],\\
\mathfrak S_7&=\{\mathbf P\in\mathcal P^{\mathcal S}:\Phi(\mathbf P)\}.
\end{aligned}                                                   \tag{7.14}
$$

实矩阵上，平方子式之和为零等价于每个子式均为零，故这正是 (7.10) 的有限多项式写法，包括全部秩层。

**命题 7.4（所有原根动作、实际子节点与提前停止）。** $\mathfrak S_7\ne\varnothing$ 等价于不存在整个 $\mathcal W_3$ 上至多八次总读数的完整目标解码器；$\mathfrak S_7=\varnothing$ 等价于存在这样的解码器。本卷没有判定其中任何一项。

证明。若源元组满足 (7.14)，命题 7.3 给出一个共同系数向量和固定完整世界 $W_q$。对每个前缀置

$$
H_v=(0,E_1,z_{E_1},\ldots,E_i,z_v),\qquad
K_v=\{W_q:q\in\mathcal D_v\}.
$$

每个世界满足其所有祖先读数。对每个下一动作 $E$，有实际子节点包含关系

$$
K_{vE}\subseteq K_v\cap\mathcal F(H_v,E,z_{vE}).             \tag{7.15}
$$

只需包含，不要求等号。每个叶有不同完整目标对，故有 $L_0$；以 (7.15)、向上单调性及 (1.2) 的两个动作合取向上归纳，得每个前缀的 $L_{7-|v|}$，包括初读零根的 $L_7$。每个节点都含后代的不同目标对，故所有提前停止也被覆盖。第一个动作无论 $J$ 或 $M$、每个后续动作及其选定失败响应都在同一系统内。

反之，初读零整个纤维的 $L_7$ 按 (1.2) 展开：对每个前缀、每种下一动作选一个失败实际响应，在每个深度七的叶取不同目标对。所得 $256$ 个槽的固定世界同时满足各自全部祖先及一个共享的 $z_v$，所以 (7.6)、所有 $G$ 和适用的 $D$ 条件都成立。命题 7.3 给出一个 $\mathfrak S_7$ 元。这是同一有限树的双向展开，不是彼此无关的末端配对。

最后，对任意已取得的初读 $a=g(0)+\delta$，映射

$$
(P,g,\delta)\longmapsto(P,g,\delta-a)                       \tag{7.16}
$$

将整个初读 $a$ 纤维双射到整个初读零纤维，在每条动作字上把全部读数减去 $a$，保留时钟、源、增益、所有响应分割及停止。初读零解码器通过减去实际初读、执行同一选择并给返回漂移加回 $a$，运输到整个 $\mathcal W_3$；全域解码器也可限制到初读零。结合定义 1.2 的有限时限对应，得到等价。∎

**说明 7.5（全部 G 成立不准删除同源 D）。** IV 命题 13.4 的合法反例也保留在这个接口中：令所有 $256$ 个源都为

$$
P_*=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix}.
$$

任意 $h\in\mathbb R^4$ 的对角系数向量 $x_q=h$ 都在 $\ker B$，所以每个 $G_q|_{\ker B}$ 满射，所有增益守卫成立。但在 $w_*=M^7$ 的同源叶，两槽在时钟 $1,2,3,4$ 的读数相等强制

$$
R_*D_{w_*}x=0,\qquad
R_*=\begin{pmatrix}
1/2&3/2&3/2&3/2\\
3/2&5&10&20\\
3&12&36&108\\
11/2&26&104&416
\end{pmatrix}.                                               \tag{7.17}
$$

这里 $\operatorname{tr}(M^iP_*)$ 在这四个原时钟为 $(3/2,5/2,4,13/2)$，代入 (7.2) 即给出该矩阵。从 $2R_*$ 后三行分别减去第一行的 $3,6,11$ 倍，留下右下三阶块

$$
\begin{pmatrix}1&11&31\\6&54&198\\19&175&799\end{pmatrix}.
$$

再消去首列，最后二阶行列式为

$$
\det\begin{pmatrix}-12&12\\-34&210\end{pmatrix}
=-2520+408=-2112,\qquad \det R_*=-2112/16=-132\ne0.
$$

故所有 $x\in\ker B$ 都满足 $D_{w_*}x=0$，这个同源叶的区别守卫失败。该元组不是失败树见证，不能因它的所有 $G$ 成立就忽略 $D$；也不能由这个元组的失败推出所有合法源元组均失败。

## 8. 数学来源、参数对应与新增范围

本卷相对于所列既有结果的额外推导是：整个不受限实际 $\mathcal U_{x,w}$ 上的无根承诺恒等式 (5.1)，以及已实现的同漂移、异 $k$ 的 $R$ 碰撞必须满足的联合条件 (6.2)。式 (6.7) 是该证明使用的三次插值工具，不将一般插值原理另称新内容。第 3、4 节的显式对、互补历史碰撞、第五 $J$ 的 $L_2$、条件第五及第六 $M$ 必要性和同父粘合，均为 V 既有结果的实例、复用或参数输运；所保留的完整计算不改变其既有成果身份。第 4.7 小节的 V 第 13–15 节完整有理收缩盒证书、精确三目标与五目标父失败族，同样全部为既有结果的复用及应用；它们在一个精确 $y_*$ 上补足 V 第 12 节条件粘合的存在性前提，不增加本卷的独立见证。旧多项式、承诺解码器和原根等价也不计为新构造。

| 数学来源 | 精确对应及保留的适用条件 |
| --- | --- |
| [V](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_V.md) 定理 10.1、11.1 | V 的归一父历史正是本卷 $H_p(Y)$ 减去 $D_0$ 再除以 $\lambda$；V 的 $L_0,Q,C_0$ 对应本卷 $L,B,C$，不能把它的矩阵 $Q$ 与本卷 $Q=MC$ 混同。完整第五 $J$ 二目标 $L_2$ 刻画和两个严格开窗口由 (4.4)–(4.6) 复用；基线漂移和增益射线是完整二目标失败的结论，不是一次零响应给出的信息。该刻画不分类更大失败族或单个第六分支的末端碰撞。 |
| V 命题 5.3、11.3，定理 12.1 | 本卷 $y=1632/55,t=81/88,\ell=88/69,88/53$ 的同一显式配对已经位于规范窗口内。第 3 节全历史表、第 4 节第五 $J$ 失败和条件第五 $M$ 必要性均为既有应用。规范结果还给出实际第五 $M$ 响应 $D_0$ 后的第六 $M$ 必要性，仍以全纤维成功要求为前提；该对在 $M,M$ 上的分离只恢复该对。 |
| V 定理 12.2、12.3，推论 12.4 | (4.9)–(4.14) 完整保留同一 $y$、完整字面父历史、实际第五或第六子纤维成员资格，以及任意基数的同父粘合和条件等价。规范归一化的第五 $M0$ 实际读数为 $D_0$，其第六 $J$ 读数为 $2D_0+48\lambda/5-Y$。两个最后动作可有不同碰撞对；粘合条件式不要求一个共同坏对。其存在性前提在 V 第 13–15 节的精确 $y_*,v_*$ 处由实际三目标补足，其范围为一个精确父参数及其仿射副本，不是所有 $y,v$ 的分类。 |
| V 定义 13.1、定理 14.2、15.1、推论 15.2 | 第 4.7 小节完整保留其有理插值、九元联合方程、中心、$9\times9$ 有理矩阵、区间与导数规则、全部行界、收缩误差、投影及末端分离界，以及精确极限和五目标失败证明。$29286821/10^6<y_*<29286822/10^6$，$-45328099/10^6<v_*<-45328097/10^6$；精确相等来自联合零点定理。实际历史是 $(H_p(y_*),M,0,M,v_*)$，末 $J$ 对 $1,2$，末 $M$ 对 $1,3$；与同一规范 $\mathcal A_{y_*}$ 粘成 $L_2$ 与父 $L_3$。两种符号的运输保持完整世界、原时钟与所有停止。此处时钟五、六的累计矩阵为 $Q,MQ$，不是 $\mathcal U_{x,w}$ 的 $B,C$；实例及其漂移、增益、根或射线事实不跨历史迁移。只解决这个精确父参数及其仿射副本的局部存在性，不提供较早原根失败子树或所有纤维分类。 |
| V 定理 5.2、命题 5.3 | 整个承诺类为相同 $JMMJ$ 父历史中的 $\delta=D_0,g(7)=0$ 世界；增益射线在该类内推出。第五、第六 $M,M$ 的七总读逆不等于不受限父纤维的逆，响应 $D_0$ 本身也不认证这些承诺。显式两世界与该逆和分离完全相容。 |
| IV 定理 2.1、式 (2.2)、推论 2.2 | 本卷 $R_a=R_1,R_b=R_3$，旧的未归一化增益为 $\lambda T(T-5)(T-7)$，旧漂移取 $D_0$。旧失败历史是第四 $M$ 的 $JMMM$，状态 $J+2L$，第四读数 $D_0+252\lambda/5$。V 命题 5.3、11.3 已在第四 $J$ 的不同字面历史上验证 $\operatorname{tr}(CR_a)=\operatorname{tr}(CR_b)=136/55$，第四读数为 $D_0+1632\lambda/55$；本卷保留其逐项证明，没有将第四 $M$ 历史直接改名，也不把该互补响应计作新增结果。旧的条件第四 $J$ 必要性与 V 的条件第五 $M$ 必要性可以接续，但仍只是条件链。 |
| [VII](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_VII.md) 定义 12.1、式 (12.3)–(12.5)、定义 14.2 | 本卷 $H_p(Y),f,d,y,k,\ell,r,x,w,R,S$ 与该接口完全相同；$B=J+L$，$C$ 是实际第六 $J$ 状态，$Q$ 是此状态的最后 $M$ 后继。特例取 $y=1632/55,x=0,w=-816/55$，没有把实际第六读数视为漂移。 |
| VII 引理 12.3、13.1，定理 13.2、推论 14.1 | 既有整个承诺类是 $\mathcal C_6(H_p)=\{W\in\mathcal F(H_p):f(6)=0\}$。对其任意已知子集，允许任意基数与不同漂移；第五 $J$、第六 $J$ 后第六读数才等于漂移，每个所得整个子纤维至多两世界，两个末端预测联合单射，因这个二世界上界可选择一个末动作，以至多八次总读数完整恢复。根七可以存在，源无需对称。本卷两个见证均有 $f(6)\ne0$，实现了既有推论所要求的非根六失败成员；并不推翻根六承诺解码器，也不把承诺当成从历史取得的信息。 |
| VII 定理 4.1、5.1、推论 5.2 | 既有任意漂移二目标 $L_2$ 排除在实际第五 $M$ 状态 $Q$ 上。其整族消费者假设每个整个实际第五 $M$ 子纤维至多两目标。这里的第五 $J$ 状态是 $B$，且同一对在第五 $M$、第六 $M$ 上已被分离，所以两个结论相容。没有从二目标排除推出更大纤维解码器，也没有给不受限 $\mathcal U_{x,w}$ 插入有限基数条件。 |
| VII 第 8–11 节 | $H_*$ 的归一化第四读数是 $48/5$，第五动作为 $M$、响应为 $-532/5$。其完整纤维增益射线排除、$\operatorname{tr}(JP)=1$ 的两世界切片、远端代数目标、局部逆及充分小整个已知源带上的七读逆，均保留这个不同祖先及其仿射副本。源带成员资格是已知限制，半径只是存在性，带外纤维与跨带碰撞未由该逆判定。第 3 节的归一化第四读数是 $1632/55$ 且第五动作取 $J$；第 4.7 小节的规范三目标则取第四读数 $y_*$、第五 $M$ 响应零。两者均保持自己的完整历史，不迁移 $H_*$ 的切片、射线或带承诺。 |
| VII 第 6、7、11 节 | 共同预测类属于另一字面父历史 $(0,M,1,M,23/7,J,331/35,M,Y)$。其整族结果要求已知共同 $m,j,b_0,d_0$，其中 $\kappa=m-j,\omega=d_0-b_0$，并要求 $\omega\ne0$ 或 $\omega=0,\kappa\ne0$；$\omega=\kappa=0$ 层不在该消费者内。所述不同 $MMJM$ 父节点的至多三目标结论也保留其规模与历史条件。这些条件均未移到当前 $JMMJ$ 或 $JMMJJJ$ 纤维。 |
| IV 第 3–8、11–12 节 | $MJMJ$、$JMJMJ$ 的失败例子保持自己的祖先与互补臂。共同第五响应的 $MMJM$ 例外对、割线系统、交叉分配排除及混合第六根结式保持其共同响应、非对角和恰三目标等条件；这些条件不是本卷整个实际纤维的限制。 |
| IV 第 9–10、13–14 节 | 十六槽局部系统属于它的 $MMJM$ 历史；原根 $256$ 槽、全部共享前缀、$1538\times1024$ 响应矩阵及全部 $G,D$ 守卫由第 7 节原样保留其数学量词。有限固定线性增益射线读出障碍不等于任意非线性完整目标协议的八读下界。没有给这些系统赋予可行性结论。 |

迹线性、秩一归一化、三次插值、有限时限递归、秩与零度及有限子空间避让都是既有数学工具。(5.4)–(5.5) 和 (6.7) 在整个三次及以下空间上使用，不将一般插值原理另称新定理。本卷的来源对应限于 IV、V、VII 所给出的内容，不构成外部优先权、文献穷尽或世界范围原创认证。

## 9. 完整目标与仍未解决的边界

**局部结论的精确量词。** 对任意 $D_0$ 和两种非零 $\lambda$，既有窗口在已显示的 $Y_\dagger$ 上给出 $x=0,w=-816/55$ 的同一整个实际 $\mathcal U_{x,w}$，两个合法末动作都非单射；同一固定不同世界对已经足够。第五 $J$ 的 $L_2$ 覆盖两种第六动作及其各自全部最后动作，并覆盖每个所用节点的提前停止。这是 V 定理 10.1、11.1、12.1 与命题 11.3 的应用，反驳对所有 $Y,x,w$ 的无条件固定第五 $J$、第六 $J$ 末动作逆，不是新增的失败族或新窗口。规范结果在整个 $y\in\mathcal I$ 上给出成功全纤维解码器的第五 $M$ 必要性及实际响应 $D_0$ 后第六 $M$ 必要性，但不声称每个 $Y$ 都失败、每个协议都会到达所示历史或这些必要动作已经构成解码器。

**整个纤维没有被有限见证替换。** $\mathcal F(H_p)$、$\mathcal F(H_x)$、$\mathcal U_{0,-816/55}$ 均保留其他所有相容世界。V 的第五 $J$ 二目标 $L_2$ 刻画没有分类这些整个纤维中的所有漂移、增益、源或根型；没有给整个纤维的基数上界，也没有构造或断言该 $\mathcal U$ 必有根六成员。见证自己的共同漂移、共同增益射线与根 $0,5,7$ 不成为输入承诺。两世界都不是第六根世界，而且第六读数不同于真实漂移。

**精确第五 M 族已经存在，更早原根两臂仍须共同实现。** 第 3 节的同一对在第五 $M$、第六 $M$ 已被分开，只排除用该对证明其父层 $L_3$。V 定理 14.2、15.1 已在另一个精确 $y_*$ 上供应共同实现的三目标：实际历史是 $JMMJMM$，第五归一响应为零，第六归一响应为 $v_*$，最后 $J$ 的碰撞对为 $1,2$，最后 $M$ 的碰撞对为 $1,3$。与同一个规范 $\mathcal A_{y_*}$ 组成的五目标族有实际第五 $M0$ 子节点 $L_2$ 和完整同父 $L_3$；第 4.7 小节完整复用其存在定理、证书数据和证明，本卷不另行构造该族。它们的整个实际纤维也由包含关系失败。该规范结果确定了这个精确参数处的局部存在性。

这个结论限于一个精确 $y_*$ 及其仿射副本。一般所有 $y,v$ 的分类、其他精确 $y$（包括第 3 节固定的 $1632/55$）的相应完整第五 $M$ 子树和父层判定、初始 $J$ 或其他原根分支的完整失败树，均未由此解决。不同第六动作可以保留不同坏对，坏对可以无公共端点；排除一个二目标或给出一个局部失败子集，均不能替代其他实际纤维的联合论证。本卷 (4.11)、(4.12) 是 V 定理 12.2、12.3 的同父归约，V 第 13–15 节在 $y_*,v_*$ 处供应其前提；二者都不允许移用不同 $Y$ 或不同祖先的配对。特别地，实际 $JMMJMM$ 三目标在 $JMMJJJ$ 的同一 $\mathcal U_{x,w}$ 中的成员资格未获证明；若要用于后者，须另证其全部共同实际方程，现有结果没有这样的跨历史桥梁。所有较早动作、实际响应与提前停止仍保留其原根义务。

**插值碰撞轨迹保持必要性。** (5.1) 对任意不受限 $\mathcal U_{x,w}$ 的每个成员成立；(6.2) 仅约束已经实现的异 $k$、同漂移 $R$ 碰撞。它的充分性、同 $k$、异漂移及联合 $S$ 碰撞分类没有解决。$y=w$ 的排除只在定理 6.1 的完整前提下成立，不能据此排除定理 3.3 的同 $k$ 见证。

**原根替代保持完整。** 原问题仍是

$$
\boxed{\ n_{\mathrm{det}}(3,0)\ge9\quad\text{还是}\quad
\text{存在整个 }\mathcal W_3\text{ 上至多八次总读数的完整目标解码器}\ }.
                                                               \tag{9.1}
$$

它量化全部初始动作、每条实际历史、全部祖先、每个提前停止、任意确定性策略，以及整个源、非零三次及以下增益和任意常漂移域。两种增益符号、较低次数、采样根、重复根及非对称源均保留。按第 7 节，下界方向需要一个满足所有 $G$ 与适用 $D$ 守卫的合法完整原根源元组；全域八读方向需要排除每个这样的元组，或给出全部实际历史上的合法动作和完整答案。局部强制动作链以及 V 的一个精确父层五目标 $L_3$ 都没有完成其中任何一项。没有九读上界由此得出，也没有以有限固定线性读出限制替代任意完整目标协议。

本卷结论是所列假设内的符号数学推导。不声称 Lean 或 kernel 认证、经验或数值实验认证、一般神经网络结论、噪声稳定性、有效计算、逆的效率或资源界。既有承诺结果仍按各自条件适用，不因此得到未知类标签的采集或不受限全域结论。

## 追加锚（本行以下为增补区）
