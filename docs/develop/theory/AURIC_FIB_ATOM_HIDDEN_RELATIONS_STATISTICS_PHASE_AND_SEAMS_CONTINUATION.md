# FIB-ATOM：隐藏关系、统计相位与共享接缝（续卷）

**约定 C-60.0（同一来源的延续）。** 本卷接续[《FIB-ATOM：隐藏关系、统计相位与共享接缝》第 59 章](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md#59-带标号正活动环与局部四角问题)。正乘积活动环、五态顺序、局部均值及底面残差均使用 C-59.2、C-59.4；以下 C-2–C-59 的条目号指该卷，C-60–C-66 指本卷。定义、条件事件和标号始终属于同一份有限联合律。

## 60. 外部路径的完整响应与五律

**定义 C-60.1（不含三个局部活动的外部矩阵）。** 固定中心 $i$，写 $L=i-1$、$C=i$、$R=i+1$。沿避开 $C$ 的环路，从 $L$ 到 $R$ 依次为

$$
L,r_1,r_2,\ldots,r_{n-3},R,
\qquad r_k=i-1-k\pmod n.
$$

这条路径有 $n-2$ 条边、$n-3$ 个内部顶点。复用 C-7.9 的兼容矩阵，改记

$$
J=\begin{pmatrix}1&1\\1&0\end{pmatrix},\qquad
D_j=\operatorname{diag}(1,\lambda_j),\qquad
H_i=J D_{r_1}J D_{r_2}\cdots J D_{r_{n-3}}J.
\tag{C60.1}
$$

$H_i$ 的行是 $B_L$，列是 $B_R$。它不含 $\lambda_L,\lambda_C,\lambda_R$。令 $s_0=x,s_{n-2}=y$，则等价的逐格定义为

$$
H_i(x,y)=\sum_{s_1,\ldots,s_{n-3}\in\{0,1\}}
\left(\prod_{k=1}^{n-3}\lambda_{r_k}^{s_k}\right)
\left(\prod_{k=0}^{n-3}J_{s_k,s_{k+1}}\right).
\tag{C60.2}
$$

因此每格是固定两个端点后外部填充的精确总权。

**命题 C-60.2（同源外部消元的五格应用）。** 定义 C-59.2 的三位边缘满足

$$
w=(H_{00},\lambda_LH_{10},\lambda_CH_{00},
\lambda_RH_{01},\lambda_L\lambda_RH_{11}),
\qquad p^{(i)}=\frac{w}{\mathcal Z},
\tag{C60.3}
$$

其中

$$
\mathcal Z=(1+\lambda_C)H_{00}
+\lambda_LH_{10}+\lambda_RH_{01}
+\lambda_L\lambda_RH_{11},\qquad w_2=\lambda_Cw_0.
\tag{C60.4}
$$

四个 $H_{xy}$ 都严格正。式 (C60.3) 使用全环的一个归一化常数，保留实际联合边界。

证明。展开矩阵积，每个内部指标是原来的 $B_{r_k}$，每个 $D_{r_k}$ 给予它的活动一次，每个 $J$ 检查一条外部边。这正是 C-8.2 的路径求和，参数取路径的 $n-1$ 个顶点，并将其两端对角活动从矩阵中取出；于是得到式 (C60.2)。内部全零是任意固定 $x,y$ 的合法填充，贡献一，所以各格至少为一。

固定局部合法三位 $(x,z,y)$，完整配置权分解为

$$
\lambda_L^x\lambda_C^z\lambda_R^y
J_{x,z}J_{z,y}
\left(\prod_k\lambda_{r_k}^{s_k}\right)
\left(\prod_kJ_{s_k,s_{k+1}}\right).
$$

外部求和只消去括号内的内部指标。按五模式依次代入，得到式 (C60.3) 的五项。每个合法全环配置恰进入一个局部模式，且每位活动、每条边恰计一次，五项和因此是原来的 $\mathcal Z$，并非另选的窗口总权。中位只在 010 出现，000 与 010 有相同的外部端点 00，故 $w_2=\lambda_Cw_0$。证毕。

有限求和重排使用 Peyrard 等 v2 §§2.1–2.2、3.2 的 sum-product 消元背景。这里原始边因子 $J_{11}=0$ 被保留；没有取它的对数，也不需要由条件独立反推正势分解。C-7.1 的孤立三位模型相当于没有额外联合外部因子；环上必须保留 $H_i$，不能把 C-7.1 的底面乘法式当成环上边缘的假设。

**命题 C-60.3（外部行列式进入局部残差）。** 对同一正活动环的每个中心，

$$
\det H_i=(-1)^{n-2}\prod_{j\notin\{L,C,R\}}\lambda_j,
\qquad
\Delta_i=\frac{(-1)^n\prod_{j\ne i}\lambda_j}{\mathcal Z^2}.
\tag{C60.5}
$$

因而偶数 $n$ 时 $\Delta_i>0$，奇数 $n$ 时 $\Delta_i<0$，有限正活动下均非零；并有

$$
\lambda_i\Delta_i
=\frac{(-1)^n\prod_j\lambda_j}{\mathcal Z^2},
\tag{C60.6}
$$

右边不依赖中心位置。

证明。C-8.2 的行列式乘法在式 (C60.1) 中给 $n-2$ 个 $\det J=-1$ 和 $n-3$ 个 $\det D_{r_k}=\lambda_{r_k}$。式 (C60.3) 的底面表是

$$
\begin{pmatrix}p_0&p_3\\p_1&p_{13}\end{pmatrix}
=\frac1{\mathcal Z}
\operatorname{diag}(1,\lambda_L)H_i
\operatorname{diag}(1,\lambda_R).
$$

两端活动贡献 $\lambda_L\lambda_R$，归一化贡献 $\mathcal Z^{-2}$，故得式 (C60.5)。$(-1)^{n-2}=(-1)^n$，正活动给严格符号。再乘中心活动即得式 (C60.6)。这个符号来自条件化后剩余路径的边数，不要求在一般图上按最短距离判符号。证毕。

Bencs 的 *Christoffel-Darboux type identities for independence polynomial*，v1 Theorem 1.3，是独立集多项式差的相关经典先例，其求和对象为含指定两点的诱导连通二分子图；Theorem 1.1 讨论匹配多项式。此处非齐次局部残差由上述实际路径乘积承担，不从一般图的最短路径奇偶性推出。[C-66.3](#66-来源范围与三种读数的共同边界) 记录该文的准确范围。

**命题 C-60.4（非均匀五环的完整实例）。** 按 $j=0,1,2,3,4$ 取

$$
(\lambda_0,\lambda_1,\lambda_2,\lambda_3,\lambda_4)=(1,2,3,4,5).
$$

则 $\mathcal Z=56$，中心 $i=2$ 的五律、活动比和残差为

$$
p^{(2)}=\frac{(7,12,21,8,8)}{56},\qquad
\frac{p_2}{p_0}=3,\qquad
\Delta_2=-\frac5{392},\qquad
\lambda_2\Delta_2=-\frac{15}{392}.
\tag{C60.7}
$$

全部窗口共享最后一个校准值，却不共享未经校准的 $\Delta_i$。

证明。五环合法独立集只有空集、单点及非相邻两点。单点总权为 $15$；两点 $\{0,2\},\{0,3\},\{1,3\},\{1,4\},\{2,4\}$ 的权依次为 $3,4,8,10,15$，总权 $40$，所以 $\mathcal Z=1+15+40=56$。中心二的外部路径是 $1,0,4,3$，故

$$
H_2=JD_0JD_4J=\begin{pmatrix}7&2\\6&1\end{pmatrix}.
$$

代入式 (C60.3) 得五项。交叉乘积差为 $(7\cdot8-12\cdot8)/56^2=-40/3136$，得到式 (C60.7)。对同一批十一种配置按其他中心分组，完整结果如下：

| 中心 $i$ | $56p^{(i)}$，按 $(0,1,2,3,13)$ | $56^2\Delta_i$ | $56^2\lambda_i\Delta_i$ |
| --- | --- | ---: | ---: |
| 0 | $(8,20,8,10,10)$ | $-120$ | $-120$ |
| 1 | $(10,5,20,18,3)$ | $-60$ | $-120$ |
| 2 | $(7,12,21,8,8)$ | $-40$ | $-120$ |
| 3 | $(4,6,16,15,15)$ | $-30$ | $-120$ |
| 4 | $(6,12,30,4,4)$ | $-24$ | $-120$ |

各行求和为 $56$，第三项与第一项之比分别为 $1,2,3,4,5$；共同校准值也等于 $-\prod_j\lambda_j/56^2=-120/3136$。证毕。

## 61. 外部对数四角项与固定均值纤维

**定义 C-61.1（外部耦合读数）。** 对定义 C-59.2 的窗口，置

$$
\Omega_i=\frac{p_0p_{13}}{p_1p_3},\qquad
\mathscr J_i=\log\Omega_i.
\tag{C61.1}
$$

所有对数均为自然对数。C-7.7–C-7.8 的四角差是经典正二元表坐标；这里对它的消费者是条件事件 $B_i=0$ 下的外部路径。它与中位也被求和的无条件端点表具有不同语义。

**命题 C-61.2（固定外部时的局部不变量与有效五律）。** 固定外部活动 $\lambda_j$，$j\notin\{L,C,R\}$，则

$$
\Omega_i=\frac{H_{00}H_{11}}{H_{10}H_{01}}
\tag{C61.2}
$$

在任意三个正局部活动 $\lambda_L,\lambda_C,\lambda_R$ 的变化下不变。取

$$
u=\frac{p_1}{p_0}=\lambda_L\frac{H_{10}}{H_{00}},\quad
v=\frac{p_3}{p_0}=\lambda_R\frac{H_{01}}{H_{00}},\quad
w=\frac{p_2}{p_0}=\lambda_C,
$$

则完整五律精确为

$$
p=\frac{(1,u,w,v,uv\exp\mathscr J_i)}
{1+u+w+v+uv\exp\mathscr J_i}.
\tag{C61.3}
$$

在这个表示中，$u,v$ 包含外部消息，不能当成裸端点活动。$\mathscr J_i=0$ 恰等价于底面条件独立；非零 $\mathscr J_i$ 是外部消元后仍需保留的联合因子。

证明。将式 (C60.3) 代入四角比，$\mathcal Z^2$ 及两端活动精确消去，得到式 (C61.2)。除全部五项以 $p_0$，最后一项等于 $uv\Omega_i$，归一化便给式 (C61.3)。在五个合法三位上，未归一化因子可写为

$$
u^xw^zv^y\exp(\mathscr J_i xy),\qquad xz=zy=0.
$$

当 $z=0$，四格表独立当且仅当交叉乘积相等，即 $\Omega_i=1$；这复用 C-3.2 和上述行列式供应的推导 5.1。若 $\mathscr J_i\ne0$，常数、单端项的对数四角差均为零，不能表示这个非零联合项。证毕。

残差 $\Delta_i$ 没有同样的局部不变性。例如固定两端及外部活动，令中心活动为 $t>0$，记

$$
A=H_{00}+\lambda_LH_{10}+\lambda_RH_{01}
+\lambda_L\lambda_RH_{11},\quad
N=\lambda_L\lambda_R\det H_i\ne0.
$$

于是 $\mathcal Z=A+tH_{00}$，

$$
\Delta_i(t)=\frac{N}{(A+tH_{00})^2},\qquad
\frac{d\Delta_i}{dt}=-\frac{2NH_{00}}{(A+tH_{00})^3}\ne0.
\tag{C61.4}
$$

中位均值 $Z(t)=tH_{00}/(A+tH_{00})$ 的导数为 $AH_{00}/(A+tH_{00})^2>0$。故同一个外部 $\Omega_i$ 可对应不同边缘及不同 $\Delta_i$。这也明确了变化时固定的是外部参数，并未同时固定均值纤维。

**命题 C-61.3（外部耦合在正均值纤维上选择唯一隐藏参数）。** 固定

$$
0<Z<1,\qquad r=1-Z,\qquad 0<X<r,\quad0<Y<r.
$$

四底角全正的五律恰由

$$
p(\kappa)=(r-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa),
\qquad
\max(0,X+Y-r)<\kappa<\min(X,Y)
\tag{C61.5}
$$

给出。在此开区间上，外部耦合所须匹配的函数为

$$
\mathscr J(\kappa)
=\log\frac{(r-X-Y+\kappa)\kappa}{(X-\kappa)(Y-\kappa)},
\qquad
\mathscr J'(\kappa)
=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}>0.
\tag{C61.6}
$$

因此给定实际外部矩阵 $H_i$ 和这组可见均值，至多存在一个与之相符的 $\kappa$；在抽象正五律纤维中，每个有限实值 $\mathscr J$ 恰对应一个 $\kappa$。

证明。由 $X,Y,Z,\kappa$ 逐项解出概率就是式 (C61.5)，其四个严格正条件等价于显示的区间。给定假设使区间非空：$X+Y-r<X,Y$ 且 $X,Y>0$。C-4.5–C-4.6 已在同一切向量 $(1,-1,0,-1,1)$ 上给出 Fisher 系数及四角差导数；将其 $\vartheta$ 对应为本节 $\mathscr J$，即得式 (C61.6)。逐项检验亦是 $p'_0=p'_{13}=1$、$p'_1=p'_3=-1$、$p'_2=0$，四个导数均以正号进入。

趋近左端时，分子至少一因子趋零，分母两因子仍正，故 $\mathscr J\to-\infty$；趋近右端时，分母至少一因子趋零，分子两因子仍正，故 $\mathscr J\to+\infty$。连续性、严格单调性和介值定理给全实数上的唯一反解。作为该外部源的应用，令反解值匹配式 (C61.2)，便恢复隐藏的 $p_{13}$，继而恢复五律。

这个反解并不声称任意均值、任意 $H_i$ 和任意局部活动都能同时由指定环实现。环的完整源条件仍须满足式 (C60.3)；特别是简单正活动环的 $\mathscr J_i$ 符号已由式 (C60.5) 固定。证毕。

作为同一应用的局部敏感度，C-4.5 的信息系数 $\mathcal I$ 在这里给

$$
\mathcal I=\mathscr J'(\kappa),\qquad
\frac{d\kappa}{d\mathscr J}=\mathcal I^{-1},\qquad
ds^2_{\rm Fisher}=\mathcal I\,d\kappa^2.
$$

C-3.6、C-4.6 的熵与 KL 中间结果也在同一参数对应下适用：令 $\kappa_*=XY/r$，则 $\mathscr J(\kappa_*)=0$，$\frac{d}{d\kappa}H(p(\kappa))=-\mathscr J(\kappa)$，且

$$
H(p_*)-H(p)=\operatorname{KL}(p\Vert p_*)\ge0.
$$

这是独立补全的纤维比较，不把真实有环来源替换为最大熵律。实际环的非零 $\mathscr J_i$ 指定其偏离零耦合点的方向与唯一位置；它不是从可见均值自行产生的额外信息。

## 62. 双切口、两项混合与共同状态

**定义 C-62.1（第二个实际切点）。** 固定 $j\notin\{i-1,i,i+1\}$，令 $T=B_j$。在 $B_i=0$ 的条件律中，写

$$
\pi_c=\mathbb P(T=c\mid B_i=0),\qquad
m_L(c)=\mathbb E(B_L\mid B_i=0,T=c),\quad
m_R(c)=\mathbb E(B_R\mid B_i=0,T=c).
$$

全零配置和只有 $j$ 被占的配置分别说明 $\pi_0,\pi_1>0$。再固定 $T=c$ 后，删去 $i,j$ 留下两条互不相交的路径，各含一个局部端点 $L$ 或 $R$；路径可只有一个顶点。

**命题 C-62.2（允许硬零和退化分量的精确双切口分解）。** 对每个 $c=0,1$，在正概率事件 $(B_i,T)=(0,c)$ 下，两个端点独立。因而有精确分解

$$
Q_i(x,y)=\sum_{c=0}^1\pi_c\,q_L(x\mid c)q_R(y\mid c),
\tag{C62.1}
$$

其中 $q_L,q_R$ 是这一事件下的实际端点边缘。分量允许为确定律。对于当前简单正活动环，表示 $Q_i$ 所需的非负乘积分量最少恰为二。

证明。令删除 $i,j$ 后含 $L,R$ 的顶点集分别为 $U,W$。把所有活动、内部边及连接固定切点的边按其所属侧分组，记为 $F_U(b_U;c)$、$F_W(b_W;c)$。这些因子非负，包含可能为零的排斥指示。条件事件内未归一化的完整权恰为

$$
\lambda_j^c F_U(b_U;c)F_W(b_W;c).
$$

两侧内部变量不相交，且无跨侧边；全部变量求和的分配律给总权

$$
\lambda_j^c Z_U(c)Z_W(c),\qquad
Z_U(c)=\sum_{b_U}F_U(b_U;c),\quad
Z_W(c)=\sum_{b_W}F_W(b_W;c).
$$

两侧全零各贡献一，所以两个 $Z$ 严格正。归一化后完整条件律就是 $[F_U/Z_U][F_W/Z_W]$，进一步对各侧非端点求和得到端点独立。最后按同一个实际 $T$ 的两种值用全概率公式混合，得到式 (C62.1)。

若 $j$ 与 $L$ 相邻且 $c=1$，则 $B_L=0$ 被强制，$q_L(1\mid1)=0$。这不破坏以上证明，因为没有除以这个零概率；另一侧相同。不能要求混合的每个分量都四格全正。

另一方面，式 (C59.3)、(C60.5) 给 $\det Q_i\ne0$。一个乘积分量形成秩一矩阵，行列式为零，故不能单项表示 $Q_i$。式 (C62.1) 已给两个非负乘积分量，最少数因此恰为二。证毕。

这使用 C-19.3 的“共同二态指标—最少乘积项数”中间论证，但此处实际指标是外部路径上的 $B_j$，不是星形模型中新引入的中心。两侧因子、$\pi_c$ 及其数值精度仍要给定；两项分解不意味着整个外部配置、概率参数或全部历史可存于一个比特。求和式也没有把同一个 $T$ 复制为两个独立变量。

Edera、Bromberg、Schlüter 的 *Markov random fields factorization with context-specific independences*，v1 Theorem 1、Auxiliary Lemma 1 和 Theorem 2 都假设原联合分布为正。当前在整个二值笛卡尔空间上有硬零，故这些正性假设不满足；它们不承担命题 C-62.2。上述证明直接处理非负因子与正条件总质量，允许全部所需的硬零。[C-66.3](#66-来源范围与三种读数的共同边界) 给出精确文献定位。

**命题 C-62.3（遗漏共同切点产生的协方差）。** 同一条件律满足

$$
\frac{\Delta_i}{r^2}
=\pi_0\pi_1\bigl(m_L(1)-m_L(0)\bigr)
\bigl(m_R(1)-m_R(0)\bigr).
\tag{C62.2}
$$

证明。命题 C-62.2 使给定 $T$ 的端点条件协方差为零。式 (C62.1) 给

$$
\begin{aligned}
\mathbb E_Q(B_LB_R)&=\pi_0m_L(0)m_R(0)+\pi_1m_L(1)m_R(1),\\
\mathbb E_Q B_L&=\pi_0m_L(0)+\pi_1m_L(1),\\
\mathbb E_Q B_R&=\pi_0m_R(0)+\pi_1m_R(1).
\end{aligned}
$$

相减并用 $\pi_0+\pi_1=1$，恰得右边。左边由式 (C59.3) 识别。由于 $\Delta_i\ne0$ 且两混合权为正，两侧条件均值差在此模型中都非零；它们的乘积符号由环长奇偶性确定。分解中的这些均值及混合权是实参数，共同变量的两种取值不消除参数信息。证毕。

## 63. 条件路径的相关运输与信息界

**定义 C-63.1（条件路径与未来总权）。** 在事件 $B_i=0$ 下，按外部顺序记

$$
(V_0,V_1,\ldots,V_\ell)
=(B_L,B_{r_1},\ldots,B_{r_{n-3}},B_R),\qquad \ell=n-2,
$$

并记对应活动为 $\alpha_0,\ldots,\alpha_\ell$。整个路径的条件律记作 $\nu_i$；其端点边缘才是 $Q_i$。因与中心相接的两条边因子均等于一，$\nu_i$ 精确正比于

$$
\prod_{k=0}^{\ell}\alpha_k^{v_k}
\prod_{k=0}^{\ell-1}J_{v_k,v_{k+1}}.
\tag{C63.1}
$$

对固定 $V_k=s$，令 $R_k(s)$ 为右侧 $k+1,\ldots,\ell$ 的填充总权，不含第 $k$ 位的活动。于是

$$
R_\ell(s)=1,\qquad
R_k(s)=\sum_{t=0}^1J_{s,t}\alpha_{k+1}^tR_{k+1}(t)>0.
\tag{C63.2}
$$

所有协方差、相关系数及条件概率在本章均取自 $\nu_i$，除非明确写回完整环律。

**命题 C-63.2（外部路径的精确相关乘积）。** 条件路径为非齐次一阶 Markov 链，且每个单点边缘非退化。其端点相关系数满足

$$
\operatorname{Corr}_{\nu_i}(V_0,V_\ell)
=\prod_{k=0}^{\ell-1}\operatorname{Corr}_{\nu_i}(V_k,V_{k+1}).
\tag{C63.3}
$$

每条边的相关系数严格负，因此端点相关的符号为 $(-1)^\ell=(-1)^n$。式 (C63.3) 是对当前外部来源的精确恒等式。

证明。对任意有正概率的合法前缀，式 (C63.1) 的前缀权在条件分子、分母中消去，余下

$$
\mathbb P_{\nu_i}(V_{k+1}=t\mid V_0=v_0,\ldots,V_k=s)
=\frac{J_{s,t}\alpha_{k+1}^tR_{k+1}(t)}{R_k(s)}.
\tag{C63.4}
$$

它只依赖最后状态 $s$ 及位置 $k$，其两项和为一；这直接证明 Markov 性。非法前缀概率为零，不给它虚构条件概率。全零路径及仅第 $k$ 位占用的路径都有正权，所以 $\mu_k=\mathbb E_{\nu_i}V_k$ 满足 $0<\mu_k<1$，方差 $s_k^2=\mu_k(1-\mu_k)>0$。

二值条件均值必有唯一仿射形式

$$
\mathbb E_{\nu_i}(V_{k+1}\mid V_k)=a_k+b_kV_k,
\qquad
b_k=\frac{\operatorname{Cov}_{\nu_i}(V_k,V_{k+1})}{s_k^2}.
\tag{C63.5}
$$

第二式来自与 $V_k-\mu_k$ 相乘后取均值。由 Markov 性与条件期望塔式，在每步均有

$$
\operatorname{Cov}_{\nu_i}(V_0,V_{k+1})
=b_k\operatorname{Cov}_{\nu_i}(V_0,V_k).
$$

从 $\operatorname{Cov}(V_0,V_0)=s_0^2$ 起归纳，端点协方差等于 $s_0^2\prod_kb_k$。而

$$
\operatorname{Corr}(V_k,V_{k+1})=b_k\frac{s_k}{s_{k+1}},
$$

连乘时中间标准差消去，得到 $\prod_k\operatorname{Corr}(V_k,V_{k+1})=(s_0/s_\ell)\prod_kb_k$，正是端点协方差除以 $s_0s_\ell$。

最后 $V_kV_{k+1}=0$ 恒成立，所以每条边的协方差为 $-\mu_k\mu_{k+1}<0$。全部标准差为正，边相关也严格负，遂得符号结论。这个推导与 C-8.2 的行列式符号在同一路径上相符；没有对不同来源的最优边界作拼合。证毕。

**命题 C-63.3（只有统一上界的非齐次衰减）。** 若对完整环有

$$
0<\lambda_j\le\Lambda<\infty\quad(j\in V),\qquad
q_\Lambda=\frac{\Lambda}{1+\Lambda}<1,
$$

则

$$
\begin{aligned}
\bigl|\operatorname{Corr}_{Q_i}(B_L,B_R)\bigr|
&\le q_\Lambda^{n-2},\\
|\Delta_i|&\le\frac{(1-Z)^2}{4}q_\Lambda^{n-2}.
\end{aligned}
\tag{C63.6}
$$

该界不要求活动有统一正下界，并覆盖外部路径的两条边界边。

证明。固定一个边 $k,k+1$。由式 (C63.4)，

$$
\mathbb P(V_{k+1}=1\mid V_k=0)
=\frac{\alpha_{k+1}R_{k+1}(1)}
{R_{k+1}(0)+\alpha_{k+1}R_{k+1}(1)}.
\tag{C63.7}
$$

若 $k+1<\ell$，固定 $V_{k+1}=1$ 强制下一位为零，允许的后缀集合是固定 $V_{k+1}=0$ 所允许集合的子集，且各后缀权相同。因此 $0<R_{k+1}(1)\le R_{k+1}(0)$。若 $k+1=\ell$，两者均为一，仍成立。于是式 (C63.7) 不超过 $\alpha_{k+1}/(1+\alpha_{k+1})\le q_\Lambda$。

从左侧定义同样的过去总权，完全相同的子集论证给反向条件概率

$$
\mathbb P(V_k=1\mid V_{k+1}=0)\le\frac{\alpha_k}{1+\alpha_k}\le q_\Lambda.
$$

没有依赖某一边必须远离端点；终端空后缀总权一已包含端点情形。

对这条排斥边，$\mathbb P(11)=0$，所以

$$
\begin{aligned}
\bigl|\operatorname{Corr}(V_k,V_{k+1})\bigr|^2
&=\frac{\mu_k\mu_{k+1}}{(1-\mu_k)(1-\mu_{k+1})}\\
&=\mathbb P(V_{k+1}=1\mid V_k=0)
\mathbb P(V_k=1\mid V_{k+1}=0)
\le q_\Lambda^2.
\end{aligned}
\tag{C63.8}
$$

式 (C63.3) 给相关系数界。再由二值方差不超过 $1/4$，有 $s_0s_\ell\le1/4$，并由式 (C59.3) 得

$$
|\Delta_i|=r^2\bigl|\operatorname{Cov}_{Q_i}(B_L,B_R)\bigr|
=r^2s_0s_\ell\bigl|\operatorname{Corr}_{Q_i}(B_L,B_R)\bigr|,
$$

从而得到第二界。所有步骤只用活动的上界和逐点严格正性；当某些活动趋零时，界保持一致，但极限上的相关系数仍须另查方差是否为零。证毕。

这个 $q_\Lambda$ 是上述有限路径的直接估计。Sinclair–Srivastava–Yin v2 的强空间混合定理需要统一活动及连接常数阈值，不供应式 (C63.6)。本界也不宣称是齐次模型的最优谱速率。

**定义 C-63.4（事件条件下的信息量）。** 以 $Q=Q_i$，$Q_L,Q_R$ 为其两个边缘，定义

$$
I_Q=\sum_{x,y=0}^1Q(x,y)
\log\frac{Q(x,y)}{Q_L(x)Q_R(y)}
=\operatorname{KL}(Q\Vert Q_L\otimes Q_R).
\tag{C63.9}
$$

这是先条件化于事件 $B_i=0$ 后的互信息，单位由自然对数规定。它不同于按随机变量 $B_i$ 的全部取值平均的条件互信息。

**命题 C-63.5（外部依赖的事件信息界及完整条件互信息）。** 在命题 C-63.3 的假设下，

$$
0<I_Q\le\bigl|\operatorname{Corr}_{Q}(B_L,B_R)\bigr|^2
\le q_\Lambda^{2(n-2)}.
\tag{C63.10}
$$

而在完整环律中，

$$
I(B_L;B_R\mid B_i)=(1-Z)I_Q
\le(1-Z)q_\Lambda^{2(n-2)}.
\tag{C63.11}
$$

证明。置 $P=Q_L\otimes Q_R$。$Q$ 四格全正，所以 $P$ 也全正。对每格使用 $\log t\le t-1$，得

$$
\operatorname{KL}(Q\Vert P)
\le\sum_{x,y}\frac{Q(x,y)^2}{P(x,y)}-1
=\sum_{x,y}\frac{(Q(x,y)-P(x,y))^2}{P(x,y)}
=\chi^2(Q\Vert P).
\tag{C63.12}
$$

最后等式只用 $\sum Q=\sum P=1$。这个有限 KL 估计与 C-3.6 所用对数不等式同属经典中间方法；其在本二元表上的值可以完整算出。记 $a=Q_L(1)$、$b=Q_R(1)$、$\delta=\operatorname{Cov}_Q(B_L,B_R)$。C-8.7 的同边缘差表给

$$
Q-P=\delta\begin{pmatrix}1&-1\\-1&1\end{pmatrix},
$$

故

$$
\begin{aligned}
\chi^2(Q\Vert P)
&=\delta^2\left(\frac1a+\frac1{1-a}\right)
\left(\frac1b+\frac1{1-b}\right)\\
&=\frac{\delta^2}{a(1-a)b(1-b)}
=\bigl|\operatorname{Corr}_Q(B_L,B_R)\bigr|^2.
\end{aligned}
$$

命题 C-63.3 给最后的衰减界。KL 非负及其等号条件可由同一个对数不等式作用于 $P/Q$ 得出；等号要求 $Q=P$。当前 $\det Q\ne0$，所以 $Q\ne P$ 且 $I_Q>0$。

当 $B_i=1$，两个相邻端点均确定为零，其互信息为零。条件互信息按两个中心事件的实际概率平均，$\mathbb P(B_i=0)=r=1-Z$，立即得到式 (C63.11)。证毕。

同一应用还保留 C-8.7 的精确端点近似意义：

$$
\operatorname{TV}(Q,Q_L\otimes Q_R)
=\frac{2|\Delta_i|}{r^2}\le\frac12q_\Lambda^{n-2}.
$$

这些界控制当前指定的端点表及其有界函数。每个有限正活动长度仍有 $\Delta_i\ne0$、$I_Q>0$；小误差不等于精确独立，也不自动控制额外稀有事件条件化后的误差或整个外部配置的重建。

## 64. 边界块组合与连通图中的精确抵消

**定义 C-64.1（一般两端响应的计权约定）。** 对有两个不同标记端点 $L,R$ 的有限图块，给内部顶点正活动、每条边排斥因子 $J$。定义 $H(x,y)$ 为固定端点 $(x,y)$ 后，对内部配置的活动乘积与全部边因子求和。这个响应不包含端点活动。内部活动、边及固定端点在组合时均须代表同一个实际对象；一个因子不能在两个块中重复计入。

**命题 C-64.2（窗口外部块的串联与并联消费）。** 若两块串联，仅共享一个顶点 $s$，其活动为 $d>0$，两块各自都把 $s$ 当端点并排除其活动，且两侧无其他共有顶点、跨块边或共同因子，则合并响应为

$$
H_{\rm series}=H_1\operatorname{diag}(1,d)H_2,
\qquad
\det H_{\rm series}=d\,\det H_1\det H_2.
\tag{C64.1}
$$

若两块并联，仅共享两个端点 $L,R$，内部顶点不交、边集合不重叠，且没有连接两块内部的额外边，则

$$
H_{\rm parallel}=H_1\odot H_2,
\tag{C64.2}
$$

其中 $\odot$ 是逐格乘积。若两块四格全正，则

$$
\Omega(H_{\rm parallel})=\Omega(H_1)\Omega(H_2),\qquad
\mathscr J(H_{\rm parallel})=\mathscr J(H_1)+\mathscr J(H_2).
\tag{C64.3}
$$

这些响应可在式 (C60.3) 中替代外部路径，前提是另加的局部中位只与 $L,R$ 相邻、活动只计一次。

证明。串联时固定两外端，先固定实际共享状态 $s\in\{0,1\}$。给定 $s$ 后内部变量分成两组，有限和分解为 $H_1(x,s)H_2(s,y)$。共享活动未在任何块中出现，应在求和时乘 $d^s$ 恰一次，故总和为 $\sum_sH_1(x,s)d^sH_2(s,y)$，即式 (C64.1)。行列式乘法给第二式；若两块都是路径，边数相加，原路径奇偶符号保持。

并联时两个端点已固定，没有待求和的共享指标。内部两组独立求和，完整填充总权为两个总权相乘，即式 (C64.2)。外端活动都未计入，后续接到局部三位时再计一次。对四格相乘所得交叉比，逐项分组得到式 (C64.3)。最后局部五项的证明仍是固定 $(x,z,y)$ 后对外部求和，故式 (C60.3) 原样成立。证毕。

式 (C64.1) 消费 C-8.2 的同源串接，式 (C64.2) 则是另一个消元布局。并联不是矩阵乘法，不能把串联的行列式乘法或单路径奇偶结论搬到并联图。若两块有共同内部变量，必须对它共同求和；若有额外跨边，乘积缺失了该因子；若重复端点活动，则权重改变。这些都不满足本命题的图条件。

**命题 C-64.3（正活动的两条外路可精确抵消四角项）。** 在同一对端点间取两条内部不交的路径：短路 $L,A,R$，内部活动 $a>0$；长路 $L,B,D,R$，内部活动分别为 $b,c>0$。它们的响应为

$$
H_{\rm short}=JD(a)J=\begin{pmatrix}1+a&1\\1&1\end{pmatrix},
\qquad
H_{\rm long}=JD(b)JD(c)J
=\begin{pmatrix}1+b+c&1+b\\1+c&1\end{pmatrix}.
\tag{C64.4}
$$

两路各自有非零、符号相反的对数四角项；取

$$
a=\frac{bc}{1+b+c}>0
\tag{C64.5}
$$

时，其并联响应的 $\Omega$ 精确等于一。再加局部路径 $L,C,R$，所得六顶点图连通且全部活动可严格正，而该局部窗口的底面残差为零。

证明。按内部状态枚举或直接用 $J,D$ 相乘，得到式 (C64.4)。例如长路的 10 格强制 $B=0$，只剩 $D$ 可选，权为 $1+c$；01 格为 $1+b$，所以矩阵的方向与左右端点一致。其四角比分别为

$$
\Omega(H_{\rm short})=1+a>1,\qquad
\Omega(H_{\rm long})=\frac{1+b+c}{(1+b)(1+c)}<1,
$$

第二个严格不等式来自分母比分子多 $bc>0$。由式 (C64.3)，并联的比值为一恰当且仅当

$$
(1+a)(1+b+c)=(1+b)(1+c)=1+b+c+bc,
$$

亦即式 (C64.5)。两条路径均存在且内部不交，因此外部图连通；加局部中位也保持连通。并联响应四格正且行列式零，再用命题 C-64.2 对局部五律的应用，得到 $\Delta=\lambda_L\lambda_R\det H/\mathcal Z^2=0$。证毕。

**命题 C-64.4（六顶点抵消的完整五律）。** 在命题 C-64.3 中取 $a=1/3$、$b=c=1$，三个局部活动 $\lambda_L=\lambda_C=\lambda_R=1$。顶点集为 $\{L,C,R,A,B,D\}$，边恰为

$$
\{LC,CR,LA,AR,LB,BD,DR\}.
$$

这个连通正活动来源有

$$
H=\begin{pmatrix}4&2\\2&1\end{pmatrix},\quad
\mathcal Z=13,\quad p=\frac{(4,2,4,2,1)}{13},\quad
\Delta=0,
\tag{C64.6}
$$

而条件端点律 $Q$ 是两个参数 $1/3$ 的 Bernoulli 律的乘积。

证明。短路响应为 $\left(\begin{smallmatrix}4/3&1\\1&1\end{smallmatrix}\right)$，长路为 $\left(\begin{smallmatrix}3&2\\2&1\end{smallmatrix}\right)$，逐格相乘得显示的 $H$。完整局部五项为 $(H_{00},H_{10},H_{00},H_{01},H_{11})=(4,2,4,2,1)$，逐模式加和得 $13$；由填充求和证明，它就是全图的配分总权。底面交叉乘积差为 $(4\cdot1-2\cdot2)/13^2=0$，底面质量为 $9/13$，所以

$$
Q=\frac19\begin{pmatrix}4&2\\2&1\end{pmatrix}
=\begin{pmatrix}2/3\\1/3\end{pmatrix}
\begin{pmatrix}2/3&1/3\end{pmatrix}.
$$

外部的两条实际路径均保留，所有活动为正，图的边集合明确连通。因此零残差不能推出没有外部连接。无条件端点协方差仍为 $Z\kappa=4/169>0$，也不能把底面独立改说成完整端点独立。证毕。

这里的抵消是两个正概率响应的对数四角项相加为零；每个配置权都非负。单路径的严格残差与这个多路径的零残差具有不同的图假设。

## 65. 均匀环、Fibonacci 响应与常活动谱

**命题 C-65.1（均匀来源在外部五律中的闭式）。** 取全部 $\lambda_j=1$，以 $F_0=0,F_1=1,F_{k+2}=F_{k+1}+F_k$ 定义 Fibonacci 数，并置 $L_n=F_{n-1}+F_{n+1}$。对每个 $n\ge5$，

$$
H_i=J^{n-2}
=\begin{pmatrix}F_{n-1}&F_{n-2}\\F_{n-2}&F_{n-3}\end{pmatrix},
\qquad\mathcal Z=L_n,
\tag{C65.1}
$$

所以

$$
p^{(i)}=\frac{(F_{n-1},F_{n-2},F_{n-1},F_{n-2},F_{n-3})}{L_n},
\qquad
\Delta_i=\frac{(-1)^n}{L_n^2},
\tag{C65.2}
$$

且

$$
\Omega_i=\frac{F_{n-1}F_{n-3}}{F_{n-2}^2}.
\tag{C65.3}
$$

证明。C-8.3 的等权路径矩阵以路径顶点数 $N=n-1$ 代入，给式 (C65.1) 的矩阵；这个代入具有 $N-1=n-2$ 条边，正是外部路径，不能误用完整环的 $n$ 条边。式 (C60.3) 得五项，其和为

$$
2F_{n-1}+2F_{n-2}+F_{n-3}
=F_{n-1}+F_{n+1}=L_n.
$$

这里使用两次 Fibonacci 递推。也可在同一来源上使用 C-26.11 的迹，$\mathcal Z=\operatorname{tr}(J^n)=F_{n+1}+F_{n-1}$。式 (C60.5) 给残差，式 (C61.2) 给四角比。全部所用 Fibonacci、Lucas 及矩阵幂都是既有中间公式，当前结论是它们在外部窗口五律中的明确参数对应。证毕。

例如 $n=5$ 时，$H_i=\left(\begin{smallmatrix}3&2\\2&1\end{smallmatrix}\right)$，$p=(3,2,3,2,1)/11$，$\Delta=-1/121$、$\Omega=3/4$；$n=6$ 时，$H_i=\left(\begin{smallmatrix}5&3\\3&2\end{smallmatrix}\right)$，$p=(5,3,5,3,2)/18$，$\Delta=1/324$、$\Omega=10/9$。这两组直接代入式 (C65.1)–(C65.3)，分别展示两种严格符号。

**命题 C-65.2（常活动环的完整谱分母）。** 若全部活动为同一个 $\lambda>0$，置

$$
T=JD(\lambda)=\begin{pmatrix}1&\lambda\\1&0\end{pmatrix},\qquad
r_\pm=\frac{1\pm\sqrt{1+4\lambda}}2.
$$

则同一来源的配分总权和窗口残差为

$$
\mathcal Z=\operatorname{tr}(T^n)=r_+^n+r_-^n,\qquad
\Delta_i=\frac{(-1)^n\lambda^{n-1}}{(r_+^n+r_-^n)^2},
\qquad\frac{p_2}{p_0}=\lambda.
\tag{C65.4}
$$

单位活动时 $r_+=\varphi=(1+\sqrt5)/2$、$r_-=-\varphi^{-1}$，还原命题 C-65.1。

证明。C-26.11、C-26.12 已给同源迹与谱公式。为确定此处的全部计权，展开

$$
\operatorname{tr}(T^n)
=\sum_{b_0,\ldots,b_{n-1}}\prod_{j=0}^{n-1}T_{b_{j-1},b_j},
\qquad b_{-1}=b_{n-1}.
$$

每项等于 $\lambda^{\sum_jb_j}\prod_jJ_{b_{j-1},b_j}$，所以合法环配置各出现一次；这保留标号，不除以 $n$。$T$ 的特征多项式为 $t^2-t-\lambda$，两个实根不同，因此可对角化，幂的迹就是两根幂之和。将此分母及 $\prod_{j\ne i}\lambda_j=\lambda^{n-1}$ 代入式 (C60.5)，得到完整残差。活动比由式 (C60.3) 得出。最后代入 $\lambda=1$，两根成为显示的黄金比例值。证毕。

设 $\rho_\lambda=|r_-|/r_+<1$，则 $\mathcal Z=r_+^n[1+(-\rho_\lambda)^n]$。对固定有限 $\lambda$，第二项相对第一项随 $n$ 衰减；当 $\lambda\to\infty$，$\rho_\lambda\to1$，这个结论不是关于无界活动的统一估计。这里 $\rho_\lambda$ 是常活动谱比，命题 C-63.3 的 $q_\Lambda=\Lambda/(1+\Lambda)$ 是另一个路径上界，二者不混用。非齐次活动必须保留 $\prod_jJD_j$ 的有序乘积，不能用一对共同特征根或一组普通 Fibonacci 数替代。

## 66. 来源范围与三种读数的共同边界

**命题 C-66.1（来源模型内的完整活动恢复及其边界）。** 对已知带标号环 $n\ge5$ 的正乘积活动来源，全部中心的五律给出

$$
\lambda_i=\frac{p_2^{(i)}}{p_0^{(i)}},\qquad
\frac{p_2^{(i)}}{p_0^{(i)}}
\left(p_0^{(i)}p_{13}^{(i)}-p_1^{(i)}p_3^{(i)}\right)
=\frac{(-1)^n\prod_j\lambda_j}{\mathcal Z^2}.
\tag{C66.1}
$$

因此，在这个已经指定的源族内，全部精确比值唯一确定活动，进而唯一确定完整环律。后一个式子是同一律的跨窗口校准恒等式，不是任意局部表列表来自该乘积活动源族的充分条件。

证明。式 (C60.3) 中 $p_0>0$，并且 $p_2=\lambda_ip_0$，故恢复公式无除零问题。每个位置都可作为中心，所以全部活动被唯一恢复；定义 (C59.1) 对这些参数给唯一有限总权和唯一概率律。第二式就是式 (C60.6) 的概率坐标表达。

若只给候选五律，可先从比值构造唯一候选活动，但还须用该活动构造完整律并核对全部窗口是否真的等于所给表；只核对比值或共同残差并不完成这个核对。一个全正的具体例子是在六环的每个中心都报告

$$
p=\frac{(1,1,4,1,3)}{10},\qquad
X=Y=Z=\frac25,\quad \frac{p_2}{p_0}=4,\quad
\Delta=\frac1{50},\quad\frac{p_2}{p_0}\Delta=\frac2{25}.
$$

这份列表的单位置及相邻边边缘一致，且每窗校准值相同、符号为正。然而若它来自正乘积活动六环，恢复式强制每个活动都为四。该环的独立集数按占位数为 $1,6,9,2$：非相邻对有 $\binom62-6=9$ 个，三占位只有两个交替配置。因此其配分总权为 $1+6\cdot4+9\cdot4^2+2\cdot4^3=297$，式 (C60.5) 强制残差为 $4^5/297^2=1024/88209\ne1/50$，矛盾。这个例子只排除指定乘积源族，不据此排除全部相关来源。

C-26.8 另外区分局部相容与任意共同来源的存在性，模型内的单射性不扩大那个存在性结论。跨位置共同值在一次给定律上恒定，并未规定随活动变化的动力学守恒量。证毕。

**命题 C-66.2（去掉来源条件的两个具体失败方式）。** 固定总占位会破坏本章的活动比和路径符号结论；对一般共同来源，即使所有三位窗口完全相同，也未必决定全局律。

证明。第一种情形取六环、所有活动一，再条件化于总占位恰为一。六个单点配置等概率，对每个中心的窗口有

$$
p=\frac{(3,1,1,1,0)}6,\qquad
\frac{p_2}{p_0}=\frac13\ne1,\qquad
\Delta=-\frac1{36}<0.
$$

空窗口来自窗口外三个单点；另外三个局部单点各一项，两端共同占位不允许。这个总数条件不是定义 C-59.2 的来源，故其偶数环负残差不与命题 C-60.3 矛盾。切开图也没有去掉剩余总占位约束，所以不能再将两侧总权相乘。

第二种情形取九环，只让 $B_0,B_3,B_6$ 可变，其余位固定零。令 $\nu$ 在这三位上为三个独立公平位的律；令 $\eta$ 在四个偶校验词 $000,011,101,110$ 上均匀。二者都支持合法环配置，而且每个连续三位窗口至多含上述一个可变位置，所以所有窗口边缘相同：该位公平，其余位确定零。但 $\nu$ 对三位奇校验事件赋概率 $1/2$，$\eta$ 赋概率零，完整律不同。

若还要求每个合法环配置都正，取定义 C-59.2 中单位活动的全支持律 $\tau$，固定 $0<\varepsilon<1$，令

$$
\widetilde\nu=(1-\varepsilon)\nu+\varepsilon\tau,\qquad
\widetilde\eta=(1-\varepsilon)\eta+\varepsilon\tau.
$$

二者在每个合法配置上的质量至少为 $\varepsilon\tau(b)>0$，全部三位窗口仍相同，而上述事件概率之差为 $(1-\varepsilon)/2>0$。因此合法支持上的严格正性本身也不能替代乘积活动假设。证毕。

**约定 C-66.3（经典来源及其精确使用范围）。** 下列文献作为已知中间方法使用；版本、对象及条件均随引文给出。当前源特定应用由 C-59–C-66 的普通数学推导承担，不把经典恒等式、同义改写或参数代入作为独立的新内容。

| 文献 | 实际使用范围与条件 |
| --- | --- |
| Alistair Sinclair、Piyush Srivastava、Yitong Yin，*Spatial mixing and approximation algorithms for graphs with bounded connective constant*，[arXiv:1308.1762v2](https://arxiv.org/abs/1308.1762v2)，§1.1、Theorem 1.1 | §1.1 的统一活动硬核独立集权为 $\lambda^{|I|}$。Theorem 1.1 要求连接常数至多 $\Delta$ 且统一活动 $\lambda<\lambda_c(\Delta+1)$。这里只取模型背景；非齐次恒等式及 $q_\Lambda$ 界由 C-60、C-63 的有限源证明给出。 |
| Ferenc Bencs，*Christoffel-Darboux type identities for independence polynomial*，[arXiv:1409.2527v1](https://arxiv.org/abs/1409.2527v1)，Theorem 1.3、Corollary 1.5 | Theorem 1.3 对独立集多项式给含指定两点的诱导连通二分子图求和，项的符号由子图内部距离决定。Corollary 1.5 对二分图及正统一变量给符号结论。Theorem 1.1 是匹配多项式恒等式。该文还明确一般图的最短距离奇偶猜想不成立；本章不援引一般图奇偶法则。 |
| Alejandro Edera、Facundo Bromberg、Federico Schlüter，*Markov random fields factorization with context-specific independences*，[arXiv:1306.2295v1](https://arxiv.org/abs/1306.2295v1)，Theorem 1、Auxiliary Lemma 1、Theorem 2 | 三处均要求正联合分布；Theorem 2 还要求各约化依赖模型 graph-isomorph 及 CSI-map 条件。硬排斥的全二值来源有零概率配置，不满足其正性前提。此文只用于定位适用边界，不承担双切口因子分解。 |
| Nathalie Peyrard、Marie-Josée Cros、Simon de Givry、Alain Franc、Stéphane Robin、Régis Sabbadin、Thomas Schiex、Matthieu Vignes，[arXiv:1506.08544v2](https://arxiv.org/abs/1506.08544v2)，§§2.1–2.2、3.2 | v2 PDF 题名为 *Exact or approximate inference in graphical models: why the choice is dictated by the treewidth, and how variable elimination can be exploited*；摘要页题名为 *Exact and approximate inference in graphical models: variable elimination and beyond*。使用有限因子与分配律消元背景；§2.1 也讨论 Boolean $0/1$ 势。当前非负因子证明允许零，不调用正势反推定理，也不从一般稠密表复杂度推出本两项表示的存储下界。 |
| Mathias Drton、Seth Sullivant，*Algebraic Statistical Models*，[arXiv:math/0703609v1](https://arxiv.org/abs/math/0703609v1)，§3.2 Example 16 | 离散条件独立的交叉乘积等式背景。对应这里底面二元表的行列式零判据；它不单独给活动恢复、路径符号、外部唯一性或衰减界。 |

Bencs Theorem 1.3 的原式使用一个共同变量 $x$，明确为

$$
I(G-u,x)I(G-v,x)-I(G,x)I(G-u-v,x)
=\sum_{H\in\mathcal B_{u,v}}
(-1)^{d_H(u,v)+1}x^{|V(H)|}I(G-N[H],x)^2,
$$

其中 $\mathcal B_{u,v}$ 是包含 $u,v$ 的诱导连通二分子图族，$N[H]$ 是闭邻域。这是独立多项式差的先例定位，不把当前非齐次权强行代入其单变量陈述，也不把不同子图的符号用整个图的一条最短路径替换。

仓内对应关系也逐项限定：C-7.1 的孤立三位正活动律提供局部计权，C-7.3 区分无条件协方差与底面残差，C-7.7–C-7.10 给四角系数及额外排斥边的区别；C-8.2–C-8.3 给路径矩阵与均匀闭式，C-8.7 给同边缘二元表的差；C-19.3 给共同指标与乘积分量的秩论证；C-26.11–C-26.12、C-26.22 给完整闭路迹及同源归一化。C-3.6、C-4.5–C-4.6 的 KL、Fisher 与对数四角坐标用于 C-61 的实际纤维。底面行列式与退化条件表另沿用《行列式、条件拼接与原生守卫接续》推导 4.2–5.2。它们都作为本应用的中间输入，不被重新命名为独立成果。

**约定 C-66.4（全链条与不可省略的条件）。** 当前应用的连接是

$$
\mathbb P_\lambda
\ \longrightarrow\ H_i
\ \longrightarrow\ p^{(i)}
\ \longrightarrow\left(
\frac{p_2^{(i)}}{p_0^{(i)}},\ \Omega_i,\ \lambda_i\Delta_i
\right).
$$

第一箭头对同一外部变量求和；第二箭头接回三个局部活动并用同一 $\mathcal Z$ 归一化。第三箭头的三个读数分别为：中心活动、固定外部的联合四角比、同一完整环律的跨中心校准量。它们的固定参数不同，不能互换“恒定”的含义。

简单环、$n\ge5$、正活动、完整乘积来源及不固定总占位，是 C-60 的严格非零结论和 C-62–C-63 路径论证的共同前提。所有对数和比值只在已证明正的格上使用；$\lambda_j=0$ 的极限可改变秩和支持，不能照用正性结论。三角形的端点直接相邻，101 不在支持中，不能使用这里的全正五律；长度四不在本章所声明范围内。

衰减界另需统一有限上界 $\Lambda$；其概率空间先固定为 $B_i=0$ 的事件条件律，完整条件互信息另乘 $1-Z$。双切口组件允许退化，但条件事件总质量必须正。串联、并联还分别要求 C-64.2 的共有顶点、边集合及计权条件；多路连接可有 C-64.4 的精确抵消。模型内的全活动恢复以精确标号窗口律为输入，不声称任意局部列表可实现，也不从有限样本取得精确人口律。

这些结论限于已声明的有限占位概率源及其数学消元。普通证明承担各全称命题；所列具体配置与有理数实例说明其适用方式和失败边界，不替代全称证明。

## 追加锚（本行以下为增补区）

## 67. 四角关系的规范椭圆与边缘比较

**约定 C-67.1（五态、底面与两种比较）。** 沿用 C-59.4、C-60.2、C-61.3 的同一五模式次序

$$
\Sigma=(0,1,2,3,13)
=\bigl(F[\mathrm{null}],F[1],F[2],F[3],F[1,3]\bigr),
$$

对应占位词 $(000,100,010,001,101)$。设 $p_s>0$ 且 $\sum_s p_s=1$，定义

$$
X=p_1+p_{13},\qquad Y=p_3+p_{13},\qquad Z=p_2,
\qquad r=1-Z,\qquad\kappa=p_{13}.
$$

这里 $Y$ 始终是右端占位均值；经典 Yule's Y 另记作 $\rho_*$，不以同一个字母表示两个对象。已有的概率反演为

$$
p_\kappa=(r-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa).
\tag{C67.1}
$$

底面表的行索引是左端，列索引是右端，各按 $0,1$ 排列：

$$
H=\begin{pmatrix}p_0&p_3\\p_1&p_{13}\end{pmatrix},
\qquad
Q=\frac Hr
=\mathcal L(B_L,B_R\mid B_C=0).
\tag{C67.2}
$$

$H$ 的总质量是 $r$。复用 C-59.4 的四角残差，直接代入亦得

$$
\det H=(r-X-Y+\kappa)\kappa-(X-\kappa)(Y-\kappa)
=r\kappa-XY.
\tag{C67.3}
$$

“正矩阵”在以下各章只指四个元素严格正，不指对称或正定；$H$ 本身不是协方差矩阵。

对任意这样的矩阵 $H=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)$，另行声明比较规则

$$
H\sim\widetilde H
\quad\Longleftrightarrow\quad
\widetilde H=D_LHD_R,
\qquad D_L,D_R\text{ 为正对角矩阵}.
\tag{C67.4}
$$

允许总质量变化；若要概率表，可在重加权后再归一化。定义

$$
\Omega(H)=\frac{ad}{bc},\qquad J(H)=\log\Omega(H),
\qquad\eta(H)=\frac18J(H).
\tag{C67.5}
$$

式 (C67.4) 消去两端各自的权重偏好，一般改变边缘，不能作为固定 $(X,Y,Z)$ 纤维内的移动。对 C-60.2 的实际外部响应 $H_i$，局部底面表为

$$
H=\mathcal Z^{-1}\operatorname{diag}(1,\lambda_L)
H_i\operatorname{diag}(1,\lambda_R).
\tag{C67.6}
$$

因此 C-61.2 给出的同一个外部四角比恰是式 (C67.5) 的输入，$J(H)=\mathscr J_i$。这项对应固定外部时成立，不要求局部边缘固定。

**命题 C-67.2（外部四角比的带标记、定面积椭圆表示）。** 对式 (C67.2) 的底面表，或任意四格正的边界响应，先取其正行列等价类中总质量一、两边缘均为 $(1/2,1/2)$ 的代表 $Q_*(H)$，再取这个代表的 $\pm1$ 协方差椭圆并将面积归一化为 $\pi$。所得椭圆在固定标记方向

$$
e_+=\frac1{\sqrt2}(1,1),\qquad
 e_-=\frac1{\sqrt2}(1,-1)
$$

上的半轴分别为 $e^\eta,e^{-\eta}$。以 $z_+,z_-$ 表示这两个方向的坐标，其方程是

$$
e^{-2\eta}z_+^2+e^{2\eta}z_-^2=1.
\tag{C67.7}
$$

这个带标记椭圆完整确定式 (C67.4) 的等价类。对于五态底面，它成为圆当且仅当两端在事件 $B_C=0$ 下条件独立。

证明中的经典中间结果取自 Dirk Hasenclever、Markus Scholz，*Comparing measures of association in 2x2 probability tables*，[arXiv:1302.6161v1](https://arxiv.org/abs/1302.6161v1)，Proposition 1、§3.1 及 Proposition 4：正行列轨道由 odds ratio 分类，轨道有唯一平衡代表，Yule's Y 在该代表上等于 Pearson 相关。以下给出这些中间步骤在本底面表示中的全部参数计算；不另把经典分类或 Yule 公式立为新结论。

首先，若 $D_L=\operatorname{diag}(l_0,l_1)$、$D_R=\operatorname{diag}(r_0,r_1)$，交叉乘积的分子和分母都乘 $l_0l_1r_0r_1$，所以 $\Omega$ 不变。反之，若 $\Omega(\widetilde H)=\Omega(H)$，令

$$
t_{ij}=\frac{\widetilde H_{ij}}{H_{ij}}>0.
$$

交叉比相等给 $t_{00}t_{11}=t_{01}t_{10}$。取

$$
D_L=\operatorname{diag}(t_{00},t_{10}),\qquad
D_R=\operatorname{diag}(1,t_{01}/t_{00}),
$$

则 $D_LHD_R$ 的前三格等于 $\widetilde H$，第四格由该乘法等式也相等。故交叉比相等正好等价于正行列等价。

总质量一且两个边缘均平衡的正表必为

$$
\begin{pmatrix}x&1/2-x\\1/2-x&x\end{pmatrix},\qquad0<x<1/2.
$$

其比值比为 $[x/(1/2-x)]^2$，故唯一解是

$$
x=\frac{\sqrt\Omega}{2(1+\sqrt\Omega)}.
$$

由已证轨道分类，它确在 $H$ 的轨道中。因此

$$
Q_*(H)=\frac14
\begin{pmatrix}1+\rho_*&1-\rho_*\\1-\rho_*&1+\rho_*\end{pmatrix},
\qquad
\rho_*=\frac{\sqrt{ad}-\sqrt{bc}}{\sqrt{ad}+\sqrt{bc}}
=\frac{\sqrt\Omega-1}{\sqrt\Omega+1}
=\tanh\frac J4.
\tag{C67.8}
$$

四格正给 $-1<\rho_*<1$。按 $s_0=1,s_1=-1$ 编码两端，平衡边缘给均值零、方差一；对角格的乘积编码为一，非对角格为负一，故交叉矩为 $\rho_*$。协方差矩阵于是为

$$
\Sigma_*=\begin{pmatrix}1&\rho_*\\\rho_*&1\end{pmatrix}.
$$

它的带标记特征向量为 $e_+,e_-$，相应特征值 $1+\rho_*,1-\rho_*$ 都正。协方差椭圆具体定义为 $\Sigma_*^{1/2}$ 对欧氏单位圆的像，原半轴为 $\sqrt{1+\rho_*}$、$\sqrt{1-\rho_*}$，面积为 $\pi\sqrt{1-\rho_*^2}$。把全部坐标除以 $(1-\rho_*^2)^{1/4}$，面积变为 $\pi$，带标记半轴成为

$$
\left(\frac{1+\rho_*}{1-\rho_*}\right)^{1/4},\qquad
\left(\frac{1-\rho_*}{1+\rho_*}\right)^{1/4}.
$$

由式 (C67.8)，$(1+\rho_*)/(1-\rho_*)=\sqrt\Omega=e^{J/2}$，所以两半轴正是 $e^{J/8},e^{-J/8}$。这证明式 (C67.7)。带标记半轴恢复 $\eta$，继而恢复 $\Omega=e^{8\eta}$ 和整个轨道。

最后，$\eta=0$ 等价于 $ad=bc$，即正表秩一。正表秩一时可写为两个正向量的外积，归一化后是两个概率向量的外积；反过来独立概率表显然秩一。用于 $Q=H/r$，这正是底面条件独立。结合式 (C67.3)，

$$
\operatorname{sgn}\eta=\operatorname{sgn}(\det H)
=\operatorname{sgn}(r\kappa-XY).
$$

正号表示沿 $e_+$ 伸长，负号表示沿 $e_-$ 伸长。若允许旋转并忘掉方向标记，$\eta$ 与 $-\eta$ 给同一个无标记形状，只剩轴比 $e^{2|\eta|}$，不能再区分两种关联符号。证毕。

**命题 C-67.3（Yule、条件 Pearson 与无条件 Pearson 的具体区分）。** 式 (C67.8) 的 $\rho_*$ 是 Yule's Y；Yule's Q 则为

$$
Q_{\rm Yule}=\frac{\Omega-1}{\Omega+1}=\tanh\frac J2.
\tag{C67.9}
$$

对任意正表归一化得到的二元律，Pearson 系数是

$$
\operatorname{Corr}(B_L,B_R)
=\frac{ad-bc}{\sqrt{(a+b)(c+d)(a+c)(b+d)}}.
\tag{C67.10}
$$

它在平衡代表 $Q_*(H)$ 上等于 $\rho_*$，一般表上则不同；“在平衡代表上相等”不表示“只有平衡代表才能相等”。此外，五态律的底面条件 Pearson 和全五态的无条件 Pearson 也不同。

证明。式 (C67.9) 是上述 Hasenclever–Scholz §3.1 的经典命名，代入 $\Omega=e^J$ 即给双曲正切式。令 $T=a+b+c+d$，二元律的两个占位均值为 $(c+d)/T$、$(b+d)/T$，交叉矩为 $d/T$。其协方差是 $(ad-bc)/T^2$，两个方差的乘积是 $(a+b)(c+d)(a+c)(b+d)/T^4$，所以式 (C67.10) 成立。将式 (C67.8) 代入即得 $\rho_*$。

具体取偏置表

$$
Q_{\rm bias}=\frac1{16}\begin{pmatrix}9&1\\3&3\end{pmatrix}.
$$

它的两个占位均值为 $3/8,1/4$，协方差为 $3/32$，方差分别为 $15/64,3/16$，故

$$
\Omega=9,\qquad\rho_*=\frac12,\qquad
\operatorname{Corr}_{Q_{\rm bias}}(B_L,B_R)
=\frac{24}{\sqrt{10\cdot6\cdot12\cdot4}}
=\frac1{\sqrt5}\ne\frac12.
\tag{C67.11}
$$

此表可作为任意 $0<Z<1$ 下底面质量 $r=1-Z$ 的条件律，故确属当前五态模型的可用实例。另一方面，取

$$
Q_{\rm ind}=\frac1{15}\begin{pmatrix}2&3\\4&6\end{pmatrix}
=\begin{pmatrix}1/3\\2/3\end{pmatrix}
\begin{pmatrix}2/5&3/5\end{pmatrix}.
$$

两边缘均不平衡，但 $ad=bc$，所以 $\rho_*=0$ 且 Pearson 也为零。这已排除上述“只有”读法。

最后取五态均匀律 $p_s=1/5$。此时 $r=4/5$、$X=Y=2/5$、$\kappa=1/5$，底面条件表四格均为 $1/4$，所以 $\eta=\rho_*=0$ 且条件 Pearson 为零。全五态律中 $B_LB_R$ 的均值是 $1/5$，协方差为 $1/5-4/25=1/25$，两个方差均为 $6/25$，无条件 Pearson 因而为 $1/6$。这就是 C-59.4 的 $\kappa-XY=\Delta+Z\kappa$ 与 $\Delta/r^2$ 的实际区别。证毕。

## 68. 反向圆周、固定纤维与黄金参数

**命题 C-68.1（四角椭圆的两个反向圆周分量）。** 在命题 C-67.2 的标记主轴平面中，以复数表示坐标 $z=z_++iz_-$。同一规范椭圆有参数式

$$
z(t)=e^\eta\cos t+i e^{-\eta}\sin t
=\cosh\eta\,e^{it}+\sinh\eta\,e^{-it},
\qquad t\in\mathbb R/2\pi\mathbb Z.
\tag{C68.1}
$$

两个圆周分量具有相同频率、相反旋向，椭圆面积恒为 $\pi$。这个几何参数 $t$ 不是五态振幅的相位坐标。

证明。展开右边，其实部系数是 $\cosh\eta+\sinh\eta=e^\eta$，虚部系数是 $\cosh\eta-\sinh\eta=e^{-\eta}$，所以等于左边。若 $\eta<0$，第二个实系数为负，可写成 $|\sinh\eta|e^{-it+i\pi}$；这只是该圆周分量多一个 $\pi$ 相位。若 $\eta=0$，第二分量为零，第一分量为单位圆。椭圆的两半轴之积为

$$
(\cosh\eta+\sinh\eta)(\cosh\eta-\sinh\eta)
=\cosh^2\eta-\sinh^2\eta=1,
$$

故面积为 $\pi$。这里输入只有四角比和选择的平面标记，既没有指定五个复振幅，也没有把此处的两个圆周分量认作两个概率事件。证毕。

**命题 C-68.2（固定可见纤维上的椭圆反演）。** 固定

$$
0<Z<1,\qquad r=1-Z,\qquad0<X<r,\quad0<Y<r.
$$

则五态全正的充要区间为

$$
\kappa_-<\kappa<\kappa_+,\qquad
\kappa_-=max(0,X+Y-r),\quad\kappa_+=\min(X,Y).
\tag{C68.2}
$$

在这个开区间上，带符号椭圆参数

$$
\eta(\kappa)=\frac18\log
\frac{(r-X-Y+\kappa)\kappa}{(X-\kappa)(Y-\kappa)}
\tag{C68.3}
$$

是到 $\mathbb R$ 的严格递增光滑双射，且

$$
\frac{d\eta}{d\kappa}=\frac{\mathcal I(\kappa)}8>0,
\qquad
\mathcal I(\kappa)=\frac1{p_0}+\frac1{p_1}
+\frac1{p_3}+\frac1{p_{13}}.
\tag{C68.4}
$$

因此，已知 $(X,Y,Z)$ 和带标记椭圆即可恢复全部五概率；没有给定可见均值时，一个椭圆不能恢复五律。

证明。这是 C-61.3 的完整纤维及四角坐标在 $J=8\eta$ 下的应用。由式 (C67.1)，四底角正恰要求 $\kappa>0$、$\kappa>X+Y-r$、$\kappa<X$、$\kappa<Y$，即式 (C68.2)。因为 $X,Y<r$，有 $X+Y-r<X,Y$，再用 $X,Y>0$ 得开区间非空。

沿该纤维，四底角导数依次为 $1,-1,-1,1$。逐项对式 (C68.3) 求导，两个分母项的负号与概率导数的负号抵消，得到式 (C68.4)。趋近下端时，$p_0p_{13}\to0$，而 $p_1,p_3$ 各有正极限：若 $\kappa_-=0$，二者极限为 $X,Y$；若 $\kappa_-=X+Y-r$，极限为 $r-Y,r-X$。故 $\eta\to-\infty$，包括 $X+Y=r$ 时两个分子同时趋零的情形。趋近上端时，$p_1p_3\to0$，而 $p_{13}>0$、$p_0$ 的极限为 $r-\max(X,Y)>0$，所以 $\eta\to+\infty$，包括 $X=Y$ 的双零分母情形。连续性、严格单调性和介值定理给双射，导数非零给光滑局部反演，故反函数在全实轴上光滑。

由反解 $\kappa$ 代回式 (C67.1) 恢复五律。若不固定可见均值，正行列重加权可改变底面边缘而保留同一个 $\eta$；还可改变底面总质量 $r$，同时补中位概率 $Z=1-r$。这两种变化均不由椭圆决定。对实际正活动环，反解后仍须满足 C-60.2 的来源关系；抽象纤维的双射没有断言任意外部矩阵和任意均值可由同一个指定环同时实现。证毕。

**命题 C-68.3（单位剪切与规范椭圆的黄金参数对应）。** 令 $\varphi=(1+\sqrt5)/2$。单位剪切

$$
T=\begin{pmatrix}1&1\\0&1\end{pmatrix}
$$

把欧氏单位圆映为半轴 $\varphi,\varphi^{-1}$ 的椭圆。将其长轴对应到规范椭圆的 $e_+$ 标记时，该形状对应

$$
\eta=\log\varphi,\qquad
\rho_*=\frac{\sqrt5}{3},\qquad\Omega=\varphi^8.
\tag{C68.5}
$$

证明。线性像的半轴是奇异值。$T^{\mathsf T}T=\left(\begin{smallmatrix}1&1\\1&2\end{smallmatrix}\right)$ 的特征多项式是 $u^2-3u+1$，两个根为 $(3\pm\sqrt5)/2=\varphi^{\pm2}$。平方根给 $\varphi,\varphi^{-1}$；行列式一也给像的面积 $\pi$。这是一个局部欧氏计算，不需要额外格点或概率来源。

用式 (C67.7) 对应 $e^\eta=\varphi$，得到 $\eta=\log\varphi$、$\Omega=e^{8\eta}$。又由 $\varphi-\varphi^{-1}=1$ 和 $\varphi+\varphi^{-1}=\sqrt5$，有

$$
\varphi^2-\varphi^{-2}=\sqrt5,\qquad
\varphi^2+\varphi^{-2}=3.
$$

所以 $\rho_*=\tanh(2\log\varphi)=(\varphi^2-\varphi^{-2})/(\varphi^2+\varphi^{-2})=\sqrt5/3$。反之用这个 $\rho_*$ 构造式 (C67.8) 的平衡表，再任选 $0<r<1$，取底面质量 $rQ_*$、中位质量 $1-r$，即有全正五律实现此形状。

若把长轴对应到 $e_-$，则应取负的 $\eta$、负的 $\rho_*$ 和倒数 $\Omega$；无标记形状本身不选择符号。这个对应只说某一种四角关联具有黄金半轴，不说任意 FIB 五律必有该值，也不把剪切的坐标基、概率端点标签与某个格点来源自动识别。证毕。

## 69. 有限边界权的拼接与并联椭圆

**定义 C-69.1（含条件填充的有限响应）。** 取两个不同的二元端点 $a,b\in\{0,1\}$ 和一组有限内部变量 $u\in\mathcal U$。给定非负权 $f(a,u,b)$，它可以是活动与兼容因子的乘积，允许某些内部配置权为零。定义

$$
H_f(a,b)=\sum_{u\in\mathcal U}f(a,u,b).
\tag{C69.1}
$$

以下要求四个条件总权均严格正，而非要求每个内部配置都正。外端活动先从 $f$ 中取出；要形成完整权时，分别乘一次 $\alpha_a>0$、$\gamma_b>0$。C-60.1 的 $H_i$ 和 C-64.1 的两端图块都是此定义的实际实例。C-60.2 证明外部路径任意端点条件下都有全零内部填充，因而满足四格正。

并联时，两个块只共享外端，内部变量集合不交，条件于端点后的允许集合是 $\mathcal U_1\times\mathcal U_2$，完整内部权精确为 $f_1(a,u,b)f_2(a,v,b)$。这个条件排除了内部跨块耦合因子、额外共同内部变量和共同总量约束。串联时，两块仅共享一个二元接缝 $c$，各自内部集合不交；接缝的完整活动 $w_c>0$ 未计入任一块，固定 $c$ 后内部权精确为 $f_1(a,u,c)f_2(c,v,b)$。两种拼接都要求因子和变量来自同一实际对象。

**命题 C-69.2（一次计权的拼接在椭圆坐标中的应用）。** 在定义 C-69.1 的条件下，不含外端活动的响应分别为

$$
H_\parallel=H_1\odot H_2,\qquad
H_{\rm series}=H_1WH_2,
\qquad W=\operatorname{diag}(w_0,w_1).
\tag{C69.2}
$$

其中 $\odot$ 表示逐格乘积。对于并联，规范椭圆的参数满足

$$
J_\parallel=J_1+J_2,\qquad
\eta_\parallel=\eta_1+\eta_2,\qquad
\rho_{*,\parallel}=\frac{\rho_{*,1}+\rho_{*,2}}
{1+\rho_{*,1}\rho_{*,2}}.
\tag{C69.3}
$$

若使用同一对标记方向，面积保持伸缩

$$
S_\eta=\begin{pmatrix}e^\eta&0\\0&e^{-\eta}\end{pmatrix}
$$

满足 $S_{\eta_1}S_{\eta_2}=S_{\eta_1+\eta_2}$，给并联与几何伸缩复合的对应。

证明。C-64.2 已给同源图块的两种消元式；这里把其有限和及计权条件写到一般条件填充上。固定 $a,b$，并联的总权为

$$
\sum_{u\in\mathcal U_1}\sum_{v\in\mathcal U_2}
 f_1(a,u,b)f_2(a,v,b)
=\left(\sum_u f_1(a,u,b)\right)
 \left(\sum_v f_2(a,v,b)\right).
$$

这由有限和的分配律给出式 (C69.2) 第一式。归一化后，完整内部条件律为

$$
\frac{f_1(a,u,b)f_2(a,v,b)}{H_1(a,b)H_2(a,b)}
=\frac{f_1(a,u,b)}{H_1(a,b)}
 \frac{f_2(a,v,b)}{H_2(a,b)}.
$$

所以两块内部确在同一个端点条件下独立；它们无条件时可以通过共享端点相关。若有额外因子 $g(u,v)$，总权中须保留它，上面的分配律一般不再产生两个总权的乘积。

串联先对同一个接缝取值 $c$ 分组，固定外端后总权恰为

$$
\begin{aligned}
\sum_{c=0}^1\sum_u\sum_v
 f_1(a,u,c)w_cf_2(c,v,b)
&=\sum_{c=0}^1H_1(a,c)w_cH_2(c,b)\\
&=(H_1WH_2)_{ab}.
\end{aligned}
$$

接缝状态只求和一次，活动只乘一次。这不是两个独立接缝状态的求和。若取图块活动约定 $w_0=1,w_1=d$，即还原 C-64.2 的 $\operatorname{diag}(1,d)$。外端的完整活动在上述两式之外统一乘 $\alpha_a\gamma_b$，所以完整响应为 $D_\alpha H_{\rm composite}D_\gamma$；把同一个外端活动同时装入两块再相乘会多计一次，给不同的权。若某端活动已经存在于一块，应在另一块中排除，或先明确分配两个因子使其乘积恰为该活动。四个条件总权正使两个合成响应仍四格正。

现在逐格乘法给

$$
\Omega(H_1\odot H_2)
=\frac{(a_1a_2)(d_1d_2)}{(b_1b_2)(c_1c_2)}
=\Omega(H_1)\Omega(H_2).
$$

取对数并除以八得到前两式；使用 $\rho_{*,k}=\tanh(2\eta_k)$ 及双曲正切加法公式得到第三式。分母严格正，因为两系数都在 $(-1,1)$ 内。对角矩阵逐项相乘给 $S$ 的公式。这里要求主轴标记一致；任意旋转后的两个伸缩矩阵不受此一参数加法支配。经典 sum-product 消元背景及在硬排斥图上的范围见 C-66.3 的 Peyrard 等引文；当前证明只使用有限非负权与严格正的条件总质量。证毕。

**命题 C-69.3（正响应的精确抵消不删除路径）。** 取

$$
H_+=\begin{pmatrix}3&1\\1&3\end{pmatrix},\qquad
H_-=\begin{pmatrix}1&3\\3&1\end{pmatrix}.
$$

它们的带标记伸缩参数互为相反数，而并联响应的规范椭圆是圆。

证明。两比值比分别为 $9,1/9$，所以 $J_\pm=\pm\log9$、$\eta_\pm=\pm(\log9)/8$、$\rho_{*,\pm}=\pm1/2$。逐格相乘得

$$
H_+\odot H_-=\begin{pmatrix}3&3\\3&3\end{pmatrix}.
$$

它的比值比为一，故 $\eta=0$。两矩阵可直接作为没有内部变量的正端点因子；组合后每个权仍严格正。若要求实际有内部路径的图块，C-64.3–C-64.4 已供应连通六顶点例子：短路内部活动 $1/3$、长路两内部活动一，其响应分别为

$$
\begin{pmatrix}4/3&1\\1&1\end{pmatrix},\qquad
\begin{pmatrix}3&2\\2&1\end{pmatrix},
$$

并联为 $\left(\begin{smallmatrix}4&2\\2&1\end{smallmatrix}\right)$。四角比 $(4/3)(3/4)=1$，同样给圆；该已知例子的完整五律为 $(4,2,4,2,1)/13$。这里消费其来源和计权，不另声称构造了新路径反例。两条路径仍在图中，每个配置仍有非负权；抵消的是带符号对数关联，并不是路径消失或复振幅干涉。证毕。

## 70. 一般串联的偏置、完整递推与同形反例

**定义 C-70.1（边界矩阵的对数坐标）。** 对 $H=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)>0$，取 $s_0=1,s_1=-1$，定义

$$
\begin{aligned}
c_0(H)&=\tfrac14\log(abcd),&
h_L(H)&=\tfrac14\log\frac{ab}{cd},\\
h_R(H)&=\tfrac14\log\frac{ac}{bd},&
j(H)&=\tfrac14\log\frac{ad}{bc}=2\eta(H).
\end{aligned}
\tag{C70.1}
$$

这些是经典二元对数线性坐标，亦与 C-7.7–C-7.8 的四角项一致；在以下一般串联中保留它们作为输入。它们满足唯一展开

$$
\log H_{ab}=c_0+h_Ls_a+h_Rs_b+j s_as_b.
\tag{C70.2}
$$

此式中矩阵索引 $a,b$ 取 $0,1$；式 (C70.1) 的 $a,b,c,d$ 则是四个格值。为核对唯一性，将四个对数格值依次按符号模式 $(1,1,1,1)$、$(1,1,-1,-1)$、$(1,-1,1,-1)$、$(1,-1,-1,1)$ 求和并除以四，正好得到式 (C70.1)。四个符号模式两两正交、平方长度四，所以逆变换必为式 (C70.2)。这同时证明存在与唯一。

乘整个矩阵以正数只平移 $c_0$。因此 $(\eta,h_L,h_R)$ 完整决定归一化的端点律及对端点概率比的响应；完整未归一化权还需 $c_0$。单独的 $\eta$ 只决定正行列轨道，不能恢复所有局部概率。

**命题 C-70.2（保留接缝偏置的完整串联公式）。** 设两块具有式 (C70.2) 的坐标，写作 $c_k,h_L^{(k)},h_R^{(k)},j_k$，$k=1,2$。设正接缝权为 $W=\operatorname{diag}(w_0,w_1)$，定义

$$
\ell_w=\tfrac12\log(w_0w_1),\qquad
h_w=\tfrac12\log(w_0/w_1),\qquad
\beta=h_R^{(1)}+h_L^{(2)}+h_w.
\tag{C70.3}
$$

对外端符号 $s,t\in\{1,-1\}$，置

$$
L_{st}=\log\cosh(\beta+j_1s+j_2t),\qquad
C=c_1+c_2+\ell_w+\log2.
$$

则合成响应的每个格值及全部对数坐标为

$$
H_{\rm series}(s,t)
=2e^{c_1+c_2+\ell_w+h_L^{(1)}s+h_R^{(2)}t}
\cosh(\beta+j_1s+j_2t),
\tag{C70.4}
$$

$$
\begin{aligned}
c_{\rm series}&=C+\tfrac14(L_{++}+L_{+-}+L_{-+}+L_{--}),\\
h_{L,\rm series}&=h_L^{(1)}+\tfrac14(L_{++}+L_{+-}-L_{-+}-L_{--}),\\
h_{R,\rm series}&=h_R^{(2)}+\tfrac14(L_{++}-L_{+-}+L_{-+}-L_{--}),\\
j_{\rm series}&=\tfrac14(L_{++}-L_{+-}-L_{-+}+L_{--}),\qquad
\eta_{\rm series}=j_{\rm series}/2.
\end{aligned}
\tag{C70.5}
$$

特别地，令

$$
P_\beta=\frac{\cosh(2\beta)+\cosh(2(j_1+j_2))}{2},\qquad
R_\beta=\frac{\cosh(2\beta)+\cosh(2(j_1-j_2))}{2},
\tag{C70.6}
$$

则

$$
\Omega_{\rm series}=\frac{P_\beta}{R_\beta},\qquad
\rho_{*,\rm series}=\frac{\sqrt{P_\beta}-\sqrt{R_\beta}}
{\sqrt{P_\beta}+\sqrt{R_\beta}}.
\tag{C70.7}
$$

因此一般串联的椭圆还依赖 $\beta$，下一次串联则仍需式 (C70.5) 的两个输出偏置。

证明。接缝符号记作 $u\in\{1,-1\}$。由于 $w_u=e^{\ell_w+h_wu}$，式 (C69.2) 的逐格和成为

$$
\begin{aligned}
H_{\rm series}(s,t)
&=\sum_{u=\pm1}
\exp\bigl(c_1+c_2+\ell_w+h_L^{(1)}s+h_R^{(2)}t
+u(\beta+j_1s+j_2t)\bigr)\\
&=2e^{c_1+c_2+\ell_w+h_L^{(1)}s+h_R^{(2)}t}
\cosh(\beta+j_1s+j_2t).
\end{aligned}
$$

这证明式 (C70.4)，且没有删除任何偏置或质量因子。对其对数应用式 (C70.1) 的四个正交投影即得式 (C70.5)。计算四角比时，公共倍数与外端线性偏置消去，剩下

$$
\frac{\cosh(\beta+j_1+j_2)\cosh(\beta-j_1-j_2)}
{\cosh(\beta+j_1-j_2)\cosh(\beta-j_1+j_2)}.
$$

使用 $\cosh(x+y)\cosh(x-y)=[\cosh(2x)+\cosh(2y)]/2$ 得式 (C70.6)–(C70.7)。两项始终正。这个推导所用的二元消元是 C-64.2 的已知拼接，新增的椭圆读法保留了其中无法由 $\eta_1,\eta_2$ 独自确定的接缝信息。证毕。

**命题 C-70.3（平衡接缝的精确乘法与退化范围）。** 在命题 C-70.2 的条件下，

$$
\beta=0\quad\Longrightarrow\quad
\rho_{*,\rm series}=\rho_{*,1}\rho_{*,2}.
\tag{C70.8}
$$

若 $j_1j_2\ne0$，该等式成立当且仅当 $\beta=0$；若 $j_1=0$ 或 $j_2=0$，两边对任何 $\beta$ 都等于零。对所有有限偏置都有

$$
|\rho_{*,\rm series}|\le|\rho_{*,1}|\,|\rho_{*,2}|,
\tag{C70.9}
$$

在非退化且不平衡时严格小于。

证明。先取 $\beta=0$。式 (C70.6) 给 $P_0=\cosh^2(j_1+j_2)$、$R_0=\cosh^2(j_1-j_2)$。双曲余弦正，故

$$
\begin{aligned}
\rho_{*,\rm series}
&=\frac{\cosh(j_1+j_2)-\cosh(j_1-j_2)}
{\cosh(j_1+j_2)+\cosh(j_1-j_2)}\\
&=\frac{2\sinh j_1\sinh j_2}{2\cosh j_1\cosh j_2}
=\tanh j_1\tanh j_2
=\rho_{*,1}\rho_{*,2}.
\end{aligned}
$$

平衡条件在原坐标中恰为

$$
h_R^{(1)}+h_L^{(2)}+\tfrac12\log(w_0/w_1)=0;
\tag{C70.10}
$$

它消掉实际接缝的总偏好，并不要求两个块的所有外端边缘都平衡。

一般 $\beta$ 下，$P_\beta$ 和 $R_\beta$ 比 $P_0,R_0$ 都增加同一个非负数 $(\cosh2\beta-1)/2$，此数为零当且仅当 $\beta=0$。它们的差与 $\beta$ 无关：

$$
P_\beta-R_\beta=\sinh(2j_1)\sinh(2j_2).
$$

有理化式 (C70.7) 得

$$
\rho_{*,\rm series}
=\frac{P_\beta-R_\beta}
{(\sqrt{P_\beta}+\sqrt{R_\beta})^2}.
\tag{C70.11}
$$

若 $j_1j_2\ne0$，分子非零且符号不变；$\beta\ne0$ 时分母严格增大，故绝对值严格减小。这证明上界、等号的必要性及带符号乘法的范围。若某个 $j_k=0$，它对应正秩一矩阵，$P_\beta=R_\beta$，合成也秩一，所以等式对任意偏置成立，不能在这个退化情形反推接缝平衡。证毕。

作为平衡表示的同一中间计算，令

$$
K_\rho=\frac12\begin{pmatrix}1+\rho&1-\rho\\1-\rho&1+\rho\end{pmatrix},
\qquad-1<\rho<1.
$$

它是平衡行随机矩阵，并等于 $2Q_*$。直接相乘时，对角格为 $[(1+\rho_1)(1+\rho_2)+(1-\rho_1)(1-\rho_2)]/4=(1+\rho_1\rho_2)/2$，非对角格为 $(1-\rho_1\rho_2)/2$，所以

$$
K_{\rho_1}K_{\rho_2}=K_{\rho_1\rho_2}.
\tag{C70.12}
$$

这与式 (C70.8) 相符。它只给已指定平衡接缝的精确乘法，不把一般式 (C70.9) 的上界改为等式。

**命题 C-70.4（同一椭圆不能独立预测串联）。** 取

$$
H=\begin{pmatrix}3&1\\1&3\end{pmatrix},\qquad
D=\begin{pmatrix}3&0\\0&1\end{pmatrix},\qquad
\widetilde H=HD=\begin{pmatrix}9&1\\3&3\end{pmatrix}.
$$

$H$ 与 $\widetilde H$ 具有同一个带标记规范椭圆，但 $H^2$ 与 $\widetilde HH$ 的规范椭圆不同。

证明。正列重加权保持四角比，两表均为 $\Omega=9$、$\rho_*=1/2$。实际乘法却给

$$
H^2=\begin{pmatrix}10&6\\6&10\end{pmatrix},\qquad
\widetilde HH=\begin{pmatrix}28&12\\12&12\end{pmatrix}.
$$

前者 $\Omega=25/9$、$\rho_*=(10-6)/(10+6)=1/4$；后者 $\Omega=7/3$，所以

$$
\rho_*(\widetilde HH)
=\frac{\sqrt{21}-3}{\sqrt{21}+3}
\approx0.208712153\ne\frac14.
\tag{C70.13}
$$

若等于 $1/4$，交叉相乘会给 $3\sqrt{21}=15$，平方后 $21=25$，矛盾，故差别是精确的。$H$ 的左右偏置为零；$\widetilde H$ 的 $h_L=0$、$h_R=(\log3)/2$，两者 $j$ 相同。于是第二个乘积恰把原来可从单块等价类中消去的右权重 $D$ 放到了实际接缝，$\beta=(\log3)/2\ne0$。这也从式 (C70.9) 解释了严格缩小。正行列等价只回答孤立块的比较问题，没有允许在拼接后删除实际接缝活动。证毕。

## 71. 椭圆轴比与边界对数响应的最佳收缩

**定义 C-71.1（正射线上的边界响应）。** 输入为正向量 $v=(v_0,v_1)$，整体正倍数视为同一射线，用

$$
x=\log(v_0/v_1)\in\mathbb R
$$

表示其比例。对 $H=\left(\begin{smallmatrix}a&b\\c&d\end{smallmatrix}\right)>0$，输出向量 $Hv$ 也正，定义输出比例函数

$$
F_H(x)=\log\frac{ae^x+b}{ce^x+d}.
\tag{C71.1}
$$

两个输入正射线的 Hilbert 距离在二维恰为

$$
d_{\rm Hil}(u,v)
=\log\frac{\max(u_0/v_0,u_1/v_1)}{\min(u_0/v_0,u_1/v_1)}
=\left|\log\frac{u_0}{u_1}-\log\frac{v_0}{v_1}\right|.
\tag{C71.2}
$$

这是正锥的射影距离，不是欧氏平面中任意两个向量的距离。

**命题 C-71.2（四角椭圆的精确响应含义）。** 对命题 C-67.2 的规范椭圆，若无标记轴比为 $R_{\rm ell}=e^{2|\eta|}$，则该正边界块对对数比例的最小全局 Lipschitz 常数为

$$
\sup_{x\in\mathbb R}|F_H'(x)|
=|\rho_*(H)|
=\tanh(2|\eta(H)|)
=\frac{R_{\rm ell}^2-1}{R_{\rm ell}^2+1}<1.
\tag{C71.3}
$$

若 $ad\ne bc$，导数绝对值在唯一输入

$$
e^x=\sqrt{\frac{bd}{ac}}
\tag{C71.4}
$$

达到最大；若 $ad=bc$，$F_H$ 恒定，最佳常数为零，所有输入都达到该值。

证明中的收缩机制是经典 Birkhoff–Hilbert 正锥结果。Samuel N. Cohen、Eliana Fausti，*Hyperbolic contractivity and the Hilbert metric on probability measures*，[arXiv:2309.02413v2](https://arxiv.org/abs/2309.02413v2)，Theorem 2.4 明确署名 Birkhoff，Proposition 4.1 给非负矩阵的经典系数表达。此处将其二维精确值与已有四角椭圆轴比连接，完整的标量计算如下。

求导得到

$$
F_H'(x)=\frac{(ad-bc)e^x}{(ae^x+b)(ce^x+d)}.
\tag{C71.5}
$$

令 $z=e^x>0$，则导数绝对值为

$$
\frac{|ad-bc|}{acz+(ad+bc)+bd/z}.
$$

由

$$
acz+\frac{bd}{z}-2\sqrt{abcd}
=\left(\sqrt{acz}-\sqrt{bd/z}\right)^2\ge0,
$$

分母在 $z=\sqrt{bd/(ac)}$ 取最小，且正格值保证这个输入有限而唯一。如果分子非零，这也给唯一最大导数。最大值为

$$
\begin{aligned}
\frac{|ad-bc|}{ad+bc+2\sqrt{abcd}}
&=\frac{|(\sqrt{ad}-\sqrt{bc})(\sqrt{ad}+\sqrt{bc})|}
{(\sqrt{ad}+\sqrt{bc})^2}\\
&=\frac{|\sqrt{ad}-\sqrt{bc}|}{\sqrt{ad}+\sqrt{bc}}
=|\rho_*|.
\end{aligned}
$$

若 $ad=bc$，两行正比例，$(ae^x+b)/(ce^x+d)=a/c=b/d$，所以 $F_H$ 恒定。两种情形下均得到显示的上确界。均值定理使它成为全局 Lipschitz 上界；反过来，任意全局 Lipschitz 常数必须不小于每一点差商的极限 $|F_H'(x)|$，所以它确是最小常数。这里的“达到”首先指导数；不要求两个不同有限输入间的差商也恰等于最大导数。

式 (C67.8) 给 $|\rho_*|=\tanh(|J|/4)=\tanh(2|\eta|)$，再用 $R_{\rm ell}^2=e^{4|\eta|}$ 得式 (C71.3)。与经典直径式也可逐项对照：$F_H(-\infty)=\log(b/d)$，$F_H(+\infty)=\log(a/c)$，且导数符号恒定；所以输出正射线集合的 Hilbert 直径是

$$
\Delta(H)=\left|\log\frac{a/c}{b/d}\right|=|J(H)|.
$$

Birkhoff 的 $\tanh(\Delta/4)$ 因此正是当前系数，没有额外乘二或除二。证毕。

**命题 C-71.3（串联上界与不能删除的输出偏置）。** 对定义 C-69.1 的正串联响应，有

$$
F_{H_1H_2}=F_{H_1}\circ F_{H_2},\qquad
F_W(x)=x+\log(w_0/w_1),
\tag{C71.6}
$$

以及

$$
|\rho_*(H_1WH_2)|
\le|\rho_*(H_1)|\,|\rho_*(H_2)|.
\tag{C71.7}
$$

这一界约束输入差异传递的幅度，仍不决定输出概率比的绝对位置。

证明。对正向量 $v$，其右边先经 $H_2$ 得到正向量，再经 $H_1$ 得到 $H_1H_2v$。比例不依赖中间向量的整体倍数，所以先读 $F_{H_2}(x)$ 再读 $F_{H_1}$ 等于一次读乘积矩阵，证明第一式。对角矩阵把比值乘以 $w_0/w_1$，证明第二式。链式法则给

$$
\left|(F_{H_1}\circ F_W\circ F_{H_2})'(x)\right|
\le\sup|F_{H_1}'|\,\sup|F_{H_2}'|,
$$

因为 $F_W'=1$。用命题 C-71.2 对整个正乘积矩阵识别左边的上确界，即得式 (C71.7)。这与命题 C-70.3 的直接偏置公式相符；不同输入位置的两个导数峰值一般不能同时达到，不能据两个单块的尖锐性直接声称乘积上界处处可达。

例如左乘 $D_L=\operatorname{diag}(l_0,l_1)$ 给

$$
F_{D_LH}(x)=F_H(x)+\log(l_0/l_1),
$$

导数和规范椭圆不变，但每个输出对数比均移动。右乘正对角矩阵则平移输入位置。因此，若要继续拼接或恢复端点律，仍需 C-70.1 的两偏置。圆形的 $\eta=0$ 只意味着输出比例与输入比例无关，输出比例本身可以有任意有限偏好。证毕。

## 72. Fibonacci 响应的两种椭圆与正射线遗忘

**约定 C-72.1（组成矩阵与实际外部供应）。** 以 $F_0=0,F_1=1,F_{m+2}=F_{m+1}+F_m$ 定义 Fibonacci 数。沿用[《辛预测完成》§35.10](SYMPLECTIC_PREDICTIVE_COMPLETION.md#3510-原生守卫固定仿射分支与反辛符号)的两坐标线性部分，另取交换矩阵，写为

$$
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
P=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
A=PMP=\begin{pmatrix}1&1\\1&0\end{pmatrix}.
\tag{C72.1}
$$

只交换坐标得到 $A$，不识别概率标签与任意物理坐标。$A$ 也正是 C-60.1 的兼容矩阵 $J$；为避免与对数比 $J(H)$ 混淆，此处专用字母 $A$。定义 $H_m=A^m$，$m\ge2$。C-8.3、C-65.1 已给路径幂公式；在均匀正活动环的外部路径中，其实际参数为 $m=n-2$，因而该环供应使用 $m\ge3$。$m=2$ 则仍是有效的两边路径响应。

**命题 C-72.2（同一个 Fibonacci 响应的规范形变量）。** 对 $m\ge2$，

$$
H_m=\begin{pmatrix}F_{m+1}&F_m\\F_m&F_{m-1}\end{pmatrix}>0,
\qquad\det H_m=(-1)^m,
\tag{C72.2}
$$

其带标记规范椭圆满足

$$
\eta_m=\frac18\log\left(1+\frac{(-1)^m}{F_m^2}\right),
\qquad
\rho_{*,m}=\frac{(-1)^m}
{\left(\sqrt{F_m^2+(-1)^m}+F_m\right)^2}.
\tag{C72.3}
$$

因而偶数层为正关联，奇数层为负关联，且 $\eta_m\to0$、$\rho_{*,m}\to0$，规范椭圆的无标记轴比趋于一。

证明。这里消费上述路径供应的矩阵幂，参数索引可用递推逐项对照：$A^2=\left(\begin{smallmatrix}2&1\\1&1\end{smallmatrix}\right)$；若式 (C72.2) 在 $m$ 成立，右乘 $A$ 给

$$
\begin{pmatrix}F_{m+1}+F_m&F_{m+1}\\F_m+F_{m-1}&F_m\end{pmatrix}
=\begin{pmatrix}F_{m+2}&F_{m+1}\\F_{m+1}&F_m\end{pmatrix}.
$$

这也核定 $m$ 是边数。$m\ge2$ 时三个相关 Fibonacci 数均正；$m=1$ 的右下角为零，不在本正表椭圆定义域。行列式乘法及 $\det A=-1$ 给

$$
F_{m+1}F_{m-1}-F_m^2=(-1)^m,
$$

即这里所用的经典 Cassini 中间式。于是

$$
\Omega_m=\frac{F_{m+1}F_{m-1}}{F_m^2}
=1+\frac{(-1)^m}{F_m^2}>0,
$$

代入式 (C67.5) 即得 $\eta_m$。而式 (C67.8) 给

$$
\rho_{*,m}=\frac{\sqrt{F_m^2+(-1)^m}-F_m}
{\sqrt{F_m^2+(-1)^m}+F_m}.
$$

分子乘共轭并约去得到式 (C72.3)。奇数 $m\ge3$ 时 $F_m\ge2$，所以根号内严格正；偶数情形也显然正。符号由 $(-1)^m$ 给出。

边界 $m=2$ 给 $\Omega_2=2$、$\eta_2=(\log2)/8$、$\rho_{*,2}=(\sqrt2-1)/(\sqrt2+1)=3-2\sqrt2$，没有除零。由递推及 $F_{m+2}\ge2F_m$（$m\ge2$），有 $F_m\to\infty$，所以式 (C72.3) 的对数趋零、分母趋无穷，得两个极限。无标记轴比是 $e^{2|\eta_m|}\to1$。进一步由 $\log(1+t)/t\to1$ 得

$$
\eta_m=\frac{(-1)^m}{8F_m^2}+O(F_m^{-4}),\qquad
\rho_{*,m}=\frac{(-1)^m}{4F_m^2}+O(F_m^{-4}).
\tag{C72.4}
$$

这些渐近式在当前整数序列上使用 $F_m\to\infty$，没有加入任何素性假设。证毕。

**命题 C-72.3（直接线性像变扁而规范关联像变圆）。** 同一个 $H_m$ 直接作用于欧氏单位圆，其半轴为

$$
\varphi^m,\quad\varphi^{-m},\qquad
\operatorname{Area}=\pi,\qquad
R_{\rm direct}=\varphi^{2m}\longrightarrow\infty.
\tag{C72.5}
$$

其规范关联椭圆则有

$$
R_{\rm intrinsic}=e^{2|\eta_m|}\longrightarrow1.
\tag{C72.6}
$$

这两个极限分别描述欧氏方向伸缩和正边界输入比例敏感性，所用比较规则不同。

证明。$A$ 为实对称矩阵，特征多项式 $t^2-t-1$ 的两个根为 $\varphi,-\varphi^{-1}$，有正交特征基。故 $H_m$ 的特征值为 $\varphi^m,(-1)^m\varphi^{-m}$。半轴必须取奇异值，即 $H_m^{\mathsf T}H_m$ 特征值的正平方根，因而为 $\varphi^m,\varphi^{-m}$；奇数层的负特征值表示在该特征方向上的反向，绝不表示负半轴。两半轴乘积一，所以面积为 $\pi$；或者由 $|\det H_m|=1$ 得同一结论。长短轴比给式 (C72.5)，式 (C72.6) 已由命题 C-72.2 得出。

下表均为所列精确公式的十进制舍入值，用来比较两种像，不作为极限证明：

| $m$ | $F_m$ | 直接线性像轴比 $\varphi^{2m}$ | 规范关联椭圆轴比 $e^{2|\eta_m|}$ |
| ---: | ---: | ---: | ---: |
| 3 | 2 | $17.9443$ | $1.07457$ |
| 5 | 5 | $122.992$ | $1.01026$ |
| 7 | 13 | $842.999$ | $1.00148$ |
| 11 | 89 | $39603.0$ | $1.00003156$ |

例如首行的规范轴比恰为 $(4/3)^{1/4}$；后面三个奇数层分别是 $(25/24)^{1/4}$、$(169/168)^{1/4}$、$(7921/7920)^{1/4}$。$F_5=5,F_7=13,F_{11}=89$ 为素数，但 $m=6$ 的合数项 $F_6=8$ 同样给 $\Omega_6=65/64$、$\eta_6=(\log(65/64))/8$，所以这些关系不是素性判据。证毕。

**命题 C-72.4（正输入的归一化遗忘及有符号例外）。** 对固定正输入 $u,v$，有

$$
d_{\rm Hil}(H_mu,H_mv)
\le |\rho_{*,m}|\,d_{\rm Hil}(u,v)\longrightarrow0.
\tag{C72.7}
$$

将 $H_mv$ 按坐标和归一化后，所有固定正输入趋向同一个 Perron 概率向量

$$
\frac{(\varphi,1)}{\varphi+1}.
\tag{C72.8}
$$

该结论不适用于任意有符号向量。

证明。$m\ge2$ 时 $H_m$ 严格正，命题 C-71.2 给式 (C72.7)，命题 C-72.2 给系数趋零。为确定共同极限，取正交特征向量

$$
u_+=(\varphi,1),\qquad u_-=(1,-\varphi).
$$

任意 $v>0$ 可唯一写成 $v=\alpha u_++\gamma u_-$，其中

$$
\alpha=\frac{v\cdot u_+}{u_+\cdot u_+}>0.
$$

于是

$$
H_mv=\alpha\varphi^m u_++\gamma(-\varphi^{-1})^m u_-.
$$

除以 $\alpha\varphi^m$ 后，第二项的系数是 $(\gamma/\alpha)(-1)^m\varphi^{-2m}\to0$。正输入的输出始终正，坐标和归一化连续，得到式 (C72.8)。相反，对有符号向量 $v=u_-$，Perron 分量恰为零，$H_mv=(-\varphi^{-1})^m u_-$ 始终沿另一个特征射线，不能称为遗忘到正主方向；它也不在式 (C71.2) 的正锥度量域内。

因此，直接椭圆越来越扁表示同一个线性算子的奇异值差异扩大；规范椭圆越来越圆表示它对正输入比例的最坏敏感性趋零。两者与主方向优势相容，但不能从后者推出任意有符号方向或任意原始长度均不可区分。证毕。

## 73. 四角复比值、独立相位与条件底面

**定义 C-73.1（明确指定的复振幅完成）。** 除五概率外，另给五个相位，采用《辛预测完成》§35 的约定

$$
\psi_s=\sqrt{p_s}e^{-i\theta_s},\qquad
\sum_s|\psi_s|^2=1,\qquad
\theta_s\in\mathbb R/2\pi\mathbb Z.
\tag{C73.1}
$$

这是假设一个正交五模式复载体，不从经典概率唯一推出。隐藏角为

$$
\chi=\theta_0-\theta_1-\theta_3+\theta_{13}\pmod{2\pi},
$$

四角复比值为

$$
\Xi=\frac{\psi_0\psi_{13}}{\psi_1\psi_3}\in\mathbb C^\times.
\tag{C73.2}
$$

全正性确保分母非零；此处 $\chi$ 是角，旧 C-13.3 用于复比值的同形字母改由 $\Xi$ 表示。

**命题 C-73.2（规范椭圆与剩余相位的联合表示）。** 对定义 C-73.1，

$$
\Xi=e^{4\eta-i\chi},\qquad
\eta=\frac14\log|\Xi|,\qquad
\chi=-\arg\Xi\pmod{2\pi}.
\tag{C73.3}
$$

所以同一带标记概率椭圆容许整个独立相位圆周。固定 $(X,Y,Z)$ 后，$\Xi$ 完整参数化概率与指定位置相位商的正内部；没有固定这些均值时，$\Xi$ 不恢复全部五振幅。

证明。直接计算模与相位，

$$
|\Xi|=\sqrt{\frac{p_0p_{13}}{p_1p_3}}
=e^{J/2}=e^{4\eta},\qquad
\frac{\Xi}{|\Xi|}=e^{-i(\theta_0+\theta_{13}-\theta_1-\theta_3)}=e^{-i\chi}.
$$

这给式 (C73.3)。要核定“剩余”所指的精确等价关系，取共同相位及三个位置相位作用

$$
\theta_s\longmapsto\theta_s+\gamma_0+x_s\gamma_X+y_s\gamma_Y+z_s\gamma_Z,
\tag{C73.4}
$$

其中占位函数在五模式上分别为

$$
x=(0,1,0,0,1),\quad y=(0,0,0,1,1),\quad z=(0,0,1,0,0).
$$

交替和 $(1,-1,0,-1,1)$ 与这四个函数正交，故保持 $\chi$。反过来，选 $\gamma_0=-\theta_0$，$\gamma_X=\theta_0-\theta_1$，$\gamma_Y=\theta_0-\theta_3$，$\gamma_Z=\theta_0-\theta_2$，则前四模式相位全部归零，最后相位恰为 $\chi$。所有式子在整周期环面上成立，所以没有残余有限覆盖，余角周期为 $2\pi$。这就是旧 C-13.2 的完整商结论在相反角约定下的应用。

固定均值时，命题 C-68.2 使 $\eta$ 遍历全实轴，$\chi$ 可独立遍历圆周，因此 $(\eta,\chi)\mapsto e^{4\eta-i\chi}$ 双射到 $\mathbb C^\times$。旧相位约定 $c_s=\sqrt{p_s}e^{i\theta_s^{\rm old}}$ 对应 $\theta_s^{\rm old}=-\theta_s$，故 $\Phi_{\rm old}=-\chi$，旧实坐标 $u=\tfrac12\log\Omega=4\eta$。固定均值的商层面上这已完整；在原五振幅层面，它既忘掉位置相位标架，也不提供未知的三个可见均值。证毕。

**命题 C-73.3（相同概率圆的两个不同底面相干结构）。** 按五模式顺序取

$$
|\Psi_+\rangle=\frac1{\sqrt5}(1,1,1,1,1),\qquad
|\Psi_-\rangle=\frac1{\sqrt5}(1,1,1,1,-1).
\tag{C73.5}
$$

它们具有相同五概率、相同规范圆，但 $\Xi_+=1$、$\Xi_-=-1$。条件于底面并明确识别四个模式为 $\mathbb C^2\otimes\mathbb C^2$ 的 $(00,01,10,11)$ 后，前者是乘积纯态，后者的两侧约化态均为 $I_2/2$。这个实例是原卷 C-12.3 的已知见证在椭圆—复比值坐标中的应用。

证明。两向量均归一化，五个模平方均为 $1/5$。四角比为一，所以 $\eta=\rho_*=0$，而四角复乘积的符号直接给 $\Xi_+=1$、$\Xi_-=-1$；后一情形可取 $\theta_{13}=\pi$，其余为零，故 $\chi=\pi\bmod2\pi$。底面概率为 $r=4/5$。投影到底面并除以 $\sqrt r$，按行左端、列右端排列得到系数矩阵

$$
B_+=\frac12\begin{pmatrix}1&1\\1&1\end{pmatrix},\qquad
B_-=\frac12\begin{pmatrix}1&1\\1&-1\end{pmatrix}.
\tag{C73.6}
$$

前者是 $(1,1)^{\mathsf T}/\sqrt2$ 与 $(1,1)/\sqrt2$ 的外积，秩一，对应 $|+\rangle\otimes|+\rangle$。后者行列式为 $-1/2$，秩二，且

$$
B_-B_-^\dagger=B_-^\dagger B_-=\frac12 I_2.
$$

对两因子纯态，系数矩阵秩一恰等价于可写成两个向量的张量积；约化态通过一侧指标求和得到上述矩阵乘积。Wootters，*Entanglement of Formation of an Arbitrary State of Two Qubits*，[arXiv:quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)，式 (2)，将二部纯态纠缠定义为任一约化态的以二为底的熵。此处 $B_+$ 的约化谱为 $(1,0)$，熵零；$B_-$ 的约化谱为 $(1/2,1/2)$，熵一，达到二元约化态的最大值：任意二元谱 $(t,1-t)$ 的熵 $-t\log_2t-(1-t)\log_2(1-t)$ 在 $0<t<1$ 的导数为 $\log_2((1-t)/t)$，在 $t=1/2$ 左正右负，端点连续值为零，故最大值为一。这里只使用该文的纯态定义，不调用其一般混态优化公式。

同样的概率表还可给经典对角混合

$$
\rho_{\rm diag}=\frac14\sum_{a,b=0}^1
|a\rangle\langle a|\otimes|b\rangle\langle b|,
$$

它显式为乘积态混合，因而可分。故概率圆本身既不供应相干，也不认证纠缠。上述张量积结构是在条件底面的四维空间上明确指定的；整个五模式空间维数为五，不能因此直接当作两个二元因子的张量积，也没有仅凭模式字典获得物理子系统。证毕。

**命题 C-73.4（模与相位共同控制条件纯态行列式）。** 在定义 C-73.1 的全正域，把条件底面系数写为

$$
B=\frac1{\sqrt r}\begin{pmatrix}\psi_0&\psi_3\\\psi_1&\psi_{13}\end{pmatrix}.
$$

则

$$
\begin{aligned}
r^2|\det B|^2
&=(\sqrt{p_0p_{13}}-\sqrt{p_1p_3})^2
+4\sqrt{p_0p_1p_3p_{13}}\sin^2(\chi/2),\\
\det B=0&\quad\Longleftrightarrow\quad\Xi=1
\quad\Longleftrightarrow\quad\eta=0\ \text{且}\ \chi=0\pmod{2\pi}.
\end{aligned}
\tag{C73.7}
$$

证明。消费 C-12.2 的相位敏感行列式，在当前记号中可直接由

$$
r\det B=\psi_0\psi_{13}-\psi_1\psi_3
=\psi_1\psi_3(\Xi-1)
$$

核对。令两复乘积的模分别为 $a=\sqrt{p_0p_{13}}$、$b=\sqrt{p_1p_3}$，它们的相对相位为 $-\chi$。故模平方为 $a^2+b^2-2ab\cos\chi=(a-b)^2+4ab\sin^2(\chi/2)$。正性给 $ab>0$，两非负项同时为零恰要求 $a=b$ 且 $\chi=0\bmod2\pi$。这证明全部等价。若底角为零，须直接用复乘积差，不定义零振幅的辐角或零分母的 $\Xi$。该式表明规范圆消除的只是第一项，独立相位项仍可非零；其适用载体仍是明确给定的条件两因子纯态。证毕。

## 74. 实际固定矩相位商中的椭圆坐标与辛尺度

**约定 C-74.1（来源、符号及尺度的完整对应）。** 本章只在 $0<Z<1$、$0<X,Y<r$、$\kappa_-<\kappa<\kappa_+$ 的全正内部使用几何。来源为[《辛预测完成》§35.3–§35.7](SYMPLECTIC_PREDICTIVE_COMPLETION.md#357-隐藏概率信息反相位与两倍尺度的关系度量)与原卷 [C-13、C-14](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md#13-固定均值的五态相位商与复关系坐标)。它们均是另行指定复振幅之后的射影几何，不能由五概率自动唯一选出。

为避免同名参数掩盖尺度，精确字典为

$$
\begin{gathered}
\tau_{\rm SP}=J=\log\Omega,\qquad
\eta_{\rm SP}=J/2=4\eta,\qquad
\zeta_{\rm SP}=\Xi,\qquad I_{\rm SP}=\mathcal I,\\
\theta_s^{\rm old}=-\theta_s,\qquad
\Phi_{\rm old}=-\chi,\qquad
u_{\rm old}=4\eta,\qquad
 g_{\rm SP}=2g_{\rm old}.
\end{gathered}
\tag{C74.1}
$$

这里 $u_{\rm old}$ 指 C-13.3 的实对数模坐标。$\eta$ 始终是本椭圆半轴的对数，绝不能直接与 §35.7 的 $\eta_{\rm SP}$ 等同。两种角约定描述同一个复振幅，不是把状态另作复共轭。

所选射影尺度在每条标准 $\mathbb{CP}^1$ 上辛面积为 $2\pi$。在全正归一化图上，来源的形式及度量为

$$
\omega=\sum_s d\theta_s\wedge dp_s,
\qquad
 g=\frac12\sum_s\frac{dp_s^2}{p_s}
+2\left[\sum_s p_s\,d\theta_s^2
-\left(\sum_s p_s\,d\theta_s\right)^2\right].
\tag{C74.2}
$$

共同相位先按射线识别，再固定三个矩值 $(X,Y,Z)$，最后除去三个位置相位的 $T^3$ 作用；只有这整个操作才给二维关系空间。底面条件化是另一种操作。

**命题 C-74.2（实际约化形式与椭圆—相位换元）。** 在约定 C-74.1 的全正固定矩商中，$\chi$ 的周期为 $2\pi$，且

$$
\omega_{\rm red}=d\chi\wedge d\kappa,\qquad
 g_{\rm red}=\frac{\mathcal I}{2}d\kappa^2
+\frac2{\mathcal I}d\chi^2.
\tag{C74.3}
$$

改用椭圆参数 $\eta$ 后，

$$
\omega_{\rm red}=\frac8{\mathcal I}\,d\chi\wedge d\eta,\qquad
 g_{\rm red}=\frac2{\mathcal I}
\left(16\,d\eta^2+d\chi^2\right)
=\frac2{\mathcal I}|d\log\Xi|^2.
\tag{C74.4}
$$

最后一个复对数只在局部相位图取值；$\mathcal I$ 是随 $\kappa$、等价地随 $\eta$ 变化的正函数，不能删除。

证明。§35.4–§35.5 已供应真正的固定矩约化，§35.7 已给所选两倍尺度的水平度量。为完整连接到本椭圆，先核定周期与符号。令

$$
\vartheta_X=\theta_1-\theta_0,\quad
\vartheta_Y=\theta_3-\theta_0,\quad
\vartheta_Z=\theta_2-\theta_0.
$$

其整数逆变换为

$$
\theta_1=\theta_0+\vartheta_X,\quad
\theta_3=\theta_0+\vartheta_Y,\quad
\theta_2=\theta_0+\vartheta_Z,\quad
\theta_{13}=\theta_0+\vartheta_X+\vartheta_Y+\chi.
$$

正逆变换在整周期环面上互逆，故 $\chi$ 的周期恰为 $2\pi$。代入式 (C74.2)，共同角项因 $\sum_sdp_s=0$ 消失，余下

$$
\omega=d\vartheta_X\wedge dX+d\vartheta_Y\wedge dY
+d\vartheta_Z\wedge dZ+d\chi\wedge d\kappa.
$$

固定 $X,Y,Z$ 使前三项限制为零；沿三个位置角的轨道方向也为零，因而下降为式 (C74.3) 的二形式。这是限制后再取商，不是只固定三个数就丢掉三个相位方向。

对度量，固定矩的概率切向量为

$$
dp_s=d_s\,d\kappa,\qquad d=(1,-1,0,-1,1),
$$

所以概率项为 $(\mathcal I/2)d\kappa^2$。相位方向取代表速度 $v_s$，先去共同相位使 $\sum p_sv_s=0$，固定隐藏角速度 $\sum d_sv_s=\dot\chi$。Cauchy–Schwarz 给

$$
\dot\chi^2
=\left(\sum_s\frac{d_s}{\sqrt{p_s}}\sqrt{p_s}v_s\right)^2
\le\mathcal I\sum_s p_sv_s^2.
$$

取

$$
v_s=\frac{d_s}{p_s\mathcal I}\dot\chi
$$

达到等号。它与共同相位及三个位置角方向都正交，因为对于 $f=1,x,y,z$ 均有

$$
\sum_s p_sv_sf_s=\frac{\dot\chi}{\mathcal I}\sum_s d_sf_s=0.
$$

所以它确是完整位置标架商中的最短水平代表，相位度量项为 $2\dot\chi^2/\mathcal I$。复振幅微分的概率—相位混合内积纯虚，实度量无交叉项，得到式 (C74.3) 第二式。这也逐项核定相对于 C-14.2 的两倍尺度。

现在用命题 C-68.2 的 $d\eta=(\mathcal I/8)d\kappa$，即 $d\kappa=(8/\mathcal I)d\eta$。代入二形式与度量分别得到

$$
d\chi\wedge d\kappa=\frac8{\mathcal I}d\chi\wedge d\eta,\qquad
\frac{\mathcal I}{2}\frac{64}{\mathcal I^2}d\eta^2
+\frac2{\mathcal I}d\chi^2
=\frac2{\mathcal I}(16d\eta^2+d\chi^2).
$$

局部选择 $\chi$ 的实提升时，式 (C73.3) 给 $\log\Xi=4\eta-i\chi$ 加一个常数整倍 $2\pi i$，所以 $d\log\Xi=4d\eta-i\,d\chi$，其模平方为 $16d\eta^2+d\chi^2$。不同局部对数分支的微分相同，故度量本身良定义。证毕。

**命题 C-74.3（变量系数、周期和闭端点的边界）。** 式 (C74.4) 不是常系数的全局 Darboux 坐标表达；$\log\Xi$ 不是全局单值函数。内部约化几何不要求所有闭端点光滑，且底面条件化不能替代此固定矩商。

证明。$\mathcal I(\kappa)$ 由四个正仿射概率的倒数组成。在任一非退化纤维的任一端，至少一个底角概率趋零，故 $\mathcal I\to\infty$，而内部值有限，因而该函数不恒定。已经选定的 $\eta$ 不能在不改变坐标意义的情况下吸收式 (C74.4) 的系数。$(\chi,\kappa)$ 在局部实角图中给 Darboux 形式，但 $\chi$ 是圆周坐标，不是全局实数。绕固定 $\eta$ 的相位圆一次，$\Xi=e^{4\eta-i\chi}$ 绕原点一次，任一连续对数提升变化 $-2\pi i$，所以不存在全局单值复对数。

所选面积尺度可直接在两个模式的射影直线上核定：内部坐标为一个概率 $p\in(0,1)$ 和一个相对角 $\theta\bmod2\pi$，二形式为 $d\theta\wedge dp$，相容定向下总面积为 $2\pi$。这说的是所选标准 $\mathbb{CP}^1$ 的尺度，不是每条固定矩约化曲面面积都为 $2\pi$。在非墙条件 $X\ne Y$、$X+Y\ne r$ 下，§35.5 的正则闭曲面面积是

$$
2\pi(\kappa_+-\kappa_-).
$$

本章的所有椭圆与换元公式只需全正开圆柱。即便闭纤维相位商拓扑为球面，也不能据此宣布标准光滑圆球度量。具体地，在距端点的概率参数 $t>0$ 下，若有 $m\in\{1,2\}$ 个底角同时消失，则 C-14.3 给 $\mathcal I=m/t+O(1)$；在本章两倍尺度中，径向距离和相位圆周长分别为

$$
\varrho(t)=\int_0^t\sqrt{\mathcal I(s)/2}\,ds
=\sqrt{2mt}+O(t^{3/2}),\qquad
\ell(t)=2\pi\sqrt{2/\mathcal I(t)}
=2\pi\sqrt{2t/m}+O(t^{3/2}).
$$

其比值趋于 $2\pi/m$。单零端点给 $2\pi$，双零端点给 $\pi$；下端双零恰为 $X+Y=r$，上端双零恰为 $X=Y$。两倍度量同时乘两长度以 $\sqrt2$，不消除锥角。零概率处不使用本章的倒数或相位坐标。

最后，条件于底面是把 $\psi$ 投影到四个底面模式，再除以 $\sqrt r$；它的目标为四维复载体的射线空间 $\mathbb{CP}^3$，之后才可另指定 $\mathbb C^2\otimes\mathbb C^2$ 解释。固定矩商则保留五模式概率关系，固定三个连续均值并商掉 $T^3$，正内部为二维实圆柱。这两个操作的域、等价关系、维数和输出都不同。§35.14 的事件投影降秩结论适用于前者；它不是五模式固定矩辛约化，也不由其条件两因子例子推断物理子系统。证毕。

## 75. 四角椭圆应用的来源与适用对象

**约定 C-75.1（经典中间结果的准确归属）。** 本组椭圆、拼接和相位应用使用以下来源，所引结论不作为新的独立经典定理发表。

| 来源 | 本文实际消费的范围 |
| --- | --- |
| Dirk Hasenclever、Markus Scholz，*Comparing measures of association in 2x2 probability tables*，[arXiv:1302.6161v1](https://arxiv.org/abs/1302.6161v1)，Proposition 1、§3.1、Proposition 4 | 正二元概率表的行列重加权轨道及平衡代表；$\Omega$ 完整分类；Yule's Y 为 $(\sqrt\Omega-1)/(\sqrt\Omega+1)$，Yule's Q 为 $(\Omega-1)/(\Omega+1)$；Pearson 在对角对称平衡代表上与 Yule's Y 相等。用于 C-67 的协方差椭圆构造，不把均值 $Y$ 与 Yule's Y 混用，不将平衡充分条件误作所有相等情形的必要条件。 |
| Samuel N. Cohen、Eliana Fausti，*Hyperbolic contractivity and the Hilbert metric on probability measures*，[arXiv:2309.02413v2](https://arxiv.org/abs/2309.02413v2)，Theorem 2.4、Proposition 4.1 | Theorem 2.4 的 Birkhoff 经典 Hilbert 收缩系数为 $\tanh(\Delta/4)$；Proposition 4.1 给非负矩阵系数的交叉比表达。当前矩阵四格严格正、二维直径为 $|J|$，C-71 连接此系数与规范椭圆轴比并保留完整标量证明。该文较强的双曲距离结果不被说成本章的新收缩原理。 |
| William K. Wootters，*Entanglement of Formation of an Arbitrary State of Two Qubits*，[arXiv:quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)，式 (2) | 只用明确二部纯态的约化熵定义；在 C-73 的条件底面 $\mathbb C^2\otimes\mathbb C^2$ 上比较熵零与一。该文的一般混态纠缠形成公式不负责从经典概率供应相干、张量分解或物理子系统。 |
| 原卷 C-12.2、C-12.3、C-13.2–C-14.3 | 四角相位敏感行列式、同概率的乘积与最大纠缠例子、整周期位置相位商及水平度量。C-73 明确复用 $B_\pm$，C-74 保留旧角到新角的负号及两倍度量尺度，不把这些例子与几何重新作为独立发现。 |
| 本卷 C-60.1–C-61.3、C-64.1–C-65.2 | 实际外部条件总权进入五律，外端活动只计一次；固定均值的对数四角坐标；串并联与连通图抵消；均匀环外部 $A^{n-2}$ 的 Fibonacci 闭式。C-67、C-69、C-72 将这些已有供应连接到规范椭圆，所有来源、端点及条件事件保持相同。 |
| 《辛预测完成》§35.3–§35.7、§35.14 | 明确振幅符号、$\mathbb{CP}^1$ 辛面积 $2\pi$ 的尺度、真正的固定矩 $T^3$ 约化、正内部度量、局部复对数与事件条件化的区别。精确参数字典为式 (C74.1)，椭圆换元为式 (C74.4)。 |

**约定 C-75.2（由关系而非形状辨认对象）。** 当前普通数学应用的三条对应为

$$
\begin{aligned}
\text{同源底面正表}
&\longmapsto\Omega
\longmapsto\eta=\tfrac18\log\Omega
\longmapsto\text{带标记规范关联椭圆},\\
\text{有限边界权及实际接缝}
&\longmapsto H_1\odot H_2\ \text{或}\ H_1WH_2
\longmapsto\text{相加或保留偏置的递推},\\
\text{另给的五模式复振幅}
&\longmapsto\Xi=e^{4\eta-i\chi}
\longmapsto\text{规范椭圆模参数与周期相位}.
\end{aligned}
$$

第一条中的圆表示底面条件独立，不表示无条件端点独立、没有外路或全部五概率已知。第二条中并联有 $\eta$ 加法，平衡串联有带符号 $\rho_*$ 乘法，一般串联需 $(\eta,h_L,h_R)$，完整质量还需 $c_0$；它们不能相互替换。第三条中 $\Xi$ 在固定均值及声明的相位商后才是完整坐标，不是全部原始振幅的编码。

直接线性像的椭圆保留欧氏基及奇异值，规范关联椭圆保留行列比较及轴标签，约化几何还保留复振幅、位置相位作用和尺度。它们之间的对应均由上面的公式、假设和证明承担；相同外形本身不识别来源、操作或物理实现。经典公式在这里提供中间结构，源特定的综合应用不据此主张世界首创、原生操作实现或新的物理定律。

## 追加锚（本行以下为增补区）
