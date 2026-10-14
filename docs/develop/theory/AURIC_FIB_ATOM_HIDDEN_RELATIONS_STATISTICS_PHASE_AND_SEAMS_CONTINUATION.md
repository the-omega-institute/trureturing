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
