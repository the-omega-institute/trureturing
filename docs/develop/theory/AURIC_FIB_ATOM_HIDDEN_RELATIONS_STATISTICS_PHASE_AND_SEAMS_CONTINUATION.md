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

## 76. 椭圆读出、条件振幅与隐藏状态面的共同参数

**约定 C-76.1（全正纤维与三个不同对象）。** 固定五模式次序

$$
\Sigma=(0,1,2,3,13)
=\bigl(F[\mathrm{null}],F[1],F[2],F[3],F[1,3]\bigr),
$$

占位词依次为 $(000,100,010,001,101)$。在正交五模式载体上另给归一化纯振幅

$$
\psi_s=\sqrt{p_s}e^{-i\theta_s},\qquad
p_s>0,\qquad \sum_s p_s=1.
$$

取可见均值 $X=p_1+p_{13}$、$Y=p_3+p_{13}$、$Z=p_2$，令 $r=1-Z$、$\kappa=p_{13}$。以下均固定

$$
0<Z<1,\qquad 0<X,Y<r,\qquad
\kappa_-<\kappa<\kappa_+,
$$

$$
\kappa_-=\max(0,X+Y-r),\qquad
\kappa_+=\min(X,Y).
\tag{C76.1}
$$

C-67.1 的概率反解在这些条件下为

$$
p_\kappa=(r-X-Y+\kappa,\ X-\kappa,\ Z,\ Y-\kappa,\ \kappa).
\tag{C76.2}
$$

四底角的正性分别等价于 $\kappa>X+Y-r$、$\kappa<X$、$\kappa<Y$、$\kappa>0$，所以式 (C76.1) 是完整全正区间。它确非空：若 $X+Y\le r$，下端零而上端正；若 $X+Y>r$，由 $X,Y<r$ 得 $X+Y-r<X,Y$。四底角总质量为 $r$，中模式概率为 $Z$。

沿用 C-67、C-73 的带标记关联椭圆及复关系坐标：

$$
J=\log\frac{p_0p_{13}}{p_1p_3},\qquad
\eta=\frac J8,\qquad
\chi=\theta_0-\theta_1-\theta_3+\theta_{13}\pmod{2\pi},
$$

$$
\Xi=\frac{\psi_0\psi_{13}}{\psi_1\psi_3}
=e^{4\eta-i\chi}.
\tag{C76.3}
$$

概率关联椭圆在固定方向 $e_\pm=(1,\pm1)/\sqrt2$ 上的半轴为 $e^\eta,e^{-\eta}$，方程为

$$
e^{-2\eta}z_+^2+e^{2\eta}z_-^2=1.
\tag{C76.4}
$$

这是 C-67.2 的平衡底面协方差、定面积读出，保留的是四角比及方向标记。$\eta=0$ 对应底面条件独立，未断言无条件端点独立。以下另定义条件振幅的谱椭圆，最后研究整个固定矩相位商的度量；三者的关系为

| 对象 | 数学载体与所保留的信息 |
| --- | --- |
| 带标记概率关联椭圆 | 正底面表的行列重加权类；半轴保留 $\eta$ |
| 条件底面振幅矩阵及其谱椭圆 | 明确指定的两因子纯态；同时依赖概率与相位 |
| 隐藏状态面 | 五模式固定矩层再除去占位相位；坐标 $(\kappa,\chi)$ 连同指定度量 |

共用参数不识别这些操作，也不自动供应物理子系统或距离。

**定义 C-76.2（条件底面、精确基序与商不变量）。** 条件于底面事件 $s\ne2$，将四个模式识别为

$$
0\leftrightarrow |0\rangle_A|0\rangle_B,\quad
1\leftrightarrow |1\rangle_A|0\rangle_B,\quad
3\leftrightarrow |0\rangle_A|1\rangle_B,\quad
13\leftrightarrow |1\rangle_A|1\rangle_B.
\tag{C76.5}
$$

因此按张量积标准次序 $(00,01,10,11)$ 写的系数向量是
$(\psi_0,\psi_3,\psi_1,\psi_{13})/\sqrt r$；它不同于删掉中模式后的原标签次序 $(0,1,3,13)$。行指标为 $A$、列指标为 $B$，二者均按 $0,1$ 排列，矩阵为

$$
\mathsf B=\frac1{\sqrt r}
\begin{pmatrix}\psi_0&\psi_3\\ \psi_1&\psi_{13}\end{pmatrix},
\qquad
\operatorname{Tr}(\mathsf B\mathsf B^\dagger)=1,\qquad
\mathcal C=2|\det\mathsf B|.
\tag{C76.6}
$$

这里的 $\mathsf B$ 依赖代表元。具体地，C-73.4 的共同及占位相位作用
$\theta_s\mapsto\theta_s+\gamma_0+x_s\gamma_X+y_s\gamma_Y+z_s\gamma_Z$
使

$$
\mathsf B\longmapsto e^{-i\gamma_0}
\begin{pmatrix}1&0\\0&e^{-i\gamma_X}\end{pmatrix}
\mathsf B
\begin{pmatrix}1&0\\0&e^{-i\gamma_Y}\end{pmatrix}.
\tag{C76.7}
$$

底面上 $z_s=0$，故 $\gamma_Z$ 不出现。这是整体相位和左右对角酉变换；矩阵本身一般变化，但行列式模与奇异值不变。因此 $\mathcal C$ 及奇异值下降到声明的五模式相位商。这里允许的相位变换与 C-67.4 的正行列重加权不同：前者保留每个概率，后者一般改变概率。

经典中间定义取自 Wootters，*Entanglement of Formation of an Arbitrary State of Two Qubits*，[arXiv:quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)，式 (2)、(6)–(8)。对归一化两因子纯态 $|\varphi\rangle$，其 concurrence 为
$|\langle\varphi|(\sigma_y\otimes\sigma_y)|\overline\varphi\rangle|$。
在式 (C76.5) 的标准基上代入 $\sigma_y|0\rangle=i|1\rangle$、
$\sigma_y|1\rangle=-i|0\rangle$，得到 $2|\det\mathsf B|$，与原卷 C-12.2 一致。
本处只消费纯态公式，不调用一般混态的优化结论。

归一化也直接证明取值范围。设 $\lambda_1,\lambda_2$ 是正半定矩阵
$\mathsf B\mathsf B^\dagger$ 的特征值，则

$$
\lambda_1,\lambda_2\ge0,\qquad \lambda_1+\lambda_2=1,\qquad
\mathcal C^2=4\lambda_1\lambda_2
=1-(\lambda_1-\lambda_2)^2.
\tag{C76.8}
$$

故 $0\le\mathcal C\le1$。$\mathcal C=0$ 恰为非零矩阵 $\mathsf B$ 秩一，即条件纯态为乘积态；
$\mathcal C=1$ 恰为两特征值均为 $1/2$，即两个 Schmidt 系数相等。
约化态实际为 $\rho_A=\mathsf B\mathsf B^\dagger$、
$\rho_B=\mathsf B^{\mathsf T}\overline{\mathsf B}$；后者与
$\mathsf B^\dagger\mathsf B$ 互为转置，有相同谱。其纯态熵为
$-\sum_j\lambda_j\log_2\lambda_j$，零谱项按连续值零处理。
二元熵在 $\lambda_1=1/2$ 取最大值一：其内部导数为
$\log_2((1-\lambda_1)/\lambda_1)$，在该点左正右负。这说明“最大纠缠”在此指声明的二元因子纯态，而非整个五维空间的无条件张量分解。

## 77. 椭圆伸缩、相位平方和与完整谱读出

**命题 C-77.1（同一全正纤维上的归一化平方和）。** 在 C-76 的条件下，令
$\mathscr R=\sqrt{p_0p_1p_3p_{13}}>0$。则

$$
\mathcal C^2=
\frac{16\mathscr R}{r^2}
\left(\sinh^2(2\eta)+\sin^2\frac\chi2\right),
\qquad
\mathcal C=0\ \Longleftrightarrow\
\eta=0,\ \chi=0\pmod{2\pi}.
\tag{C77.1}
$$

这是 C-12.2、C-73.4 的相位敏感行列式在带标记椭圆坐标和纯态 concurrence 归一化中的应用。

证明。令 $a=\sqrt{p_0p_{13}}$、$b=\sqrt{p_1p_3}$。实际复乘积差为

$$
r\det\mathsf B
=e^{-i(\theta_1+\theta_3)}(ae^{-i\chi}-b).
$$

去掉共同相位后，

$$
\begin{aligned}
\mathcal C^2
&=\frac4{r^2}|ae^{-i\chi}-b|^2,\\
|ae^{-i\chi}-b|^2
&=a^2+b^2-2ab\cos\chi
=(a-b)^2+4ab\sin^2(\chi/2).
\end{aligned}
$$

由 $a/b=e^{4\eta}$ 得
$a=\sqrt{ab}\,e^{2\eta}$、$b=\sqrt{ab}\,e^{-2\eta}$，所以
$a-b=2\sqrt{ab}\sinh(2\eta)$。再用 $ab=\mathscr R$ 即得全部系数。
正性使前因子严格正，两平方同时零恰要求 $\eta=0$ 和 $\chi=0\bmod2\pi$。
因而概率椭圆成为圆只消去幅度不平衡项，四角相位不闭合项仍可非零。证毕。

**命题 C-77.2（同概率圆的连续相位族及三种谱图）。** 全五态纯振幅族

$$
\psi(\chi)=\frac1{\sqrt5}(1,1,1,1,e^{-i\chi})
\tag{C77.2}
$$

满足 $p_s=1/5$、$X=Y=2/5$、$Z=1/5$、$r=4/5$、
$\kappa=1/5$、$\eta=0$。它的概率关联图恒为圆，但条件底面矩阵和 concurrence 为

$$
\mathsf B(\chi)=\frac12\begin{pmatrix}1&1\\1&e^{-i\chi}\end{pmatrix},
\qquad
\mathcal C(\chi)=\left|\sin\frac\chi2\right|.
\tag{C77.3}
$$

定义谱椭圆为两个半轴分别取 $\mathsf B$ 的奇异值 $s_+\ge s_-\ge0$ 的椭圆；
允许 $s_-=0$ 时退化为线段。一般 C-76 条件纯态都有

$$
s_\pm^2=\frac{1\pm\sqrt{1-\mathcal C^2}}2.
\tag{C77.4}
$$

证明。式 (C77.2) 直接给所有概率和矩。条件化除以 $\sqrt{4/5}$ 得式 (C77.3) 的矩阵；
其行列式为 $(e^{-i\chi}-1)/4$，故 concurrence 为所列绝对正弦。
对一般矩阵，$\mathsf B\mathsf B^\dagger$ 的迹为一、行列式为
$|\det\mathsf B|^2=\mathcal C^2/4$，特征多项式为
$\lambda^2-\lambda+\mathcal C^2/4$。求根给式 (C77.4)，取非负平方根即为奇异值。
这一步是二阶正矩阵的经典谱计算，在这里连接同一概率椭圆上的相位族：

| 隐藏相位 $\chi$ | 概率关联图 | $\mathcal C$ | $(s_+^2,s_-^2)$ | 谱半轴 $(s_+,s_-)$ 及图形 |
| --- | --- | ---: | --- | --- |
| $0$ | 圆，半轴 $(1,1)$ | $0$ | $(1,0)$ | $(1,0)$，线段 |
| $\pi/2$ | 圆，半轴 $(1,1)$ | $1/\sqrt2$ | $((2+\sqrt2)/4,(2-\sqrt2)/4)$ | $(\sqrt{2+\sqrt2}/2,\sqrt{2-\sqrt2}/2)$，非退化椭圆 |
| $\pi$ | 圆，半轴 $(1,1)$ | $1$ | $(1/2,1/2)$ | $(1/\sqrt2,1/\sqrt2)$，圆 |

第一行和第三行复用 C-73.3 的两端见证，整族给它们之间的连续谱变化。
概率圆表达标准化底面条件独立；谱圆表达两个 Schmidt 系数相等。
前者的朝向在 $\eta=0$ 时不可辨，后者的谱仍随 $\chi$ 改变，故 $\chi$ 不能解释为概率圆的朝向。
相同概率表另可供应可分的经典对角混合
$\frac14\sum_{a,b}|ab\rangle\langle ab|$；纯相干制备是本命题的实质假设。证毕。

## 78. 相位操作、两份联合投影与占位标签

**命题 C-78.1（保持五概率的指定相位操作）。** 对实际五模式基施加

$$
U_\tau=\operatorname{diag}(1,1,1,1,e^{-i\omega\tau}),
\qquad \omega\in\mathbb R.
\tag{C78.1}
$$

则各概率、三个可见均值及 $\kappa$ 不变，而
$\chi(\tau)=\chi(0)+\omega\tau\bmod2\pi$。
对式 (C77.2) 中 $\chi(0)=0$ 的均匀初态，

$$
\mathcal C(\tau)=|\sin(\omega\tau/2)|.
\tag{C78.2}
$$

证明。最后一个振幅乘 $e^{-i\omega\tau}$，在 $\psi_s=\sqrt{p_s}e^{-i\theta_s}$ 的约定下
正是 $\theta_{13}$ 增加 $\omega\tau$。模平方不变，四角交替和只增加同一项。
代入式 (C77.3) 得 concurrence。与[《辛预测完成》§35.8](SYMPLECTIC_PREDICTIVE_COMPLETION.md#358-目标的四角差与隐藏角的-hamilton-响应)的精确对应为

$$
(f_0,f_1,f_2,f_3,f_{13})=(0,0,0,0,\omega),\quad
H_f=\omega\kappa,\quad J_f=\omega,\quad
\iota_{X_H}\omega_{\rm red}=dH.
$$

该约定下 $\omega_{\rm red}=d\chi\wedge d\kappa$，故
$\dot\chi=\partial_\kappa H=\omega$、$\dot\kappa=-\partial_\chi H=0$。
$\omega$ 在此为实参数，$\omega_{\rm red}$ 为二形式；$\tau$ 是操作参数，未自动指定为物理时间。
式 (C78.2) 的正弦简式只对所述均匀初态成立，一般初态应将变化后的 $\chi$ 代入式 (C77.1)。证毕。

**假设 C-78.2（实际同一纯态的两份资源与明确仪器）。** 独立制备两份相同的实际纯态
$|\psi\rangle\otimes|\psi\rangle$，其中每份均满足 C-76，并另供下面的联合投影。
“相同”指同一个纯态射线及同一占位相位参照，不能只要求两份有相同五概率、相同商坐标而允许不同局部重相位。
此假设供应两份制备，不要求复制任意未知态。

**命题 C-78.3（四项投影、总占位守恒与读出边界）。** 定义

$$
|\Omega\rangle=\frac12
\bigl(|0,13\rangle+|13,0\rangle-|1,3\rangle-|3,1\rangle\bigr),
\qquad P=|\Omega\rangle\langle\Omega|.
\tag{C78.3}
$$

则 $\|\Omega\|=1$，在假设 C-78.2 的输入上

$$
\langle\Omega|\psi\otimes\psi\rangle
=\psi_0\psi_{13}-\psi_1\psi_3=r\det\mathsf B,\qquad
\Pr(P)=\frac{r^2\mathcal C^2}{4}.
\tag{C78.4}
$$

记单份占位算子为 $N_x,N_y,N_z$，对角元依次是
$x=(0,1,0,0,1)$、$y=(0,0,0,1,1)$、$z=(0,0,1,0,0)$；
两份总占位为 $N_a^{\rm tot}=N_a\otimes I+I\otimes N_a$。则

$$
[P,N_x^{\rm tot}]=[P,N_y^{\rm tot}]=[P,N_z^{\rm tot}]=0.
\tag{C78.5}
$$

若仪器明确取投影 Lüders 的未归一化两分支

$$
\mathcal L_1(\sigma)=P\sigma P,\qquad
\mathcal L_0(\sigma)=(I-P)\sigma(I-P),
\tag{C78.6}
$$

则各分支不把一个总占位联合本征空间送入另一个，非选择性输出
$\mathcal L_1(\sigma)+\mathcal L_0(\sigma)$ 保留完整总占位联合分布。
后选择可以重加权这些标签，且单份一般不保留原固定均值纤维。

证明。四个有序基向量两两正交，故四个系数模平方之和为一。
取内积所得四项中，同号的两个乘积相等，系数 $1/2$ 抵消重复次数，得到式 (C78.4)。
四个向量的总占位都是 $(1,1,0)$，所以
$N_a^{\rm tot}|\Omega\rangle=\nu_a|\Omega\rangle$，其中 $\nu=(1,1,0)$。
由自伴性，同样有 $\langle\Omega|N_a^{\rm tot}=\nu_a\langle\Omega|$，
从而 $N_a^{\rm tot}P=PN_a^{\rm tot}=\nu_aP$。

令 $Q_\nu$ 为任意总占位联合谱投影。它与 $P$、$I-P$ 对易；
两分支 Kraus 算子均为块对角，故不会转移标签。
对任意密度算子 $\sigma$，迹的循环性及 $P^2=P$ 给

$$
\begin{aligned}
\operatorname{Tr}\bigl(Q_\nu(\mathcal L_1+\mathcal L_0)(\sigma)\bigr)
&=\operatorname{Tr}\bigl((PQ_\nu P+(I-P)Q_\nu(I-P))\sigma\bigr)\\
&=\operatorname{Tr}(Q_\nu\sigma).
\end{aligned}
$$

这是非选择性联合分布守恒。单一分支再除以成功概率会改变标签权重：
成功分支仅含 $(1,1,0)$。特别地，若成功概率正，成功后态为 $P$，
四项的另一份标签互异，取任一份的偏迹会消去全部交叉项，得到

$$
\operatorname{Tr}_2P=\operatorname{Tr}_1P
=\frac14\bigl(|0\rangle\langle0|+|1\rangle\langle1|
+|3\rangle\langle3|+|13\rangle\langle13|\bigr).
$$

每份的三个占位均值因而变为 $(1/2,1/2,0)$，与假设中的 $Z>0$ 已不同。
因此“保留总占位标签”不等于两份各自留在原 $(X,Y,Z)$ 纤维。
对易效果本身也不规定任意实现仪器的后态；上述结论使用了式 (C78.6) 的具体两分支。

式 (C77.1) 表明此概率关于 $\chi\mapsto-\chi$ 为偶函数；
它读取的是行列式模平方，不能恢复有向相位。均匀族中
$\chi=\pi/2$ 与 $-\pi/2$ 的 $\Xi$ 不同而此概率相同；
$\chi=0$ 与 $\pi$ 的概率则分别为零与 $4/25$。
原卷 C-15.2 的两种带参照设置可分别读复交叉项的实部和虚部；
这里的单个四项投影并不替代那套有向读出。证毕。

数学引文与归一化对应。Aolita、Mintert，*Measuring multipartite concurrence with a single factorizable observable*，
[arXiv:quant-ph/0608012v2](https://arxiv.org/abs/quant-ph/0608012v2)，式 (1)–(2)，给纯态两份表示
$C_N^2=\langle\varphi|^{\otimes2}A|\varphi\rangle^{\otimes2}$。
在两因子二元情形，其求和只剩两个反对称投影，$A=4P_-^A\otimes P_-^B$。
准确的因子重排为

$$
R:\ |a,b\rangle\otimes|a',b'\rangle
\longmapsto |a,a'\rangle\otimes|b,b'\rangle.
$$

设 $|\varepsilon\rangle=(|01\rangle-|10\rangle)/\sqrt2$。
按式 (C76.5) 展开得

$$
R|\Omega\rangle=|\varepsilon\rangle_{AA'}\otimes|\varepsilon\rangle_{BB'},
\qquad RPR^\dagger=P_-^A\otimes P_-^B.
\tag{C78.7}
$$

在两份已归一化条件底面态上，故 $\Pr(P)=\mathcal C^2/4$。
原五态每份落在底面的概率为 $r$，两份独立给 $r^2$，恢复式 (C78.4)。
这只在底面双副本子空间使用 $R$，不把整个五维空间写成两个二元因子。
反对称投影的经典先例与本章投影归一化直接相符。

Romero、López、Lastra、Solano、Retamal，*Direct measurement of concurrence for atomic two-qubit pure states*，
[arXiv:quant-ph/0611016v1](https://arxiv.org/abs/quant-ph/0611016v1)，式 (2)–(5)，
研究另一个包含局部操作、CNOT 和旋转的两份电路。其
$A_-=c_1c_2-c_0c_3$、$P_{gggg}=|A_-|^2/2=\mathcal C^2/8$。
它提供两份纯态 concurrence 测量的背景，不能把它的特定输出概率认作式 (C78.4)。
这些文献及本章数学投影均不供应 FIB 原生仪器实现。

## 79. 所选隐藏状态度量的曲率与固定底面质量的锐界

**约定 C-79.1（实际约化供应与尺度字典）。** 在 C-76 的全正固定矩层上，采用
[《辛预测完成》§35.5–35.7](SYMPLECTIC_PREDICTIVE_COMPLETION.md#355-固定可见均值后的真正辛约化)
及 C-74 已指定的几何：归一化五振幅先按共同相位成为射线，再固定 $(X,Y,Z)$，
最后除去占位 $T^3$ 作用。内部为
$(\kappa_-,\kappa_+)\times(\mathbb R/2\pi\mathbb Z)$。
令

$$
\mathcal I=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}.
$$

与旧 HiddenRelations 相位和尺度的对应，以及与《辛预测完成》的对数坐标对应，完整写为

$$
\theta_s^{\rm old}=-\theta_s,\qquad
\Phi_{\rm old}=-\chi,\qquad g_{\rm SP}=2g_{\rm old},
\qquad
J=\tau_{\rm SP},\qquad \frac J2=\eta_{\rm SP}=4\eta.
\tag{C79.1}
$$

同一振幅仍是 $\psi_s=\sqrt{p_s}e^{-i\theta_s}$；角符号对应不对状态作额外复共轭。
选定约化结构为

$$
g=g_{\rm SP,red}
=\frac{\mathcal I}{2}\,d\kappa^2+\frac2{\mathcal I}\,d\chi^2,
\qquad \omega_{\rm red}=d\chi\wedge d\kappa.
\tag{C79.2}
$$

这里的 $2$ 固定在来源所选的标准射影直线辛面积 $2\pi$ 的尺度上。
概率方向 $dp_s=(1,-1,0,-1,1)_s\,d\kappa$ 给第一系数；
相位方向的最短水平代表 $v_s=d_s/(p_s\mathcal I)$ 给第二系数，完整最小化及占位正交性已由 C-74.2 供应。
这不是五概率的唯一几何后果。将度量整体乘常数会反向缩放高斯曲率，故下面界值始终附带式 (C79.2)。

**命题 C-79.2（四角信息控制的曲率表达）。** 令 $f=2/\mathcal I$，则

$$
g=\frac{d\kappa^2}{f(\kappa)}+f(\kappa)d\chi^2,\qquad
\mathcal K=-\frac12 f''(\kappa)
=\frac{\mathcal I\mathcal I''-2(\mathcal I')^2}{\mathcal I^3}.
\tag{C79.3}
$$

证明。在内部引入径向弧长 $s$，$ds=d\kappa/\sqrt f$，并令
$h(s)=\sqrt{f(\kappa(s))}$。于是 $g=ds^2+h(s)^2d\chi^2$。
旋转对称度量的经典曲率公式在这里可由连接直接核定：
非零 Christoffel 符号为
$\Gamma^s_{\chi\chi}=-hh'$、
$\Gamma^\chi_{s\chi}=\Gamma^\chi_{\chi s}=h'/h$，
所以 $R_{s\chi s\chi}=-hh''$，除以度量行列式 $h^2$ 得
$\mathcal K=-h''/h$。此处 $h'$ 为对 $s$ 求导。链式法则给

$$
\frac{dh}{ds}=\frac{f'}2,\qquad
\frac{d^2h}{ds^2}=\frac{f''\sqrt f}{2}.
$$

故 $\mathcal K=-f''/2$。再由
$f'=-2\mathcal I'/\mathcal I^2$、
$f''=-2\mathcal I''/\mathcal I^2+4(\mathcal I')^2/\mathcal I^3$
得到第二式。曲率计算使用整个度量，不能仅从某个椭圆外形或坐标中的双曲函数判断符号。证毕。

**定理 C-79.3（固定 $r$ 的最佳正曲率下界及完整等号条件）。** 对每个满足 C-76 的内部点，

$$
\mathcal K\ge\frac2r>0.
\tag{C79.4}
$$

在某个内部点取等号，当且仅当该固定均值纤维满足 $X=Y=r/2$；
此时对全部内部 $\kappa$ 及全部 $\chi$ 均取等号。因此对每个固定 $r\in(0,1)$，
$2/r$ 是跨越该 $r$ 下所有允许均值和内部状态的最佳下界。

证明。以下求和仅遍历四底角，顺序为 $(0,1,3,13)$，置

$$
d=(1,-1,-1,1),\qquad
A_2=\sum_s\frac{d_s}{p_s^2},\qquad
A_3=\sum_s\frac1{p_s^3},\qquad
\beta=\frac{A_2}{\mathcal I}.
$$

固定均值时 $p_s'=d_s$，所以
$\mathcal I'=-A_2$、$\mathcal I''=2A_3$。
将平方展开，不遗漏交叉项，得

$$
\begin{aligned}
S&:=\sum_s\frac{(d_s-\beta p_s)^2}{p_s^3}\\
&=A_3-2\beta A_2+\beta^2\mathcal I
=A_3-\frac{A_2^2}{\mathcal I},\\
\mathcal K&=\frac{2S}{\mathcal I^2}.
\end{aligned}
\tag{C79.5}
$$

令 $u_s=(d_s-\beta p_s)/p_s^{3/2}$、$v_s=d_s\sqrt{p_s}$。
因 $\sum_s d_s=0$、$d_s^2=1$、$\sum_s p_s=r$，有

$$
\sum_su_sv_s
=\sum_s\left(\frac1{p_s}-\beta d_s\right)=\mathcal I,
\qquad
\sum_su_s^2=S,\qquad \sum_sv_s^2=r.
$$

加权 Cauchy–Schwarz 因此给
$\mathcal I^2\le Sr$，代入式 (C79.5) 得下界。
这是对任意正参数的证明，未用有限样本替代不等式。

等号恰要求 $u=cv$，且内积关系强制

$$
c=\frac{\mathcal I}{r}>0,\qquad
d_s-\beta p_s=c\,d_s p_s^2.
\tag{C79.6}
$$

对 $d_s=1$，正概率满足 $cp_s^2+\beta p_s-1=0$；
对 $d_s=-1$，满足 $cp_s^2-\beta p_s-1=0$。
两式的常数项均为 $-1$、首项系数 $c>0$，
根的乘积为 $-1/c<0$，判别式 $\beta^2+4c>0$，
所以各有且仅有一个正根，分别为

$$
\frac{-\beta+\sqrt{\beta^2+4c}}{2c},\qquad
\frac{\beta+\sqrt{\beta^2+4c}}{2c}.
$$

同号的两个概率必须相等：
$p_0=p_{13}$、$p_1=p_3$。由式 (C76.2)，它们依次等价于
$X+Y=r$、$X=Y$，合起来恰为 $X=Y=r/2$。

反之，若 $p_0=p_{13}=a$、$p_1=p_3=b$，则
$a,b>0$、$r=2(a+b)$，

$$
\mathcal I=\frac2a+\frac2b,\qquad
c=\frac{\mathcal I}{r}=\frac1{ab},\qquad
\beta=\frac{2/a^2-2/b^2}{2/a+2/b}=\frac1a-\frac1b.
$$

于是 $1-\beta a=a/b=ca^2$、
$-1-\beta b=-b/a=-cb^2$，确满足全部等号方程。
在对称均值下 $a=\kappa$、$b=r/2-\kappa$，每个内部 $\kappa$ 都满足；
度量与曲率又独立于 $\chi$。对每个固定 $r$ 可选此纤维取等，证明锐性。证毕。

命题 C-79.2 与定理 C-79.3 的解释边界为：$\sinh,\cosh,\tanh$ 可以出现在概率伸缩及相关读数的参数化中，
但函数形状不决定度量曲率。式 (C79.2) 所选状态面恰有严格正曲率。
这里的最佳界是固定底面质量 $r=1-Z$ 的界，不能省去尺度与固定 $r$ 的量词。

## 80. 零支撑端点的解析极坐标与锥形延伸

**命题 C-80.1（端点多重数、有限径向距离与伸缩发散）。** 在完整区间两端，
令 $m_-,m_+$ 为归零底角数，则

$$
m_-=2\ \Longleftrightarrow\ X+Y=r,\qquad
m_+=2\ \Longleftrightarrow\ X=Y,
\qquad m_\pm\in\{1,2\}.
\tag{C80.1}
$$

若距所考察端点的向内概率差为 $\delta>0$、该端多重数为 $m$，则

$$
\mathcal I=\frac m\delta+O(1),\qquad
f=\frac{2\delta}{m}+O(\delta^2),\qquad
\rho(\delta):=\int_0^\delta\frac{du}{\sqrt{f(u)}}
=\sqrt{2m\delta}+O(\delta^{3/2}).
\tag{C80.2}
$$

这里 $f(u)$ 表示用该端向内坐标写的同一函数。相位圆周长
$\ell=2\pi\sqrt f$ 满足 $\ell/\rho\to2\pi/m$。
下端 $\eta\to-\infty$、上端 $\eta\to+\infty$，而两端均在有限径向距离。

证明。下端若 $X+Y<r$，只有 $p_{13}=0$；若 $X+Y>r$，
只有 $p_0=0$；若相等，则二者同时为零，其他底角为 $X,Y>0$。
上端若 $X<Y$，只有 $p_1=0$；若 $Y<X$，只有 $p_3=0$；
若相等则二者同时为零，余下底角为 $r-X,X>0$。
严格条件 $0<X,Y<r$ 排除了第三个底角同时为零。

每个归零概率在向内坐标中都恰为 $\delta$，其余概率在该端有正极限，
所以其倒数之和为有界函数，给 $\mathcal I=m/\delta+O(1)$。
倒数展开得到 $f$ 的首项。于是
$f^{-1/2}=\sqrt{m/2}\,\delta^{-1/2}(1+O(\delta))$，
积分给 $\rho$，特别是长度有限。圆周长为
$2\pi\sqrt{2\delta/m}(1+O(\delta))$，与径向距离相除得 $2\pi/m$。
下端 $p_0p_{13}\to0$ 而 $p_1p_3$ 有正极限；
上端相反，故由 $\eta=J/8$ 得两个发散方向。
概率关联椭圆长短轴比 $e^{2|\eta|}$ 因而无界，
但这不是隐藏度量距离无界的证据。证毕。

**定理 C-80.2（单零端点的真正光滑性与双零的半周商）。** 对式 (C79.2) 的每一端，
径向坐标中的函数 $h(\rho)=\sqrt{f(\delta(\rho))}$ 有收敛的奇解析展开

$$
h(\rho)=\frac{\rho}{m}+\rho^3 H(\rho^2),
\tag{C80.3}
$$

其中 $H$ 在零附近实解析。因此 $m=1$ 时该端可加为普通光滑点；
$m=2$ 时角向双覆盖加端点后光滑，原度量是其旋转半周商，锥角为 $\pi$。
仅由圆周长与半径之比趋于 $2\pi$ 不足以推出光滑性，本结论使用下述解析性证明。

证明。其他非零概率是 $a_j+\epsilon_j\delta$，其中 $a_j>0$、
$\epsilon_j=\pm1$，所以在足够小的实邻域内

$$
q(\delta):=\sum_{\text{非零底角 }j}\frac1{a_j+\epsilon_j\delta}
\quad\hbox{实解析},\qquad
f(\delta)=\frac{2\delta}{m+\delta q(\delta)}
=\delta F(\delta),\quad F(0)=\frac2m>0.
\tag{C80.4}
$$

这给 $f$ 在端点的有理解析延伸，不仅给渐近首项。
令 $t=\sqrt\delta$，把径向积分改写为

$$
\rho(t)=\int_0^t\frac{2\,dv}{\sqrt{F(v^2)}}.
\tag{C80.5}
$$

因 $F(0)>0$，选择正平方根后被积函数为偶解析函数；
$\rho(t)$ 因而为奇解析函数，且
$\rho'(0)=2/\sqrt{F(0)}=\sqrt{2m}>0$。
实解析逆函数定理给局部解析逆 $t=t(\rho)$。
由原函数的奇性和逆的唯一性，$t(-\rho)=-t(\rho)$，
故 $t(\rho)$ 也奇解析，首项 $\rho/\sqrt{2m}$。
于是

$$
h(\rho)=t(\rho)\sqrt{F(t(\rho)^2)}
$$

奇解析且首项为 $\rho/m$，其余奇次幂可写成式 (C80.3)。
在穿孔端邻域内度量恰为 $d\rho^2+h(\rho)^2d\chi^2$。

若 $m=1$，令 $x=\rho\cos\chi$、$y=\rho\sin\chi$。
保留完整角向张量因子，恒等式为

$$
d\rho^2+h^2d\chi^2
=dx^2+dy^2+
\frac{h^2-\rho^2}{\rho^4}(x\,dy-y\,dx)^2.
\tag{C80.6}
$$

由 $h=\rho+\rho^3H(\rho^2)$，
$(h^2-\rho^2)/\rho^4=2H(\rho^2)+\rho^2H(\rho^2)^2$，
它是 $\rho^2=x^2+y^2$ 的解析函数。
右边所有张量系数都在 $(0,0)$ 解析延伸，原点值为欧氏内积，近邻仍正定。
这证明真正的 Cartesian 光滑性，而非仅确认总角。

若 $m=2$，取角向双覆盖，令 $\chi=2\phi$ 且 $\phi$ 周期为 $2\pi$。
拉回度量为

$$
d\rho^2+(2h(\rho))^2d\phi^2,\qquad
2h(\rho)=\rho+2\rho^3H(\rho^2).
$$

对 $2h$ 重复式 (C80.6) 的论证，覆盖面加原点后光滑且解析。
覆盖变换 $\phi\mapsto\phi+\pi$ 是该旋转对称度量的等距半周旋转，
在原点有固定点，商正好恢复 $\chi\bmod2\pi$ 的原穿孔度量。
所以原端点是角 $\pi$ 的锥点；不是原角周期下的普通光滑点。证毕。

由式 (C80.4)，$f''$ 在每端都有有限极限；内部又是正分母有理函数的导数。
因此在固定纤维的闭区间上 $\mathcal K=-f''/2$ 有界。
这项端点结论关于所选度量的延伸，不在零概率处继续使用 $1/p_s$、
$\arg\psi_s$ 或 $\Xi$ 作为普通坐标。

## 81. 完整 Cauchy 边界、球面拓扑与曲率缺角

**定理 C-81.1（完备化恰加两个点）。** 赋予开圆柱
$M=(\kappa_-,\kappa_+)\times S^1$ 以内在长度距离。
式 (C79.2) 的 Cauchy 完备化在每一端恰加一点，没有其他度量边界；
两端点不同。完备化紧致，拓扑同胚于 $S^2$。

证明。置

$$
s(\kappa)=\int_{\kappa_-}^{\kappa}\frac{du}{\sqrt{f(u)}},
\qquad
T=\int_{\kappa_-}^{\kappa_+}\frac{du}{\sqrt{f(u)}}.
\tag{C81.1}
$$

两端由命题 C-80.1 可积，内部连续正，故 $0<T<\infty$。
在 $0<s<T$ 上写 $g=ds^2+h(s)^2d\chi^2$，
其中 $h>0$，且 $h(s)\to0$ 于 $s\to0,T$。
任意分段光滑曲线的长度至少为其 $s$ 坐标总变差，因此

$$
|s(p)-s(q)|\le d(p,q).
\tag{C81.2}
$$

即 $s$ 是 $1$-Lipschitz。固定角的径向线段长度恰为 $|s(p)-s(q)|$。
所以沿固定角趋向下端或上端的点列为 Cauchy 列，分别定义完备化点 $E_-,E_+$。

在下端，将两个点 $(s,\chi)$、$(t,\chi')$ 先沿径向移到
$0<u<\min(s,t)$，再沿该圆的较短弧相连，得到

$$
d((s,\chi),(t,\chi'))
\le s+t-2u+\pi h(u).
$$

令 $u\downarrow0$，右侧趋于 $s+t$。
特别地，任意 $s_n\to0$ 的点列都是 Cauchy，
且所有这样的列彼此距离趋零，代表同一点 $E_-$。
结合式 (C81.2) 及固定角径向列，准确地有
$d((s,\chi),E_-)=s$。
同理 $d((s,\chi),E_+)=T-s$。这是有限径向尾长和消失端圆周长共同给出的统一结论，
没有要求角度序列收敛。

现排除其他 Cauchy 边界。若 $(s_n,\chi_n)$ 为任意 Cauchy 列，
式 (C81.2) 使 $s_n$ 收敛到某个 $s_*\in[0,T]$。
若极限为两端之一，上段已处理。若 $0<s_*<T$，
该列最终留在某个紧条带 $[\epsilon,T-\epsilon]\times S^1$。
此条带上 $h$ 的最大值有限、最小值严格正，
局部度量与普通圆柱度量互相有界比较，给相同局部拓扑。
条带的产品紧致性给收敛子列；在小坐标邻域内用路径长度上界，
该子列也按 $d$ 收敛到同一内部点。原列 Cauchy，故整列收敛到该点。
若担心内在距离路径越过条带，式 (C81.2) 保证足够短路径不能穿越一个固定正宽度的径向间隔；
所以此局部比较不会遗漏来自端部的捷径。

两端间由延伸的 $1$-Lipschitz 坐标得 $d(E_-,E_+)\ge T$，
固定角经线给反向不等式，故距离恰为 $T>0$，不能合并。
每个 $\epsilon$ 端尾距相应端点不超过 $\epsilon$，中间条带紧致；
因此完备化全有界且完备，故紧致。

更具体地，连续映射 $[0,T]\times S^1\to\overline M$ 在内部取恒等，
将两个端圆分别送到 $E_-,E_+$。端部连续性由刚证明的统一距离公式保证；
除了同一端圆内的点，没有其他识别。
它诱导紧 Hausdorff 空间间的连续双射

$$
([0,T]\times S^1)/(\{0\}\times S^1,\ \{T\}\times S^1)
\ \longrightarrow\ \overline M,
$$

故为同胚。左边是圆周的悬挂，可由
$(s,\chi)\mapsto(\sin(\pi s/T)\cos\chi,\sin(\pi s/T)\sin\chi,\cos(\pi s/T))$
显式识别为球面。此证明补足原卷 C-13.3、C-14.3 在当前尺度下的全部内在度量边界论证。证毕。

**定理 C-81.2（总面积、直接端斜率积分及全部缺角类型）。** 令
$w=\kappa_+-\kappa_-=\min\{X,Y,r-X,r-Y\}>0$，则

$$
\operatorname{Area}(\overline M)=2\pi w,\qquad
\int_M\mathcal K\,dA
=2\pi\left(\frac1{m_-}+\frac1{m_+}\right).
\tag{C81.3}
$$

两端总角为 $\alpha_\pm=2\pi/m_\pm$，缺角
$D_\pm=2\pi-\alpha_\pm$，满足

$$
\int_M\mathcal K\,dA+D_-+D_+=4\pi.
\tag{C81.4}
$$

证明。在 $(\kappa,\chi)$ 坐标中 $\det g=1$，故无向面积密度为
$dA=d\kappa\,d\chi$，等于 $|\omega_{\rm red}|$；
这里未把坐标次序的有向二形式 $d\kappa\wedge d\chi$ 与
$d\chi\wedge d\kappa$ 误认同号。积分相位周期和区间宽度即得总面积。
每个端尾面积随 $\delta$ 线性趋零，新增的两个点为零面积。
宽度公式可直接分 $X+Y\le r$、$X+Y\ge r$：
前者 $w=\min(X,Y)$，后者 $w=\min(r-X,r-Y)$，合并即四项最小值。

式 (C80.4) 是解析展开，故可对端点求导，而非对不受控的渐近余项求导。
下端向内坐标为 $\delta=\kappa-\kappa_-$，上端为 $\delta=\kappa_+-\kappa$，从而

$$
f'(\kappa_-)=\frac2{m_-},\qquad
f'(\kappa_+)=-\frac2{m_+}.
\tag{C81.5}
$$

$f''$ 在整个闭区间连续有界，故微积分基本定理和式 (C79.3) 给

$$
\begin{aligned}
\int_M\mathcal K\,dA
&=-\pi\int_{\kappa_-}^{\kappa_+}f''(\kappa)\,d\kappa\\
&=-\pi\bigl(f'(\kappa_+)-f'(\kappa_-)\bigr)
=2\pi\left(\frac1{m_-}+\frac1{m_+}\right).
\end{aligned}
$$

加两个缺角得到式 (C81.4)。完整类型如下，其中一双零行包括两种端点次序：

| 两端类型及条件 | 总面积 | 内部曲率积分 | 端点缺角总和 | 曲率加缺角 |
| --- | ---: | ---: | ---: | ---: |
| 单零、单零：$X+Y\ne r$ 且 $X\ne Y$ | $2\pi w$ | $4\pi$ | $0$ | $4\pi$ |
| 一单零、一双零：$X+Y=r$ 与 $X=Y$ 恰一成立 | $2\pi w$ | $3\pi$ | $\pi$ | $4\pi$ |
| 双零、双零：$X=Y=r/2$ | $\pi r$，此时 $w=r/2$ | $2\pi$ | $2\pi$ | $4\pi$ |

这也核对锥度量 Gauss–Bonnet 公式，但拓扑和积分已分别直接证明。为精确应用
Fang、Xu、Yang，*The Gauss-Bonnet formula of a conical metric on a compact Riemann surface*，
[arXiv:1912.01187v3](https://arxiv.org/abs/1912.01187v3)，文首定义及 Theorem，
还须核对其共形锥形和可积性条件。

在每端取穿孔邻域的等温径向变量 $q>0$ 满足
$dq/q=d\rho/h(\rho)$，并以 $z=q e^{i\chi}$ 作局部复坐标。
式 (C80.3) 给

$$
\frac1{h(\rho)}=\frac m\rho+\rho A(\rho^2),\qquad
q=c\,\rho^m e^{B(\rho^2)},\quad c>0,
$$

其中 $A,B$ 解析，可把 $B(0)$ 吸入 $c$。
度量为

$$
g=\frac{h(\rho)^2}{q^2}|dz|^2
=e^{2u(z)}|z|^{2\beta_{\rm cone}}|dz|^2,\qquad
\beta_{\rm cone}=\frac1m-1.
\tag{C81.6}
$$

确切地，
$e^{2u}=h(\rho)^2/q^{2/m}$ 在 $\rho\to0$ 时趋于
$1/(m^2c^{2/m})>0$，所以 $u$ 在端点连续，在穿孔处光滑。
内部取相容等温图，两端分别取与定向相容的 $\chi$ 或 $-\chi$，
获得紧球面上的 Riemann 曲面结构；符号选择不改变式 (C81.6)。
锥指数为 $0$ 或 $-1/2$，都严格大于 $-1$。
又因面积有限且 $\mathcal K$ 有界，$\int_M|\mathcal K|\,dA<\infty$。
这满足所引定理的 $L^1$ 曲率条件，其
$\int\mathcal K\,dA=2\pi(\chi_{\rm Euler}(S^2)+\sum\beta_{\rm cone})$
正给式 (C81.4)。该文没有替本文证明四角概率的锐界、等号条件或完备化拓扑。证毕。

## 82. 对称纤维的球面半周商与最大 concurrence

**命题 C-82.1（常曲率对称纤维的完整球面表示）。** 取
$X=Y=r/2$，令 $L=r/2>0$。则

$$
p_\kappa=(\kappa,L-\kappa,Z,L-\kappa,\kappa),
\qquad 0<\kappa<L,
$$

$$
\mathcal I=\frac2\kappa+\frac2{L-\kappa},\qquad
f=\frac{\kappa(L-\kappa)}L.
\tag{C82.1}
$$

换元

$$
\kappa=\frac L2(1-\cos\vartheta),\qquad 0<\vartheta<\pi
\tag{C82.2}
$$

给

$$
g=L\left(d\vartheta^2+\frac14\sin^2\vartheta\,d\chi^2\right),
\qquad \mathcal K=\frac1L=\frac2r.
\tag{C82.3}
$$

完备化是半径 $\sqrt L$ 的圆球绕两极旋转半周所得的度量商，
两个极点的锥角均为 $\pi$；极点距离恰为 $\pi\sqrt L$。
概率关联圆的位置为整个赤道相位圆：

$$
\eta=0\ \Longleftrightarrow\ \kappa=L/2
\ \Longleftrightarrow\ \vartheta=\pi/2,\qquad \chi\in S^1.
\tag{C82.4}
$$

证明。将对称均值代入式 (C76.2)，得到概率。
四倒数求和后取 $2/\mathcal I$，给式 (C82.1)。
式 (C82.2) 中

$$
d\kappa=\frac L2\sin\vartheta\,d\vartheta,\qquad
f=\frac L4\sin^2\vartheta,
$$

故 $d\kappa^2/f=L\,d\vartheta^2$，角向项如式 (C82.3)。
对 $f=\kappa-\kappa^2/L$ 有 $-f''/2=1/L$。
局部令 $\phi=\chi/2$，度量变成
$L(d\vartheta^2+\sin^2\vartheta\,d\phi^2)$，
是半径 $\sqrt L$ 的标准圆球度量。
但原 $\chi$ 周期为 $2\pi$，所以这里 $\phi$ 周期只有 $\pi$。
从 $\phi$ 周期为 $2\pi$ 的整圆球出发，识别 $\phi$ 和 $\phi+\pi$，
便得到原内部度量；两极由定理 C-80.2 的半周商延伸，均有角 $\pi$。
定理 C-81.1 排除其他完成点，所以这一局部表示确给整个完备化的度量商。

任一连接两极的可求长路径在内部满足
$ds\ge\sqrt L\,|d\vartheta|$。
从第一极到第二极，连续 $\vartheta$ 的总变差至少为 $\pi$，
因而长度至少 $\pi\sqrt L$；若路径经过极点，可先在
$\epsilon\le\vartheta\le\pi-\epsilon$ 截取再令 $\epsilon\downarrow0$，
仍得同一下界。固定 $\chi$ 的经线长度为
$\int_0^\pi\sqrt L\,d\vartheta=\pi\sqrt L$，达到下界。
这也与式 (C81.1) 的 $T$ 完全一致。

最后，
$p_0p_{13}/(p_1p_3)=\kappa^2/(L-\kappa)^2$，
故 $\eta=\frac14\log(\kappa/(L-\kappa))$，
零点恰为 $\kappa=L/2$，换元后即赤道。
此时 $\chi$ 仍自由遍历整个 $2\pi$ 圆周，不能把一个概率圆读数当成唯一隐藏态。
常曲率局部圆球与全局带两个锥点的半周商在这里各有明确含义。证毕。

**定理 C-82.2（纤维层面的曲率取等与最大纠缠存在性）。** 固定 C-76 的
$(X,Y,Z)$，以下三项等价：

$$
\begin{gathered}
X=Y=r/2;\\
\text{存在内部 }(\kappa,\chi)\text{ 使 }\mathcal K=2/r;\\
\text{存在内部条件底面纯态使 }\mathcal C=1.
\end{gathered}
\tag{C82.5}
$$

在这条对称纤维上，$\chi=\pi\bmod2\pi$ 的每个内部 $\kappa$ 都有 $\mathcal C=1$；
曲率则在全部内部点取等，包括 $\mathcal C=0$ 的点。

证明。第一项与第二项的等价由定理 C-79.3 的完整等号条件给出。
若 $\mathcal C=1$，式 (C76.8) 使
$\mathsf B\mathsf B^\dagger=I_2/2$。
由于 $\mathsf B$ 可逆，由
$\mathsf B\mathsf B^\dagger=I_2/2$ 左乘 $\mathsf B^{-1}$ 再右乘 $\mathsf B$，
得 $\mathsf B^\dagger\mathsf B=I_2/2$，因此另一侧约化态也为 $I_2/2$。
两侧占位为一的概率分别是

$$
(\rho_A)_{11}=\frac{p_1+p_{13}}r=\frac Xr,\qquad
(\rho_B)_{11}=\frac{p_3+p_{13}}r=\frac Yr.
$$

二者必须均为 $1/2$，故 $X=Y=r/2$。
反之，在对称纤维中 $a=\kappa$、$b=L-\kappa$，
选 $\chi=\pi$，行列式模为 $(a+b)/r=L/(2L)=1/2$，所以

$$
\mathcal C=\frac{2}{r}|-\kappa-(L-\kappa)|=1.
$$

每个内部 $\kappa$ 均可作此选择，且可由前四相位为零、最后相位为 $\pi$ 的实际五态代表实现。
这证明存在性的反向及整条相位经线结论。证毕。

**命题 C-82.3（球面坐标中的 concurrence 与唯一内部乘积点）。** 对称纤维上

$$
\begin{aligned}
\mathcal C^2
&=\frac{(2\kappa-L)^2
+4\kappa(L-\kappa)\sin^2(\chi/2)}{L^2}\\
&=1-\sin^2\vartheta\cos^2(\chi/2).
\end{aligned}
\tag{C82.6}
$$

在全正内部，唯一 $\mathcal C=0$ 的商状态为
$(\vartheta,\chi)=(\pi/2,0\bmod2\pi)$；
全部 $\mathcal C=1$ 的内部状态恰为 $\chi=\pi\bmod2\pi$。

证明。在式 (C77.1) 的乘积差展开中代入
$a=\kappa$、$b=L-\kappa$、$r=2L$，给第一行。
由
$2\kappa-L=-L\cos\vartheta$、
$4\kappa(L-\kappa)=L^2\sin^2\vartheta$，
第一行变为
$\cos^2\vartheta+\sin^2\vartheta\sin^2(\chi/2)$，即第二行。
要 $\mathcal C=0$，两个不超过一的非负因子
$\sin^2\vartheta$、$\cos^2(\chi/2)$ 的乘积必须为一，
故各自均为一，给唯一内部点。
要 $\mathcal C=1$，两因子乘积为零；内部 $\sin\vartheta>0$，
所以只能 $\cos(\chi/2)=0$，即所述整条经线。

特别地，赤道上 $\chi=0$ 与 $\chi=\pi$ 同有 $\mathcal K=2/r$，
而 concurrence 分别为零和一。这是“曲率在该点取等当且仅当该点最大纠缠”的反例；
正确等价是定理 C-82.2 的纤维对称性与最大纠缠的存在性。
沿 $\chi=\pi$ 改变内部 $\kappa$ 可以改变概率椭圆但保持最大 concurrence；
沿赤道改变 $\chi$ 可以保持概率圆但改变 concurrence。
这两个函数可以同在一个参数面上，却不能彼此替代。证毕。

## 83. 经典中间结构、来源归属与适用界限

**约定 C-83.1（本组综合推导的来源范围）。** 以下来源各承担所列数学中间结构；
归一化、参数桥和新增结论的假设仍以对应条目为准。

| 来源 | 实际使用的内容与边界 |
| --- | --- |
| 原卷 C-12.2–C-15.3；本续卷 C-67、C-68、C-73、C-74 | 四角相位行列式、同概率乘积与最大纠缠见证、全周期相位商、底面关联椭圆、水平最短度量及有限端点主项。本组保留这些供应的明确归属，连接到归一化 concurrence、固定质量锐曲率及完整解析完备化；并非重立上述先例。 |
| [《辛预测完成》§35.5–35.9](SYMPLECTIC_PREDICTIVE_COMPLETION.md#355-固定可见均值后的真正辛约化) | 真正固定矩后再取 $T^3$ 商；§35.7 的反相位、两倍度量及对数坐标尺度；§35.8 的正号角速度。§35.9 的四次不变 Hamilton 函数可改变 $\kappa$，与 C-78.1 固定对角相位操作不同；本组没有从其非线性交换推得固定五阶线性仪器。 |
| William K. Wootters，*Entanglement of Formation of an Arbitrary State of Two Qubits*，[quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)，式 (2)、(6)–(8) | 归一化二元两因子纯态的约化熵、spin-flip concurrence 及二元谱关系。本文按式 (C76.5) 对应为 $2|\det\mathsf B|$；不借一般混态结论恢复未供应的相干或张量因子。 |
| Leandro Aolita、Florian Mintert，*Measuring multipartite concurrence with a single factorizable observable*，[quant-ph/0608012v2](https://arxiv.org/abs/quant-ph/0608012v2)，式 (1)–(2) | 两份纯态及反对称子空间投影的经典关系；两二元因子时为 $4P_-^A\otimes P_-^B$。式 (C78.7) 明列重排，条件底面投影概率为 $\mathcal C^2/4$，五态无条件概率另乘 $r^2$。 |
| G. Romero、C. E. López、F. Lastra、E. Solano、J. C. Retamal，*Direct measurement of concurrence for atomic two-qubit pure states*，[quant-ph/0611016v1](https://arxiv.org/abs/quant-ph/0611016v1)，式 (2)–(5) | 两份已供应纯态经特定电路后的 $P_{gggg}=\mathcal C^2/8$。仅作两份读出背景，不替代本文四项投影的归一化或 Lüders 后态合同。 |
| Hanbing Fang、Bin Xu、Bairui Yang，*The Gauss-Bonnet formula of a conical metric on a compact Riemann surface*，[1912.01187v3](https://arxiv.org/abs/1912.01187v3)，文首锥度量定义及 Theorem | 紧 Riemann 曲面、锥指数大于 $-1$ 及相对于度量面积 $L^1$ 的曲率条件下的锥 Gauss–Bonnet。C-80、C-81 逐项给这些条件；它不是四概率曲率锐界、等号分类或本度量拓扑的来源。 |

式 (C79.5)–(C79.6) 的四角加权平方和与等号分类、它们与
式 (C82.5) 的纤维层面存在性等价，是在这里指定的五模式、矩约束及尺度下的综合推导。
Schmidt 谱、Cauchy–Schwarz、旋转对称度量曲率、解析逆函数与锥 Gauss–Bonnet
是经典中间工具；上述来源对应不作全局原创性主张。

**约定 C-83.2（两种操作及解释范围）。** 底面条件化先投影到四维复子空间、再除以
$\sqrt r$，输出为条件射线；之后才指定 $\mathbb C^2\otimes\mathbb C^2$ 的因子结构。
五模式固定矩约化则从 $\mathbb{CP}^4$ 的矩层除去占位 $T^3$，
输出二维实关系面。前者更改条件概率，后者识别相位轨道。
二者的域、等价关系及输出不同，$\mathsf B$ 仍依赖代表，
只有其 concurrence 与奇异值在所述相位商上不变。

本组的有限距离、曲率与球面拓扑全部属于式 (C79.2) 的无量纲选定度量，
concurrence 属于式 (C76.5) 的明确条件张量结构。
改变度量尺度、改变因子划分、改用混态或撤掉同态两份制备条件，
均须重新确定相应命题。这里不把曲率认作引力曲率，不将参数认作物理常数，
不从形式投影的存在推出 FIB 原生测量或未知态克隆能力。

## 追加锚（本行以下为增补区）

## 84. 隐藏宽度、底面质量与所选面积的完整字典

**约定 C-84.1（闭概率纤维与纯振幅完成）。** 沿用 C-76 的正交五模式载体，固定次序和占位词

$$
\Sigma=(0,1,2,3,13)
=\bigl(F[\mathrm{null}],F[1],F[2],F[3],F[1,3]\bigr),
\qquad (000,100,010,001,101).
$$

另给纯振幅 $\psi_s=\sqrt{p_s}e^{-i\theta_s}$，$\sum_s p_s=1$。
本组固定三个可见均值及底面质量

$$
X=p_1+p_{13},\qquad Y=p_3+p_{13},\qquad Z=p_2,\qquad
r=1-Z,\qquad 0<r<1,\quad 0<X,Y<r.
\tag{C84.1}
$$

以 $\kappa=p_{13}$ 为隐藏概率，完整反解为

$$
p_\kappa=(r-X-Y+\kappa,\ X-\kappa,\ 1-r,\ Y-\kappa,\ \kappa).
\tag{C84.2}
$$

允许合法零概率的闭纤维区间为

$$
[\kappa_-,\kappa_+],\qquad
\kappa_-=\max(0,X+Y-r),\qquad
\kappa_+=\min(X,Y).
\tag{C84.3}
$$

四底角分别非负恰给这四个不等式；中模式因 $r<1$ 严格正。
以下“全正”指五概率全正，等价于 $\kappa_-<\kappa<\kappa_+$。
零振幅处不把 $\theta_s$ 当作内在坐标，含相位的端点表达均由实际振幅或内部连续延伸解释。

**命题 C-84.2（宽度与两边缘的共同最小量）。** 定义绝对宽度 $w=\kappa_+-\kappa_-$、
相对宽度 $\nu=w/r$。则

$$
w=\min\{X,Y,r-X,r-Y\},\qquad 0<\nu\le\frac12,
$$

$$
\min\{X(r-X),Y(r-Y)\}=w(r-w).
\tag{C84.4}
$$

证明。若 $X+Y\le r$，则 $X\le r-Y$、$Y\le r-X$，故四项最小值为
$\min(X,Y)=w$。若 $X+Y\ge r$，则
$w=\min(X,Y)-(X+Y-r)=\min(r-X,r-Y)$，且这两项分别不大于 $Y,X$。
四项都正，所以 $w>0$。置

$$
u=\min(X,r-X),\qquad v=\min(Y,r-Y).
$$

则 $u,v\in(0,r/2]$，$w=\min(u,v)$，给 $\nu$ 的范围。
又 $X(r-X)=u(r-u)$、$Y(r-Y)=v(r-v)$。
对 $0\le a<b\le r/2$，

$$
b(r-b)-a(r-a)=(b-a)(r-a-b)>0.
$$

故 $t(r-t)$ 在 $[0,r/2]$ 严格递增，取最小量即得最后的精确恒等式。
特别地 $w=r/2$ 当且仅当 $X=Y=r/2$。证毕。

宽度公式的概率来源为
[《局部填充》§3.1](AURIC_FIB_ATOM_PYRAMID_LOCAL_FILLINGS_SOFT_TO_RIGID_AND_ODD_CYCLE_OBSTRUCTIONS.md#31-隐藏纤维的宽度)，
其在相位商面积中的应用由 C-81.2 给出。
$r$ 表示底面在完整五模式中的质量，$\nu$ 表示固定条件边缘后相对底面质量的余量；两者不能互相替代。

**约定 C-84.3（相位商、尺度与面积）。** 先将归一化振幅除去共同相位成为射线，
固定 $(X,Y,Z)$，再除去占位 $T^3$ 作用

$$
\theta_s\longmapsto\theta_s+\gamma_0+x_s\gamma_X+y_s\gamma_Y+z_s\gamma_Z.
$$

这里 $x=(0,1,0,0,1)$、$y=(0,0,0,1,1)$、$z=(0,0,1,0,0)$。
全正内部的剩余角为

$$
\chi=\theta_0-\theta_1-\theta_3+\theta_{13}\pmod{2\pi}.
$$

C-73.2 的整周期消相位公式给周期恰为 $2\pi$。
按 C-74、C-79 及[《辛预测完成》§35.5–35.7](SYMPLECTIC_PREDICTIVE_COMPLETION.md#355-固定可见均值后的真正辛约化)选择

$$
\omega_{\rm red}=d\chi\wedge d\kappa,\qquad
g=\frac{\mathcal I}{2}d\kappa^2+\frac2{\mathcal I}d\chi^2,\qquad
\mathcal I=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}.
\tag{C84.5}
$$

这是标准射影直线辛面积 $2\pi$ 的尺度，即原卷度量的两倍。
$\det g=1$，故 Riemann 面积密度等于 $|\omega_{\rm red}|=d\kappa\,d\chi$，
完整面积为

$$
\mathcal A=\int_{\kappa_-}^{\kappa_+}\int_0^{2\pi}d\chi\,d\kappa=2\pi w.
\tag{C84.6}
$$

两端的新增点面积为零。C-80、C-81 已证明：$X+Y=r$ 使下端双零，
$X=Y$ 使上端双零；其余端点单零。单零端点光滑，双零端点锥角为 $\pi$。
因此非墙条件 $X\ne Y$、$X+Y\ne r$ 下是光滑闭曲面面积；
墙上同一内部积分仍成立，却不把锥点变成普通光滑点。
这是一种已选择的约化几何，不由宽度另推一种维数。

在全正域，带标记概率关联椭圆继续使用

$$
\eta=\frac18\log\frac{p_0p_{13}}{p_1p_3},\qquad
\Xi=\frac{\psi_0\psi_{13}}{\psi_1\psi_3}=e^{4\eta-i\chi}.
\tag{C84.7}
$$

$\log$ 在此为自然对数。概率椭圆的标记半轴为 $e^\eta,e^{-\eta}$；
它的圆条件 $\eta=0$ 与下面条件振幅的谱圆条件不同。

## 85. 任意固定均值纤维的精确联合容量

**定义 C-85.1（明确的条件两因子结构）。** 采用 C-76.2 的对应

$$
0\leftrightarrow00,\qquad1\leftrightarrow10,\qquad
3\leftrightarrow01,\qquad13\leftrightarrow11.
$$

行指标为左因子、列指标为右因子，均按 $0,1$ 排列。条件底面纯态的标准基序
$(00,01,10,11)$ 系数向量是 $(\psi_0,\psi_3,\psi_1,\psi_{13})/\sqrt r$，故

$$
B=\frac1{\sqrt r}\begin{pmatrix}\psi_0&\psi_3\\\psi_1&\psi_{13}\end{pmatrix},
\qquad \operatorname{Tr}(BB^\dagger)=1,\qquad \mathcal C=2|\det B|.
\tag{C85.1}
$$

这是标准两二元因子纯态 concurrence：Wootters，
[quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)，式 (6)–(8)，
使用 spin-flip $|\langle\phi|(\sigma_y\otimes\sigma_y)|\bar\phi\rangle|$；
把四个标准基系数代入给 $2|\det B|$。
归一化来自四底角和为 $r$。若 $BB^\dagger$ 的谱为 $\lambda_+,\lambda_-$，
则 $\lambda_++\lambda_-=1$，$\mathcal C^2=4\lambda_+\lambda_-\le1$。

商作用把代表矩阵变成

$$
B\longmapsto e^{-i\gamma_0}
\operatorname{diag}(1,e^{-i\gamma_X})\,
B\,\operatorname{diag}(1,e^{-i\gamma_Y}).
\tag{C85.2}
$$

因左右都是酉矩阵，$\mathcal C$ 及奇异值在商上不变，$B$ 本身却一般变化。
底面上 $z_s=0$，故 $\gamma_Z$ 不作用于它。
此条件张量识别是额外数学结构；五个模式名并不自行给出两个实际物理子系统，
一般经典对角混合也不具有上述纯态公式的意义。

**定理 C-85.2（固定均值的闭容量与完整取值区间）。** 在约定 C-84.1 的全部纯态上，

$$
\mathcal C_{\max}=\frac{2\sqrt{w(r-w)}}r
=2\sqrt{\nu(1-\nu)},\qquad
\{\mathcal C\}=[0,\mathcal C_{\max}].
\tag{C85.3}
$$

这里允许闭纤维端点；它是状态集合上的结论，不是原生控制可达性的结论。

证明。左侧约化矩阵 $\rho_L=BB^\dagger$ 的对角为 $(r-X)/r,X/r$。
右侧约化矩阵为 $\rho_R=B^{\mathsf T}\bar B$，其对角为 $(r-Y)/r,Y/r$；
它与 $B^\dagger B$ 互为转置，且两侧行列式均为 $|\det B|^2$。因此分别有

$$
\begin{aligned}
\mathcal C^2
&=4\det\rho_L
=\frac{4X(r-X)}{r^2}-4|(\rho_L)_{01}|^2
\le\frac{4X(r-X)}{r^2},\\
\mathcal C^2
&=4\det\rho_R
=\frac{4Y(r-Y)}{r^2}-4|(\rho_R)_{01}|^2
\le\frac{4Y(r-Y)}{r^2}.
\end{aligned}
\tag{C85.4}
$$

C-84.2 的最小量恒等式给所需上界。下面给满足原概率约束的取等构造。

先作有限个可逆坐标重标记。交换左、右二元因子的零一标签以及交换因子，
对参数的作用分别为

$$
\begin{aligned}
L:(X,Y,\kappa)&\longmapsto(r-X,Y,Y-\kappa),\\
R:(X,Y,\kappa)&\longmapsto(X,r-Y,X-\kappa),\\
S:(X,Y,\kappa)&\longmapsto(Y,X,\kappa).
\end{aligned}
\tag{C85.5}
$$

$L$ 交换底面表的两行，$R$ 交换两列，$S$ 转置；中模式保持不动。
这些都是对五个基标签的置换，各自为对合，保持总质量、合法性、$r,w$、
行列式绝对值及谱。先把两边缘分别折到
$u=\min(X,r-X)$、$v=\min(Y,r-Y)$，再将较小者放在左边，便有

$$
X=w,\qquad Y=y,\qquad 0<w\le y\le r/2,\qquad 0\le\kappa\le w.
\tag{C85.6}
$$

单侧翻转使 $\chi$ 变号，因子交换保持 $\chi$；$0,\pi$ 这两个相位条件均不变。
把所得振幅用逆置换送回即恢复原来的 $X,Y$ 及原标签。
这仅为证明中的坐标变换，没有给原生操作表增加任何控制。

若 $w<r/2$，置 $d=r-2w>0$ 并定义

$$
\kappa_*=\frac{w(r-w-y)}d.
\tag{C85.7}
$$

由 $y\le r/2$ 得 $r-w-y\ge r/2-w=d/2>0$，故 $\kappa_*>0$。
又 $y\ge w$ 给 $r-w-y\le r-2w=d$，故 $\kappa_*\le w$。
四底角的完整值为

$$
\begin{aligned}
p_0^*&=\frac{(r-w)(r-w-y)}d,&
p_1^*&=\frac{w(y-w)}d,\\
p_3^*&=\frac{(r-w)(y-w)}d,&
p_{13}^*&=\frac{w(r-w-y)}d.
\end{aligned}
\tag{C85.8}
$$

这可由式 (C84.2) 逐项代入；分母为正、两个分子因子非负，故全部合法。
两行和分别为 $r-w,w$，右边缘为 $y$，所以并未更改折叠后的矩约束。
另有 $p_0^*p_1^*=p_3^*p_{13}^*$。
取实际代表

$$
\psi^*=(\sqrt{p_0^*},\sqrt{p_1^*},\sqrt{1-r},
\sqrt{p_3^*},-\sqrt{p_{13}^*}).
$$

在全正处其 $\chi=\pi$，在端点该式仍直接定义振幅。
$B$ 的行内积为
$(\sqrt{p_0^*p_1^*}-\sqrt{p_3^*p_{13}^*})/r=0$，故

$$
\rho_L=\operatorname{diag}((r-w)/r,w/r).
$$

于是 $\mathcal C=2\sqrt{w(r-w)}/r$，达上界。

若 $w=r/2$，C-84.2 强制原边缘 $X=Y=r/2$。置 $L=r/2$，
概率是 $(\kappa,L-\kappa,1-r,L-\kappa,\kappa)$。
每个内部 $\kappa\in(0,L)$ 在 $\chi=\pi$ 时都有

$$
B=\frac1{\sqrt r}
\begin{pmatrix}\sqrt\kappa&\sqrt{L-\kappa}\\
\sqrt{L-\kappa}&-\sqrt\kappa\end{pmatrix},
\qquad BB^\dagger=\frac12I_2,\qquad\mathcal C=1.
\tag{C85.9}
$$

两个端点也由同一振幅表达取到一，但不在零振幅处要求一个内在角。

最后，对原来的任意边缘，在

$$
\kappa_0=\frac{XY}{r},\qquad \chi=0
\tag{C85.10}
$$

取全部底角振幅非负。四底角概率为

$$
\left(\frac{(r-X)(r-Y)}r,\ 
\frac{X(r-Y)}r,\ 
\frac{(r-X)Y}r,\ 
\frac{XY}r\right).
\tag{C85.11}
$$

四者严格正，且条件向量分解为

$$
|\phi_0\rangle=
\left(\sqrt{1-X/r}|0\rangle+\sqrt{X/r}|1\rangle\right)
\otimes
\left(\sqrt{1-Y/r}|0\rangle+\sqrt{Y/r}|1\rangle\right).
$$

故 $\mathcal C=0$。在折叠坐标中，从这个点到上述最优点取
$\kappa(t)=(1-t)wy/r+t\kappa_*$、$\chi(t)=\pi t$；
对称分支任选一个内部最优高度代替 $\kappa_*$。
取前三个底角的正平方根、最后一个乘 $e^{-i\pi t}$，中模式恒为 $\sqrt{1-r}$，
便是一条合法实际振幅连续路径。再逆置换回原标签。
行列式模连续，从零到上界，由介值定理得到全部中间值；上界排除其他值。证毕。

**命题 C-85.3（全正域的精确取等分类）。** 在折叠坐标中，全正最大值可取得当且仅当

$$
y>w\quad\hbox{或}\quad w=y=r/2.
\tag{C85.12}
$$

若 $y=w<r/2$，闭纤维最大值只在 $\kappa=w$ 取得；
此点 $p_1=p_3=0$。在全正域，concurrence 的取值恰为
$[0,\mathcal C_{\max})$，上确界为 $\mathcal C_{\max}$ 而没有最大值。

证明。$y>w$ 时，式 (C85.8) 四项都正；对称分支已有内部构造。
反过来，在非中心折叠域，达到左边缘行列式界必须使行内积为零，
因而两个贡献的模相等，必要地

$$
p_0p_1-p_3p_{13}
=(r-w-y+\kappa)(w-\kappa)-(y-\kappa)\kappa
=w(r-w-y)-(r-2w)\kappa=0.
\tag{C85.13}
$$

正系数 $r-2w$ 给唯一高度 $\kappa_*$。
若 $y=w<r/2$，此高度恰为 $w$，两个零角不能避免。
上述路径在 $t<1$ 时仍全正，且 concurrence 趋向上界；
对任何严格低于上界的非负目标，取足够近端的路径点再用介值定理即可取得。
其余两种情形连接两个内部点的路径全在内部，故全正取值是闭区间。
该分类包括原标签中的 $X=Y$ 或 $X+Y=r$ 的非中心墙；不能遗漏它们的逆置换。证毕。

## 86. 谱椭圆最圆的限度与条件纯态熵

**定理 C-86.1（相对宽度限制 Schmidt 谱）。** 令谱椭圆半轴为 $B$ 的奇异值
$s_+\ge s_-\ge0$。固定 C-84 的可见均值，则

$$
s_-^2\le\nu,\qquad s_+^2\ge1-\nu,\qquad
\frac{s_+}{s_-}\ge\sqrt{\frac{1-\nu}{\nu}},
\tag{C86.1}
$$

$s_-=0$ 时把轴比定义为 $+\infty$。闭纤维的最优谱为
$(s_+^2,s_-^2)=(1-\nu,\nu)$，轴比下界可达。

证明。C-76、C-77 的归一化谱关系给
$s_+^2+s_-^2=1$、$\mathcal C=2s_+s_-$。
令 $a=s_-^2\in[0,1/2]$，则 $\mathcal C^2=4a(1-a)$。
C-84.2 的严格单调性在 $r=1$ 时说明 $a(1-a)$ 在此域严格增加，
故 C-85.2 的界等价于 $a\le\nu$。
当 $a>0$，轴比平方为 $(1-a)/a$，它严格递减，因而得到所述界；
$a=0$ 的约定与极限一致。C-85 的取等构造使 $a=\nu$。证毕。

| 相对宽度 $\nu$ | 最优平方谱 $(s_+^2,s_-^2)$ | 最大 $\mathcal C$ | 最小谱轴比 |
| ---: | --- | ---: | ---: |
| $1/8$ | $(7/8,1/8)$ | $\sqrt7/4$ | $\sqrt7$ |
| $1/4$ | $(3/4,1/4)$ | $\sqrt3/2$ | $\sqrt3$ |
| $1/2$ | $(1/2,1/2)$ | $1$ | $1$ |

**推论 C-86.2（圆的存在性与最大纯态熵）。** 固定纤维中存在谱圆当且仅当

$$
\nu=\frac12\quad\Longleftrightarrow\quad X=Y=r/2.
\tag{C86.2}
$$

采用 $\log_2$，条件两因子纯态纠缠熵的闭纤维最大值为

$$
S_{\max}=h_2(\nu)
=-\nu\log_2\nu-(1-\nu)\log_2(1-\nu),
\tag{C86.3}
$$

单位为比特；若使用自然对数，则值乘 $\log 2$，单位为 nat。
非中心并列折叠边缘 $y=w<r/2$ 下，全正域的最优谱轴比仅为未取得的下确界，
熵上界仅为未取得的上确界；$y>w$ 或中心对称时二者在全正域取得。

证明。谱圆要求 $s_+=s_-$，由归一化即 $a=1/2$，故 $\nu=1/2$；
C-84.2 给边缘平衡，式 (C85.9) 给反向构造。
纯态纠缠熵按任一侧约化谱定义为 $h_2(a)$。
在 $0<a<1/2$，

$$
h_2'(a)=\log_2\frac{1-a}{a}>0,
$$

并在端点连续，故最大熵与最大 $a$ 同时取得。
C-85.3 的取等分类一并给出全正域的取得性。证毕。

纯态熵定义及其与 concurrence 的单调关系是经典中间结构：
Hill–Wootters，*Entanglement of a Pair of Quantum Bits*，
[quant-ph/9703041v2](https://arxiv.org/abs/quant-ph/9703041v2)，
纯态定义段及式 (4)–(6)，明确使用 $\log_2$；
Wootters [quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)，式 (2)、(6)–(8)，给相同纯态关系。
这里仅把它们应用到带固定边缘的条件态，未对一般混态套用本章最优式。
存在谱圆也不意味着任意初态仅靠改相位便能变成任意形状：
对固定概率，相位不改变 $\kappa$ 或 $\eta$；非中心最优还要求特定高度。

## 87. 联合容量缺口的概率项与相位项

**定理 C-87.1（完整缺口恒等式）。** 在折叠坐标 $X=w\le Y=y\le r/2$，有

$$
\begin{aligned}
\mathcal C_{\max}^2-\mathcal C^2
=\frac4{r^2}\left[
\left(\sqrt{p_0p_1}-\sqrt{p_3p_{13}}\right)^2
+4\sqrt{p_0p_1p_3p_{13}}\cos^2\frac\chi2
\right].
\end{aligned}
\tag{C87.1}
$$

在全正域，取等恰要求 $p_0p_1=p_3p_{13}$ 及 $\chi=\pi\bmod2\pi$。
在闭端点，恒等式由振幅连续延伸；若两乘积均零，则取等且不需指定内在角，
若其中恰一个为零，则不能取等。

证明。由式 (C85.4) 及 $X=w$，

$$
\mathcal C_{\max}^2-\mathcal C^2=4|(\rho_L)_{01}|^2,\qquad
r(\rho_L)_{01}=\psi_0\bar\psi_1+\psi_3\bar\psi_{13}.
$$

两个复数项的相角差为 $-\chi$，故

$$
r^2|(\rho_L)_{01}|^2
=p_0p_1+p_3p_{13}
+2\sqrt{p_0p_1p_3p_{13}}\cos\chi.
$$

置 $A=\sqrt{p_0p_1}$、$D=\sqrt{p_3p_{13}}$，
右侧为 $(A-D)^2+4AD\cos^2(\chi/2)$，得到全部系数。
两项非负；全正时 $AD>0$，两项同时零给所述充要条件。
端点某个振幅零时 $AD=0$，相位项消失，剩余 $(A-D)^2$，
取等恰为 $A=D=0$。因此没有在零支撑上使用未定义的 $\arg$。证毕。

**命题 C-87.2（高度误差的精确代价）。** 若 $w<r/2$，则

$$
p_0p_1-p_3p_{13}=(r-2w)(\kappa_*-\kappa).
\tag{C87.2}
$$

只在 $\sqrt{p_0p_1}+\sqrt{p_3p_{13}}>0$ 处有

$$
\left(\sqrt{p_0p_1}-\sqrt{p_3p_{13}}\right)^2
=
\frac{(r-2w)^2(\kappa-\kappa_*)^2}
{\left(\sqrt{p_0p_1}+\sqrt{p_3p_{13}}\right)^2}.
\tag{C87.3}
$$

证明。展开式 (C85.13) 并代入 $\kappa_*$ 即得第一式。
再用 $(A-D)(A+D)=A^2-D^2$，在声明的正分母处除法并平方即得第二式。
非中心并列边缘的最优端点有 $A=D=0$，故第二式不在该点定义；
其值须回到第一项 $(A-D)^2=0$，不能将 $0/0$ 当作公式。
在中心分支 $r=2w,y=w$，直接有 $p_0p_1=p_3p_{13}$ 对全部高度成立，
不使用含 $r-2w$ 分母的 $\kappa_*$。证毕。

式 (C87.1) 是此条件矩阵的行列式与非对角元展开：
概率贡献幅度相等和相位抵消分别承担两个取等条件。
它不以单独一种相位操作供应一般高度修正，也不声称一个新的基本互补性原理。

## 88. 整数填充与连续容量之间的精度条件

**命题 C-88.1（既有整数区间计数与容量的对应）。** 设整数 $m\ge1$ 满足
$mX,mY,mZ\in\mathbb Z$，置 $K=m\kappa$。与这些均值相容的非负整数五模式表恰为

$$
\begin{aligned}
n_0&=m-mX-mY-mZ+K,&n_1&=mX-K,\\
n_2&=mZ,&n_3&=mY-K,&n_{13}&=K,
\end{aligned}
\tag{C88.1}
$$

其中 $K$ 遍历闭整数区间
$m\kappa_-\le K\le m\kappa_+$。因而单纤维表数及连续容量满足

$$
N_m=1+mw=1+\frac{m\mathcal A}{2\pi},\qquad
\mathcal C_{\max}
=2\sqrt{\frac{\mathcal A}{2\pi r}
\left(1-\frac{\mathcal A}{2\pi r}\right)}.
\tag{C88.2}
$$

证明。此处直接消费
[《金字塔关联与原生续卷》数学引文 9.2](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md#九整数概率格点与合法历史是不同计数)
的固定可见点提升数
$1+\min(U,V)-\max(0,U+V+W-m)$。
其标签 $(0,2,3,5,25)$ 对应这里的 $(0,1,2,3,13)$，
参数为 $(U,V,W,k)=(mX,mY,mZ,K)$；
[《基础公式》定义 12.1、数学引文 12.2](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md#十二整数回路计数与原生窗口历史两种数列)
及[《辛预测完成》§35.6](SYMPLECTIC_PREDICTIVE_COMPLETION.md#356-选择的辛体积先验与整数概率格)
给相同逆式与宽度桥。为明确本处计数对象，式 (C88.1) 的和为 $m$，
占位和分别为 $mX,mY,mZ$，且每个表由最后一格 $K$ 唯一决定。
五格非负恰给上述区间；因 $mr=m-mZ$ 也是整数，两端均为整数，
所以点数是 $m\kappa_+-m\kappa_-+1=1+mw$。
面积式由式 (C84.6)，容量式由 C-85.3 代入，未另立一种整数计数结果。证毕。

$N_m$ 数的是计数表，不是其有序排列或原生历史数，也不是相位连续的量子态数或测量次数。
本章把既有计数供应连接到同一个宽度的连续最优值；整数制备精度另有限制。

**命题 C-88.2（相位优化网格的取等条件）。** 在闭概率网格上，允许连续选择相位。
每个合法高度的相位最优值为

$$
\mathcal C_{\rm ph}^2(\kappa)
=\frac4{r^2}
\left(\sqrt{p_0p_{13}}+\sqrt{p_1p_3}\right)^2.
\tag{C88.3}
$$

若折叠后的 $w<r/2$，网格达到连续容量当且仅当 $m\kappa_*\in\mathbb Z$。
若 $w=r/2$，每个合法网格高度都能达到 $\mathcal C=1$。

证明。行列式的两个乘积模固定，其差的模至多为两模之和；
在全正处令 $\chi=\pi$ 取等，端点缺失相位时同一振幅选择仍取等。
C-87.1 在该相位的剩余缺口只有 $(A-D)^2$，
式 (C85.13) 使非中心情形的零点唯一为 $\kappa_*$。
因此网格是否含这个高度恰为取等判据。
各折叠映射在计数坐标中分别为
$K\mapsto mY-K$、$K\mapsto mX-K$ 或保持 $K$，
边缘也在整数 $mr$ 内取补，所以折叠及其逆保持整性。
中心情形直接用式 (C85.9) 和其端点延伸。证毕。

若另限制全正网格，则必须先保证存在内部格点；存在时仍只在上述合法最优高度且四角全正时取等。
非中心并列边缘即使网格含 $\kappa_*$，这个点也被全正限制排除。
这里的网格是概率精度，未假定仪器能对任意实相位精确制备。

**命题 C-88.3（五个网格竞争者的完整比较）。** 取

$$
r=\frac45,\qquad X=\frac15,\qquad Y=\frac7{20}.
$$

则 $w=1/5$、$\kappa_*=1/8$、$\mathcal C_{\max}^2=3/4$。
在 $m=20$ 时，以 $j=20\kappa\in\{0,1,2,3,4\}$ 写全部表，
逐高度相位优化的结果为

| $j$ | $\kappa$ | $(n_0,n_1,n_2,n_3,n_{13})$ | $\mathcal C_{\rm ph}^2$ |
| ---: | ---: | --- | ---: |
| $0$ | $0$ | $(5,4,4,7,0)$ | $7/16$ |
| $1$ | $1/20$ | $(6,3,4,6,1)$ | $(6+3\sqrt3)/16$ |
| $2$ | $1/10$ | $(7,2,4,5,2)$ | $(6+\sqrt{35})/16$ |
| $3$ | $3/20$ | $(8,1,4,4,3)$ | $(7+2\sqrt6)/16$ |
| $4$ | $1/5$ | $(9,0,4,3,4)$ | $9/16$ |

因此唯一最优高度为 $1/10$，且

$$
\mathcal C_{20,\max}^2=\frac{6+\sqrt{35}}{16}<\frac34.
\tag{C88.4}
$$

在 $m=40$ 时，$\kappa_*=5/40$ 的表 $(15,3,8,9,5)$ 恢复连续上界。

证明。式 (C85.7) 给
$\kappa_*=(1/5)(4/5-1/5-7/20)/(4/5-2/5)=1/8$。
合法区间为 $[0,1/5]$，故上表穷尽 $m=20$ 的五个高度。
式 (C88.1) 给一般表 $(5+j,4-j,4,7-j,j)$。
代入式 (C88.3) 得一个可逐行直接化简的式子

$$
\mathcal C_{\rm ph}^2(j/20)
=\frac{\left(\sqrt{j(5+j)}+\sqrt{(4-j)(7-j)}\right)^2}{64}.
\tag{C88.5}
$$

$j=0,4$ 分别给 $28/64$、$36/64$；
$j=1$ 给 $(\sqrt6+\sqrt{18})^2/64$；
$j=2$ 给 $(\sqrt{14}+\sqrt{10})^2/64$；
$j=3$ 给 $(\sqrt{24}+2)^2/64$，正是表中五值。

比较分子，$\sqrt{35}>3\sqrt3$ 由 $35>27$；
$\sqrt{35}>3$ 使 $6+\sqrt{35}>9>7$。
剩下与 $7+2\sqrt6$ 的比较等价于 $\sqrt{35}>1+2\sqrt6$。
两边都正，可平方化为 $35>25+4\sqrt6$；
再因两边 $10,4\sqrt6$ 都正，等价于 $100>96$，严格成立。
最后 $\sqrt{35}<6$ 给严格低于 $12/16=3/4$。
$m=40$ 的所列表和为四十、占位和为八、十四、八，且高度恰为 $1/8$，
故命题 C-88.2 给恢复上界。证毕。

## 89. 同宽度纤维的不同最优概率椭圆与坐标度量

**命题 C-89.1（同面积、同容量而不同的最优高度）。** 取两个固定均值纤维

$$
b_A:\ (r,X,Y)=\left(\frac45,\frac15,\frac3{10}\right),\qquad
b_B:\ (r,X,Y)=\left(\frac45,\frac15,\frac25\right).
\tag{C89.1}
$$

它们都有 $Z=1/5$、$w=1/5$、$\nu=1/4$、
$\mathcal A=2\pi/5$、$\mathcal C_{\max}=\sqrt3/2$。其余读数如下：

| 量 | 纤维 $A$ | 纤维 $B$ |
| --- | ---: | ---: |
| 最优高度 $\kappa_*$ | $3/20$ | $1/10$ |
| 最优相位 $\chi$ | $\pi$ | $\pi$ |
| 最优 $(p_0,p_1,p_2,p_3,p_{13})$ | $(9,1,4,3,3)/20$ | $(3,1,2,3,1)/10$ |
| 最优四角比 $p_0p_{13}/(p_1p_3)$ | $9$ | $1$ |
| 最优 $\eta$ | $(\log9)/8$ | $0$ |
| 最优概率关联椭圆 | 非圆 | 圆 |
| 最优谱平方轴 | $(3/4,1/4)$ | $(3/4,1/4)$ |
| $\kappa=1/10$ 处 $\mathcal I$ | $55/2$ | $80/3$ |
| $\kappa=1/10$ 处 $\mathcal I'$ | $75/4$ | $0$ |
| $\kappa=1/10$ 处 $\mathcal I''$ | $17125/4$ | $112000/27$ |
| $\kappa=1/10$ 处 $\mathcal K$ | $7490/1331$ | $35/6$ |

证明。两组都已经折叠，代入式 (C85.7) 得 $3/20,1/10$；
再代入五概率公式给表中的完整最优概率。
其四角比分别为 $(9\cdot3)/(1\cdot3)=9$ 与 $(3\cdot1)/(1\cdot3)=1$，
故按式 (C84.7) 得 $\eta$ 及概率椭圆形状。
两组全正，$\chi=\pi$ 取等；谱由 C-86.1 得到。

为计算同一命名高度处的度量，令底角顺序为 $(0,1,3,13)$，
其斜率 $d=(1,-1,-1,1)$，由 $p_s'=d_s$，

$$
\mathcal I'=-\sum_s\frac{d_s}{p_s^2}
=-\frac1{p_0^2}+\frac1{p_1^2}+\frac1{p_3^2}-\frac1{p_{13}^2},
\qquad
\mathcal I''=2\sum_s\frac1{p_s^3}.
\tag{C89.2}
$$

在 $\kappa=1/10$，$A$ 的四底角为 $(2/5,1/10,1/5,1/10)$，所以

$$
\begin{aligned}
\mathcal I_A&=\frac52+10+5+10=\frac{55}2,\\
\mathcal I_A'&=-\frac{25}4+100+25-100=\frac{75}4,\\
\mathcal I_A''&=2\left(\frac{125}8+1000+125+1000\right)
=\frac{17125}4.
\end{aligned}
\tag{C89.3}
$$

$B$ 的四底角为 $(3/10,1/10,3/10,1/10)$，所以

$$
\begin{aligned}
\mathcal I_B&=\frac{10}3+10+\frac{10}3+10=\frac{80}3,\\
\mathcal I_B'&=-\frac{100}9+100+\frac{100}9-100=0,\\
\mathcal I_B''&=2\left(\frac{1000}{27}+1000+\frac{1000}{27}+1000\right)
=\frac{112000}{27}.
\end{aligned}
\tag{C89.4}
$$

C-79.2 对所选度量给

$$
\mathcal K=-\frac12(2/\mathcal I)''
=\frac{\mathcal I''}{\mathcal I^2}
-\frac{2(\mathcal I')^2}{\mathcal I^3}.
$$

于是

$$
\mathcal K_A=
\frac{17125}{3025}-\frac{5625}{166375}
=\frac{7490}{1331},\qquad
\mathcal K_B=\frac{112000}{27}\frac9{6400}
=\frac{35}6.
\tag{C89.5}
$$

全部导数都在固定各自 $(X,Y,Z)$ 下对 $\kappa$ 求取。证毕。

这个例子证明面积和最大 concurrence 不能恢复带有指定概率坐标的完整度量：
两者在同一命名坐标 $\kappa=1/10$ 的度量系数不同。
仅由两个被标记点曲率不同，不能排除某个把它们送到不同点的抽象等距映射，
故这里不作抽象非等距结论。最优时 $A$ 的概率关联椭圆非圆、$B$ 为圆，
而两者谱椭圆同为轴比 $\sqrt3$，再次区分概率形状与 Schmidt 谱。

## 90. 跨纤维的底面质量缩放与消失分支

**定义 C-90.1（固定条件态的比较及表面映射）。** 固定
$0<\widehat X,\widehat Y<1$，令

$$
\widehat\kappa_-=\max(0,\widehat X+\widehat Y-1),\qquad
\widehat\kappa_+=\min(\widehat X,\widehat Y).
$$

在归一化底面上取
$\widehat\kappa\in[\widehat\kappa_-,\widehat\kappa_+]$，
底角概率为
$(1-\widehat X-\widehat Y+\widehat\kappa,
\widehat X-\widehat\kappa,\widehat Y-\widehat\kappa,\widehat\kappa)$。
另固定各个实际复振幅，得到一个归一化底面纯态 $|\phi\rangle$；
这比固定 $\chi$ 或概率表更强。对 $0<r<1$ 定义

$$
|\psi_r\rangle=\sqrt{1-r}|2\rangle+\sqrt r|\phi\rangle,\qquad
(X,Y,Z,\kappa)=(r\widehat X,r\widehat Y,1-r,r\widehat\kappa).
\tag{C90.1}
$$

中模式系数取正，故相对底面的共同相位也已固定。
每个 $r$ 有不同的固定均值纤维；这里不是在一条固定 $(X,Y,Z)$ 曲面上改变 $r$。
为比较整个曲面，令 $\widehat\kappa,\chi$ 变化，使用对应映射

$$
F_r:(\widehat\kappa,\chi)\longmapsto(r\widehat\kappa,\chi).
\tag{C90.2}
$$

帽号几何是总底面质量一的参数模型；不宣称它是 $Z>0$ 的五模式全正纤维。

**定理 C-90.2（同条件坐标下的精确缩放）。** 在各自全正内部，有

$$
\kappa_\pm=r\widehat\kappa_\pm,\qquad
w=r\widehat w,\qquad
\nu=\widehat w,\qquad
\mathcal I=\frac{\widehat{\mathcal I}}r,
$$

$$
F_r^*g_r=r\widehat g,\qquad
F_r^*\omega_r=r\widehat\omega,\qquad
\mathcal K_r\circ F_r=\frac{\widehat{\mathcal K}}r.
\tag{C90.3}
$$

对应曲线长度及距离乘 $\sqrt r$，面积乘 $r$。
条件 $\eta,\chi,\mathcal C,\nu$ 均不变，其中 $\eta,\chi$ 的坐标解释限于定义域；
$\mathcal C$ 与谱可以用振幅延伸到闭端点。

证明。因 $r>0$，乘 $r$ 与 $\min,\max$ 交换，得到两端及宽度关系。
四底角每项都是 $r\widehat p_s$，故倒数和为 $\widehat{\mathcal I}/r$；
此处只在每个 $r$ 固定的表面上微分，所以 $d\kappa=r\,d\widehat\kappa$。代入得

$$
F_r^*g_r
=\frac{\widehat{\mathcal I}}{2r}r^2d\widehat\kappa^2
+\frac{2r}{\widehat{\mathcal I}}d\chi^2=r\widehat g,\qquad
F_r^*\omega_r=r\,d\chi\wedge d\widehat\kappa.
$$

每条曲线的速度范数乘 $\sqrt r$，积分给长度缩放；
对所有连接路径取下确界给距离缩放，进而也延伸到 Cauchy 完备化。
二维度量行列式的平方根乘 $r$，给面积缩放。
另置 $f_r=2/\mathcal I=r\widehat f(\widehat\kappa)$，
对 $\kappa$ 求两次导数得 $f_r''=\widehat f''/r$，
由 C-79.2 得曲率缩放；曲率在规则部分使用。

四角比中的 $r^2$ 抵消，故 $\eta$ 不变，实际相位原已固定；
条件系数除以 $\sqrt r$ 后恰为 $\phi$，所以 $\mathcal C$、谱不变，
而 $w/r=\widehat w$。证毕。

**命题 C-90.3（条件最大联合与完整纯态趋于中模式可以并存）。** 采用迹距离约定

$$
D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1,
$$

则式 (C90.1) 满足

$$
D(|\psi_r\rangle\langle\psi_r|,|2\rangle\langle2|)=\sqrt r.
\tag{C90.4}
$$

存在固定全正条件态使所有 $r>0$ 都有 $\mathcal C=1$，
同时 $\mathcal K=2/r\to+\infty$，而完整态的迹距离趋零。

证明。$\phi$ 与 $|2\rangle$ 正交，在正交基 $(|2\rangle,|\phi\rangle)$ 上，
两个密度矩阵之差为

$$
\begin{pmatrix}
-r&\sqrt{r(1-r)}\\
\sqrt{r(1-r)}&r
\end{pmatrix}.
$$

其迹为零、行列式为 $-r$，故特征值为 $\pm\sqrt r$；
正交补上为零，迹范数为 $2\sqrt r$。
例如取
$|\phi\rangle=(|0\rangle+|1\rangle+|3\rangle-|13\rangle)/2$，
则条件四格全正，$\widehat X=\widehat Y=1/2$、$\widehat\kappa=1/4$，
$B=\frac12\left(\begin{smallmatrix}1&1\\1&-1\end{smallmatrix}\right)$ 给 $\mathcal C=1$。
C-82.1 给所选尺度的 $\mathcal K=2/r$。证毕。

这里 $r=0$ 不在条件化定义域，不能在质量已消失的分支上继续声称有一个实际条件态。
上述极限同时保留了 $r>0$ 时的条件关系和完整态的分支稀有性。
曲率发散来自指定度量的整体缩小，不推出信息量单调增加或引力增强。

## 91. 同一实际纯态的两份投影与底面概率成本

**假设 C-91.1（实际制备、单次接口和跨试验条件）。** 每次提供两份独立制备的同一个
实际五态纯态射线，即 $|\psi\rangle\otimes|\psi\rangle$，
并提供下述联合投影；“同一个”包括占位相位参照。
相同概率表或相同商点不足以替代这一假设；它不要求克隆任意未知态。

令 $P_{\rm bot}=\sum_{s\ne2}|s\rangle\langle s|$。
单次事件公式更一般只需要两份输入密度算子满足充分接口

$$
(P_{\rm bot}\otimes P_{\rm bot})\rho_{12}
(P_{\rm bot}\otimes P_{\rm bot})
=r^2|\phi\otimes\phi\rangle\langle\phi\otimes\phi|,
\tag{C91.1}
$$

其中 $\phi=P_{\rm bot}\psi/\sqrt r$ 为同一归一化条件态。
独立同态制备保证该式；它是本事件在底面双副本子空间实际需要的块。
下章的等待公式另要求跨试验事件独立同分布，单次接口本身不供应跨试验独立性。

**定理 C-91.2（指定四项事件的宽度界与面积恒等式）。** 定义归一化向量及其效果

$$
|\Omega\rangle=\frac12\bigl(
|0,13\rangle+|13,0\rangle-|1,3\rangle-|3,1\rangle\bigr),
\qquad E_\Omega=|\Omega\rangle\langle\Omega|.
\tag{C91.2}
$$

在假设 C-91.1 下，事件概率为

$$
q_\Omega
=|\psi_0\psi_{13}-\psi_1\psi_3|^2
=\frac{r^2\mathcal C^2}{4},
$$

$$
q_{\Omega,\max}=w(r-w)
=\frac{\mathcal A}{2\pi}\left(r-\frac{\mathcal A}{2\pi}\right).
\tag{C91.3}
$$

最大值在闭纤维取得。若只允许全正态，它在 $y>w$ 或 $w=y=r/2$ 时取得，
在 $y=w<r/2$ 时仅为未取得的上确界。

证明。四个有序五模式基向量互相正交，四个系数模平方之和为一。
对同一个实际 $\psi$ 的两份输入，

$$
\langle\Omega|\psi\otimes\psi\rangle
=\frac12(\psi_0\psi_{13}+\psi_{13}\psi_0
-\psi_1\psi_3-\psi_3\psi_1)
=\psi_0\psi_{13}-\psi_1\psi_3.
$$

式 (C85.1) 给它为 $r\det B$。
更一般，$E_\Omega$ 支持在底面双副本块内，所以由式 (C91.1) 取迹同样得到
$r^2|\langle\Omega|\phi\otimes\phi\rangle|^2=r^2\mathcal C^2/4$。
对状态最大化，消费 C-85.2 的容量和 C-85.3 的取得性，再代入 $\mathcal A=2\pi w$ 即得。证毕。

这一因子分解明确保留成本：

$$
q_\Omega=
\underbrace{r^2}_{\text{两份均落在底面的概率}}
\ \underbrace{\frac{\mathcal C^2}{4}}_{\text{条件底面中的投影概率}}.
\tag{C91.4}
$$

因此先条件化再报告大 concurrence，不能删去完整试验的 $r^2$ 因子。
C-78.3 已给同一投影及其占位对易性质；这些性质并不供应一个原生仪器实现。

数学先例与精确归一化。Aolita–Mintert，
*Measuring multipartite concurrence with a single factorizable observable*，
[quant-ph/0608012v2](https://arxiv.org/abs/quant-ph/0608012v2)，式 (1)–(2)，
给两份纯态上的 $C_N^2=\langle A\rangle$，其中
$A=4\sum P_{s_1}^{1}\otimes\cdots\otimes P_{s_N}^{N}$，
求和限于偶数个反对称因子并排除全对称项。
两个二元因子时只剩 $A=4P_-^L\otimes P_-^R$。
按实际基序作重排

$$
R:\ |a,b\rangle\otimes|a',b'\rangle
\longmapsto |a,a'\rangle\otimes|b,b'\rangle,\qquad
|\varepsilon\rangle=(|01\rangle-|10\rangle)/\sqrt2.
$$

四项直接展开给

$$
R|\Omega\rangle=|\varepsilon\rangle_{LL'}\otimes|\varepsilon\rangle_{RR'},
\qquad RE_\Omega R^\dagger=P_-^L\otimes P_-^R.
\tag{C91.5}
$$

故两份归一化条件态的概率为 $\mathcal C^2/4$，与本处完全一致。
重排只在四维底面各自的两因子结构上定义，不把整个五维载体当作二元张量积。
Romero、López、Lastra、Solano、Retamal，
*Direct measurement of concurrence for atomic two-qubit pure states*，
[quant-ph/0611016v1](https://arxiv.org/abs/quant-ph/0611016v1)，式 (2)–(5)，
采用另一个含局部操作、CNOT 与旋转的电路：
$A_-=c_1c_2-c_0c_3$，$P_{gggg}=|A_-|^2/2=\mathcal C^2/8$。
该输出不是此处归一化 $\Omega$ 的概率；两份资源的经典方向不能抹去这项因子差异。

**命题 C-91.3（相同概率和商点不能替代实际同态）。** 令
$|\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2$，在既定底面张量识别中取

$$
|\phi_+\rangle=|+\rangle\otimes|+\rangle,\qquad
|\phi_-\rangle=|-\rangle\otimes|-\rangle,
$$

$$
|\psi_\pm\rangle=\sqrt{1-r}|2\rangle+\sqrt r|\phi_\pm\rangle.
\tag{C91.6}
$$

两者五概率相同，均有 $X=Y=r/2$、$\kappa=r/4$、$\chi=0\bmod2\pi$、
$\mathcal C=0$，但

$$
|\langle\Omega|\psi_+\otimes\psi_-\rangle|^2=\frac{r^2}4>0.
\tag{C91.7}
$$

证明。按 $(0,1,3,13)$ 顺序，两底面系数分别为
$(1,1,1,1)/2$、$(1,-1,-1,1)/2$。
各模平方为 $1/4$，后一组相位可取 $(0,\pi,\pi,0)$，交替和为 $-2\pi$。
每组均为乘积态，故行列式为零。
混合输入的四项内积却为

$$
\frac12\left(\frac r4+\frac r4-\left(-\frac r4\right)-\left(-\frac r4\right)\right)
=\frac r2,
$$

平方得到所列值。这个输入既没有共同条件态 $\phi\otimes\phi$，
也不满足式 (C91.1)；不存在与定理 C-91.2 的矛盾。证毕。

## 92. 固定双副本测试的等待代价与曲率尺度

**定理 C-92.1（首个事件的几何等待及最优取得性）。** 固定一份允许的实际纯态，
每次重新供应两份独立制备，跨试验独立同分布地执行式 (C91.2) 的测试。
令 $T$ 为第一次成功的试验编号，没有成功则 $T=+\infty$。
若 $q_\Omega=0$，则 $T=+\infty$ 几乎必然，$\mathbb ET=+\infty$。
若 $q_\Omega>0$，则

$$
\Pr(T>n)=(1-q_\Omega)^n\quad(n\ge0),\qquad
\mathbb ET=\frac1{q_\Omega}.
\tag{C92.1}
$$

在固定均值的闭纤维、固定这个测试与 iid 合同内，

$$
\min\mathbb ET=\frac1{w(r-w)}.
\tag{C92.2}
$$

每次使用两份制备，故最佳平均制备份数为 $2/[w(r-w)]$。
在全正域中，$y=w<r/2$ 时右侧仅为未取得的下确界；
$y>w$ 或中心对称时为取得的最小值。

证明。前 $n$ 次都失败的概率由独立性为 $(1-q_\Omega)^n$。
$q_\Omega=0$ 时每次成功概率零，可数并仍为零，所以从不成功。
$q_\Omega>0$ 时，尾概率趋零，$T$ 有限几乎必然；
非负整数随机变量的尾和公式可由
$T=\sum_{n\ge0}\mathbf1_{\{T>n\}}$ 与单调收敛得到，故

$$
\mathbb ET=\sum_{n=0}^{\infty}(1-q_\Omega)^n=\frac1{q_\Omega}.
$$

$r>w>0$ 保证 $w(r-w)>0$。
在同一测试内，$1/q$ 对正 $q$ 严格递减，因此 C-91.2 的最大概率及取得性
直接给最优等待和全正域的下确界分类。
到成功为止每次确用两份，制备总数为 $2T$，其期望为 $2\mathbb ET$，无穷值亦成立。证毕。

这里“最佳”只在上述状态选择、两份制备与固定测试内比较。
一次事件不恢复完整状态，公式不是所有量子测量或状态辨识方法的最优样本下界。
单次的独立同态资源与跨试验 iid 是两个分别需要的条件。

**命题 C-92.2（对称锥曲面上的曲率—等待对应）。** 若 $X=Y=r/2$，
则 $w=r/2$、$\mathcal C_{\max}=1$。在式 (C84.5) 的选定尺度和规则部分，

$$
f=\frac2{\mathcal I}
=\frac{\kappa(r/2-\kappa)}{r/2},\qquad
\mathcal K=-\frac12f''=\frac2r.
$$

因此指定事件的最优概率与等待为

$$
q_{\Omega,\max}=\frac{r^2}4=\frac1{\mathcal K^2},
\qquad
\min\mathbb ET=\frac4{r^2}=\mathcal K^2.
\tag{C92.3}
$$

这些最优值都能用全正状态取得。

| 底面质量 $r$ | 条件最大 $\mathcal C$ | 规则部分曲率 $\mathcal K$ | 最大 $q_\Omega$ | 最佳平均双副本试验次数 | 平均制备份数 |
| ---: | ---: | ---: | ---: | ---: | ---: |
| $4/5$ | $1$ | $5/2$ | $4/25$ | $25/4$ | $25/2$ |
| $1/5$ | $1$ | $10$ | $1/100$ | $100$ | $200$ |
| $1/20$ | $1$ | $40$ | $1/1600$ | $1600$ | $3200$ |

证明。对称纤维四底角为
$(\kappa,r/2-\kappa,r/2-\kappa,\kappa)$，
故 $\mathcal I=2/\kappa+2/(r/2-\kappa)$。
取倒数给所列 $f=\kappa-2\kappa^2/r$，两次求导得 $f''=-4/r$。
式 (C85.9) 供应每个内部高度在 $\chi=\pi$ 的最大 concurrence，
故式 (C91.3) 与式 (C92.2) 分别给概率和等待，代入三个 $r$ 即得表。证毕。

这里使用的是 C-82.1 的球面半周商，两个端点锥角均为 $\pi$；
$\mathcal K=2/r$ 指规则部分的高斯曲率，不能把端点当作普通光滑点而省去缺角。
若另将度量乘常数 $c>0$，曲率变成 $\mathcal K/c$，
而 $q_\Omega$ 与固定测试不变；所以式 (C92.3) 依赖选定尺度，
不是普适的“曲率等于计算复杂度”定律。
条件联合仍可最大，而随 $r$ 减少，两份实际进入底面的成本使等待变大。

## 93. 宽度、谱和取得代价的来源及适用对象

**约定 C-93.1（数学供应及其精确范围）。** 本组连接的三个量为

$$
w\longmapsto\mathcal A=2\pi w,\qquad
\nu=\frac wr\longmapsto\mathcal C_{\max}=2\sqrt{\nu(1-\nu)},\qquad
(r,w)\longmapsto q_{\Omega,\max}=w(r-w).
\tag{C93.1}
$$

它们分别描述绝对面积、条件纯态联合容量及已指定两份读口的事件概率。
同一宽度的既有来源、经典中间结构与本处应用的关系为

| 来源 | 本组实际消费的内容 |
| --- | --- |
| 《局部填充》§3.1；《金字塔关联与原生续卷》9.2；《基础公式》12.1–12.3 | 五模式闭区间、宽度及完整整数提升；标签与参数的对应见 C-84、C-88。单纤维表数不等于全体可见格点数或有序来源数。 |
| 《辛预测完成》35.5–35.7；本续卷 C-73、C-74、C-76–C-83 | 实际固定矩相位商、$\eta=J/8$、尺度与度量、条件矩阵的商不变量、四项投影、完整端点和对称锥曲面。 |
| Wootters，quant-ph/9709029v2，式 (2)、(6)–(8) | 归一化两因子纯态 concurrence、约化熵及二元谱关系；本组只取其纯态范围。 |
| Hill–Wootters，quant-ph/9703041v2，纯态定义及式 (4)–(6) | 以二为底的约化熵与 concurrence 的单调关系，支持 C-86 的单位与公式。 |
| Aolita–Mintert，quant-ph/0608012v2，式 (1)–(2) | 两份同一纯态及 $4P_-^L\otimes P_-^R$；式 (C91.5) 给实际基重排，条件事件概率为 $\mathcal C^2/4$。 |
| Romero 等，quant-ph/0611016v1，式 (2)–(5) | 特定两份电路的 $P_{gggg}=\mathcal C^2/8$；其归一化与本文投影不同，不能作事件概率的替代式。 |

取最小边缘行列式、二阶谱、连续路径、几何尾和及常数度量缩放是经典数学工具。
C-85 的折叠最优高度与全正取等分类、C-88 的五格精度比较、
C-89 的相同宽度而不同坐标度量、C-90 至 C-92 的质量与固定读口成本关系，
都是在这些明确供应和五模式约束下的普通数学推导；
这些应用不附带全球原创性结论，也不把普通证明称作 Lean 内核认证。

**约定 C-93.2（状态选择与实际取得分别承担的条件）。** 概率可行、纯相干完成、
条件张量结构、商几何、指定制备和指定仪器是不同层次的条件。
宽度决定可取谱范围；在全正域，达到最优同时需要正确高度和抵消相位。
这里没有由“能写出这样的振幅”推出原生控制能制备它，也没有由一个数学投影
推出实际硬件或未知态克隆能力。

[《实际 renewal 仪器与检测器秩》定义 22.1、定理 22.3](FIB_REAL_RENEWAL_INSTRUMENTS_AND_DETECTOR_RANK.md#22-all-sum-conditional-acquisition-at-the-cubic-near-one-order)
的原生连续 no11 读取协议在一条实际来源流中取得全部完整间隔对，逐位支付初始等待和每一对的两个闭合 tick。
它的成本等式为 $L=1+\tau+\sum_{j=1}^N(K_{2j-1}+K_{2j}+2)$；
这套来源及成本合同不供应两份相干纯态或式 (C91.2) 的投影。
若将该 renewal 来源的参数记为 $q_{\rm native}$、逐位取得成本记为 $L$，
则它们分别区别于此处的 $q_\Omega$ 和试验编号 $T$；
没有可用于直接代入的 $r=1-q_{\rm native}$ 关系。
跨模型若要比较，必须另给保持实际来源、输出事件及成本单位的映射。
在这份指定几何中，面积缩小、曲率增大与条件 concurrence 不变能够同时发生；
完整状态的分支质量和两份取得代价仍须保留。

## 追加锚（本行以下为增补区）

## 94. 五模式混态、底面张量结构与完整双副本测量

**定义 C-94.1（任意密度算子及固定均值的闭集合）。** 在 C-84.1 的正交五模式空间
$\mathcal H_5=\operatorname{span}\{|0\rangle,|1\rangle,|2\rangle,|3\rangle,|13\rangle\}$ 上，
取任意 $\rho\succeq0$、$\operatorname{Tr}\rho=1$，令 $p_s=\langle s|\rho|s\rangle$。
不要求 $\rho$ 纯，也不要求中模式与底面之间的矩阵元为零。沿用

$$
X=p_1+p_{13},\qquad Y=p_3+p_{13},\qquad Z=p_2,\qquad
r=1-Z,\qquad\kappa=p_{13}.
\tag{C94.1}
$$

固定 $0<r<1$、$0<X,Y<r$。C-84.1–C-84.2 的概率反解及宽度在此仍为

$$
\begin{aligned}
p&=(r-X-Y+\kappa,\ X-\kappa,\ 1-r,\ Y-\kappa,\ \kappa),\\
\kappa_-&=\max(0,X+Y-r),\qquad\kappa_+=\min(X,Y),\\
w&=\kappa_+-\kappa_-=\min\{X,Y,r-X,r-Y\},\\
x&=X/r,\qquad y=Y/r,\qquad\nu=w/r=\min\{x,1-x,y,1-y\}.
\end{aligned}
\tag{C94.2}
$$

这里 $\mathfrak D(r,X,Y)$ 指满足这些固定均值的所有五维密度算子，
允许 $\kappa\in[\kappa_-,\kappa_+]$ 变化并允许合法零对角元。
这些式子只使用对角非负及迹一，因此适用于任意秩。
完整混态另有非对角自由度；本集合不等于以 $(\kappa,\chi)$ 为坐标的纯态相位商。
C-84.3 的 $\mathcal A=2\pi w$ 仍只属于那里指定尺度的纯振幅辛完成，
不是本混态集合的面积或维数公式。

**定义 C-94.2（条件底面及可分离性）。** 令

$$
P_{\mathrm b}=|0\rangle\langle0|+|1\rangle\langle1|
+|3\rangle\langle3|+|13\rangle\langle13|.
$$

以等距嵌入 $\iota:\mathbb C_A^2\otimes\mathbb C_B^2\longrightarrow\mathcal H_5$ 指定

$$
\iota|00\rangle=|0\rangle,\quad
\iota|10\rangle=|1\rangle,\quad
\iota|01\rangle=|3\rangle,\quad
\iota|11\rangle=|13\rangle.
\tag{C94.3}
$$

于是 $\iota^\dagger\iota=I_4$、$\iota\iota^\dagger=P_{\mathrm b}$，定义

$$
\sigma=\frac{\iota^\dagger\rho\iota}{r},\qquad
\iota\sigma\iota^\dagger=\frac{P_{\mathrm b}\rho P_{\mathrm b}}r,
\qquad\sigma_A=\operatorname{Tr}_B\sigma,\quad
\sigma_B=\operatorname{Tr}_A\sigma.
\tag{C94.4}
$$

$\sigma$ 是正半定迹一算子，因为压缩保持正性且
$\operatorname{Tr}(P_{\mathrm b}\rho)=r$。按标准张量基 $(00,01,10,11)$，
其对角为 $(p_0,p_3,p_1,p_{13})/r$，并有

$$
(\sigma_A)_{ac}=\sum_b\sigma_{ab,cb},\qquad
(\sigma_B)_{bd}=\sum_a\sigma_{ab,ad},\qquad
\operatorname{diag}\sigma_A=(1-x,x),\quad
\operatorname{diag}\sigma_B=(1-y,y).
\tag{C94.5}
$$

本组“底面可分离”恰指存在有限分解

$$
\sigma=\sum_j t_j\alpha_j\otimes\beta_j,
\qquad t_j\ge0,\quad\sum_jt_j=1,
\tag{C94.6}
$$

其中 $\alpha_j,\beta_j$ 各为二阶密度算子。
这一定义的对象是已指定的底面两因子；五维载体本身没有被识别为两个物理子系统。

**假设 C-94.3（实际成对输入及读口）。** 一次完整试验实际接收
$\rho\otimes\rho$，即同一密度算子的两份独立制备，并允许执行下述联合测量。
相同的两个单份边缘不作为乘积输入的替代条件；也不假设未知态克隆。
此处只规定单轮来源，跨轮独立同分布另在取得成本定理中规定。

在 $\mathcal K=(\mathbb C_A^2\otimes\mathbb C_B^2)^{\otimes2}$ 上，写基向量为
$|a,b,a',b'\rangle$，定义

$$
F_A|a,b,a',b'\rangle=|a',b,a,b'\rangle,\qquad
F_B|a,b,a',b'\rangle=|a,b',a',b\rangle.
\tag{C94.7}
$$

等价地，在重排
$R|a,b,a',b'\rangle=|a,a'\rangle\otimes|b,b'\rangle$ 后，
$F_A$ 是第一对因子的交换，$F_B$ 是第二对的交换。
二者自伴、平方为恒等，且交换不同坐标所以彼此对易。
令 $s,t\in\{+1,-1\}$，定义

$$
P_s^A=(I+sF_A)/2,\qquad P_t^B=(I+tF_B)/2,
\qquad\Pi_{st}=P_s^AP_t^B.
\tag{C94.8}
$$

它们满足 $\Pi_{st}^\dagger=\Pi_{st}=\Pi_{st}^2$；
若符号对不同，至少一个因子的异号投影相乘为零，故四个投影正交，且
$\sum_{s,t}\Pi_{st}=I_{16}$。令 $J=\iota\otimes\iota$，实际五维双副本测量的效果为

$$
Q_{st}=J\Pi_{st}J^\dagger,\qquad
Q_{\mathrm f}=I_{25}-P_{\mathrm b}\otimes P_{\mathrm b}.
\tag{C94.9}
$$

因 $J^\dagger J=I_{16}$，四个 $Q_{st}$ 仍是互相正交的正投影，
其和为 $JJ^\dagger=P_{\mathrm b}\otimes P_{\mathrm b}$，与正投影 $Q_{\mathrm f}$ 相加为恒等。
故这是包含底面选择失败在内的完整五结果测量。
定义未条件化概率

$$
q_{st}=\operatorname{Tr}[Q_{st}(\rho\otimes\rho)],\qquad
q_{\mathrm f}=\operatorname{Tr}[Q_{\mathrm f}(\rho\otimes\rho)].
\tag{C94.10}
$$

这里的“失败”包括恰一份及两份都未进入底面的全部情况。

**定理 C-94.4（五模式测量的压缩、四符号概率及纯度字典）。** 在假设 C-94.3 下，
令 $\mathcal P=\operatorname{Tr}\sigma^2$、
$\mathcal P_A=\operatorname{Tr}\sigma_A^2$、$\mathcal P_B=\operatorname{Tr}\sigma_B^2$。
上述实际测量满足

$$
q_{st}=\frac{r^2}{4}(1+s\mathcal P_A+t\mathcal P_B+st\mathcal P),\qquad
\sum_{s,t}q_{st}=r^2,\quad q_{\mathrm f}=1-r^2.
\tag{C94.11}
$$

并且 C-91.2 的归一化向量

$$
|\Omega\rangle=\tfrac12(|0,13\rangle+|13,0\rangle-|1,3\rangle-|3,1\rangle)
\tag{C94.12}
$$

满足 $Q_{--}=|\Omega\rangle\langle\Omega|$，从而 $q_\Omega=q_{--}$。

证明。首先按实际输入作双侧压缩：

$$
\begin{aligned}
&(P_{\mathrm b}\otimes P_{\mathrm b})(\rho\otimes\rho)
(P_{\mathrm b}\otimes P_{\mathrm b})\\
&\hspace{12mm}=(P_{\mathrm b}\rho P_{\mathrm b})\otimes(P_{\mathrm b}\rho P_{\mathrm b})
=r^2J(\sigma\otimes\sigma)J^\dagger.
\end{aligned}
\tag{C94.13}
$$

取迹给两份都在底面的概率 $r^2$，取各 $Q_{st}$ 的迹给
$q_{st}=r^2\operatorname{Tr}[\Pi_{st}(\sigma\otimes\sigma)]$。
这一步没有交换 $\rho$ 与 $P_{\mathrm b}$，所以没有假设
$[\rho,P_{\mathrm b}]=0$；任意底面—中位相干都已被实际投影正确处理。

二元交换的反对称空间是一维，由
$|\varepsilon\rangle=(|01\rangle-|10\rangle)/\sqrt2$ 张成。
因此 $R\Pi_{--}R^\dagger$ 是
$|\varepsilon\rangle_{AA'}\otimes|\varepsilon\rangle_{BB'}$ 的秩一投影。
将其四项逆重排并用 $J$ 嵌入，依次得到
$\tfrac12(|0,13\rangle-|3,1\rangle-|1,3\rangle+|13,0\rangle)$，正是 $\Omega$。
四个不同有序基向量正交，所以其范数平方为 $4/4=1$。

为展开每个交换迹，令矩阵元为 $\sigma_{ab,cd}$，所有指标遍历 $\{0,1\}$。
按定义直接有

$$
\begin{aligned}
\operatorname{Tr}[F_A(\sigma\otimes\sigma)]
&=\sum_{a,b,c,d}\sigma_{cb,ab}\sigma_{ad,cd}
=\sum_{a,c}(\sigma_A)_{ca}(\sigma_A)_{ac}=\mathcal P_A,\\
\operatorname{Tr}[F_B(\sigma\otimes\sigma)]
&=\sum_{a,b,c,d}\sigma_{ad,ab}\sigma_{cb,cd}
=\sum_{b,d}(\sigma_B)_{db}(\sigma_B)_{bd}=\mathcal P_B,\\
\operatorname{Tr}[F_AF_B(\sigma\otimes\sigma)]
&=\sum_{a,b,c,d}\sigma_{cd,ab}\sigma_{ab,cd}=\mathcal P,\\
\operatorname{Tr}(\sigma\otimes\sigma)&=1.
\end{aligned}
\tag{C94.14}
$$

$F_AF_B$ 在第三式中交换完整的两份底面。把
$\Pi_{st}=(I+sF_A+tF_B+stF_AF_B)/4$ 代入即得

$$
\begin{aligned}
q_{--}&=\tfrac{r^2}4(1-\mathcal P_A-\mathcal P_B+\mathcal P),\\
q_{-+}&=\tfrac{r^2}4(1-\mathcal P_A+\mathcal P_B-\mathcal P),\\
q_{+-}&=\tfrac{r^2}4(1+\mathcal P_A-\mathcal P_B-\mathcal P),\\
q_{++}&=\tfrac{r^2}4(1+\mathcal P_A+\mathcal P_B+\mathcal P).
\end{aligned}
\tag{C94.15}
$$

相加只余 $r^2$，其补数就是失败概率。证毕。

本推导消费经典交换—纯度恒等式。Mintert–Buchleitner，
*An observable entanglement measure for mixed quantum states*，
[quant-ph/0605250v3](https://arxiv.org/abs/quant-ph/0605250v3)，式 (1)–(3)，
分别给纯态 $4P_-^A\otimes P_-^B$、混态 concurrence 下界和整体—局部纯度差；
这里的 $J$、五维效果及 $r^2$ 因子明确了这些中间结构在当前来源中的参数。

**命题 C-94.5（纯态极限、经典混合和被遗漏的混合性）。** 若条件底面纯，
写 $|\phi\rangle=\sum_{a,b}B_{ab}|ab\rangle$，$\operatorname{Tr}BB^\dagger=1$，
则 $\mathcal P=1$，两约化谱相同，且

$$
\mathcal C(\phi)=2|\det B|,\qquad
q_{--}=\frac{r^2\mathcal C(\phi)^2}{4},\qquad q_{-+}=q_{+-}=0.
\tag{C94.16}
$$

对一般条件混态则只有

$$
q_{-+}+q_{+-}=\frac{r^2}{2}(1-\mathcal P),
\tag{C94.17}
$$

不能用 $q_{--}=r^2\mathcal C^2/4$ 定义混态 concurrence。

证明。纯态的约化矩阵为 $BB^\dagger$ 和 $B^{\mathsf T}\bar B$，
其相同非零谱由奇异值给出；二阶迹一矩阵满足
$\operatorname{Tr}\sigma_A^2=1-2\det\sigma_A=1-2|\det B|^2$。
代入式 (C94.15) 即得纯态式，式 (C94.17) 则由两个异号式相加得到。
为展示混态边界，取

$$
\sigma_{\rm cl}=\tfrac12|00\rangle\langle00|+\tfrac12|11\rangle\langle11|.
\tag{C94.18}
$$

它是纯乘积态混合，故可分离；其整体及两个局部纯度都是 $1/2$。
所以 $q_{--}=q_{-+}=q_{+-}=r^2/8$、$q_{++}=5r^2/8$。
在任意 $r>0$ 时，$q_{--}$ 为正却无底面纠缠。
经典混合和纯态不可分解性都能贡献同一事件，式 (C94.17) 保留了区分它们所需的一项信息。证毕。

## 95. 固定可见均值的任意态容量与可分离容量

**定理 C-95.1（两个固定均值的尖锐上限）。** 对定义 C-94.1 的闭集合，
并在每个状态上使用假设 C-94.3 的实际同态乘积输入，有

$$
\max_{\rho\in\mathfrak D(r,X,Y)}q_\Omega=w(r-w),\qquad
\max_{\substack{\rho\in\mathfrak D(r,X,Y)\\\sigma\ \text{separable}}}q_\Omega
=\tfrac12w(r-w).
\tag{C95.1}
$$

两个最大化都固定 $r,X,Y$，允许 $\kappa$ 变化；不是对任意预先固定的五个对角概率断言取等。

证明。因为对易投影的乘积小于各因子，
$0\preceq\Pi_{--}\preceq P_-^A$ 且 $\Pi_{--}\preceq P_-^B$。
对 $\sigma\otimes\sigma\succeq0$ 取迹，并使用式 (C94.14)，得

$$
\frac{q_\Omega}{r^2}\le\frac{1-\mathcal P_A}{2},\qquad
\frac{q_\Omega}{r^2}\le\frac{1-\mathcal P_B}{2}.
\tag{C95.2}
$$

若 $\sigma_A=\left(\begin{smallmatrix}1-x&z_A\\\bar z_A&x\end{smallmatrix}\right)$，则
$\mathcal P_A=(1-x)^2+x^2+2|z_A|^2\ge(1-x)^2+x^2$。
同理 $\mathcal P_B\ge(1-y)^2+y^2$。于是

$$
\frac{q_\Omega}{r^2}\le\min\{x(1-x),y(1-y)\}=\nu(1-\nu).
\tag{C95.3}
$$

最后的等号消费 C-84.2 的瓶颈恒等式：把每个边缘折到
$\min(x,1-x),\min(y,1-y)\in[0,1/2]$，函数 $t(1-t)$ 在该区间递增，
故最小值等于 $\nu(1-\nu)$。再乘 $r^2$ 就是 $w(r-w)$。

对可分离态，把式 (C94.6) 中每个 $\alpha_j,\beta_j$ 各作正交谱分解，
以原权重乘两个谱权重，得到归一化纯乘积向量的有限混合

$$
\sigma=\sum_j t_j|a_j\rangle\langle a_j|\otimes|b_j\rangle\langle b_j|.
\tag{C95.4}
$$

约化后分别是 $\sum_jt_j|a_j\rangle\langle a_j|$ 和
$\sum_jt_j|b_j\rangle\langle b_j|$，从而

$$
\begin{aligned}
\mathcal P&=\sum_{j,k}t_jt_k|\langle a_j|a_k\rangle|^2|\langle b_j|b_k\rangle|^2,\\
\mathcal P_A&=\sum_{j,k}t_jt_k|\langle a_j|a_k\rangle|^2,\qquad
\mathcal P_B=\sum_{j,k}t_jt_k|\langle b_j|b_k\rangle|^2.
\end{aligned}
\tag{C95.5}
$$

每个重叠模平方在 $[0,1]$ 内，权重非负，逐项比较证明
$\mathcal P\le\mathcal P_A$ 及 $\mathcal P\le\mathcal P_B$。
在式 (C94.15) 中分别用 $\mathcal P\le\mathcal P_B$ 和
$\mathcal P\le\mathcal P_A$，得

$$
\frac{q_\Omega}{r^2}\le\frac{1-\mathcal P_A}{4}\le\frac{x(1-x)}2,
\qquad
\frac{q_\Omega}{r^2}\le\frac{1-\mathcal P_B}{4}\le\frac{y(1-y)}2.
\tag{C95.6}
$$

同一最小量恒等式给因子 $1/2$ 的上界。这一步是经典可分离态纯度比较在本固定边缘问题中的应用；
以下构造同时承担两个上界的可达性。

用 C-85.2 的标签置换 $L,R,S$，其参数作用仍为

$$
L:(X,Y,\kappa)\mapsto(r-X,Y,Y-\kappa),\quad
R:(X,Y,\kappa)\mapsto(X,r-Y,X-\kappa),\quad
S:(X,Y,\kappa)\mapsto(Y,X,\kappa).
\tag{C95.7}
$$

选择实现四项最小值的因子为 $A$，必要时翻转该因子的零一标签，即可安排
$x=\nu$、$\nu\le y\le1-\nu$。这些置换保留 $r,w$、可分离性及 $q_{--}$：
在两份上同时作同一局部置换时，交换投影与之对易；交换 $A,B$ 也保留 $--$。
逆置换把任何构造送回原均值。这是坐标重标记，不是增加原生控制。

先设 $0<\nu<1/2$，令

$$
u=\frac{y-\nu}{1-2\nu}\in[0,1],\qquad
|b_0\rangle=\sqrt{1-u}|0\rangle+\sqrt u|1\rangle,\quad
|b_1\rangle=\sqrt u|0\rangle-\sqrt{1-u}|1\rangle.
\tag{C95.8}
$$

二者范数一、内积零。置 $|e_0\rangle=|0\rangle|b_0\rangle$、
$|e_1\rangle=|1\rangle|b_1\rangle$，它们为正交纯乘积向量，定义

$$
\sigma_0=(1-\nu)|e_0\rangle\langle e_0|+\nu|e_1\rangle\langle e_1|,
\qquad
|\Phi\rangle=\sqrt{1-\nu}|e_0\rangle+\sqrt\nu|e_1\rangle.
\tag{C95.9}
$$

两态的 $A$ 约化态都为 $\operatorname{diag}(1-\nu,\nu)$。
$B$ 约化态都为 $(1-\nu)|b_0\rangle\langle b_0|+\nu|b_1\rangle\langle b_1|$，
其占位均值为 $(1-\nu)u+\nu(1-u)=\nu+(1-2\nu)u=y$。
纯态中两个交叉项的任一侧偏迹均零：一侧用 $\langle b_1|b_0\rangle=0$，
另一侧用 $\langle1|0\rangle=0$。所以两态具有相同所需边缘，且

$$
\mathcal P_A=\mathcal P_B=(1-\nu)^2+\nu^2,\qquad
\mathcal P(\sigma_0)=(1-\nu)^2+\nu^2,\quad
\mathcal P(|\Phi\rangle\langle\Phi|)=1.
\tag{C95.10}
$$

代入式 (C94.15)，分别给
$q_\Omega(\sigma_0)=r^2\nu(1-\nu)/2$ 和
$q_\Omega(\Phi)=r^2\nu(1-\nu)$。

当 $\nu=1/2$ 时，原边缘必为 $x=y=1/2$。
另取任意二元正交归一基 $b_0,b_1$，仍按式 (C95.9) 定义，
两个边缘均为 $I_2/2$。这不使用分母为零的式 (C95.8)，
并分别给 $q_\Omega=r^2/8,r^2/4$。

最后，对上述任一条件态 $\sigma$，五维实现为

$$
\rho[\sigma]=(1-r)|2\rangle\langle2|+r\iota\sigma\iota^\dagger.
\tag{C95.11}
$$

两个正块支撑正交、迹之和为一；其底面质量与均值是所规定的 $r,X,Y$。
对纯条件态还可取完整纯态
$|\psi\rangle=\sqrt{1-r}|2\rangle+\sqrt r\,\iota|\Phi\rangle$，
它有相同底面压缩，却有底面—中位相干；两种实现的四符号概率相同。
逆置换后构造对每个原标签下的闭均值纤维均成立，故两个上界都是最大值。证毕。

**命题 C-95.2（固定对角约束与精确阈值的边界）。** 固定五个对角概率时，
式 (C95.1) 的两个数仍为上界，但任意态上界不必能达到。例如

$$
r=\tfrac12,\quad X=\tfrac1{10},\quad Y=\tfrac15,\quad\kappa=0
\tag{C95.12}
$$

给标准底面基序 $(00,01,10,11)$ 的归一化对角 $(2/5,2/5,1/5,0)$
（原底角序 $(0,1,3,13)$ 则为 $(2/5,1/5,2/5,0)$），且固定此对角时

$$
\max q_\Omega=\frac1{50}<\frac1{25}=w(r-w).
\tag{C95.13}
$$

证明。正半定性给 $|\sigma_{ij}|^2\le\sigma_{ii}\sigma_{jj}$，
故 $11$ 对角为零迫使其整行整列为零。
$\Omega$ 的含 $11$ 两项于是对压缩后的输入没有贡献，另外两项给

$$
\frac{q_\Omega}{r^2}=\frac12\bigl(\sigma_{10,10}\sigma_{01,01}
+|\sigma_{10,01}|^2\bigr)
\le\sigma_{10,10}\sigma_{01,01}=\frac2{25}.
$$

条件纯态 $\sqrt{2/5}|00\rangle+\sqrt{2/5}|01\rangle+
\sqrt{1/5}|10\rangle$ 达等，乘 $r^2=1/4$ 得 $1/50$。
此处 $w=1/10$，故宽度上界为 $1/25$。证毕。

对任何允许状态，精确人口概率若满足
$q_\Omega>\tfrac12w(r-w)$，则由 C-95.1 排除底面可分离。
逆命题不成立，见 C-97.2；一次或若干次有限事件也不等于已经知道精确概率超过阈值。
有限数据的风险控制使用 C-98 的单独合同。

## 96. 同一完整对角上的相干插值与凸屋顶 concurrence

**定义 C-96.1（固定正交乘积基的相干族）。** 固定 C-95.1 构造中的
$\nu,b_0,b_1,e_0,e_1$；非中心时用式 (C95.8)，中心时固定任意正交基。
对 $0\le\gamma\le1$，定义

$$
\begin{aligned}
\sigma_\gamma={}&(1-\nu)|e_0\rangle\langle e_0|+\nu|e_1\rangle\langle e_1|\\
&+\gamma\sqrt{\nu(1-\nu)}
\bigl(|e_0\rangle\langle e_1|+|e_1\rangle\langle e_0|\bigr),\\
\rho_\gamma={}&(1-r)|2\rangle\langle2|+r\iota\sigma_\gamma\iota^\dagger.
\end{aligned}
\tag{C96.1}
$$

**定理 C-96.2（固定对角的完整插值读数）。** 这些算子都是密度算子，
所有五个对角概率与两个约化态均不依赖 $\gamma$。
置 $a=\nu(1-\nu)$、$h=r^2a=w(r-w)$，则

$$
\mathcal P_A=\mathcal P_B=1-2a,\qquad
\mathcal P=1-2a(1-\gamma^2),
\tag{C96.2}
$$

$$
\begin{aligned}
q_{--}&=\tfrac h2(1+\gamma^2),&
q_{-+}=q_{+-}&=\tfrac h2(1-\gamma^2),\\
q_{++}&=r^2-\tfrac h2(3-\gamma^2),&
q_{\mathrm f}&=1-r^2.
\end{aligned}
\tag{C96.3}
$$

证明。在 $e_0,e_1$ 的支撑子空间中，矩阵是

$$
\begin{pmatrix}1-\nu&\gamma\sqrt a\\\gamma\sqrt a&\nu\end{pmatrix}.
\tag{C96.4}
$$

其迹一、对角正、行列式 $a(1-\gamma^2)\ge0$，所以正半定；
正交补上为零。$0\le\gamma<1$ 时秩二，$\gamma=1$ 时为 $|\Phi\rangle\langle\Phi|$。
$\rho_\gamma$ 的正性和归一化由式 (C95.11) 得到。
由于 $e_0,e_1$ 的 $A$ 基标签不同，它们交叉项在每个计算基向量上的对角元为零。
非中心分支中，完整五概率明确为

$$
(p_0,p_1,p_2,p_3,p_{13})=
\bigl(r(1-\nu)(1-u),\ r\nu u,\ 1-r,\ r(1-\nu)u,\ r\nu(1-u)\bigr).
\tag{C96.5}
$$

其 $X=r\nu$、$Y=r[\nu+(1-2\nu)u]$，
$\kappa=r\nu(1-u)$ 均固定。中心的 $b_0,b_1$ 可写成同样模平方参数
$u=|\langle1|b_0\rangle|^2$，式 (C96.5) 仍成立。
两个交叉项在任一侧的偏迹为零，理由与 C-95.1 相同，故

$$
\sigma_A=(1-\nu)|0\rangle\langle0|+\nu|1\rangle\langle1|,
\quad
\sigma_B=(1-\nu)|b_0\rangle\langle b_0|+\nu|b_1\rangle\langle b_1|.
\tag{C96.6}
$$

正交性给两个局部纯度 $1-2a$。把式 (C96.4) 平方取迹，得到
$(1-\nu)^2+\nu^2+2\gamma^2a=1-2a(1-\gamma^2)$。
将三项纯度代入式 (C94.15)，逐项化简给式 (C96.3)；四项之和恰为 $r^2$。证毕。

**定理 C-96.3（该族的凸屋顶精确值）。** 采用标准两二元因子 concurrence 的凸屋顶定义

$$
\mathcal C(\sigma)=\inf_{\sigma=\sum_jt_j|\phi_j\rangle\langle\phi_j|}
\sum_jt_j\,2|\det B_j|,
\quad t_j\ge0,\quad\sum_jt_j=1,\quad\|\phi_j\|=1,
\tag{C96.7}
$$

其中 $B_j$ 是 $\phi_j$ 的标准 $2\times2$ 系数矩阵。则

$$
\mathcal C(\sigma_\gamma)=2\gamma\sqrt{\nu(1-\nu)},\qquad
\mathcal C(\sigma_\gamma)^2=\frac8{r^2}
\left(q_\Omega-\tfrac12w(r-w)\right).
\tag{C96.8}
$$

定义及一般两量子位凸屋顶的经典来源为 Wootters，
*Entanglement of Formation of an Arbitrary State of Two Qubits*，
[quant-ph/9709029v2](https://arxiv.org/abs/quant-ph/9709029v2)，式 (7)、(10)、(19)–(22)
及等 concurrence 分解的证明。此处对所给支撑另给上下界一致的直接计算，
不把一般混态事件概率等同于 concurrence。

证明。先以局部酉换基把 $b_0,b_1$ 送到 $|0\rangle,|1\rangle$，
于是 $e_0,e_1$ 送到 $00,11$。
纯态系数矩阵在局部酉下变为 $UBV^{\mathsf T}$，其行列式模不变；
该变换双射地对应所有纯态分解，所以凸屋顶也不变。

对任意分解及任意位于 $\operatorname{span}\{00,11\}$ 正交补内的 $v$，有

$$
0=\langle v|\sigma_\gamma|v\rangle
=\sum_jt_j|\langle v|\phi_j\rangle|^2.
\tag{C96.9}
$$

每项非负；取正交补的一组基，说明每个 $t_j>0$ 的纯成分都在该二维空间内。
因此写成 $a_j|00\rangle+b_j|11\rangle$，$|a_j|^2+|b_j|^2=1$，
纯态 concurrence 恰为 $2|a_jb_j|$。
这个论证也适用于 $\gamma=1$ 的更小实际支撑。
用交叉矩阵元及三角不等式，任意分解满足

$$
\sum_jt_j\,2|a_jb_j|
\ge2\left|\sum_jt_ja_j\bar b_j\right|
=2|(\sigma_\gamma)_{00,11}|=2\gamma\sqrt a.
\tag{C96.10}
$$

另一方面，下面是含实际归一化纯成分的分解：

$$
\sigma_\gamma=
\gamma|\Phi\rangle\langle\Phi|
+(1-\gamma)(1-\nu)|e_0\rangle\langle e_0|
+(1-\gamma)\nu|e_1\rangle\langle e_1|.
\tag{C96.11}
$$

三个权重非负且和为一，展开给式 (C96.1)；两个 $e_i$ 是乘积态，
而 $\Phi$ 的 concurrence 为 $2\sqrt a$。
所以此分解的平均值是 $2\gamma\sqrt a$，达到下界。
由式 (C96.3) 的 $q_{--}-h/2=h\gamma^2/2$ 得第二式。证毕。

$\gamma=0$ 可分离，$\gamma>0$ 时任何纯乘积分解都会有零平均 concurrence，
与式 (C96.10) 矛盾，所以条件态纠缠。
$\gamma$ 描述密度矩阵中相干项的保留量；$\gamma<1$ 时的混态
不具有一个由纯振幅唯一决定的 $\chi$。不同纯态分解也不能被指定为唯一隐藏纯相位。

**命题 C-96.4（全五概率均匀且规范概率圆不变的家族）。** 取

$$
r=\frac45,\quad\nu=\frac12,\quad
|b_0\rangle=|+\rangle=\frac{|0\rangle+|1\rangle}{\sqrt2},\quad
|b_1\rangle=|-\rangle=\frac{|0\rangle-|1\rangle}{\sqrt2}.
\tag{C96.12}
$$

则式 (C96.1) 给所有 $\gamma$ 下 $p_s=1/5$，
$X=Y=2/5$、$\kappa=1/5$、$w=2/5$、$h=4/25$，且

| $\gamma$ | 底面可分离 | $\mathcal C$ | $q_{--}$ | $q_{-+}$ | $q_{+-}$ | $q_{++}$ | $q_{\mathrm f}$ |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| $0$ | 是 | $0$ | $2/25$ | $2/25$ | $2/25$ | $2/5$ | $9/25$ |
| $1/2$ | 否 | $1/2$ | $1/10$ | $3/50$ | $3/50$ | $21/50$ | $9/25$ |
| $1$ | 否 | $1$ | $4/25$ | $0$ | $0$ | $12/25$ | $9/25$ |

证明。每个底角条件概率为 $1/4$，乘 $4/5$ 后为 $1/5$，
中模式同为 $1/5$；其余参数由定义计算。
式 (C96.8) 在 $\nu=1/2$ 给 $\mathcal C=\gamma$，
表中全部事件由式 (C96.3) 逐项代入。

这里的“概率圆”准确消费 C-67.2、C-76.1、C-84.3 的规范定义：
对底面正表 $H=\left(\begin{smallmatrix}p_0&p_3\\p_1&p_{13}\end{smallmatrix}\right)$
作正行列平衡后取面积 $\pi$ 的带标记协方差椭圆，

$$
\eta=\frac18\log\frac{p_0p_{13}}{p_1p_3}=0,\qquad
 e^{-2\eta}z_+^2+e^{2\eta}z_-^2=1.
\tag{C96.13}
$$

所以该规范椭圆始终是单位圆。
它不是全五态占位变量 $(B_L,B_R)$ 的无条件协方差椭圆：后者满足
$\mathbb E B_L=\mathbb E B_R=2/5$、$\mathbb E B_LB_R=1/5$，故

$$
\operatorname{Cov}(B_L,B_R)=
\begin{pmatrix}6/25&1/25\\1/25&6/25\end{pmatrix}.
\tag{C96.14}
$$

特征值 $7/25,1/5$ 不等，那个椭圆并非圆。
因此相同的五个顶点权重、隐藏高度和规范概率圆，仍容许表中不同的混态联合结构。证毕。

## 97. 双事件纯度差、保留率与不完备的纠缠见证

**命题 C-97.1（固定对照的纯度差与条件比例）。** 在实际独立同态双副本合同下，

$$
q_{--}-q_{-+}=\frac{r^2}{2}(\mathcal P-\mathcal P_B),\qquad
q_{--}-q_{+-}=\frac{r^2}{2}(\mathcal P-\mathcal P_A).
\tag{C97.1}
$$

若任一差严格为正，底面条件态纠缠。预先选择比较 $--$ 与 $-+$，其保留率为

$$
H_A:=q_{--}+q_{-+}=\frac{r^2}{2}(1-\mathcal P_A).
\tag{C97.2}
$$

当且仅当 $H_A>0$ 才定义

$$
\theta=\frac{q_{--}}{H_A}.
\tag{C97.3}
$$

可分离态在此域中满足 $\theta\le1/2$，而 C-96 的家族满足
$H_A=h=w(r-w)>0$、$\theta=(1+\gamma^2)/2$。

证明。式 (C94.15) 相减分别消去 $\mathcal P_A$ 和 $\mathcal P_B$，
得到式 (C97.1) 的准确因子次序；相加给式 (C97.2)。
对可分离态，式 (C95.5) 给 $\mathcal P\le\mathcal P_A,\mathcal P_B$，
所以两个差都不正；逆否即给充分见证。
当分母正时，$\theta\le1/2$ 等价于 $q_{--}\le q_{-+}$。
两项中的 $r^2$ 消去，但保留事件自身的发生率仍是 $H_A$。
对 C-96 家族，式 (C96.3) 相加并相除就给声明的值。
若 $H_A=0$，两项非负且和为零，所以均为零，$\theta$ 未定义。
$w>0$ 并不排除这个分支：条件纯乘积态 $|+\rangle_A|+\rangle_B$
有 $x=y=1/2$、$w=r/2>0$，但 $\mathcal P_A=1$，故 $H_A=0$。证毕。

式 (C97.1) 的机制是经典 Mintert–Buchleitner 见证，非新的普适纠缠判据。
其 [quant-ph/0605250v3](https://arxiv.org/abs/quant-ph/0605250v3) 式 (2)–(3)
在本参数中还给

$$
\mathcal C(\sigma)^2\ge\frac4{r^2}
\max\{0,q_{--}-q_{-+},q_{--}-q_{+-}\}.
\tag{C97.4}
$$

文中的 $4P_-^A(P_-^B-P_+^B)$ 对应 $4(q_{--}-q_{-+})/r^2$，
$4(P_-^A-P_+^A)P_-^B$ 对应另一个差。
C-96 家族的两个差均为 $h\gamma^2$，式 (C96.8) 表明其饱和这个经典下界。
相消未知质量只简化比例的判定，不消去获得一个保留事件之前支付的完整试验。

**命题 C-97.2（负部分转置而两个见证均不通过）。** 在声明的两因子中取

$$
|\Phi^+\rangle=\frac{|00\rangle+|11\rangle}{\sqrt2},\qquad
\sigma_{\rm iso}=\frac12|\Phi^+\rangle\langle\Phi^+|+\frac18 I_4.
\tag{C97.5}
$$

它纠缠，却满足

$$
\lambda_{\min}(\sigma_{\rm iso}^{T_B})=-\frac18,\qquad
\frac{q_{--}}{r^2}=\frac7{64},\qquad
\frac{q_{-+}}{r^2}=\frac{q_{+-}}{r^2}=\frac9{64},\qquad
\frac{q_{++}}{r^2}=\frac{39}{64}.
\tag{C97.6}
$$

证明。以 $T_B$ 表示在 $B$ 计算基的转置。
$|\Phi^+\rangle\langle\Phi^+|$ 的部分转置为完整两因子交换算子 $F/2$，
故 $\sigma_{\rm iso}^{T_B}=F/4+I_4/8$。
$F$ 在三维对称空间为 $+1$、一维反对称空间为 $-1$，
所以谱为 $3/8,3/8,3/8,-1/8$。
可分离态必为正部分转置：每项 $\alpha_j\otimes\beta_j$ 转成
$\alpha_j\otimes\beta_j^{\mathsf T}\succeq0$，因为转置保持正性，
其非负凸组合仍正。负特征值因此排除可分离；这里只用必要性，不需要 PPT 充分性。

$\sigma_{\rm iso}$ 本身在 $\Phi^+$ 方向的特征值是 $5/8$，另外三个为 $1/8$，
故 $\mathcal P=(25+3)/64=7/16$。两个约化态均为 $I_2/2$，
$\mathcal P_A=\mathcal P_B=1/2$。代入式 (C94.15) 给全部四项。
此态 $x=y=1/2$，所以 $\tfrac12w(r-w)=r^2/8=8r^2/64$，
单事件容量见证也不通过；双事件差则严格为负。
五维实现用式 (C95.11) 即可。证毕。

因此未超过容量阈值、未出现正纯度差或有限记录未越界，均不能反推可分离。
经典可分离混合的正事件、这里的见证漏检和 C-100 的相关副本，是三种不同边界。


**约定 C-97.3（对照概率与有限记录的连接）。** 使用同一五维测量及预先固定对照的
[续卷 C-98–C-101](AURIC_FIB_ATOM_HIDDEN_RELATIONS_MIXED_STATE_CAPACITY_AND_CERTIFICATION.md#98-全部成对试验上的随时有效认证)
给条件乘积来源的全时间风险界、固定 iid 相干族的付费停止成本，以及相同单份边缘的相关配对反例。

## 追加锚（本行以下为增补区）
