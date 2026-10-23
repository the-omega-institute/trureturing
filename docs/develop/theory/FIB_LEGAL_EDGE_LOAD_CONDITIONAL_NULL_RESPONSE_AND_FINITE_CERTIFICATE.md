# FIB 合法边调和负载：条件零响应与有限证书

本卷只作普通数学陈述。可见空间、目标和隐藏生产者均保持原定义。令

$$
X=\{x\in\{0,1\}^{\mathbb Z}:x_ix_{i+1}=0\ (i\in\mathbb Z)\},\quad
B_n=\{w\in\{0,1\}^n:w_iw_{i+1}=0\ (1\le i<n)\},\quad \mathcal E_i=\sigma(X_j:j\ne i),
$$

$$
h(s,t)=\begin{cases}st/(s+t)&s+t>0,\\0&s=t=0,\end{cases}\qquad
\Phi_n(\mu)=\sum_{\{b,c\}\in E(\Gamma_n)}h(\mu_b,\mu_c),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu).
$$

这里 $\Gamma_n$ 是完整开放路径词图：全零词、合法端点 $1$、所有接缝、强制单点和零总质量纤维都保留；不存在首尾相接约束。记 $c_\star=\lim_n\kappa_n/n$。$X_i$ 是坐标变量，$(Tx)_i=x_{i+1}$；$[w]_a$ 是从 $a$ 开始的词柱，$[w]=[w]_1$，$P_n$ 是 $P$ 在 $[1,n]$ 的实际边缘。

## 1. 供应接口和同律表示

[Stationary] §2 给出每个归一化两侧平稳合法律 $P$ 的实际外部后验 $q_i=\mathbb E_P[X_i\mid\mathcal E_i]$、风险恒等式

$$
d(P)=\lim_n\Phi_n(P_n)/n
=\mathbb E_P[(X_0-q_0)^2]=\inf_{r\ge0}D_r(P)\le c_\star.
$$

$D_r$ 使用半径 $r$ 的真实可见外部，$r=0$ 的字段为平凡字段。有限纤维恒等式把每条原始 Hamming 边的调和项识别为二点条件 Brier 风险，并允许零质量和强制零纤维。[Growth] 定理 5.2、7.3 和推论 5.3 给出

$$
nc_\star\le\kappa_n\le(n+1)c_\star,\qquad
\frac{1800}{12559}\le c_\star\le\bar c:=3-2\sqrt2.
$$

[Universal Posterior Defect] 定理 3.1 给出：若 $d(P)=c_\star$，则每个自由外部后验在 $[1/4,1/2]$ 内，全部合法柱正，且 $n c_\star\le\Phi_n(P_n)\le\kappa_n$。以下“达到律”恒指这样的归一化两侧平稳合法律。

对任意整数 $N\ge1$，完整边发射域是 [Universal Posterior Defect] 定义 4.1 的

$$
\Theta_N=\{(\lambda,M_0,M_1):\lambda\ge0,\ \lambda\mathbf1=1,
M_0,M_1\in\mathbb R_{\ge0}^{N\times N},
A=M_0+M_1,\ A\mathbf1=\mathbf1,\ \lambda A=\lambda,
\lambda M_1^2\mathbf1=0\}.
$$

$\lambda$ 为行向量，$M_w=M_{w_1}\cdots M_{w_n}$，空词矩阵为单位阵。该供应卷命题 4.2 给出的一个实际归一化两侧平稳联合律具有 $H_i\in\{1,\ldots,N\}$，其区间概率为

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^bM_{x_i}(h_i,h_{i+1}),\qquad
P_\theta([w]_a)=\lambda M_w\mathbf1.
$$

所有模型专用的变量、后验和期望都取在这个 $J_\theta$ 的可见边缘 $P_\theta$ 下，不另行拼接条件表。联合律的左右相容分别由 $A\mathbf1=\mathbf1$ 和 $\lambda A=\lambda$ 保证；每位置 $11$ 的零概率及可数并保证合法性。

给定任意 $\theta\in\Theta_N$，由 [P7 separation] 引理 8.2 可裁掉 $\lambda_i=0$ 的状态：非负平稳流使保留集合对 $M_0,M_1$ 闭，裁剪保留全部柱概率；其 $\lambda$ 全正且 $M_1^2=0$。这只是同律约化。通常“先按状态发射再转移”的约定由 $M_x=\operatorname{diag}(e_s(x))A$ 接入；可见律平稳而隐藏初始未平稳时，供应命题 4.2 的 Cesàro 约化保持同维数与全部可见柱。反向三元组状态 $(s,x,t)$ 给至多 $2N^2$ 个确定性状态发射状态。两种约定的最小维数不由这些对应判等。

## 2. 一侧缺陷预算

固定任意达到律 $P$，置 $c=d(P)=c_\star$、$q_i=\mathbb E_P[X_i\mid\mathcal E_i]$、$\ell_i=(X_i-q_i)^2$。后验均取 $[0,1]$ 版本，并可取 $q_i=q_0\circ T^i$。本节及一般响应定理的全部期望均属于这个 $P$。令

$$
p^L_r=\mathbb E_P[X_0\mid X_{-r},\ldots,X_{-1},X_1,X_2,\ldots],\quad
p^R_r=\mathbb E_P[X_0\mid\ldots,X_{-2},X_{-1},X_1,\ldots,X_r],
$$

$$
e_L(r)=\mathbb E_P(q_0-p^L_r)^2,\quad e_R(r)=\mathbb E_P(q_0-p^R_r)^2,\quad
\tau(R)=\sum_{r\ge R}(e_L(r)+e_R(r)),\qquad r,R\in\mathbb N.
$$

空坐标列表不提供信息。条件投影、原纤维恒等式和有限图上界给出

$$
\sum_{r=0}^{m-1}(e_L(r)+e_R(r))\le c\quad(m\ge1),\qquad
\tau(0)\le c,\quad \tau(R)\downarrow0,
\tag{2.1}
$$

$$
0\le D_r(P)-c\le\frac{c}{r+1}.
\tag{2.2}
$$

证明这些预算，令 $u_{n,i}=\mathbb E_P[X_i\mid\sigma(X_j:1\le j\le n,j\ne i)]$。投影正交性给

$$
0\le\sum_{i=1}^n\mathbb E_P(q_i-u_{n,i})^2
=\Phi_n(P_n)-nc\le c.
$$

取 $n\ge2m$；首 $m$ 个有限字段各包含于对应 $p^L_0,\ldots,p^L_{m-1}$ 的平移字段，末 $m$ 个包含于对应 $p^R_{m-1},\ldots,p^R_0$ 的平移字段。精化条件减小平方缺陷，平稳性遂给（2.1）的部分和界。非负级数给其尾界及尾趋零。在长 $r+1$ 区间，每个去中心有限字段都包含于该坐标的半径 $r$ 字段；故上述和至少为 $(r+1)(D_r(P)-c)$，得到（2.2）。这是达到律的边界预算，不需有限隐藏、混合、不可约或收缩假设。

## 3. 条件零响应定理

对有限区间 $C=[1,L]$、$L\ge1$，取任意 $f:B_L\to\mathbb R$，置 $f_C=f(X_1,\ldots,X_L)$、$F=\max_{w\in B_L}|f(w)|$、$\mathcal H_C=\sigma(X_j:j\notin C)$。一般定理的方向假设是同一个达到律 $P$ 下的

$$
\mathbb E_P[f_C\mid\mathcal H_C]=0.
\tag{3.1}
$$

矩阵充分条件另有明确对应：对任意 $\theta\in\Theta_N$，在实际律 $P=P_\theta$ 下，若

$$
\sum_{w\in B_L}f(w)M_w=0,
\tag{3.2}
$$

则（3.1）成立，不需先假设达到。确实，对任意有限外部柱集 $H$，未指定位的发射相加为 $A$，同一 $J_\theta$ 的联合概率给

$$
\mathbb E_{P_\theta}[\mathbf1_Hf_C]
=\lambda U\Big(\sum_{w\in B_L}f(w)M_w\Big)V\mathbf1=0.
$$

$U,V$ 是对应外部指定及缺失坐标的有限矩阵乘积；有限并用线性性处理。包括没有左右外部指定的空乘积。有限柱生成 $\mathcal H_C$，有界单调类扩张给（3.1）。矩阵式只对其所表示的 $P_\theta$ 作此推论；应用下面定理还须 $d(P_\theta)=c_\star$。

**定理 3.1（条件零响应与绝对可和）。** 对每个达到律 $P$ 和满足（3.1）的上述 $C,f$，级数

$$
S_P(f)=\sum_{i\in\mathbb Z}\mathbb E_P[f_C\ell_i]
\tag{3.3}
$$

绝对收敛，且

$$
S_P(f)=0,\qquad
\sum_{i\notin C}|\mathbb E_P[f_C\ell_i]|
\le F\tau(0)\le Fc,\qquad
\left|\sum_{i\in C}\mathbb E_P[f_C\ell_i]\right|\le Fc.
\tag{3.4}
$$

**证明。** 若 $i\le0$，令 $\mathcal G_i^C=\sigma(X_j:j\le0,j\ne i)$；若 $i\ge L+1$，令 $\mathcal G_i^C=\sigma(X_j:j\ge L+1,j\ne i)$。置 $p_i=\mathbb E_P[X_i\mid\mathcal G_i^C]$。$X_i,p_i$ 及 $(X_i-p_i)^2$ 都是 $\mathcal H_C$ 可测的；$f_C$ 是 $\mathcal E_i$ 可测的。先用（3.1），再条件于 $\mathcal E_i$ 消去投影交叉项，得到

$$
0=\mathbb E_P[f_C(X_i-p_i)^2]
=\mathbb E_P[f_C\ell_i]+\mathbb E_P[f_C(q_i-p_i)^2].
\tag{3.5}
$$

这里没有假设 $f_C$ 对 $\mathcal H_C$ 可测。左侧 $i=-r$ 的平方缺陷是 $e_R(r)$，右侧 $i=L+1+r$ 的是 $e_L(r)$。因此外部绝对和至多 $F\tau(0)$，距离块至少 $R+1$ 的外部尾至多 $F\tau(R)$。块内只有 $L$ 项，故（3.3）绝对收敛。

对实数 $t$ 满足 $|t|F\le1/2$，令 $g_C=1+tf_C$、$R_t=g_CP$。（3.1）使 $R_t$ 归一化且保留 $\mathcal H_C$ 上全部边缘；密度在 $[1/2,3/2]$ 内，所以两律等价并同样合法。记任意中间律 $R$ 的后验为 $q_i(R)=\mathbb E_R[X_i\mid\mathcal E_i]$，风险为 $r_i(R)=\mathbb E_R[(X_i-q_i(R))^2]$。

块外 $g_C$ 是 $\mathcal E_i$ 可测的，故 $q_i(R_t)=q_i$。块内在自由外部的条件二点律上，令 $f_a$ 为把第 $i$ 位设为 $a$ 的 $f_C$ 值，直接条件化给

$$
q_i(R_t)-q_i=
\frac{tq_i(1-q_i)(f_1-f_0)}
{1+t((1-q_i)f_0+q_if_1)},\qquad |q_i(R_t)-q_i|\le |t|F.
$$

强制零外部后验仍零；概率零的外部集合可任选版本，不影响积分。所有有限零总质量纤维仍零总质量，不作除法，加权项为零。由 $\mathbb E_R\ell_i=r_i(R)+\mathbb E_R[q_i(R)-q_i]^2$ 的条件 Brier 正交分解，得到绝对收敛的总增量

$$
\Delta(t):=\sum_i(r_i(R_t)-c)
=tS_P(f)-\sum_{i\in C}\mathbb E_{R_t}[q_i(R_t)-q_i]^2,\qquad
0\le tS_P(f)-\Delta(t)\le LF^2t^2.
\tag{3.6}
$$

为放大增量，固定整数 $m\ge1$ 和上述 $t$，取 $m$ 个互不相交的平移块 $C_j=[a_j,a_j+L-1]$，置 $f_j=f(X_{a_j},\ldots,X_{a_j+L-1})$、$g_j=1+tf_j$、$G=\prod_jg_j$、$R=GP$。平稳性把（3.1）转移至每块；其他因子对该块外部可测，逐个条件消去得 $\mathbb E_PG=1$，并保留整个块并集外字段 $\sigma(X_i:i\notin\cup_jC_j)$ 上的联合边缘。在 $i\in C_j$，其他因子对 $\mathcal E_i$ 可测而在条件后验分子分母中相消，故 $q_i(R)=q_i(g_jP)$；并集外 $q_i(R)=q_i$。置 $d_i=q_i(g_jP)-q_i$ 于 $C_j$ 内，并集外置 $d_i=0$，则

$$
r_i(R)-c=\mathbb E_P[(G-1)\ell_i]-\mathbb E_P[G\,d_i^2].
\tag{3.7}
$$

以下说明块间距趋无穷的极限，不用独立性。记 $B=(1+|t|F)^{m-1}$。展开 $G-1=\sum_jtf_jh_j$，其中 $h_j=\prod_{k<j}g_k$ 且 $|h_j|\le B$。对全部块外的 $i$，$f_jh_j$ 是 $\mathcal E_i$ 可测的，$h_j$ 是 $C_j$ 外部可测的；（3.5）的同一投影计算给

$$
|\mathbb E_P[f_jh_j\ell_i]|
\le FB\,\mathbb E_P(q_i-p_i^{\,j})^2.
$$

$p_i^{\,j}$ 用 $C_j$ 相应一侧的字段定义。对整数 $K\ge0$，令 $U_j(K)$ 为 $C_j$ 向两端各扩 $K$ 位的区间，则

$$
\sum_{i\notin\cup_jU_j(K)}|r_i(R)-c|
\le m|t|FB\,\tau(K).
\tag{3.8}
$$

此界对块间距一致，也证明每个固定复制律的总增量绝对收敛。

在固定 $U_j(K)$ 中，$\ell_i$ 以及块内 $d_i^2$ 都是有界可测函数，能在 $L^1(P)$ 中由该位置附近的有限柱函数逼近；这是有限坐标字段递增生成全字段的条件期望收敛。平稳性使平移后的误差相同，$G\le(3/2)^m$ 一致控制积分误差。对这样的有限柱函数 $H$，当其他块在其坐标支撑之外时，逐个条件消去给 $\mathbb E_P[GH]=\mathbb E_P[g_jH]$。固定 $m,t,K$ 与逼近半径，送所有块的最小间距至无穷，再令逼近误差为零，（3.7）在这些有限邻域上的和趋于单块对应和的 $m$ 倍。最后用（3.8）和单块尾界 $|t|F\tau(K)$ 令 $K\to\infty$，得

$$
\sum_i(r_i(R)-c)\longrightarrow m\Delta(t).
\tag{3.9}
$$

任意归一化合法中间律 $R$ 和有限区间 $I$ 上，全外部条件精化有限去中心字段，原纤维恒等式及有限图上界遂给

$$
\sum_{i\in I}r_i(R)\le\Phi_{|I|}(R_I)
\le\kappa_{|I|}\le(|I|+1)c_\star.
$$

对上面绝对可和的改变，以区间穷尽 $\mathbb Z$ 得 $\sum_i(r_i(R)-c)\le c_\star$；这是带符号净增量的上界。若 $S_P(f)\ne0$，取符号使 $tS_P(f)>0$，再取充分小的 $t$ 使（3.6）给 $\Delta(t)>0$，最后固定 $m$ 使 $m\Delta(t)>c_\star$。（3.9）与上界矛盾。故 $S_P(f)=0$；结合外部绝对界得到（3.4）的块内界。$F=0$ 时全部项直接为零。$\square$

## 4. 直接有限证书

对任意整数 $N,L\ge1$、$r\ge0$、候选 $\theta\in\Theta_N$ 和满足（3.2）的 $f:B_L\to\mathbb R$，全部对象明确取在该候选的实际 $P_\theta$ 下。对 $i=1,\ldots,L$ 令

$$
q^\theta_{r,i}=\mathbb E_{P_\theta}[X_i\mid
\sigma(X_{i-r},\ldots,X_{i-1},X_{i+1},\ldots,X_{i+r})],\qquad
T_{L,r}(\theta,f)=\sum_{i=1}^L
\mathbb E_{P_\theta}[f_C(X_i-q^\theta_{r,i})^2].
\tag{4.1}
$$

具体地，半径 $r$ 外部词为 $u,v$ 时，正总质量原子上的 $q^\theta_{r,i}$ 等于

$$
\frac{\lambda M_uM_1M_v\mathbf1}{\lambda M_uAM_v\mathbf1}.
$$

分母为零时取零而加权风险为零；强制中心原子的分子为零。$r=0$ 用两个空词。故（4.1）完全由同一个 $P_\theta$ 在 $[1-r,L+r]$ 的有限柱概率决定，包括 $f_C$ 与窗口的重叠。

仅为推导必要界，假设这个候选满足 $d(P_\theta)=c_\star$，并置 $P=P_\theta$、$c=c_\star$、$q_i=\mathbb E_{P_\theta}[X_i\mid\mathcal E_i]$。矩阵桥与定理 3.1 给块内响应界，投影给 $\mathbb E_{P_\theta}(q_i-q^\theta_{r,i})^2=D_r(P_\theta)-c$。由 $|(X-a)^2-(X-b)^2|\le2|a-b|$、Cauchy–Schwarz 和（2.2），

$$
|T_{L,r}(\theta,f)|\le Fc+2LF\sqrt{\frac{c}{r+1}}.
\tag{4.2}
$$

因此，量词仍遍历任意上述候选 $\theta\in\Theta_N$：若其某个精确矩阵零方向严格满足

$$
|T_{L,r}(\theta,f)|>F\bar c+2LF\sqrt{\frac{\bar c}{r+1}},
\tag{4.3}
$$

则 $d(P_\theta)<c_\star$。证明是对这个同律候选假设达到后用（4.2）产生矛盾：右侧随非负 $c$ 单调且 $c_\star\le\bar c$；再用全平稳律的 $d(P_\theta)\le c_\star$ 得严格非达到。证书可在裁剪前或裁剪后的表示上使用；它只排除产生该证书的同律，不给统一 $L,r,f$ 或证书存在性。

## 5. 适用域、归属和未决问题

一般定理 3.1 的完整前提是归一化两侧平稳合法达到律及实际条件零均值；有限隐藏不是前提。矩阵桥和证书（4.3）遍历任意有限 $N$ 的完整精确实数、非负 $\Theta_N$，允许结构零、零平稳质量、可约链、周期链和任意接缝。预算与零响应不在未假设达到的任意模型上宣称成立。全零词、端点词、强制纤维和零总质量纤维始终保留。$R_t$ 与复制律只是归一化合法有限密度改变，不必平稳或有限隐藏；所需事实是每个实际有限边缘仍在原完整单纯形。

[Positive Unique Optimizer] 定理 3.1 和式（3.11）是 [Universal Posterior Defect] 普适后验及支撑结果的前置；本卷复用其结果。[Growth] 供应有限图上界，[Stationary] 供应原调和风险身份；完整 $\Theta_N$ 联合律明确归于 [Universal Posterior Defect] 定义 4.1、命题 4.2。[Ergodic Full Support]、[Nonattainment] 与 [Finite Visible Completeness] 分别保留遍历达到、有限可见阶严格非达到及逼近边界，不能把有限隐藏生成转成有限可见记忆。[P7 separation] 的零质量裁剪、$N_+\le3$ 与秩一重置排除仍是已有边界。

成熟机制的方法归属是 [Dawid–Lauritzen–Parry] arXiv:1104.2224v2，§§4.2.1–4.2.2、例 4.4、式（14）的条件 Brier／ratio matching 平方差，以及 [van Enter–Verbitskiy] arXiv:1001.3122v1，Definition 4、Theorems 5–6 的外部擦除不确定性背景。前者的全乘积空间论证要求处处正概率；后者涉及 Shannon 擦除熵，Theorem 6 另有 Gibbs 前提。两者都不供应本卷的调和目标、矩阵零响应或有限证书；所需二点代数和条件投影已在原合法纤维上证明，不移用估计或 Gibbs 结论。相对这些供应，达到律的一侧预算、条件零响应和有限严格违反消费者是本卷的普通综合，不作世界优先性或内核核验宣称。

[UDB] 的确定性有限关系源、共同字面描述符、联合 Presburger／完整行及 read/update/halt 条件，没有在此转换为随机隐藏生产者或调和风险的假设。观察器状态数不是生产者资源；本卷不增加观察端口或样本，不给资源等价、取得效率、有限样本保证、最优律唯一性、物理或实际机器学习收益。

仍未解决的原问题是：任意有限非重置、$N_+\ge4$ 的准确隐藏生产者是否存在达到 $c_\star$ 的同律。矩阵零空间维数、有限依赖条目数或秩锥信息既不推出 $S_P(f)\ne0$，也不推出（4.3）的违反。下一步须证明一个对任意精确达到者都成立的生产性有限见证，或给出明确达到者。单个 $(L,r,f)$ 证书只排除其对应律；固定 $N$ 的全域排除仍需覆盖完整紧集 $\Theta_N$。任意有限非重置域的统一排除和任意有限达到问题均保持开放，没有由必要响应条件推出全有限排除的推论。

[Stationary]: FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[Ergodic Full Support]: FIB_LEGAL_EDGE_LOAD_ERGODIC_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[Universal Posterior Defect]: FIB_LEGAL_EDGE_LOAD_UNIVERSAL_POSTERIOR_DEFECT_AND_FINITE_HIDDEN_SEPARATION.md
[Positive Unique Optimizer]: FIB_LEGAL_EDGE_LOAD_POSITIVE_UNIQUE_OPTIMIZER.md
[Growth]: FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[Finite Visible Completeness]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_COMPLETENESS.md
[Nonattainment]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_NONATTAINMENT.md
[P7 separation]: FIB_LEGAL_EDGE_LOAD_RENEWAL_CLOSURE_SEPARATION_AND_OBSERVABLE_DEPENDENCE.md
[UDB]: RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_DESCRIPTOR_BOUNDARY.md
[Dawid–Lauritzen–Parry]: https://arxiv.org/html/1104.2224v2
[van Enter–Verbitskiy]: https://arxiv.org/html/1001.3122v1

## 追加锚（本行以下为增补区）
