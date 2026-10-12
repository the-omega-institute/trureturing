# FIB 合法边调和负载：普适后验缺陷与有限隐藏维数分离

## 1. 完整词域、实际概率律与供应结果

**定义 1.1（完整开放路径目标；[增长卷][G] 定义 2.2、2.4）。** 对 $n\ge1$ 令

$$
B_n=\{b\in\{0,1\}^n:b_jb_{j+1}=0\ (1\le j<n)\},\qquad k(b)=\sum_{j=1}^n b_j.
$$

$\Gamma_n$ 的顶点是全部 $B_n$，边是全部合法 Hamming 一位差词对。测试插入时约定 $b_0=b_{n+1}=0$，但不把首尾相接。对整个概率单纯形 $\mathcal P(B_n)$ 定义

$$
h(s,t)=\begin{cases}st/(s+t),&s+t>0,\\0,&s=t=0,\end{cases}\qquad
\Phi_n(\mu)=\sum_{\{b,c\}\in E(\Gamma_n)}h(\mu_b,\mu_c),\qquad
\kappa_n=\max_{\mu\in\mathcal P(B_n)}\Phi_n(\mu).
\tag{1.1}
$$

零质量不删除顶点或边；全零词、合法端点 $1$ 及任意分组接缝上的边都保留。

**定义 1.2（一个实际平稳律；[平稳卷][S] §2）。** 令

$$
X=\{x\in\{0,1\}^{\mathbb Z}:x_jx_{j+1}=0\ (j\in\mathbb Z)\},\quad
(Tx)_j=x_{j+1},\quad X_j(x)=x_j.
$$

$[w]_a$ 指坐标 $a,\ldots,a+|w|-1$ 等于 $w$ 的柱集，$[w]=[w]_1$。$P$ 恒为 $X$ 上一个归一化 Borel 概率律；平稳指 $T_*P=P$。$P_n$ 是它在 $1,\ldots,n$ 上的实际边缘。置

$$
\mathcal E_i=\sigma(X_j:j\ne i),\quad F_i=\{X_{i-1}=X_{i+1}=0\},\quad
\mathcal F_r=\sigma(X_{-r},\ldots,X_{-1},X_1,\ldots,X_r),
$$

$$
q=\mathbb E_P[X_0\mid\mathcal E_0],\quad q_r=\mathbb E_P[X_0\mid\mathcal F_r],\quad
D_r(P)=\mathbb E_P[(X_0-q_r)^2],\quad I=[1/4,1/2].
\tag{1.2}
$$

条件期望取值在 $[0,1]$，均只按所属律的几乎处处等价类解释。合法性给出 $q=0$ 于 $F_0^c$。有限零总质量纤维的后验可任取，其加权项为零。

**约定 1.3（供应前提及其归属）。** [增长卷][G] 引理 3.1、定理 3.2、5.2 给出 $h$ 的连续、凹及一次齐次性，并给出

$$
c_\star=\lim_{n\to\infty}\kappa_n/n,\qquad
n c_\star\le\kappa_n\le(n+1)c_\star,\qquad
\kappa_n/(n+1)\longrightarrow c_\star.
\tag{1.3}
$$

[唯一最优卷][O] 定理 3.1 给出每个 $n$ 的正最大点 $\pi^{(n)}$，在每条合法插入边上满足

$$
\tfrac13\pi^{(n)}_b\le\pi^{(n)}_{b+e_i}\le\pi^{(n)}_b.
\tag{1.4}
$$

该卷式（3.11）拥有整个有限单纯形上的精确平方差恒等式。以下只改写其后验表达并作平稳极限推论，不把该恒等式作为新结果。

[平稳卷][S] 式（2.1）–（2.6）给出，对每个平稳 $P$，无支撑或记忆假设，

$$
\begin{aligned}
D_r(P)&=\sum_{\substack{u,v\in B_r\\u_r=v_1=0}}h(P([u0v]),P([u1v])),\\
D_r(P)&\downarrow d(P):=\lim_{n\to\infty}\Phi_n(P_n)/n
=\mathbb E_P[(X_0-q)^2]\le c_\star.
\end{aligned}
\tag{1.5}
$$

每个有限坐标纤维的风险等于其原边调和项，强制零单点风险为零，每坐标风险至多 $1/4$；出处为 [非达到卷][N] 引理 2.1。已知达到律的插入支撑论证归于 [平稳卷][S] §4；其实际遍历分量的后验转移归于 [遍历卷][E] 定理 2.1。有限可见阶的严格非达到及其逼近完备性分别归于 [非达到卷][N] 定理 1.5、[完备卷][C] 定理 1.4。这些均作为原范围内的供应结果使用。

**引理 1.4（所用条件极限；[Gray][Gray] §5.9，引理 5.9.3–5.9.4）。** $q_r\to q$ 在 $L^2(P)$ 中成立。因此对 $[0,1]$ 上的任意 Lipschitz 函数 $f$，有 $\mathbb E_P|f(q_r)-f(q)|\to0$。

证明。条件期望是 $L^2$ 正交投影。对 $t\ge r$，塔性质及正交性给出

$$
\|q_t-q_r\|_2^2=\|q_t\|_2^2-\|q_r\|_2^2.
$$

右侧范数平方单调且至多一，故 $q_r$ 为 Cauchy 列。其极限 $q'$ 属于 $L^2(\mathcal E_0)$。对 $A\in\bigcup_r\mathcal F_r$，条件恒等式在极限给出 $\int_A q'\,dP=\int_A X_0\,dP$。这些事件组成一个生成 $\mathcal E_0$ 的代数；有限有符号测度的唯一性把恒等式扩到整个 $\mathcal E_0$，故 $q'=q$。Lipschitz 界和 Cauchy–Schwarz 给出最后一项。这里 $X_0$ 有界，全部投影属于同一个概率空间。$\square$

## 2. 从供应恒等式到普适后验缺陷

**引理 2.1（有限恒等式的后验写法；[唯一最优卷][O] 式（3.11））。** 固定 $n$。在坐标 $i$ 的合法双点纤维 $\{b,b+e_i\}$ 上置

$$
a_{n,i}=\frac{\pi^{(n)}_{b+e_i}}{\pi^{(n)}_b+\pi^{(n)}_{b+e_i}},\qquad
p_{\mu,n,i}=\frac{\mu_{b+e_i}}{\mu_b+\mu_{b+e_i}}\quad(\mu_b+\mu_{b+e_i}>0).
$$

在强制零单点上两者均取零；零总质量双点上的 $p_{\mu,n,i}$ 任取。在全 $\mathcal P(B_n)$ 上有

$$
\kappa_n-\Phi_n(\mu)=\sum_{i=1}^n\mathbb E_\mu[(p_{\mu,n,i}-a_{n,i})^2].
\tag{2.1}
$$

在双点纤维上 $a_{n,i}\in I$，包括开放端点与 $n=1$。

证明。供应式（3.11）中一条正总质量边的项恰为

$$
\frac{(\mu_b\pi^{(n)}_{b+e_i}-\mu_{b+e_i}\pi^{(n)}_b)^2}
{(\mu_b+\mu_{b+e_i})(\pi^{(n)}_b+\pi^{(n)}_{b+e_i})^2}
=(\mu_b+\mu_{b+e_i})(p_{\mu,n,i}-a_{n,i})^2.
$$

每条原边恰属一个坐标纤维，强制单点与零零纤维均贡献零，遂得（2.1）。由（1.4），插入比在 $[1/3,1]$，其后验在 $I$。供应卷在端点及 $n=1$ 的更强界也蕴含此界。$\square$

**定理 2.2（普适平稳后验缺陷界；由引理 2.1 与 [平稳卷][S] 式（2.5））。** 对每个平稳合法律 $P$，包括具有零柱概率的律，

$$
c_\star-d(P)\ge\Delta(P):=\mathbb E_P[\mathbf1_{F_0}\operatorname{dist}(q,I)^2].
\tag{2.2}
$$

对每个 $r\ge1$，同一左侧还支配

$$
\Delta_r(P):=\mathbb E_P[\mathbf1_{F_0}\operatorname{dist}(q_r,I)^2],\qquad
\Delta_r(P)\longrightarrow\Delta(P).
\tag{2.3}
$$

证明。取 $n\ge2r+1$，将引理 2.1 用于实际边缘 $\mu=P_n$。设

$$
\mathcal G_{n,i}=\sigma(X_j:1\le j\le n,\ j\ne i),\quad
p_{n,i}=\mathbb E_P[X_i\mid\mathcal G_{n,i}].
$$

当 $r+1\le i\le n-r$ 时，半径 $r$ 的去中心邻域字段 $\mathcal H_{r,i}$ 包含于 $\mathcal G_{n,i}$，且 $F_i\in\mathcal H_{r,i}$。塔性质给出

$$
q_{r,i}:=\mathbb E_P[X_i\mid\mathcal H_{r,i}]
=\mathbb E_P[p_{n,i}\mid\mathcal H_{r,i}].
$$

函数 $z\mapsto\operatorname{dist}(z,I)^2$ 凸。在 $F_i$ 的每个实际纤维上，供应后验 $a_{n,i}$ 属于 $I$。条件 Jensen 不等式因而给出

$$
\begin{aligned}
\mathbb E_P[\mathbf1_{F_i}\operatorname{dist}(q_{r,i},I)^2]
&\le\mathbb E_P[\mathbf1_{F_i}\operatorname{dist}(p_{n,i},I)^2]\\
&\le\mathbb E_P[(p_{n,i}-a_{n,i})^2].
\end{aligned}
\tag{2.4}
$$

平稳性使左侧等于 $\Delta_r(P)$。对这 $n-2r$ 个内部坐标相加，由（2.1）其余项非负，得到

$$
(n-2r)\Delta_r(P)\le\kappa_n-\Phi_n(P_n).
\tag{2.5}
$$

这里未删除端点贡献，只在下界中不计它们。先固定 $r$，除以 $n$ 后用（1.3）、（1.5）令 $n\to\infty$，得到（2.3）的界。$F_0\in\mathcal F_r$，而平方距离函数在 $[0,1]$ 上 Lipschitz；引理 1.4 给出（2.3）的极限，再令 $r\to\infty$ 得（2.2）。全程只在实际有限边缘上使用供应恒等式，不对无限体积最优律求导。$\square$

**推论 2.3（有限外部柱集的定量证书；由定理 2.2）。** 若 $C$ 仅依赖有限个 $j\ne0$ 的坐标，且 $C\subseteq F_0$，令

$$
s=P(C,X_0=0),\qquad t=P(C,X_0=1),\qquad z_+=\max\{z,0\}.
$$

若 $s+t>0$，则

$$
\begin{aligned}
c_\star-d(P)&\ge(s+t)\operatorname{dist}\left(\frac{t}{s+t},I\right)^2\\
&=\frac{(s-3t)_+^2}{16(s+t)}+\frac{(t-s)_+^2}{4(s+t)}.
\end{aligned}
\tag{2.6}
$$

当 $s=t=0$ 时右侧定义为零。任一 $s>3t$ 或 $t>s$ 的有限柱集因此给出严格非达到证书。

证明。由条件期望的定义，$t=\int_C q\,dP$，$P(C)=s+t$。对概率律 $P(\cdot\mid C)$ 用 Jensen，定理 2.2 的右侧至少为（2.6）的第一项。若 $t/(s+t)<1/4$，平方距离为 $(s-3t)^2/[16(s+t)^2]$；若大于 $1/2$，为 $(t-s)^2/[4(s+t)^2]$；其余为零。这两个违反方向不可能同时出现。零总质量时积分为零，无需定义条件律。$\square$

**推论 2.4（有限证书与无限后验；由定理 2.2）。** $q\in I$ 在 $F_0$ 上几乎处处成立，当且仅当每个有限外部事件 $C\subseteq F_0$ 都有 $s/3\le t\le s$。若 $\Delta(P)>0$，则某个有限半径外部柱集给出（2.6）的正值。

证明。前向由 $q\in I$ 积分得到。反向只需完整半径 $r$ 外部原子：正质量原子上的 $q_r=t/(s+t)\in I$，零质量原子不影响积分。所以 $\Delta_r(P)=0$ 对所有 $r$ 成立，由（2.3）得 $\Delta(P)=0$。若 $\Delta(P)>0$，某个 $r$ 有 $\Delta_r(P)>0$；它是有限个自由原子加权平方距离之和，其中至少一项为正。$\square$

## 3. 每个精确达到者的完整支撑

**定理 3.1（全达到者后验与支撑；由定理 2.2 及 [平稳卷][S] §4 的插入论证）。** 若平稳 $P$ 满足 $d(P)=c_\star$，则对每个 $i\in\mathbb Z$，其实际外部后验 $q_i$ 满足

$$
q_i=0\ \text{于 }F_i^c,\qquad \tfrac14\le q_i\le\tfrac12\ \text{于 }F_i,
\quad P\text{-几乎处处}.
\tag{3.1}
$$

对 $A\in\mathcal E_i$ 有 $P(A,X_i=0)\ge P(A)/2$；若 $A\subseteq F_i$，则

$$
\tfrac13P(A,X_i=0)\le P(A,X_i=1)\le P(A,X_i=0).
\tag{3.2}
$$

对每个 $a\in\mathbb Z$、$m,n\ge1$、$w\in B_n$，

$$
P([0^m]_a)\ge2^{-m},\qquad
P([w]_a)\ge2^{-(n+2)}3^{-k(w)}>0,
\tag{3.3}
$$

且

$$
n c_\star\le\Phi_n(P_n)\le\kappa_n\le(n+1)c_\star.
\tag{3.4}
$$

证明。定理 2.2 使 $\Delta(P)=0$，即中心后验在自由事件上属于 $I$；强制事件上合法性使它为零。平稳性将这项结论转移到所有坐标，可同时取一个对可数坐标成立的满测集。积分恒等式

$$
P(A,X_i=1)=\int_A q_i\,dP,\qquad P(A,X_i=0)=\int_A(1-q_i)\,dP
$$

与 $1-q_i\ge1/2$、自由部分的 $(1-q_i)/3\le q_i\le1-q_i$ 给出（3.2）及其零事件情形。

现在对 $m$ 个位置依次施加 $P(A,X_i=0)\ge P(A)/2$；已经指定的其他位置形成下一位置的外部事件，故得到全零界。从 $[0^{n+2}]_{a-1}$ 起，在中间 $n$ 位逐个插入 $w$ 中的 $1$。插入位置彼此不相邻，每一步的其余指定位置属于 $\mathcal E_i$ 且强制两邻为零；两端也有补零保护。沿（3.2）相乘，

$$
P([w]_a)\ge P([0w0]_{a-1})\ge3^{-k(w)}P([0^{n+2}]_{a-1}),
$$

得到（3.3）。这正是供应卷的插入机制；新增前提是（3.1）已对任意达到者成立。没有从某个混合律的支撑推断其分量支撑。

对有限区间中每个 $i$，$\mathcal G_{n,i}\subseteq\mathcal E_i$，正交分解给出

$$
\mathbb E_P[(X_i-\mathbb E_P[X_i\mid\mathcal G_{n,i}])^2]
=d(P)+\mathbb E_P[(q_i-\mathbb E_P[X_i\mid\mathcal G_{n,i}])^2]\ge c_\star.
$$

左侧是原坐标纤维风险；相加并用（1.3）得（3.4），包括 $n=1$ 与全部开放端点。$\square$

**推论 3.2（任意合法有限指定与接续；由定理 3.1）。** 每个精确达到者在任何有合法完成的有限坐标柱集上都为正；每个合法有限接续 $wv$ 的条件概率 $P([wv])/P([w])$ 为正。若 $w$ 的末位为 $1$，下一位只能为零且条件概率为一。

证明。在有限指定位置的最小覆盖区间内把未指定位置填零，得到合法区间词；其柱集由（3.3）为正且包含于指定事件。接续的分子、分母均为正。末位为一时 $[w1]$ 为空而 $[w0]=[w]$。任意切口都使用这些同一律的实际柱概率，没有接缝独立假设。$\square$

## 4. 任意有限非负随机表示与一个相容联合律

**定义 4.1（固定边发射隐藏维数）。** 对整数 $N\ge1$，记 $\mathbf1$ 为 $N$ 维全一列向量。$\Theta_N$ 包含全部实参数 $\theta=(\lambda,M_0,M_1)$，满足

$$
\lambda\ge0,\quad\lambda\mathbf1=1,\quad M_0,M_1\ge0,\quad
A:=M_0+M_1,\quad A\mathbf1=\mathbf1,\quad\lambda A=\lambda,\quad
\lambda M_1M_1\mathbf1=0.
\tag{4.1}
$$

$\lambda$ 为行向量。结构零、零质量状态、可约性、周期性及任意精确实数条目都允许。$M_w=M_{w_1}\cdots M_{w_n}$，空词矩阵为单位阵。此定义是有限随机过程表示的非负矩阵约定；其实际律由下述构造确定，而非由独立指定的条件表确定。

**命题 4.2（相容联合律及表示对应；[完备卷][C] 引理 4.2 的概率扩张机制）。** 每个 $\theta\in\Theta_N$ 定义一个归一化两侧平稳联合律 $J_\theta$，其隐藏状态 $H_i\in\{1,\ldots,N\}$ 与可见位 $X_i\in\{0,1\}$ 的区间概率为

$$
J_\theta(H_a=h_a,\ldots,H_{b+1}=h_{b+1},X_a=x_a,\ldots,X_b=x_b)
=\lambda_{h_a}\prod_{i=a}^b M_{x_i}(h_i,h_{i+1}).
\tag{4.2}
$$

其可见边缘 $P_\theta$ 支持于 $X$，且对所有有限词

$$
P_\theta([w]_a)=\lambda M_w\mathbf1.
\tag{4.3}
$$

通常的有限状态发射 HMM 属于此类；即使其原隐藏初始分布不平稳，只要可见律平稳，也能在同一隐藏维数选取平稳初始分布而保持全部可见柱概率。反之此类有一个有限状态、确定性发射表示。这一对应保持可见律，但不宣称两种约定的最小固定维数相同。

证明。把（4.2）的最后一对位、状态相加用 $A\mathbf1=\mathbf1$，把第一对相加用 $\lambda A=\lambda$，得到右、左相容性；总和为 $\lambda A^{b-a+1}\mathbf1=1$。任意有限坐标的分布由这些区间边缘化，相容性使选择覆盖区间无关。有限字母乘积空间的柱代数紧：递减柱代数事件若交为空，则某项为空。故相容有限概率在此代数上连续于空集，概率扩张给出唯一联合律。平移不改变（4.2），所以联合律平稳。逐状态求和即（4.3）。

由（4.1），每个位置的 $11$ 概率为零；可数并使任何相邻 $11$ 出现的概率为零。反向，一个由前三组归一化、平稳条件产生的律若合法，其 $11$ 柱概率必为零，故（4.1）的最后条件也必要。这里全零词与首尾为一的合法词始终由（4.3）定义，任意接缝 $uv$ 使用 $\lambda M_uM_v\mathbf1$，不拆成两个边缘的乘积。

若状态 $s$ 先以概率 $e_s(x)$ 发射，再按随机矩阵 $A$ 转移，令 $D_x=\operatorname{diag}(e_s(x))$、$M_x=D_xA$。若原初始分布 $\alpha$ 只保证可见律 $P$ 平稳，则对每个词 $w$ 与 $k\ge0$，$\alpha A^kM_w\mathbf1=P([w])$。置

$$
\lambda_K=\frac1K\sum_{k=0}^{K-1}\alpha A^k,\qquad
\lambda_KA-\lambda_K=\frac{\alpha A^K-\alpha}{K}.
$$

概率单纯形紧，故某个子列收敛到概率行向量 $\lambda$；上式给出 $\lambda A=\lambda$，而每个固定词的线性连续性给出 $\lambda M_w\mathbf1=P([w])$。因此全部柱概率同时保留；合法性使 $\lambda M_1M_1\mathbf1=P([11])=0$，得到（4.1）和（4.2）的平稳联合表示。此平均只作用于有限隐藏分布，不要求链混合或非周期。原隐藏分布已平稳时可直接取它为 $\lambda$。

反向，以所有 $M_x(s,t)>0$ 的三元组 $(s,x,t)$ 为新状态，发射 $x$，转移为

$$
K((s,x,t),(t,y,u))=M_y(t,u),\qquad
\rho(s,x,t)=\lambda_sM_x(s,t),
\tag{4.4}
$$

其余转移为零。每行总和为一，$\rho$ 总和为一，且输入到 $(s,x,t)$ 的质量为 $(\lambda A)_sM_x(s,t)=\rho(s,x,t)$。有限维数至多 $2N^2$；相邻三元组的前一第三坐标等于后一第一坐标。其可见词概率逐状态求和仍为（4.3）。这覆盖全部有限维的存在问题，同时保留可约、周期与零条目。$\square$

**推论 4.3（隐藏表示的有限柱证书；由推论 2.3）。** 对非空合法词 $u,v$，若 $u$ 末位及 $v$ 首位为零，取外部事件 $C=\{X_{-|u|}\cdots X_{-1}=u,\ X_1\cdots X_{|v|}=v\}$。则

$$
s=\lambda M_uM_0M_v\mathbf1,\qquad t=\lambda M_uM_1M_v\mathbf1
\tag{4.5}
$$

代入（2.6）给出该实际律的定量缺口。精确达到要求全部此类词对满足

$$
\lambda M_u(M_0-M_1)M_v\mathbf1\ge0,\qquad
\lambda M_u(3M_1-M_0)M_v\mathbf1\ge0.
\tag{4.6}
$$

证明。（4.3）给出（4.5），而 $C\subseteq F_0$，故推论 2.3 适用。达到时两违反方向都不允许。全部半径 $r$ 外部原子包含于这些词对中，故（4.6）对所有词对成立也等价于后验区间条件，依据推论 2.4；它尚不等价于达到。$\square$

## 5. 实际分量约化与周期性

**定理 5.1（有限隐藏链的实际遍历分量；后验转移机制见 [遍历卷][E] §2.2）。** 每个 $\theta\in\Theta_N$ 的可见律是其同一个联合律中有限个实际平稳遍历可见律的混合。合并相同的可见律后，写成

$$
P_\theta=\sum_{\ell=1}^L w_\ell R_\ell,\qquad w_\ell>0,\quad\sum_\ell w_\ell=1,
\tag{5.1}
$$

其中不同的 $R_\ell$ 是实际可见遍历分量，其标签由可见无限过去确定。对该混合的外部后验 $q$，它在每个 $R_\ell$ 下也是外部后验，且

$$
d(P_\theta)=\sum_{\ell=1}^L w_\ell d(R_\ell).
\tag{5.2}
$$

若 $d(P_\theta)=c_\star$，则每个正权重隐藏闭不可约类的可见律都达到 $c_\star$ 并满足定理 3.1。因此一个有限隐藏达到者必给出一个闭不可约有限隐藏达到者；不需要非周期或正转移假设。

证明。先考察有限隐藏链 $A$。其正转移图的每个状态都能到达某个闭不可约类。对不在这些类中的状态集 $V$，从每个状态选一条进入闭类的正概率路径。有限性给出一个步数 $k$ 和 $\eta>0$，使从任意 $V$ 状态在 $k$ 步内离开 $V$ 的概率至少为 $\eta$；离开后不能回来。平稳性于是给出 $\lambda(V)\le(1-\eta)\lambda(V)$，故 $\lambda(V)=0$。

设闭类为 $C_j$，正权重 $\alpha_j=\lambda(C_j)$。限制矩阵 $M_x^j$ 没有流出，因为 $A$ 的流出为零且 $M_x\ge0$。令 $\lambda^j=\lambda|_{C_j}/\alpha_j$，它平稳且在不可约类的每个状态都为正：一处正质量沿正概率路径传播。全局合法条件是

$$
0=\lambda M_1M_1\mathbf1
=\sum_j\alpha_j\lambda^jM_1^jM_1^j\mathbf1.
$$

各项非负，所以每个正权重类的限制参数仍满足定义 4.1。联合律先选类 $j$、再按其限制参数运行；类标签在整个两侧轨道不变。这给出实际混合，不是从分别实现的边缘量拼接。

每个不可约类对应的三元组链（4.4）也不可约：从 $(s,x,t)$ 到 $(u,y,v)$，先沿 $A$ 的正路径由 $t$ 到 $u$，在每条边选一个正质量发射，再走指定的 $y$ 边。有限不可约平稳链在一步平移下遍历，即使有周期。为明确这一点，设该链为 $Z$，$B$ 是平移不变事件。用有限柱函数在 $L^2$ 逼近 $\mathbf1_B$，并把逼近函数平移到非负坐标；平稳性与 $B$ 的不变性保持逼近误差。因此 $B$ 有未来可测版本。令 $g(z)=\mathbb P(B\mid Z_0=z)$，由未来 Markov 性与不变性得 $g=Kg$。在有限不可约图上，调和函数的最大值沿每条正边传播到全图，故 $g$ 为常数 $p$。对每个 $n\ge0$，不变性及 Markov 性又给出

$$
\mathbb E[\mathbf1_B\mid\sigma(Z_j:j\le n)]=g(Z_n)=p.
$$

这些字段递增生成整个两侧轨道字段；引理 1.4 的投影论证同样适用于 $\mathbf1_B$，故 $\mathbf1_B=p$ 几乎处处，$p\in\{0,1\}$。可见律是该链的平移因子，因此也遍历。此论证未使用 $K^n$ 的逐项收敛。

合并相同可见律得到（5.1）。对每个有限词 $w$，考虑只依赖负坐标的过去频率

$$
f_w(x)=\lim_{n\to\infty}\frac1n\sum_{k=|w|}^{n}\mathbf1_{[w]_0}(T^{-k}x).
\tag{5.3}
$$

[Gray][Gray] 定理 7.2.1 应用于平稳系统 $T^{-1}$ 及有界柱指标，给出在 $R_\ell$ 下 $f_w=R_\ell([w]_0)$ 几乎处处。有限字母的柱集可数；对全部词同时取满测集。不同可见律在某个有限柱集上不同，故由（5.3）的整组值确定的事件 $E_\ell$ 两两不交、属于 $\mathcal E_0$，且 $R_\ell(E_\ell)=1$。标签因而确由实际可见过去确定，联合律中的合并标签与它几乎处处一致。

对任意 $A\in\mathcal E_0$，混合律的条件恒等式在 $A\cap E_\ell$ 给出

$$
0=\int_{A\cap E_\ell}(X_0-q)\,dP_\theta
=w_\ell\int_A(X_0-q)\,dR_\ell.
\tag{5.4}
$$

所以 $q$ 是每个分量的外部后验。将（1.5）的无限外部风险按实际混合积分即得（5.2）。每个分量密度不超过 $c_\star$；若平均达到，则每个正权重项都达到。合并前的隐藏类具有相同结论，再用定理 3.1 导出各类的完整可见支撑。有限窗口风险一般只满足凹性，未在此宣称 $D_r$ 对混合仿射。$\square$

## 6. 固定隐藏维数的精确紧分离等价

**定义 6.1（整个参数域上的极值）。** 在定义 4.1 的整个 $\Theta_N$ 上置

$$
U_{N,r}=\max_{\theta\in\Theta_N}D_r(P_\theta),\qquad
C_N=\sup_{\theta\in\Theta_N}d(P_\theta),\qquad r\ge1.
\tag{6.1}
$$

这里不先加可见全支撑条件；零质量参数也参与。

**定理 6.2（固定维数的有限分离等价；由定理 3.1 与（1.3）、（1.5））。** 对每个固定 $N\ge1$，$C_N$ 取到且

$$
C_N=\inf_{r\ge1}U_{N,r}\le c_\star.
\tag{6.2}
$$

以下三项等价：没有至多 $N$ 个边发射隐藏状态的全支撑精确达到律；$C_N<c_\star$；存在有限整数 $r,m\ge1$ 使

$$
U_{N,r}<\frac{\kappa_m}{m+1}.
\tag{6.3}
$$

若（6.3）成立，则对整个参数域都有

$$
c_\star-d(P_\theta)\ge\frac{\kappa_m}{m+1}-U_{N,r}>0.
\tag{6.4}
$$

证明。$\Theta_N$ 非空：取 $M_0$ 为单位阵、$M_1=0$ 及任意概率行向量。所有条目在 $[0,1]$，而（4.1）是闭的多项式等式与不等式，所以 $\Theta_N$ 紧。由（4.3），每个有限柱概率是参数的多项式；由（1.5）及 $h$ 在 $(0,0)$ 的连续性，$D_r(P_\theta)$ 在整个紧域连续。故 $U_{N,r}$ 取到，且随 $r$ 递减。

设 $U=\lim_rU_{N,r}$，选最大参数 $\theta_r$，再取收敛子列 $\theta_{r_j}\to\theta_*$，其中 $r_j\to\infty$。对任意固定 $k$，当 $r_j\ge k$，

$$
D_k(P_{\theta_{r_j}})\ge D_{r_j}(P_{\theta_{r_j}})=U_{N,r_j}.
$$

连续性给出 $D_k(P_{\theta_*})\ge U$；对 $k$ 取下确界得 $d(P_{\theta_*})\ge U$。反向，对任意 $\theta$ 和 $k$，$d(P_\theta)\le D_k(P_\theta)\le U_{N,k}$，所以 $d(P_\theta)\le U$。这证明最大值存在及（6.2），没有假设 $d$ 连续或交换无控制的两重极值。

若 $C_N=c_\star$，最大参数的可见律由定理 3.1 自动全支撑。因此全支撑达到者不存在，当且仅当 $C_N<c_\star$。零质量隐藏状态允许补足维数：在新状态上添加独立的确定性零自环，赋初始质量零，保留旧矩阵和旧律；故“至多 $N$”与 $\Theta_N$ 的存在量词相同。

若 $C_N<c_\star$，由 $U_{N,r}\downarrow C_N$，可先选 $r$ 使 $U_{N,r}<c_\star$，再由 $\kappa_m/(m+1)\to c_\star$ 选 $m$ 使（6.3）成立。若（6.3）成立，由（1.3）、（6.2）有 $C_N\le U_{N,r}<\kappa_m/(m+1)\le c_\star$，且同一串不等式给出（6.4）。$\square$

## 7. 后验必要条件的不足与原问题

**命题 7.1（必要区间并不充分；[完备卷][C] 命题 6.2 的单链及 [增长卷][G] 定理 7.3）。** 令 $R^a$ 为两状态平稳链，状态就是可见位，其转移及平稳分布为

$$
A^a=\begin{pmatrix}1-a&a\\1&0\end{pmatrix},\qquad
\lambda^a=\left(\frac1{1+a},\frac a{1+a}\right),\qquad 0<a<1.
\tag{7.1}
$$

取 $a=1/3$，该律合法、全支撑、不可约、非周期，并满足自由外部后验 $q=3/7\in I$，因而满足全部（4.6）；但

$$
d(R^{1/3})=\frac17<\frac{1800}{12559}\le c_\star.
\tag{7.2}
$$

证明。行和为一且直接相乘得 $\lambda^aA^a=\lambda^a$。合法转移都为正，故每个合法词概率为正；零自环使不可约链非周期。取 $M_x=D_xA^a$，$D_0=\operatorname{diag}(1,0)$、$D_1=\operatorname{diag}(0,1)$，得到定义 4.1 的精确表示。

自由中心两种取值的转移乘积分别为 $(1-a)^2$ 与 $a$，所以任何包含两邻的外部窗口都有后验

$$
q=\frac{a}{(1-a)^2+a}\quad\text{于 }F_0,
\tag{7.3}
$$

强制部分为零。共同的其余转移及初始因子相消；窗口扩张由引理 1.4 给出同一无限外部后验，这是 [非达到卷][N] 命题 2.2 的一阶实例。实际三位柱概率为

$$
R^a([000])=\frac{(1-a)^2}{1+a},\qquad R^a([010])=\frac a{1+a}.
$$

由（1.5）或该共同后验，

$$
d(R^a)=\frac{a(1-a)^2}{(1+a)((1-a)^2+a)}.
\tag{7.4}
$$

代入 $a=1/3$ 得 $q=3/7$、$d=1/7$。供应增长下界的有理部分给出 $c_\star\ge1800/12559$，其证明不需要小数或数值程序；严格比较等价于 $12559<12600$。（4.6）由推论 2.4 积分推出。因此全支撑、有限非负实现及后验区间同时成立仍不能推出达到。这个见证复用供应单链与密度机制，不作为新的有限隐藏构造。$\square$

**命题 7.2（区间条件也不强制有限可见阶；复用 [完备卷][C] 命题 6.2 的混合机制）。** 实际混合 $M=(R^{1/3}+R^{1/4})/2$ 有四隐藏状态、完整可见支撑，外部后验在自由部分属于 $I$，却没有任何有限可见 Markov 阶，且 $d(M)<c_\star$。

证明。隐藏状态记录一次选择的参数及当前位；两闭类的矩阵（7.1）按块直和，初始分布各乘 $1/2$，故是一份实际平稳联合律。每个合法柱概率是两个正概率的平均。其两个自由后验分别为 $3/7$ 与 $4/13$，均属于 $I$；定理 5.1 的实际外部标签及后验转移表明 $M$ 的后验正取这些值。

令 $a=1/3$、$b=1/4$，$q\ge1$。实际全零历史的下一位概率为

$$
M(X_0=1\mid X_{-q}\cdots X_{-1}=0^q)
=\frac{aA_q+bB_q}{A_q+B_q},\quad
A_q=\frac{(1-a)^{q-1}}{1+a},\quad B_q=\frac{(1-b)^{q-1}}{1+b}.
\tag{7.5}
$$

比值 $B_q/A_q=(16/15)(9/8)^{q-1}$ 严格递增，且 $a\ne b$，故（7.5）严格变化。若存在有限阶 $m$，塔性质会使全部 $q\ge m$ 的值均等于同一行 $k(1\mid0^m)$，矛盾。这是供应四状态反例的同一机制，只选择了两个满足区间的参数。由（7.4）和定理 5.1，

$$
d(M)=\tfrac12\left(\tfrac17+\tfrac9{65}\right)=\frac{64}{455}<\frac17<c_\star.
$$

所以区间条件不能把有限隐藏类约化成有限可见阶；已知可见阶非达到定理也不能据此推广。$\square$

**推论 7.3（随隐藏维数的已有逼近；[完备卷][C] 定理 1.4）。** $C_N$ 随 $N$ 单调不减，且 $\sup_N C_N=c_\star$。

证明。补零质量状态的构造给出单调性。任意有限可见阶的平稳律可用其合法可见后缀作为有限隐藏状态，转移附带下一可见位；这是定义 4.1 的一个有限边发射表示。供应完备性给出密度任意接近 $c_\star$ 的这类全支撑律，所以 $\sup_N C_N\ge c_\star$；反向为（6.2）。$\square$

**开放问题 7.4（任意有限隐藏维数的精确达到）。** 是否存在某个有限 $N$ 与 $\theta\in\Theta_N$ 使 $d(P_\theta)=c_\star$，或是否对每个有限 $N$ 都有 $C_N<c_\star$？定理 6.2 将后一项等价地写成

$$
\forall N\ge1\ \exists r,m\ge1:\quad U_{N,r}<\kappa_m/(m+1).
\tag{7.6}
$$

本卷没有给出对每个 $N$ 的分离对，也没有给出一个有限隐藏精确达到者。（4.6）只是必要条件，命题 7.1–7.2 已表明其不足。紧性给出固定维数的极值及有限分离等价，不决定（7.6）。推论 7.3 给出的跨维数逼近也不决定有限维数达到；即使每个 $C_N<c_\star$，仍可有 $C_N\uparrow c_\star$。这些量词保持原完整 no11 域与原调和目标。

[G]: FIB_LEGAL_EDGE_LOAD_GROWTH_CONSTANT.md
[O]: FIB_LEGAL_EDGE_LOAD_POSITIVE_UNIQUE_OPTIMIZER.md
[S]: FIB_LEGAL_EDGE_LOAD_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[E]: FIB_LEGAL_EDGE_LOAD_ERGODIC_FULL_SUPPORT_STATIONARY_ATTAINMENT.md
[N]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_NONATTAINMENT.md
[C]: FIB_LEGAL_EDGE_LOAD_FINITE_VISIBLE_MEMORY_COMPLETENESS.md
[Gray]: https://www-ee.stanford.edu/~gray/arp.pdf "Robert M. Gray, Probability, Random Processes, and Ergodic Properties，作者版 January 2, 2010；§5.9、定理 7.2.1"

## 追加锚（本行以下为增补区）
