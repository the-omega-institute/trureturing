# AURIC FIB ATOM：静态 seam、转移环流与 Fibonacci 切换环

## 1. 五态概率纤维与读出前提

**定义 1.1（支持、输出与观察）。** 令

$$
\Sigma=\{0,1,2,3,13\}
=\{\varnothing,\{1\},\{2\},\{3\},\{1,3\}\}.
$$

固定状态顺序为 $(0,1,2,3,13)$，用 $\mathbf e_s$ 表示状态空间 $H=\mathbb R^\Sigma$ 的单位向量。输出标签函数为

$$
F(0)=\mathrm{null},\quad F(1)=[2],\quad F(2)=[3],\quad
F(3)=[5],\quad F(13)=[2,5].
$$

支持状态、输出列表、状态概率和数值读出分别属于不同的载体。特别地，列表 $[2,5]$ 不等于数值 $7$。令 $\mathcal D=\{p\in H:p_s\ge0,\ \sum_sp_s=1\}$，并定义

$$
\begin{aligned}
T&=\{v\in H:\textstyle\sum_sv_s=0\},\\
A(v)&=(v_1+v_{13},v_2,v_3+v_{13}),\\
(X,Z,Y)&=A(p),\qquad \kappa=p_{13},\qquad
\mathbf d=(1,-1,0,-1,1).
\end{aligned}
$$

**数学引文 1.2（内禀 seam 与所选截面）。** 使用[《局部源分裂与读出几何》数学引文 2.1–2.2、约定 2.3、定理 3.3–3.4 及 4.2–4.3](AURIC_FIB_ATOM_LOCAL_SOURCE_SPLITTING_AND_READOUT_GEOMETRY.md)的以下前提。固定 $b=(X,Z,Y)$ 的概率纤维非空当且仅当

$$
Z\ge0,\qquad 0\le X,Y\le1-Z.
$$

此时令 $l_b=\max(0,X+Z+Y-1)$、$u_b=\min(X,Y)$，则

$$
\mathcal F_b=\{p_\kappa:l_b\le\kappa\le u_b\},\qquad
p_\kappa=(1-X-Z-Y+\kappa,X-\kappa,Z,Y-\kappa,\kappa).
$$

有 $p_\kappa-p_{\kappa'}=(\kappa-\kappa')\mathbf d$ 及 $\ker(A|_T)=\mathbb R\mathbf d$；整个 $H$ 上的核则为 $\operatorname{span}\{\mathbf e_0,\mathbf d\}$。取明确截面

$$
L(\dot X,\dot Z,\dot Y)=(-\dot X-\dot Z-\dot Y,\dot X,\dot Z,\dot Y,0),
$$

便有 $AL=I$ 及 $v=L(Av)+v_{13}\mathbf d$。若 $L'=L+\mathbf d\ell_0$，其中 $\ell_0$ 为线性泛函，则相对于 $L'$ 的隐藏系数为 $v_{13}-\ell_0(Av)$。这不改变实际联合坐标导数 $\dot p_{13}$。内禀对象是核以及商映射；上述直和系数相对于截面定义。

在 $p$ 的零坐标上，单侧可行导数须非负，双侧可微路径的导数须为零。在线段相对内点，$a\mathbf d$ 的两个符号均可行；在端点须保持参数位于 $[l_b,u_b]$。单点纤维没有非零纤维内导数。代数截面的分量不自动满足这些概率条件。

**数学引文 1.3（独立补全、联合质量与中心化量）。** 采用[《边界、运输纤维与回路闭合》Q3、定理 3.1](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md)及[《环流读出、控制接口、KL 作用量与 toric 关系》Q4、Q12](AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS.md)的条件独立补全。设合法边界满足 $r=1-Z>0$，令 $U=\mathbf1_{\{1,13\}}$、$V=\mathbf1_{\{3,13\}}$。给定 $s\ne2$ 的两占据指标独立，当且仅当

$$
\kappa=\kappa_{\mathrm{ind}}=\frac{XY}{r}.
$$

此点在可行区间内。具体地，$XY/r\le\min(X,Y)$，且

$$
\frac{XY}{r}-(X+Y-r)=\frac{(r-X)(r-Y)}r\ge0.
$$

令 $\delta\kappa=\kappa-XY/r$，则所引四格关系在此记号下为

$$
\begin{aligned}
\det\begin{pmatrix}p_0&p_3\\p_1&p_{13}\end{pmatrix}
 &=r\kappa-XY=r\,\delta\kappa,\\
\operatorname{Cov}_p(U,V\mid s\ne2)
 &=\frac\kappa r-\frac{XY}{r^2}=\frac{\delta\kappa}{r},\\
\operatorname{Cov}_p(U,V)&=\kappa-XY.
\end{aligned}
$$

$\kappa$ 是联合质量，$\delta\kappa$ 是相对于独立补全的偏移，协方差由上述归一化决定。若 $r=0$，合法边界强制 $X=Y=0$，唯一分布为 $\mathbf e_2$，不在零概率事件 $s\ne2$ 上定义条件独立。

**数学引文 1.4（数值矩与四角响应）。** 令 $W=2U+3\mathbf1_{\{2\}}+5V$，其五态值为 $(0,2,3,5,7)$。这是输出列表的加性数值编码。使用[《边界、运输纤维与回路闭合》Q8、§5.1](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md)及[《局部源分裂与读出几何》§5](AURIC_FIB_ATOM_LOCAL_SOURCE_SPLITTING_AND_READOUT_GEOMETRY.md)的矩公式与四角配对，得

$$
\begin{aligned}
\mathbb E_pW&=2X+3Z+5Y,\\
\mathbb E_pW^2&=4X+9Z+25Y+20\kappa,\\
\kappa&=\frac{\operatorname{Var}_p(W)+(2X+3Z+5Y)^2-4X-9Z-25Y}{20}.
\end{aligned}
$$

恢复式的前提是同一分布的 $X,Z,Y$ 已知且方差为精确值。对 $K:\Sigma\to\mathbb R$，既有配对为 $\Delta_{\mathbf d}K=K(0)-K(1)-K(3)+K(13)$。将其用于状态上的非线性读出 $M_\lambda(s)=\exp(\lambda W(s))$，得到

$$
\Delta_{\mathbf d}M_\lambda
=(e^{2\lambda}-1)(e^{5\lambda}-1)>0\quad(\lambda\in\mathbb R\setminus\{0\}),
\qquad
\Delta_{\mathbf d}M_\lambda=10\lambda^2+O(\lambda^3)\quad(\lambda\to0).
$$

因两因子同号，非零实 $\lambda$ 的精确期望在固定边界纤维上分离不同 $\kappa$；展开式由两个指数在零点的展开相乘得到。$\mathbb E[W^2]$ 和 $\mathbb E[e^{\lambda W}]$ 分别是新的状态读出期望，不能以 $(\mathbb EW)^2$ 或 $e^{\lambda\mathbb EW}$ 替换。只对已知均值作后处理不增加纤维区分能力。这些公式讨论精确律的识别，不给出固定样本量下的精确恢复保证。

## 2. 边、状态与观察的三层映射

**定义 2.1（五边转移图）。** 顶点为 $\Sigma$，有向边依次为

$$
e_1:0\to1,\quad e_2:1\to13,\quad e_3:13\to3,\quad
 e_4:3\to0,\quad e_5:0\to2.
$$

令 $E=\{e_1,\ldots,e_5\}$，有符号链空间为 $\mathbb R^E$。边界约定为终点减起点，矩阵为

$$
B=\begin{pmatrix}
-1&0&0&1&-1\\
1&-1&0&0&0\\
0&0&0&0&1\\
0&0&1&-1&0\\
0&1&-1&0&0
\end{pmatrix},\qquad
A=\begin{pmatrix}
0&1&0&0&1\\
0&0&1&0&0\\
0&0&0&1&1
\end{pmatrix}.
$$

这里每一列的对象是一条状态转移。它不同于[《边界、运输纤维与回路闭合》Q1–Q2、定理 2.1](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md)中把左右边界标签分开、以五种状态为五条边的二部运输图；后者有六个顶点和两个连通分量。

**定理 2.2（五边转移的静态／动态短正合列）。** 令 $\mathbf c=(1,1,1,1,0)\in\mathbb R^E$。在实向量空间上有

$$
\ker B=\mathbb R\mathbf c,\qquad
\ker(AB)=\{(a,b,a,b,0):a,b\in\mathbb R\},
$$

及短正合列

$$
0\longrightarrow\mathbb R\mathbf c
\xrightarrow{\ \iota\ }\ker(AB)
\xrightarrow{\ B\ }\mathbb R\mathbf d\longrightarrow0,
$$

其中 $\iota$ 是包含映射。因此 $\dim\ker(AB)=2$，状态层和边层两个一维核位于不同空间。

证明。用 $f=(a,b,c,d,e)$ 表示边链的坐标，则

$$
Bf=(-a+d-e,a-b,e,c-d,b-c),\qquad
AB=\begin{pmatrix}1&0&-1&0&0\\0&0&0&0&1\\0&1&0&-1&0\end{pmatrix},
\qquad ABf=(a-c,e,b-d).
$$

方程 $Bf=0$ 强制 $e=0$ 及 $a=b=c=d$，反向代入也成立。方程 $ABf=0$ 则恰为 $c=a,d=b,e=0$，而

$$
B(a,b,a,b,0)=(b-a)\mathbf d.
$$

任意 $t\mathbf d$ 有原像 $(0,t,0,t,0)$，故限制映射满射；其核由 $a=b$ 给出，正好为 $\mathbb R\mathbf c$。这证明每一处正合性。该机制是将线性同构定理用于 $B|_{\ker(AB)}$：一般像为 $\ker A\cap\operatorname{im}B$，此处正好等于 $\mathbb R\mathbf d$。所用一般工具见 Axler，[《Linear Algebra Done Right》第四版 §3E，3.105–3.107](https://linear.axler.net/LADR4e.pdf)；这里计算的是指定五边矩阵与指定观察 $A$ 的对应。∎

**定义 2.3（有符号链、概率流与路径计数）。** 有符号链 $f\in\mathbb R^E$ 允许负系数。所列有向边上的概率流要求 $f_e(t)\ge0$，并由概率曲线满足 $\dot p=Bf$。有限跃迁率的进一步要求是

$$
f_{i\to j}(t)=p_i(t)q_{ij}(t),\qquad q_{ij}(t)\ge0\quad(i\ne j),\qquad
q_{ii}(t)=-\sum_{j\ne i}q_{ij}(t).
$$

若 $p_i(t)=0$，有限率必有该顶点所有出流为零；若 $p_i(t)>0$，可由 $q_{ij}=f_{i\to j}/p_i$ 定义率。要定义整个时间区间上的非爆炸过程，还须相应的局部有界性或其他非爆炸条件。

一条有限有向走法 $\gamma=(s_0\to s_1\to\cdots\to s_m)$ 的计数 $N(\gamma)\in\mathbb Z_{\ge0}^E$ 则来自实际可拼接的边序列，并满足

$$
BN(\gamma)=\mathbf e_{s_m}-\mathbf e_{s_0}.
$$

此式由每次跃迁的边界望远镜相消得到。整数性和这个边界式都不能替代可拼接性，例如计数 $\mathbf c$ 虽有零边界，却不能由从出度为零的顶点 $2$ 开始的走法实现。计数也不单独记录完整顺序：从 $0$ 或从 $1$ 出发绕方形一周，都给出 $\mathbf c$，但有不同的有序边记录。定理 2.2 是向量空间的正合列，不是非负概率流或单条走法的正合列。

**定理 2.4（同一 seam 曲线的两个有限率实现）。** 令

$$
\bar p=(1/5,1/5,1/5,1/5,1/5),\quad
p(t)=\bar p+t\mathbf d,\quad 0\le t<1/5,
$$

并取非负边流

$$
f=(0,1,0,1,0),\qquad g=(1,2,1,2,0)=f+\mathbf c.
$$

对每个 $0<T_0<1/5$，这两个流分别由 $[0,T_0]$ 上非爆炸、有限率的 Markov 过程实现；两个过程均以 $\bar p$ 开始，并具有同一时刻律 $p(t)$。它们的期望累计边计数分别为 $tf$ 和 $tg$。因此，即使给定整条概率曲线，边计数律仍不由该曲线唯一决定。

证明。直接代入得 $Bf=Bg=\mathbf d$ 及 $ABf=ABg=0$。$p(t)$ 的五个坐标依次为 $1/5+t,1/5-t,1/5,1/5-t,1/5+t$，质量为一，且在 $[0,T_0]$ 上均至少为 $1/5-T_0>0$。对于 $h=f$ 或 $h=g$，在列出的边上设

$$
q^{(h)}_{ij}(t)=\frac{h_{i\to j}}{p_i(t)},
$$

其余非对角率为零，对角率为出率之负和。这些率连续，每个顶点的出率不超过 $2/(1/5-T_0)$。可取一个不小于此界的常数 $M$，用强度 $M$ 的 Poisson 候选时刻，在时刻 $t$、状态 $i$ 以概率 $q^{(h)}_{ij}(t)/M$ 跃迁到 $j$，余下概率保持原态。这给出有限时间内只有有限次候选的过程，故非爆炸。其时刻律满足有限维前向方程。

所给 $p(t)$ 满足该方程，因为 $p_i(t)q^{(h)}_{ij}(t)=h_{i\to j}$，故 $\dot p=Bh=\mathbf d$。有界连续系数的线性初值问题唯一，因此构造的过程确有该时刻律。对每条边，其期望跃迁计数为

$$
\mathbb E N_{i\to j}(t)
=\int_0^t p_i(s)q^{(h)}_{ij}(s)\,ds=t h_{i\to j}.
$$

这也可从上述 Poisson 候选的接受概率积分得到。$t>0$ 时两组期望计数不同，所以其边记录律不同。每个样本的计数仍为可拼接的非负整数；$f$ 和 $g$ 本身不能充当一条走法的计数，因为其边界 $\mathbf d$ 不是两个单位状态向量之差。所构造率不声明在 $t=1/5$ 有有限延拓。∎

## 3. 正向路径钟与平稳循环

**定义 3.1（指定有向边的累计成本）。** 沿用[《观察者相对局部模型与未来可识别性》§10](AURIC_FIB_ATOM_OBSERVER_RELATIVE_LOCAL_MODELS_AND_FUTURE_IDENTIFIABILITY.md)的非负可加路径钟，将本图每条合法有向边的成本指定为有限实数 $\ell_i\ge0$。有限走法的钟为

$$
\Theta_\ell(\gamma)=\sum_{k=1}^m\ell(s_{k-1}\to s_k),
$$

空走法取零，拼接时相加。对非爆炸跃迁过程 $S_t$，累计钟为

$$
J_t=\sum_{0<s\le t}\ell(S_{s-}\to S_s).
$$

每条样本路径上的 $J_t$ 非减。状态统计 $\langle K,p(t)\rangle$ 则使用[《局部源分裂与读出几何》命题 5.3](AURIC_FIB_ATOM_LOCAL_SOURCE_SPLITTING_AND_READOUT_GEOMETRY.md)的不同合同：其变化积分只给端点差，一般不非减。

**定理 3.2（带正成本的循环与平稳概率律）。** 令

$$
C=(0\to1\to13\to3\to0),\qquad L_C=\ell_1+\ell_2+\ell_3+\ell_4.
$$

对整数 $m\ge1$，$C^m$ 是合法走法，$N(C^m)=m\mathbf c$ 且 $\Theta_\ell(C^m)=mL_C$。此外，对每个 $\gamma>0$，存在初始律为 $\bar p$ 的有限率平稳过程，其概率流为 $\gamma\mathbf c$，并且

$$
p(t)=\bar p,\qquad A(p(t))=(2/5,1/5,2/5),\qquad
\mathbb E J_t=\gamma tL_C.
$$

当且仅当至少一个循环边成本严格为正时，$\mathbb E J_t$ 随 $t$ 严格增长。该实现的叶边 $0\to2$ 速率为零。

证明。有限走法部分由四条可拼接的循环边及拼接可加性给出。对过程部分，指定

$$
q_{01}=q_{1,13}=q_{13,3}=q_{30}=5\gamma,\qquad q_{02}=0,
$$

其余非对角率均为零，对角率为出率之负和。状态 $2$ 保持不动。可用强度 $5\gamma$ 的 Poisson 时刻构造过程：每个时刻让方形上的状态前进一步，状态 $2$ 留在原处。这个五态变换是一个四循环和一个不动点，保持均匀律，故任意时刻的律均为 $\bar p$。Poisson 计数在每个有限区间内有限，过程非爆炸。

每条循环边的概率流为 $(1/5)5\gamma=\gamma$，叶边流为零。给定 Poisson 候选次数为 $m$，初态仍均匀，每一步的平均成本为 $L_C/5$；保持于 $2$ 的候选不算跃迁，成本为零。因此

$$
\mathbb E J_t=\mathbb E N_t\,\frac{L_C}{5}
=5\gamma t\,\frac{L_C}{5}=\gamma tL_C.
$$

由于四个成本均非负，$L_C>0$ 恰当且仅当其中至少一个为正。这是平稳的概率律与持续跳跃的样本之间的区别；非减样本钟可以有等待平台，也可以因初态为 $2$ 而恒为零，结论不声称每条样本严格增长。∎

**命题 3.3（叶边限制与相同状态曲线下的活动差）。** 在定义 2.1 的定向图上，每个非负平稳流都形如 $a\mathbf c$，其中 $a\ge0$，因而叶边流必为零。若平稳律满足 $p_0>0$ 且要求 $q_{02}>0$，则不存在这样的平稳实现。对于定理 2.4 的两个过程，同一成本合同下则有

$$
\mathbb E J_t^{(g)}-\mathbb E J_t^{(f)}=tL_C.
$$

证明。平稳条件为 $Bf=0$，由定理 2.2 及非负性得 $f=a\mathbf c$、$a\ge0$，特别是 $f_5=0$。有限率关系给出 $f_5=p_0q_{02}$，与两个因子严格为正矛盾。允许 $p_0=0$ 时并无此矛盾，例如全部质量位于 $2$ 的吸收律，所以结论明确保留 $p_0>0$。两个非平稳过程的期望累计成本为 $t\langle\ell,g\rangle$ 与 $t\langle\ell,f\rangle$，相减并用 $g-f=\mathbf c$ 得到公式。∎

**数学引文 3.4（有符号图上同调的适用对象）。** 将五边图视为没有二维胞腔的一维图，一条实边余链 $\alpha\in\mathbb R^E$ 在形式反向上取负号。其恰当性指存在状态势 $\phi$ 使 $\alpha=B^{\mathsf T}\phi$。由[《观察者相对局部模型与未来可识别性》命题 10.2、10.4](AURIC_FIB_ATOM_OBSERVER_RELATIVE_LOCAL_MODELS_AND_FUTURE_IDENTIFIABILITY.md)的有符号闭走法判据，等价条件为 $\alpha$ 湮灭 $\ker B$。本图因此只需

$$
\alpha_1+\alpha_2+\alpha_3+\alpha_4=0,
\qquad H^1(G;\mathbb R)=\mathbb R^E/\operatorname{im}B^{\mathsf T}.
$$

在本图也可直接读出这个条件：取 $\phi_0=0$、$\phi_1=\alpha_1$、$\phi_{13}=\alpha_1+\alpha_2$、$\phi_3=\alpha_1+\alpha_2+\alpha_3$、$\phi_2=\alpha_5$，前三条循环边和叶边均满足势增量式，第四条恰要求上述零和。于是定理 3.2 的 $L_C>0$ 排除以状态势表示这些指定成本；它不排除全局图、定义于全图的边函数，或额外给定的全局参数 $t$。

若将 $\ell$ 视作这个有符号余链，形式反向的值为 $-\ell$。若另外允许实际反向跳跃，其非负成本须另行指定，不能同时默认等于这个负值。填入方形二维胞腔会改变链复形，故不沿用此处一维图的 $H^1$。

## 4. 同一初始 seam 的未来合同

**假设 4.1（共同模型与实际可达域）。** 固定一个已知操作模型和一个非空实际可达域 $\mathcal C\subseteq\mathcal D$，令 $\mathcal C_b=\mathcal C\cap\mathcal F_b\ne\varnothing$。比较所有初态时，使用相同的合法有限操作词／有限时域策略集合 $\mathcal W$，其中 $|w|$ 表示规定的有限步数上界，集合包含空操作。策略可以依赖已观察历史，不能依赖尚未观察的真态；拒绝动作可通过显式拒绝输出总化。对每个 $w$，固定共同的可测记录空间及从状态 $s$ 出发的完整记录概率律 $\Gamma_{w,s}$。分支质量、停止、拒绝、等待及未完成结果均按该合同保留；不同长度若属于同一过程，还要求截断相容。

**数学引文 4.2（未来识别在本纤维上的应用）。** 采用[《局部源分裂与读出几何》假设 9.1、定义 9.2–9.3、定理 10.2 与约定 10.3](AURIC_FIB_ATOM_LOCAL_SOURCE_SPLITTING_AND_READOUT_GEOMETRY.md)的共同初始质量合同，定义线性全记录映射

$$
R_w(q)=\sum_{s\in\Sigma}q_s\Gamma_{w,s},\qquad
K_m=T\cap\bigcap_{w\in\mathcal W,\ |w|\le m}\ker R_w,\qquad
K_\infty=T\cap\bigcap_{w\in\mathcal W}\ker R_w.
$$

这里 $R_w$ 作用于未作后选择归一化的初始有符号质量。对概率输入它给出完整的精确记录律，且 $K_{m+1}\subseteq K_m$。既有受限域判据在此为

$$
\{R_w\}_{w\in\mathcal W}\text{ 在 }\mathcal C_b\text{ 上单射}
\quad\Longleftrightarrow\quad
(\mathcal C_b-\mathcal C_b)\cap K_\infty=\{0\}.
$$

具体地，若 $\mathcal C_b$ 含两个不同 $\kappa$，则

$$
\{R_w\}_{w\in\mathcal W}\text{ 在 }\mathcal C_b\text{ 上单射}
\quad\Longleftrightarrow\quad
\exists w\in\mathcal W:\ R_w(\mathbf d)\ne0.
$$

该应用的全部推导是

$$
R_w(p_\kappa)-R_w(p_{\kappa'})
=(\kappa-\kappa')R_w(\mathbf d).
$$

若有一个非零响应，每一对实际不同参数在该记录律上不同；非零有符号测度还意味着存在可测事件，其两概率不同。若全部响应为零，选取假设保证的实际不同参数对，所有记录律均相同，故不单射。一般差异集判据同样由 $R_w(p)-R_w(q)=R_w(p-q)$ 得出。当 $\mathcal C_b$ 为单点时，它已经被确定，即使所有 $R_w(\mathbf d)$ 都为零；当 $\mathcal C_b$ 为空时，前提无可达实现。

若只保留某成功事件 $D$ 条件下的记录，则在成功概率正时得到

$$
\frac{R_w(p)(\,\cdot\cap D)}{R_w(p)(D)}.
$$

参数相关的分母使该映射一般不线性，故须保留成功概率才能使用上述线性记录判据。精确记录律的区分不等于从单次随机历史或任意预定有限样本量精确恢复 $\kappa$。

**定义 4.3（两种逆问题的参数范围）。** 假设 4.1 中 $q\mapsto R_w(q)$ 比较固定动态模型下的初始质量。定理 2.4 比较的则是不同动态模型在同一初始律下的边记录。前者的 $\mathbf d$ 位于初始状态空间，后者的 $\mathbf c$ 位于边空间。若把动态模型也设为未知量，须另行定义包含模型参数的共同源和完整记录合同；不把定理 2.2 的边链商自动当成初始律未来识别定理。

## 5. n 窗口切换图中的两种隐藏维数

**定义 5.1（独立支持与单位置切换）。** 对整数 $n\ge0$，令 $[n]=\{1,\ldots,n\}$，其中 $[0]=\varnothing$，并取

$$
\Sigma_n=\{I\subseteq[n]:i\in I\Rightarrow i+1\notin I\}.
$$

图 $\Gamma_n$ 的顶点为 $\Sigma_n$，无向边为 $\{I,J\}$，其中 $|I\mathbin\triangle J|=1$。这是 Fibonacci cube 的一位差邻接，且 $\Gamma_0=K_1$，参见 S. Klavžar，[《Structure of Fibonacci cubes: a survey》§1](https://users.fmf.uni-lj.si/klavzar/preprints/FibonacciCubesRevised.pdf)，Journal of Combinatorial Optimization 25 (2013), 505–522，[DOI:10.1007/s10878-011-9433-z](https://doi.org/10.1007/s10878-011-9433-z)。对每条无向边任选一次参考定向，得到有符号边界映射 $B_n:\mathbb R^{E(\Gamma_n)}\to H_n=\mathbb R^{\Sigma_n}$。参考定向尚不声明可执行的跳跃方向。

定义

$$
T_n=\{v\in H_n:\textstyle\sum_Iv_I=0\},\qquad
(A_nv)_i=\sum_{I\ni i}v_I\quad(i\in[n]),
$$

并记 $V_n=|\Sigma_n|$、$E_n=|E(\Gamma_n)|$、$h_n=\dim\ker(A_n|_{T_n})$、$c_n=\dim\ker B_n$。取 $F_0=0,F_1=1,F_{j+2}=F_{j+1}+F_j$，并置 $K_n=\lfloor(n+1)/2\rfloor$。所需的既有计数和观察秩来自[《对称 seam、路径缺陷与 Fibonacci 层级》Q7–Q8、第二部分定理 3–4](AURIC_FIB_ATOM_SYMMETRIC_SEAM_PATH_DEFECT_AND_FIBONACCI_HIERARCHY.md)：

$$
N_{n,k}=\begin{cases}\binom{n-k+1}{k},&0\le k\le K_n,\\0,&\text{其他整数 }k,\end{cases}
\qquad V_n=F_{n+2},\qquad h_n=V_n-n-1.
$$

这里 $N_{n,k}$ 是含 $k$ 个位置的合法支持数；质量行与 $n$ 个单点观察的秩为 $n+1$。下述有限和均只在 $0\le k\le K_n$ 取值，空和为零。

**定理 5.2（切换图到静态隐藏空间的比较）。** 对每个 $n\ge0$，有 $\operatorname{im}B_n=T_n$，并有实向量空间短正合列

$$
0\longrightarrow\ker B_n\longrightarrow\ker(A_nB_n)
\xrightarrow{\ B_n\ }\ker(A_n|_{T_n})\longrightarrow0.
$$

因此 $\dim\ker(A_nB_n)=c_n+h_n$，且

$$
\begin{aligned}
E_n&=\sum_{k=0}^{K_n}kN_{n,k},\\
h_n&=\sum_{k=2}^{K_n}N_{n,k},\\
c_n&=E_n-V_n+1=\sum_{k=2}^{K_n}(k-1)N_{n,k},\\
c_n-h_n&=\sum_{k=3}^{K_n}(k-2)N_{n,k}.
\end{aligned}
$$

特别地 $c_n\ge h_n$；严格不等式恰在 $n\ge5$ 成立。边界和前几个值为

$$
\begin{array}{c|rrrrrrr}
n&0&1&2&3&4&5&6\\\hline
h_n&0&0&0&1&3&7&14\\
c_n&0&0&0&1&3&8&18
\end{array}.
$$

证明。每个非空独立支持都能逐个删除元素而保持合法，直到空集，所以 $\Gamma_n$ 连通。对任意顶点 $I$，将空集到 $I$ 的无向路径按参考定向赋予正负系数，边界为 $\mathbf e_I-\mathbf e_\varnothing$。这些差生成 $T_n$，每条边界又都质量为零，故 $\operatorname{im}B_n=T_n$。$n=0$ 时两个空间均为零，同样成立。

由既有观察秩前提，$A_n|_{T_n}$ 的秩为 $n$；其参数对应可直接由 $A_n(\mathbf e_{\{i\}}-\mathbf e_\varnothing)=\mathbf e_i$ 看出。若 $v\in\ker(A_n|_{T_n})$，满射性给出 $B_nf=v$，于是 $A_nB_nf=0$；这证明限制映射的满射性，其核恰是 $\ker B_n$。故得到所述正合列。由秩－零度公式，$\operatorname{rank}B_n=V_n-1$，所以 $c_n=E_n-V_n+1$，并得到中间空间维数。所用秩与商空间结论分别见 Axler，前引书定理 3.21 和 §3E。

为了将两层维数写在同一组支持计数上，按每条边的较大支持 $I$ 及所删除的元素 $i\in I$ 计数。每个这样的对给出边 $\{I,I\setminus\{i\}\}$，每条边恰有一个较大端点及一个被删元素，故

$$
E_n=\sum_{I\in\Sigma_n}|I|=\sum_{k=0}^{K_n}kN_{n,k}.
$$

这个边计数是经典 Fibonacci cube 公式，也等于 Klavžar 前引综述 §4.2 定理 4.4 的 cube polynomial 中一次项的系数；这里的删除计数用于把该公式接到同一观察核上。由 $N_{n,0}=1$、$N_{n,1}=n$（$n=0$ 时后者为零）及 $V_n=\sum_kN_{n,k}$，得

$$
h_n=V_n-n-1=\sum_{k=2}^{K_n}N_{n,k},\qquad
E_n-V_n+1=\sum_{k=2}^{K_n}(k-1)N_{n,k}.
$$

相减即得差值式。$n\le4$ 时没有三元素合法支持，差值为空和；$n\ge5$ 时 $\{1,3,5\}$ 合法，且 $N_{n,3}=\binom{n-2}{3}>0$，每个差值项非负，故差严格为正。表中值由这些有限公式逐项代入；一般 $n$ 的结论由上述计数与满射论证成立。∎

**命题 5.3（概率边界、参考定向与正流）。** 定义 5.1 的 $h_n$ 是全局质量零观察核的维数。含全支撑律的非空固定单点边缘纤维具有此仿射维数；只含边界律的纤维可降维，全部单点边缘为零的纤维对每个 $n$ 都是单点。$c_n$ 与参考定向无关，但若将所有边的实际方向规定为支持添加，则

$$
\ker B_n\cap\mathbb R_{\ge0}^{E(\Gamma_n)}=\{0\}.
$$

若将每条无向边的两个方向均作为不同合法弧，则弧边界 $\widehat B_n$ 的有符号核维数为 $2E_n-V_n+1$。此时非负跳跃成本须作用于两个方向各自的总流，不能仅由净有符号流定价。

证明。固定质量和边缘后的仿射解空间是一个解加上 $\ker(A_n|_{T_n})$。若含全支撑点，在足够小的邻域内其每个仿射方向都保持非负，故概率纤维的仿射维数等于 $h_n$；边界纤维只是该仿射空间与单纯形的交，维数不能更大。若每个边缘为零，非负性迫使任何含某位置的非空支持概率为零，只剩空集上的单位质量。这也证明全局核维数不能替代每个具体纤维的维数。

反转一条参考边只将相应矩阵列乘以 $-1$，给边链空间一个可逆坐标变换，故不改变 $c_n$。现在取支持添加为实际方向，令状态势 $\rho(I)=|I|$。每条边的势增量为一，因而对 $f\ge0$，

$$
\langle\rho,B_nf\rangle=\sum_ef_e.
$$

若 $B_nf=0$，右边为零，所有 $f_e$ 必为零。势沿每条边严格增加，同时证明这种实际定向没有非空有向闭走法。这与 $n\ge3$ 时 $c_n>0$ 相容：非零的有符号循环必须使用正负两种系数。

两个方向都允许时，弧边界矩阵可按 $\widehat B_n=(B_n,-B_n)$ 排列，其像仍为 $T_n$，故核维数为 $2E_n-(V_n-1)$。对弧流 $(f^+,f^-)$，状态导数为 $B_n(f^+-f^-)$，而给定非负弧成本的活动率为

$$
\sum_e\bigl(\ell_e^+f_e^++\ell_e^-f_e^-\bigr).
$$

在同一边两个方向各加 $a>0$ 保持净流不变，却将该式增加 $a(\ell_e^++\ell_e^-)$。只要此成本和为正，净流即不足以决定活动率。若顶点律全支撑，这一对相等的反向流可由有限率 $a/p_i$、$a/p_j$ 实现，并有零边界，所以也是可行平稳活动。

$n=3$ 时，无向 $\Gamma_3$ 正是定义 2.1 的方形加叶边：顶点对应为空集、三个单点及 $\{1,3\}$。定义 2.1 特意采用绕方形一周的实际定向，包含两条删除边，故适用定理 3.2；全添加定向不具有那个正循环。两种定向拥有相同的有符号维数，却有不同的非负可实现性。∎

## 追加锚（本行以下为增补区）

## 6. 指定平稳五态族的同路径两矩

本章在既有五态概率纤维和四边正循环上明确选择一个二参数 Markov 族，研究同一完整路径记录上两个固定函数的精确期望。结论是指定矩对在整个紧矩形及共同小时间窗内的单射性；完整记录已有的参数识别、平方矩比较和各项实现边界分别保留。

### 6.1. 参数族、结论与量词

**定义 6.1（参数族、生成元与固定读出）。** 给定任意常数

$$
0<\epsilon<\frac15,\qquad 0<g_{\min}<g_{\max}<\infty,
$$

定义紧矩形

$$
\Theta=[\epsilon,\tfrac25-\epsilon]\times[g_{\min},g_{\max}],
\qquad \theta=(\kappa,\gamma).
\tag{6.1}
$$

令 $\Sigma=\{0,1,2,3,13\}$。状态顺序固定为 $(0,1,2,3,13)$，初始行概率为

$$
p_\kappa=(\tfrac1{10}+\kappa,\tfrac25-\kappa,
\tfrac1{10},\tfrac25-\kappa,\kappa).
\tag{6.2}
$$

记 $C=\{0,1,13,3\}$，后继映射为

$$
\sigma(0)=1,\quad\sigma(1)=13,\quad
\sigma(13)=3,\quad\sigma(3)=0.
$$

行生成元 $Q_\theta$ 的非零元按下式定义

$$
q_{i,\sigma(i)}=\frac{\gamma}{p_{\kappa,i}}\quad(i\in C),
\qquad q_{ii}=-\frac{\gamma}{p_{\kappa,i}}\quad(i\in C).
\tag{6.3}
$$

其余元为零，尤其 $q_{02}=0$，状态 $2$ 吸收。固定状态函数及其列向量为

$$
W(0)=0,\quad W(1)=2,\quad W(2)=3,\quad W(3)=5,\quad W(13)=7,
\qquad w=(0,2,3,5,7)^{\mathsf T}.
\tag{6.4}
$$

令 $N_{01}(T)$ 只计实际的 $0\to1$ 跃迁。$T$ 是已知、共同单位下的确定性截止时间，所有期望均取自以 (6.2) 开始、生成元为 (6.3) 的同一无条件路径律。

**定理 6.2（指定矩对的统一小时间窗分离）。** 对每个 (6.1) 的矩形，(6.2)–(6.3) 在共同路径空间上定义平稳、有限率、非爆炸的概率律族，并允许第 6.3 节所定的参数无关完整记录映射。取

$$
\boxed{T_* = \frac{15\epsilon^3}{28g_{\max}}>0.}
\tag{6.5}
$$

则对每一个 $0<T\le T_*$，映射

$$
\mathcal M_T:\Theta\longrightarrow\mathbb R^2,\qquad
\mathcal M_T(\kappa,\gamma)
=\left(\mathbb E_\theta N_{01}(T),
\mathbb E_\theta[W(S_0)N_{01}(T)]\right)
\tag{6.6}
$$

在整个 $\Theta$ 上单射。更具体地，令第二坐标为 $H_T(\kappa,\gamma)$，则

$$
\mathbb E_\theta N_{01}(T)=\gamma T,
\qquad
\partial_\kappa H_T(\kappa,\gamma)
\le -5\gamma^2T^2\le-5g_{\min}^2T^2<0
\tag{6.7}
$$

对上述全部参数与时间同时成立。端点导数由开域 $0<\kappa<2/5$ 上的光滑公式限制而来。

量词是“任取矩形，存在同一个显式 $T_*$，对全部 $T\in(0,T_*]$ 和任意两参数成立”，不是每点各有一个邻域或时间。常数 (6.5) 仅为充分界，不声称最优，也不判定更长时间的原矩对是否单射。完整记录的识别与平方矩比较在任意已知 $T>0$ 成立，见第 6.6 节；它们不替代 (6.6) 的证明。

### 6.2. 载体、概率可行性与平稳构造

**定义 6.3（状态质量与边流载体）。** 状态质量空间为 $H=\mathbb R^{\{0,1,2,3,13\}}$，质量零空间为 $T_0=\{v:\sum_iv_i=0\}$。定义

$$
A(v)=(v_1+v_{13},v_2,v_3+v_{13}),\qquad
b=(\tfrac25,\tfrac1{10},\tfrac25),\qquad
d=(1,-1,0,-1,1).
$$

直接消元得 $A(p_\kappa)=b$、$\sum_i p_{\kappa,i}=1$，固定 $b$ 的全部概率纤维为 $0\le\kappa\le2/5$，且

$$
p_\kappa-p_{\kappa'}=(\kappa-\kappa')d,
\qquad \ker(A|_{T_0})=\mathbb Rd.
\tag{6.8}
$$

这是本卷 §1 和 [S5] §§1–3 的既有纤维。在 (6.1) 上，四个循环状态的质量均至少为 $\epsilon$；状态 $2$ 的质量恒为 $1/10$。所有五个质量严格为正，并有

$$
a:=p_{\kappa,0}=\tfrac1{10}+\kappa
\le\tfrac12-\epsilon<\tfrac12.
\tag{6.9}
$$

按边顺序 $(0\to1,1\to13,13\to3,3\to0,0\to2)$，边空间中的向量为 $c=(1,1,1,1,0)$。若 $B$ 的每列为终点单位质量减起点单位质量，则 $Bc=0$。$d$ 属于状态质量空间，$c$ 属于边流空间；二者没有被识别成同一个向量。

**引理 6.4（共同有限率构造）。** (6.2)–(6.3) 对整个矩形给出所需平稳路径律；其平稳边流为 $\gamma c$。

**证明。** 每个循环状态的出率不超过

$$
M:=\frac{g_{\max}}\epsilon<\infty.
$$

对全部参数使用强度同为 $M$ 的 Poisson 候选时刻。初态按 $p_\kappa$ 取值；在候选时刻按行随机矩阵

$$
K_\theta=I+Q_\theta/M
$$

更新状态，每次采用独立随机选择。保持原态的候选不算实际跃迁。非对角元非负、对角元非负、行和为一，故这是一个概率构造；状态 $2$ 永远不动。有限时间的实际跃迁数不超过 Poisson 候选数，因而非爆炸。其转移矩阵直接由候选次数求和得到

$$
P_\theta(t)=e^{-Mt}\sum_{n=0}^\infty\frac{(Mt)^n}{n!}K_\theta^n
=e^{tQ_\theta}.
\tag{6.10}
$$

每条循环边的初始概率流为 $p_{\kappa,i}q_{i,\sigma(i)}=\gamma$；各循环顶点入流与出流同为 $\gamma$，状态 $2$ 的入出流均为零。因此 $p_\kappa Q_\theta=0$，进而 $p_\kappa K_\theta=p_\kappa$、$p_\kappa P_\theta(t)=p_\kappa$。齐次转移与不变初始律还给出有限维联合分布的时间平移不变性，即严格平稳性。

这个构造可使用共同的 Poisson 候选序列、独立均匀变量及初态逆分布取样，因各概率关于参数连续而得到可测参数族。不同参数下的实现不要求使用相同实际样本；它们使用同一状态、路径及记录合同。该链可约，本章不声称不可约、唯一不变律或每条样本都活动。“正”指初态全支撑和四条选定循环边率严格正，不指所有非对角率均正。

本卷定理 2.4 已使用有限率 Poisson 构造，定理 3.2 已给出均匀初态的平稳正循环，命题 3.3 已限定叶边流为零。本章复用这一有限状态构造，并验证其在整个非均匀族上的适用性。∎

### 6.3. 共同完整记录及指定矩

**定义 6.5（共同路径空间与完整记录）。** 共同路径空间 $\Omega$ 取所有 $[0,\infty)$ 上右连续、有左极限、每个有限区间仅有有限次实际跃迁的 $\Sigma$ 值路径，实际跃迁仅沿 (6.3) 的循环边；配以坐标评价生成的可测结构。引理 6.4 的全部参数律均定义在此空间上。

在有限区间 $[0,T]$，令 $0<t_1<\cdots<t_m\le T$ 为实际跃迁时刻，$s_0=S_0$、$s_j=S_{t_j}$、$t_0=0$。记录空间取所有这样的有限有标号时间记录的不交并，赋予各时间单纯形的 Borel 可测结构；只允许相邻标签满足指定循环边，或没有跃迁。定义

$$
R_T(S)=\bigl(s_0;(t_j,s_{j-1},s_j)_{j=1}^m;
 s_m,T-t_m,\mathrm{censored}\bigr).
\tag{6.11}
$$

$m=0$ 时末项为 $(s_0,T,\mathrm{censored})$。吸收分支 $s_0=2,m=0$、每个循环初态的无跳分支、全部多跳路径及最后一个尚未结束的等待段均保留。固定时刻恰发生跳跃是零概率事件，(6.11) 仍给出明确约定。候选 Poisson 自环不是实际事件，不记入 (6.11)。

这是所有参数共同的可测映射，映射内没有未知参数，也没有模型标识被额外输出。它没有按成功、活动、初态或跳数进行后选择。记录在不同截止时间间由截断相容；底层过程同一个，未对不同矩分别重置或另行选择实验。初态标签、实际跳时与跳边还原有限区间的整条分段常值路径。

为明确无跳和末段质量，设 $\lambda_i=-q_{ii}$。对合法循环路径及其有序时间，相对于标签计数测度与有序时刻 Lebesgue 测度的记录密度为

$$
p_{\kappa,s_0}
\left[\prod_{j=1}^m
 e^{-\lambda_{s_{j-1}}(t_j-t_{j-1})}
 q_{s_{j-1},s_j}\right]
 e^{-\lambda_{s_m}(T-t_m)}.
\tag{6.12}
$$

该式也由候选构造得到：停留在 $i$ 时，“没有接受一次离开”的概率为
$e^{-Mh}\sum_n(Mh)^n(1-\lambda_i/M)^n/n!=e^{-\lambda_i h}$。
对 $m=0$，(6.12) 是原子概率 $p_{\kappa,i}e^{-\lambda_iT}$，其中 $i=2$ 给 $1/10$。合法循环路径密度严格正；其他记录概率为零。末段指数因子不可省略。

在同一记录上定义

$$
n(r)=\sum_{j=1}^m\mathbf1_{(s_{j-1},s_j)=(0,1)},
\qquad h(r)=W(s_0)n(r).
\tag{6.13}
$$

于是 (6.6) 恰为 $(\int n\,d\mu_{\theta,T},\int h\,d\mu_{\theta,T})$，其中 $\mu_{\theta,T}=(R_T)_*\mathbb P_\theta$。由 $0\le n\le$ 候选 Poisson 数、$0\le W\le7$，两个期望均有限。$W$ 始终为 (6.4)，不使用随参数变动的读出。

**引理 6.6（带初态权重的计数公式）。** 对任意固定有界状态函数 $f$，有

$$
\mathbb E_\theta[f(S_0)N_{01}(T)]
=q_{01}\int_0^T
\mathbb E_\theta[f(S_0)\mathbf1_{\{S_t=0\}}]\,dt.
\tag{6.14}
$$

**证明。** 在长度 $h$ 的一小段内，条件于段首完整历史，恰一个候选时只有段首为 $0$ 且接受 $0\to1$ 才贡献该边计数，其期望为 $\mathbf1_{\{S_t=0\}}q_{01}h e^{-Mh}$。至少两个候选贡献的计数期望至多 $Mh(1-e^{-Mh})\le M^2h^2$；把 $e^{-Mh}$ 换为一的误差也不超过 $M^2h^2$。乘以已在段首历史中可知的 $f(S_0)$，误差绝对值至多 $2\|f\|_\infty M^2h^2$。均分 $[0,T]$ 后求和并令网格趋零，误差趋零，连续的有限矩阵转移概率给出右侧积分。固定时刻 $S_t$ 与 $S_{t-}$ 几乎处处无差别。∎

取 $f=1$ 并用平稳性，立即得到

$$
\mathbb E_\theta N_{01}(T)
=\frac\gamma a\int_0^T a\,dt=\gamma T.
\tag{6.15}
$$

### 6.4. 原交叉矩的精确表示

令 $D_\kappa=\operatorname{diag}(p_\kappa)$，定义仅供计算使用的矩阵

$$
\widehat Q_\theta=D_\kappa^{-1}Q_\theta^{\mathsf T}D_\kappa,
\qquad L_\kappa=\widehat Q_\theta/\gamma.
\tag{6.16}
$$

若 $\rho=\sigma^{-1}$，则 $L_\kappa$ 的每个循环行只有

$$
(L_\kappa)_{i,\rho(i)}=1/p_{\kappa,i},
\qquad (L_\kappa)_{ii}=-1/p_{\kappa,i};
\tag{6.17}
$$

第 $2$ 行为零。它仍是行生成元，反向循环为 $0\to3\to13\to1\to0$。式 (6.16) 是平稳转移矩阵的代数伴随表示，不授权实际执行反向边；下述期望仍是原来的正向路径律和 (6.13) 的函数。

由矩阵幂级数与转置，有

$$
e^{t\widehat Q_\theta}
=D_\kappa^{-1}(e^{tQ_\theta})^{\mathsf T}D_\kappa.
$$

故逐项求和得到

$$
\mathbb E_\theta[W(S_0)\mathbf1_{\{S_t=0\}}]
=\sum_i p_{\kappa,i}w_i(P_\theta(t))_{i0}
=a(e^{t\widehat Q_\theta}w)_0.
\tag{6.18}
$$

将 (6.18) 代入 (6.14)，并令 $u=\gamma t$、$z=\gamma T$，得原交叉矩的精确公式

$$
\boxed{H_T(\kappa,\gamma)
=\gamma\int_0^T(e^{\gamma tL_\kappa}w)_0\,dt
=\int_0^z(e^{uL_\kappa}w)_0\,du.}
\tag{6.19}
$$

(6.18) 没有除以观察事件概率、没有丢弃任何分支；它只是同一无条件求和的改写。特别地，(6.19) 没有用 $W(S_T)$、条件初态、边际均值或独立拼接的路径代替 $W(S_0)N_{01}(T)$。

因为 $w_0=0$ 且 $\rho(0)=3$，有

$$
(L_\kappa w)_0=\frac5a,
\qquad (L'_\kappa w)_0=-\frac5{a^2},
\tag{6.20}
$$

其中撇号指固定状态坐标下对 $\kappa$ 求导。这给出二阶主项；要证明全矩形结论，还必须控制导数余项。

### 6.5. 统一导数余项与全局单射证明

对列向量取最大值范数，对矩阵取其诱导范数

$$
\|B\|_\infty=\max_i\sum_j|B_{ij}|.
$$

由 (6.17) 和 $p'_{\kappa,i}\in\{1,-1\}$（循环状态），整个矩形上均有

$$
\|L_\kappa\|_\infty\le\frac2\epsilon,
\qquad \|L'_\kappa\|_\infty\le\frac2{\epsilon^2}.
\tag{6.21}
$$

注意状态 $2$ 对这两个范数的贡献都是零。$L_\kappa$ 的矩阵指数是随机矩阵，理由与 (6.10) 相同，故对 $u\ge0$，

$$
\|e^{uL_\kappa}\|_\infty=1,
\qquad
\|e^{uL_\kappa}-I\|_\infty
\le u\|L_\kappa\|_\infty.
\tag{6.22}
$$

第二式由 $e^{uL}-I=\int_0^u e^{vL}L\,dv$ 得到。

**引理 6.7（参数导数的二阶余项界）。** 对上述全部参数及 $u\ge0$，

$$
\left\|\partial_\kappa e^{uL_\kappa}-uL'_\kappa\right\|_\infty
\le u^2\|L_\kappa\|_\infty\|L'_\kappa\|_\infty
\le\frac{4u^2}{\epsilon^3}.
\tag{6.23}
$$

**证明。** 有限矩阵恒等式

$$
e^{uA}-e^{uB}
=\int_0^u e^{(u-v)A}(A-B)e^{vB}\,dv
$$

可由对 $e^{(u-v)A}e^{vB}$ 求导并积分直接验证。取 $A=L_{\kappa+h}$、$B=L_\kappa$，除以 $h$ 后令 $h\to0$。有限区间上的矩阵连续性给

$$
\partial_\kappa e^{uL_\kappa}
=\int_0^u e^{(u-v)L_\kappa}L'_\kappa e^{vL_\kappa}\,dv.
\tag{6.24}
$$

这也证明所需导数存在，不假设 $L$ 与 $L'$ 交换。减去 $uL'_\kappa$ 后，积分内写成

$$
(e^{(u-v)L_\kappa}-I)L'_\kappa e^{vL_\kappa}
+L'_\kappa(e^{vL_\kappa}-I).
$$

应用 (6.22)，两项范数之和至多
$[(u-v)+v]\|L_\kappa\|_\infty\|L'_\kappa\|_\infty$。
积分即给第一界，再用 (6.21)。这里的界对整个矩形共同成立，没有隐含参数相关的 $O(\cdot)$ 常数。∎

**定理 6.2 的剩余证明。** 固定 $\gamma,T$，$z=\gamma T$ 对 $\kappa$ 不变。(6.19)、(6.20)、(6.23) 及 $\|w\|_\infty=7$ 给出

$$
\partial_\kappa H_T(\kappa,\gamma)
=-\frac5{2a^2}z^2+E_\kappa(z),
\qquad
|E_\kappa(z)|\le\frac{28}{3\epsilon^3}z^3.
\tag{6.25}
$$

积分下求导由 (6.24) 的连续性与有限区间共同界保证。若 $0<T\le T_*$，则

$$
0<z\le g_{\max}T_* =\frac{15\epsilon^3}{28},
\qquad
\frac{28}{3\epsilon^3}z^3\le5z^2.
$$

又由 $a<1/2$，有 $5/(2a^2)\ge10$。因此

$$
\partial_\kappa H_T\le-10z^2+5z^2=-5z^2,
$$

即 (6.7)。对任意 $\kappa_2>\kappa_1$，在整个参数线段上积分，得到

$$
H_T(\kappa_2,\gamma)-H_T(\kappa_1,\gamma)
\le-5\gamma^2T^2(\kappa_2-\kappa_1)<0.
\tag{6.26}
$$

若两个参数点的 (6.6) 相同，则由第一坐标 (6.15) 和 $T>0$，先得 $\gamma_1=\gamma_2$。在这个相同的 $\gamma$ 上，(6.26) 再给 $\kappa_1=\kappa_2$。这直接排除了矩形上任意两点的碰撞，完成全局单射证明；没有把非零 Jacobian 的局部结论当成全局结论。∎

为说明响应的阶数，(6.22) 同样给

$$
\left\|e^{uL_\kappa}-I-uL_\kappa\right\|_\infty
\le\tfrac12u^2\|L_\kappa\|_\infty^2,
$$

从而有可核算的统一主项式

$$
\left|H_T(\kappa,\gamma)-\frac5{2a}(\gamma T)^2\right|
\le\frac{14}{3\epsilon^2}(\gamma T)^3.
\tag{6.27}
$$

首个非零项来自初态 $3$ 经 $3\to0\to1$ 的两跳贡献；初态 $0$ 的权重为零。这个说明与 (6.19)–(6.27) 一致，但单靠“两跳主导”的口头叙述不能承担统一性证明。

### 6.6. 完整记录识别与平方矩比较

**完整律反演。** 对任意已知 $T>0$，完整记录律已给出

$$
\kappa=\mu_{\theta,T}\{s_0=13\}.
\tag{6.28}
$$

再由 (6.15) 得 $\gamma=T^{-1}\int n\,d\mu_{\theta,T}$。也可完全使用记录事件概率：令

$$
v_0=\mu_{\theta,T}\{s_0=0,m=0\}
=a e^{-\gamma T/a},
$$

则

$$
\gamma=-\frac aT\log\left(\frac{v_0}{a}\right).
\tag{6.29}
$$

式 (6.29) 由两个无条件质量作代数计算，实际记录仍是 (6.11)，没有删除无跳以外的分支。由于 $a>0$、$0<v_0<a$，逆式良定义。完整初始记录单独识别 $\kappa$，但不识别 $\gamma$；保留路径活动后才识别两者。甚至 $W(S_0)$ 的完整分布已给 $\Pr(W(S_0)=7)=\kappa$，因为 (6.4) 五值互异。这复用 [S3] Q9、第二部分定理 6–7 及 [S4] 命题 11.5 的既有无损编码结论。

**平方矩／计数比较。** 在同一个 (6.11) 上还可计算 $W(s_0)^2$。直接代入 (6.2)，或者复用本卷数学引文 1.4，有

$$
\mathbb E_\theta W(S_0)=\frac{31}{10},
\qquad
\mathbb E_\theta W(S_0)^2=\frac{25}{2}+20\kappa.
\tag{6.30}
$$

因此比较矩对

$$
\left(\mathbb E_\theta W(S_0)^2,
\mathbb E_\theta N_{01}(T)\right)
=\left(\frac{25}{2}+20\kappa,\gamma T\right)
\tag{6.31}
$$

对所有已知 $T>0$ 都显然单射。它是已知静态平方矩反演与计数恒等式的直接组合，不是本章目标的新版本。本章定理证明的是原来的 (6.6)，其中第二坐标必须为 $\mathbb E[W(S_0)N_{01}(T)]$，而非 (6.31) 的平方矩、端点均值或其他坐标。

只取两个边际均值 $(\mathbb EW(S_0),\mathbb EN_{01}(T))=(31/10,\gamma T)$ 不能区分 $\kappa$；把交叉矩换成它们的乘积 $(31/10)\gamma T$ 也不能。主项 (6.27) 是二阶，而该乘积是一阶。相关性在同一初始标号与后续计数之间，不能由分开取得的边际期望代替。

**本命题实际增加的内容。** 完整记录早已识别参数，(6.6) 的两个函数也是该记录的固定后处理；本命题不增加记录信息。它精确增加了一个比较结论：在指定正二参数族上，两个指定的精确期望已经足以分离参数，并有整个紧矩形共同的正时间界。这里“矩足以分离”仅指参数到期望向量的单射；不声称随机统计量 $(n,h)$ 是 Fisher–Neyman 意义的充分统计量，也不声称它与完整记录具有相同决策风险或统计信息。

**单样本与统计恢复。** 每个参数下，“初态为 $2$、全程吸收”这一完全相同的记录都有概率 $1/10$。所以不存在只凭一条记录就对所有参数几乎必然无误的精确估计器；即使另行允许有限 $n$ 次独立重复制备，全为该记录的概率仍为 $10^{-n}>0$，同样不能保证无误精确恢复。本章没有给出采样方法、有效样本量、置信界、风险优越性或资源收益。

(6.26) 是已知相同 $\gamma$ 下精确矩的确定性斜率界，不是含噪联合反演的统计保证。该界随 $T\downarrow0$ 退化，也没有消除取得二阶小信号的代价。链有吸收成分，亦不能未经论证便用一条长路径的时间平均替代这里的平稳总体期望。

### 6.7. 源、动作、时间及黄金供应的对应边界

**两个不同的逆问题。** 本卷定义 4.3、[S4] 假设 1.4、[S5] 定义 10.5 区分固定动态模型下的初始质量反演和未知模型反演。本章显式选择扩大参数域 (6.1)：$\kappa$ 同时改变初始质量和 (6.3) 的等待率，$\gamma$ 改变循环活动尺度。因而路径律并非一个参数无关线性算子单独作用于 $p_\kappa$；不能直接套用固定核的 $R(p_\kappa)-R(p_{\kappa'})=(\kappa-\kappa')R(d)$。

在每个固定参数点，物理时间解释尚未赋予的数学参数 $t$ 下有 $\partial_t p=0$ 和边流 $\gamma c$；沿模型参数变化则有 $\partial_\kappa p=d$。这两种导数不相同。对每个允许 $\kappa$，整个 $[g_{\min},g_{\max}]$ 都可取，故没有推出 $\gamma=f(\kappa)$，也没有把一维初始纤维变成两个原生源。式 (6.3) 是本章选定族的指定动力学，不是从维数、正负号或名称推导出来的 FIB 实现。

**共同时间单位。** (6.15) 反演 $\gamma$ 使用已知 $T$。式 (6.19) 的动力学尺度为 $z=\gamma T$。若把时间坐标改为 $t'=ct$（$c>0$），则 $T'=cT$、$\gamma'=\gamma/c$，乘积及同单位表示的结论不变；(6.5) 也相应变为 $T_*'=cT_*$。没有独立的共同时间校准，就没有以某个物理单位识别 $\gamma$ 的结论。Poisson 参数、跳跃数、非负路径成本、等待秒数和状态期望导数是不同对象。

**黄金与正谱供应的实际范围。** [S2] 定义 1.1、约定 1.2 与定理 3.2 使用有符号阶乘余项的累计正性前提，给同一函数的正 Laplace 谱密度及完全单调性；定理 5.2 给五模式解析响应的黄金阈值。其定义 6.1 的四单位向量合同是

$$
G_\tau=\begin{pmatrix}
1&\sqrt\tau&0&0\\
\sqrt\tau&1&\sqrt\tau&0\\
0&\sqrt\tau&1&\sqrt\tau\\
0&0&\sqrt\tau&1
\end{pmatrix},
\qquad
G_\tau\succeq0\ \Longleftrightarrow
0\le\tau\le\frac{3-\sqrt5}{2}.
\tag{6.32}
$$

其完整证明通过行列式 $1-3\tau+\tau^2$、四个路径谱特征值和 Gram 分解完成；非相邻内积为零是不可删除的合同。本章没有给出由 (6.11) 产生这四个单位向量及所有指定内积的映射，没有把阶乘尺度平移接成 (6.3) 的生成元，也没有把其谱正性接成 (6.19) 的路径计数公式。单独选取 $w=(0,2,3,5,7)$ 只指定一个实值状态函数，不实例化 (6.32)。状态数相同、矩阵秩相同、某些量都为正或都出现 Fibonacci 名称，均不能建立这种对应。

**尚需的对应。** 若要进一步主张原生 FIB、黄金、物理或资源结论，至少须分别给出实际可制备来源与 $p_\kappa$ 的对应、合法动作与各跳边/等待率的对应、完整输出和截尾记录与 (6.11) 的对应、同一来源上的正性/Gram 实现、时间及其他量纲校准，以及具体采样/控制/资源模型。本章均未建立这些桥，也没有新增实际源端口、读出端口、时钟或状态重置权限。

本章不处理原始共同零点问题（common-zero）或风险下确界，不证明 COMPLETE 最优性，不向全部窗口、全部时间或整个金字塔推广。独立的 returned-cut 记忆定理不构成本章联合关系的证明。

### 6.8. 数学来源与适用范围

| 来源 | 复用的数学内容及其范围 |
| --- | --- |
| 本卷 §§1–4 | 五态概率纤维及其质量零方向，状态质量与边流的不同载体，定理 2.4 的有限率 Poisson 构造、定理 3.2 的平稳正循环、命题 3.3 的叶边限制，以及定义 4.3 的两类逆问题。数学引文 1.4 已给出平方矩反演。 |
| [S2：带符号阶乘核、黄金阈值与共同 Gram 相容性](AURIC_FIB_ATOM_SIGNED_FACTORIAL_KERNEL_AND_GOLDEN_COMPATIBILITY.md) | 定义 1.1、约定 1.2 与定理 3.2 给出同一阶乘余项在累计估计前提下的正 Laplace 谱表示；命题 3.3、定理 5.2 给出五模式解析响应的黄金阈值；定义 6.1、定理 6.2 给出四单位向量的完整 Gram 合同与判据。累计估计是该谱供应的显式前提；定理 6.2（本章）不依赖这些估计或谱结论。 |
| [S3：对称 seam、路径缺陷与 Fibonacci 隐藏层级](AURIC_FIB_ATOM_SYMMETRIC_SEAM_PATH_DEFECT_AND_FIBONACCI_HIERARCHY.md) | 第二部分定理 6–7 及 Q9 的完整初值给出合法支持上列表和加权和的无损编码；Q10–Q11 限定共同核、精确律和完整记录的识别条件。五值函数的完整分布与单一均值不可互换。 |
| [S4：观察者相对局部模型与未来可识别性](AURIC_FIB_ATOM_OBSERVER_RELATIVE_LOCAL_MODELS_AND_FUTURE_IDENTIFIABILITY.md) | 假设 1.4 固定比较中的共同模型；§§5–6 区分完整记录律、实际可行差异及有限样本恢复；命题 11.5 给出五态加和计数的无损律编码及均值盲性；假设 11.8 与定义 12.5 保留模型参数和物理对应的额外条件。 |
| [S5：局部源分裂与读出几何](AURIC_FIB_ATOM_LOCAL_SOURCE_SPLITTING_AND_READOUT_GEOMETRY.md) | §§1–5 给出既有纤维、可行域、状态／读出载体及固定读出的响应；假设 9.1、定义 9.2–9.3 与定理 10.2 要求共同初始源和完整记录；定义 10.5 区分改变初始律与改变取得核。固定初始源的一维核结论不直接成为本章二参数结论。 |

本章使用有限状态 Markov 过程的 Poisson 构造、平稳转移矩阵的代数伴随、矩阵指数差分积分公式和诱导范数估计，并在第 6.2–6.5 节给出所需推导。既有纤维、完整初始编码、平方矩反演及有限率循环保留上述归属，一般线性代数和矩阵方法也不作原创性声明。

式 (6.19)–(6.26) 说明本章的具体结论：原交叉矩的参数导数具有全矩形共同的余项界，与计数恒等式共同给出定理 6.2。它没有增加完整记录的信息，没有建立第 6.7 节所列的原生、黄金、物理、资源或统计对应，也不蕴含这些对应不存在。该结论及上述归属不构成新颖性判断。

## 追加锚（本行以下为增补区）
