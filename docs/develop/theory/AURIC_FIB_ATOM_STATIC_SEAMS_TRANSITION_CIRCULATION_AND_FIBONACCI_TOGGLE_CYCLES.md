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

## 6. 固定总槽数的指数—计数—概率桥

**定义 6.1（四种编码及其共同来源）。** 沿用定义 1.1 的原生列表标签。另取非负整数指数 $a=(a_2,a_3,a_5,a_7)$，指定数值编码

$$
N(a)=2^{a_2}3^{a_3}5^{a_5}7^{a_7},\qquad
M a=(a_2+a_7,a_3,a_5+a_7)=(u,v,w),\qquad
S(a)=2a_2+3a_3+5a_5+7a_7.
$$

这里 $7$ 是编码所用素数；列表 $[2,5]$ 的加性值也是 $7$，但列表、素数、指数不是同一对象。由[《Fibonacci 原子关系生成》定理 58.1](FIBONACCI_ATOMIC_RELATION_GENERATION.md)及[《kappa 荷、指数纤维与黄金范数读出》Q1、Q3–Q7](AURIC_FIB_ATOM_KAPPA_CHARGE_EXPONENT_FIBERS_AND_GOLDEN_NORM_READOUT.md)，固定 $Ma$ 后指数为 $(u-k,v,w-k,k)$，$k\in\mathbb Z\cap[0,\min(u,w)]$，且 $\ker M=\mathbb Z(-1,0,-1,1)$。这不是 $S$ 的核：$S=(2,3,5)M$，而 $(3,-2,0,0)\in\ker S\setminus\ker M$。

给定总槽数 $m\ge1$，只允许 $\sum_j a_j\le m$，将指数解释成四种非空模式的出现次数，并补空槽

$$
n=(n_0,n_1,n_2,n_3,n_{13})
=(m-\textstyle\sum_j a_j,a_2,a_3,a_5,a_7),\qquad p=n/m.
$$

这是一份声明的计数来源，不从整数 $N(a)$ 自动生成有序原生历史。[《观察者与算术关系》A-3.1–A-3.3](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md)供应固定总数计数纤维。其在此字典下给出

$$
\begin{aligned}
n(k)&=(m-u-v-w+k,u-k,v,w-k,k),\\
\max(0,u+v+w-m)&\le k\le\min(u,w),\qquad k\in\mathbb Z,\\
(X,Z,Y)&=(u/m,v/m,w/m),\qquad \kappa=k/m.
\end{aligned}
$$

整数区间非空恰要求 $u,v,w\ge0$、$u+v\le m$、$w+v\le m$。若另设指数盒 $0\le a_j\le A_j$，还须 $0\le v\le A_3$，并把下界换为 $\max(0,u+v+w-m,u-A_2,w-A_5)$、上界换为 $\min(u,w,A_7)$。非空时格点数为上界减下界加一。总槽数零仅给零计数，不能除以零归一化。

**命题 6.2（核的整数提升及归一化网格）。** 令 $T_{\mathbb Z}=\{n\in\mathbb Z^5:\sum_s n_s=0\}$，取投影 $\pi(n)=(n_1,n_2,n_3,n_{13})$ 及提升

$$
j(a)=(-a_2-a_3-a_5-a_7,a_2,a_3,a_5,a_7).
$$

则 $\pi:T_{\mathbb Z}\to\mathbb Z^4$ 与 $j$ 互逆，$Aj=M$，并将 $\ker M$ 双射到 $\ker(A|_{T_{\mathbb Z}})$，其生成元提升为 $\mathbf d$。固定 $m$ 的计数桥为 $n=m\mathbf e_0+j(a)$；它把相容的非负指数与空槽计数双射到满足 $mp_s\in\mathbb Z$ 的概率律。固定边界时，其像恰为数学引文 1.2 的线段与该网格的交。

证明。$\pi j=I$，而质量零使 $j\pi n=n$；$Aj=M$ 由三个占位坐标给出。代入整数核生成元得 $j(-1,0,-1,1)=\mathbf d$。仿射式的首坐标非负正是总槽数限制；除以 $m$ 的逆为乘以 $m$，故不丢失这些整数计数。它只给分母整除 $m$ 的有理点。对任意固定 $m$，一般实概率不在像中；所有 $m$ 的并给有理律，也不含无理律。$p$ 的实 seam 坐标 $\kappa$ 与指数 $k$ 由 $k=m\kappa$ 联系，不能省略 $m$。$S(a)/m=\mathbb E_pW$ 由定义 6.1 和数学引文 1.4 得到，故补空槽保证了同一分母。∎

## 7. 边流逆式与实际可行纤维

**定义 7.1（对称边截面与残余坐标）。** 在定义 2.1 的边序下，记 $f=(a,b,c,d,e)$，并取

$$
x=a-c,\quad z=e,\quad y=b-d,\quad
r_\sigma=a-b+c-d,\quad r_\omega=a+b+c+d.
$$

指定 $AB$ 的右逆 $Q(x,z,y)=(x/2,y/2,-x/2,-y/2,z)$。于是 $f-Q(ABf)=(a_0,b_0,a_0,b_0,0)$，其中 $a_0=(a+c)/2$、$b_0=(b+d)/2$。置

$$
\sigma=b_0-a_0=-r_\sigma/2,\qquad
\Omega=a_0+b_0=r_\omega/2,\qquad
U=(1,0,1,0,0),\quad V=(0,1,0,1,0).
$$

消费定理 2.2 得

$$
f-Q(ABf)=\frac{\Omega}{2}\mathbf c+\frac{\sigma}{2}(V-U),
\qquad B(f-Q(ABf))=\sigma\mathbf d.
$$

因此 $\Omega$ 的一半才是此分裂中的循环系数。若 $\dot p=Bf$，实际 $\dot\kappa=b-c=(x+y)/2+\sigma$；只有 $x=y=0$ 时它等于 $\sigma$。这里的状态截面为 $BQ$，与数学引文 1.2 的 $L$ 相差 $\mathbf d(x+y)/2$。更换截面改变残余系数，不改变 $p_{13}$ 或 $\dot p_{13}$。

**定理 7.2（五读数逆式及非负像）。** 线性映射 $f\mapsto(x,z,y,r_\sigma,r_\omega)$ 的逆为

$$
\begin{aligned}
a&=(r_\sigma+r_\omega+2x)/4,&
b&=(r_\omega-r_\sigma+2y)/4,\\
c&=(r_\sigma+r_\omega-2x)/4,&
d&=(r_\omega-r_\sigma-2y)/4,\qquad e=z.
\end{aligned}
$$

非负边流的精确像为

$$
z\ge0,\qquad r_\omega+r_\sigma\ge2|x|,\qquad
r_\omega-r_\sigma\ge2|y|.
$$

给定当前律 $p$ 后，还须在 $p_0=0$ 时令 $a=e=0$，在 $p_1=0,p_{13}=0,p_3=0$ 时分别令 $b=0,c=0,d=0$，其中各坐标由上述逆式计算。

证明。两和 $a+c=(r_\omega+r_\sigma)/2$、$b+d=(r_\omega-r_\sigma)/2$ 与两差 $a-c=x,b-d=y$ 共同给出逆式，反向代入恢复五读数。每对和至少为差的绝对值恰等价于该对坐标非负。最后的零坐标条件正是定义 2.3 的有限率出流条件；正质量起点可取 $q_{ij}=f_{ij}/p_i$。这些是一个时刻的精确条件，整个规定轨迹还要满足 $\dot p=Bf$、初值、概率可行性及非爆炸条件。逆式恢复的是给定时刻边流或同型累计边向量，不恢复等待时刻、走法顺序或完整历史律。∎

**定理 7.3（本图的实际可行纤维识别）。** 固定 $p$ 和可见速度 $(x,z,y)$，令 $\mathcal F_p(x,z,y)$ 为定理 7.2 所列支持限制下的非负流纤维。定义

$$
\begin{aligned}
I_a&=[\max(0,x),\infty)\cap
 \begin{cases}\{0\},&p_0=0,\\\mathbb R,&p_0>0\end{cases}
 \cap\begin{cases}\{x\},&p_{13}=0,\\\mathbb R,&p_{13}>0,\end{cases}\\
I_b&=[\max(0,y),\infty)\cap
 \begin{cases}\{0\},&p_1=0,\\\mathbb R,&p_1>0\end{cases}
 \cap\begin{cases}\{y\},&p_3=0,\\\mathbb R,&p_3>0.\end{cases}
\end{aligned}
$$

纤维非空当且仅当 $z\ge0$、$p_0=0\Rightarrow z=0$ 且两个区间非空；此时

$$
\mathcal F_p(x,z,y)=\{(a,b,a-x,b-y,z):a\in I_a,b\in I_b\}.
$$

置 $\epsilon_U=\mathbf1_{p_0p_{13}>0}$、$\epsilon_V=\mathbf1_{p_1p_3>0}$。对任意线性附加读口 $R:\mathbb R^5\to\mathbb R^q$，$R$ 在这个非空纤维上单射，当且仅当只保留活动列的矩阵

$$
[\,RU\ (\epsilon_U=1),\ RV\ (\epsilon_V=1)\,]
$$

具有列秩 $\epsilon_U+\epsilon_V$。零列情形表示纤维已为单点，无需附加读口。

证明。消去 $c,d,e$ 得区间式；每个区间在对应两起点质量均正时为半直线，否则在非空前提下为单点。半直线的差集为 $\mathbb R$，单点差集为零，故

$$
\mathcal F_p-\mathcal F_p
=\operatorname{span}\{U:\epsilon_U=1;\ V:\epsilon_V=1\}.
$$

应用[《局部源分裂与读出几何》约定 10.3](AURIC_FIB_ATOM_LOCAL_SOURCE_SPLITTING_AND_READOUT_GEOMETRY.md)的实际差集判据，单射恰要求该空间与 $\ker R$ 交为零，即所述列秩。这计算了整份实际纤维，不把单个流的零边支持或环境空间的二维核替代它。∎

**命题 7.4（有限先验支持与二维开域的不同下界）。** 令未知流 $F$ 只取有限个可行值，$S_+=\{f:\Pr(F=f)>0\}$，观测为确定的精确数值 $Y=RF$。将 [Shannon 的有限熵与条件熵](../../../Library/Estimation/shannon1948communication.md)应用于这个有限载体，得到

$$
I(F;Y)=H(F)\quad\Longleftrightarrow\quad
H(F\mid Y)=0\quad\Longleftrightarrow\quad
R|_{S_+}\text{ 单射}.
$$

特别地，均匀 $p$、可见速度零时，$S_+=\{0,U,V\}$ 可由一个读口 $Rf=a+2b$ 精确区分，尽管此读口不单射于整个二维可行纤维。相反，在二维仿射开集上的线性恢复必须有秩二；一般实际集合 $C$ 的准则是 $(C-C)\cap\ker R=\{0\}$。

证明。所引有限熵恒等式中，正概率观测纤维的条件熵为零恰在其中只有一个正概率流时成立。例子的三个读数为 $0,1,2$。二维开集含任一核方向的足够小线段，故非零核必造成碰撞。有限支持没有这个开集性质。这里没有把连续变量的微分熵用于零条件熵判据；若仪器只提供带噪样本或经验均值，也没有获得这里假设的精确 $RF$。初态精确未来律与有限样本的另一区别沿用数学引文 4.2。∎

## 8. 静态载体、内嵌观察者与有类型的源摘要

**定义 8.1（显式提取模型）。** 给定集合族 $X_i$ 和一个固定对象 $\Phi\in\prod_{i\in I}X_i$。额外指定结构提取 $\mathcal G$，输出顶点、合法弧、所需边权和关系约束；指定概率提取 $\Pi_O$，输出合法五态律或下文的五态律场；指定动态数据提取，输出转移核、时钟成本及允许的记录。乘积元素本身不供应这些映射，也不自动具有线性张量空间或张量范畴结构。

内嵌观察者的数据为状态集 $H_O$、单射 $\iota_O:H_O\hookrightarrow V_{\mathcal G(\Phi)}$、允许更新关系 $U_O$ 和读口族。要求每个 $(h,h')\in U_O$ 都映为一条允许弧，读口为指定整体读口沿 $\iota_O$ 的限制；若包括概率更新，其推前须与提取的转移合同一致。区域为 $\iota_O(H_O)$。这些嵌入和相容等式是“内部”的含义，不能用没有类型的 $O\subseteq\Phi$ 替代。

完整提取固定后，$\Phi$ 给一个确定结果。比较同摘要而不同响应，所用域是声明的相容提取数据族 $\mathcal A$；它可以比较不同对象或不同提取参数，不能声称同一个完整输入经同一个函数同时给两个结果。模型只规定数学来源与读口，不附加物理时空、引力或宏观方程的实现断言。

**定义 8.2（线性回路、二项式与条件行列式）。** 将质量行加到 $A$ 得配置矩阵 $C$。沿用[《环流读出、控制接口、KL 作用量与 toric 关系》§§11–12 及 Q12–Q13](AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS.md)与 [Drton–Sullivant 的代数统计背景](../../../Library/Estimation/drtonsullivant2007algebraic.md)：$C\mathbf d=0$ 是列配置的 primitive circuit；在实多项式环间取单项式映射 $\mathbb R[z_0,z_1,z_2,z_3,z_{13}]\to\mathbb R[t,u,v,w]$

$$
(z_0,z_1,z_2,z_3,z_{13})\longmapsto(t,tu,tv,tw,tuw),
$$

则对应核理想由 $z_0z_{13}-z_1z_3$ 生成。评价 $z_s=p_s$ 得数值 $\Delta(p)$；一般概率律不要求该二项式为零。这里的整数格关系、多项式与数值函数各有自己的载体。

固定数学引文 1.3 的四格分区，$r=1-Z>0$ 时有

$$
\Delta(p)=r\kappa-XY,\qquad
\det\begin{pmatrix}p_0/r&p_3/r\\p_1/r&p_{13}/r\end{pmatrix}
=\Delta(p)/r^2=\operatorname{Cov}(U,V\mid s\ne2).
$$

$\kappa=p_{13}$ 是固定状态坐标；$\Delta$ 是相对这份四格分区和独立子模型的残差，既非截面系数，也非观察者无关的不变量。交换一行或一列会变号，更换分区会更换函数；$r=0$ 时不定义该条件表。状态空间上的 $\mathbf d$ 与边空间上的 $\mathbf c$ 通过定理 2.2 关联，而不相等。

**命题 8.3（同源摘要的钟率反例与因子化边界）。** 令源摘要为 $S_O=(\Delta(p),\mathcal H_\ell)$，其中 $\mathcal H_\ell=\ell_1+\ell_2+\ell_3+\ell_4$ 是方形一周的成本。对定理 3.2 的均匀平稳律，取五条合法边成本全为一，并分别取 $\gamma=1,2$。两份有限率模型同有

$$
S_O=(0,4),\qquad ABf=Bf=0,
$$

但 $d\mathbb E J_t/dt$ 分别为 $4,8$。因此即使另给完整 $p$，此源摘要仍不决定该钟率。

在任一声明的相容域 $\mathcal A$ 上，响应 $\Gamma:\mathcal A\to\mathcal Y$ 能写成 $\bar\Gamma\circ S_O$，当且仅当

$$
S_O(a)=S_O(a')\Longrightarrow\Gamma(a)=\Gamma(a')
\quad(a,a'\in\mathcal A).
$$

该判据只在像 $S_O(\mathcal A)$ 上要求定义 $\bar\Gamma$；其他外参若未固定，必须进入摘要或进入同纤维条件。

证明。钟率数值直接消费定理 3.2 的 $\gamma\mathcal H_\ell$，没有重新构造平稳过程。因子化的必要性由函数保持相等；充分性是在每个非空摘要纤维上取其共同响应值，条件保证良定义。反例两元素属于同纤维而钟率不同，故否定该域上的因子化。$\mathcal H_\ell$ 是每圈成本，$\gamma$ 是每单位指定参数的概率环流；两者不能互相替代。∎

**定义 8.4（几何与商的附加合同）。** 对有限提取图，给嵌入读口 $r:V\to\mathbb R^3$ 后，“仿射维数三”指差向量 $r(v)-r(v_0)$ 的张成秩三。有限顶点集没有由此自动产生的微分秩；微分秩三另要求光滑域及可微映射。五态坐标按[《金字塔关联与原生接续》定义 1.1](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)为 $(x,y,z)$，其均值 $(X,Y,Z)$ 与本卷 $A(p)=(X,Z,Y)$ 相差第二、三坐标置换。

给非负合法弧长度后，最短有向路长为扩展有向距离，不可达取 $+\infty$；它满足三角不等式，未必对称。有限连通无向图的对称严格正长度给距离；允许零长度时一般只给伪距离。若按 $v\sim v'$ 作商，公式 $\bar d([u],[v])=d(u,v)$ 要求 $d$ 在两端等价类上恒定；伪距离的零距离类满足此要求。三个任意坐标并不保证图距离如此下降。两观察几何的等价要求明确的双射保持所指定的邻接、长度或距离，坐标值不同本身不判定等价与否。

## 9. 空支持、势源与同参数储存平衡

**定义 9.1（零、单位和根的不同操作）。** 空支持、$W(0)=0$ 及计数空间的零向量互不等同。空列表是自由列表连接的单位，但固定三位置合法支持不对任意连接封闭。若选部分运算为不相交且并集合法时的支持并，空支持是此部分运算的单位；这些操作须先指定。标量 $0$ 是加法单位，不能由此推出任意载体上的乘法单位或恒等算子。

定义 5.1 的全添加定向以空支持为唯一入度零且可达所有顶点的根；定义 2.1 的方形定向则有 $3\to0$，所以 $0$ 不是入度零根。这沿用命题 5.3 的定向区分。[《金字塔边界演算》§§0.1–1.3](AURIC_FIB_ATOM_PYRAMID_BOUNDARY_CALCULUS.md)的外部空窗口贡献不改变原生树至少含一个叶子的语法；[《二阶关系完成》§§87.3、95.2](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)中的角色零与矩阵单位也不提供空树构造子。

**假设 9.2（对称电导、符号与区域）。** 取有限无向图的参考定向，$B$ 仍为终点减起点。每条边有对称非负电导 $k_e$，$K_E=\operatorname{diag}(k_e)$，$L=BK_EB^{\mathsf T}$；连通性一律指严格正电导边组成的图。给势 $\varphi$，定义下坡有符号电流和向外散度

$$
j=-K_EB^{\mathsf T}\varphi,\qquad
\operatorname{div}_{\rm out}j=-Bj=L\varphi=s.
$$

$s_v>0$ 表示净向外电流，若储存平稳，需要等量外加供给。经典 Laplacian 的核、像及能量公式取自 [von Luxburg，§§2.1、3.1，命题 1–2](../../../Library/Geometry/vonluxburg2007spectralclustering.md)；电流与循环的背景见 [Schnakenberg，§§VIII–IX](../../../Library/Dynamics/schnakenberg1976network.md)。因此 $s=L\varphi$ 在每个正电导连通分量上总和零，反之该条件给解，势在各分量相差常数。

对观察区域 $R\subseteq V$，定义 $\operatorname{Cut}_Rj$ 为穿出 $R$ 的参考边电流减穿入的参考边电流。它允许电流为负，并满足 $\sum_{v\in R}s_v=\operatorname{Cut}_Rj$。区域内可以只有一个非零正源，其补偿位于区域外；有限闭图总和零只约束此模型的向量源，不是关于物理孤立引力源的陈述。

**命题 9.3（五边图的势流障碍与摘要不充分）。** 将定义 2.1 的五条边改作无向正电导边，但保持原参考定向。一个下坡电流若还要求在原五条单向合法弧上全部非负，则四条方形电流全为零，且 $\varphi_0\ge\varphi_2$；反之，方形四顶点等势及这个不等式给这样的电流。若再要求 $Bj=0$，则全部电流为零。

单位电导下取 $\varphi=\mathbf e_0$，有

$$
j=(1,0,0,-1,1),\qquad s=(3,-1,-1,-1,0).
$$

特别地，令 $p=(9/16,3/16,0,3/16,1/16)$、时钟余链为零，分别取势 $0$ 和 $\mathbf e_0$。两组数据同有 $(\Delta,\mathcal H)=(0,0)$，却有不同节点源。因此没有额外 constitutive law 时，两个标量不决定节点源向量。

证明。沿方形求和，$\sum_{i=1}^4j_i/k_i=-\sum_{i=1}^4(B^{\mathsf T}\varphi)_i=0$；非负项只能全零，故四顶点等势。叶边电流为 $k_5(\varphi_0-\varphi_2)$。平稳时状态 $2$ 的流入必须零，叶边亦零。实例逐边势差给 $j$，再由 $-Bj$ 得 $s$；第四边电流负，说明它不是原单向图的合法概率流。概率表的两乘积均为 $9/256$，时钟摘要均零，而 $L0=0$。在 $R=\{0\}$，三个净向外单位电流恰平衡 $s_0=3$；区域外的三个 $-1$ 不消失。∎

**命题 9.4（共同参数的局部储存与切口）。** 在同一有限图上，另给可微的可加储存密度 $\rho_v(t)$、有符号电流 $j_e(t)$ 和外加源 $\eta_v(t)$，共同参数为 $t$，规定

$$
\dot\rho=Bj+\eta.
$$

则 $d\sum_{v\in R}\rho_v/dt+\operatorname{Cut}_Rj=\sum_{v\in R}\eta_v$。本五态图上，取 $j=0$、$\eta=\mathbf e_0-\mathbf e_1$、$\rho(t)=\bar p+t(\mathbf e_0-\mathbf e_1)$，$|t|<1/5$，得到总量不变且区域 $\{0\}$ 的正源完全增加局部储存、切流恒零的实例。

证明。对区域求和时内部边两端抵消，只留下负的向外切流，给第一式。实例密度各项非负，导数等于 $\eta$，总源零。故局部正源不强迫同一时刻存在向外切流；只有零储存导数时才有这种等量关系。若每个顶点另用 $\tau_v(t)$，转换须为 $\dot\rho_v=(d\rho_v/d\tau_v)\dot\tau_v$，并将边流也换成每单位同一个 $t$ 的量，不能直接相加不同 $\tau_v$ 的导数。这里的 $\rho$ 是指定可加量；一般联合 Shannon 熵不等于各顶点边缘熵之和，不承担此连续性方程。∎

## 10. 合法路径钟与指定 seam 响应

**假设 10.1（离散累计与连续参数的分工）。** 路径钟取定义 3.1 的正向成本合同。若将边值解释为有符号余链，必须使用数学引文 3.4 的形式反向及全部底层有符号循环；只检查一个弱连通有向图的有向闭走法不足以援用该判据。严格正的实际反向成本是另一数据，不能等于形式反向的负值。非恰当性只排除状态势，不排除额外的共同参数。

离散路径上的共同边钟比为 $\ell^{(1)}_e/\ell^{(2)}_e$，须分母正。对连续模型，另给 $C^1$ 钟函数 $\tau_i(t)$、$\dot\tau_2>0$ 及 $C^1$ 重参数 $u=f(t)$、$f'(t)>0$；链式法则给两导数之比均为 $\dot\tau_1/\dot\tau_2$。这个规则不适用于任意严格递增但不具上述正导数条件的函数，也不把跳跃累计路径自动变成可微曲线。

**命题 10.2（同一固定边界上的合法 seam 钟律）。** 固定 $(X,Z,Y)=(2/5,1/5,2/5)$，取 $0<\kappa<2/5$，$\gamma>0$，并声明

$$
p_\kappa=(\kappa,2/5-\kappa,1/5,2/5-\kappa,\kappa),
\quad f=\gamma\mathbf c,\quad
q_{i\to j}=\gamma/p_{\kappa,i}\quad(e_1,\ldots,e_4),\quad q_{02}=0.
$$

另指定 $\ell_1(\kappa)=1+\kappa$，其余四条成本为一。每个参数给有限率平稳模型，并有

$$
\mathcal H(\kappa)=4+\kappa,\qquad
\frac{d}{dt}\mathbb E J_t=\gamma(4+\kappa),\qquad
\frac{\sum_e f_e\ell_e}{\sum_e f_e}=(4+\kappa)/4.
$$

因此已知 $\gamma$ 时，精确累计钟率在整个可行开区间上单射，局部导数为 $\gamma$，任意不同参数对都被区分；按总体跳跃强度加权的每跳平均成本则是第三式，不能遗漏跳跃强度 $4\gamma$ 而当作第二式。

证明。所有方形起点质量正，率有限；$p_iq_{ij}=\gamma$，所以 $Bf=0$，有限状态常率过程保持 $p_\kappa$。消费定义 2.3、定理 3.2 的流—累计成本关系即可得到三式，差为 $\gamma(\kappa'-\kappa)$。此族显式改变成本和生成器，是一个已指定的参数族，不是数学引文 4.2 中固定核只改变初态的合同。未知 $\gamma$ 时 $\gamma(4+\kappa)$ 可碰撞。成本对 $\kappa$ 的依赖也是提取模型的假设，不由五模式语法或 $\Delta$ 自动推出。∎

**命题 10.3（同一底层图上的有向闭走法盲点）。** 将方形改取全添加方向 $0\to1\to13$、$0\to3\to13$，叶边仍为 $0\to2$。各弧成本为一，唯 $3\to13$ 为二。没有非空有向闭走法，因而有向闭走法的零和条件真空成立，但不存在状态势给出这些增量。

证明。命题 5.3 的支持大小沿每弧增加，故没有有向闭走法。两条从 $0$ 到 $13$ 的路成本分别为二和三；若为同一势增量，两者必须相等。底层有符号方形用第二条路的形式反向，积分为 $2-3=-1$，正被数学引文 3.4 的完整判据检出。∎

## 11. 中心化图钟响应的精确 seam 纤维

**假设 11.1（图站点上的五态律场）。** 固定 $n\ge1$ 个站点组成的有限连通对称正电导图，Laplacian 为 $L$。每个站点 $v$ 另有一个局部五态律 $p^v$；这是 $n$ 份律的场，不是把一个概率律当作图上密度。固定合法边界 $b_v=(X_v,Z_v,Y_v)$，取数学引文 1.2 的区间 $\kappa_v\in[l_v,u_v]$。提取这些边界、图和观察者嵌入均属于定义 8.1 的数据。

令 $C=I-\mathbf1\mathbf1^{\mathsf T}/n$，令 $K=L^\dagger$ 为在 $\mathbf1^\perp$ 上的逆、在常数上为零。所引 [von Luxburg 的 Laplacian 核及逆](../../../Library/Geometry/vonluxburg2007spectralclustering.md)给 $LK=KL=C$。取实系数 $a,b$，$b\ne0$，以及 $\alpha,r_0>0$，指定

$$
\begin{aligned}
\rho_v&=a\mathbb E_{p^v}W+b\mathbb E_{p^v}W^2=g_v+20b\kappa_v,\\
g_v&=a(2X_v+3Z_v+5Y_v)+b(4X_v+9Z_v+25Y_v),\\
\varphi&=KC\rho,\qquad r_v=r_0e^{-\alpha\varphi_v}.
\end{aligned}
$$

势取零均值规范。$r_v$ 是规定的正钟读数；若要认作路径每单位参数的累计率，还须另供如命题 10.2 的实现。加常数规范将全部 $r_v$ 乘同一因子，所有比值不变。

**定理 11.2（全部钟比的实际纤维及单锚恢复）。** 对任何合法扰动 $t$，即 $\kappa+t\in\prod_v[l_v,u_v]$，有精确式

$$
\log\frac{r'_v/r'_u}{r_v/r_u}
=-20\alpha b(e_v-e_u)^{\mathsf T}Kt.
$$

所有钟比保持不变当且仅当 $t$ 是空间常数。因此通过 $\kappa$ 的实际响应纤维恰为

$$
\left\{\kappa+c\mathbf1:
\max_v(l_v-\kappa_v)\le c\le\min_v(u_v-\kappa_v)\right\}.
$$

它可在边界退化为一点；若所有 seam 均为区间内点，则含非零常数扰动。一个已知站点 seam 值与全部比值共同唯一恢复整个场。等价恢复公式为

$$
C\kappa=-\frac1{20\alpha b}L\log r-\frac1{20b}Cg.
$$

证明。数学引文 1.4 在每个站点给 $\rho'-\rho=20bt$，故 $\varphi'-\varphi=20bKt$。取对数得到首式。全部差向量湮灭该势差恰要求势差为常数；其均值零，故它为零。施 $L$ 得 $Ct=0$，反向由 $K\mathbf1=0$ 成立。将常数扰动逐坐标同合法区间相交即得精确纤维，不需要将环境空间秩误作每个实际纤维维数。一个锚令 $c=0$。最后对 $\log r=(\log r_0)\mathbf1-\alpha\varphi$ 施 $L$ 得恢复公式；任意代表全部比值的 $\log r$ 相差常数，右侧相同。∎

**命题 11.3（五边图上的局部变化与常数变化）。** 在命题 9.3 的单位电导无向图上，把五个顶点视为五个站点，在每站放置均匀五态律。此时每站 $\kappa_v=1/5$、$[l_v,u_v]=[0,2/5]$。令 $a=0,b=1$，仅将站点 $2$ 的 seam 增加 $1/20$，则

$$
\Delta\rho=\mathbf e_2,\qquad
\Delta\varphi=(1/25,-13/50,21/25,-13/50,-9/25),\qquad
\Delta\log(r_2/r_0)=-4\alpha/5.
$$

若每站 seam 都增加 $1/20$，则密度各增一而所有响应不变。均匀场的整个同钟比纤维为 $\kappa+c\mathbf1$、$-1/5\le c\le1/5$。

证明。两种扰动均留在所列合法区间。对首式所列势向量求和为零，乘 $L$ 得 $\mathbf e_2-\mathbf1/5$，故是唯一零均值解；站点 $2$ 与 $0$ 的势差为 $4/5$。常数扰动及完整区间直接消费定理 11.2。∎

**命题 11.4（分量、单个钟比与一般源函数）。** 若正电导图不连通，则以各分量均值构成 $C$、每分量零均值构成 $K$，同一证明给：全部分量内钟比相等恰在源差于各分量为常数。在线性 seam 模型中，各分量可各有一个合法常数偏移，每分量一个锚消除此歧义。若只读取一个钟比，条件仅为 $(e_v-e_u)^{\mathsf T}Kt=0$，不能替代全部比值。对任意指定非线性源函数 $\rho(\kappa)$，全部分量内钟比相等的精确条件仍是 $C(\rho(\kappa')-\rho(\kappa))=0$。

证明。各正电导分量是 $L$ 的独立块，经典核结论给块常数核。取对数、施 $L$ 的推导逐块成立；一个比值只给一条线性等式。一般源差替换 $20bt$ 后其余推导不变。全空间秩 $n-1$ 仅属于假设 11.1 的连通仿射场，不是有限支持信息恢复的必要维数。∎

## 12. 源敏感性、熵碰撞与完整边界变量

**定义 12.1（实际区间上的三种敏感性）。** 固定一个边界，令 $m_1=2X+3Z+5Y$、$m_{20}=4X+9Z+25Y$。对规定的源函数 $G$，实际函数为 $\psi(\kappa)=G(m_1,m_{20}+20\kappa)$，定义域必须是实际 seam 集合。指定参数对被区分指 $\psi(\kappa)\ne\psi(\kappa')$；可微内点的一阶敏感性指 $\psi'(\kappa)\ne0$；全部恢复指 $\psi$ 在实际集合上单射。可微时 $\psi'=20\partial_2G$。全实域上对第二变量非恒定，不保证实际区间上非恒定；区间上非恒定也不保证每一对被区分。固定核的未来律读口使用数学引文 4.2 的 $R_w(\mathbf d)$ 判据，不用任意非线性 $G$ 的一次方向评价替代。

**命题 12.2（熵相等的 seam 与复合源抵消）。** 本节熵用自然对数及 $0\log0=0$。对命题 10.2 的 $p_\kappa$，$p_\kappa$ 与 $p_{2/5-\kappa}$ 只是四个底面质量的置换。因此它们熵相等；例如 $\kappa=3/20,1/4$ 给不同律、相同边界与熵，而二阶矩相差 $2$。故纯熵源可在进入 Laplacian 以前即发生碰撞。

对 $\rho=a m_1+b\mathbb EW^2+\eta H(p)$，即使 $b\ne0$，也没有任意 $\eta$ 下的无抵消保证。在两点 $\kappa\ne\kappa'$ 熵不同时，取

$$
\eta=-\frac{20b(\kappa'-\kappa)}{H(p_{\kappa'})-H(p_\kappa)}
$$

使两点源相等。这样的点存在，例如 $\kappa=1/10,\kappa'=1/5$。

证明。$p_\kappa=(\kappa,2/5-\kappa,1/5,2/5-\kappa,\kappa)$，参数反射交换两对质量，熵的置换不变性来自 [Shannon §6](../../../Library/Estimation/shannon1948communication.md)。二阶矩差由数学引文 1.4 给 $20(1/4-3/20)=2$。沿区间内部

$$
\frac{d}{d\kappa}H(p_\kappa)=2\log\frac{2/5-\kappa}{\kappa},
$$

故熵从 $1/10$ 到 $1/5$ 严格增加，所列分母非零，代入即抵消。对于可微复合源，其导数为 $20b+\eta H'(p_\kappa)$，也可能在某点为零；一阶导数为零不推出整个函数恒定。∎

**假设 12.3（概率集合、实际边界与参考信息）。** 另供有限微观集合 $\mathcal Z$ 上的概率律 $\mu$，以 $Z_*$ 表示随机微观对象。一个固定静态对象若只配 Dirac 律，其 Shannon 熵为零；非零熵需要另供 $\mu$ 或定义 8.1 的概率提取合同。实际边界变量为函数 $B_*=b(Z_*)$，内部变量为 $I_*=i(Z_*)$。只有 $(b,i)$ 在正概率支持上单射时，Shannon 的链式恒等式才在完整表示上给

$$
H(Z_*)=H(B_*,I_*)=H(B_*)+H(I_*\mid B_*).
$$

若整体更新是该微观集合的双射，沿用该经典置换不变性，完整熵保持；局部边缘熵与条件熵可变化。这不声称 $H(B_*)$ 是对某个固定参考的可恢复信息。另给参考变量 $R_*$ 后，恢复由 $H(R_*\mid B_*)$ 或 $I(R_*;B_*)$ 判定，且确定粗粒化 $Y=f(B_*)$ 满足数据处理界 $I(R_*;Y)\le I(R_*;B_*)$。

在本五态模型中，$(X,Y,Z)$ 是一份律的期望参数，通常不是微观抽样上逐次取得的边界变量。若实际读取纯模式的 $(x,y,z)$，五点坐标反而单射地标识全部五模式。因而不能把期望投影的 seam 直接放入 $H(I_*\mid B_*)$，除非另给随机“律的参数”或相应边界观测实验。上述信息论工具的归属为 [Shannon 的有限链式规则](../../../Library/Estimation/shannon1948communication.md)及[基础金字塔卷 §9](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)；它们不是可加物质密度、衰变定律或物理信息守恒公理。

## 13. 窗口维数、有限观察与控制的对应域

**定义 13.1（长窗口的指定图与任务）。** 若采用定义 5.1 的独立支持切换图，长窗口数据明确为 $V_n=F_{n+2}$、$E_n=\sum_k k\binom{n-k+1}{k}$，有符号循环维数为定理 5.2 的 $c_n=E_n-V_n+1$。若采用连续 $n$ 个三位置原生窗口，则[《金字塔关联与原生接续》§§8、13–18](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)的对象是合法词及其共同律；词数、合法相邻表、运输图、切换图各有自己的顶点和边。未给图与边界映射时，单独一列词数不定义循环维数。

有限任务的充分观察者须保留一个实际可更新的历史商：等价历史给同样合法动作与完整后续记录律，更新保持等价关系，且相应等价类在该任务域上有限。可取得性及费用须另供。[《稀疏字面历史运输》§§3–4](RECURSIVE_RELATIONAL_OBSERVATION_SPARSE_LITERAL_HISTORY_TRANSPORT.md)的有限共同像保留原来源的字面访问合同；[《成对校准可观察性》§11、§13.5](RECURSIVE_RELATIONAL_OBSERVATION_PAIRED_CALIBRATION_OBSERVABILITY.md)的紧完整律空间及有限再生具有另一合同，不自动保存给定三时刻耦合。有限图、紧参数空间或有限个均值均不单独保证有限状态的完整未来商。

**假设 13.2（控制秩的线性范围）。** 在定理 7.3 的非空纤维内，以活动的 $U,V$ 列组成 $D$，选一个相对内点 $f_*$，合法控制写成 $f_*+Du$，$u$ 留在真实区间。读口缺陷的变化恰为 $RDu$，故可精确消除的给定缺陷 $h$ 满足 $-h\in RD(\text{合法参数域})$。在相对内点的小邻域里，要覆盖一个声明的线性缺陷空间 $W$ 的全部小扰动，条件为 $W\subseteq\operatorname{im}(RD)$；有多少控制参数只是此条件的秩下界，不能替代非负可行性。此处消费[《环流读出、控制接口、KL 作用量与 toric 关系》§4 及 Q2、Q3、Q7、Q14](AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS.md)的线性／局部控制范围。一般非线性全局控制不由该秩句认证；单点消缺陷也不要求覆盖整个 $W$。

## 追加锚（本行以下为增补区）

## 14. 加权 seam 提升、梯度钟比与有向交通障碍

**定义 14.1（余链、电流与所配源的类型）。** 在假设 9.2 的参考定向图上，只保留正电导边，取顶点质量矩阵 $M_V=\operatorname{diag}(m_v)$、$m_v>0$ 和电导矩阵 $W_E=\operatorname{diag}(w_e)$、$w_e>0$。顶点内积为 $u^{\mathsf T}M_Vv$，边余链内积为 $a^{\mathsf T}W_Eb$。记 $\delta_0=B^{\mathsf T}$，则

$$
\delta_0^*=M_V^{-1}BW_E,\qquad
L_M=\delta_0^*\delta_0=M_V^{-1}BW_EB^{\mathsf T}.
$$

这里 $\delta_0$ 是算子，状态 seam 向量仍写 $\mathbf d$。余链 $a$ 在形式反向上变号；电流 $j=W_Ea$ 使用内积 $j^{\mathsf T}W_E^{-1}k$。向内散度为 $M_V^{-1}Bj$，向外散度为其负数。因此对下坡余链 $a_\varphi=-B^{\mathsf T}\varphi$ 及电流 $j_\varphi=W_Ea_\varphi$，

$$
\delta_0^*a_\varphi=-L_M\varphi=\sigma_{\rm in},\qquad
\operatorname{div}_{\rm out}j_\varphi=L_M\varphi=-\sigma_{\rm in}.
$$

在 $M_V=I$ 时，假设 9.2 的 $s$ 等于 $-\sigma_{\rm in}$。方程 $-L_M\varphi=\sigma_{\rm in}$ 的相容条件是每个正电导分量上 $\sum_vm_v\sigma_{{\rm in},v}=0$；源取密度减去分量的 $m_v$ 加权均值时满足此条件。势的常数规范和解的存在沿用 [von Luxburg 的核结论](../../../Library/Geometry/vonluxburg2007spectralclustering.md)，对该方程先左乘 $M_V$ 即可。正负源的名称取决于所声明的散度，不赋予作用力方向。

[加权 Hodge 分解，Jiang–Lim–Yao–Ye，定义 4.2–4.3、定理 4.7、5.1](../../../Library/Geometry/jianglimyaoye2011hodge.md)在没有二维胞腔的图上提供中间工具

$$
a=B^{\mathsf T}\psi+h,\quad BW_Eh=0,
\qquad
j=W_EB^{\mathsf T}\psi+k,\quad Bk=0.
$$

两式分别在 $W_E$ 与 $W_E^{-1}$ 内积下正交，$k=W_Eh$；一般不能把 $h$ 当作 $\ker B$ 中的电流。若势 $\varphi$ 已由另一份密度指定，则 $j-j_\varphi$ 是循环的充要条件为 $Bj=M_V\sigma_{\rm in}$，因为 $B(j-j_\varphi)=Bj-M_V\sigma_{\rm in}$。即使底层是树，也只有边界匹配时任意给定场才等于这份指定梯度。密度读口及其 seam 敏感性采用假设 11.1、定理 11.2 和命题 12.2 的合同；中心化及熵碰撞仍保留。观察误差需要另给观察空间、映射和误差数据，例如 $y=Ra+\varepsilon$，并指定该空间的范数；上述正交分解不自动产生第三个“观察误差”项。非负合法交通则另要求 $j_e\ge0$ 及定义 2.3 的概率实现条件。

**定理 14.2（五边图的加权最小能量提升及钟比障碍）。** 在定义 2.1 的五边图上取 $M_V=I$，令

$$
r_i=1/w_i,\qquad P=r_1+r_3,\quad Q=r_2+r_4,\quad R=P+Q.
$$

固定边界概率曲线的一个可行导数为 $\dot p=v\mathbf d$，其中 $v=\dot\kappa\in\mathbb R$。则全部有符号提升为

$$
Bj=v\mathbf d\quad\Longleftrightarrow\quad
j=j_0+\gamma\mathbf c,\qquad
j_0=\frac vR(-Q,P,-Q,P,0),\quad \gamma\in\mathbb R.
$$

其规范循环系数、能量及非负条件为

$$
\begin{aligned}
\gamma&=\frac{\mathbf c^{\mathsf T}W_E^{-1}j}{R},\qquad
\mathbf c^{\mathsf T}W_E^{-1}j_0=0,\\
\|j\|_{W_E^{-1}}^2&=v^2\frac{PQ}{R}+\gamma^2R,\\
j\ge0&\quad\Longleftrightarrow\quad
\gamma\ge\max\left(\frac{vQ}{R},-\frac{vP}{R}\right).
\end{aligned}
$$

因此 $j_0$ 是唯一的最小能量有符号提升；非负提升的最小能量在 $v\ge0$ 时为 $v^2Q$，在 $v\le0$ 时为 $v^2P$。若 $v\ne0$，每个非负提升的循环系数严格为正。单位电导下

$$
j_0=\frac v2(-1,1,-1,1,0),\qquad
\psi=v(1/5,-3/10,1/5,-3/10,1/5),\qquad j_0=B^{\mathsf T}\psi,
$$

且有符号与非负最小能量分别是 $v^2$、$2v^2$。

一般正电导下存在势 $\psi$ 使 $j_0=W_EB^{\mathsf T}\psi$，唯一到加常数。取 $\varphi=-\psi$、$\alpha,N_{\rm ref}>0$，并声明节点钟率 $N_s=N_{\rm ref}e^{-\alpha\varphi_s}$，则

$$
-BW_EB^{\mathsf T}\varphi=v\mathbf d,\qquad
\log\frac{N_{\operatorname{head}(e)}}{N_{\operatorname{tail}(e)}}
=\alpha(W_E^{-1}j_0)_e.
$$

完整电流的电阻加权余链 $a=W_E^{-1}j$ 则满足

$$
\langle a,\mathbf c\rangle=\gamma R.
$$

当 $v\ne0$ 且 $j\ge0$ 时，它不能表示成任何标量节点函数的增量，特别不能表示成同校准节点钟率的对数比。这里的余链—循环配对是标量，$\gamma$ 是所选加权截面的循环系数；二者均不等同于状态坐标 $\kappa$。

证明。定理 2.2 已给 $Bj=v\mathbf d$ 的全部解 $(a,a+v,a,a+v,0)$。电阻加权循环正交条件为 $aP+(a+v)Q=0$，所以 $a=-vQ/R$，得 $j_0$。余下解与它相差 $\gamma\mathbf c$；内积展开给能量式，其中 $\|j_0\|_{W_E^{-1}}^2=v^2PQ/R$、$\|\mathbf c\|_{W_E^{-1}}^2=R$。严格凸二次式给唯一最小值。四个坐标的非负性恰给所列下界；该下界非负，代入能量即得两种符号下的尖锐最小值。单位电导的势逐边差为 $j_0$ 且均值零。

一般情形下 $W_E^{-1}j_0$ 湮灭 $\mathbf c$，故由数学引文 3.4 取得 $\psi$。取对数得到钟比，沿循环和为零；完整余链的循环配对是 $\gamma R$，用同一恰当性判据得到障碍。若导数被另解释为密度源，这是新指定的对应 $\sigma_{\rm in}=v\mathbf d$。上述提升首先是瞬时向量；若概率曲线为 $C^1$、四个方形起点质量在紧区间上严格正，且所选非负交通连续有界，则定理 2.4 的有限率构造适用，叶边率取零；零质量起点仍受定理 7.2 限制。它不恢复单条路径或赋予概率纤维外的导数可行性。∎

**定义 14.3（长度积分、路径阶数与光滑钟参数）。** 给每条保留边长度 $\ell_e>0$，记 $D_\ell=\operatorname{diag}(\ell_e)$；这些长度是另给数据，不与定义 3.1 的钟成本自动相同。长度梯度为 $G=D_\ell^{-1}B^{\mathsf T}$；边内积改用 $D_\ell W_ED_\ell$ 时，其伴随及 Laplacian 为

$$
G^*=M_V^{-1}BW_ED_\ell,\qquad G^*G=L_M.
$$

对 $g=-G\varphi$，电流为 $j=W_ED_\ell g$，向内散度为 $G^*g=-L_M\varphi$。沿有符号边链 $z$ 积分使用 $z^{\mathsf T}D_\ell g$，不是 $z^{\mathsf T}g$。定理 14.2 的指数钟满足

$$
\log(N_{\operatorname{head}(e)}/N_{\operatorname{tail}(e)})
=\alpha\ell_eg_e.
$$

这是同一正校准 $N_{\rm ref}$ 下的公式；改变势的常数只共同缩放钟率，若同时调整 $N_{\rm ref}$ 则可保持各率。任意逐节点独立校准会添加自己的对数差，不能省略。非负路径成本使用定义 3.1、假设 10.1，不同于这些可正可负的对数增量。

图的 coboundary 采用所引 Hodge 文献引理 4.4：一维图的二阶余链空间为零；即使另填二维胞腔，仍有 $\delta_1\delta_0=0$。这不是 Hessian。对路径上三次采样 $u,v,w$，若参数步长为 $h_-,h_+>0$，规定二阶除差为

$$
\mathcal D^2\varphi(u,v,w)=\frac{2}{h_-+h_+}
\left(\frac{\varphi(w)-\varphi(v)}{h_+}-\frac{\varphi(v)-\varphi(u)}{h_-}\right).
$$

相同步长 $h$ 才化为 $(\varphi(w)-2\varphi(v)+\varphi(u))/h^2$。例如沿本图 $0\to1\to13$ 取参数 $0,1,3$ 及同值的势，原始二次差为一，而所规定除差为零。该算子依赖路径和步长，不由顶点邻接独自定义 Hessian 或曲率。

若另给光滑流形及联络 $\nabla$、$C^2$ 函数 $\varphi$ 和 $C^2$ 路径 $\eta(\lambda)$，Hessian 指 $\nabla d\varphi$。另给沿路径的 $C^1$ 函数 $N(\lambda)>0$，令 $d\tau=N\,d\lambda$，普通链式法则在此合同下给

$$
\begin{aligned}
D_\tau(\varphi\circ\eta)&=N^{-1}d\varphi(\dot\eta),\\
D_\tau^2(\varphi\circ\eta)&=N^{-2}\left[
(\nabla d\varphi)(\dot\eta,\dot\eta)
+d\varphi(\nabla_{\dot\eta}\dot\eta)
-\frac{d\log N}{d\lambda}d\varphi(\dot\eta)\right],\\
\frac{d^2\tau}{d\lambda^2}&=\frac{dN}{d\lambda}.
\end{aligned}
$$

第二式直接将 $N^{-1}d/d\lambda$ 作用于第一式；不将外微分 $d(d\varphi)=0$ 换成 $\nabla d\varphi$。若取 $N=N_{\rm ref}e^{-\alpha\varphi\circ\eta}$ 且 $N_{\rm ref}$ 恒定，最后一式成为 $-\alpha N\,d(\varphi\circ\eta)/d\lambda$。只有模型让 $N$ 自由时，才允许同势而任意比较 $N$ 与 $2N$；固定构成律与校准后不再有这种自由。图、长度、概率矩及 KL 对 $\kappa$ 的导数均不供应该光滑几何，也不把这些参数导数识别成几何曲率。

## 15. 非线性 KL 下降的五边实现与活动自由度

**假设 15.1（严格内部、迁移率与共同钟）。** 固定合法边界，令 $r=1-Z>0$、$0<X,Y<r$，取

$$
I=(\max(0,X+Y-r),\min(X,Y)),\qquad
\kappa_0=XY/r,\qquad \kappa_{\rm init}\in I.
$$

采用数学引文 1.2 的 $p_\kappa$ 及[《环流读出、控制接口、KL 作用量与 toric 关系》Q4–Q5、定理 3.1–3.2](AURIC_FIB_ATOM_CIRCULATION_CONTROL_KL_ACTION_AND_TORIC_RELATIONS.md)的共同支持 KL 量 $\mathcal A(\kappa)=D(p_\kappa\Vert p_{\kappa_0})$。所引结论为四格内部的

$$
\mathcal A'(\kappa)=\log\frac{p_0p_{13}}{p_1p_3},\qquad
\mathcal A''(\kappa)=\frac1{p_0}+\frac1{p_1}+\frac1{p_3}+\frac1{p_{13}}>0.
$$

四个变动格严格正；固定格 $p_2=Z$ 可为零，零格对 KL 的贡献按共同支持取零。退化纤维或端点不沿用这些有限导数。此统计凸性和数学引文 1.4 的二阶矩均不等于路径的二阶参数导数。

在 $I$ 上另给正 $C^1$ 函数 $\mu,N$，规定

$$
\frac{d\kappa}{d\lambda}=-\mu(\kappa)\mathcal A'(\kappa),\qquad
\kappa(0)=\kappa_{\rm init},\qquad
\tau(\lambda)=\int_0^\lambda N(\kappa(u))\,du.
$$

$\mu$ 是所选迁移率，$N$ 是整条律轨迹共用的确定钟率，尚未指定成样本状态依赖的随机换钟。再给非负连续函数 $\beta(\lambda)$，在每个有限区间有界。它指定在必需交通之外添加多少循环，不能由 KL 曲率决定。

**定理 15.2（下降律的全部非负交通及尖锐钟活动）。** 假设 15.1 的解对全部 $\lambda\ge0$ 存在，留在 $\kappa_{\rm init}$ 与 $\kappa_0$ 之间的闭线段，并趋于 $\kappa_0$。令

$$
s=-\mu(\kappa)\mathcal A'(\kappa),\qquad
s_+=\max(s,0),\quad s_-=\max(-s,0).
$$

在本五边图上，全部满足 $Bf=s\mathbf d$ 的非负交通恰为

$$
f=(s_-,s_+,s_-,s_+,0)+\beta\mathbf c,\qquad \beta\ge0.
$$

以此给定的 $\beta(\lambda)$、方形边率 $q_{ij}=f_{ij}/p_i$、叶边率零及负行和对角项，得到每个有限区间上非爆炸的有限状态非齐次 Markov 实现，其边缘律为 $p_{\kappa(\lambda)}$。对实际每次跳跃成本一的累计计数 $J$，

$$
\begin{aligned}
\frac{d\mathbb EJ}{d\lambda}&=2\mu|\mathcal A'|+4\beta,&
\frac{d\mathcal A}{d\lambda}&=-\mu(\mathcal A')^2,\\
\frac{d\mathbb EJ}{d\tau}&=\frac{2\mu|\mathcal A'|+4\beta}{N},&
\frac{d\mathcal A}{d\tau}&=-\frac\mu N(\mathcal A')^2.
\end{aligned}
$$

其中 $J$ 在第二行按共同参数逆函数重参数。最小期望跳跃活动由 $\beta=0$ 达到，且

$$
a_{\min}=\frac{2\mu|\mathcal A'|}{N},\qquad
a_{\min}^2=4\frac\mu N\left(-\frac{d\mathcal A}{d\tau}\right).
$$

这个最小交通亦为定理 14.2 在任意正电导下的非负最小能量提升。一般交通 $f$ 的规范系数为 $\gamma=\beta+\max(sQ/R,-sP/R)$，所以 $\beta$ 与加权正交分解的 $\gamma$ 是两个不同的坐标。在平衡处，$\beta>0$ 仍可累积跳跃钟；此时的自由度正是定理 3.2、命题 3.3 的平稳循环机制。

证明。所引 KL 严格凸性给 $\mathcal A'(\kappa_0)=0$，漂移在该点左边为正、右边为负。$C^1$ 漂移的唯一性使初态和平衡之间的闭线段正向不变；该线段紧含于 $I$，因此漂移有界，解不能在有限参数处终止。解单调且有界；若极限异于 $\kappa_0$，正迁移率和非零连续漂移在极限附近有严格的单向下界，与收敛矛盾。线段上 $N$ 亦有正下界和有限上界，故 $\tau$ 是到 $[0,\infty)$ 的正则递增换元。

由定理 2.2 的全部提升，$f=(a,a+s,a,a+s,0)$；非负性等价于 $a=s_-+\beta$、$\beta\ge0$。四个方形起点质量在线段上有共同正下界，故所规定率在每个有限区间有界连续。直接应用定理 2.4 的 Poisson 候选及前向方程唯一性构造，初律取 $p_{\kappa_{\rm init}}$，得到宣称的边缘；当 $Z=0$ 时状态 $2$ 不可达且吸收，不需除以 $p_2$。期望实际跳数导数为 $\sum_ef_e=2|s|+4\beta$，KL 导数由链式法则给出，随后除以 $N$。最小值及平方恒等式直接代入。加权系数由定理 14.2 比较首坐标取得。叶边被迫无流，不能把这一实现说成每条合法弧都严格活动；期望计数也不等于任一个样本历史。∎

**命题 15.3（同一实现的线性尺度与非线性经过时间）。** 令 $\mu_0=\mu(\kappa_0)$、$N_0=N(\kappa_0)$，则

$$
H_0=\mathcal A''(\kappa_0)
=\frac{r^3}{XY(r-X)(r-Y)}.
$$

定理 15.2 的平衡线性变分 $z$ 满足

$$
\frac{dz}{d\lambda}=-\mu_0H_0z,\qquad
\frac{dz}{d\tau}=-\frac{\mu_0H_0}{N_0}z.
$$

它的指数衰减尺度分别为 $1/(\mu_0H_0)$、$N_0/(\mu_0H_0)$；这使用[《响应三角形与内部记忆》定理 9.1–9.2](AURIC_FIB_ATOM_RESPONSE_TRIANGLE_AND_INTERNAL_MEMORY.md)中线性松弛的指数求解机制，只应用于这里的线性变分。以 $\kappa(\tau)$ 表示经共同参数逆函数重参数后的轨迹，非平衡解从 $\tau_i$ 到 $\tau>\tau_i$ 的实际经过时间为

$$
\tau-\tau_i=\int_{\kappa(\tau)}^{\kappa(\tau_i)}
\frac{N(u)}{\mu(u)\mathcal A'(u)}\,du,
$$

两端位于平衡同一侧；该有向积分在上、下两侧均为正。它不把线性变分的指数公式当作原非线性解。沿该共同钟律的钟率变化是

$$
\frac{d^2\tau}{d\lambda^2}
=-N'(\kappa)\mu(\kappa)\mathcal A'(\kappa),
$$

需要另给 $N'$，不能仅从 $H_0$ 推出。

证明。独立点的四格为 $(r-X)(r-Y)/r$、$X(r-Y)/r$、$(r-X)Y/r$、$XY/r$。将其倒数相加得 $H_0$。漂移对 $\kappa$ 求导时含 $\mu'\mathcal A'$ 的项在平衡消失；换元后的漂移为 $-(\mu/N)\mathcal A'$，同理得到第二个线性方程。分离原方程 $d\kappa/d\tau=-(\mu/N)\mathcal A'$ 给积分式，正则唯一性使非平衡解在有限参数内不会穿越或到达平衡。

例如 $X=Y=2/5,Z=1/5,\kappa=3/10$ 时，$\kappa_0=1/5$、$H_0=20$，真实 $\mathcal A'=2\log3$，而 $H_0(\kappa-\kappa_0)=2$。两者不同，故以同一正迁移率代入也给不同瞬时速度。最后的钟率式由假设 15.1 链式求导。它和活动式共同区分了 KL 下降、钟率变化与可自由增加的循环跳数；这些都是规定参数的量。∎

## 16. 终点 Bellman 势与五态钟读口

**假设 16.1（有限正成本的到达合同）。** 给有限有向图、终点 $t$，到达 $t$ 即停止；每个顶点可经有限路径到达 $t$，每条非终止边成本满足 $c_e\ge c_{\min}>0$ 且有限。值 $V(u)$ 定义为从 $u$ 到 $t$ 的有限路径成本最小值，$V(t)=0$。采用 [Bertsekas 的终点 Bellman 框架](../../../Library/Dynamics/bertsekas2015terminaldp.md)，这里的确定性合同只需：删去正成本循环使最小值在有限个简单路径中达到，按第一条边拆分得到

$$
V(u)=\min_{u\to v}\{c_{uv}+V(v)\}\quad(u\ne t).
$$

最小边使 $V$ 至少下降 $c_{\min}$，故沿最小边的策略有限步到达终点；不要求所有策略终止。一般有限实值解也等于此最小路径值：Bellman 不等式沿任一终点路径给上界，而逐步选择最小边、用严格下降排除有限图上的循环，给达到等号的路径。作为后文计算的经典中间量，令

$$
\varepsilon_e=c_e+V(\operatorname{head}(e))-V(\operatorname{tail}(e))\ge0.
$$

对有限路径 $\zeta:u\leadsto v$，逐边相加便有 $\sum_\zeta c=V(u)-V(v)+\sum_\zeta\varepsilon$；循环上 $\sum\varepsilon=\sum c$。没有终点、时域或折扣条件时不采用此方程，例如单点单位成本自环会要求 $V=1+V$。有限时域版本须有阶段下标，折扣版本须有折扣因子及相应加权望远镜和，均不同于此合同。

**命题 16.2（五边终点值、seam 钟响应与离散换钟）。** 在定义 2.1 的图上指定终点 $2$、五条边成本全为一。按本卷的状态序和边序，有

$$
V=(1,4,0,2,3),\qquad
\varepsilon=(4,0,0,0,0),\qquad
 g_B=-B^{\mathsf T}V=(-3,1,1,1,1).
$$

从 $0$ 出发绕方形 $m\in\mathbb Z_{\ge0}$ 周再去 $2$，路径成本为 $4m+1$；方形上值降的总和零而残差总和四。特别是合法边 $0\to1$ 提高 $V$，合法路径不必处处使值下降。

另取 $\alpha,N_{\rm ref}>0$，定义状态钟读口 $N_s=N_{\rm ref}e^{-\alpha V_s}$。记 $z=e^{-\alpha}\in(0,1)$，则

$$
\Delta_{\mathbf d}N
=N_{\rm ref}(z-z^4-z^2+z^3)
=N_{\rm ref}z(1-z)(1+z^2)>0.
$$

所以在任一固定非退化概率纤维上，该钟读口的精确期望按数学引文 1.4 的四角准则单射地区分 $\kappa$。这里 $V$ 由同一终点任务固定，概率变化不重新求解 $V$。

对实际有限路径 $s_0,\ldots,s_m$，指定 $h>0$、$\lambda_n=nh$、$N_n=N_{s_n}$，以及左端点累计 $\tau_{n+1}-\tau_n=hN_n$。对 $0\le n\le m-2$，令 $g_{B,n}=V(s_n)-V(s_{n+1})$，则精确式为

$$
\tau_{n+2}-2\tau_{n+1}+\tau_n
=hN_n\bigl(e^{\alpha g_{B,n}}-1\bigr).
$$

若另指定 $C^1$ 插值 $\widetilde V(\lambda)$ 并定义 $\widetilde N=N_{\rm ref}e^{-\alpha\widetilde V}$、$\widetilde\tau=\int\widetilde N\,d\lambda$，则在该连续模型内

$$
\widetilde\tau''=-\alpha\widetilde N\,\widetilde V'
=\alpha\widetilde N\,\widetilde g_B,\qquad
\widetilde g_B=-\widetilde V'.
$$

即使插值在节点处吻合，连续积分也不自动等于离散左端点累计，$\widetilde g_B$ 也不等于未除步长的一步值降。

证明。从 $0$ 到终点的直接边给值一；其余方形状态沿唯一前进方向依次到达 $0$，得 $V_3=2,V_{13}=3,V_1=4$，额外循环增加四不能改进最小值。逐边代入给 $\varepsilon$ 和 $g_B$，路径式消费假设 16.1 的望远镜和。钟读口的四角配对由所列五个值直接给出并因式分解；固定纤维的期望差因此是 $N_{\rm ref}z(1-z)(1+z^2)(\kappa'-\kappa)$，精确律与样本的范围沿用数学引文 1.4。

离散累计二次差等于 $h(N_{n+1}-N_n)$，而 $N_{n+1}/N_n=e^{\alpha g_{B,n}}$，得指数式，不能将 $e^{\alpha g_B}-1$ 精确替换成 $\alpha g_B$。连续式则是定义 14.3 的链式法则。比如一段非零值降上取线性插值，其钟积分为 $hN_n(e^{\alpha g_{B,n}}-1)/(\alpha g_{B,n})$，不等于 $hN_n$；分段线性插值在斜率跳变的顶点不提供 $C^1$ 合同。图上对数比仍是 $-\alpha B^{\mathsf T}V$ 的恰当余链，正的累计钟使用另一规则。这些构造区分终点优化、精确律读口和实际路径累计，并不从静态值函数推出运动律或物理时间。∎

## 追加锚（本行以下为增补区）

## 17. 同一五态律的占据读数与 Pauli 读数

**定义 17.1（模式换名、概率域与几何归属）。** 本节至第二十节采用对应

$$
(0,1,2,3,13)_{\rm support}
\longleftrightarrow(0,x,z,y,xy)_{\rm mode}
\longleftrightarrow(0,2,3,5,25)_{\rm label}.
$$

右端只是[《金字塔基础公式与关系》定义 2.1](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)的模式简记，$25$ 不表示整数二十五或素数乘积；列表、数值编码与历史仍按定义 1.1、6.1 区分。概率列向量按此顺序记为 $p=(p_0,p_2,p_3,p_5,p_{25})^{\mathsf T}$。

$$
\Delta_4=\{p\in\mathbb R^5:p\ge0,\ \mathbf1^{\mathsf T}p=1\},\qquad
P=A,\quad q=Pp=(X,Z,Y),\quad \kappa=p_{25},\quad
h=(1,-1,0,-1,1)^{\mathsf T}=\mathbf d.
$$

沿用数学引文 1.2 及所引基础卷 §§3–4，$\Delta_4$ 的仿射维数为四；其像是有界三维金字塔

$$
Q=\{(X,Z,Y):X,Z,Y\ge0,\ X+Z\le1,\ Y+Z\le1\}.
$$

$Q$ 不是整个 $\mathbb R^3$，也不是自身的拓扑边界；归一化仿射超平面模去 $\mathbb Rh$ 才是仿射三空间。实际概率纤维为 $p_\kappa$ 的区间 $[l_q,u_q]$，其中 $l_q=\max(0,X+Y+Z-1)$、$u_q=\min(X,Y)$；边界可使区间缩成一点，不据此声明全局乘积或恒定维数纤维丛。基础卷的可见次序 $(X,Y,Z)$ 与这里 $(X,Z,Y)$ 经第二、三坐标交换对应。

五函数代数直接取基础卷数学引文 2.2 的 $\mathcal A=\mathbb R^\Sigma$ 及五个原始事件幂等元。作为不带标记的实含幺代数，自同构可任意置换这五个幂等元，故为 $S_5$；要求保留生成元及冲突图 $x-z-y$ 时，只剩端点交换的 $C_2$，该冲突图有三个顶点。进一步下降为占据凸体的仿射自同构则取[《金字塔关联与原生接续》推导 10.2–10.3](AURIC_FIB_ATOM_PYRAMID_CORRELATION_AND_NATIVE_CONTINUATION.md)的八元 $D_4$；原标准欧氏尺子的等距群为 $C_2$，原生方向和数量还有额外限制。这些是不同的保持条件。连续连通群在这些有限自同构群中的连续作用只能为恒等；这不排除另外指定的非线性作用或另一载体上的连续表示。函数基的 $1+3+1$ 分组本身不是 $SO(3)$ 不可约分解。

**假设 17.2（同律、固定基架的通道实现）。** 使用[基础卷数学引文 14.1–14.3](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)与[《二阶关系完成》定义 112.1、定理 112.2](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md#112-五模式权重与固定基架旋转)的指定来源代表及经典随机模式选择：

$$
\mathcal N_p(\rho)=p_0\rho+p_2\sigma_x\rho\sigma_x
 +(p_3+p_{25})\sigma_y\rho\sigma_y+p_5\sigma_z\rho\sigma_z.
$$

输入量子态 $\rho=(I+r\cdot\sigma)/2$ 的 Bloch 向量 $r$ 位于单位球；固定共同输入、输出基架后，通道作用为 $r\mapsto D(p)r$，$D(p)=\operatorname{diag}(d_x,d_y,d_z)$。通道系数 $d_{\rm ch}=(d_x,d_y,d_z)$ 位于四个 Pauli 共轭的系数四面体，既不是占据点 $q$，也不是输入态 $r$。在质量归一化时，所引公式可写为 $d_{\rm ch}=Cp$，其中

$$
C=\begin{pmatrix}
1&1&-1&-1&-1\\
1&-1&1&-1&1\\
1&-1&-1&1&-1
\end{pmatrix}.
$$

这里的 $C$ 是通道读数矩阵，不是定义 8.2 的配置矩阵。所引全旋转协变条件是 $p_2=p_5=p_3+p_{25}$，不重新证明该一般通道事实。以下恢复要求 $q$ 与校准后的通道系数属于同一精确律 $p$；改变输入、输出基架或模式实现须相应重建字典。独立新环境且每步重置的同通道复合给 $D(p)^n$；反复使用同一个保留环境则须使用二阶卷定义 110.1、定理 110.2 的联合演化，命题 110.4 已给两者不同的例子。普通通道也不供应共同相干控制、来源相位或实际历史。

**定理 17.3（互补纤维及一个通道系数的完整恢复）。** 在假设 17.2 下，同一律满足

$$
d_x=1-2(Y+Z),\qquad
d_y=1-2(X+Y)+4\kappa,\qquad
d_z=1-2(X+Z).
$$

因而给定 $q\in Q$ 与 $d_y$，存在相容五态律当且仅当

$$
1-2(X+Y)+4l_q\le d_y\le1-2(X+Y)+4u_q.
$$

相容时唯一的律由

$$
\kappa=\frac{d_y-1+2X+2Y}{4},\qquad
p=(1-X-Y-Z+\kappa,X-\kappa,Z,Y-\kappa,\kappa)
$$

恢复。若还给出 $d_x,d_z$，它们须满足上面两条无 $\kappa$ 的等式。在质量零差空间 $T_0=\ker\mathbf1^{\mathsf T}$ 上，两种读数核为

$$
\ker(P|_{T_0})=\mathbb Rh,\qquad
\ker(C|_{T_0})=\mathbb Rg,\qquad
g=(0,0,1,0,-1)^{\mathsf T},\qquad
Ch=(0,4,0)^{\mathsf T},\quad Pg=(-1,1,-1)^{\mathsf T}.
$$

所以它们的核交为零，但单独两种读数互不决定。

证明。把数学引文 1.2 的逆式代入 $Cp$ 给三个系数；$d_y$ 随 $\kappa$ 的斜率为四，故合法区间与逆式都包含退化纤维和零概率端点。对 $v\in T_0$，$Cv=0$ 的三个分量分别给 $v_0+v_2=0$、$v_0+v_3+v_{25}=0$、$v_0+v_5=0$；与总质量零联立得到 $v_0=v_2=v_5=0$、$v_3=-v_{25}$，即所列通道核。占据核复用数学引文 1.2，两个方向不共线，直接相乘给 $Ch,Pg$。

互不决定有实际概率见证：$\delta_3$ 与 $\delta_{25}$ 的通道相同，占据却分别为 $(0,1,0)$ 与 $(1,0,1)$；$(\delta_0+\delta_{25})/2$ 与 $(\delta_2+\delta_5)/2$ 的占据均为 $(1/2,0,1/2)$，通道系数分别为 $(0,1,0)$ 与 $(0,-1,0)$。联合读数恢复的是精确概率律；它不把有限样本变成精确系数，也不恢复自由来源树或保留环境。∎

**定理 17.4（每条合法占据纤维的协变截取）。** 给定 $q=(X,Z,Y)\in Q$，假设 17.2 的全旋转协变通道在该纤维上有原像，当且仅当

$$
X=Y=u,\qquad 0\le Z\le u,\qquad u+Z\le\frac23.
$$

有原像时该五态律唯一，为

$$
\kappa_{\rm iso}=\frac{u-Z}{2},\qquad
p_{\rm iso}=\left(1-\frac{3(u+Z)}2,\frac{u+Z}2,Z,
                  \frac{u+Z}2,\frac{u-Z}2\right),\qquad
D(p_{\rm iso})=[1-2(u+Z)]I_3.
$$

允许的占据点构成三角形，按 $(X,Z,Y)$ 排列的顶点为 $(0,0,0)$、$(2/3,0,2/3)$、$(1/3,1/3,1/3)$。但固定一个标量通道 $D=tI_3$ 的全部五态原像是

$$
-\frac13\le t\le1,\quad a=\frac{1-t}{4},\qquad
p=(1-3a,a,z,a,a-z),\quad 0\le z\le a,
\qquad q=(2a-z,z,2a-z).
$$

除 $t=1$ 外，该通道有一整段不同占据和不同五态律。

证明。使用已引的协变条件，$p_2=p_5$ 给 $X=Y=u$；$p_2=p_3+p_{25}$ 给 $u-\kappa=Z+\kappa$，故唯一可能的 $\kappa$ 如上。代回概率逆式，五个分量非负恰给所列三个不等式，总和为一，故也充分。这些不等式在 $(u,Z)$ 平面切出所列三角形，包含全部边界。再代入定理 17.3 得标量系数。反过来固定 $t$，协变三个 Pauli 总权都等于 $a=(1-t)/4$，留下的唯一自由度是把 $a$ 分成 $p_3=z$ 与 $p_{25}=a-z$；非负性给 $0\le a\le1/3$、$0\le z\le a$。由此得到全部原像。这一分类区别了同占据纤维内的唯一性和固定通道本身的可识别性，不从通道协变推断物理空间各向同性。∎

## 18. 实际域闭合与表示读出的类型

**数学引文 18.1（列概率下的闭合及未来范围）。** 固定一个非负列随机矩阵 $T$，即 $\mathbf1^{\mathsf T}T=\mathbf1^{\mathsf T}$，作用为 $p'=Tp$。[基础卷定义 14.4、命题 14.5](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)用行随机矩阵 $T_{\rm row}$，这里明确取 $T=T_{\rm row}^{\mathsf T}$，并交换其占据的第二、三坐标。于是该既有四角条件在全 $\Delta_4$ 上为 $PTh=0$。满足时唯一下降的仿射映射 $F:Q\to Q$ 为

$$
F(X,Z,Y)=v_0+(v_2-v_0)X+(v_3-v_0)Z+(v_5-v_0)Y,
\qquad v_s=PT\delta_s.
$$

单有总质量保持只给仿射映射到 $\mathbb R^3$；非负随机性才保证像留在 $Q$。对实际限制域 $D\subseteq\Delta_4$，采用[《局部钟因果场与纤维动力学》Q1、Q5–Q6](AURIC_FIB_ATOM_LOCAL_CLOCK_CAUSAL_FIELD_AND_FIBER_DYNAMICS.md)的纤维条件：

$$
PT(p'-p)=0\quad\text{对所有 }p,p'\in D\text{ 且 }Pp=Pp'.
$$

只有 $D$ 中存在非零同纤维差时，该条件才强制 $PTh=0$；若投影在 $D$ 上单射，一步集合下降自动成立。固定域上的迭代还需 $T(D)\subseteq D$，或逐步指定可达域链。

在全单纯形上满足 $PTh=0$ 的同一个固定 $T$ 下，质量保持和既有一维核给 $Th=\lambda h$；随机矩阵的 $\ell^1$ 收缩给 $|\lambda|\le1$。因此同一初始占据纤维内的两个律满足 $T^n(p'-p)=\lambda^n(p'-p)$，其 $\kappa$ 差按同一因子缩放。这里控制的是差，不是绝对 $\kappa_n$；也不比较不同可见初值或不同更新规则。所断言的闭合只涉及未条件化的终点均值。完整记录和按记录继续的充分合同仍用基础卷命题 14.6 的输出—更新共同核、正概率条件化和守卫，不用均值闭合代替。

**命题 18.2（协变、交换泄漏与受限面）。** 令 $M$ 交换模式 $0,2$，固定其余模式，并取

$$
p^{\rm iso}=\frac1{10}(1,3,2,3,1)^{\mathsf T},\qquad
p^{\rm alt}=\frac1{10}(3,1,2,1,3)^{\mathsf T}.
$$

两者占据同为 $(2/5,1/5,2/5)$，通道系数分别为 $(-1/5,-1/5,-1/5)$ 与 $(-1/5,3/5,-1/5)$；所以此占据不能单独决定全旋转协变。下一占据为

$$
PMp^{\rm iso}=(1/5,1/5,2/5),\qquad
PMp^{\rm alt}=(3/5,1/5,2/5),\qquad PMh=(2,0,0)^{\mathsf T}.
$$

但在不变面 $D_0=\{p:p_{25}=0\}$ 上，同一 $M$ 的占据更新确实闭合，为 $F_0(X,Z,Y)=(1-X-Y-Z,Z,Y)$。此外，令 $U$ 将模式 $3$ 送到 $25$，固定其余模式，则 $Uh=h$ 而 $\kappa' =\kappa+Z$。

证明。两律的差为 $h/5$，定理 17.3 给通道系数，定理 17.4 判定其中仅第一律协变。交换后的两律分别为 $(3,1,2,3,1)/10$ 与 $(1,3,2,1,3)/10$，相加其第二、五分量给两个不同的 $X$，其余占据不变。在 $D_0$ 上 $p=(1-X-Y-Z,X,Z,Y,0)$，故投影单射、$M(D_0)=D_0$，直接交换给 $F_0$。最后 $h$ 的模式 $3$ 分量为零，$U$ 对其作用不变，但将全部 $p_3=Z$ 加入 $p_{25}$；例如 $\delta_3$ 的 $\kappa$ 从零变一。因此隐藏特征值一并不表示绝对联合质量守恒。∎

**假设 18.3（截面读出、等变与局部恢复）。** 若把定义 8.1 的静态提取扩展到场，另给同一底空间 $M$ 上的丛 $B_{\rm rel}\to M$、$E_\lambda\to M$。点态读出是覆盖恒等的丛映射 $r_\lambda:B_{\rm rel}\to E_\lambda$，诱导

$$
R_\lambda:\Gamma(B_{\rm rel})\to\Gamma(E_\lambda),\qquad
R_\lambda(\Phi)=r_\lambda\circ\Phi.
$$

读出须保留所选连续或光滑截面类。需要导数时另给光滑底流形及光滑丛；依赖 $k$ 阶局部导数时，改给 $r_\lambda:J^kB_{\rm rel}\to E_\lambda$，对 $C^k$ 截面读 $r_\lambda\circ j^k\Phi$，并声明输出的正则性。$B_{\rm rel}\to\Gamma(E_\lambda)$ 不是这里的逐点读出类型；单个 $q\in Q$ 也不是整个场截面。此丛截面不同于数学引文 1.2 的线性分裂截面。

等变性另需群在底空间和两个丛上的相容作用。若 $g$ 覆盖 $g_M$，则截面作用为 $(g\cdot\Phi)(x)=g_B(\Phi(g_M^{-1}x))$；要求 $r_\lambda g_B=g_Er_\lambda$，高阶版本则使用诱导 jet 作用。向量丛中的线性读出与一般非线性映射须分别说明，不能由相同维数推出等变同构。

对于 $Q$ 的内部或指定光滑分层上的 $C^1$ 读出，秩指微分的秩。若要求向一个开放六维目标域的 $C^1$ 局部右逆，链式法则强制该秩为六；三维源不可能满足。但目标若只是一给定低维约束像，则不要求秩六；有限状态集也没有这个微分秩。逐点可恢复不自动给整个截面、导数或动态可恢复，仍须指定其共同域与操作。

物理表示只作为类型索引的既有背景：[PDG《Quantum Chromodynamics》§9.1、式 (9.1)–(9.2)](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-qcd.pdf)区分 $SU(3)$ 夸克的三维复内部表示、胶子的八维实伴随表示和时空指标 $\mu$。它们不是三维实空间向量；$8+3+1$ 是所声明 $\mathfrak{su}(3)\oplus\mathfrak{su}(2)\oplus\mathfrak u(1)$ 的内部维数，未计入时空一形式指标。规范连接写成代数值一形式须选局部平凡化，不默认存在单一全局连接形式。这里不引入这些物理场的作用量或演化；若请求 Maxwell、Yang–Mills 或 Einstein 对应，还须给相应载体、群作用、单位、场方程和受控实现或极限。定理 17.3–17.4 与命题 18.2 只消费有限五态和指定通道合同。

## 19. 函数—概率对偶与共同读出的路径合同

**定义 19.1（评价、系数与对偶矩）。** 在定义 17.1 的模式顺序中，函数代数 $\mathcal A=\operatorname{Fun}(\Sigma,\mathbb R)$ 用点乘；概率质量则是其对偶空间中的正、归一化泛函。复用[基础卷数学引文 2.2、7.2](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)，函数系数顺序取 $(1,x,z,y,xy)$，记

$$
c=(c_0,c_x,c_z,c_y,\chi)^{\mathsf T},\qquad
f=E c,\qquad
E=\begin{pmatrix}
1&0&0&0&0\\
1&1&0&0&0\\
1&0&1&0&0\\
1&0&0&1&0\\
1&1&0&1&1
\end{pmatrix}.
$$

此处 $f$ 是五点评价值列，$E$ 是评价矩阵，不是第二节的边集合。它由既有五函数基可逆，且

$$
m=E^{\mathsf T}p=(1,X,Z,Y,\kappa)^{\mathsf T},\qquad
\mathbb E_p[f]=f^{\mathsf T}p=c^{\mathsf T}m
=c_0+c_xX+c_zZ+c_yY+\chi\kappa,
\qquad E^{\mathsf T}h=(0,0,0,0,1)^{\mathsf T}.
$$

$\chi=f_{25}-f_2-f_5+f_0$ 是可观察函数的混合系数，$\kappa=p_{25}$ 是状态矩；两者由期望配对相遇，不是同一坐标。常函数 $1$ 的评价列是 $\mathbf1$，空模式指示函数则是 $1-x-z-y+xy$，评价列为 $\delta_0$。系数空间、评价空间和概率对偶的这三套坐标都为五维，但不会因此具有同一乘法、正性或归一化。

例如 $(c_x+\chi,c_z,c_y+\chi)$ 是可声明的系数线性读出，并非该函数的概率占据。若另行把 $Ec$ 声明为质量列，还必须有 $Ec\ge0$、$\mathbf1^{\mathsf T}Ec=1$，其占据才是 $PE c$，不是 $Pc$。函数族 $v\mapsto c(v)$ 也不自动给概率律场；须按定义 8.1 或另给的正归一化规则提取。以上等式是同一既有基的坐标字典，不增加新的五态代数定理。

**定义 19.2（状态推前与函数拉回）。** 给两个五态载体 $V_u,V_v$、其函数代数和评价矩阵 $E_u,E_v$。列随机 $T_e:V_u\to V_v$ 推前质量；终点函数 $f_v$ 的起点拉回为 $T_e^{\mathsf T}f_v$。系数拉回和矩推前分别为

$$
c_u=K_e c_v,\quad K_e=E_u^{-1}T_e^{\mathsf T}E_v,
\qquad
m_v=M_e m_u,\quad M_e=E_v^{\mathsf T}T_eE_u^{-\mathsf T}=K_e^{\mathsf T}.
$$

所以 $c_v^{\mathsf T}m_v=(K_ec_v)^{\mathsf T}m_u$；其方向和转置不能互换。列随机性使评价拉回为正且保常函数一，但不保证保点乘。在第二十节的重置 $R_a=a\mathbf1^{\mathsf T}$ 下，任意非平凡事件指示函数 $f$ 被拉回为常数 $\mathbb E_a f\in(0,1)$，其平方不等于自身，故该拉回不是代数同态。一般有限函数代数的含幺同态需把互斥事件幂等元仍送到互斥幂等元；逐个起点评价恰选择一个终点事件，给确定性函数拉回。带符号电流映射也不会仅因矩阵形状相同就成为这些概率或函数操作。

**假设 19.3（有类型的共同边输运与交织）。** 另给有限有向图 $\mathcal G=(\mathcal V,\mathcal E)$；每个节点携带五态质量空间 $V_v$、实际域 $D_v\subseteq\Delta_4$。每条允许边 $e:u\to v$ 配列随机 $T_e:V_u\to V_v$，满足 $T_e(D_u)\subseteq D_v$。这些是节点间传送一整个概率律的边，非定义 2.1 中单个状态跳转的五条边。若采用部分守卫，须额外给允许域，以下比较限于共同合法的继续，或以保留拒绝输出的方式总化。

对每种读出 $\lambda$，给线性映射 $L_v^\lambda:V_v\to W_v^\lambda$ 和 $S_e^\lambda:W_u^\lambda\to W_v^\lambda$，要求

$$
L_v^\lambda T_e=S_e^\lambda L_u^\lambda.
$$

使用[局部钟因果场卷 Q3、Q5、Q7](AURIC_FIB_ATOM_LOCAL_CLOCK_CAUSAL_FIELD_AND_FIBER_DYNAMICS.md)的路径与实际因子化范围，这一合同按路径 $\gamma=(e_1,\ldots,e_n):u\leadsto v$ 复合为

$$
T_\gamma=T_{e_n}\cdots T_{e_1},\quad
S_\gamma^\lambda=S_{e_n}^\lambda\cdots S_{e_1}^\lambda,\quad
L_v^\lambda T_\gamma=S_\gamma^\lambda L_u^\lambda.
$$

在基于 $u$ 的回路 $C$ 上置 $H_C=T_C$，则同一式给

$$
L_u^\lambda(H_C-I_{V_u})=(S_C^\lambda-I_{W_u^\lambda})L_u^\lambda.
$$

这是具有匹配源、靶的交织应用；不能把作用于状态的 $L$ 改写为没有定义的 $L(T_2T_1)$。在线性全空间上，下降首先只定义于 $\operatorname{im}L_u$；更大目标空间上的延拓须另定。实际域上的非线性读出则用 $L_v(T_ep)=S_e(L_u(p))$ 的逐纤维合同，不把其不可区分性写成线性核。

占据更新通常仿射，故应使用总量增广 $B_{{\rm obs},v}=(\mathbf1^{\mathsf T};P_v)$ 来交织，或者明确采用仿射 $S_e$；$B_{\rm obs}$ 不是本卷关联矩阵 $B$。例如重置在占据上是非零常映射，不能由原点齐次的三维线性图表示。路径复合给路径范畴上的作用；若还要称为某个主算子半群的表示，必须证明代表同一主算子的不同分解诱导同一 $S$。群表示或可逆联络则另需许可的逆输运；一般随机 $H_C-I$ 只是算子差，既非随机更新，也未定义几何曲率。

**数学引文 19.4（现在不可见与全部指定未来不可见）。** 在同一节点，对实际可行 $p,p+\alpha h\in D_v$，线性读出族当前相同的精确条件为 $\alpha L_v^\lambda h=0$ 对每个 $\lambda$ 成立；要由 $L_v^\lambda h\ne0$ 给区别见证还须 $\alpha\ne0$。非线性读出直接比较两实际值。对未来，消费[本卷数学引文 4.2](#4-同一初始-seam-的未来合同)及[局部钟因果场卷 Q5、Q9](AURIC_FIB_ATOM_LOCAL_CLOCK_CAUSAL_FIELD_AND_FIBER_DYNAMICS.md)的完整共同任务合同；在线性、总定义、前向不变域的终点读数任务中可写成

$$
N_u=\left\{z\in\ker\mathbf1^{\mathsf T}:
L_{t(\gamma)}^\lambda T_\gamma z=0
\ \text{对每条从 }u\text{ 出发的允许路径 }\gamma
\text{ 及每个 }\lambda\right\}.
$$

路径包含空路径，故未来不可见蕴含当前不可见；操作上的比较仍需实际对 $p,p'\in D_u$ 且 $p'-p\in N_u$。若守卫依赖状态，还需二者有相同允许继续，不能仅由集合差 $D_u-D_u$ 认证可执行性。单算子的全未来核及商已有[最大不可观测子空间的 `future_kernel_is_maximal_invariant`](../../../D5/S3/ObserverMemory/Dynamics/MaximalUnobservableSubspace.lean)和[未来读出商的 `future_readout_quotient_is_coarsest_with_unique_dynamics`](../../../D5/S3/ObserverMemory/Dynamics/FutureReadoutQuotient.lean)作为归属；此处只指定当前模型的读出和路径族，不把它们再列为新定理。

当 $P$ 属于当前读出时，$N_u\subseteq\mathbb Rh$。在共同完整五态域、所有动作均允许的模型中，若每个 $T_eh=\lambda_eh$，路径差就乘以 $\prod_e\lambda_e$；若所有终点 $L_v^\lambda h=0$，全部这些终点读数都不见该方向。反之，只要某个允许路径和读出满足 $L_{t(\gamma)}^\lambda T_\gamma h\ne0$，这个线性未来核即为零；在限制域上仍需非零可行差才能给实际辨识。因此数学引文 18.1 的同一闭合 $T$ 不会在稍后的未条件化占据均值中突然泄漏，换动作、读口或条件记录是另一合同。

完整档案概率要求所有分支仪器词，而非仅终点算子；须保留子归一化分支质量，并只对正质量档案条件化，具体充分条件用基础卷命题 14.6。现在或未来不可见都相对于这份菜单，不自动定义规范等价。边差 $J_e=P_vT_eh$ 位于有符号读数空间 $\mathbb R^3$，不是非负金字塔 $Q$ 的一点；它也不是 Laplacian 的节点源、可加储存密度或物理场源。

## 20. 可见输运不能自动提升为共同节点律

**定义 20.1（同时赋值与联合实现）。** 对假设 19.3 的全部边，共同节点律的可行集合定义为

$$
\mathcal C=\left\{(p_v)\in\prod_{v\in\mathcal V}D_v:
p_v=T_ep_u\ \text{对每条 }e:u\to v\right\}.
$$

它要求所有入边同时相容。若要一个共同随机场，还须另有 $\Pi$ 在 $\Sigma^{\mathcal V}$ 上，使节点边缘为 $p_v$，且每条边满足

$$
\Pi(X_u=s,X_v=t)=p_u(s)T_e(t,s).
$$

采用[《边界、运输纤维与回路闭合》Q4、Q11、§7](AURIC_FIB_ATOM_BOUNDARY_TRANSPORT_FIBERS_AND_LOOP_CLOSURE.md)的联合可行性界限，节点边缘方程本身不保证这组边联合律可同时实现。若只逐路径生成状态，则写 $p_\gamma=T_\gamma p_r$，允许同一终点有不同的路径标记律，不称为 $\mathcal C$ 的元素。对选定初态，各回路固定该态弱于 $H_C=I$；对 DAG，所有有向回路条件还可能真空成立。可逆路径比较另按假设 19.3 所引 Q3、Q7 的条件，不把形式反向添加成合法随机逆。

**定理 20.2（严格正重置的菱形障碍）。** 令

$$
\pi=\tfrac15\mathbf1,\qquad
a=\pi+\tfrac1{10}h=\tfrac1{10}(3,1,2,1,3)^{\mathsf T},\qquad
b=\pi-\tfrac1{10}h=\tfrac1{10}(1,3,2,3,1)^{\mathsf T},
\qquad R_a=a\mathbf1^{\mathsf T},\quad R_b=b\mathbf1^{\mathsf T}.
$$

在菱形 $r\to u\to t$、$r\to v\to t$ 上，前两条从 $r$ 出发的边均取 $I_5$，$u\to t$ 取 $R_a$，$v\to t$ 取 $R_b$，节点域全为 $\Delta_4$。每条边都为随机输运，两条重置边严格正、各自保持占据闭合，并且

$$
R_ah=R_bh=0,\qquad
PR_a=PR_b=q_*\mathbf1^{\mathsf T},\qquad q_*=(2/5,1/5,2/5)^{\mathsf T}.
$$

任一初始律都有单值的可见节点赋值，且两条完整路径的可见映射相等；然而 $\mathcal C=\varnothing$，对任何初始律都没有共同五态节点赋值。图中没有非空有向回路。若终点还读假设 17.2 的通道，则两条路径的 $d_y$ 分别为 $3/5$、$-1/5$，区分这份路径依赖。

证明。$a,b$ 的五分量严格正、总和一，且 $a-b=h/5\ne0$。故重置矩阵各列非负、列和一；$\mathbf1^{\mathsf T}h=0$ 使两者消去隐藏方向，$Ph=0$ 使投影相同，$P\pi=q_*$ 给所列常映射。可见赋值取 $q_u=q_v=q_r$、$q_t=q_*$，满足全部可见边约束。

任何共同全律赋值却必须同时有 $p_u=p_v=p_r$、$p_t=R_ap_r=a$ 和 $p_t=R_bp_r=b$，与 $a\ne b$ 矛盾。两条合法路径仍各自有终点律 $a,b$。图按 $r$、$u,v$、$t$ 分层，无有向回路，故仅查回路不能发现此障碍。通道差直接消费定理 17.3 或命题 18.2 的同一对律。特别地，这里不仅 $P(R_a-R_b)h=0$，而且整个 $P(R_a-R_b)=0$；即使局部隐藏闭合和全可见路径一致都满足，也不能提升成共同全律，更不能推出具有规定边耦合的共同随机场。∎

**命题 20.3（固定律的不可逆收缩回路）。** 对同一个 $\pi$，置 $R=\pi\mathbf1^{\mathsf T}$，并取 $0<\lambda<1$，定义

$$
T_\lambda=\lambda I+(1-\lambda)R.
$$

此输运严格正且列随机，满足

$$
T_\lambda\pi=\pi,\qquad T_\lambda h=\lambda h,\qquad
T_\lambda^n=\lambda^nI+(1-\lambda^n)R\quad(n\ge0),\qquad T_\lambda\ne I.
$$

一节点自环采用它时，共同节点律唯一为 $\pi$，每个回路都固定这个选定律，但每个非空回路的算子非恒等。同一占据纤维中的两律之差收缩为 $\lambda^n$ 倍，未条件化占据保持闭合；完整态的逆却不保持概率：

$$
T_\lambda^{-1}=\lambda^{-1}I-\frac{1-\lambda}{\lambda}R,
\qquad
(T_\lambda^{-1})_{ij}=-\frac{1-\lambda}{5\lambda}<0\quad(i\ne j).
$$

因此它没有全单纯形上的随机逆。令 $S_t=e^{-t}I+(1-e^{-t})R$，则 $t\ge0$ 给前向随机半群；没有以相同 $S_t$ 为正参数部分的、全单纯形随机映射组成的双向群延拓。

证明。$R^2=R$、$R\pi=\pi$、$Rh=0$，故 $T_\lambda=\lambda(I-R)+R$ 在两个互补投影上分别乘 $\lambda,1$，得到幂和唯一线性逆。非对角元 $(1-\lambda)/5$ 为正，对角元再加 $\lambda$，列和为一。若概率律满足 $T_\lambda p=p$，则 $(1-\lambda)(p-\pi)=0$，故唯一为 $\pi$；$T_\lambda h=\lambda h\ne h$ 则说明算子不恒等。可见下降具体为 $q\mapsto\lambda q+(1-\lambda)q_*$。

逆的任一列都有负分量，故把相应纯态送出单纯形。任何全单纯形上的逆映射都必须取这个唯一线性原像，因此即使不预设逆的线性也不能获得全域概率逆。用 $e^{-s}e^{-t}=e^{-(s+t)}$ 和两个互补投影得 $S_sS_t=S_{s+t}$；若延拓为群，负参数必为正参数的逆，仍有上述负分量。限制到可达像 $T_\lambda(\Delta_4)$ 可以作集合逆，但这不等于全单纯形双向随机输运，也未赋予逆动作权限。选定固定律、可见闭合、隐藏差收缩、线性可逆和概率可逆在此有明确不同的结论；参数 $t$ 没有由该构造获得物理时间意义。∎

## 追加锚（本行以下为增补区）

## 21. 五面删除的乘法与链边界障碍

**定义 21.1（位置、质量、函数、矩与链的分别承载）。** 本节恢复定义 1.1 的位置顺序 $(0,1,2,3,13)$，它与第十七至二十节的列表简记 $(0,2,3,5,25)$ 逐项对应。自由质量空间为 $H=\bigoplus_{s\in\Sigma}\mathbb R\mathbf e_s$，概率域为 $\mathcal D$；函数空间为 $H^\vee=\operatorname{Fun}(\Sigma,\mathbb R)$，事件基记 $\epsilon_s(t)=\mathbf1_{s=t}$。函数点乘、系数基 $(1,x,z,y,xy)$、评价矩阵和对偶矩沿用定义 19.1，故 $p$、函数系数 $c$、评价值 $f$ 与矩 $(1,X,Z,Y,\kappa)$ 不互作替身。常函数 $1=\sum_s\epsilon_s$ 与空态指示 $\epsilon_0=1-x-z-y+xy$ 不同；根则是定义 9.1 中另给的带点结构。

以 $A$ 表定义 1.1 的占据映射，另记

$$
B_{\rm obs}p=(\mathbf1^{\mathsf T}p,Ap),\qquad
h=\mathbf d=\mathbf e_0-\mathbf e_1-\mathbf e_3+\mathbf e_{13}.
$$

$B_{\rm obs}$ 不是图关联矩阵 $B$。数学引文 1.2 给 $\ker B_{\rm obs}=\mathbb Rh$，而 $\ker A$ 在整个 $H$ 上有二维。$h\ne0$，只有其观察像 $B_{\rm obs}h=0$；自由基不满足 $\mathbf e_0+\mathbf e_{13}=\mathbf e_1+\mathbf e_3$，事件基也不满足相应等式。

支持复形取 $K_{\rm A}=\{\varnothing,1,2,3,13\}$。[隐藏关系卷 C-28.7.1–C-28.8.2](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)已给其维数和同伦型，并区分支持复形、三维占据凸包和四维概率单纯形；定义 2.1 的五态转移图是另一对象。为比较删除操作，额外选 $V=\mathbb R^3$ 的有序基 $u_1,u_2,u_3$、外代数 $\mathcal E=\Lambda V$ 和线性子空间

$$
S=\operatorname{span}(1,u_1,u_2,u_3,u_{13}),\qquad
u_{ij}=u_i\wedge u_j,\qquad u_{123}=u_1\wedge u_2\wedge u_3.
$$

外幂的基与秩使用 [Conrad，定理 4.2、10.2 及例 10.3](../../../Library/Geometry/conrad2026exterior.md)。线性字典 $\Theta:H\to S$ 指定 $\mathbf e_0\mapsto1$、$\mathbf e_i\mapsto u_i$、$\mathbf e_{13}\mapsto u_{13}$，它没有指定保乘法、概率或动态的意义。把 $\mathcal E$ 的基单项式同时标为完整三顶点单纯形的增广链时，外次数 $r$ 对应链次数 $r-1$：三顶点的满面是二维三角形，面数 $1+3+3+1$ 包含空面，不是三维体的面数。$S$ 对应 $K_{\rm A}$ 的增广链；其空面基元也不是函数 $\epsilon_0$。

在此字典上使用 [Hatcher §2.1 的交错边界](../../../Library/Geometry/hatcher2002algebraic.md)，并明确加入增广项：

$$
\partial1=0,\qquad \partial u_i=1,\qquad
\partial u_{ij}=u_j-u_i,\qquad
\partial u_{123}=u_{23}-u_{13}+u_{12}.
$$

这是降链次数的边界，不是函数的混合有限差分，也不是升形式次数的外微分。合法支持中 $12,23,123$ 均为禁面；它们在额外载体 $\mathcal E$ 中存在，不表示原概率源已含三个潜在物理场。

**定理 21.2（五面投影的两种乘法及链回缩障碍）。** 定义 $Q:\mathcal E\to S$ 在 $1,u_1,u_2,u_3,u_{13}$ 上为恒等，在 $u_{12},u_{23},u_{123}$ 上为零，包含映射记 $\iota_S:S\hookrightarrow\mathcal E$。则 $S$ 是增广链子复形，$Q$ 是分次线性回缩，但 $S$ 不对原外积封闭，且 $Q$ 不是链映射。外积比较均经 $\iota_S$ 放在 $\mathcal E$ 中，链缺陷取值在 $S$；其精确式为

$$
\begin{aligned}
Q(u_1\wedge u_2)&=0\ne u_{12}=Q(u_1)\wedge Q(u_2),\\
(Q\partial-\partial Q)u_{12}&=u_2-u_1,\\
(Q\partial-\partial Q)u_{23}&=u_3-u_2,\\
(Q\partial-\partial Q)u_{123}&=-u_{13}.
\end{aligned}
$$

更强地，不存在从完整三角形增广链到 $S$、固定三个标号顶点的分次链回缩。若改在 $S$ 定义 $a\star b=Q(a\wedge b)$，则 $(S,\star)$ 是有单位的结合代数，且

$$
(S,\star)\cong\mathcal E/J,\qquad
J=(u_{12},u_{23})=\operatorname{span}(u_{12},u_{23},u_{123}).
$$

$Q$ 到这个新乘法才是代数同态；原边界不能沿这个商下降。无论采用 $\mathcal E$ 的原外积还是 $S$ 的 $\star$，均没有把 Boolean 函数生成元 $x,z,y$ 分别送到 $u_1,u_2,u_3$ 的保乘法识别。$\iota_SQ$ 也不是任何 $P_0:V\to V$ 的外代数延拓 $\Lambda(P_0)$。

证明。$\partial S\subseteq S$ 由五个基元的边界直接给出；所列三个缺陷逐项代入交错公式。若链映射 $r$ 固定全部顶点，则 $r(u_{12})$ 必为 $c u_{13}$，链条件要求 $c(u_3-u_1)=u_2-u_1$；左侧 $u_2$ 系数零，右侧为一，矛盾。这个论证甚至排除任何固定顶点的分次链映射，不只排除所选 $Q$。

$J$ 中每个单项式包含禁边 $12$ 或 $23$，再左右外乘任何基单项式仍在 $J$ 或为零，故是两侧理想；$u_{123}=u_{12}\wedge u_3$ 也在其中。直和 $\mathcal E=S\oplus J$ 将商乘法运输成 $\star$，给结合性、单位和 $Q$ 的代数同态性。但 $\partial u_{12}=u_2-u_1\notin J$，所以两个相同商类 $[u_{12}]=[0]$ 的边界类不同，边界无法下降。$S$ 上保留的 $\partial|_S$ 是有效链边界，却不使这个商投影变成链映射。

[基础卷数学引文 2.2](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)给 $x^2=x$，而 $u_1\wedge u_1=u_1\star u_1=0\ne u_1$，故上述生成元对应不保乘法。最后，若 $\iota_SQ=\Lambda(P_0)$，一次部分迫使 $P_0=I_V$；[关系观察卷 §129.2](RECURSIVE_RELATIONAL_OBSERVATION.md)的真正外延拓遂为恒等，与 $Q(u_{12})=0$ 矛盾。此为指定五面删除的应用推导；不增加支持同伦、矩反演或未来闭包的另一套结论。∎

**定义 21.3（同一概率源的三元读数与相干量类型）。** 在 $p\in\mathcal D$ 上区分占据三元 $T_{\rm occ}(p)=(X,Z,Y)$ 与端点联合三元 $T_{\rm end}(p)=(X,Y,\kappa)$。后者等价于按 $x,y$ 为行、列的归一化四格端点表。它们的全部实际纤维、不同遗忘方向及同读数而不同下一回复的见证，直接使用[隐藏关系卷 C-7.5–C-7.6](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)；不能由两者都写成三个数就认定其商相同。支持同伦使用同卷 C-28.7–C-28.8，一般矩反演、误差和闭包使用 C-28.5、C-28.10–C-28.12，不从 $Q$ 推导随机输运或任务下降。

在同一 $p$ 上，[隐藏关系卷 C-7.3](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)与本卷数学引文 1.3 固定下列不同量：

$$
\operatorname{Cov}_p(x,y)=\kappa-XY,\qquad
\Delta=p_0p_{13}-p_1p_3=(1-Z)\kappa-XY,\qquad
\operatorname{Cov}_p(x,y\mid s\ne2)=\frac{\Delta}{(1-Z)^2}\quad(Z<1).
$$

对指定函数 $f$，定义 19.1 的混合系数则是 $J_f=f_{13}-f_1-f_3+f_0=\langle f,h\rangle$。它描述该目标沿质量方向 $h$ 的响应，不是联合质量或协方差。是否可从边缘恢复由实际来源族决定；协方差非零本身不否定可识别性，已有 C-7.4 的正活动族给出具体受限来源。

若另供有限维量子联合态 $\rho_{RQ'}$，取 $S(\rho)=-\operatorname{tr}(\rho\log_2\rho)$，则 [Schumacher–Nielsen §4、式 (3)](../../../Library/Quantum/schumachernielsen1996quantum.md)的相干信息为 $I_c(R\rangle Q')=S(\rho_{Q'})-S(\rho_{RQ'})$；解释为通道相干信息还需供给输入纯化与作用于输入系统的通道。非对角相位／相干又须指定共同 Hilbert 载体、基和可比较操作，直接采用 C-28.12.1–C-28.12.3。经典概率、$J_f$、协方差、相干信息和非对角元在这些合同下分别定义。

**假设 21.4（外形式三元的比较接口）。** 为比较而额外供给实余向量空间 $W^*=\operatorname{span}(\theta^0,\theta^1,\theta^3)$，有序定向体积 $\mathrm{vol}_W=\theta^0\wedge\theta^1\wedge\theta^3$ 和余度规 $\operatorname{diag}(\sigma,1,1)$，其中 $\sigma=1$ 为 Euclidean，$\sigma=-1$ 为 $2+1$ Lorentzian。取诱导外幂内积，以 $\alpha\wedge\star\beta=\langle\alpha,\beta\rangle\mathrm{vol}_W$ 定义 Hodge 星号。由 [Tong 的 Hodge 定义及星号平方公式 (3.97)–(3.98)](../../../Library/Geometry/tong2021general.md)，在这个明确约定下

$$
\star\theta^{01}=\sigma\theta^3,\qquad
\star\theta^{03}=-\sigma\theta^1,\qquad
\star\theta^{13}=\theta^0,\qquad
\star^2|_{\Lambda^2W^*}=\sigma I,
\quad \theta^{ij}:=\theta^i\wedge\theta^j.
$$

例如 $\theta^{03}\wedge\theta^1=-\mathrm{vol}_W$、$\langle\theta^{03},\theta^{03}\rangle=\sigma$，给第二个符号；其余同理。这三个系数是所给三维载体上一个二形式的完整坐标，Hodge 把它送到同载体的一形式。若另供带余标架 $(\theta^0,\theta^1,\theta^2,\theta^3)$ 和余度规 $\operatorname{diag}(-1,1,1,1)$ 的 $3+1$ 载体，$\sigma=-1$ 的上述模型正是其 $013$ 子载体。固定 $\theta^0,\theta^1$ 且将 $\theta^3\mapsto\theta^2,\theta^2\mapsto-\theta^3$ 的空间旋转，把 $\theta^{03},\theta^{13}$ 送到 $\theta^{02},\theta^{12}$。所以这个混合子空间不在全空间旋转群 $SO(3)$ 下不变；所选 $2+1$ 载体内的 Hodge 同构不是该全空间群的三轴表示。

同一比较中，若另供实四维余空间上的 $F=\sum_{i<j}F_{ij}\theta^{ij}$，外积运算给

$$
F\wedge F=2(F_{01}F_{23}-F_{02}F_{13}+F_{03}F_{12})\,
\theta^0\wedge\theta^1\wedge\theta^2\wedge\theta^3.
$$

这里 $F\wedge F=0$ 等价于 $F$ 可写为两个一形式的外积，允许 $F=0$。这是 [Conrad §8 的可分解外积背景](../../../Library/Geometry/conrad2026exterior.md)在四维的坐标计算：非零时置换指标使 $F_{01}\ne0$，零平方条件恰使

$$
F=\left(\theta^0-\frac{F_{12}}{F_{01}}\theta^2-\frac{F_{13}}{F_{01}}\theta^3\right)
\wedge\left(F_{01}\theta^1+F_{02}\theta^2+F_{03}\theta^3\right).
$$

反向由重复外因子给零。采用 [Tong §2.4.2、式 (2.87)](../../../Library/Geometry/tong2021general.md)的 $c=1$ 电磁符号 $E_i=-F_{0i}$、$B=(F_{23},F_{31},F_{12})$，上述平方系数为 $-2E\cdot B$；这不是任何经典协方差。若进一步写 $F=d\mathscr A$，须另供流形和局部或全局的一形式势 $\mathscr A$，其范围依供给而定。

与五态源比较时，只按假设 18.3 另给有类型的读出、群作用及所需交织；没有这些映射，$u_i$、函数 $x,z,y$、矩 $X,Z,Y$ 和 $F_{0i}$ 没有等同关系。三维光滑流形上的 $1,3,3,1$ 是每点 $\Lambda^kT_s^*M$ 的秩；$\Omega^k(M)$ 是光滑截面空间，不能把这些秩报成整空间维数。此接口未供应 Maxwell 方程、传播态、物理空间、度量提取或引力／颜色实现。

## 22. 当前 null 纤维、相容细化与独立一阶 jet

**定义 22.1（当前读口的实际纤维）。** 给定非空实际制备域 $D\subseteq\mathcal D$ 与 $b\in B_{\rm obs}(D)$，定义

$$
\mathcal N_D(b)=\{p\in D:B_{\rm obs}p=b\}.
$$

“当前 null”指这份实际纤维，或在声明光滑层／可行路径后取其切方向；不能把它直接当作概率模式。任取 $p\in\mathcal N_D(b)$，环境仿射纤维为 $p+\ker B_{\rm obs}$，$\mathcal N_D(b)=D\cap(p+\ker B_{\rm obs})$ 才是实际域。由数学引文 1.2，$D=\mathcal D$ 时它是可能退化的闭线段；单点无非零实际纤维差。双侧可微路径在零质量坐标上导数为零，单侧可行导数则有相应非负限制。因此代数核 $\mathbb Rh$ 不自动等于每个边界点的可行切集，更不是空态指示、常函数或根。

**假设 22.2（内生提取和保留旧读口的细化）。** 静态对象、内嵌观察者、局部概率提取与允许更新均采用定义 8.1；观察状态应包含使用的记忆和策略。若额外写 $K_\infty=\lim_n\mathscr D^nK_0$，须给 $\mathscr D$ 的定义域、承载该极限的拓扑或序及收敛条件；若写 $\mathscr D K_\infty=K_\infty$，须独立供给固定点条件或推导。存在、唯一、最大各是不同命题，符号本身不提供其中任何一项。内生动作与摘要相容使用[边界动力学卷 §41.1、式 (41.3)–(41.3a)](RECURSIVE_RELATIONAL_OBSERVATION_BOUNDARY_DYNAMICS.md)的实际像和策略下降合同；递归是否真正细化使用同卷 §31.3，而不以重复命名当前核为新信息。

一个有限来源细化须另供非空有限载体 $\widetilde\Sigma$、映射 $\pi:\widetilde\Sigma\to\Sigma$、非空实际域 $\widetilde D\subseteq\Delta(\widetilde\Sigma)$ 和其中的非负归一化律 $q$，满足

$$
(\pi_*q)_s=\sum_{\pi(t)=s}q_t,\qquad
\pi_*q=p\in D,\qquad
\widetilde B_{\rm old}=B_{\rm obs}\pi_*.
$$

须说明该相容条件适用于一个已给律还是整个来源族；若要求覆盖全部旧制备，还须 $`\pi_*(\widetilde D)=D`$。附加读口 $\widetilde R$ 及其取得操作另行给出，新摘要取 $(\widetilde B_{\rm old}q,\widetilde R(q))$。它严格细化旧摘要，意指存在 $q,q'\in\widetilde D$，旧摘要相同而 $\widetilde R(q)\ne\widetilde R(q')$。若还保留旧随机动态 $T$，则给列随机 $\widetilde T$ 及前向可行域，要求

$$
\pi_*\widetilde Tq=T\pi_*q\quad(q\in\widetilde D).
$$

若任务只保留当前观察，可改为两边经 $B_{\rm obs}$ 后相等，但须明确这是较弱合同。完整回复、后继摘要、成本和策略仍按[观察者与算术关系卷 A-19.4](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md)、本卷数学引文 19.4 处理；一步均值相容不能替代联合操作核。

这些假设没有从 $\mathbb Rh$ 生成新五态概率律。若输入仅为原线段的一个参数，$C^1$ 重编码的微分秩至多一；边场、多节点联合律或 jet 需要另外声明的来源。未来的 $PTh$ 灵敏度、实际非零差和回路算子的范围直接采用数学引文 19.4、定义 20.1 与命题 20.3。一般随机回路算子差不因此成为可逆 holonomy 或连接曲率。

**命题 22.3（固定占据场中的四参数一阶信息）。** 在额外指定的参数域 $U=(-1,1)^3$ 上，给定平滑五态律场族

$$
\begin{gathered}
\Theta_0=\{(a,b_1,b_2,b_3)\in\mathbb R^4:
|a|+|b_1|+|b_2|+|b_3|<1/8\},\\
p_\circ=(3/8,1/8,1/4,1/8,1/8),\qquad
\chi_\theta(s)=a+b_1s_1+b_2s_2+b_3s_3,\qquad
p_\theta(s)=p_\circ+\chi_\theta(s)h.
\end{gathered}
$$

每个 $p_\theta(s)$ 都严格正且归一化，并在整个 $U$ 上满足

$$
B_{\rm obs}p_\theta(s)=(1,1/4,1/4,1/4).
$$

点态映射 $\theta\mapsto p_\theta(0)$ 的微分秩一，只依赖 $a$；若另给精确一阶 jet 读口，则

$$
j^1_0\chi_\theta=(\chi_\theta(0),\partial_1\chi_\theta(0),
\partial_2\chi_\theta(0),\partial_3\chi_\theta(0))=(a,b_1,b_2,b_3)
$$

的像是四维开集 $\Theta_0$。特别地，$\theta=0$ 与 $\theta=(0,1/32,0,0)$ 的中心完整律及全部占据场相同，中心一阶导数不同。这不违反固定单点纤维的秩界：jet 读口的源是整个已供给场族，不能经中心概率律因子化。

证明。对 $s\in U$，有 $|\chi_\theta(s)|\le|a|+\sum_i|b_i|<1/8$，故四个变化质量 $3/8+\chi,1/8-\chi,1/8-\chi,1/8+\chi$ 均正，第三分量固定为 $1/4$。$\sum h_s=0$ 保持总质量一，$B_{\rm obs}h=0$ 保持所列整个占据场。中心评价为 $p_\circ+ah$，其微分为 $(\dot a,\dot b)\mapsto\dot a h$；直接求导给 jet 恒等映射。两指定参数都在 $\Theta_0$ 内，且 $\partial_1p_\theta(0)$ 分别为 $0,h/32$，因子化若存在就会把相同中心律送到两个不同 jet，矛盾。

在同一域上取实标量势的一形式 $\mathscr A_\theta=d\chi_\theta=\sum_i b_i\,ds_i$，则 $d\mathscr A_\theta=0$。这里可直接由常系数求导，也符合 [Tong §2.4.1–§2.4.3](../../../Library/Geometry/tong2021general.md) 的 $d^2=0$。一般光滑流形上只要 $\chi$ 是全局 $C^2$ 实函数，全局恰当的 $d\chi$ 仍闭且所有分段 $C^1$ 闭路径积分为零；拓扑不把它变成非零场强。局部势或另给的非恰当连接是另一合同。

该构造的 $\chi_\theta$ 是相对于 $p_\circ$ 的概率纤维系数，既非定义 19.1 的函数系数，也非 $\kappa-XY$；此处 $\kappa=1/8+\chi_\theta$。参数空间 $U$ 不因这个公式成为物理空间，精确导数读取、共同多点采样律与场动力学均须另供。命题消费[局部源分裂卷 §§1–3](AURIC_FIB_ATOM_LOCAL_SOURCE_SPLITTING_AND_READOUT_GEOMETRY.md)的质量和可行路径合同，以这个正律场给出点态秩与 jet 秩的具体分离，不宣称额外内禀单点自由度。∎

## 追加锚（本行以下为增补区）

## 23. 能量倾斜的归一化关联流与有向环实现

**定义 23.1（指定能量、评价与两种端点表）。** 在定义 21.1 的支持顺序 $(0,1,2,3,13)$ 中，给定与概率律无关的实函数 $H:\Sigma\to\mathbb R$。若称其为能量，另指定能量单位；模式列表本身不供应这个解释。直接使用定义 19.1 的评价矩阵及[基础公式卷数学引文 2.2、7.2、命题 7.3–7.4](AURIC_FIB_ATOM_PYRAMID_FOUNDATIONAL_FORMULAS_AND_RELATIONS.md)，记

$$
\begin{aligned}
H&=E_0+\epsilon_1x+\epsilon_2z+\epsilon_3y+Jxy,\\
c_H&=(E_0,\epsilon_1,\epsilon_2,\epsilon_3,J)^{\mathsf T},\\
\mathbf H&=(H_0,H_1,H_2,H_3,H_{13})^{\mathsf T}=Ec_H\\
&=(E_0,E_0+\epsilon_1,E_0+\epsilon_2,E_0+\epsilon_3,
E_0+\epsilon_1+\epsilon_3+J)^{\mathsf T},\\
\mathcal E_H(p)&=\mathbf H^{\mathsf T}p
=E_0+\epsilon_1X+\epsilon_2Z+\epsilon_3Y+J\kappa,\\
J&=H_{13}+H_0-H_1-H_3=\mathbf H^{\mathsf T}h.
\end{aligned}
$$

五函数基的唯一性取决于已经固定的 Boolean 坐标；它不是任意换基下的不可约性，也不是物理相互作用的存在证明。$J<0$ 恰比较 $H_{13}+H_0<H_1+H_3$，不单独保证联合态比每个单态更低、动力学稳定或实际结合。$xy$ 是状态函数，$\kappa=\mathbb E_p[xy]$ 是无量纲概率；$Jxy$ 是指定函数的相互作用项，$J\kappa$ 是其期望。固定非退化占据纤维中，目标期望的斜率、乘积补全残差及 minimax 误差直接取上述基础卷以 $f=H$ 的结果，不另证一套能量恢复定理。

定义 21.3 的 $T_{\rm end}=(X,Y,\kappa)$ 在此明确指**无条件**端点联合表，按 $x,y=0,1$ 为行、列：

$$
W_{\rm end}=\begin{pmatrix}p_0+p_2&p_3\\p_1&p_{13}\end{pmatrix}
=\begin{pmatrix}1-X-Y+\kappa&Y-\kappa\\X-\kappa&\kappa\end{pmatrix}.
$$

它的总质量为一，左上格包含中态 $2$。$r=1-Z>0$ 时，条件于 $s\ne2$ 的表另为

$$
W_{\rm base}=\frac1r\begin{pmatrix}p_0&p_3\\p_1&p_{13}\end{pmatrix}.
$$

两表的行列式分别为 $\kappa-XY$ 和 $\Delta/r^2$；后者的四格交叉比为 $p_0p_{13}/(p_1p_3)$。这补明定义 21.3 的端点表所用事件，保持其原来的无条件协方差与条件协方差公式。取对数需要对应四格严格正。[隐藏关系卷 C-7.7–C-7.8](AURIC_FIB_ATOM_HIDDEN_RELATIONS_STATISTICS_PHASE_AND_SEAMS.md)中消去中态后的有效对数系数属于 $W_{\rm end}$，不能直接替代 $W_{\rm base}$ 的交叉比或这里的 $J$。

**假设 23.2（Gibbs 比较及预先指定的检验对象）。** 给定非空、固定有限支持 $S\subseteq\Sigma$、有限 $H_s$ 和有限实参数 $\beta$，在 $S$ 外取零质量，在 $S$ 上采用计数基准测度及

$$
\mathcal Z_H(\beta)=\sum_{s\in S}e^{-\beta H_s},\qquad
\pi_s=\frac{e^{-\beta H_s}}{\mathcal Z_H(\beta)}.
$$

这是 [Jaynes，式 (2-9)–(2-15)](../../../Library/StatisticalMechanics/jaynes1957information.md)的有限指数族作为本节的比较律。若 $H$ 有能量单位，$\beta$ 有其倒数单位；正温度的自由能解释另外要求 $\beta>0$ 及温标、环境和单位的独立对应。$H\mapsto H+C$ 不改变 $\pi$，只改变配分函数的因子和期望能量的共同零点。以下反演固定 $\beta\ne0$；若连 $\beta$ 也未知，则 $H\mapsto aH,\beta\mapsto\beta/a$ 的尺度不能由同一律辨识。$\beta=0$ 时有限 $H$ 仅给 $S$ 上均匀律。

对全支持严格正五态律，固定 $\beta\ne0$ 后总能取 $H_s=-\beta^{-1}\log p_s+C$。在 $H_0=0$ 的规范中，定义 23.1 的字典给

$$
\epsilon_i=-\beta^{-1}\log(p_i/p_0)\quad(i=1,2,3),\qquad
\beta J=-\log\frac{p_0p_{13}}{p_1p_3}.
$$

故自由拟合五个能级只重写原有四维正概率律，不确认能量、平衡或跃迁率。零概率不能由全支持有限能级给出，须另定支持或明确采用无限能级的极限；支持缩小后也不沿用全五函数系数的可辨识性。用 Gibbs 律提出可被否定的模型时，$S,H,\beta$、允许的控制参数及能量／率的意义须独立于待检验律预先给定，再比较全部状态比，而不是仅比较一个交叉比。样本误差和物理标定不由精确律公式提供。

对固定支持、固定 $\beta\ne0$，仅令 $J$ 通过 $Jxy$ 变化且其余能量系数固定时，所引对数配分函数导数给

$$
-\beta^{-1}\partial_J\log\mathcal Z_H=\mathbb E_\pi[xy],\qquad
\partial_J(-\beta^{-1}\log\mathcal Z_H)=\mathbb E_\pi[xy].
$$

这里读出的是该指定 Gibbs 族对耦合的响应，不是任意非平衡 $p$ 的实验性定义。$\beta>0$ 时括号才采用正温度自由能的称呼。

**假设 23.3（归一化动态与守恒的量词）。** 对固定列随机矩阵 $T$，离散动态是 $p'=Tp$；对固定非负非对角元、行和为零的生成元 $Q=(q_{ij})$，连续动态是 $\dot p=Q^{\mathsf T}p$。定义 19.2 的对偶输运给：指定常时能量对**每个**初律守恒分别要求

$$
\mathbf H^{\mathsf T}T=\mathbf H^{\mathsf T},\qquad Q\mathbf H=0.
$$

只需在五个纯态检验这些线性恒等式。减去共同 $E_0$ 后应使用评价列

$$
e_H=(0,\epsilon_1,\epsilon_2,\epsilon_3,\epsilon_1+\epsilon_3+J)^{\mathsf T},
$$

而非系数列 $(0,\epsilon_1,\epsilon_2,\epsilon_3,J)^{\mathsf T}$。联合概率及边缘总量对应的评价列分别为 $e_\kappa=(0,0,0,0,1)^{\mathsf T}$、$e_{X+Y}=(0,1,0,1,2)^{\mathsf T}$，须各自代入相应条件。

一份律 $\pi$ 平稳只要求 $T\pi=\pi$ 或 $Q^{\mathsf T}\pi=0$，因此沿这份律所有常时目标均值不变；这不同于所有初律的守恒。详细平衡另要求 $\pi_iT_{ji}=\pi_jT_{ij}$，或 $\pi_iq_{ij}=\pi_jq_{ji}$。在严格正 Gibbs 律与双向正率下，后式要求 $q_{ij}/q_{ji}=e^{-\beta(H_j-H_i)}$；若允许缺边，两个方向的零流也须相等。平稳不逆推此逐边条件，使用定理 3.2、命题 3.3 的已有环流边界。有限不可约链的全初律守恒标量只能是常数：在最大值状态，邻点值的非正差之加权和为零强制所有可达邻点也取最大值；连通传播即得结论。可约的本五边图须按实际活动类处理，不能假称不可约。

仅供应 $1\rightleftarrows3$ 两率时，其余质量固定，$\dot p_1=-k_{13}p_1+k_{31}p_3=-\dot p_3$ 是一个归一化线性交换模型；若两率同为 $k$，则 $p_1-p_3$ 按 $e^{-2kt}$ 衰减。它不从模式标签推出。人口反应 $1+3\rightleftarrows13$ 的浓度方程则有 $\dot c_1=\dot c_3=-R,\dot c_{13}=R$，总粒子浓度变化为 $-R$；单个系统的五态概率不能照搬。反应浓度与粒子数主方程的区分使用 [Maas–Mielke，§1、§2.1–§2.3](../../../Library/StatisticalMechanics/maasmielke2020reaction.md)。即使补上 $\dot p_0=R$，取 $R=p_1p_3-p_{13}$、$p=(0,1/4,0,1/4,1/2)$ 仍给 $\dot p_0=-7/16$，违反单纯形边界。归一化与非负性都是必要条件。

本节采用另行规定的二对二关联律 $1+3\rightleftarrows0+13$，而不把反应对视为单个样本同时占据的状态。取常数 $k_+,k_->0$，定义

$$
a=k_-p_0p_{13},\qquad b=k_+p_1p_3,\qquad v=b-a,\qquad
\dot p=vh,\qquad \lambda=\log(k_-/k_+).
$$

这里 $t$ 是同一指定参数，$k_\pm$ 的单位是其倒数。若消费定义 23.1 的指定能量，额外要求 $\lambda=\beta J$，能量与率比的对应是模型条件。定理 23.4 给该多项式律在原有向图上的单系统概率实现；率依赖当前完整律，不把它称为一个对所有初律相同的固定线性 Markov 生成元。

**定理 23.4（能量倾斜纤维的有界率实现与非均匀 Gibbs 环流）。** 对假设 23.3 的关联律，固定 $0\le Z<1$、$r=1-Z$、$0<X,Y<r$，令 $[l,u]$、$p_\kappa$ 采用数学引文 1.2。每个 $\kappa(0)\in[l,u]$ 有唯一全局解，保持 $X,Z,Y$ 及总质量，且在 $t>0$ 四个底格严格正。它趋向唯一内部平衡 $\kappa_*$，满足

$$
\frac{p_{*,0}p_{*,13}}{p_{*,1}p_{*,3}}=e^{-\lambda},\qquad
|\kappa(t)-\kappa_*|\le e^{-r\min(k_+,k_-)t}|\kappa(0)-\kappa_*|.
$$

令 $\mathcal A(\kappa)=D(p_\kappa\Vert p_{XY/r})$ 采用假设 15.1 的共同支持约定，令 $\Psi(\kappa)=\mathcal A(\kappa)+\lambda\kappa$。在四底格内部，

$$
\frac{d\Psi}{dt}=-(a-b)\log(a/b)\le0,
$$

等号恰在 $\kappa=\kappa_*$；并且 $\Psi(\kappa)-\Psi(\kappa_*)=D(p_\kappa\Vert p_{\kappa_*})$。所以至该**受限纤维平衡**的 KL 下降；当 $\lambda\ne0$ 时不声称至原条件独立点的 $\mathcal A$ 本身下降。若 $\lambda=\beta J$，$\Psi$ 与 $\beta\mathcal E_H-S(p)$ 相差一个纤维常数，$S(p)=-\sum_sp_s\log p_s$，而

$$
\frac{d\mathcal E_H}{dt}=Jv.
$$

故这项熵下降不等于能量守恒。单个交叉比也不保证 $p_{\kappa_*}$ 等于预先固定全部一体能级的无约束 Gibbs 律；一般需为固定的 $X,Z,Y$ 另加拉格朗日乘子。

在定义 2.1 的原五边次序，取

$$
\begin{gathered}
f=(a,b,a,b,0),\\
q_{01}=k_-p_{13},\quad q_{1,13}=k_+p_3,\quad
q_{13,3}=k_-p_0,\quad q_{30}=k_+p_1,\quad q_{02}=0.
\end{gathered}
$$

其余非对角率为零，对角率为负行和。这些率在整个闭单纯形有界，即使某个底格为零也无除法奇点；每条边有 $f_{ij}=p_iq_{ij}$，且 $Bf=vh$。对每份确定的解 $p(t)$，$Q(p(t))$ 给一个非爆炸的非齐次有限态 Markov 实现；解处于平衡时才冻结为相应常生成元。不能免费取得未知律的完整值来执行这些率。

在内部平衡，$a=b>0$，故 $f=a\mathbf c$。这是反应的正反向通量平衡，同时在单状态有向图上有严格正单向环流，缺少的反向率使详细平衡失败。一个全支持实例为

$$
\begin{gathered}
k_+=2,\quad k_-=1,\quad \beta=1,\quad E_0=\epsilon_1=\epsilon_2=\epsilon_3=0,
\quad J=-\log2,\\
p_*=(1,1,1,1,2)/6,\quad (X,Z,Y)=(1/2,1/6,1/2),\quad
\mathcal Z_H=6,\quad f_*=(1,1,1,1,0)/18.
\end{gathered}
$$

它恰是这份完整 $H$ 的 Gibbs 律，$\Psi$ 导数为零，单向每边仍有 $1/18$ 流；Gibbs 表示、单律平稳、反应平衡与逐边详细平衡因而有不同结论。

证明。数学引文 1.2 的 $\mathbf1^{\mathsf T}h=0$、$Ah=0$ 给归一化及占据不变。若 $p_0$ 或 $p_{13}$ 为零，则 $a=0$，该零格导数为 $b\ge0$；若 $p_1$ 或 $p_3$ 为零，则 $b=0$，该零格导数为 $a\ge0$；$p_2$ 固定。多项式向量场局部 Lipschitz，闭单纯形正向不变且紧，故解唯一并全局存在。在非退化纤维上 $v(l)>0,v(u)<0$，且

$$
v'(\kappa)=-k_+(p_1+p_3)-k_-(p_0+p_{13})
\le-r\min(k_+,k_-)<0.
$$

这给唯一内部根、端点立即入内及内点不能出界。对 $w=\kappa-\kappa_*$ 用中值公式得 $(w^2)'\le-2r\min(k_+,k_-)w^2$，积分即所列全时界。若 $X$ 或 $Y$ 取 $0,r$，纤维退化为单点且反应两乘积均零；该边界不属于内部对数或收敛率的断言。

消费假设 15.1 的已有导数，$\Psi'=\log(p_0p_{13}/(p_1p_3))+\lambda=\log(a/b)$，再乘 $\dot\kappa=b-a$ 给耗散式。对数严格递增给符号与等号。由 $p_{\kappa_*}$ 的交叉比，$D(p_\kappa\Vert p_{\kappa_*})$ 对 $\kappa$ 的导数同为 $\log(a/b)$，在 $\kappa_*$ 同取零，给上述差值恒等式。这里是 [Maas–Mielke 定理 2.2 及式 (2.9)–(2.12)](../../../Library/StatisticalMechanics/maasmielke2020reaction.md)的一反应熵机制的具体应用；一般熵梯度结论不另立。相应正迁移率是 $\mu=(a-b)/(\log a-\log b)$，在 $a=b$ 以 $\mu=a$ 连续延拓；倾斜势满足 $v=-\mu\Psi'$。第十五节的未倾斜公式取 $\lambda=0$，其证明和结论原样适用。

已有熵导数为 $S'=-\mathcal A'$，而定义 23.1 给 $\mathcal E_H'=J$，所以 $\beta\mathcal E_H-S$ 与 $\Psi$ 的导数相等。$Z=0$ 时固定零格始终省略，四底格内部仍可微；$t=0$ 的端点只用熵的连续延拓，不声称对数导数有限。这个封闭概率模型没有环境能量项；若解释为放热反应，还须另给环境及其交换平衡，不能从 $Jv$ 自动推出整个物理系统的守恒。

原图上的边界恒等式直接取定理 2.2。定理 15.2 已分类全部非负交通；这里对应其最小交通加上 $\min(a,b)\mathbf c$，不是新的交通分类。四条显示率乘各自起点概率即为 $f$，每条率至多 $\max(k_+,k_-)$。因沿解连续且全局有界，直接采用定理 2.4 的有限率实现与前向方程唯一性；这也覆盖端点初态。叶边率零符合命题 3.3。平衡时 $p_{*,0}q_{01}=a>0$ 而 $p_{*,1}q_{10}=0$，故不满足详细平衡；所列实例以权重 $(1,1,1,1,2)$ 归一化，两个反应流均为 $1/18$。平稳环流这一一般障碍已由定理 3.2 给出，这里增加的是非零 $J$、受限平衡及边界有界率的同一实现。

最后，区分本非线性动态与冻结的 $Q(p_*)$：在整个非线性族上，$\dot{\mathcal E}_H=Jv$ 对所有初律恒零恰当且仅当 $J=0$，一体均值均守恒。对固定 $Q(p_*)$ 却须在整个活动方环取常能级，即 $\epsilon_1=\epsilon_3=J=0$，而孤立的 $2$ 允许任意 $\epsilon_2$；这是其四条正边上的 $Q\mathbf H=0$ 逐项所迫。上述 $J=-\log2$ 因而只有指定平稳律的均值不变，没有全初律能量守恒。

更一般地，若一个固定随机核在全五态单纯形上同时保持三个 Boolean 均值，则从每个纯态出发，输出每个 Boolean 位的期望仍为原来的 $0$ 或 $1$，迫使三个输出位逐个确定。三个位区分全部五态，故此核只能为恒等。固定生成元版本由其随机半群同理得到零生成元。这是本应用为何需要律依赖或另供多人系统的边界，不把第十八节的“均值闭合”误换成“均值恒定”。∎

**假设 23.5（同一应用的连接比较接口）。** 定理 23.4 只供应概率、指定能量和有向流。要另谈曲率，须按假设 18.3 供给底流形、向量丛、群作用、读出以及保留所需操作的对应；概率占据 $\kappa$ 不被定义成曲率。作为比较，给光滑底流形、矩阵 Lie 群 $G$ 的表示与局部 $C^2$ 连接一形式 $\mathscr A$，取列截面约定 $D=d+\mathscr A$。定义

$$
\mathscr F=d\mathscr A+\mathscr A\wedge\mathscr A,\qquad
[D_1,D_3]\psi=\mathscr F_{13}\psi,\qquad
\mathscr F_{13}=\partial_1\mathscr A_3-\partial_3\mathscr A_1+[\mathscr A_1,\mathscr A_3].
$$

规范取 $\psi'=g^{-1}\psi$、$\mathscr A'=g^{-1}\mathscr A g+g^{-1}dg$，则 $\mathscr F'=g^{-1}\mathscr Fg$。离散版本须另供可逆边输运 $U_{u\to v}$，沿路径按后边左乘组成；回路乘积才是相应 holonomy。若这些边来自上述光滑连接的平行方程 $\dot\psi=-\mathscr A(\dot\gamma)\psi$，沿 $+1,+3,-1,-3$ 小矩形且边长以有界非零比例趋零时，起点标架中

$$
U_{13}=I-a_1a_3\mathscr F_{13}+o(a_1a_3).
$$

这是带定向与符号的连续极限，非任意晶格上的精确差分式。直接以 $\Delta_1\mathscr A_3-\Delta_3\mathscr A_1+[\mathscr A_1,\mathscr A_3]$ 定义离散数组时，必须另外说明格点、乘积及规范变换，不能据此宣布它是该回路乘积或规范协变量。定义 19.3 的一般随机输运并未供应逆、连接或这些光滑极限。

标量 $U(1)$ 取 $\mathscr A=i\,d\chi$、全局实 $C^2$ 函数 $\chi$ 时，命题 22.3 的 $d^2=0$ 及闭路积分结论给 $\mathscr F=0$ 和恒等 holonomy；交换差分下的标量恰当梯度同样无旋。非阿贝尔的 $\mathscr A=d\chi$ 若 $\chi=s_1T_1+s_3T_3$、$[T_1,T_3]\ne0$，却有 $\mathscr F_{13}=[T_1,T_3]$；它不是纯规范的一般形式。真正的 $\mathscr A=g^{-1}dg$ 由 $d(g^{-1})=-g^{-1}(dg)g^{-1}$ 给 $\mathscr F=0$。平坦与全局平凡另须区分：圆周上的 $i\alpha\,d\theta$ 曲率零，而本平行约定的闭路因子为 $e^{-2\pi i\alpha}$；$\alpha\notin\mathbb Z$ 时非恒等，它没有全局单值实势。这个例子没有把全局恰当梯度变成非零局部场强。外微分背景仍用[本卷命题 22.3 所引 Tong](../../../Library/Geometry/tong2021general.md)，非交换项由此处声明的矩阵连接计算。

**假设 23.6（能量、光锥及内部旋转的变分比较）。** 在假设 23.5 之外，若比较规范场能量，另取 $3+1$ 平直时空、$c=1$、度规 $\eta=\operatorname{diag}(+,-,-,-)$，紧群代数上的正定不变实内积 $\langle\ ,\ \rangle$、耦合常数 $g_c>0$，并规定 Lagrangian

$$
\mathcal L_{\rm YM}=-\frac1{4g_c^2}\langle\mathscr F_{\mu\nu},\mathscr F^{\mu\nu}\rangle.
$$

内部内积可对反 Hermitian 矩阵取适当归一化的 $-\operatorname{Tr}(AB)$，不能不声明约定就把任意迹当作正内积。置 $E_i=-\mathscr F_{0i}$、$B=(\mathscr F_{23},\mathscr F_{31},\mathscr F_{12})$；对这份作用量的 Hilbert 张量，采用给出正 $T_{00}$ 的 $+---$ 约定，

$$
\begin{aligned}
\langle\mathscr F_{\mu\nu},\mathscr F^{\mu\nu}\rangle
&=2(\|B\|^2-\|E\|^2),\\
T_{\mu\nu}&=g_c^{-2}\left(-\langle\mathscr F_{\mu\alpha},\mathscr F_\nu{}^\alpha\rangle
+\tfrac14\eta_{\mu\nu}\langle\mathscr F_{\alpha\beta},\mathscr F^{\alpha\beta}\rangle\right),\\
T_{00}&=\frac{\|E\|^2+\|B\|^2}{2g_c^2}\ge0.
\end{aligned}
$$

这里复用 [Tong，Chapter 6 式 (6.1)–(6.3)、(6.16)–(6.18)](../../../Library/Quantum/tong2006qft.md)的 Abelian 作用量与 Hamiltonian 区别；给定正内部内积后按相同指标收缩得到显示式。例如 $E\perp B$、$\|E\|=\|B\|>0$ 时 Lorentz 收缩为零而 $T_{00}>0$。因此作用量中的 $\mathscr F_{\mu\nu}\mathscr F^{\mu\nu}$ 不是正场能，单个空间分量的平方也只是指定场能中的一项。局部能动守恒还需该 Lagrangian 的无外源场方程；有物质耦合时守恒的是含物质交换的总张量。积分能量守恒须有限能量和空间边界通量为零或无穷远衰减条件。

光锥比较另限 $1+1$ 维，保持 $\eta=\operatorname{diag}(+,-)$，给实 $C^2$ 标量场和 $C^1$ 势，$\mathcal L=\tfrac12\partial_\mu\phi\partial^\mu\phi-V(\phi)$，$x^\pm=(t\pm x)/\sqrt2$，故 $\eta_{+-}=1$。按 [Tong Chapter 1 式 (1.42)–(1.46)](../../../Library/Quantum/tong2006qft.md)的应力张量 $T_{\mu\nu}=\partial_\mu\phi\partial_\nu\phi-\eta_{\mu\nu}\mathcal L$ 作坐标变换，得

$$
T_{++}=(\partial_+\phi)^2,\quad T_{--}=(\partial_-\phi)^2,\quad T_{+-}=V(\phi),\qquad
T_{tt}=\frac{T_{++}+T_{--}+2T_{+-}}2,\quad
T_{tx}=\frac{T_{++}-T_{--}}2.
$$

这些是下标分量；$T^{0x}=-T_{tx}$，能流符号不省略升降指标。守恒要求满足 $\Box\phi+V'(\phi)=0$；总能量或动量还需可积及端点无净通量。自由无质量且 $V=0$ 时混合项零；非零势函数不保证在每个场值上 $V(\phi)\ne0$，更不推出五态的模式交换机制。这里的混合张量分量不是 $xy$ 或 $p_{13}$。

内部旋转比较另给 $3+1$ 维复场 $\Phi=(\phi_1+i\phi_3)/\sqrt2$、$\mathcal L=\partial_\mu\Phi^*\partial^\mu\Phi-V(|\Phi|^2)$，同取 $+---$。全局变换 $\delta\Phi=i\theta\Phi$ 的流及能量为

$$
j^\mu=\phi_1\partial^\mu\phi_3-\phi_3\partial^\mu\phi_1,\qquad
T_{00}=\frac12\sum_{a=1,3}\big((\partial_t\phi_a)^2+|\nabla\phi_a|^2\big)+V(|\Phi|^2).
$$

[Noether，§1 定理 I 及其 on-shell 限定](../../../Library/Geometry/noether1918invariant.md)，结合 [Tong 式 (1.60)–(1.63)](../../../Library/Quantum/tong2006qft.md)的该复场应用，给满足 Euler–Lagrange 方程时 $\partial_\mu j^\mu=0$；$Q=\int j^0\,d^3x$ 的守恒另需可积和边界 $j$ 通量为零。$V\ge0$ 时显示能量非负；一般势不自动有此性质。流包含导数及旋转生成元，守恒荷不是 $\phi_1\phi_3$，Lorentz 缩并的导数平方也不是显示的正平方和。

上述场合同只是定理 23.4 中“能量”一词的分别类型化比较，没有提供从概率、环流、内部振幅或连接之间的对应。若再写 Einstein 方程，还须另供 Lorentz 度规、协变物质作用量、按该度规变分的完整应力张量、场方程及相容的 $\nabla^\mu T_{\mu\nu}=0$；必要的守恒条件也不单独保证 Einstein 方程的解。$J\kappa$、概率占据或状态图回路均未供应这些数据，故本有限模型没有断言 Einstein 源或引力几何。

## 追加锚（本行以下为增补区）

## 24. 五边图的源标定碰撞与联合能量读口

**定义 24.1（带源的接地合同与既有消元对应）。** 在定义 2.1 的底层无向图上记 $O=0,L=1,T=2,R=3,J=13$，边为 $OL,OT,OR,LJ,RJ$；这些字母在图上标顶点，在 $\Sigma$ 上标模式，两种用途通过这份指定字典对应，不把顶点当作物理位置。一般消元允许有限无向无自环图，$c_{ij}=c_{ji}\ge0$，仅将正电导边计入连通性。取非空保留集 $B$、非空内部集 $I$，每个内部连通分量均有正电导边接到 $B$。$B$ 在本节是顶点集合，不是定义 2.1 的关联矩阵。固定实边界 $b=u_B$、源系数 $q=(q_B,q_I)$ 及电导，采用假设 9.2 的正 Laplacian $L$，声明

$$
\mathcal I(u;q)=\tfrac12u^{\mathsf T}Lu+q^{\mathsf T}u+g(q),\qquad
K=L_{II},\qquad K u_I+L_{IB}b+q_I=0.
$$

$g$ 是另给的、与 $u$ 无关的能量零点函数；不指定时本节取 $g=0$。若赋予单位，$c u^2$、$q u$、$g$ 必须有同一能量单位，比较不同来源时这些单位和零点保持共同标定。这里 $q$ 是 $+q^{\mathsf T}u$ 的系数。按假设 9.2 的下坡电流及向外散度，内部平衡为 $\operatorname{div}j=-q_I$；不能把它不加改号地称为该散度的正注入。边界响应定义为 $j_B=\partial_b\min_{u_I}\mathcal I$，包含 $q_B$，与单独的边电流有不同类型。

所用静态极小值直接复用[《响应三角形与内部记忆》theorem 8.1](AURIC_FIB_ATOM_RESPONSE_TRIANGLE_AND_INTERNAL_MEMORY.md)和[SchurMinimum 的二次型最小值](../../../D5/S3/Quantum/Matrix/SchurMinimum.lean) `schur_quadratic_is_least`。有源对应是在后者取保留向量 $(b,1)$、块

$$
A_{\rm aug}=\begin{pmatrix}L_{BB}&q_B\\q_B^{\mathsf T}&0\end{pmatrix},\qquad
B_{\rm aug}=\begin{pmatrix}L_{BI}\\q_I^{\mathsf T}\end{pmatrix},\qquad C=K,
$$

再将二次型乘 $1/2$ 并加 $g(q)$；实矩阵的极小点也为实向量。由此取得本应用的既有公式

$$
\begin{aligned}
u_I^*(b,q)&=-K^{-1}(L_{IB}b+q_I),\\
\Lambda&=L_{BB}-L_{BI}K^{-1}L_{IB},\\
W&=-L_{BI}K^{-1},\\
q_{\rm eff}&=q_B+Wq_I,\\
C(q)&=-\tfrac12q_I^{\mathsf T}K^{-1}q_I,\\
V(b;q):=\min_{u_I}\mathcal I&=\tfrac12b^{\mathsf T}\Lambda b+q_{\rm eff}^{\mathsf T}b+C(q)+g(q),\\
j_B(b;q)&=\Lambda b+q_{\rm eff}.
\end{aligned}
$$

接地条件确实给 $K>0$：将内部向量在 $B$ 上补零，零二次能量迫使每个正边分量取同一常数，接到零边界又迫使它为零。若某分量完全没有边界，则 $Lu=-q$ 在该分量可解恰要求源和为零，解只定到常数；不满足时，沿该分量的常数平移使泛函无下界。闭图要逐分量平衡，只有总和为零不足以处理不连通图；非负源在闭图上因而只能为零。这是本有限合同的适用条件，不是对物质源的限制。

[Dörfler–Bullo，v1 式 (1.1)–(1.2)、(2.1)–(2.2) 和 Lemma 2.1](../../../Library/GraphInvariants/dorflerbullo2013kron.md)供应 Schur/Kron 与 accompanying matrix 的经典中间步骤。其原引理的边界至少有两个顶点；这里对单边界或多个内部块使用上述接地条件。接地最大值原理给 $K^{-1}_{ij}\ge0$，恰在 $i,j$ 属于同一内部正边连通分量时严格正：负极小值与非负右端不相容，非零非负右端的零极小值沿内部正边传播即与源矛盾。不同内部块的逆矩阵项为零。由 $L_{BI}\le0$ 及 $K\mathbf1_I+L_{IB}\mathbf1_B=0$ 得

$$
W\ge0,\qquad \mathbf1_B^{\mathsf T}W=\mathbf1_I^{\mathsf T},\qquad
\mathbf1_B^{\mathsf T}q_{\rm eff}=\mathbf1^{\mathsf T}q.
$$

列随机形式只表示这份静态源的非负重新分配，没有随机发射的附加解释。它也不把固定边界的不同内部块接成一块：全图连通仍可能有 $K^{-1}_{ij}=0$。

**定义 24.2（固定源、源族与能量规范的标定范围）。** 对定义 24.1 的全部 $b\in\mathbb R^B$，固定源的边界响应由 $(\Lambda,q_{\rm eff})$ 完全给出；绝对极小值还需 $C(q)+g(q)$。这些是不同任务的充分数据；只给一个源点的常数并不供应改变来源后的响应或导数。对固定 $L$ 及已知仿射控制族

$$
q_I(t)=q_{I0}+Q_I t,\qquad q_B(t)=q_{B0}+Q_Bt,\qquad t\in D\subseteq\mathbb R^m,
$$

边界任务使用 $q_{{\rm eff},0}$ 和 $R=Q_B+WQ_I$。若还需能量及其源导数，须保留已标定的整个 $g(q(t))$，以及

$$
\begin{gathered}
C_0=-\tfrac12q_{I0}^{\mathsf T}K^{-1}q_{I0},\qquad
\ell=-Q_I^{\mathsf T}K^{-1}q_{I0},\qquad
G_Q=Q_I^{\mathsf T}K^{-1}Q_I,\\
C(q(t))=C_0+\ell^{\mathsf T}t-\tfrac12t^{\mathsf T}G_Qt,\\
\nabla_t V=R^{\mathsf T}b+\ell-G_Qt+\nabla_t(g\circ q),\qquad
\nabla_t^2V=-G_Q+\nabla_t^2(g\circ q).
\end{gathered}
$$

导数在 $D$ 的开域及所示函数可微的条件下解释，Hessian 还需二次可微。若 $L$ 也变，须给相应的 $\Lambda(t),W(t),C(t)$ 及其导数，不能套用固定算子式。直接以 $q_I,q_B$ 为控制时，固定 $L,b$ 的包络导数分别为 $u_I^*+\partial_{q_I}g$ 和 $b+\partial_{q_B}g$。因此源依赖的加法项虽不影响边界电流，却可以改变源导数和联合能量。

对固定已知 $q_B$、实际允许的内部源集合 $\mathcal Q$，边界源识别要求

$$
\ker W\cap(\mathcal Q-\mathcal Q)=\{0\}.
$$

这是[观察者算术卷命题 A-19.4](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md)的实际纤维判据，不是 $W$ 列随机性的推论。若 $q_B$ 也未知，须改查 $(q_B,q_I)\mapsto q_B+Wq_I$ 的实际纤维。共同势原点平移 $u\mapsto u+h\mathbf1$、$b\mapsto b+h\mathbf1_B$ 使 $V$ 增加 $h\mathbf1^{\mathsf T}q$；边界电流不变。对加法源律该项的四角差为零，但任意源依赖的 $g$ 不必如此。固定源、全体电导乘 $a>0$ 时，$W$ 不变而 $K^{-1}$ 与 $C$ 除以 $a$，$\Lambda$ 乘 $a$；源分配本身不校准能量尺度。

**定理 24.3（本五边图的单源标定不能确定共同源能量）。** 在定义 24.1 的五边图取全部电导一，保留 $B=\{O\}$，内部次序 $(L,T,R,J)$，$q_B=0$、$g=0$，边界实值为 $b$。内部坐标向量 $e_L,e_R$ 不是模式概率。比较同一单位和能量零点下的两份源赋值，在全部实控制 $(a,c)$ 上取

$$
Q^{(A)}(a,c)=ae_L+ce_R,\qquad Q^{(B)}(a,c)=(a+c)e_L.
$$

两赋值对每个 $(a,c,b)$ 给完全相同的边界电流 $a+c$；在 $c=0$ 或 $a=0$ 的全部单源能量曲线上也完全相同。但同时启用两源时

$$
\begin{aligned}
V_A(b;a,c)&=b(a+c)-\tfrac38(a^2+c^2)-\tfrac14ac,\\
V_B(b;a,c)&=b(a+c)-\tfrac38(a^2+c^2)-\tfrac34ac,\\
V_B-V_A&=-\tfrac12ac.
\end{aligned}
$$

所以“全部边界电流加上各来源分别的全部能量标定”在这个实际源赋值域上仍不能下降为联合能量预测。若把同一五态模式的 $(x(s),y(s))$ 作为 $(a,c)$，令 $U_A(s)=V_A(b;x(s),y(s))$、$U_B(s)=V_B(b;x(s),y(s))$，则

$$
\begin{gathered}
U_A=(b-3/8)(x+y)-xy/4,\qquad
U_B=(b-3/8)(x+y)-3xy/4,\\
J_{U_A}=-1/4,\qquad J_{U_B}=-3/4,\qquad
\mathbb E_p(U_B-U_A)=-\kappa/2.
\end{gathered}
$$

这里期望使用同一实际律 $p$，$\kappa=p_{13}$；缺失的是源之间的配对，尚未改变概率律。它不同于固定一个能量函数再比较同占据均值、不同 $\kappa$ 的问题。

证明。由五条实际边组装内部块与其逆得

$$
K=\begin{pmatrix}2&0&0&-1\\0&1&0&0\\0&0&2&-1\\-1&0&-1&2\end{pmatrix},\qquad
K^{-1}=\tfrac14\begin{pmatrix}3&0&1&2\\0&4&0&0\\1&0&3&2\\2&0&2&4\end{pmatrix},
\qquad W=(1,1,1,1),\quad\Lambda=0.
$$

显示矩阵相乘为单位矩阵，$L_{BI}=(-1,-1,-1,0)$、$L_{BB}=3$。代入定义 24.1 的既有极小值公式，两源矩阵的 Gram 数据分别为

$$
G_A=\begin{pmatrix}3/4&1/4\\1/4&3/4\end{pmatrix},\qquad
G_B=\begin{pmatrix}3/4&3/4\\3/4&3/4\end{pmatrix}.
$$

$WQ$ 和两个对角元相等，非对角元不同；这正给相同电流、相同单源曲线与所列交叉差。模式代入只用 $x^2=x,y^2=y$；期望和 $J$ 的消费直接取定义 19.1、23.1 及[观察者算术卷命题 A-2.5](AURIC_FIB_ATOM_OBSERVER_AND_ARITHMETIC_RELATIONS.md)，不另证五函数分解。此处在 $B$ 被接地后，$T$ 独成内部块，$L,R,J$ 同在另一块，故 $K^{-1}_{LT}=0$ 而 $K^{-1}_{LR}=1/4>0$；全图连通并不替代这个内部支撑条件。

同一应用的一般加法源对应是：固定共同 $K$、共同零边界和 $g=0$，另给固定内部向量

$$
q(s)=q_0+x(s)q_1+z(s)q_2+y(s)q_3,\qquad
u(s)=-K^{-1}q(s),\qquad U(s)=-\tfrac12q(s)^{\mathsf T}K^{-1}q(s).
$$

消费[双线性 seam 卷 theorem 2.1 及 Q1–Q4](AURIC_FIB_ATOM_SEAM_BILINEAR_CURVATURE_AND_OUTPUT_FUTURE_QUOTIENT.md)的四角乘积差，以 $K^{-1}$ 收缩即给

$$
J_u=0,\qquad J_U=-q_1^{\mathsf T}K^{-1}q_3,\qquad
\Delta\mathbb E_p[U]=-q_1^{\mathsf T}K^{-1}q_3\,\Delta\kappa
$$

及同 $(X,Z,Y)$ 时相同的 $\mathbb E_p[u]$。最后一个差分比较固定源赋值、固定算子下的两份合法律，使用数学引文 1.2 的实际区间 $[\max(0,X+Y+Z-1),\min(X,Y)]$；非退化时能量期望识别 $\kappa$ 恰要求该交叉系数非零，单点纤维没有待识别参数。不同模式各换算子、不同来源各解不同边界问题、源律另有 $xy$ 项或额外 $g(q(s))$ 时，不能沿用此式。

对 $q_1,q_3\ge0$，定义 24.1 的逆矩阵支撑给精确条件

$$
J_U<0\quad\Longleftrightarrow\quad
\exists i,j\in I:\ (q_1)_i>0,\ (q_3)_j>0,
\quad i,j\text{ 属于同一内部正边连通分量}.
$$

否则 $J_U=0$；允许有符号源时不承诺此符号。负四角差只是指定能量的结合比较，没有距离导数或力的结论。一个共同场线性响应而能量有交叉项，是上述既有二次型的消费，并非场方程非线性的证据。若实际允许源域包含 $q_1,q_3,q_1+q_3$，已知这三个源的 $C$ 值即可由 $C(q_1+q_3)-C(q_1)-C(q_3)$ 恢复负交叉配对；本反例只缺这份联合标定，不否定极化。∎

**数学引文 24.4（其他边界选择与源摘要的对应）。** 本节消元并未将名称“空”赋予源。若明确仅在 $O$ 放源 $q$、取 $g=0$，并取 $I=\{O\}$、$B=(L,T,R,J)$，本图的 $K=3$。直接在[响应三角形卷 theorem 7.1](AURIC_FIB_ATOM_RESPONSE_TRIANGLE_AND_INTERNAL_MEMORY.md)的源自由星形消元中使用定义 24.1 的仿射源对应，得

$$
u_O=(b_L+b_T+b_R-q)/3,\qquad
q_{\rm eff}=(q/3)(1,1,1,0),\qquad C=-q^2/6,
$$

且原 $LJ,RJ$ 单位边保留，$L,T,R$ 间三条有效边权为 $1/3$。这只是既有星形结果的带源应用。三节点单位链 $0-1-2$、$B=\{2\},I=(0,1)$ 的同一公式给 $K^{-1}=\left(\begin{smallmatrix}2&1\\1&1\end{smallmatrix}\right)$、$W=(1,1),\Lambda=0$；分别置单位源 $e_0,e_1$ 时，$j_B=1$，但 $V=b-1,b-1/2$。另一带两个内部点的链 $b_L-i_1-i_2-b_R$、两端接地、单位电导给 $K=\left(\begin{smallmatrix}2&-1\\-1&2\end{smallmatrix}\right)$，对 $q_1=e_{i_1},q_3=e_{i_2}$ 有 $U_1=U_3=-1/3,U_{13}=-1,J_U=-1/3$。这些小矩阵仅说明定义 24.1 的参数对应；定理 24.3 进一步保持了单源能量曲线，缺的仍是非对角配对。

顺序消元仍复用[响应三角形卷 theorem 8.1](AURIC_FIB_ATOM_RESPONSE_TRIANGLE_AND_INTERNAL_MEMORY.md)及[Schur 补结合律](../../../D5/S3/Weil/ZetaLinear/SchurComplementAssociativity.lean)在可逆内部块上的对应；必须携带仿射项与常数项。[《二阶关系完成》定理 14.2](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)已有二次、一次、常数的消元参数，Gaussian 积分还含行列式归一化，不可与本节的取极小值混用。边界响应不恢复内部来源的结论依定义 24.2 的实际纤维判据解释，不升级为对任意动态未来的充分性。

**假设 24.5（共同标架中已校准的保留模式相位读口）。** 除定理 24.3 的能量任务外，若另问模式的钟响应，须独立给定有限 $d\ge1$ 维复探针空间、同一个固定正交标架、$\hbar>0$、自伴 $H_{\rm ref},H_s$ 及同一已校准参数 $t$。$N_s>0$ 是无量纲常数。在这份标架中“只缩放生成元时间”的判据量化所有密度输入：

$$
\forall\rho\in M_d(\mathbb C),\quad
\rho=\rho^*\ge0,\ \operatorname{tr}\rho=1:\quad
[H_s,\rho]=N_s[H_{\rm ref},\rho].
$$

按 [Etingof 等，§1.3 Corollary 1.17](../../../Library/Quantum/etingof2009representation.md)的经典标量交换子结论，此条件等价于 $H_s=N_sH_{\rm ref}+a_s I_d$、$a_s\in\mathbb R$。这里的对应是：密度矩阵实张成 Hermitian 空间，复张成全部矩阵；$H_s-N_sH_{\rm ref}$ 因而在全矩阵代数的中心，自伴性保证标量为实。仅检验一份输入态或一个可交换子代数不够。若 $H_{\rm ref}$ 非标量，$N_s,a_s$ 唯一；若 $H_{\rm ref}=hI_d$，条件仅要求 $H_s$ 为标量，任意正 $N_s$ 都能由 $a_s$ 补偿，钟率不被探针识别。这包括 $d=1$。加法标量不改变这个探针的能隙，未给出其在另一个协变物质理论中是否贡献应力的结论。

采用实际初始联合态

$$
\rho_{SP}(0)=\sum_{s\in\Sigma}p_s|s\rangle\langle s|\otimes\rho_P,
\qquad p\in\mathcal D,
$$

即每个试验开始按同一律 $p$ 抽一次经典模式，探针初态与模式独立，比较期间该模式保持不变。模式条件演化取上述常 Hamiltonian，选择参考本征态 $m,n$、已知非零能隙 $\omega=(E_m-E_n)/\hbar\ne0$，并要求制备 $\rho_{P,mn}\ne0$ 和读出已校准的两相位分量。于是忽略模式后的该非对角元乘以

$$
\Gamma_p(t)=\sum_s p_s e^{-i\omega N_st}.
$$

若初态已与模式相关，必须保留各 $\rho_{P|s}$，不再由一个公共非对角元提出这份因子。若选零能隙，$\Gamma_p\equiv1$；没有非零初始相干或相位读口，也不能把形式上的复函数当成实际观测。对有限已知率，特征函数的矩展开给

$$
\Gamma'_p(0)=-i\omega\mathbb E_p[N],\qquad
|\Gamma_p(t)|^2=1-\omega^2\operatorname{Var}_p(N)t^2+O(t^4).
$$

这里模平方是独立副本差 $N-N'$ 的特征函数，奇数阶消失；这是有限和的经典矩恒等式。$\omega\ne0$ 且方差正时，它在零附近不能等于单一确定钟率的纯相位函数，不宣称每个孤立时刻都可区分。

源律、核和取得条件直接使用[局部时钟核卷定理二及 Q1–Q6、Q9–Q10](AURIC_FIB_ATOM_LOCAL_CLOCK_KERNEL_AND_OUTPUT_RESOLVED_SEAM_VISIBILITY.md)。具体将命题 A-2.5 的函数分别换成 $\operatorname{Re}e^{-i\omega N_st}$、$\operatorname{Im}e^{-i\omega N_st}$，即为本相位读口的对应，不新增一般恢复定理。对已校准的 $N(s)=1+\varepsilon(x(s)+y(s))$、$\varepsilon>0$，置 $\zeta=e^{-i\omega\varepsilon t}$，同一实际 $p_\kappa$ 给

$$
\begin{aligned}
\Gamma_{p_\kappa}(t)&=e^{-i\omega t}\big[1+(X+Y)(\zeta-1)+\kappa(\zeta-1)^2\big],\\
J_{e^{-i\omega Nt}}&=e^{-i\omega t}(1-\zeta)^2,\\
\mathbb E_p[N]&=1+\varepsilon(X+Y),\\
\operatorname{Var}_p(N)&=\varepsilon^2\big[X+Y+2\kappa-(X+Y)^2\big].
\end{aligned}
$$

因此在已知 $(X,Z,Y)$ 的非退化实际纤维，固定时刻的完整复响应识别 $\kappa$ 恰在 $\omega\varepsilon t\notin2\pi\mathbb Z$；单点纤维无需额外识别。对已有的两份律 $p^{(A)}=(\delta_O+\delta_J)/2$、$p^{(B)}=(\delta_L+\delta_R)/2$，有

$$
\Gamma_A=e^{-i\omega(1+\varepsilon)t}\cos(\omega\varepsilon t),\qquad
\Gamma_B=e^{-i\omega(1+\varepsilon)t}.
$$

二者均值率同为 $1+\varepsilon$，方差分别为 $\varepsilon^2,0$。可见度 $|\Gamma|$ 仅在 $\omega\varepsilon t\notin\pi\mathbb Z$ 区分这对律；奇数倍 $\pi$ 时可见度相同而复相位相反。可见度因而不等于完整相位读数，零时刻及其他别名时刻不供应单时识别。

对任意有限已知互异率 $r_1,\ldots,r_m$，完整时间函数（或零附近的精确函数）确定的是分组质量 $w_j=\sum_{s:N_s=r_j}p_s$：零到 $m-1$ 阶导数给 $\sum_jw_jr_j^k$，非零 $\omega$ 和互异率的 Vandermonde 矩阵使其可逆。这是有限指数和的经典线性独立性，不恢复同率组内标签。在显示五态律中 $O,T$ 同率，$L,R$ 同率；三个分组质量是 $1-X-Y+\kappa,X+Y-2\kappa,\kappa$。未知能隙或未知时间尺度还会混淆 $\omega N_st$ 的标定，有限样本也不等于已取得完整函数。

跨多个区间的语义使用[二阶关系卷定义 110.1、定理 110.2、命题 110.4](AURIC_FIB_SECOND_ORDER_RELATION_COMPLETION.md)。同一次保留模式在区间 $\Delta_j\ge0$ 给 $\Gamma_p(\sum_j\Delta_j)$；每段重新独立按 $p$ 抽取模式且与探针独立，给 $\prod_j\Gamma_p(\Delta_j)$。若模式按过程 $S_t$ 切换，须另供从实际初律 $p$ 出发的路径律，所需量是 $\mathbb E\exp(-i\omega\int_0^tN_{S_v}\,dv)$。该式还依赖本合同的共同 $H_{\rm ref}$ 使条件生成元交换；任意变化轴的 Hamiltonian 须用有序演化。没有把定理 24.3 的能量标定变成这些率、初态或仪器的来源；相同模式标签并不提供这一物理桥梁。

**假设 24.6（能量和钟读口的外部几何比较域）。** 若将定理 24.3 的负交叉项与连续力比较，另行供应 Euclidean 三维空间、$G>0$、质量密度及物理单位。一个足够的静态数学域是 $\rho\in C_c^\infty(\mathbb R^3)$、非负，$\Phi$ 在无穷远趋零，$\int|\nabla\Phi|^2<\infty$，并采用

$$
\mathcal I[\Phi;\rho]=\frac1{8\pi G}\int|\nabla\Phi|^2\,d^3x+\int\rho\Phi\,d^3x,
\qquad \Delta\Phi=4\pi G\rho.
$$

$\Phi$ 的单位为速度平方，$G$、$\rho$ 分别取通常的引力常数和质量密度单位，两个积分均为能量。取紧支撑变分及无穷远条件后，正算子是 $-\Delta/(4\pi G)$；其源符号对应定义 24.1 的 $+q u$。这是 [Tong §5.1.2 的 Newtonian 极限](../../../Library/Geometry/tong2021general.md)中另行选入的 Poisson 模型，不由图推导。用其衰减 Green 核，两份平滑紧支撑源的有限交叉积分为

$$
U_{\rm cross}=-G\iint\frac{\rho_1(\mathbf x)\rho_3(\mathbf y)}{|\mathbf x-\mathbf y|}\,d^3x\,d^3y.
$$

理想点源只能另取互作用部分，排除各自发散自能；对不同位置的正质量 $M_1,M_3$、实际距离 $R>0$，$U_{\rm cross}=-GM_1M_3/R$ 才给 $F_R=-\partial_RU=-GM_1M_3/R^2$。本图没有提供这个距离核，因此 $J_U<0$ 自身不推出吸引力。作为 GR 弱场解释还需 $|\Phi|/c^2\ll1$、缓慢且低压物质及相应边界条件；完整应力与几何耦合仍属假设 23.6 的另给合同。

钟率的经典反比较直接用 [Tong §1.2.4 式 (1.26)](../../../Library/Geometry/tong2021general.md)：取 $c=1$、$a>0$、右楔 $1+ax>0$ 及未来定向 $dt>0$，

$$
T=(a^{-1}+x)\sinh(at),\quad X=(a^{-1}+x)\cosh(at),\qquad
ds^2=-dT^2+dX^2=-(1+ax)^2dt^2+dx^2.
$$

这是平直空间的加速坐标，曲率零，固定 $x$ 的 $d\tau=(1+ax)dt$；离开该正楔，必须使用绝对 lapse 并另定时间方向，不能延用正率式。这里采用 $-+$ 签名，与假设 23.6 的 $+-$ 场约定不同。非均匀钟率不单独识别曲率或物质源。

再以 [Will，PPN Box 2、§4.1.1 式 (59)–(60)](../../../Library/Geometry/will2014confrontation.md)作同一读口限制的经典参照。独立给 $3+1$ 维静态各向同性候选度规、$-+++$ 签名，$\Phi=-GM/r$，$G,M,c>0$，固定有限实 $\gamma$，在外部弱场区声明

$$
ds^2=-[1+2\Phi/c^2+O(\Phi^2/c^4)]c^2dt^2
+[1-2\gamma\Phi/c^2+O(\Phi^2/c^4)]d\mathbf x^2.
$$

取在所用外部路径上一致受控的光滑高阶项及其所需导数，并要求 $|\Phi|/c^2\ll1$、$|\gamma\Phi|/c^2\ll1$；各时间、空间系数保持正以维持该签名。静止 lapse 在一阶同为 $1+\Phi/c^2$，慢粒子在领先低速、弱场阶有 $\ddot{\mathbf x}=-\nabla\Phi$，不声称高阶运动相同。光学折射率却为

$$
n_\gamma=1-(1+\gamma)\Phi/c^2+O(\Phi^2/c^4).
$$

对源与观察者均在渐近无穷远、冲击参数 $b_{\rm imp}>0$、整条散射路径留在外部弱场区的光线，令 $\eta=GM/(b_{\rm imp}c^2)\ll1$ 且 $|\gamma|\eta\ll1$，引文的渐近端点特例给向内为正的偏折

$$
\delta\theta=2(1+\gamma)\eta+O(\eta^2),\qquad
|\delta\theta|=2|1+\gamma|\eta+O(\eta^2).
$$

有限观察者应保留所引式 (59) 的几何因子；$\gamma=-1$ 时领先项为零。$\gamma=0,1$ 分别给 $2\eta,4\eta$ 的领先项，却有相同领先钟率与慢粒子落体。任意 $\gamma$ 的度规族未被声明满足同一 Einstein–物质方程。这些经典比较只列明图源、标量能量、探针相位和时空输运之间尚需供应的对象与操作；五态标签、共同场的交叉项或三均值都没有自动生成该几何。

## 追加锚（本行以下为增补区）
