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
