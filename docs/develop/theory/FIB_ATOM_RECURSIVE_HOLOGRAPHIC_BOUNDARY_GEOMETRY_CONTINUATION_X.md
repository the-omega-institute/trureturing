# FIB-ATOM 递归全息边界几何·四个实际端口的树响应续卷

## 257. 实际来源、接地端口与可比较的响应

**定义 257.1（来源与几何供应项）。** 本卷承接[续卷 IX 的 §256](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_IX.md)。来源是非空有限有序二元树：叶标签为 $\alpha,\beta$，分支写为 $\langle s,t\rangle$；相同标签的不同出现仍为不同顶点。采用[Whole-rho 续卷 §55.1–§55.5](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md) 的同地址来源及其附加几何合同：

$$
\rho\alpha=\beta,\qquad
\rho\beta=\langle\beta,\alpha\rangle,\qquad
\rho\langle s,t\rangle=\langle\rho s,\rho t\rangle,
\qquad D_j(t)=\operatorname{Pos}(\rho^jt).
$$

地址为 $\{L,R\}^{*}$ 的有限字，根为 $\varepsilon$，边仅连接实际存在的父子地址。$D_j(t)$ 是实际有限树，不以完全层球替换。[§55.2](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md) 的零外延 Dirichlet 动能 $L_D$ 在根的对角为 $2$，其余实际顶点的对角均为 $3$，实际边的非对角为 $-1$；当前叶缺失的两个孩子贡献仍保留在对角。它不同于把有限树封闭后按其内部度数构成的自由 Laplacian。

来源原有的 INITIAL、实际版本、标签、左右顺序、操作、整棵候选的守卫、接受或拒绝、Read、Stop、记录与取得权限均不因这个附加几何合同改变。固定容量的执行只采用分别合法的有限前缀；数学来源族不增加越过 Stop 或无限前缀后的事件。给一个实际地址安装电势和电流接口是另加的实现合同，不是从叶标签、原有数值 Read 或来源语法自动取得该接口。

**定义 257.2（标量树消元类）。** 设 $T=(V,E)$ 是有限连通树，边权 $c_{xy}>0$，$H$ 是实对称矩阵，且

$$
H_{xy}=
\begin{cases}
-c_{xy},&\{x,y\}\in E,\\
0,&x\ne y,\ \{x,y\}\notin E.
\end{cases}
$$

对角 $H_{xx}$ 任意。固定实数 $z$、互异实际顶点构成的保留集 $B$、内点集 $I=V\setminus B$，并假设

$$
K=H_{II}-zI_I>0,\qquad
S_B(z)=H_{BB}-zI_B-H_{BI}K^{-1}H_{IB}.
\tag{257.1}
$$

空内点集的消元项约定为零。选定四个互异顶点 $P=(a,b,c,d)\subset B$，把其余保留顶点 $G=B\setminus P$ 固定为零电势。比较对象是同一矩阵的主块

$$
S_4=S_B(z)[P,P],\qquad w_{ij}=-(S_4)_{ij}\quad(i\ne j),
\tag{257.2}
$$

不是进一步自由消去 $G$ 后的响应。端口可以是原树的分支、根或叶，顶点的身份和幅值单位固定。

固定四端口值 $x$，其余保留值为零时，$H-zI$ 的二次型关于内点 $y$ 的唯一极小值在 $y=-K^{-1}H_{IP}x$ 取得，极小值为 $x^{\mathsf T}S_4x$。这个极小值只要求内块正定；它不蕴含 $H-zI$ 或 $H$ 全局非负。正导通边、非负接地导通及 $z=0$ 给出被动电阻网络的子类；任意对角的整个代数类不能统称为物理被动系统。

Schur 机制是经典中间步骤，见 [Dörfler–Bullo, arXiv:1102.2950v1, §2.1、式 (2.1) 与 Lemma 2.1](https://arxiv.org/pdf/1102.2950v1)，以及[既有文献条目](../../../Library/GraphInvariants/dorflerbullo2013kron.md)。该引理的 loopy-Laplacian、连通性和至少两个保留顶点的条件不等同于任意对角类；(257.1) 在此直接以其明确的正定内块为依据。

## 258. 原生有限来源的四端口最小值重合律

**定理 258.1（实际地址树的四端口必要条件）。** 对定义 257.2 的所有数据，六个 $w_{ij}$ 均非负，而且

$$
\min\{w_{ab}w_{cd},\ w_{ac}w_{bd},\ w_{ad}w_{bc}\}
\quad\text{至少被两个乘积取得。}
\tag{258.1}
$$

因此，对定义 257.1 的每一个实际有限 $D_j(t)$，其 §55 算子

$$
H=a_0L_D-gM_{\phi|D},\qquad
\phi(p)=2^{-|p|},\qquad a_0,g>0,
\tag{258.2}
$$

在任一满足 $H_{II}-zI_I>0$ 的实参数 $z$ 上，任选四个实际地址并将额外保留地址接地，都服从 (258.1)。同样适用于动能 $H=L_D$ 本身。这里 $a_0$ 是边权的公共系数，与端口名 $a$ 无关；负势只改变对角。正定假设必须在所用 $z$、来源、切口上成立，不能由响应存在或 $K$ 可逆替代。

证明。以下四点结构是新来源应用所消耗的经典中间关系，而非新的 quartet/tetrad 理论。Sturmfels–Uhler–Zwiernik, *Brownian motion tree models are toric*, [arXiv:1902.09905v1, Theorem 2.6，PDF 第 6 页](https://arxiv.org/pdf/1902.09905v1)，在其浓度矩阵 $C$ 的坐标 $p_{ij}=-C_{ij}$ 中给出：星形四叶的三个乘积相等；分裂 $ij|kl$ 的两个交叉乘积相等且不大于同侧乘积。其 $p_{0i}=\sum_jC_{ij}$ 是额外根叶坐标。其模型从单调 Brownian 树协方差及正定浓度矩阵出发；本定理只要求内块正定，$S_4$ 可不正定，且标记端口可在内部。对应是 $p_{ij}\leftrightarrow w_{ij}=-(S_4)_{ij}$、$ij|kl\leftrightarrow ab|cd$ 的四端口坐标对应，不是把任意 $S_4$ 宣称为该文的模型成员，也不对本定理引入其 $p_{0i}\ge0$ 条件。在严格正边的 Brownian 子类中，参数可精确取为增量方差 $\theta_e=1/c_e$：将根叶 $0$ 固定为零，其余叶响应为 $C$，则独立树边增量的叶协方差满足

$
\Sigma=C^{-1},\qquad
\Sigma_{ij}=\sum_{e\in[0,i]\cap[0,j]}\theta_e.
$

这里的两个方括号表示树上路径，$\theta_e>0$ 给出该文的单调协方差参数；完整叶响应的根耦合还满足 $p_{0i}=-S_{0i}=\sum_jC_{ij}$。这是与其模型相交子类的参数对应；任意对角及内部标记情形仍需下面的直接证明。

首先，正定 Z-matrix 的逆逐项非负。确切地，对非空 $K$ 取 $s\ge\lambda_{\max}(K)>0$，令 $N=sI-K$。矩阵 $N$ 逐项非负，且其谱在 $[0,s-\lambda_{\min}(K)]$ 内，故

$$
K^{-1}=\frac1s\sum_{n=0}^{\infty}(N/s)^n\ge0.
\tag{258.3}
$$

在同一个内点连通分量中的两点之间，连接路径对应某个正的矩阵幂项，所以逆元严格为正。由于 $H_{PI}\le0$，消元项 $H_{PI}K^{-1}H_{IP}\ge0$，再结合 $H_{ij}\le0$，得到 $w_{ij}\ge0$。

先证明只有四个标记叶作为保留端口的情形。若图为森林，不同连通分量之间的响应为零。若四端口不全在同一分量，则分量内端口数的分拆为 $3+1$、$2+2$、$2+1+1$ 或 $1+1+1+1$；在每种情形中至少两个配对乘积含有跨分量因子，故为零，已得 (258.1)。无端口的分量不贡献响应。

现在四个端口同在一个树分量。逐个消去不在四端口最小连通子树上的内点叶；这只改变其邻点对角。再消去该最小子树中度为二的内点。每次内点消元都是正定内块的 Schur 步，其枢轴 $d$ 严格为正，剩余内块仍正定。度二内点两侧的边权 $c_1,c_2$ 变成 $c_1c_2/d>0$，且不产生平行路径。所有步骤保持端口响应。所得四叶核心只有一颗四价星，或两个三价 Steiner 顶点连接的 quartet；这是树的度数恒等式 $\sum_{v\text{ 内}}(\deg v-2)=4-2$ 的结果。

星形核心的正内点对角为 $A>0$，四臂权为 $x_a,x_b,x_c,x_d>0$，所以 $w_{ij}=x_ix_j/A$，三个乘积全等。另一情形重命名为 $ab|cd$；核心内块与行列式为

$$
K_{\rm core}=\begin{pmatrix}A&-t\\-t&B\end{pmatrix},\qquad
A,B,t>0,\qquad \Delta=AB-t^2>0.
$$

四臂仍记为 $x_i>0$。直接取逆得到

$$
\begin{aligned}
w_{ab}&=x_ax_bB/\Delta,&
w_{cd}&=x_cx_dA/\Delta,\\
w_{ij}&=x_ix_jt/\Delta
&&\bigl(i\in\{a,b\},\ j\in\{c,d\}\bigr).
\end{aligned}
$$

令 $X=x_ax_bx_cx_d$，便有

$$
w_{ac}w_{bd}=w_{ad}w_{bc}=\frac{Xt^2}{\Delta^2}
<\frac{XAB}{\Delta^2}=w_{ab}w_{cd}.
\tag{258.4}
$$

这证明了标记叶情形，包括对角并非网络度数的情况。

最后处理原树内部的标记及额外接地端口。先删掉 $G$ 的坐标，保持其余对角原值；接地恰是取 $Q=(H-zI)[P\cup I,P\cup I]$，不是重算删边后的自由对角。因此底图是森林，$Q_{II}=K>0$，关于 $I$ 的响应正是 $S_4$。

对每个旧标记 $i\in P$ 附加一个新叶 $\widetilde i$，以新叶值 $u_i$、旧标记值 $x_i$ 添加二次型 $M\sum_{i\in P}|u_i-x_i|^2$。只把四个新叶保留，旧标记都改为内点。增广内块为

$$
J_M=\begin{pmatrix}Q_{PP}+MI_4&Q_{PI}\\Q_{IP}&K\end{pmatrix}.
$$

当 $M>\max\{0,-\lambda_{\min}(S_4)\}$ 时，$K>0$ 且其 Schur 块 $S_4+MI_4>0$，故 $J_M>0$。增广底图仍为森林，所有边权严格为正，新标记全为叶；刚证的叶端口结论确实适用。消去旧内点及旧标记后，新叶响应为

$$
S_M=MI_4-M^2(S_4+MI_4)^{-1}
=S_4(I_4+S_4/M)^{-1}\longrightarrow S_4.
\tag{258.5}
$$

这是真正的内块正定近似，而非在可能不正定的旧四端口上直接作无条件消元。三个配对乘积是六个非对角元的连续函数；“最小值至少两次取得”的集合等于三个闭集 $\{P_1=P_2\le P_3\}$、$\{P_1=P_3\le P_2\}$、$\{P_2=P_3\le P_1\}$ 的并，因而闭。取极限即得一般情形。辅助叶只用于证明，不向原生来源或物理装置增加资源。

在 (258.2) 中，实际父子边权恰为 $a_0>0$，势和谱参数仅改对角；§55.5 的 (55.17) 正是 (257.1)，所以逐项代入得到来源断言，无须假定所选地址为叶。□

**推论 258.2（固定端口的极限障碍）。** 若一族满足定义 257.2 的响应在同一四端口次序和幅值单位下逐项收敛，极限仍有非负 $w_{ij}$ 并满足 (258.1)。特别地，任一只有一个严格最小配对乘积的目标，不是这种固定端口响应的逐项极限。

证明。非负半直线及定理证明末尾的最小值重合集合均为闭集。这里允许树的大小、权、对角和可容许的 $z$ 随族变化；四端口及单位的比较合同固定。□

## 259. 立方体的实际面响应与精确误差

**定义 259.1（立方体目标）。** 令 $Q_3$ 的顶点为 $\{0,1\}^3$，相差一个坐标的顶点以单位导通边连接，取其自由 Laplacian $L_{Q_3}$。保留一个面上的四个顶点 $a,b,c,d$，按该面的循环顺序排列；消去相对面的四顶点。此处没有额外接地保留顶点，参数为 $z=0$，电势、电流单位固定。记 $C_4$ 的 Laplacian 为 $L_{C_4}$，并令

$$
A=I_4+L_{C_4}=\begin{pmatrix}
3&-1&0&-1\\-1&3&-1&0\\0&-1&3&-1\\-1&0&-1&3
\end{pmatrix}.
$$

按两面对应顶点的次序，整个 Laplacian 为 $\begin{pmatrix}A&-I_4\\-I_4&A\end{pmatrix}$。目标是此实际立方体上的四顶点 Schur 响应，不是自由电阻距离。

**命题 259.2（面响应及唯一最小乘积）。** 定义 259.1 的响应为

$$
\begin{aligned}
A^{-1}&=\frac1{15}
\begin{pmatrix}7&3&2&3\\3&7&3&2\\2&3&7&3\\3&2&3&7\end{pmatrix},\\
S_{\rm cube}&=A-A^{-1}=\frac1{15}\begin{pmatrix}
38&-18&-2&-18\\-18&38&-18&-2\\-2&-18&38&-18\\-18&-2&-18&38
\end{pmatrix}.
\end{aligned}
\tag{259.1}
$$

相应配对乘积按 $ab|cd,ac|bd,ad|bc$ 的次序为

$$
36/25,\qquad 4/225,\qquad 36/25.
\tag{259.2}
$$

故这个目标不属于定义 257.2 的任何树响应，也不属于其固定端口逐项闭包。

证明。$L_{C_4}\ge0$，故 $A>0$。将整数矩阵乘以 $A$ 得 $15I_4$，即为所示精确逆；代入两面块的 Schur 公式得到 (259.1)。循环相邻的 $w$ 为 $6/5$，对面的 $w$ 为 $2/15$，所以 (259.2) 的中间项是唯一严格最小值。定理 258.1 与推论 258.2 给出断言。□

**定理 259.3（一般循环目标的尖锐逐项误差）。** 给定 $u>v\ge0$，定义四端口目标

$$
S(u,v)=\begin{pmatrix}
2u+v&-u&-v&-u\\-u&2u+v&-u&-v\\-v&-u&2u+v&-u\\-u&-v&-u&2u+v
\end{pmatrix}.
\tag{259.3}
$$

对定义 257.2 的任意 $S_4$，

$$
\delta_{\rm off}:=\max_{i\ne j}|(S_4)_{ij}-S(u,v)_{ij}|
\ge\frac{u-v}{2}.
\tag{259.4}
$$

此下界可由有限、严格正权的二元树达到，且该例的全矩阵最大逐项误差也恰为 $(u-v)/2$。特别地，$S_{\rm cube}=S(6/5,2/15)$ 的尖锐误差为 $8/15$。这里最优化的比较类允许自由选择正边权及树对角；没有断言原生固定单位边权子类也达到下界，也没有断言算子范数最优性。

证明。记 $\delta=\delta_{\rm off}$。若 $\delta<(u-v)/2$，则 $u-\delta>v+\delta\ge0$。由于所有候选 $w$ 非负，

$$
\begin{aligned}
w_{ab}w_{cd},\ w_{ad}w_{bc}&\ge(u-\delta)^2,\\
w_{ac}w_{bd}&\le(v+\delta)^2<(u-\delta)^2.
\end{aligned}
$$

这给出唯一严格最小配对乘积，与 (258.1) 矛盾。这一论证只使用非对角元，不要求候选对角等于目标对角。

为达到下界，取分裂 $ab|cd$ 的树，两个内点 $p,q$ 分别连接 $a,b$ 与 $c,d$。四条端臂的导通相同，中央边导通分别为

$$
\gamma=3u+v,\qquad t=\frac{2(u+v)\gamma}{u-v}.
\tag{259.5}
$$

二者均有限且严格为正。采用此封闭加权树的自由 Laplacian，所以内块为

$$
K_{pq}=\begin{pmatrix}2\gamma+t&-t\\-t&2\gamma+t\end{pmatrix}>0,
\qquad D=(2\gamma+t)^2-t^2=4\gamma(\gamma+t)>0.
$$

四端臂对角为 $\gamma$。直接消元给出同侧与交叉幅值

$$
\begin{aligned}
w_{ab}=w_{cd}&=\frac{\gamma^2(2\gamma+t)}D=u,\\
w_{ac}=w_{ad}=w_{bc}=w_{bd}&=\frac{\gamma^2t}D=\frac{u+v}{2},\\
(S_4)_{ii}&=\gamma-u=2u+v.
\end{aligned}
\tag{259.6}
$$

因此四个交叉项相对目标的偏差绝对值为 $(u-v)/2$，同侧项和所有对角项精确相等，证明全矩阵逐项尖锐性。

立方体情形的具体参数和响应为

$$
\gamma=56/15,\qquad t=28/3,\qquad
S_*=\begin{pmatrix}
38/15&-6/5&-2/3&-2/3\\-6/5&38/15&-2/3&-2/3\\
-2/3&-2/3&38/15&-6/5\\-2/3&-2/3&-6/5&38/15
\end{pmatrix}.
\tag{259.7}
$$

把中央边细分成 $p-o-q$，每段导通为 $2t$。内点 $o$ 的对角为 $4t$，消去 $o$ 后两端间新增非对角为 $-(2t)^2/(4t)=-t$，两端的新增对角各为 $t$，恰好恢复原中央边。以 $o$ 为根，底图是具有七个实际出现的全二元树；例如来源 $\langle\langle\alpha,\alpha\rangle,\langle\alpha,\alpha\rangle\rangle$ 的形状恰为此图。立方体达到例的两段导通各为 $56/3$。所有内部 Dirichlet 块正定，因为连通正权树的零能量函数必为常数，而四个零边界值迫使该常数为零。

这里实现的是“任意 Source 形状上另加可变正权自由 Laplacian”。Source 的任意元素与从单个固定 INITIAL 出发的 Fibonacci 替换轨道不同；尤其四个 $\alpha$ 叶的例子不是已证明沿该轨道取得的来源。此达到例也不使用 §55 的固定单位边权及缺失孩子接地对角。□

## 260. 九个实际出现中的内部标记端口

**命题 260.1（原生 $T_4$ 的非叶端口响应）。** 令 $T_n=\rho^n\alpha$，则

$$
T_4=\langle\langle\langle\beta,\alpha\rangle,\beta\rangle,
                   \langle\beta,\alpha\rangle\rangle.
$$

按定义 257.1 的 §55 Dirichlet 动能取 $H=L_{D_4(\alpha)}$、$z=0$，选

$$
(a,b,c,d)=(LL,LR,RL,RR).
$$

这四个都是实际顶点，且 $a=LL$ 是分支。其余五个顶点为内点，无额外接地保留端口。精确响应为

$$
S_{T_4}=\frac1{12}\begin{pmatrix}
23&-5&-1&-1\\-5&31&-1&-1\\-1&-1&31&-5\\-1&-1&-5&31
\end{pmatrix},
\tag{260.1}
$$

所以同侧幅值为 $5/12$，四个交叉幅值为 $1/12$，配对乘积为 $25/144,1/144,1/144$。

证明。依次替换得到 $T_1=\beta$、$T_2=\langle\beta,\alpha\rangle$、$T_3=\langle\langle\beta,\alpha\rangle,\beta\rangle$，再得所示 $T_4$。其九个实际地址为

$$
\varepsilon,\ L,\ LL,\ LLL,\ LLR,\ LR,\ R,\ RL,\ RR.
$$

$LLL,LLR$ 的标签分别为 $\beta,\alpha$，故 $LL$ 确为分支；$LR,RL,RR$ 分别为 $\beta,\beta,\alpha$。由 §55 的动能对角，根为 $2$，所有其余地址为 $3$。其二次型是实际内部边的差平方加每个当前叶的两个缺失孩子项，因而严格正定：零能量使连通树上的值为常数，叶的接地项再使常数为零。故所需内块正定。

消去 $LLL,LLR$ 各减去 $LL$ 对角的 $1/3$，将其改为 $7/3$。剩余内点 $(\varepsilon,L,R)$ 的块和逆为

$$
K_0=\begin{pmatrix}2&-1&-1\\-1&3&0\\-1&0&3\end{pmatrix},\qquad
K_0^{-1}=\begin{pmatrix}
3/4&1/4&1/4\\1/4&5/12&1/12\\1/4&1/12&5/12
\end{pmatrix}.
$$

端口 $a,b$ 各以 $-1$ 连接 $L$，$c,d$ 各以 $-1$ 连接 $R$。代入 (257.1)，$a$ 的对角为 $7/3-5/12=23/12$，另三项为 $3-5/12=31/12$，非对角即 (260.1)。这既给出实际来源实例，也说明叶端口限定不足以覆盖原题。□

**定义 260.2（来源选择与装置动作的区别）。** 命题 260.1 的来源选择是一个有标签、有括号、有地址的实际有限对象；其几何使用 §55 所声明的额外合同。四个电势的独立制备、其他端口的接地以及四个电流的测量若要成为操作，必须另外安装并声明权限、单位和成本。原有符号 Read 的返回值不是 (260.1) 的一行，也不因矩阵可写而取得这些动作。使用固定容量的执行时，还必须保证到达 $T_4$ 的整棵候选分别通过原有守卫；式子本身只指明有限数学来源，不撤销拒绝和 Stop。

## 261. 任意固定向量秩的各向同性推广

**定理 261.1（树上正交规范与块范数障碍）。** 固定任意整数 $r\ge1$。在定义 257.2 的树上，把在位标量 $H_{xx}$ 替换为 $H_{xx}I_r$，边块替换为

$$
\mathcal H_{xy}=-c_{xy}O_{xy},\qquad
O_{xy}\in O(r),\qquad O_{yx}=O_{xy}^{\mathsf T}.
\tag{261.1}
$$

其余块为零，谱参数为 $zI_r$。假设消去内点的整个块
$\mathcal K=\mathcal H_{II}-zI_{r|I|}>0$，保留与接地仍按实际顶点进行。定义
$\mathcal S_B=\mathcal H_{BB}-zI_{r|B|}-\mathcal H_{BI}\mathcal K^{-1}\mathcal H_{IB}$，
并取其所选四顶点主块为 $\mathcal S_4$。所得响应 $\mathcal S_4$ 的六个数

$$
\omega_{ij}=\| (\mathcal S_4)_{ij}\|_{\rm op}\quad(i\ne j)
$$

服从 (258.1) 的相同最小值重合律。相对固定块目标 $S(u,v)\otimes I_r$，

$$
\max_{i\ne j}
\| (\mathcal S_4)_{ij}-S(u,v)_{ij}I_r\|_{\rm op}
\ge\frac{u-v}{2}.
\tag{261.2}
$$

允许定理 259.3 的可变权自由 Laplacian 时，对所有 $r$ 都有达到例，包括 $r=3$。

证明。树上任选根和 $G_o\in O(r)$。对每条父子边 $x\to y$，递归取 $G_y=O_{xy}^{\mathsf T}G_x$。唯一路径使定义相容，并有 $G_x^{\mathsf T}O_{xy}G_y=I_r$。于是块对角正交变换 $G=\operatorname{diag}(G_x)$ 给出

$$
G^{\mathsf T}(\mathcal H-zI)G=(H-zI)\otimes I_r.
$$

因此整个内块正定当且仅当标量 $K>0$。变换保留逐顶点切分及零电势条件，Schur 消元与之相容，故

$$
(\mathcal S_4)_{ij}=G_i(S_4)_{ij}I_rG_j^{\mathsf T},\qquad
\omega_{ij}=|(S_4)_{ij}|=w_{ij}.
$$

定理 258.1 给出块范数乘积律。算子范数的反三角不等式还给出

$$
|\omega_{ij}-|S(u,v)_{ij}||
\le\|(\mathcal S_4)_{ij}-S(u,v)_{ij}I_r\|_{\rm op}.
$$

若右端六项的最大值小于 $(u-v)/2$，便与定理 259.3 证明中的相同区间比较矛盾。最后取所有 $O_{xy}=I_r$，将 (259.6) 张量 $I_r$ 即达到误差下界。□

**定义 261.2（秩与空间的不同参数）。** $r$ 是每个实际出现上的向量纤维维数，不是底图的空间维数。树上消去正交运输只使用无环性和各向同性在位块；它没有证明原生程序自带运输、规范自由度或可执行的规范改变。$r=3$ 与 $r=1,2,4$ 在定理 261.1 中地位相同。各向异性在位块、多通道边、一般块耦合和有环底图没有由该证明取得相同结论。

## 262. 集体端口的反例与空间解释所需的联合合同

**命题 262.1（接线识别可将路径变成四环）。** 取五个互异实际顶点组成的单位权路径

$$
a_1-b-c-d-a_2.
$$

以一个集体电势 $a$ 同时约束 $a_1,a_2$，其余三个端口各保留自己的电势。令

$$
U=\begin{pmatrix}
1&0&0&0\\0&1&0&0\\0&0&1&0\\0&0&0&1\\1&0&0&0
\end{pmatrix},\qquad
L_{\rm path}=\begin{pmatrix}
1&-1&0&0&0\\-1&2&-1&0&0\\0&-1&2&-1&0\\0&0&-1&2&-1\\0&0&0&-1&1
\end{pmatrix}.
$$

则

$$
U^{\mathsf T}L_{\rm path}U=L_{C_4},
\tag{262.1}
$$

其配对乘积为 $1,0,1$，违反 (258.1)。

证明。把路径电势限制为 $(a,b,c,d,a)$，路径二次型变成

$$
(a-b)^2+(b-c)^2+(c-d)^2+(d-a)^2,
$$

恰为单位四环二次型，所以得到 (262.1)。此操作在底层识别两个顶点，端口 $a$ 的电流是两端电流之和；它是约束合同下的合同变换 $U^{\mathsf T}LU$，不是四个互异实际顶点的树 Schur 响应。路径是一般树反例，不是已经证明可由原生全二元 Source 形状直接实现的例子。□

**定义 262.2（与既有增长及 Markov 障碍的关系）。** [续卷 III 的 §81.1–§81.5](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_III.md) 分别讨论 §55 单位长度实际出现图的有界占用粗 Euclidean 放置，以及另一个 §52 来源图的精确同钟 Markov 因子。这里的比较对象是四个实际顶点上、指定参数与接地合同下的有限 Schur 响应；既不从自由有效电阻的加性推得，也不重证增长或 Markov 结论。它不要求无界出现图、统一空间密度或一个无穷随机游走。三种障碍的前提及目标各自保留，不能相互替代。

**命题 262.3（固定端口空间桥的必要误差与未限定类）。** 若一个来源到装置的联合实现同时满足下列假设：底层标量实际出现图仍为有限树、边导通严格为正、在所比较实参数处消去内块正定、四个装置端口分别对应四个互异实际顶点、其他保留端口固定为零、电势和电流单位与 $Q_3$ 目标一致，并且装置响应正是该 Schur 响应，则它对定义 259.1 的面响应的最大非对角逐项误差至少为 $8/15$。以定义 261.1 的各向同性正交运输替代标量时，同一结论在最大非对角块算子范数下成立。

证明。将联合实现逐项代入定理 259.3 或定理 261.1。所有限定都属于实际比较合同；改变端口基、单位或约束不构成对该结论的反例。命题 262.1 表明允许集体接线时，四环已可出现，所以不能把结论扩张为任意端口分组、混合或顶点识别的不可能性。主动、非线性、各向异性或一般多通道模型也未被本定理排除。□

**定义 262.4（数学来源、经典先例与尚缺的空间关系）。** 定理 258.1 的来源代入、定理 259.3 的固定端口误差及有限加权二元树达到例、命题 260.1 的实际地址响应，以及它们在定理 261.1 中的联合应用，均是本仓在所述供应项上的普通推导（repo-derived）。quartet/tetrad 结构属于经典先例（literature-attested），只作为这些应用内部的中间关系使用，不主张整个定理族或误差公式的世界优先权。除定理 258.1 中核对过坐标与模型差异的 Sturmfels–Uhler–Zwiernik Theorem 2.6 外，Shiers–Zwiernik–Aston–Smith, *The correlation space of Gaussian latent tree models and model selection without fitting*, [arXiv:1508.00436v2, §1 式 (1)、§2.2 Proposition 1](https://arxiv.org/pdf/1508.00436v2)，给出高斯树相关沿路径的乘积及 tetrad 限制；其协方差或相关坐标不等于此处的响应非对角元。这里采用直接消元证明，未把二者无条件互换。Dörfler–Bullo 的网络机制按定义 257.2 所列边界使用。上述有限文献范围不建立新颖性或优先权结论。

一个四环在二维平面中已经违反最小值重合律；三维立方体的一个面只是明确的空间目标。因此该必要条件不选择空间维数三，也不把局部向量秩三、抽象编码、精确量子 heralding 或有限树收缩等同于物理空间。原生单位权与固定来源轨道中误差下界是否可达，允许集体端口后哪些来源仍有受限实现，以及如何在同一来源、操作、度量、测度、场、边界和时钟下构造空间桥，均保留为未解决的数学构造问题。§81.5 的联合对应义务不由四点检验替代，单独通过这一必要检验也不构成空间实现的充分条件。

## 追加锚（本行以下为增补区）

## 263. 任意实固定纤维树响应的行列式四点律与尖锐半差障碍

**定义 263.1（完整纤维的实际端口块响应）。** 固定整数 $r\ge1$。令 $T=(V,E)$ 为至少有四个顶点的有限连通树，每个实际顶点的空间恰为 $\mathbb R^r$。在 $\bigoplus_{x\in V}\mathbb R^r$ 上取实对称块矩阵 $H$：每个对角块 $H_{xx}$ 是任意实对称矩阵，每条边的块 $H_{xy}$ 是任意实 $r\times r$ 矩阵，反向块为 $H_{yx}=H_{xy}^{\mathsf T}$，非边的非对角块为零。边块允许奇异或为零，不要求符号、各向同性或可逆性。给定任意 $z\in\mathbb R$、保留顶点集 $B\subseteq V$ 及其中四个互异实际顶点的有序组 $P=(a,b,c,d)$，令 $I=V\setminus B$，只假设消去内块

$$
K=H_{II}-zI_{r|I|}>0.
$$

记

$$
\begin{aligned}
\mathcal S_B&=H_{BB}-zI_{r|B|}-H_{BI}K^{-1}H_{IB},\\
\mathcal S_4&=\mathcal S_B[P,P],\qquad
W_{ij}=-(\mathcal S_4)_{ij}\quad(i\ne j),\\
d_{ij}&=|\det W_{ij}|=|\det(\mathcal S_4)_{ij}|
       =\prod_{\ell=1}^{r}\sigma_\ell((\mathcal S_4)_{ij}).
\end{aligned}
\tag{263.1}
$$

$I=\varnothing$ 时不要求空块之外的正定性，消元项约定为零。额外保留顶点 $G=B\setminus P$ 的所有坐标固定为零，不能自由消去。每个顶点及每个端口始终保留全部 $r$ 个坐标，电势、电流单位与 Euclidean 基固定；不允许压缩坐标、集体接线、顶点识别、跨顶点混合或重标度。端口可以是原树的根、分支、度二顶点或叶。矩阵 $H-zI$ 及 $\mathcal S_4$ 均不要求正定或非负。单个非对角块可以不对称，但反向块为其转置，故 $d_{ij}=d_{ji}\ge0$。这里的行列式取全部奇异值的乘积，不是只取最大奇异值。

**定理 263.2（只要求内块正定的行列式 quartet）。** 对定义 263.1 的全部数据，

$$
\min\{d_{ab}d_{cd},\ d_{ac}d_{bd},\ d_{ad}d_{bc}\}
\quad\text{至少由两个乘积取得。}
\tag{263.2}
$$

证明。先将额外保留顶点接地。取主块

$$
Q=(H-zI)[P\cup I,P\cup I].
$$

删除 $G$ 的坐标时保持所有剩余对角块原值，不重新计算删边后的自由 Laplacian。于是底图成为森林，$Q_{II}=K>0$，且

$$
Q_{PP}-Q_{PI}K^{-1}Q_{IP}=\mathcal S_4.
\tag{263.3}
$$

这不是关于 $G$ 的 Schur 补；$I$ 为空时右式直接为 $Q_{PP}$。以下先证明森林上四个标记端口均为叶的情形，再用正内块极限处理任意实际端口。

若四个叶不全在同一个组合连通分量，原矩阵及内块逆均按分量直和分解，跨分量响应为零。四个端口按分量的数目分拆只有 $3+1$、$2+2$、$2+1+1$ 或 $1+1+1+1$；每种分拆中至少两个配对乘积含有跨分量因子，故为零，其余乘积非负，已得 (263.2)。没有端口的分量不贡献端口响应，可以舍去。此论证也适用于组合边的矩阵块为零的情况；无须把零块当作可逆连接。

现在四个标记叶同在一个树分量。逐个消去四叶最小连通子树之外的内点叶，再消去最小子树中的度二内点。设当前消去顶点为 $x$，其对角枢轴为 $D$。当前全部待消内块正定，故其主块 $D>0$；Schur 消去后其余待消内块仍正定。内点叶的消去只把邻点 $y$ 的对角改为 $Q_{yy}-Q_{yx}D^{-1}Q_{xy}$。度二内点 $x$ 的两个邻点为 $y,w$，新增块为

$$
Q'_{yw}=-Q_{yx}D^{-1}Q_{xw},\qquad
Q'_{wy}=(Q'_{yw})^{\mathsf T},
\tag{263.4}
$$

并相应修改两个对角。树上不存在另一条 $y,w$ 连接路径，所以没有原有平行边需要合并。新增块仍可任意奇异或为零；消元不要求它可逆。所有枢轴都是 $r\times r$ 正定块，所有剩余顶点的纤维维数仍为 $r$。Schur 补的结合律保证每一步保持同一四端口响应。

约化后仅有四个标记叶，其余顶点的度至少为三。树的度数恒等式给出

$$
\sum_{x\text{ 为内点}}(\deg x-2)=4-2=2.
$$

因此核心只有一颗四臂星，或两个三价中心连接的树，后者可重命名为分裂 $ab|cd$。这一分类依据组合树，而不要求任一矩阵边满秩。

对四臂星，记中心正定块为 $A>0$，从叶 $i$ 到中心的块为 $F_i$，并记 $f_i=|\det F_i|$。叶之间没有直接边，故其非对角响应满足

$$
W_{ij}=F_iA^{-1}F_j^{\mathsf T},\qquad
 d_{ij}=\frac{f_if_j}{\det A}.
$$

于是三个配对乘积均为 $f_af_bf_cf_d/(\det A)^2$，包括某个 $F_i$ 奇异时三个乘积全为零的情形。

对双中心核心，令 $a,b$ 接在中心 $h$，$c,d$ 接在中心 $g$。内块及其逆写成

$$
J=\begin{pmatrix}A&C\\ C^{\mathsf T}&B\end{pmatrix}>0,
\qquad
J^{-1}=\begin{pmatrix}X&Y\\Y^{\mathsf T}&Z\end{pmatrix}>0.
$$

这里 $A,B$ 为正定对角块，$C$ 是任意实块。为明确逆式，令 $D=B-C^{\mathsf T}A^{-1}C>0$，则

$$
\begin{aligned}
X&=A^{-1}+A^{-1}CD^{-1}C^{\mathsf T}A^{-1},\\
Y&=-A^{-1}CD^{-1},\qquad Z=D^{-1}.
\end{aligned}
\tag{263.5}
$$

只求逆正定块 $A,D$，未求逆 $C$。将四个叶到各自中心的块仍记为 $F_i$，$f_i=|\det F_i|$，有

$$
\begin{aligned}
W_{ab}&=F_aXF_b^{\mathsf T},&
W_{cd}&=F_cZF_d^{\mathsf T},\\
W_{ij}&=F_iYF_j^{\mathsf T}
&&\bigl(i\in\{a,b\},\ j\in\{c,d\}\bigr).
\end{aligned}
$$

令 $f=f_af_bf_cf_d$。对全部 $r$ 个坐标取行列式得到

$$
\begin{aligned}
d_{ab}d_{cd}&=f\det X\det Z,\\
d_{ac}d_{bd}=d_{ad}d_{bc}&=f|\det Y|^2.
\end{aligned}
\tag{263.6}
$$

由 $J^{-1}>0$，$X,Z>0$ 且 $Z-Y^{\mathsf T}X^{-1}Y>0$。取

$$
R=X^{-1/2}YZ^{-1/2},\qquad
I_r-R^{\mathsf T}R
=Z^{-1/2}(Z-Y^{\mathsf T}X^{-1}Y)Z^{-1/2}>0.
$$

故 $R$ 的所有奇异值均小于一，从而

$$
|\det Y|^2
=\det X\det Z\det(R^{\mathsf T}R)
\le\det X\det Z.
\tag{263.7}
$$

因此两个交叉乘积相等，且不大于同侧乘积。这同时覆盖奇异 $Y$，此时两个交叉乘积为零；某个臂块奇异时三个乘积全为零。未使用 $F_i$ 或 $Y$ 的逆。其他核心分裂只需重命名四叶，故叶端口情形已证。

最后回到 (263.3) 中可为内部顶点的原端口。在每个旧端口 $i$ 附加一个 $r$ 维新叶，设其值为 $\xi_i$、旧端口值为 $x_i$，向二次型加入

$$
M\sum_{i\in P}\|\xi_i-x_i\|_2^2.
$$

仅保留四个新叶，所有旧顶点都作为内点。按旧端口、旧内点的次序，增广内块为

$$
J_M=\begin{pmatrix}
Q_{PP}+MI_{4r}&Q_{PI}\\Q_{IP}&K
\end{pmatrix}.
\tag{263.8}
$$

取 $M>\max\{0,-\lambda_{\min}(\mathcal S_4)\}$。由 $K>0$ 及其 Schur 块 $\mathcal S_4+MI_{4r}>0$，有 $J_M>0$。若 $I=\varnothing$，此论证就是 $J_M=\mathcal S_4+MI_{4r}>0$。增广底图仍为森林，全部顶点仍恰有 $r$ 个坐标，四个新端口均为叶，因而刚证的叶端口结论确实适用。

先消旧内点，再消旧端口，得到新叶响应

$$
\begin{aligned}
\mathcal S_M
&=MI_{4r}-M^2(\mathcal S_4+MI_{4r})^{-1}\\
&=\mathcal S_4(I_{4r}+\mathcal S_4/M)^{-1}
\longrightarrow\mathcal S_4.
\end{aligned}
\tag{263.9}
$$

收敛为算子范数收敛：对固定实对称矩阵 $\mathcal S_4$ 的每个特征值 $\lambda$，对应特征值为 $\lambda/(1+\lambda/M)\to\lambda$，且只有有限多个特征值。每个块的绝对行列式及三个配对乘积均为矩阵元的连续函数。“最小值重复”的三元组集合为

$$
\{p_1=p_2\le p_3\}\ \cup\
\{p_1=p_3\le p_2\}\ \cup\
\{p_2=p_3\le p_1\},
$$

是有限个闭集的并。因此将 (263.2) 对 $\mathcal S_M$ 取极限，即得原 $\mathcal S_4$ 的结论。这里的附加叶仅是证明中的辅助构造，原端口的身份、基及单位不变。全程只要求待消内块正定，没有假设 $Q$ 或 $\mathcal S_4$ 全局正定。□

**定理 263.3（任意实块的尖锐最大非对角块误差）。** 对每个整数 $r\ge1$、每个 $u>v\ge0$ 及定义 263.1 的任意响应，以 (259.3) 的循环次序 $(a,b,c,d)$ 定义目标 $S(u,v)\otimes I_r$，则

$$
\delta_{\rm off}:=\max_{i\ne j}
\|(\mathcal S_4)_{ij}-S(u,v)_{ij}I_r\|_{\rm op}
\ge\frac{u-v}{2}.
\tag{263.10}
$$

在同一比较类中此常数可达。这里最优化的是六个非对角块误差的最大值；未要求候选对角块匹配，也不将它等同于整个 $4r\times4r$ 误差矩阵的算子范数。

证明。令 $\delta=\delta_{\rm off}$，反设 $\delta<(u-v)/2$。取 $\ell=u-\delta$、$h=v+\delta$，则 $\ell>h\ge0$。循环相邻对 $ab,bc,cd,da$ 满足 $\|W_{ij}-uI_r\|_{\rm op}\le\delta$，故对任意向量 $x$，

$$
\|W_{ij}x\|_2
\ge u\|x\|_2-\|(W_{ij}-uI_r)x\|_2
\ge\ell\|x\|_2.
$$

因此其每个奇异值至少为 $\ell$，$d_{ij}\ge\ell^r$。相对对 $ac,bd$ 则满足 $\|W_{ij}-vI_r\|_{\rm op}\le\delta$，所以每个奇异值至多为 $h$，$d_{ij}\le h^r$。于是

$$
\begin{aligned}
d_{ab}d_{cd},\ d_{ad}d_{bc}&\ge\ell^{2r},\\
d_{ac}d_{bd}&\le h^{2r}<\ell^{2r},
\end{aligned}
$$

这使中间乘积成为唯一严格最小值，违背定理 263.2。证明使用的是全部奇异值的乘积及其上下界，没有断言任意块的六个算子范数满足 quartet 律。

尖锐性直接复用定理 259.3 的标量达到例及 (259.5)–(259.6)，将其每个顶点块张量 $I_r$。该正权自由 Laplacian 的标量消去内块正定，张量后仍正定；同侧响应为 $-uI_r$，四个交叉响应为 $-(u+v)I_r/2$，对角为 $(2u+v)I_r$。标量误差乘 $I_r$ 的算子范数就是其绝对值，故最大非对角块误差恰为 $(u-v)/2$。此处不重新优化边权；七顶点全二元来源形状的中央边细分也直接沿用该定理。达到例属于可变正权、任意来源形状的数学比较类，不给出固定 INITIAL 轨道或原生固定单位边权子类的达到性。□

**命题 263.4（经典协方差供应项与响应核心的精确对应）。** Anandkumar–Chaudhuri–Hsu–Kakade–Song–Zhang, *Spectral Methods for Learning Multivariate Latent Tree Structure*, [NIPS 2011 会议论文，§2.2 Conditions 1–2、§3.1 Lemma 1 与式 (1)](https://proceedings.neurips.cc/paper_files/paper/2011/file/208e43f0e45c4c78cafadb83d2888cb6-Paper.pdf)，在多变量潜树的二阶矩坐标中给出谱乘积四点关系。Conditions 1–2 位于论文第 3 页，Lemma 1 及式 (1) 位于第 5 页，模型图见第 2 页 Figure 1。这里引用的是该会议版本；线性条件均值与秩条件是其供应关系的条件，不是定义 263.1 自动满足的条件。

对于定理 263.2 的双中心叶核心，在每个 $F_i$ 及 $Y$ 都可逆的子情形，存在如下人工高斯对应。取中心向量 $(h,g)$ 为均值零的联合高斯向量，协方差恰为

$$
\operatorname{Cov}(h,g)=J^{-1}
=\begin{pmatrix}X&Y\\Y^{\mathsf T}&Z\end{pmatrix}>0.
$$

把 $h$ 定为根、$g$ 定为其子节点，则

$$
\mathbb E[g\mid h]=Y^{\mathsf T}X^{-1}h,\qquad
\operatorname{Cov}(g\mid h)=Z-Y^{\mathsf T}X^{-1}Y>0.
$$

对 $i=a,b$ 取 $z_i=F_ih+\eta_i$，对 $i=c,d$ 取 $z_i=F_ig+\eta_i$。四个 $\eta_i$ 相互独立，均为协方差 $I_r$ 的中心高斯噪声，并独立于 $(h,g)$。由此构成同一双中心树上的条件独立模型，而且

$$
\mathbb E[z_iz_j^{\mathsf T}]=W_{ij}\quad(i\ne j).
\tag{263.11}
$$

证明。独立噪声不贡献交叉二阶矩，代入中心协方差即得核心的三个块公式。高斯条件均值线性，$F_i$ 及 $Y$ 可逆使相应条件均值矩阵满秩，中心边的条件均值矩阵为 $Y^{\mathsf T}X^{-1}$；中心边的正定条件协方差同时给出非退化条件分布。因此取文献参数 $d=k=r$ 时，所需 Conditions 1–2 得到满足。两个隐藏中心各有度三，且 (263.7) 的中心收缩在非奇异情形严格小于一。该文 $\det_k$ 是前 $k$ 个奇异值的乘积；在这里 $d=k=r$，正好等于 $|\det W_{ij}|$。其 Lemma 1 式 (1) 对应的比值为

$$
\frac{d_{ac}d_{bd}}{d_{ab}d_{cd}}
=\frac{d_{ad}d_{bc}}{d_{ab}d_{cd}}
=\frac{|\det Y|^2}{\det X\det Z}<1.
\tag{263.12}
$$

观察叶的对角协方差是 $F_iXF_i^{\mathsf T}+I_r$ 或 $F_iZF_i^{\mathsf T}+I_r$，并没有等同于响应对角块。人工协方差是 $J^{-1}$，也没有把整个 $\mathcal S_4$ 或 $\mathcal S_4^{-1}$ 宣称为协方差。星形核心可另取一个协方差为 $A^{-1}$ 的隐藏高斯向量及同样的叶噪声，直接取行列式得到三个乘积全等；不以复制同一隐藏变量的奇异双中心模型套用双中心引理。

若 $F_i$ 或 $Y$ 奇异，文献满秩条件不能这样套用，定理 263.2 的直接代数仍然成立。额外端口接地、只有内块正定、原端口位于内部及空内点集，则分别由 (263.3) 与 (263.8)–(263.9) 承担。因此文献是经典协方差供应项，不是自动适用于全部实际端口响应的定理；上述完整证明也不以所引引理的补充证明为前提。□

**推论 263.5（实际来源的任意块几何与立方体消费者）。** 对定义 257.1 的每个实际有限树 $D_j(t)$，若附加的 $r$ 维块几何逐项满足定义 263.1，则在任何消去内块正定的实参数 $z$ 上，任选四个互异实际地址，包括内部地址，并将其他保留地址接地，均有 (263.2) 与 (263.10)。特别地，对定义 259.1 的实际立方体面响应，目标为

$$
S_{\rm cube}\otimes I_r=S(6/5,2/15)\otimes I_r,
$$

故每个这样的实际端口响应都满足

$$
\max_{i\ne j}\|(\mathcal S_4)_{ij}-(S_{\rm cube})_{ij}I_r\|_{\rm op}
\ge\frac{6/5-2/15}{2}=\frac8{15}.
\tag{263.13}
$$

证明。$D_j(t)$ 的实际父子底图是有限树，故将所声明的块数据代入定理 263.2–263.3 即得。尖锐性在包含可变正权自由 Laplacian 的比较类中，由定理 259.3 的达到例张量 $I_r$ 给出。□

**注记 263.6（仓内新增后果、经典输入与解释范围）。** 相对 §§257–262，新增的仓内数学后果（repo-derived）是：把固定完整纤维的半差误差与立方体 $8/15$ 必要误差，从 §261 的各向同性在位块及标量乘正交边块，扩展到任意实边块与任意实对称在位块，包括奇异、零块；保留下来的四点不变量是绝对行列式。§261 的正交规范证明不处理这些一般数据，其算子范数 quartet 也未在此扩展到任意块。正定 Schur 补、块逆、树度数恒等式、行列式收缩及经典潜树协方差关系是复用的数学输入；§258 的标量附加叶方法和 §259.3 的标量达到例也是复用项。

§258 所引 Sturmfels–Uhler–Zwiernik 的 [arXiv:1902.09905v1, Theorem 2.6](https://arxiv.org/pdf/1902.09905v1) 属于其 Brownian 浓度坐标；§262.4 所引 Shiers–Zwiernik–Aston–Smith 的 [arXiv:1508.00436v2, §1 式 (1)、§2.2 Proposition 1](https://arxiv.org/pdf/1508.00436v2) 属于高斯相关或协方差坐标；§257.2 所引 Dörfler–Bullo 的 [arXiv:1102.2950v1, §2.1 式 (2.1)、Lemma 2.1](https://arxiv.org/pdf/1102.2950v1) 给出其 loopy-Laplacian 条件下的 Kron 机制。这些模型及版本边界保持原义，不构成任意实块响应类的无条件替代定理。本文只作所列供应项与仓内缺口的对应，不作全球新颖性或优先权判断。

在此声明的线性类中，保留实际端口响应的合法内点消元也保留 (263.2)，因而它能认证违反该不变量的固定目标不属于此响应类；(263.10) 还给出对循环目标的定量间隔。这是必要条件，不能据此取得原生块接口、制备和测量权限、实际装置或充分空间实现。它不选择物理空间维数，不给出固定 INITIAL 轨道或单位权原生类的达到例，不推出训练、泛化、效率或因果结论，也不外推到任意神经网络。§262.1 的集体接线仍改变端口合同，处于这里的比较类之外。本节为普通有限维数学推导，不宣称 Lean 核验或冻结状态。

## 追加锚（本行以下为增补区）

## 264. Collective cycles force a mass-normalized dynamical defect

**Definition 264.1 (complete fibres, induced masses and the unchanged clock).** Let $T=(V,E)$ be a nonempty finite tree, let $r\ge1$, and let $H$ be any real symmetric operator on $\mathcal V=\bigoplus_{x\in V}\mathbb R^r$ with counting inner product. Its diagonal blocks are arbitrary symmetric matrices; its edge blocks are arbitrary real matrices, including zero and singular matrices; all nonedge off-diagonal blocks vanish. No positivity or invertibility is imposed on $H$. Fix a surjection $\pi:V\to B$ and orthogonal matrices $R_x\in O(r)$. Put

$$
V_b=\pi^{-1}(b),\qquad n_b=|V_b|>0,\qquad
\mathcal F=\bigoplus_{b\in B}\mathbb R^r,
\qquad \langle f,h\rangle_n=\sum_b n_b f_b^{\mathsf T}h_b.
\tag{264.1}
$$

The collective inclusion, its Hilbert adjoint, and its orthogonal projection are

$$
(Uf)(x)=R_x f_{\pi(x)},\qquad
(U^*v)_b=\frac1{n_b}\sum_{x\in V_b}R_x^{\mathsf T}v_x,
\qquad P=UU^*.
\tag{264.2}
$$

Thus $U$ is an isometry from the mass inner product, not generally from an unweighted coarse inner product. Define

$$
A=U^*HU,\qquad D=(I-P)HU=HU-UA.
\tag{264.3}
$$

The unitary coordinate map $J:\mathcal F\to\mathbb R^{r|B|}$ is $(Jf)_b=\sqrt{n_b}f_b$. Write

$$
\widehat U=UJ^{-1},\qquad
\widehat A=JAJ^{-1}=\widehat U^*H\widehat U,\qquad
\widehat D=DJ^{-1},
\qquad \|D\|=\|\widehat D\|.
\tag{264.4}
$$

All block norms below refer to the orthonormal coordinates of $\widehat A$. In particular

$$
\widehat A_{ab}=\frac1{\sqrt{n_an_b}}
 \sum_{x\in V_a,\,y\in V_b}R_x^{\mathsf T}H_{xy}R_y.
\tag{264.5}
$$

The loop-free support graph has vertices $B$ and an edge $ab$ exactly when $a\ne b$ and $\widehat A_{ab}\ne0$. Symmetry makes this undirected. Its cycles mean simple cycles of length at least three. The heat parameter and the unitary parameter in the following statements are the supplied evolution time of this fixed $H$; neither is a substitution count or a rescaled clock.

**Theorem 264.2 (arbitrary real blocks: cycle strength bounds leakage).** For all data of Definition 264.1, let $b_0,b_1,\ldots,b_{k-1},b_0$ be a simple support cycle, and put

$$
\eta=\min_{j\bmod k}\|\widehat A_{b_jb_{j+1}}\|_{\rm op}>0,
\qquad n_{\max}=\max_{b\in B}n_b.
$$

Then

$$
\|D\|\ge\frac{\eta}{\sqrt{n_{\max}}}.
\tag{264.6}
$$

More precisely, some vertex $x\in V_{b_j}$ has no tree neighbour in one of $V_{b_{j-1}},V_{b_{j+1}}$, say $V_c$, and

$$
\|D\|\ge\frac{\|\widehat A_{b_jc}\|_{\rm op}}{\sqrt{n_{b_j}}}.
\tag{264.7}
$$

Consequently $HU=UA$ forces the loop-free support graph to be a forest. This is only a necessary condition, and no optimality of the constant in (264.6) is asserted.

Proof. Keep all vertices whose labels lie on the cycle, and keep only tree edges between successive cycle labels. If every such vertex had a neighbour in each of its two adjacent cycle classes, this nonempty finite subgraph of a tree would have minimum degree at least two. A finite forest has a vertex of degree at most one: for a component with $v$ vertices its $v-1$ edges have total degree $2v-2$. This is a contradiction. The two required neighbours are distinct, including when $k=3$.

Choose a missing pair $(x,c)$ as in the statement and write $a=\pi(x)$. Since $a\ne c$, edge support gives

$$
(H\widehat U)_{xc}=0,\qquad
\widehat D_{xc}=-\frac1{\sqrt{n_a}}R_x\widehat A_{ac}.
\tag{264.8}
$$

Here the second identity uses $\widehat D=H\widehat U-\widehat U\widehat A$. Restricting the input to the $c$ block and projecting the output to $x$ are contractions. Orthogonality of $R_x$ therefore gives (264.7), hence (264.6). No multiplication around a cycle, inverse edge block, common singular vector, or noncancellation assumption has been used. If $D=0$, every proposed support cycle would contradict (264.6), proving the forest assertion. Empty edge support, one coarse vertex, and two coarse vertices are included.

The qualitative scalar role-colouring antecedent is classical: Purcell–Rombach, [arXiv:1408.5412v1, Lemma 5](https://arxiv.org/html/1408.5412v1), states that a tree's role graph is a tree with at most one self-loop. Its definition requires equal sets of neighbour colours. Here cancellation of real block sums can remove support edges even when actual edges exist, so the complete colouring need not be a role colouring. The missing-neighbour argument is used only on the particular nonzero support cycle, and its block row norm supplies the quantitative mass factor. This establishes the displayed extension directly. □

**Proposition 264.3 (the forest condition is not sufficient).** Even a one-vertex coarse support graph need not give autonomous dynamics. On a two-vertex tree take $r=1$, $R_x=1$, $H=\operatorname{diag}(0,1)$, and the constant map $\pi$. Then $n_b=2$, the loop-free support is empty, and $\|D\|=1/2$.

Proof. The normalized collective vector is $(1,1)/\sqrt2$. Its image under $H$ is $(0,1)/\sqrt2$, whose orthogonal residual is $(-1,1)/(2\sqrt2)$ and has norm $1/2$. The zero edge block is allowed. Thus absence of cycles does not remove diagonal inhomogeneity or other dynamical defects. □

## 265. Same-clock prediction, compressed evolution and hidden initial data

**Theorem 265.1 (quantitative consequences of a collective cycle).** Use Definition 264.1, complexifying all spaces for unitary evolution, and put $\mathcal K=(\operatorname{ran}U)^\perp$ and $C=(I-P)H|_{\mathcal K}$. Relative to the isometric decomposition $\mathcal V=U\mathcal F\oplus\mathcal K$,

$$
H=\begin{pmatrix}A&D^*\\D&C\end{pmatrix}.
\tag{265.1}
$$

For $z\in\{1,i\}$ and $t\ge0$ let

$$
F_z(t)=U^*e^{-ztH}U,\qquad
E_z(t)=(I-P)e^{-ztH}U.
$$

For a cycle of Theorem 264.2, with $\delta=\|D\|$ and $M=\|H\|$, one has

$$
\begin{aligned}
E_z(t)&=-ztD+O(t^2),\\
F_z(t)-e^{-ztA}&=\frac{z^2t^2}{2}D^*D+O(t^3),\\
\lim_{t\downarrow0}\frac{\|E_z(t)\|}{t}
 &=\delta\ge\frac\eta{\sqrt{n_{\max}}},\\
\lim_{t\downarrow0}\frac{\|F_z(t)-e^{-ztA}\|}{t^2}
 &=\frac{\delta^2}{2}\ge\frac{\eta^2}{2n_{\max}}.
\end{aligned}
\tag{265.2}
$$

The remainders are in operator norm on the declared mass spaces. Explicitly, for either $z$,

$$
\begin{aligned}
\|E_z(t)+ztD\|&\le\tfrac12t^2M^2e^{tM},\\
\|F_z(t)-e^{-ztA}-\tfrac12z^2t^2D^*D\|
 &\le\tfrac13t^3M^3e^{tM}.
\end{aligned}
\tag{265.3}
$$

Thus corresponding finite-time lower bounds are obtained by subtracting these right sides from $t\eta/\sqrt{n_{\max}}$ and $t^2\eta^2/(2n_{\max})$, respectively. Their positive time windows depend on the actual $M$; no uniform window for unbounded arbitrary diagonals is asserted. For every fixed $f\in\mathcal F$,

$$
\|(I-P)e^{-itH}Uf\|^2
=t^2\|Df\|^2+O(t^3),
\qquad
\|U^*e^{-itH}Uf\|_n^2
=\|f\|_n^2-t^2\|Df\|^2+O(t^3).
\tag{265.4}
$$

In particular the cycle forces leakage for some unit input, not for every input. The compressed family itself fails the semigroup law at second order:

$$
\lim_{t\downarrow0}
\frac{\|F_z(2t)-F_z(t)^2\|}{t^2}
=\delta^2\ge\frac{\eta^2}{n_{\max}}.
\tag{265.5}
$$

Proof. Self-adjointness and (264.3) give (265.1). The identity $U^*H^2U=A^2+D^*D$ follows by multiplying its blocks. The exponential power series therefore gives the first two expansions. The tail from order two in the first expansion is bounded by $\sum_{j\ge2}(tM)^j/j!\le t^2M^2e^{tM}/2$. Since $\|A\|\le M$, the two tails from order three in the second expansion total at most $2\sum_{j\ge3}(tM)^j/j!\le t^3M^3e^{tM}/3$. This proves (265.3). Dividing the expansions by $t$ or $t^2$, using norm continuity and $\|D^*D\|=\|D\|^2$, gives (265.2). Theorem 264.2 supplies the lower bounds.

For $z=i$, square the first expansion on the fixed input and use the orthogonal Pythagorean decomposition of the norm-preserving $e^{-itH}Uf$ to obtain (265.4). Finally the exact identity

$$
F_z(2t)-F_z(t)^2
=U^*e^{-ztH}(I-P)e^{-ztH}U
$$

has expansion $z^2t^2D^*D+O(t^3)$, proving (265.5). All power series are finite-dimensional norm-convergent series. No semigroup positivity is needed, so negative or zero eigenvalues and singular blocks remain in scope. □

**Theorem 265.2 (what prediction must additionally retain).** For the same data and either $z\in\{1,i\}$, an arbitrary initial vector has the unique decomposition $v(0)=Uu_0+w_0$ with $w_0\in\mathcal K$. The visible coordinate $u(t)=U^*v(t)$ of $\dot v=-zHv$ satisfies

$$
\begin{aligned}
\dot u(t)={}&-zAu(t)
 +z^2\int_0^t D^*e^{-z(t-s)C}D\,u(s)\,ds
 -zD^*e^{-ztC}w_0,\\
K_z(t)&=D^*e^{-ztC}D,\qquad
\|K_z(0)\|=\|D\|^2\ge\eta^2/n_{\max}
\quad\text{when the support contains the stated cycle.}
\end{aligned}
\tag{265.6}
$$

Consequently it is impossible to predict every initial vector's visible evolution by an autonomous law depending only on its current $U^*v$ when that support contains a cycle. More quantitatively, set

$$
T_z(t)=U^*e^{-ztH}|_{\mathcal K}.
$$

For every proposed predictor $p_t:\mathcal F\to\mathcal F$, without a linearity assumption,

$$
\sup_{\substack{w\in\mathcal K\\\|w\|\le1}}
 \|U^*e^{-ztH}w-p_t(0)\|_n
\ge\|T_z(t)\|,
\qquad
\lim_{t\downarrow0}\frac{\|T_z(t)\|}{t}
=\|D\|\ge\eta/\sqrt{n_{\max}}.
\tag{265.7}
$$

This is a statement about the declared signed or complex amplitude coordinates and all initial vectors. It grants no additional preparation or observation operation.

Proof. The block equations are $\dot u=-zAu-zD^*w$ and $\dot w=-zDu-zCw$. Variation of constants gives

$$
w(t)=e^{-ztC}w_0-z\int_0^t e^{-z(t-s)C}Du(s)\,ds.
$$

Substitution proves (265.6), retaining arbitrary hidden initial data. This is the classical linear memory identity of Gouasmi–Parish–Duraisamy, [arXiv:1611.06277v2, §2.1, equations (2.1)–(2.3)](https://arxiv.org/pdf/1611.06277v2), with their four blocks equal to $-zA,-zD^*,-zD,-zC$. Their subsequent choice of zero unresolved initial condition is not imposed here. The additional consequence is that a support cycle forces the displayed positive norm at the origin of the memory kernel.

The expansion $T_z(t)=-ztD^*+O(t^2)$ proves its norm limit. Choose a unit hidden vector maximizing $\|T_z(t)w\|$. The two possible starts $w$ and $-w$ both have current visible coordinate zero. The triangle inequality applied to their predicted errors gives

$$
2\|T_z(t)w\|
\le\|T_z(t)w-p_t(0)\|_n+
   \|-T_z(t)w-p_t(0)\|_n,
$$

which proves (265.7). At the derivative level, the hidden-to-visible map is $-zD^*$ and the same two-point argument has exact radius $\|D\|$. Nonzero $D$ therefore forbids all-state autonomous prediction, irrespective of the choice of coarse generator. □

**Proposition 265.3 (cycle-forced observable enlargement survives static elimination).** If the support contains a cycle of Theorem 264.2, every $H$-invariant linear observable space containing $\operatorname{ran}U$ has dimension at least $r|B|+\operatorname{rank}D\ge r|B|+1$. A single static elimination does not supply autonomous dynamics of the original collective coordinates. The intermediate Schur and future-closure formulas are as follows. At any spectral parameter $\lambda$ for which $C-\lambda I$ is invertible, solving the hidden equation of $(H-\lambda I)v=f$ gives the visible coefficient

$$
A-\lambda I-D^*(C-\lambda I)^{-1}D.
\tag{265.8}
$$

It does not remove (265.6)'s hidden forcing in a time evolution. A sufficient autonomous linear observable space is

$$
\mathcal W_\infty=
 \operatorname{span}\{H^jUf:f\in\mathcal F,\ j\ge0\}.
\tag{265.9}
$$

Its first enlargement has dimension

$$
\dim\bigl(\operatorname{ran}U+H\operatorname{ran}U\bigr)
=r|B|+\operatorname{rank}D.
\tag{265.10}
$$

Thus a support cycle forces at least one additional linear observable direction; (265.10) does not identify this number with a cycle rank or with a minimum native memory cost.

Proof. Write the hidden equation as $(C-\lambda I)w=f_{\mathcal K}-Du$ and substitute its unique solution into the visible equation. This is the usual Schur identity, with its explicit invertibility hypothesis. The static electrical specialization is the Kron mechanism of Dörfler–Bullo, [arXiv:1102.2950v1, §2.1 and Lemma 2.1](https://arxiv.org/pdf/1102.2950v1); their irreducible loopy-Laplacian hypotheses do not imply every arbitrary-block datum here belongs to that network class.

The space (265.9) is $H$-invariant and is the smallest invariant subspace containing $\operatorname{ran}U$: invariance follows by increasing $j$, and minimality by induction. Self-adjointness makes its orthogonal complement invariant, so projecting the evolution to this space is autonomous and retains the original visible coordinates. Equality of all visible futures for two vectors is equivalent to their difference being orthogonal to (265.9): differentiate $U^*e^{-ztH}$ at zero in one direction, and use its convergent series in the other. These are the existing future-observable closure and residual-quotient mechanisms; in particular see `observableClosure` and its private invariance proof in [DynamicsResidualQuotient](../../../D5/S3/QuantumStates/DynamicsResidualQuotient.lean), and [AllFutureStatisticsSufficiency](../../../D5/S3/Quantum/Fibers/AllFutureStatisticsSufficiency.lean). They are intermediate suppliers, not new general closure theorems here.

Finally $HU=UA+D$ and $\operatorname{ran}D\perp\operatorname{ran}U$, so the first enlarged space is the orthogonal direct sum $\operatorname{ran}U\oplus\operatorname{ran}D$. This proves (265.10); the cycle estimate forces $D\ne0$. Later enlargement can be necessary. The existing [MemoryDimensionFormula](../../../D5/S3/Observer/LinearMemory/MemoryDimensionFormula.lean) concerns linear future-observable dimension minus current rank, whereas the next section counts deterministic vertex labels. Neither statement licenses an arbitrary real-encoder or acquisition-cost inference. □

## 266. Scalar cycles and deterministic same-clock refinement

**Definition 266.1 (positive masses, killing and exact label dynamics).** Let $T=(V,E)$ be a nonempty finite tree, $c_{xy}=c_{yx}>0$ on every edge, $\mu_x>0$, and $\kappa_x\ge0$. The backward killed generator in its given time is

$$
(Gf)(x)=\sum_{y\sim x}\frac{c_{xy}}{\mu_x}(f(y)-f(x))-\kappa_xf(x).
\tag{266.1}
$$

For a surjection $\pi:V\to B$, put $\nu_b=\sum_{x\in V_b}\mu_x$, and let $H_\pi$ be the simple graph with edge $ab$ when an actual edge joins the distinct classes $a,b$. It is connected. Write $m=|B|$, $e=|E(H_\pi)|$, $\beta=e-m+1\ge0$. A deterministic refinement is a map $\psi:V\to C=\operatorname{im}\psi$ with $\pi=h\psi$. It is exact on the same clock when a killed generator $Q^\psi$ satisfies

$$
G U_\psi=U_\psi Q^\psi,\qquad
(U_\psi f)(x)=f(\psi(x)).
\tag{266.2}
$$

In finite dimension this is equivalent to the corresponding all-time heat intertwining, by differentiation at zero and by exponential series. Testing class indicators shows that (266.2) is exactly constancy, on each $\psi$ class, of all off-class sums $\sum_{\psi(y)=c}c_{xy}/\mu_x$ and of $\kappa_x$. Indeed off-class indicators give the sums, and the constant function gives $G1=-\kappa$; the converse follows by expanding $GU_\psi f$. This is ordinary lumpability, not a new criterion. Nilsson Jacobi–Görnerup, [arXiv:0710.1986v1, Theorem 1 and equation (2.1)](https://arxiv.org/pdf/0710.1986v1), states the finite stochastic row-sum supplier. For killing one may add an absorbing cemetery and uniformize the finite rates; no cemetery state is counted in $C$.

**Theorem 266.2 (cycle rank forces extra exact labels).** Every exact deterministic refinement of Definition 266.1 satisfies

$$
|C|\ge e+1=m+\beta,\qquad |C|-m\ge\beta.
\tag{266.3}
$$

The statement covers all positive edge conductances and masses, every nonnegative killing function, and every collective partition, including $m=1$ and $\beta=0$. It gives a necessary label count, not existence at that count.

Proof. The graph $H_\pi$ is connected because any tree path projects to a walk after successive equal labels are suppressed. The same holds for $H_\psi$. On an edge $ab$ of $H_\psi$, the common outgoing rate from $a$ to $b$ in (266.2) is positive: it is positive at the endpoint of an actual edge and constant throughout $a$. Reversing the actual edge proves the analogous positivity from $b$ to $a$. Thus every vertex in $a$ has some neighbour in $b$.

If $H_\psi$ had a simple cycle, keeping only its labels and its successive-label edges would again produce a nonempty finite forest of minimum degree at least two. Therefore $H_\psi$ is a tree and has $|C|-1$ edges. This is the classical qualitative no-cycle input used internally in the counting argument; killing does not change its off-class positivity.

Every edge of $H_\pi$ is represented by an actual tree edge. Its endpoints have different $\psi$ labels because $\pi=h\psi$, so it is the image of some edge of $H_\psi$. Different $H_\pi$ edges require different representing $H_\psi$ edges. Hence $e\le|E(H_\psi)|=|C|-1$, proving (266.3). Internal-$\pi$ edges in $H_\psi$ can collapse and only increase the available count; they do not invalidate this inequality. No assumption that the fibres are connected has been made. □

**Theorem 266.3 (uniform off-label row error and its optimal constant).** For any killed coarse generator $Q$ on $B$, define

$$
\Delta(G,\pi,Q)=
\max_{x\in V}\max_{b\ne\pi(x)}
\left|\sum_{\pi(y)=b}\frac{c_{xy}}{\mu_x}-Q_{\pi(x),b}\right|,
\tag{266.4}
$$

where only actual neighbours contribute, and an empty maximum is zero. If $Q$ has a bidirectional simple cycle all of whose directed rates are at least $\eta>0$, then

$$
\Delta(G,\pi,Q)\ge\eta.
\tag{266.5}
$$

The factor one is sharp in the unrestricted weighted-tree comparison class, even when $Q$ is the induced mass-weighted compression of $G$. This does not assert sharp attainment within a fixed native source orbit.

Proof. The missing-neighbour argument applied to the cycle labels gives a vertex $x$ with no neighbour in an adjacent cycle class $b$. The actual sum in (266.4) is zero, while the specified directed $Q$ rate is at least $\eta$. This proves (266.5), independently of all diagonal and killing terms.

For sharpness fix $k\ge3$. Take the path $v_0,\ldots,v_k$, masses one, all edge conductances $2\eta$, and zero killing. Give $v_j$ label $j$ for $0\le j<k$, and give $v_k$ label zero. The induced masses are $\nu_0=2$, $\nu_j=1$ for $j\ne0$. The compressed conductance between each pair of neighbouring cycle labels is $2\eta$. Its coarse generator therefore has rate $\eta$ from zero to either adjacent label, and rate $2\eta$ from every other label to each of its two neighbours. Its minimum directed cycle rate is exactly $\eta$.

At each internal path vertex all off-label rates agree with this $Q$. At either endpoint, the existing adjacent-label rate is $2\eta$ rather than $\eta$, and the other adjacent-label rate is zero rather than $\eta$; every other off-label entry agrees. Thus the maximum error is exactly $\eta$. All masses and conductances are strictly positive and finite. This proves sharpness without altering the clock or discarding endpoint rows. □

## 267. A legal nine-occurrence native cycle with inherited killing

**Proposition 267.1 (actual $T_4$, four masses and the full source operator).** Use the source and added geometry of Definitions 257.1 and 55.1–55.2 in the [first continuation](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION.md). Initialize at $\alpha$ and perform four accepted whole substitutions at fixed leaf cap $\mathrm{cap}_H\ge5$. The actual tree is

$$
T_4=\langle\langle\langle\beta,\alpha\rangle,\beta\rangle,
                  \langle\beta,\alpha\rangle\rangle.
\tag{267.1}
$$

Its addresses, in a fixed order, are

$$
(o,L,R,LL,LR,RL,RR,LLL,LLR),\qquad o=\varepsilon.
\tag{267.2}
$$

Define four collective classes, without identifying actual vertices of the source,

$$
\begin{aligned}
V_a&=\{LLL,LLR,RL,RR\},& V_b&=\{LL,LR\},\\
V_c&=\{o,R\},& V_d&=\{L\}.
\end{aligned}
\tag{267.3}
$$

With $R_x=1$ the induced mass matrix is $N_9=\operatorname{diag}(4,2,2,1)$. For every native $a_0,g>0$ retain

$$
H_9=a_0L_{D_4(\alpha)}-g\Phi_9,
\qquad
\Phi_9=\operatorname{diag}(1,\tfrac12,\tfrac12,
 \tfrac14,\tfrac14,\tfrac14,\tfrac14,\tfrac18,\tfrac18).
\tag{267.4}
$$

The diagonal of $L_D$ is $(2,3,3,3,3,3,3,3,3)$ and its off-diagonal is $-1$ exactly on

$$
(o,L),\ (o,R),\ (L,LL),\ (L,LR),\ (R,RL),\ (R,RR),\ (LL,LLL),\ (LL,LLR).
\tag{267.5}
$$

All other off-diagonal entries vanish. In coarse value coordinates the restricted kinetic and potential forms are

$$
S_9=\begin{pmatrix}
12&-2&-2&0\\-2&6&0&-2\\-2&0&3&-1\\0&-2&-1&3
\end{pmatrix},
\qquad V_9=\operatorname{diag}(\tfrac34,\tfrac12,\tfrac32,\tfrac12).
\tag{267.6}
$$

Thus

$$
A_9=N_9^{-1}(a_0S_9-gV_9),\qquad
\widehat A_9=N_9^{-1/2}(a_0S_9-gV_9)N_9^{-1/2}.
\tag{267.7}
$$

The collective conductances are $c_{ab}=c_{ac}=c_{bd}=2$, $c_{cd}=1$, and zero for the other distinct pairs. The inherited kinetic killing conductances are $(8,2,0,0)$, not zero. The support is the four-cycle $a,b,d,c,a$ with

$$
\eta_9=a_0/\sqrt2,\qquad n_{\max}=4,\qquad
\|D_9\|\ge a_0/(2\sqrt2).
\tag{267.8}
$$

Proof. Successive actual sources have leaf counts $1,1,2,3,5$. Each complete candidate therefore passes a fixed leaf-count cap at least five. This is a legal finite prefix from immutable INITIAL $\alpha$, provided no Stop has occurred. The substitutions and addressed shape agree with Proposition 260.1; no complete ball has replaced this irregular domain.

The field values in (267.4) are exactly $2^{-|p|}$ at these addresses. The source kinetic law gives root diagonal two and every other diagonal three, together with (267.5). The current leaves are $LR,RL,RR,LLL,LLR$, each retaining its two absent-child seams. For collective values $(u_a,u_b,u_c,u_d)$, the internal edge $oR$ contributes zero, and the remaining difference terms plus all absent-child terms give

$$
\begin{aligned}
\langle Uu,L_DUu\rangle={}&
2|u_a-u_b|^2+2|u_a-u_c|^2
+2|u_b-u_d|^2+|u_c-u_d|^2\\
&+8|u_a|^2+2|u_b|^2.
\end{aligned}
\tag{267.9}
$$

Expanding gives $S_9$. Summing the actual common field over each class gives $V_9$: in $a$ the sum is $1/8+1/8+1/4+1/4=3/4$, in $b$ it is $1/2$, in $c$ it is $1+1/2=3/2$, and in $d$ it is $1/2$. Since $U^*U=I$ in the mass norm, (267.7) follows. The four nonzero normalized off-diagonal magnitudes are $a_0/\sqrt2,a_0/\sqrt2,\sqrt2a_0,a_0/\sqrt2$. Theorem 264.2 gives (267.8). Negative potential changes no off-diagonal edge or source killing seam. □

**Proposition 267.2 (all nine-occurrence first leakage coefficients).** In (267.2) let $e_p$ be the unit counting vector at $p$. An orthonormal basis of the hidden space consists of

$$
\begin{aligned}
h_1&=(e_{LLL}-e_{LLR})/\sqrt2,&
h_2&=(e_{RL}-e_{RR})/\sqrt2,\\
h_3&=(e_{LLL}+e_{LLR}-e_{RL}-e_{RR})/2,\\
h_4&=(e_{LL}-e_{LR})/\sqrt2,&
h_5&=(e_o-e_R)/\sqrt2.
\end{aligned}
$$

Relative to the normalized coarse coordinate order $(a,b,c,d)$, the first two rows of $\widehat D_9$ are zero and its remaining rows are

$$
E_9=\begin{pmatrix}
g/16&-a_0/\sqrt2&a_0/\sqrt2&0\\
-a_0/\sqrt2&0&0&0\\
a_0/\sqrt2&0&-a_0/2-g/4&-a_0/\sqrt2
\end{pmatrix}.
\tag{267.10}
$$

In particular, with $f_d=N_9^{-1/2}e_d=e_d$ in coarse value coordinates,

$$
\|D_9f_d\|^2=a_0^2/2,
\qquad
\|(I-P)e^{-itH_9}Uf_d\|^2
=\tfrac12a_0^2t^2+O(t^3).
\tag{267.11}
$$

For every coarse orthonormal coordinate vector $\xi$, its full first leakage coefficient is exactly $\|E_9\xi\|^2$. The compressed evolution's second-order discrepancy is $z^2t^2E_9^{\mathsf T}E_9/2$ in (265.2), where $z\in\{1,i\}$ is the evolution parameter.

Proof. The five displayed vectors have disjoint-class support except for the three mutually orthogonal contrasts in class $a$. They are orthogonal to every class-constant vector, and their number is $9-4$, proving that they form the hidden basis. Therefore every entry can be computed as $\langle h_j,H_9\widehat Ue_b\rangle$ without forming $P$ separately.

The two siblings in either $h_1$ or $h_2$ have the same diagonal and the same actual parent, so those two rows vanish. On $h_3$, the normalized $a$ input has value $1/2$ on each of its four sites. The two deep sites have diagonal value $(3a_0-g/8)/2$ and the two shallow sites $(3a_0-g/4)/2$; their contrast is $g/16$. The normalized $b$ input gives $-a_0/\sqrt2$ at each deep site and zero at the shallow sites, giving contrast $-a_0/\sqrt2$. The normalized $c$ input reverses these two pairs, giving $a_0/\sqrt2$; the $d$ input contributes zero.

On $h_4$, only the $a$ input has a nonzero contrast: the $LL$ row receives two leaf contributions of $-a_0/2$, while the $LR$ row receives none, yielding $-a_0/\sqrt2$. The two sites have equal source potential $1/4$, so the $b$ diagonal input gives no contrast. On $h_5$, the $a$ column has values zero and $-a_0$ at $o,R$, respectively; the $c$ column has values $(a_0-g)/\sqrt2$ and $(2a_0-g/2)/\sqrt2$, including the internal $oR$ edge; the $d$ column has values $-a_0,0$. Their contrasts are the last row of (267.10); the $b$ column is zero there. This proves every matrix entry. Applying (265.4) proves (267.11) and the all-input assertion. □

## 268. A four-leaf INITIAL and an underdetermined proposed coefficient

**Definition 268.1 (the seven-occurrence source before choosing an observation).** Choose the actual INITIAL

$$
t=\langle\langle\alpha,\alpha\rangle,
          \langle\alpha,\alpha\rangle\rangle,
\qquad \mathrm{cap}_H\ge4,
\tag{268.1}
$$

and use its initial version $D_0(t)$. It has addresses $(o,L,R,LL,LR,RL,RR)$, four leaves, and no substitution needs to be accepted to reach this version. Its original labels, order, INITIAL, cap, Read and Stop are retained. For every native $a_0,g>0$, its source operator is

$$
H_7=a_0L_D-g\operatorname{diag}
 (1,\tfrac12,\tfrac12,\tfrac14,\tfrac14,\tfrac14,\tfrac14).
\tag{268.2}
$$

The root kinetic diagonal is two, all other kinetic diagonals are three, and the off-diagonal is $-a_0$ on exactly the pairs $(o,L),(o,R),(L,LL),(L,LR),(R,RL),(R,RR)$. These source data do not specify a partition or a vector named $f_b$; consequently a coefficient $\|Df_b\|^2$ is not uniquely specified by them. In particular, a proposed value $7a_0^2/6$ without those additional data is underdetermined. The next proposition gives the source-correct formula and a contrary value before a second, expressly conditional observation is considered.

**Proposition 268.2 (variance formula and a legal contrary coefficient).** For any scalar collective partition with $R_x=1$, any real symmetric source-supported $H$, and the unit mass-normalized class vector $f_b=\mathbf1_{\{b\}}/\sqrt{n_b}$, one has

$$
\begin{aligned}
s_b(x)&=\frac1{\sqrt{n_b}}\sum_{y\in V_b}H_{xy},\\
\|Df_b\|^2
&=\sum_{a\in B}\left[
 \sum_{x\in V_a}|s_b(x)|^2
 -\frac1{n_a}\left|\sum_{x\in V_a}s_b(x)\right|^2\right].
\end{aligned}
\tag{268.3}
$$

An unnormalized indicator multiplies this squared coefficient by $n_b$. On the legal source (268.1) with exactly $H_7$ and every $a_0,g>0$, take

$$
V'_a=\{LL,LR,RL,RR\},\qquad
V'_b=\{L\},\quad V'_c=\{o\},\quad V'_d=\{R\},
\qquad f'_b=e_b.
\tag{268.4}
$$

Its induced masses are $N'_7=\operatorname{diag}(4,1,1,1)$. Its kinetic and potential forms are

$$
S'_7=\begin{pmatrix}
12&-2&0&-2\\-2&3&-1&0\\0&-1&2&-1\\-2&0&-1&3
\end{pmatrix},\qquad
V'_7=\operatorname{diag}(1,\tfrac12,1,\tfrac12),
\quad
\widehat A'_7=(N'_7)^{-1/2}(a_0S'_7-gV'_7)(N'_7)^{-1/2}.
\tag{268.5}
$$

It has a four-cycle collective support, but

$$
\|D'_7f'_b\|^2=a_0^2\ne7a_0^2/6.
\tag{268.6}
$$

Indeed, with $h=(e_{LL}+e_{LR}-e_{RL}-e_{RR})/2$, its entire nonzero hidden row is

$$
\langle h,\widehat D'_7\,\cdot\,\rangle
=\begin{pmatrix}0&-a_0&0&a_0\end{pmatrix}.
\tag{268.7}
$$

Thus a partition-independent assertion of $7/6$ is false. This does not refute the same coefficient under some further, explicitly prescribed partition.

Proof. The orthogonal projection replaces each scalar class by its arithmetic mean. Subtracting these means and expanding the squared norm gives (268.3), including all diagonal terms of $H$. In (268.4), the two left leaf seams, root-left seam, root-right seam and two right leaf seams give the cycle $a,b,c,d,a$ with conductances $2,1,1,2$. Its kinetic killing conductances are $(8,0,0,0)$. Expanding these four difference terms plus $8|u_a|^2$ gives $S'_7$; summing the common field gives $V'_7$.

On its four leaves, $H_7e_L$ has values $(-a_0,-a_0,0,0)$ and mean $-a_0/2$. Their residual squared norm is $4(a_0/2)^2=a_0^2$. Every other class is a singleton. The potential is constant on the leaf class, and the $b$ input is supported on a singleton, so this calculation holds for all $g$. More generally the normalized $a$ input has no hidden component, the $b,d$ inputs give the opposite leaf contrasts $-a_0h,a_0h$, and the $c$ input gives zero at every leaf. The remaining two hidden directions are sibling differences and have zero rows. This proves (268.7) and all assertions. □

**Definition 268.3 (a second, explicitly conditional observation).** On the same source (268.1), specify instead

$$
\begin{aligned}
V_a&=\{LL,LR,RR\},&V_b&=\{L\},\\
V_c&=\{o,RL\},&V_d&=\{R\},\\
N_7&=\operatorname{diag}(3,1,2,1),&
f_b&=N_7^{-1/2}e_b=e_b.
\end{aligned}
\tag{268.8}
$$

This is an additional choice of observation, not a reconstruction of an unspecified source datum. The source operator, clock, actual vertices and their masses one have not changed; the induced coarse masses follow the displayed classes. Neither (268.4) nor (268.8) is selected uniquely by the source. Both use the same unit singleton input $Uf_b=e_L$, so their differing coefficients cannot be attributed to rescaling that input.

**Proposition 268.4 (the conditional $7/6$ value for every native $a_0,g$).** Under (268.8), for every $a_0,g>0$ the restricted forms and normalized operator are

$$
\begin{aligned}
S_7&=\begin{pmatrix}
9&-2&0&-1\\-2&3&-1&0\\0&-1&5&-2\\-1&0&-2&3
\end{pmatrix},\\
V_7&=\operatorname{diag}(\tfrac34,\tfrac12,\tfrac54,\tfrac12),\\
\widehat A_7&=N_7^{-1/2}(a_0S_7-gV_7)N_7^{-1/2}.
\end{aligned}
\tag{268.9}
$$

The conductances are $c_{ab}=2,c_{bc}=1,c_{cd}=2,c_{da}=1$, with killing conductances $(6,0,2,0)$. The cycle strength is $\eta_7=a_0/\sqrt3$, hence $\|D_7\|\ge a_0/3$. For the specified $f_b$,

$$
\|D_7f_b\|^2=\frac76a_0^2
\quad\text{for all }a_0,g>0.
\tag{268.10}
$$

Proof. The seven addresses and all kinetic diagonals are those of Definition 268.1. With collective values $u$, the restricted kinetic form is

$$
2|u_a-u_b|^2+|u_b-u_c|^2
+2|u_c-u_d|^2+|u_d-u_a|^2
+6|u_a|^2+2|u_c|^2.
\tag{268.11}
$$

This proves the conductances, killing, and $S_7$. The common field sums are $3/4,1/2,1+1/4,1/2$, proving $V_7$. The four normalized cycle magnitudes are $2a_0/\sqrt3,a_0/\sqrt2,\sqrt2a_0,a_0/\sqrt3$, proving the asserted $\eta_7$ and the bound from Theorem 264.2.

For (268.10), $Uf_b=e_L$. On class $a$, $H_7e_L$ has values $(-a_0,-a_0,0)$, whose mean is $-2a_0/3$ and whose residual squared norm is

$$
2(a_0/3)^2+(2a_0/3)^2=2a_0^2/3.
$$

On class $c$ its values are $(-a_0,0)$, with residual squared norm $a_0^2/2$. Classes $b,d$ are singletons and have zero residual. The diagonal potential acts on the one-point support $L$ only, so it contributes no hidden component for this vector, for any $g$. Summing $2/3+1/2$ proves (268.10). This conditional value neither changes (268.6) nor makes the partition-free proposal well-defined. □

**Proposition 268.5 (complete leakage matrix for the second observation).** An orthonormal hidden basis for (268.8) is

$$
h_0=(e_{LL}-e_{LR})/\sqrt2,\quad
h_a=(e_{LL}+e_{LR}-2e_{RR})/\sqrt6,\quad
h_c=(e_o-e_{RL})/\sqrt2.
$$

The $h_0$ row of $\widehat D_7$ is zero; the other two rows are

$$
E_7=\begin{pmatrix}
0&-\sqrt{2/3}\,a_0&0&\sqrt{2/3}\,a_0\\
0&-a_0/\sqrt2&-a_0/2-3g/8&0
\end{pmatrix}.
\tag{268.12}
$$

For every normalized coarse coordinate vector $\xi=(\xi_a,\xi_b,\xi_c,\xi_d)$,

$$
\|D_7J^{-1}\xi\|^2
=\tfrac23a_0^2|\xi_d-\xi_b|^2
 +\left|\tfrac{a_0}{\sqrt2}\xi_b+
                (\tfrac{a_0}{2}+\tfrac{3g}{8})\xi_c\right|^2.
\tag{268.13}
$$

In particular the unitary leakage for $f_b$ is $7a_0^2t^2/6+O(t^3)$, and its compressed second-order scalar discrepancy is

$$
\langle e_b,(\widehat F_z(t)-e^{-zt\widehat A_7})e_b\rangle
=\frac{7z^2a_0^2}{12}t^2+O(t^3),
\quad z\in\{1,i\}.
\tag{268.14}
$$

Here $\widehat F_z=JF_zJ^{-1}$. These are fixed-source, full-parameter formulas; $D_7J^{-1}e_a=0$ is a genuine exceptional input, so a positive coefficient for every input would be false.

Proof. The hidden dimension is $7-4=3$ and the displayed class contrasts are orthonormal. The $h_0$ row vanishes because $LL,LR$ have equal diagonals and the same parent. At $h_a$ only the $b,d$ columns contribute: their address values are $(-a_0,-a_0,0)$ and $(0,0,-a_0)$ on $(LL,LR,RR)$, giving the first row. At $h_c$, the $b$ column has values $(-a_0,0)$ on $(o,RL)$. The normalized $c$ column has values $(2a_0-g)/\sqrt2$ and $(3a_0-g/4)/\sqrt2$; taking the contrast gives $-a_0/2-3g/8$. The $d$ column gives $(-a_0,-a_0)$ and hence no contrast, and the $a$ column vanishes on both sites. This proves (268.12) entry by entry, then (268.13) by squaring. Equations (265.2) and (265.4) prove (268.14) and the leakage assertion. □

## 269. Source-faithful consequences and their mathematical limits

**Proposition 269.1 (what the two native cycles require).** The native kinetic backward generator on either domain of §§267–268 is $G=-a_0L_D$, with mass one at each occurrence, conductance $a_0$ on every actual edge, and killing rate $2a_0$ at each current leaf and zero elsewhere. For either partition (267.3) or (268.8), $m=e=4$ and $\beta=1$. Therefore every exact deterministic same-clock refinement needs at least five noncemetery labels. Its induced kinetic coarse generator has killing rates $a_0(2,1,0,0)$ for (267.3), and $a_0(2,0,1,0)$ for (268.8). Uniform off-label row approximation to these induced generators has error at least $a_0/2$ and $a_0/3$, respectively.

For the native amplitude operators with every $a_0,g>0$, the collective constraints still have static cyclic forms, but cannot give autonomous same-clock evolution on all coarse inputs. Their memory-kernel norms at zero are at least $a_0^2/8$ and $a_0^2/9$, respectively, and their full first leakage matrices are (267.10) and (268.12). These conclusions concern predictive information and retention of hidden modes, not selection of a physical spatial dimension.

Proof. The finite-source form (55.4) is the sum of actual internal unit seam differences and two killing terms per current leaf; multiplying by $a_0$ gives the displayed generator. Dividing the killing conductances of (267.9) and (268.11) by their induced masses gives the coarse killing rates. For the first partition, its four directed pairs have minimum rate $\min\{2a_0/4,2a_0/2,2a_0/1,a_0/2\}=a_0/2$; for the second the minimum is $a_0/3$ on $a\to d$. Theorems 266.2–266.3 now apply. This counts refinements only; it asserts neither native attainment at five nor a minimum for arbitrary real encoders, hidden Hilbert spaces or native records.

For the amplitudes, (267.8), (268.9) and Theorems 265.1–265.2 give the kernel bounds and exclude exact all-input intertwining. The potential changes the displayed hidden matrices and has not been discarded. The heat law $e^{-tH_j}$ also satisfies Theorem 265.1 algebraically, but for $g>0$ it is not being called the source's substochastic kinetic heat law; that original law is $e^{-ta_0L_D}$. No attractive-potential semigroup has replaced it. All finite-dimensional operator domains are the entire stated spaces. □

**Definition 269.2 (supplier correspondence and interpretation).** The source premises are the exact actual-tree definitions and proofs in first Continuation §§55.1–55.3 and this volume §§257–263, including the distinction between an actual-port Schur response and a collective constrained quadratic form. The quantitative arbitrary-block cycle defect (264.6), its topology-forced short-time and hidden-initial prediction bounds, the scalar refinement count (266.3), the sharp row constant with induced masses, and the two addressed full-parameter residual matrices are the additional deductions here (repo-derived). The qualitative role-graph theorem, row-sum lumpability, Schur elimination, exponential expansion, variation of constants and invariant observable closure are the attributed intermediate inputs.

Repository deterministic and linear descent suppliers include [DynamicsDescent](../../../D5/S0/Rewriting/Quotients/DynamicsDescent.lean), [LinearProjectionDescentCriterion](../../../D5/S3/Observer/Dynamics/LinearProjectionDescentCriterion.lean) and [StrongLumpabilityDescent](../../../D5/S3/Observer/ProbabilisticClosure/StrongLumpabilityDescent.lean). [OperatorSystemTowerStability](../../../D5/S3/Quantum/Fibers/OperatorSystemTowerStability.lean) concerns permanence after equality of consecutive operator-system stages; [QuotientResidualTransport](../../../D5/S3/Quantum/Fibers/QuotientResidualTransport.lean) concerns compatible quotient transitions and isometric residual costs. Neither supplies a finite actual-tree cycle-defect estimate. [CapacityPortSeparationAbsorption](../../../D5/S3/Combinatorics/Graph/Walks/CapacityPortSeparationAbsorption.lean), including its private routing and terminal-distance arguments, concerns incidence capacities and terminal separation; it assumes no tree and has no clock, update or propagation operator.

[Continuation V §§120.4–120.7](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_V.md) already gives an exact infinite-address bounded-observable cycle law, fixed-colouring finite-cut whole-volume heat error, and the failure of its infinite-fibre pullback to lie in counting $\ell^2$. Those results retain their infinite source, particular colouring, kinetic operator and norms. The present finite-tree estimates use arbitrary partitions, finite induced Hilbert masses and arbitrary real blocks; they neither contradict that infinite cycle nor reprove its positive whole-volume floor. The [finite joint cycle/radial prediction companion §§1 and 6](FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_FINITE_JOINT_PREDICTION.md) addresses another exact observation on that infinite source. No finite/infinite or norm interchange is implicit.

The primary attributions in the proofs are bounded to their stated versions and hypotheses. No world-priority or global absence assertion is part of these results. The common source/history remains a joint object: neither the partition nor the extra field/amplitude interfaces are additional original Reads. The legal finite prefixes do not authorize a cap increase, a continuation after Stop, or an event after an infinite prefix. Selecting the four-leaf INITIAL (268.1) does not assert its availability from every other fixed INITIAL orbit.

Local fibre rank $r$, number of retained deterministic labels, dimension of the invariant observable space, topological cycle rank and physical spatial dimension are distinct parameters. A cycle forces the displayed quantitative predictive defect, not a collective Euclidean physical-space theorem. Constructing an actual spatial realization with its original operations, metric, boundary, clock and acquisition cost remains a separate mathematical problem; the necessary conditions here do not assert its impossibility or its completion. All proofs in §§264–269 are ordinary finite-dimensional mathematics, with no Lean or kernel-verification assertion.

## 追加锚（本行以下为增补区）
