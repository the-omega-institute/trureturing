# AURIC 融合原子的量子原则与相干重构续卷 XIII：原度量零响应方向的约化障碍

## 1. 完整原类与原度量约化问题

**定义 1.1（数学范围与来源）。** 本卷研究 [XII55.1–55.2][XII] 的同一个有限实算子类 $\mathfrak K_{\rm r}$，不给 ready 非退化或端点正交性。它是普通数学的条件模型，不是完整实际 $\Omega$ 的实现；正文是理论参考输入，未经 Lean kernel 认证。固定版本中的全部原配置、地址、度量、准备及离散方程按定义 1.2 保留。

**定义 1.2（原来源的完整前件）。** 原配置与固定外位为

$$
\begin{gathered}
E=\{q\subseteq\{1,\ldots,9\}:q\text{ 无相邻占据}\},\qquad |E|=89,\\
b_{-1}b_0=10,\qquad b_{10}b_{11}b_{12}=010 .
\end{gathered}
\tag{1.1}
$$

每个 $b_i(q)$ 是原占据位。原边只翻转一个中心 $j\in\{1,\ldots,9\}$，且其两个邻位为零。每条边保留中心地址；无向边共有 $235$ 条，每条都给两个方向的运输。共同有限实容量、原正定几何及固定响应为

$$
\begin{gathered}
\mathcal V=\bigoplus_{q\in E}V_q,\qquad
\dim_{\mathbb R}V_q=d<\infty,\qquad g=\bigoplus_qg_q>0,\\
L_q\in\operatorname{End}_{\mathbb R}V_q,\qquad
\mathcal L=\bigoplus_qL_q,\\
T_{qt}:V_t\longrightarrow V_q,\qquad
T_{tq}=T_{qt}^{-1}=T_{qt}^{\dagger}
\quad\text{（每条原边）}.
\end{gathered}
\tag{1.2}
$$

$\dagger$ 始终相对于这个原 $g$。同一组 $g,L,T$ 不随输入、调用字、隐藏过去或未来请求重选。
唯一实际 ready 和一个固定单位准备为

$$
r=\{3,7\},\qquad
u_*\in V_r,\quad\|u_*\|_{g_r}=1,\qquad
\operatorname{tr}_{V_r}(L_r^\dagger L_r)=2 .
\tag{1.3}
$$

迹取整个原 $d$ 维纤维，既不除以 $d$，也不限制到响应支撑。以 $v_*$ 表示 $u_*$ 在 $\mathcal V$ 中的零延拓。
黄金参数固定为

$$
x=\frac{\sqrt5-1}{2},\qquad c=x\sqrt{x}>0,\qquad
\alpha=\frac{3\pi}{5},\qquad x+x^2=1,\quad c^2=x^3 .
\tag{1.4}
$$

原 $B_j$ 的活动块按中心位 $0,1$ 排列：

$$
B_j\big|_{V_{q_0}\oplus V_{q_1}}
=\begin{pmatrix}xI&cT_{q_0q_1}\\cT_{q_1q_0}&x^2I\end{pmatrix},
\qquad q_1=q_0\cup\{j\},\quad b_j(q_0)=0 .
\tag{1.5}
$$

内地址的其余合法配置是阻塞单点；这些单点和两个边界的值分别为

$$
B_j|_{V_q}=b_{j-1}(q)b_{j+1}(q)I,\qquad
B_0|_{V_q}=b_1(q)I,\qquad B_{10}|_{V_q}=b_9(q)I .
\tag{1.6}
$$

仅在原合法翻转对上使用 (1.5)，不向非法配置延伸。逆等距及 (1.4) 给 $B_j^\dagger=B_j^2=B_j$。
原响应严格在左，十一整调用及其完整方程为

$$
\begin{gathered}
A_j=\alpha\mathcal L(I+B_j),\qquad U_j=e^{A_j}\quad(0\le j\le10),\\
U_j^{10}=I\quad(0\le j\le10),\\
U_jU_{j+1}U_j=U_{j+1}U_jU_{j+1}\quad(0\le j\le9),\\
U_jU_k=U_kU_j
\quad(0\le j<k\le10,\ k-j\ge2).
\end{gathered}
\tag{1.7}
$$

这里是整个 $89d$ 维载体上的十一十回返、十个相邻 Artin 和四十五个远关系。未输入 $\mathrm{E1}:U_j^\dagger U_j=I$、$\mathrm N_{\rm r}:\ker L_r=0$、实循环性、正规性、共同活动平面、响应边交织或连续守恒。
原 $26+63$ 仍是配置的代码／补坐标划分；原七后读地址、两切口、报告与档案合同不因 (1.7) 成为额外的正字操作。

**定义 1.3（同一原准备的全部正字与两个核条件）。** 采用 XII55.2 的全部原有限前读字

$$
\mathsf W_{11}^{+}=\{0,\ldots,10\}^{<\infty},\qquad
U_{(j_1,\ldots,j_k)}=U_{j_k}\cdots U_{j_1},\quad U_\varepsilon=I .
\tag{1.8}
$$

没有字长截断，也不把线性组合当作新的物理准备。令 $Z_q=\ker L_q$。所研究的原度量核约化及全边核运输分别是

$$
\begin{aligned}
\mathsf{Red}_g&:\quad
  \ker L_q=\ker L_q^\dagger\quad(q\in E),\\
\mathsf{Tr}_{\ker}&:\quad
  T_{qt}\ker L_t=\ker L_q\quad\text{（每条原边）}.
\end{aligned}
\tag{1.9}
$$

在有限维中，第一项等价于原正交补 $Z_q^{\perp_{g_q}}$ 对 $L_q$ 不变：由 $\operatorname{ran}L_q=(\ker L_q^\dagger)^\perp$ 及秩—零化度即可得此等价。它要求原正交约化，不只是一个抽象不变补空间。

## 2. 保留全部原方向的具体响应

**定义 2.1（三维原纤维与固定单点剪切）。** 在每一个原配置上一次性选定

$$
\begin{gathered}
V_q=\mathbb R^2\oplus\mathbb R,\qquad
g_q((a,z),(a',z'))=a\cdot a'+zz',\qquad
T_{qt}=I_3\quad\text{（全部原边及其逆）},\\
J=\begin{pmatrix}0&-1\\1&0\end{pmatrix},\qquad
s=\{1,3,7\},\\
\lambda_s(a_1,a_2)=a_1,\qquad
\lambda_q=0\quad(q\ne s),\\
L_q(a,z)=(Ja,\lambda_q(Ja)),\qquad
u_*=(1,0,0)\in V_r .
\end{gathered}
\tag{2.1}
$$

这里 $r$ 和 $s$ 是原地址一的合法翻转对，两个邻位 $b_0,b_2$ 均为零；$r$ 仍是唯一指定 ready。$d=3$、欧氏 $g_q$、恒等边及 (2.1) 是一个允许成员的数据选择，不是对所有成员新加的假设。全部 $89$ 个第三方向和全部 $235$ 条边仍在原载体中。
特别地，

$$
L_r=\begin{pmatrix}0&-1&0\\1&0&0\\0&0&0\end{pmatrix},
\qquad
L_s=\begin{pmatrix}0&-1&0\\1&0&0\\0&-1&0\end{pmatrix}.
\tag{2.2}
$$

$B_j,A_j,U_j$ 逐字面由 (1.5)–(1.7) 定义；不通过对 $B_j$ 的相似变换定义它们。

**定义 2.2（原坐标的重排与证明用映射）。** 仅将同一原直和的坐标重排为

$$
H=(\mathbb R^2)^E,\qquad Z=\mathbb R^E,\qquad
\mathcal V=H\oplus Z,\qquad
(\Lambda a)_q=\lambda_q(a_q),\qquad
\mathcal J=\bigoplus_{q\in E}J .
\tag{2.3}
$$

该重排保留原正交直和度量。以 $P_j$ 表示原黄金投影的标量 $89\times89$ 矩阵：每个活动块为 $\left(\begin{smallmatrix}x&c\\c&x^2\end{smallmatrix}\right)$，每个阻塞及边界值恰为 (1.6) 的原标量。记其在 $H$ 和 $Z$ 上的作用为 $P_j^H,P_j^Z$，并令

$$
\begin{gathered}
D_j^H=I_H+P_j^H,\qquad D_j^Z=I_Z+P_j^Z,\qquad
C_j=\alpha\mathcal J D_j^H,\qquad K_j=e^{C_j},\\
\mathcal S(a,z)=(a,z+\Lambda a),\qquad
\mathcal S^{-1}(a,z)=(a,z-\Lambda a).
\end{gathered}
\tag{2.4}
$$

$\mathcal S$ 只是同一原载体上的代数证明工具。它不更改原度量、边运输、黄金矩阵、准备或任何原标签。

## 3. 完整原类中的核约化障碍

**定理 3.1（全离散关系及同 ready 范数见证）。** 定义 2.1 的数据满足定义 1.2 的全部 $\mathfrak K_{\rm r}$ 前件，且使用定义 1.3 的同一个完整正字域。它具有下列同时成立的性质：

1. 每个原 $Z_q=\operatorname{span}(e_3)$，$\mathsf{Tr}_{\ker}$ 在全部 $235$ 条原边上成立；但在原 $s$ 处

$$
\ker L_s^\dagger=\operatorname{span}\bigl((1,0,-1)\bigr)
\ne\ker L_s=\operatorname{span}(e_3).
\tag{3.1}
$$

2. 同一个原 ready 单位准备经合法字 $(1)$ 后，

$$
\|U_1v_*\|_g^2=1+\frac{x^3}{4}>1=\|v_*\|_g^2.
\tag{3.2}
$$

因此原度量端点 $\mathrm{E1}$ 及原全输入内部守恒均不由 $\mathfrak K_{\rm r}$ 推出，原 ready 边的响应交织也失败。

3. 十一十回返、十个相邻 Artin 和四十五个远关系在全部 $267$ 个原实方向上成立；每一个原第三方向被每个 $U_j$ 固定。证明没有丢弃这些方向，也没有把 $\mathcal S$ 当作原等距坐标。

从而 $\mathfrak K_{\rm r}\Rightarrow(\mathsf{Red}_g\land\mathsf{Tr}_{\ker})$ 为假；甚至给 $\mathfrak K_{\rm r}$ 另加 $\mathsf{Tr}_{\ker}$ 仍不蕴含 $\mathsf{Red}_g$。

证明。先核对完整原域。一个含 $n$ 个占据位的合法配置 $i_1<\cdots<i_n$ 经 $i_k\mapsto i_k-(k-1)$，对应 $\{1,\ldots,10-n\}$ 中的 $n$ 元子集。因此原配置与删除边的计数为

$$
|E|=\sum_{n=0}^{5}\binom{10-n}{n}=89,\qquad
|\operatorname{Edges}E|
=\sum_{n=1}^{5}n\binom{10-n}{n}=235 .
\tag{3.3}
$$

每个非空配置的每个占据位给一条删除边；每条原无向边只在其占据端计一次。这正是 [XII (54.2)][XII] 的原图，未取子图。定义 2.1 对这个集合的每个顶点和每条有向边给出固定数据，所以不是只在 ready 邻域的局部模型。所有 $T=I_3$ 及其逆都是原欧氏等距；每个 $V_q$ 的维数恰为三，$g=\bigoplus g_q$ 正定。

在这些原边数据下，(1.5) 的每个矩阵元是所给标量乘 $I_3$。故同一坐标重排后，原算子恰有

$$
B_j=\begin{pmatrix}P_j^H&0\\0&P_j^Z\end{pmatrix},
\qquad
I+B_j=\begin{pmatrix}D_j^H&0\\0&D_j^Z\end{pmatrix}
\quad(0\le j\le10).
\tag{3.4}
$$

这也覆盖所有阻塞单点和两个边界。活动标量块为 $vv^T$，其中 $v=(\sqrt{x},x)^T$，$v^Tv=x+x^2=1$；单点标量为零或一。因此每个 $P_j$ 以及原 $B_j$ 均在原度量中自伴且幂等。此处没有把 $P_j$ 换成另一个只满足抽象关系的投影。

现在验证全部离散方程，直接复用 [XII18.1、(18.2)、(18.5)–(18.6)][XII] 的完整原 Jones 家族。该供应在同一 $89$ 标签上给

$$
\widetilde K_j
=e^{i\alpha}\bigl[I+(e^{i\alpha}-1)P_j\bigr],
\qquad 0\le j\le10,
\tag{3.5}
$$

以及全部十一十回返、十个相邻和四十五个远关系，含地址零和十。在 $H$ 中用 $(a_1,a_2)\mapsto a_1+ia_2$ 只是表示同一实算子，$\mathcal J$ 对应乘 $i$；因而定义 2.2 的 $K_j$ 正是 (3.5) 的实形式。这项既有全标签供应没有以本例的原度量结论为前提。

明确地，$\mathcal J$ 与 $D_j^H$ 对易，$\mathcal J^\dagger=-\mathcal J$、$(D_j^H)^\dagger=D_j^H$，故 $C_j^\dagger=-C_j$，$K_j$ 是 $H$ 上的欧氏正交算子。完整基准调用为

$$
U_j^\flat=\begin{pmatrix}K_j&0\\0&I_Z\end{pmatrix}.
\tag{3.6}
$$

它就是 [XII59.2][XII] 所用的原生家族加全部 $89$ 个静止方向；其非空性及离散关系是既有结果，不作为本定理的新增内容。对每个保留的方程，在 $H$ 上用既有 Jones 关系，在 $Z$ 上用恒等，即得 (3.6) 在整个 $H\oplus Z$ 上的同一方程。

关键是核对实际的严格左响应，而不是定义一个任意共轭家族后声称它有原形式。由 (2.1) 和 (2.3)，

$$
\mathcal L=
\begin{pmatrix}\mathcal J&0\\\Lambda\mathcal J&0\end{pmatrix},
\qquad
A_j=\alpha
\begin{pmatrix}
\mathcal J D_j^H&0\\
\Lambda\mathcal J D_j^H&0
\end{pmatrix}
=\begin{pmatrix}C_j&0\\\Lambda C_j&0\end{pmatrix}.
\tag{3.7}
$$

直接乘同一个固定三角矩阵给

$$
\begin{aligned}
\mathcal S
\begin{pmatrix}C_j&0\\0&0\end{pmatrix}
\mathcal S^{-1}
&=
\begin{pmatrix}I_H&0\\\Lambda&I_Z\end{pmatrix}
\begin{pmatrix}C_j&0\\0&0\end{pmatrix}
\begin{pmatrix}I_H&0\\-\Lambda&I_Z\end{pmatrix}\\
&=\begin{pmatrix}C_j&0\\\Lambda C_j&0\end{pmatrix}
=A_j .
\end{aligned}
\tag{3.8}
$$

没有使用 $\Lambda P_j^H=P_j^Z\Lambda$，这个等式事实上不对全部地址成立。右下零块使 (3.8) 成立；若擅自改成右加权响应，就不能沿用此计算。
由矩阵指数的幂级数和同一个可逆 $\mathcal S$，

$$
U_j=\mathcal S U_j^\flat\mathcal S^{-1}
=\begin{pmatrix}K_j&0\\\Lambda(K_j-I_H)&I_Z\end{pmatrix}
\quad(0\le j\le10).
\tag{3.9}
$$

对任意原有限字 $w=(j_1,\ldots,j_k)$，令 $K_w=K_{j_k}\cdots K_{j_1}$、$K_\varepsilon=I_H$。中间的 $\mathcal S^{-1}\mathcal S$ 逐项消去，得到

$$
U_w=\mathcal S
\begin{pmatrix}K_w&0\\0&I_Z\end{pmatrix}
\mathcal S^{-1}.
\tag{3.10}
$$

因此 (3.6) 的全部十一／十／四十五方程同时传到实际 $U_j$，不是分别为不同地址选择不同相似矩阵。每个方程都在完整 $267$ 维域上成立。式 (3.9) 还直接给 $U_j(0,z)=(0,z)$，覆盖每一个原第三方向及其全部组合。

根校准须在原度量中另查，不能由相似不变性冒领。因为 $r\ne s$，$\lambda_r=0$，故 (2.2) 给

$$
L_r^\dagger L_r=\operatorname{diag}(1,1,0),\qquad
\operatorname{tr}_{V_r}(L_r^\dagger L_r)=2,\qquad
\|u_*\|_{g_r}^2=1.
\tag{3.11}
$$

这是完整三维迹，未删零方向。$\mathcal S$ 在 ready 纤维上恰为恒等；从基准模型到 (2.1) 始终使用同一个 $r$ 和同一个 $u_*$，没有为范数见证换准备。至此定义 1.2 的所有前件，包括固定外位、原边、黄金块、严格左顺序、完整迹及全部离散等式，都已核对。

再算原伴随核。由于 $J$ 可逆，$L_q(a,z)=0$ 当且仅当 $a=0$，所以所有原核都为 $\operatorname{span}(e_3)$。全部 $T_{qt}=I_3$ 给每条原边上的 $\mathsf{Tr}_{\ker}$。在 $s$ 处仍用原欧氏伴随，(2.2) 给

$$
L_s^\dagger(\xi,\eta,\zeta)=(\eta,-\xi-\zeta,0).
\tag{3.12}
$$

其核恰为 (3.1)。特别地 $L_se_3=0$，却有 $L_s^\dagger e_3=(0,-1,0)\ne0$。原正交活动平面未被 $L_s$ 保持，因为

$$
L_s e_2=(-1,0,-1)\notin(\ker L_s)^\perp .
\tag{3.13}
$$

同一实际 ready 边上的响应交织也不成立：

$$
(L_sT_{sr}-T_{sr}L_r)e_2=-e_3\ne0.
\tag{3.14}
$$

这不妨碍核本身在该边或其它边上的运输。

最后用同一原 ready 的合法字验证原度量后果。令 $R_\theta=e^{\theta J}$，其在 $H$ 上的同名作用指各原配置中该旋转的直和。令 $a_*\in H$ 只在 $r$ 处为 $e_1=(1,0)^T$。则 $v_*=(a_*,0)$ 且 $\Lambda a_*=0$。对数学内部参数 $0\le h\le1$，正交投影分解给

$$
e^{hC_1}
=R_{\alpha h}(I_H-P_1^H)+R_{2\alpha h}P_1^H.
\tag{3.15}
$$

旋转在每个原二维坐标中相同，故与投影对易。原 $(r,s)$ 活动块的非对角元就是 $c$，从而

$$
\bigl(e^{hC_1}a_*\bigr)_s
=c(R_{2\alpha h}-R_{\alpha h})e_1 .
\tag{3.16}
$$

式 (3.8) 对 $hA_1$ 同样成立；又只有 $\lambda_s$ 非零，因此实际演化的唯一可能非零第三坐标是

$$
\bigl(e^{hA_1}v_*\bigr)_{z_s}
=c\bigl(\cos(2\alpha h)-\cos(\alpha h)\bigr).
\tag{3.17}
$$

其活动部分 $e^{hC_1}a_*$ 的总欧氏范数平方为一，活动坐标与全部第三坐标在原 $g$ 中正交。所以精确地

$$
\|e^{hA_1}v_*\|_g^2
=1+c^2\bigl(\cos(2\alpha h)-\cos(\alpha h)\bigr)^2 .
\tag{3.18}
$$

在合法整调用端点 $h=1$，原角度给

$$
\cos\alpha=-\frac{x}{2},\qquad
\cos(2\alpha)=-\frac{1+x}{2},\qquad
c\bigl(\cos(2\alpha)-\cos\alpha\bigr)=-\frac c2 .
\tag{3.19}
$$

结合 $c^2=x^3>0$ 得 (3.2)。这已在原实际准备及一个原合法整字上排除 $U_1^\dagger U_1=I$，也排除 [IV (209.6)][IV] 的全输入、全部内部时刻守恒，不需要另一个可制备初态或可执行分数调用。

整个证明没有改变度量。事实上，取 $a$ 只在 $s$ 处为 $e_1$，有 $\|(a,0)\|_g^2=1$ 而 $\|\mathcal S(a,0)\|_g^2=2$，所以 $\mathcal S$ 确非原等距。式 (3.8)–(3.10) 只证明代数方程，不把 $\mathcal S$ 的像声明为新的全载体。核差异和范数增加均在同一原 $g$ 中计算，故给出所述反例。∎

## 4. 原度量消费者及未决问题的精确分离

**定义 4.1（活动图与原正交约化的区别）。** 定理 3.1 中的静止空间和另一个活动不变空间为

$$
Z=\{(0,z):z\in\mathbb R^E\},\qquad
G_\Lambda=\{(a,\Lambda a):a\in H\}.
\tag{4.1}
$$

由 (3.7) 和 (3.9)，$G_\Lambda$ 对 $\mathcal L$ 及所有 $U_j$ 不变，且 $\mathcal V=G_\Lambda\oplus Z$；但此直和在原度量中不正交。$Z^\perp=H\oplus\{0\}$ 对 $L_s$ 及 $U_1$ 的失败已由 (3.13)、(3.17) 检出。原 $B_j$ 也没有被共轭：例如 $v_*=(a_*,0)\in G_\Lambda$，$B_1v_*=(P_1^Ha_*,0)$，而 $(\Lambda P_1^Ha_*)_s=c\ne0$，故 $B_1v_*\notin G_\Lambda$。

直观地，离散字方程只比较乘积是否相等；同一个非正交剪切保留这些等式。原质量却用给定的欧氏内积计算，活动幅度在 $s$ 处产生的第三坐标贡献额外正平方。这个第三方向本身仍是静止方向，并没有因为能从活动输入产生该坐标而被删除。代数相似于原生家族加静止部分，不能代替原度量中的守恒、正交分解或字面 $B_j$ 的限制。

**定义 4.2（已有消费者与本障碍的作用）。** 目标消费者是 [XII49.2、53.3–54.1][XII] 的无 E1 非退化容量及原度量装配，再接 [IV210.1][IV]。这些结果要求在其完整前件内先取得 ready 非退化及共同实二维，然后才供应原反自伴、全边响应交织、E1、连续守恒和保配置的原等距复坐标。若试图对一般 $\mathfrak K_{\rm r}$ 先按原核取正交活动部分，再把它交给这些消费者，须先证明该正交部分承载所需原响应、黄金算子和运输。

定理 3.1 表明，仅凭完整 $\mathfrak K_{\rm r}$ 的原离散关系，即使另有全部核运输，也不能取得这个原度量核约化前件。在本例中每个正交活动部分都是二维，ready 上的 $L_r$ 也已经是 $J\oplus0$，但 (3.13) 使正交限制不是 $L_s$ 的自映射；(3.2) 还在同一原准备上给出原质量障碍。改取斜图、取商或另选不变度量，都不能作为原全载体上保原度量的消费者前件。

这不反驳 XII59.1 的
$\mathrm{Cyc}_{\rm r}\Longleftrightarrow\mathrm N_{\rm r}\Longleftrightarrow d=2\Longleftrightarrow\mathrm{Nat}_{\rm r}$。
本例的 $\ker L_r=\operatorname{span}(e_3)\ne0$，并不满足其中任何一个等价条件。
XII62.1、62.3–68 的实球面相位下降及 Born 应用同样明确保留 ready 非退化、局部率的射线依赖以及全部响应／过程合同；本反例不满足其容量前件，也没有替换那些合同。

**定义 4.3（两个仍未结算的全称问题）。** 定理 3.1 不决定

$$
\mathfrak K_{\rm r}\stackrel{?}{\Longrightarrow}\mathsf{Tr}_{\ker}.
\tag{4.2}
$$

本例在每条边上满足右侧，因此不能作为运输单项的反例。它决定的是 (1.9) 的原度量约化单项及两项合取的不成立。
另一个问题是在完全不给 E1、也不给 $\mathrm N_{\rm r}$ 时，是否每个原 ready 都必有原正交分解

$$
V_r=P\mathbin{\perp}Z_r,\qquad
\dim_{\mathbb R}P=2,\qquad
L_r|_P=J_P,\quad J_P^\dagger=-J_P,\quad J_P^2=-I_P,\qquad
L_r|_{Z_r}=0 .
\tag{4.3}
$$

[XII40.2][XII] 在另有 E1 的类中给出这种 ready 结论；本卷没有将它移入无 E1 的一般类。本例在 ready 恰好满足 (4.3)，故既不证明也不反驳无 E1／无非退化的一般 ready 秩二加零核命题。更不从一例推出所有容量的分类或任意分割、一般量子表示的不可能性。

**定义 4.4（完整实际来源仍保留的对象）。** 本卷的反例只在明确的有限实算子类内否定一个条件蕴涵，不是同一实际 $\Omega$ 的完整模型，也没有把无限维 CountRead 共同切口响应商替换成 $267$ 维空间。原完整目标仍包括全部 $89$ 配置、$235$ 边、$26+63$ 坐标、唯一原 ready、十一前读／七后读权限、两个记录切口、全部 $1024$ 终端及 $2048$ 形式联合标签；完整 $610$ 来源、真空接口和原十五调用读器亦不由本例供应。

所有原来源、输入准备、事件、原质量、参考与副本、实际联合、原单位与尺度、原控制和时钟、全部合法顺序／自适应／并行历史及其未来仍须同源对应。细记录的原表、分母、地址、坐标／失败、原输出类型、provenance、prefix、occurrence、parent 档案均不删除、不合并、不前移；存档不授予共同可读比较或再输入权限。零、无路径零标签、失败、拒绝、停止、报警、销毁、泄漏、返回及双向／逆向返回都保留，零质量分支不指定条件态。

原 Born／报告、正分支纯更新、档案充分性、读器再进入、完整路径律、参考／联合正性、实际 CP 与仪器、物理准备和钟的取得，均不是 (1.7) 的代数后果。数学内部参数 $h$ 不增加可执行控制。定理 3.1 不声称物理采用、全来源量子起源完成、有限样本认证、统一误差界、取得成本或总独立信息量减少。

## 5. 数学来源与增量归属

**定义 5.1（固定来源及准确使用范围）。** 来源按以下版本、条目和条件使用：

| 数学来源 | 使用范围与边界 |
| --- | --- |
| [续卷 XII，固定版本 c7278fc3e4ceac417e8a1147a754b2491d9a747c][XII]，55.1–55.2、(55.1)–(55.3) | 完整 $\mathfrak K_{\rm r}$、同一原单位 ready、完整正字域和全部原离散方程；不预付 E1、非退化、循环性或原度量装配。 |
| 同版本 XII18.1、(18.2)、(18.5)–(18.6)、54.2、59.2 | 直接复用完整原 Jones 家族及其正交零扩张的非空性、全部十一／十／四十五方程；不把这些已有结果作为新增定理。 |
| 同版本 XII14–16、40.1–40.2、44.3、49–61 | 已有非正规混叠例、E1 型 ready 秩结论及非退化／循环消费者各保留自己的前件。XII14–16 的较弱模型不承担本定理的全部相邻关系；XII59.2 的正交零扩张不具有本定理的伴随核差异或范数增加。 |
| [续卷 IV，同一固定版本][IV]，209.1–209.3、210.1 | 原合法边、黄金／阻塞／边界、严格左次序及原度量守恒／装配消费者；本卷不使用任何 Lean 声明作为新核验。 |
| [V15，同一固定版本][V15]，Theorem 3.1、Proposition 3.2、(3.2)–(3.4) | 已有投影相位与 Artin 因子，经 XII18.1 绑定全部原标签；一般三比特空间不能代替合法路径表示。 |
| Freedman–Larsen–Wang，[*The two-eigenvalue problem and density of Jones representation of braid groups*, arXiv:math/0103200v1][FLW]，§2 Lemma 2.1、Definitions 1–2、(1)–(3) | literature-attested：在 $q_J=e^{2\pi i/5}$、$(k,r_{\rm FLW})=(2,5)$、$n=12$、$\lambda=[6,6]$ 的可容许表表示中，$\rho(\sigma_i)=q_JI-(1+q_J)E_i$ 及编织关系；XII18.1 已给原路径与全部十一地址的共同对应。不使用密度、不可约分类、任意表示的酉化或物理采用结论。 |

具体地，FLW 的量子整数为
$[m]=(q_J^{m/2}-q_J^{-m/2})/(q_J^{1/2}-q_J^{-1/2})$；
§2 要求 $r_{\rm FLW}\ge k+1$，上述参数满足该条件，且 $[2]=\varphi=(1+\sqrt5)/2=x^{-1}$。其可容许表在每个前缀形状上满足行长差不超过三；这里的 $[6,6]$ 是十二盒形状。经 XII18.1 的共同路径对应，$E_i$ 的二点块及单点值正是本卷的原 $P_{i-1}$。令 $\zeta=e^{3\pi i/5}$、$\gamma=\zeta/q_J$，则

$$
\gamma\bigl[q_JI-(1+q_J)P_j\bigr]
=\zeta\bigl[I+(\zeta-1)P_j\bigr].
\tag{5.1}
$$

相邻与远关系两侧的字长分别同为三与二，故共同标量 $\gamma$ 不改变它们；十回返用 (3.5) 的原相位与投影。此处只是明确被复用供应的参数，不另立一般 Jones 定理或重做既有路径对应。

**定义 5.2（来源特定的新内容与适用边界）。** 定理 3.1 的新增内容记为 repo-derived：在同一完整 $\mathfrak K_{\rm r}$、严格左响应、原度量和同一原 ready 中，顶点相关下剪切保持全部原离散方程及全部核运输，却破坏原伴随核约化，并在合法单字上给出精确正的原质量差 $x^3/4$。矩阵相似、指数幂级数、秩—零化度和正交投影的指数公式是证明内的成熟工具，不作为新数学内容单列。

这一增量有别于仅增添一个正交静止方向来显示 $d>2$ 或循环性失败，也有别于只保留远关系的整端点混叠例。其来源特定性在于 (3.7)–(3.8) 确认字面的原左响应，(3.11) 保留完整原校准，而 (3.1)、(3.2) 直接阻断原度量消费者；不是用一个抽象接口反例代替原系数族反例。本卷不作穷尽仓库或文献的原创性／优先权主张。

[XII]: https://github.com/the-omega-institute/trureturing/blob/c7278fc3e4ceac417e8a1147a754b2491d9a747c/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_XII.md
[IV]: https://github.com/the-omega-institute/trureturing/blob/c7278fc3e4ceac417e8a1147a754b2491d9a747c/docs/develop/theory/AURIC_FIB_ATOM_QUANTUM_PRINCIPLES_AND_COHERENT_RECONSTRUCTION_CONTINUATION_IV.md
[V15]: https://github.com/the-omega-institute/trureturing/blob/c7278fc3e4ceac417e8a1147a754b2491d9a747c/docs/develop/theory/AURIC_GOLDEN_GATE_NAND_UNIVERSALITY_AND_ARITHMETIC_LIMITS_V15.md
[FLW]: https://arxiv.org/html/math/0103200v1

## 追加锚（本行以下为增补区）
