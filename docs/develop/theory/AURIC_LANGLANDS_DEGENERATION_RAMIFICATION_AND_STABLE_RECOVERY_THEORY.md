# AURIC–Langlands 退化、分歧与稳定恢复理论

仓内数学引用除量子边界卷 §§13–14 与未校准二次时钟卷取
`b84d469298a8d601e21f85bcc1d6085e3cf557f5` 外，均取
`9f20f4efdb4c90cc1e07fa7e481ffc0dc86234c3`；条目编号按相应版本。

## 1. 固定二次协变量的微分退化

### 定义 1.1（实结构、合法态与纤维输入）

固定定向欧氏空间 $V=\mathbb R^5$ 及其正交基。置

$$
J_{ij}=E_{ij}-E_{ji},\qquad
A=\sum_{i<j}a_{ij}J_{ij},\qquad
\omega_A=\sum_{i<j}a_{ij}e_i\wedge e_j.
$$

来源为 $\rho=S+iA\succeq0$，其中 $S^{\mathsf T}=S$、$\operatorname{tr}S=1$、
$A^{\mathsf T}=-A$。比较时保持 $S$ 及坐标框架，目标只取共同符号商
$[A]_\pm$，不再除以正交变基。定义

$$
\begin{aligned}
\sigma(A)&=-\tfrac12\operatorname{tr}A^2,\\
\gamma(A)&=-A^2+\tfrac15\operatorname{tr}(A^2)I,\\
\beta(A)&=*(\omega_A\wedge\omega_A),\qquad
q(A)=(\sigma(A),\gamma(A),\beta(A)),\\
K(A)&=-A^2=\gamma(A)+\tfrac25\sigma(A)I.
\end{aligned}
$$

目标空间为 $\mathbb R\oplus\operatorname{Sym}^2_0(V)\oplus V$。
矩阵使用 Frobenius 范数，二形式的边坐标使用欧氏范数，故
$\|A\|_F^2=2\sum_{i<j}a_{ij}^2$。

以下使用[量子边界卷，定理 8.2 的证明](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md#8-directional-responses-and-the-support-dependent-recovery-threshold)
所给完整实纤维分类作为输入：零态纤维为单点；非零秩二态及两个非零旋转尺度不同的秩四态纤维为 $\{A,-A\}$；
等重秩四态的纤维为固定四维支撑上的 $S^2$，共同符号商为 $\mathbb{RP}^2$。
后者用 $\beta(A)$ 定向支撑 $E$，取正向正交基后写成

$$
\begin{gathered}
L_1=J_{12}+J_{34},\quad L_2=J_{13}-J_{24},\quad L_3=J_{14}+J_{23},\\
B(u)=\sum_{j=1}^3u_jL_j,\qquad |u|=s>0.
\end{gathered}
$$

一般 $S$ 的合法纤维是此代数纤维与 $S+iB\succeq0$ 的交。
$S=I/5$、$s<1/5$ 时整个球面严格合法，谱为
$1/5-s,1/5-s,1/5+s,1/5+s,1/5$。
四维自对偶复结构的经典几何背景为
[Salamon–Viaclovsky，§2.4，命题 2.1–2.2](https://arxiv.org/html/0704.3422v2)；
这里的纤维、实结构和合法性均取上述仓内输入。

### 定理 1.2（微分核及其纤维切向解释）

在十维实向量空间 $\mathfrak{so}_5$ 上，

$$
\dim\ker Dq_A=
\begin{cases}
10,&A=0,\\
2,&\operatorname{rank}A=4\text{ 且两个非零旋转尺度相等},\\
0,&\text{其余非零 }A.
\end{cases}
$$

二维核恰为定义 1.1 的球面纤维在 $A$ 处的切空间。

**证明。** 对反对称增量 $H$，

$$
\begin{aligned}
D\sigma_A(H)&=-\operatorname{tr}(AH),\\
D\gamma_A(H)&=-(AH+HA)+\tfrac25\operatorname{tr}(AH)I,\\
D\beta_A(H)&=2*(\omega_A\wedge\omega_H).
\end{aligned}
$$

因此核条件等价于

$$
AH+HA=0,\qquad\omega_A\wedge\omega_H=0. \tag{1.1}
$$

第一式使 $H$ 与 $A^2$ 交换。秩四且尺度不同时，$H$ 保持两个二维正特征空间及一维核；
二维反对称矩阵与非零旋转块反对易只可能为零。秩二时，第一式只留下
$H\in\mathfrak{so}(\ker A)$；非零支撑面积形式与 $\Lambda^2\ker A$ 的楔积为单射，
第二式使 $H=0$。

等重秩四时，第一式排除支撑与一维核间的块。在 $E$ 上分解
$H=H_++H_-$ 为自对偶、反自对偶部分。这两类算子彼此交换。
写 $A=\sum a_iL_i$、$H_+=\sum h_iL_i$，利用
$L_iL_j+L_jL_i=-2\delta_{ij}I_E$ 得

$$
AH+HA=-2(a\cdot h)I_E+2AH_-.
$$

自对偶与反自对偶部分正交，故 $\operatorname{tr}(AH_-)=0$；取迹得 $a\cdot h=0$。
$A|_E$ 可逆，再得 $H_-=0$。剩下的 $a^\perp\subset\mathbb R^3$ 为二维，
自动满足第二个核条件，正是球面切空间。零点的全部一阶项为零。∎

### 定理 1.3（紧集上的逆与合法条件数发散）

令 $\mathcal R$ 为去掉零态及等重秩四层的集合，置
$d_\pm^F(A,B)=\min(\|A-B\|_F,\|A+B\|_F)$。
每个紧集 $C\subset\mathcal R$ 上存在有限 $c_C$，使

$$
d_\pm^F(A,B)\le c_C\|q(A)-q(B)\|,\qquad A,B\in C.
$$

此处数据范数为标量、Frobenius 矩阵和欧氏向量的直和范数。
对 $0<s<1/5$、$0<\delta<\min(s,1/5-s)$，令

$$
A_\delta=(s+\delta)J_{12}+(s-\delta)J_{34},\qquad
B_\delta=(s+\delta)J_{13}-(s-\delta)J_{24}.
$$

两者在共同 $S=I/5$ 下严格合法，且

$$
\frac{d_\pm^F(A_\delta,B_\delta)}{\|q(A_\delta)-q(B_\delta)\|}
=\frac{\sqrt{s^2+\delta^2}}{2s\delta}\sim\frac1{2\delta}. \tag{1.2}
$$

**证明。** 若紧集上比值无界，取两列及其极限 $A,B$。由有界直径及连续性，
$q(A)=q(B)$；纤维输入给 $B=\pm A$。在 $C\cup(-C)$ 内统一符号后，差趋零。
用二次映射的 Taylor 恒等式除以差的范数，再取单位差向量的收敛子列，
得到非零 $H$ 满足 $Dq_A(H)=0$，与定理 1.2 矛盾。

显式族的 $\sigma$ 相同，$\beta$ 均为 $2(s^2-\delta^2)e_5$，而

$$
\gamma(A_\delta)-\gamma(B_\delta)
=\operatorname{diag}(0,4s\delta,-4s\delta,0,0).
$$

两个矩阵 Frobenius 正交，各自范数平方为 $4(s^2+\delta^2)$。
分子为 $2\sqrt2\sqrt{s^2+\delta^2}$，分母为 $4\sqrt2s\delta$。
最大旋转尺度为 $s+\delta<1/5$，给出严格合法性及 (1.2)。∎

## 2. 三固定深度的线性秩与深度必要性

### 定义 2.1（校准滤波、原始矩与已有稳定输入）

固定

$$
F=\operatorname{diag}(1,2,3,4,5)/6,\quad
G=F^2=\operatorname{diag}(g_1,\ldots,g_5),\quad L=(I-G)^{1/2}.
$$

仪器的成功、失败 Kraus 算子分别为 $F,L$。三个全成功深度为 $0,1,2$。
对边坐标 $x=(a_{ij})_{i<j}$ 定义

$$
\mathcal T_F(A)=(K(A),\beta(A),K(FAF),K(F^2AF^2))
=\mathcal L_F(xx^{\mathsf T}),\quad
\mathcal L_F:\operatorname{Sym}^2(\mathbb R^{10})\to\mathbb R^{50}. \tag{2.1}
$$

每个对称 $5\times5$ 矩阵只列 $i\le j$ 坐标，故共有 $15+5+15+15=50$ 个分量。
$\mathbb R^{50}$ 使用这些分量的欧氏范数。

以下恢复输入均来自[量子边界卷，定理 9.1、引理 13.3、定理 13.4 及命题 14.1–14.2](RECURSIVE_RELATIONAL_OBSERVATION_MEASUREMENT_RELATIVE_QUANTUM_BOUNDARY.md)：
三个深度在全部实反对称矩阵上识别共同符号；原矩可线性恢复十个平方及三十个相邻边乘积；
原探测器的五十个无条件均值为 $Q_F(A)$，满足

$$
\mathcal T_F=D_MQ_F,\qquad
M_f=\begin{cases}2,&K_{ii},\\7/4,&K_{ij},\ i<j,\\5/2,&\beta_r.
\end{cases} \tag{2.2}
$$

同一基础多项式的 $M_f$ 在所有深度保持不变。
若 $B_F$ 为 $Q_F$ 的极化，则已有证书为

$$
\|B_F(u,v)\|_2\ge c_F\|u\|_2\|v\|_2,\qquad
c_F=1/40310784000. \tag{2.3}
$$

令 $d=\min(\|x-y\|_2,\|x+y\|_2)$、$D=\max(\|x-y\|_2,\|x+y\|_2)$，
上述输入给出 $dD\le c_F^{-1}\|Q_F(x)-Q_F(y)\|_2$。
因 $\|D_M^{-1}\|=4/7$，记 $C_T=4/(7c_F)$，其同一归一化下的后果是

$$
\begin{aligned}
\|xx^{\mathsf T}-yy^{\mathsf T}\|_F&\le C_T\|\mathcal T_F(x)-\mathcal T_F(y)\|_2,\\
d&\le\sqrt{C_T\|\mathcal T_F(x)-\mathcal T_F(y)\|_2},\\
D\ge a>0\quad&\Longrightarrow\quad
d\le C_T\|\mathcal T_F(x)-\mathcal T_F(y)\|_2/a.
\end{aligned} \tag{2.4}
$$

这里仅用了 $\|xx^{\mathsf T}-yy^{\mathsf T}\|_F\le\|x-y\|_2\|x+y\|_2$
及 $D\ge d$，不另引入未知常数。
若 $\|x\|,\|y\|\ge a$，则 $D\ge\sqrt2a$，尤其可用 (2.4) 的 $a$ 界。
原始数据误差不超过 $\epsilon$ 且估计的残差不超过 $\epsilon$ 时，将右侧数据差替换为 $2\epsilon$；
对任意离像读数则用真实误差与估计残差之和。
一般相位恢复的对应见
[Wang–Xu，定理 2.1](https://arxiv.org/html/1605.08034v3) 及
[Zhuang，引理 2.1、定理 2.3](https://doi.org/10.1186/s13660-019-1968-z)，
此处常数和探测面板取仓内已给证书。

### 命题 2.2（原面板的秩四十五与十维核）

在 (2.1) 的坐标合同下，

$$
\operatorname{rank}\mathcal L_F=45,\qquad\dim\ker\mathcal L_F=10.
$$

核没有非零秩至多二的实对称矩阵；面板可恢复实际秩一来源张量，
但不构成任意 $55$ 维对称张量的线性层析。

**证明。** 以已知可逆对角矩阵作合同变换，三个平方矩等价于
$N_r=AG^rA$、$r=0,1,2$。对每个 $i\ne j$，非对角元为
其余三个 $k$ 的 $a_{ik}a_{kj}$ 的三阶 Vandermonde 矩。
引理 13.3 的原矩反演给出全部三十个相邻边乘积，及十个平方。
这些是 $\operatorname{Sym}^2(\mathbb R^{10})$ 的四十个不同坐标方向，
因而平方矩部分的行空间至少为这四十维；它的每个分量只含这些坐标，故恰为四十维。

余下十五个坐标是不相交边乘积。每个四顶点集 $\{a,b,c,d\}$ 贡献三个，
对应的 $\beta$ 分量为带定向符号的

$$
2(a_{ab}a_{cd}-a_{ac}a_{bd}+a_{ad}a_{bc}).
$$

五个四顶点集的三个坐标组互不相交，每组增加恰一个非零独立方向。
总秩为 $40+5=45$，而对称矩阵空间维数为 $55$，核维数为十。

读数 $\operatorname{tr}K(A)=2\|x\|_2^2$ 说明核中张量迹为零。
若有非零秩至多二的核元，实谱分解将其写为
$xx^{\mathsf T}-yy^{\mathsf T}$，其中 $x,y$ 非零正交。
量子边界卷定理 9.1 的恢复输入迫使 $y=\pm x$，矛盾。∎

### 定义 2.3（同源制备、归一化与有限记录）

第 $j$ 次全成功分支的概率及虚部为

$$
p_j=\operatorname{tr}(F^{2j}S)>0,\qquad A_j=F^jAF^j/p_j,
\qquad p_j^2K(A_j)=K(F^jAF^j).
$$

两份独立同源输入同时成功的概率为 $p_j^2$。
使用量子边界卷定义 10.1 的联合二次探测、命题 10.2 的完整固定排程：
五十个成对配置、十五个单副本配置各尝试 $N$ 次，保留全部失败前缀，不重试。
成对报告 $Z_f\in\{-1,0,1\}$ 在失败时为零，按全部 $N$ 次求均值，直接估计 $Q_F$。
这需要独立同源制备及声明的联合探测，不由局部实操作单独提供。

命题 14.2 的已有置信输入是：$L_\delta=\log(130/\delta)$ 时，以概率至少 $1-\delta$，

$$
\|\overline q-Q_F(A)\|_2\le10\sqrt{L_\delta/N},\qquad
\|S_N-S\|_F\le\sqrt{85}\sqrt{L_\delta/(2N)}.
$$

若算术输出另有已界定误差 $a_Q,a_S$，分别加到两界上。
推论 14.3 在同一排程下计入 $115N$ 次来源制备、$15N$ 次单副本探测、
至多 $90N$ 次局部滤波、至多 $50N$ 次联合探测及 $155N$ 个填充记录位。
未知滤波器漂移、相关制备或新后选择规则不在这一输入合同内。

### 定理 2.4（一次滤波的严格合法连续盲族）

固定 $F$，只提供原始 $q$、一次成功及一次失败分支的 $q$、共同 $S$ 和标志概率时，
存在严格合法的完整 $\mathbb{RP}^1$ 歧义族。故此合同的最大滤波深度一不足，
深度 $0,1,2$ 则由定义 2.1 的输入达到恢复。

**证明。** 对一般 $0<g_1<\cdots<g_5<1$，在
$\operatorname{span}(e_1,e_3,e_5)$ 内选单位向量 $n$，满足

$$
n_i^2=\frac{(g_i-g_2)(g_i-g_4)}
 {\prod_{k\in\{1,3,5\}\setminus\{i\}}(g_i-g_k)},
\qquad i\in\{1,3,5\}.
$$

交错次序使三个数均正。对首一二次多项式作 Lagrange 插值，最高次项给其和为一，
且

$$
\sum_i n_i^2\prod_{k\in\{1,3,5\}\setminus\{i\}}(z-g_k)
=(z-g_2)(z-g_4).
$$

该式是三维对角矩阵压缩到 $n^\perp$ 的特征多项式；再加上 $e_2,e_4$，
得到 $E=n^\perp$ 上 $H=PGP|_E$ 的谱为 $(g_2,g_2,g_4,g_4)$，其中 $P=I-nn^{\mathsf T}$。
取适配的正向正交基，使两个谱平面为前二及后二坐标，定义

$$
A_\theta=s(\cos\theta L_2+\sin\theta L_3),\qquad0<s<1/5.
$$

其 $q$ 恒定。$L_2,L_3$ 都交换两个谱平面，且其任意单位线性组合平方为 $-I_E$，故

$$
A_\theta H A_\theta=-s^2(g_4P_{g_2}+g_2P_{g_4})
$$

恒定。由 $A_\theta=PA_\theta P$，这也确定恒定的 $A_\theta GA_\theta$，
因而成功分支平方 $-(FA_\theta F)^2$ 恒定。
对可逆实矩阵 $D$，外幂恒等式给

$$
\beta(DAD^{\mathsf T})=\det(D)D^{-\mathsf T}\beta(A).
$$

于是成功支的 $\beta$ 恒定。失败算子 $L$ 可逆，且
$A_\theta(I-G)A_\theta=A_\theta^2-A_\theta GA_\theta$ 恒定，失败支也如此。
共同 $S=I/5$ 使两分支的实部、概率及归一化因子均恒定，输入全严格正定。
$\theta$ 模 $\pi$ 为 $\mathbb{RP}^1$，不同点不互为共同符号。
对指定 $F$，上述 $n$ 可取

$$
n=(\sqrt{30}e_1+\sqrt{35}e_3+\sqrt{63}e_5)/\sqrt{128}.
$$

这只限制所述分支读数，不限制另行供应的完整联合张量探测。∎

### 推论 2.5（两个固定全成功深度不足）

一个预先固定的面板若只读两个不同全成功深度 $r<s$ 的 $q$，
外加共同 $S$ 与滤波成功/失败标志，则不能统一恢复所有合法态的 $[A]_\pm$。
在此固定面板合同内，最少需要三个深度，$(0,1,2)$ 达到。

**证明。** 置 $B=F^rAF^r$，两个代数读数等价于
$q(B)$、$q(F^{s-r}BF^{s-r})$，其归一化因子只依赖共同 $S$。
对简单谱滤波器 $F^{s-r}$ 应用定理 2.4 的成功支构造得 $B_\theta$。
令 $A_\theta=F^{-r}B_\theta F^{-r}$；统一缩小幅度使整个紧族在 $S=I/5$ 下严格合法。
所有标志词的 Kraus 算子均为实对角，故其概率只依赖 $S$，不区分该族。
三个深度的充分性是定义 2.1 的已有恢复输入。
此处不计入中间失败支的额外 $q$，不对自适应深度或任意新联合探测作最优性结论。∎

### 命题 2.6（零点的指数边界）

即使采用三深度面板，零态邻域也不存在指数严格大于 $1/2$ 的统一 Hölder 状态逆。

**证明。** 固定非零 $A_0$，比较 $tA_0$ 与零。输入商距离正比于 $t$，
全部二次数据差正比于 $t^2$；若指数为 $\alpha>1/2$，
$t\le Ct^{2\alpha}$ 在 $t\downarrow0$ 时不可能。
共同取 $S=I/5$ 及充分小的 $t$，两输入严格合法。∎

## 3. 二次张量与 Hecke 态射的类型

### 定义 3.1（系数表示及本征结构输入）

复化并置 $\check G=\operatorname{SO}_5(\mathbb C)$、$G=\operatorname{Sp}_4(\mathbb C)$，
$R=\operatorname{Sym}^2(\mathfrak{so}_5)$、$R'=\mathbf1\oplus V_{14}\oplus V_5$。
[结构取得卷，定理 6.2、7.2、7.4](AURIC_LANGLANDS_STRUCTURE_ACQUISITION_AND_SPECTRAL_EXTENSION_THEORY.md#7-从张量态射到-hecke-相容性)
供应满射 $\Psi:R\twoheadrightarrow R'$、三十五维核表示 $W$、平行分裂和 Hecke 自然性。
实态上 $\Psi(A\odot A)=q(A)$。

给定光滑连通复曲线 $X$ 上的 $\check G$ 局部系统 $E$。
在复线性自守范畴中，一个非零本征对象 $\mathcal F$ 具有对每个表示 $T$ 的同构

$$
\varepsilon_T:\mathsf H_T(\mathcal F)\xrightarrow{\sim}E_T\boxtimes\mathcal F,
$$

且对表示态射、单位、张量积及多点融合相容。
这里 $\mathsf H_T$ 是从自守范畴到曲线与自守空间乘积上相应范畴的函子。
表示态射 $\phi:T\to T'$ 产生自然变换
$\mathsf H(\phi):\mathsf H_T\Rightarrow\mathsf H_{T'}$，
在 $x\in X$ 的取值为态射

$$
\mathsf H(\phi)_x(\mathcal F):
\mathsf H_{T,x}(\mathcal F)\longrightarrow\mathsf H_{T',x}(\mathcal F),
$$

满足

$$
\varepsilon_{T',x}\circ\mathsf H(\phi)_x(\mathcal F)
=(\phi_{E,x}\otimes\operatorname{id}_{\mathcal F})\circ\varepsilon_{T,x}. \tag{3.1}
$$

半单性给出 $p_W:R\to W$ 及 $i_W:W\to R$，$p_Wi_W=\operatorname{id}_W$。
$p_W$ 是态射，不是 Hecke 函子的表示对象下标。
[语境谱重构卷，定理 10.7](AURIC_LANGLANDS_CONTEXT_AND_SPECTRAL_RECONSTRUCTION_THEORY.md#10-中心提升与具体-hecke-接口)
的非零通道输入具体用于 (3.1)，给出

$$
\mathsf H(p_W)_x(\mathcal F):
\mathsf H_{R,x}(\mathcal F)\longrightarrow\mathsf H_{W,x}(\mathcal F)
\quad\text{非零}. \tag{3.2}
$$

其线性理由是：纤维函子 $T\mapsto E_{T,x}$ 忠实，$p_{W,E,x}$ 有非零矩阵元 $c$；
若右侧的 $p_{W,E,x}\otimes\operatorname{id}_{\mathcal F}$ 为零，
前后复合相应坐标注入、投影即得 $c\operatorname{id}_{\mathcal F}=0$，
与 $\mathcal F\ne0$ 矛盾。故完整本征合同不能经一个杀掉此态射的线性商下降并仍保留非零 $\mathcal F$。
该论证是既有自然性输入的具体应用。

### 命题 3.2（三深度恢复与系数商的不同目标）

采用[结构取得卷，命题 15.1](AURIC_LANGLANDS_STRUCTURE_ACQUISITION_AND_SPECTRAL_EXTENSION_THEORY.md#152-严格正定态上的完整反例)
的合法等重纤维与非零差 $A\odot A-B\odot B\in W$ 作为输入。
三深度面板能在实际来源张量上恢复该差，
但其十维线性核及其非等变的固定滤波不提供整个 $\operatorname{Rep}(\check G)$ 的替代。

**证明。** 所引输入可取定义 1.1 合法球面中的 $A=sL_1$、$B=sL_2$；
其秩一张量不同而 $\Psi$ 像相同。
定义 2.1 的恢复输入分离这两个张量，命题 2.2 又给非零十维线性核，
因此任意对称张量的线性恢复仍不成立。
$F$ 在固定框架内有互异特征值，一般不与 $\operatorname{SO}_5$ 变基交换，
故这些读数没有由定义获得表示张量函子结构。
要使用 (3.1)，仍须另外给出同一 $E$、表示态射和完整本征结构。∎

### 假设 3.3（外部无分歧本征存在性的适用范围）

若由 $E$ 推出本征对象存在，取特征零复系数、光滑连通射影复曲线、
代数 de Rham $\check G$ 局部系统，且 $E$ 不存在到真抛物子群的水平约化。
采用 $\mathrm D\text{-}\mathrm{mod}_{1/2}(\operatorname{Bun}_G)$ 的标准半扭约定，
以及其标准 Hecke、张量和融合归一化。
外部供应为 [Gaitsgory–Raskin I，§6.1.1、定理 6.1.3(1)–(4)](https://arxiv.org/html/2405.03599v3)
在 GLC 前提下的本征对象接口，加上
[V，推论 2.3.11、§5.5](https://arxiv.org/html/2409.09856v3) 的 GLC 结论。
不使用 I 的定理 6.1.3(5) 所附的中心连通及特征循环断言。
仅给分别存在的本征同构而不给态射自然性，不足以使用 (3.1)。
穿孔曲线上的有分歧参数、其他系数范畴或未经代数化的比较，均须各自的外部接口。

## 4. 完整来源、读数阶及退化换图

### 定义 4.1（来源模型与读数坐标）

取 $R=\mathbb C\{s\}$ 或 $\mathbb C[[s]]$，$K=\operatorname{Frac}(R)$。
给定有限自由秩 $n$ 的交换来源代数 $\mathcal A/R$，要求泛代数 $\mathcal A_K$ 有限 étale。
若要把来源判别式解释为完整来源的几何分歧，取真实有限平坦来源模型，
特别可取 $\mathcal A_K$ 的有限正规化；单读数生成的阶不自动是这个模型。
对来源基 $b=(b_0,\ldots,b_{n-1})$，置

$$
G_{\mathcal A,b}=(\operatorname{Tr}_{\mathcal A/R}(b_ib_j)),\qquad
\Delta_{\mathcal A,b}=\det G_{\mathcal A,b}.
$$

泛原始读数 $m\in\mathcal A$ 满足 $K[m]=\mathcal A_K$。
记 $Q_m$ 为乘法 $m$ 的特征多项式，并定义

$$
(1,m,\ldots,m^{n-1})=bC_m,\qquad I_m=\det C_m,\qquad
\mathcal B_m=R[m]\subseteq\mathcal A.
$$

迹判别式及 étale 判据采用
[Stacks，§49.3、引理 49.3.1](https://stacks.math.columbia.edu/tag/0BVH)。

### 定理 4.2（完整来源的读数退化与补充读数换图）

在定义 4.1 中，来源与读数的退化由下式分开：

$$
\operatorname{disc}Q_m=I_m^2\Delta_{\mathcal A,b},\qquad
v_s(\operatorname{disc}Q_m)
=v_s(\Delta_{\mathcal A,b})+2\operatorname{length}_R(\mathcal A/\mathcal B_m). \tag{4.1}
$$

来源仍 étale 时，单读数碰撞的消失阶必为偶数；反向不成立。
若有限 étale 复解析来源覆盖的函数对 $(m,j)$ 在一点纤维分离全部来源，
则除去至多 $\binom n2$ 个 $\lambda\in\mathbb C$，$m+\lambda j$ 在该点附近的幂基
给出完整来源代数的正则基；旧 $m$ 碰撞不妨碍此换图中的规范连接。

**证明。** 先将经典判别式变基律应用到这里的来源与读数阶。
Cayley–Hamilton 及泛原始性使幂序列成为 $R[m]$ 的基，且

$$
G_m=C_m^{\mathsf T}G_{\mathcal A,b}C_m.
$$

泛分裂域内 $G_m=V_m^{\mathsf T}V_m$，$V_m$ 的第 $a$ 行为
$(1,m_a,\ldots,m_a^{n-1})$，故 $\det G_m=\operatorname{disc}Q_m$。
取行列式得第一式；DVR 上 $C_m$ 的 Smith 标准形给
$v_s(I_m)=\operatorname{length}_R(\mathcal A/R[m])$，得第二式。
迹配对的 étale 判据使来源 étale 时第一项为零。
反例是完整正规来源 $R[t]/(t^3-s)$：真实分歧，而判别式 $-27s^2$ 为偶数阶。
因此偶数阶不能证明来源无分歧。

在所述 étale 纤维上，一对来源若 $j_a=j_b$，则 $m_a\ne m_b$，任何 $\lambda$ 均分离；
若 $j_a\ne j_b$，仅 $\lambda=-(m_a-m_b)/(j_a-j_b)$ 失效。
避开这些至多 $\binom n2$ 个值，纤维的 Vandermonde 行列式非零。
缩小邻域使其为单位，幂基遂为完整来源基。
étale 代数的规范连接内在正则，故能越过旧读数碰撞。
若某一对同时有相同 $m,j$，所有线性组合都不能分离这一对。∎

### 命题 4.3（二来源的留数、分歧及正规化）

对 $\eta\in\{0,1\}$，取

$$
\mathcal A_\eta=R[e]/(e^2-s^\eta),\qquad
m=c(s)+s^ku(s)e,\quad k\ge0,\quad u\in R^\times.
$$

来源基 $(1,e)$ 与中心化读数基 $(1,m-c)$ 给

$$
\begin{aligned}
\Delta_{\mathcal A_\eta}&=4s^\eta,&\operatorname{disc}Q_m&=4s^{2k+\eta}u^2,\\
\nabla e&=\tfrac\eta2e\,ds/s,&
\nabla(m-c)&=(m-c)\bigl((k+\eta/2)ds/s+du/u\bigr).
\end{aligned} \tag{4.2}
$$

解析情形 $R=\mathbb C\{s\}$ 的水平单值为 $\operatorname{diag}(1,(-1)^\eta)$；
形式情形只断言连接及留数公式。整数读数留数可在完整来源格中消去；
简单分歧的半整数留数不能在未分歧圆盘上消去。

**证明。** 来源迹矩阵为 $\operatorname{diag}(2,2s^\eta)$，读数变基行列式为 $s^ku$。
代入 (4.1)，并对 $e^2=s^\eta$ 求导，再用 Leibniz 法则得 (4.2)。
$du/u$ 留数为零，中心化读数基的留数为 $\operatorname{diag}(0,k+\eta/2)$。
水平系数满足 $df+Cf=0$，单值为 $\exp(-2\pi i\operatorname{Res}C)$。

$\eta=0,k=1,u=1,c=0$ 给来源 $R\oplus R$、读数 $(s,-s)$ 及方程 $T^2-s^2$。
来源始终分离，$e=m/s$ 在完整来源代数内，但不在旧阶 $R[m]$ 内；
该消奇步骤不是旧阶内处处可逆的换基。
$\eta=1$ 给 $T^2-s$；穿孔单值为 $-1$，而圆盘单连通，故不能无分歧延拓这个秩一分量。
作 $s=t^2$ 后，直接拉回代数 $\mathbb C\{t\}[e]/(e^2-t^2)$ 仍在原点非 étale；
其正规化为 $\mathbb C\{t\}\oplus\mathbb C\{t\}$，在其中 $e/t$ 才提供正则分裂格。
消单值与选择延拓格因此为两个不同步骤。∎

### 命题 4.4（读数幂基的条件数与实际三来源应用）

设一条实参数路径上 $n$ 个实读数在 $s=0$ 有有限极限，恰一对差
$d(s)=m_1(s)-m_2(s)$ 趋零，其他根差保持非零，且小的 $s\ne0$ 时 $d(s)\ne0$。
则

$$
\sigma_{\min}(V_m)\asymp|d(s)|,\quad
\|V_m^{-1}\|\asymp|d(s)|^{-1},\quad
\lambda_{\min}(G_m)\asymp|d(s)|^2. \tag{4.3}
$$

对[正 $M$ 整子域卷，定理 1.1–1.2、§5](FIB_POSITIVE_M_ENTIRE_CHILD_J_OBSTRUCTION.md)
的三个完整实际来源，内部终端 $M$ 碰撞点附近的复化分支形成
$\mathcal A_{\rm act}\simeq\mathcal O_B^3$。
来源判别式为单位，终端 $J$ 为越过该碰撞的原始元图。

**证明。** 极限 Vandermonde 矩阵秩为 $n-1$，最大的 $n-1$ 个奇异值有正的上下界。
其行列式为根差乘积，与 $d(s)$ 同阶，奇异值乘积公式给前两式。
实路径的 $G_m=V_m^{\mathsf T}V_m$ 给第三式；复路径不能用此非 Hermitian 迹矩阵
代替 $V_m^*V_m$ 来推断最小特征值。

所引实际来源输入给：参数矩形内恰有三个完整来源，宽度根简单，来源、增益及漂移实解析，
终端 $J$ 两两分离，且存在来源二、三的终端 $M$ 碰撞。
在内部碰撞点附近复化并缩小邻域，三个来源继续分离，故来源代数分裂。
由于 $J$ 分离纤维，定理 4.2 的换图适用。若其余 $M$ 根差为单位，则

$$
\operatorname{disc}Q_{M,\rm act}
=(m_1-m_2)^2(m_1-m_3)^2(m_2-m_3)^2
=u(m_2-m_3)^2,\qquad u\in\mathcal O_B^\times.
$$

此式不要求 $m_2-m_3$ 有简单零，不能据此断言 $k=1$。
结论仅涉及这三个来源，未识别的其余复候选不包含在 $\mathcal A_{\rm act}$ 中。∎

### 假设 4.5（换图的取得条件）

$m+\lambda j$ 是来源函数的代数表达式。
若 $m,j$ 来自互斥终端动作，应用其重构公式须已合法恢复完整来源，
或另有可独立重备同一来源并分别取得两者的合同。
单纯允许这两个终端动作，不意味着可在同一次未知来源上免费共同取得它们。

## 5. 完整来源取向与已给谱提升的共同覆盖

### 定义 5.1（正规来源覆盖、锚点与评价的共同底）

固定光滑连通射影复曲线 $X$，以及指定的完整泛来源代数
$\mathcal K/\mathbb C(X)$，它是有限可分域扩张的有限直积。
令 $\overline{\mathcal A}$ 为 $\mathcal O_X$ 在 $\mathcal K$ 内的积分闭包，
$\overline C=\operatorname{Spec}_X\overline{\mathcal A}$。
删去有限分歧点及所需函数极点，得非空 $U=X\setminus D$，置

$$
\mathcal A_U=\overline{\mathcal A}|_U,\quad
C=\operatorname{Spec}_U\mathcal A_U\xrightarrow{\pi}U.
$$

它是完整来源的有限 étale 覆盖，可以不连通；来源身份须由模型指定，
单个读数的方程不能替代这个指定。定义 4.1 的局部来源代数取
$\overline{\mathcal A}$ 的相应局部化或完成，读数阶是其中的子代数。
在读数幂基行列式为单位的开集，读数阶与完整来源代数相同；
旧读数碰撞但来源 étale 的点则用定理 4.2 换图。

若来源首先在另一个参数空间 $B$ 上给出，须给出明确的模型映射
$f:U\to B$ 及 $\mathcal A_U\simeq f^*\mathcal A_B$ 的来源识别。
仅有读数多项式同次或候选数相同，不构成该识别。
固定基点 $x_0\in U$ 及合法取得的完整来源评价 $c_0\in C_{x_0}$。
记 $\Omega=C_{x_0}$，$\Gamma=\pi_1(U,x_0)$，
$\nu:\Gamma\to\operatorname{Sym}(\Omega)$，$F_0=\operatorname{im}\nu$，
$\omega=c_0$，$H=(F_0)_\omega$，$m=[F_0:H]$。
基本群取解析基本群；有限作用也等价地经其 étale 完备化。

[取得覆盖卷，命题 4.5、定理 10.3](AURIC_LANGLANDS_ACQUISITION_COVER_AND_CRITICAL_DOMAIN_THEORY.md)
的选层输入具体给：包含 $c_0$ 的连通分支 $Z_0\subset C$ 是
$\nu^{-1}(H)$ 对应的 $m$ 层带锚覆盖。
令 $S=(\pi|_{Z_0})_*\mathcal O_{Z_0}$，限制映射为
$\chi:\mathcal A_U\twoheadrightarrow S$。拉回到 $Z_0$ 后，图截面给

$$
e\in\mathcal A_U\otimes_{\mathcal O_U}S,\qquad
e^2=e,\quad\operatorname{Tr}(e)=1,\quad
\chi(a)=\operatorname{Tr}((a\otimes1)e),\quad\nabla e=0. \tag{5.1}
$$

这里的迹相对于 $S$。该幂等元在完整拉回代数中，而非 $S$ 自身中的迹一幂等元。
逐纤维它恰选择图截面那一个来源，故 (5.1) 的评价及迹成立；
对 $e^2=e$ 求导并用 $(2e-1)^2=1$，得水平性。
有限覆盖与有限基本群集合的经典供应为
[Stacks，定理 58.6.2](https://stacks.math.columbia.edu/tag/0BND)。

### 定理 5.2（来源取向作用于指定稠密提升）

对定义 5.1 的整个来源覆盖，令

$$
\varepsilon=\operatorname{sgn}\circ\nu:\Gamma\to\mu_2,
\qquad L_\varepsilon\text{ 为其秩一局部系统}.
$$

其为来源置换局部系统的行列式；不要求 $F_0$ 是全对称群。
另外给定同一 $X$ 上的提升

$$
\widetilde\rho_X:\pi_1(X,x_0)\to\operatorname{Spin}_5(\mathbb C)
\simeq\operatorname{Sp}_4(\mathbb C),\qquad
\rho_X=\varpi\widetilde\rho_X
$$

且 $\rho_X$ 的像在 $\operatorname{SO}_5$ 中 Zariski 稠密。
对包含 $j:U\hookrightarrow X$，准确的扭曲为

$$
\widetilde\rho_U=\widetilde\rho_X\circ j_*,\qquad
\widetilde\rho_U^\varepsilon(\gamma)
=\varepsilon(\gamma)\widetilde\rho_X(j_*\gamma). \tag{5.2}
$$

它是同一 $\rho_X\circ j_*$ 的稠密中心提升。
$\varepsilon\ne1$ 时，新旧提升不同构。
同时完成指定来源选层及平凡化整个取向字符的最小连通有限 étale 覆盖次数为

$$
\boxed{[F_0:H\cap\ker(\operatorname{sgn}|_{F_0})]
=m[H:H\cap\ker(\operatorname{sgn}|_{F_0})]\in\{m,2m\}.} \tag{5.3}
$$

**证明。** 泛原始读数的 Vandermonde 平方根
$d_m=\prod_{a<b}(m_a-m_b)$ 沿来源置换变为 $\varepsilon d_m$。
换读数在泛来源代数中只是两个基间的变换，(4.1) 使其比值为单值有理行列式，
因此字符不变。平方因子的读数交叉不产生新取向单值；
$y^2=\operatorname{disc}Q_m$ 在碰撞处非正规时，取其二次泛代数的正规化，允许其分裂。

稠密性与中心提升的比较沿用[取得覆盖卷，命题 6.2–6.3](AURIC_LANGLANDS_ACQUISITION_COVER_AND_CRITICAL_DOMAIN_THEORY.md#6-共同底曲线稠密性与中心提升)
的有限指数及中心化子论证，在这里将字符明确取为完整来源的取向。
由中心 $\mu_2$ 的乘法律，(5.2) 为表示且被 $\varpi$ 杀去字符。
$j_*$ 满射，所以未扭曲的正交像仍稠密。
提升的 Zariski 闭包映满 $\operatorname{SO}_5$，有限核给相同维数，故闭包为连通群 $\operatorname{Sp}_4$。
有限指数子群在连通代数群中的稠密表示仍稠密：否则该群为真闭子群有限个陪集之并，
与不可约性矛盾。在 $\ker\varepsilon$ 上两表示相同，因此扭曲也稠密。
若共轭元 $h\in\operatorname{Sp}_4$ 识别两个提升，则 $\varpi(h)$ 中心化稠密正交像。
$\operatorname{SO}_5$ 的中心平凡，所以 $h\in\mu_2$，共轭作用恒等，迫使 $\varepsilon=1$。

最后用定义 5.1 的有限覆盖输入。子群 $K\le\Gamma$ 同时实现选层和全局取向平凡化，
当且仅当

$$
K\subseteq\nu^{-1}(H)\cap\ker\varepsilon
=\nu^{-1}(H\cap\ker\operatorname{sgn}).
$$

右端为最大的允许子群，故其指数给最小次数并被对应覆盖达到。
符号像至多二阶，得到 $m$ 或 $2m$。∎

### 定理 5.3（外围延拓的次数与剩余 Picard 类）

设 $f:Y\to X$ 为 $U$ 上某个连通有限 étale 覆盖 $Z\to U$ 的正规光滑紧化，
$e_y$ 是 $y\mid x\in D$ 的局部分歧指数，$\delta_x$ 为外围环路。
固定提升 (5.2) 拉回后无分歧延拓到 $Y$ 当且仅当

$$
\varepsilon(\delta_x)^{e_y}=1\quad\text{对所有 }y\mid x. \tag{5.4}
$$

在最小选层 $Z_0$ 的紧化 $Y_0$ 上，记限制字符为 $\varepsilon_0$。
所有完成同一带锚选层的进一步连通覆盖中，令固定提升无分歧延拓所需的最小总次数为
$m$，若 $\varepsilon_0$ 在所有外围环路上平凡；否则为 $2m$。

取整个泛来源代数的泛原始读数，令其非零有理判别式为
$\Delta_m\in\mathbb C(X)^\times$，在 $Y_0$ 置 $g=f_0^*\Delta_m$。
于是

$$
\begin{aligned}
\varepsilon(\delta_x)&=(-1)^{\operatorname{ord}_x\Delta_m},\\
m\text{ 层即平凡化全局取向}
&\Longleftrightarrow g\in\mathbb C(Y_0)^{\times2},\\
m\text{ 层即无分歧延拓固定提升}
&\Longleftrightarrow\operatorname{div}(g)\in2\operatorname{Div}(Y_0).
\end{aligned} \tag{5.5}
$$

若除子为偶，$D_g=\tfrac12\operatorname{div}(g)$ 给剩余中心类

$$
\mathcal O_{Y_0}(D_g)\in\operatorname{Pic}^0(Y_0)[2], \tag{5.6}
$$

它平凡当且仅当 $g$ 是函数域平方。

**证明。** $y$ 的外围小圈在 $U$ 中映为 $\delta_x^{e_y}$，至多差共轭。
原提升来自整个 $X$，故其外围像为单位；扭曲的拉回外围像恰为
$\varepsilon(\delta_x)^{e_y}I_4$。
穿孔曲线基本群到紧曲线基本群的核由外围圈正规生成，得 (5.4)。

任何同一带锚选层覆盖都经由 $Z_0$。
若外围已平凡，$Z_0$ 达到次数 $m$。
若某外围值为 $-1$，进一步覆盖在该边界点每个上方点的局部指数必须为偶数，
这些指数之和是进一步覆盖次数，故次数至少二且为偶。
$\ker\varepsilon_0$ 的双覆盖消去整个字符，达到总次数 $2m$。

局部写 $\Delta_m=s^a u$，$a\in\mathbb Z$ 允许为负；单位 $u$ 在小圆盘有平方根，
故其平方根单值为 $(-1)^a$。拉回阶数乘以局部分歧指数，得到 (5.5) 的外围判据。
全局平方类平凡恰为对应二值覆盖分裂，即字符消失。
当 $\operatorname{div}(g)$ 为偶，$2D_g$ 主且 $\deg D_g=0$，得 (5.6)。
局部平方根的符号转移函数给该二阶线丛。
若此线丛平凡，写 $D_g=\operatorname{div}(h)$，则 $g/h^2$ 在紧曲线上无零极点，
为非零复常数，常数有平方根，因此 $g$ 为平方；逆向直接成立。
这是 [Stacks，§59.28](https://stacks.math.columbia.edu/tag/03PK) 的 Kummer 序列
在此来源判别式上的具体应用。∎

### 命题 5.4（两个覆盖目标的区别及谱对偶方向）

全局取向平凡化的最小次数可以为 $2m$，而固定提升无分歧延拓只需 $m$。
中心扭曲保持全部 $\operatorname{SO}_5$ 系数本征值，却可改变四维旋量系数。

**证明。** 若 $\varepsilon_0$ 在紧曲线的把手环路上非平凡、在所有外围圈上平凡，
则 (5.3) 需再加双覆盖，而 (5.4) 已在 $Y_0$ 上成立。
这个情形可由完整来源实现：取正 genus 的 $X$ 及其非平凡未分歧双覆盖，
令 $C$ 为该双覆盖与一个平凡来源层的无交并，并锚定平凡层。
此时 $m=1$、$Y_0=X$，而整个三层来源的取向恰为该双覆盖的非平凡字符。
这种双覆盖由 $H^1(X,\mu_2)$ 的非零元素给出。
局部来源单值若是换位，选中被交换来源的局部指数二消去该中心值；
选中被换位固定的另一个来源则局部指数一，保留 $-I_4$。
自然 $S_n$ 单值、$n\ge3$ 时，稳定子 $S_{n-1}$ 有非平凡符号，(5.3) 为 $2n$；
$n=2$ 时稳定子平凡，仅需二层。候选数至多十八不推出单值群为 $S_{18}$。

四维旋量表示满足

$$
V_4(\widetilde\rho_U^\varepsilon)=V_4(\widetilde\rho_U)\otimes L_\varepsilon,
\qquad
\Lambda^2_0V_4(\widetilde\rho_U^\varepsilon)
\simeq\Lambda^2_0V_4(\widetilde\rho_U),
$$

第二式的右端取同一五维识别，来自 $L_\varepsilon^{\otimes2}\simeq\mathbf1$。
一般中心齐次表示按中心奇偶性扭曲或不变。
因此 $\operatorname{SO}_5$ 谱群对应自守群 $\operatorname{Sp}_4$，
若改用 $\operatorname{Spin}_5\simeq\operatorname{Sp}_4$ 谱群，则自守对偶改为 $\operatorname{SO}_5$。
有限覆盖上仍稠密；若 (5.4) 成立，提升下降到 $Y$ 后仍稠密，
因而无真抛物水平约化。依假设 3.3 的 de Rham、半扭和无分歧外部供应可取得相应本征对象。
这只把来源的二值字符作用于已给稠密提升，不把有限置换像等同于稠密正交像，
也不构造自守基变换函子。∎

## 6. 共同历史与七读数的局部重构

### 定义 6.1（共同历史下界的输入及独立时钟合同）

来源域含非空 $n$ 维光滑开片，目标在片上单射。
每个固定、实际可执行有限动作词的每项实标量报告光滑依赖来源。
确定性反馈只依赖已取得的完整动作—读数历史，策略函数无需连续、可测或可计算，
标量预算计入强制初读。
[自校准卷 II，引理 75.3、76.3、定理 76.4、推论 76.5](FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md)
供应共同历史下界 $n$：固定共同历史后，下一动作相同；每个非恒定光滑报告
可在正则等值面上保持共同历史且维数只减一，恒定报告不降维。
因此少于 $n$ 项不能消去正维共同历史纤维。

其多项式实例取

$$
S(p,q,r)=\begin{pmatrix}p&q\\r&qr/p\end{pmatrix},\quad p,q,r>0,
\quad G_\gamma(t)=1+\sum_{l=1}^k\gamma_lt^l,\quad\deg D\le d,
$$

读取 $z_i=G_\gamma(i)\operatorname{tr}(A_iS)+D(i)$，
目标为 $(S/\operatorname{tr}S,(\operatorname{tr}S)G_\gamma,D)$。
第二分量常数项恢复 $\operatorname{tr}S$，故目标单射，参数维数为 $k+d+4$。
沿用所引定理的世界开域及常漂移见证，$k\ge2$ 时统一下界为
$\max\{k+d+4,k+5\}$。这些为既有输入。

另一个不同的资源合同来自
[未校准二次时钟卷，定义 1.1、定理 3.1、10.2–10.4](FIB_UNCALIBRATED_QUADRATIC_CLOCK_THREE_INDEX_DESIGN.md)：
同一轨迹的索引 $0<u<v$ 供应

$$
y_i=\alpha(i+\tau)^2+\beta+\eta_i,
\quad\tau\in[a,b],\quad\alpha\ge m>0,\quad\beta\in\mathbb R,
\quad\eta\in[-\epsilon,\epsilon]^3.
$$

它的增益、零位与主世界干扰独立，原始闭坐标误差保持为整立方体，
不同候选可分别校准；其精确三索引风险、严格平衡尾部及有限核心整数设计均为所引输入。
等待、实际报告及同轨迹主动作分别计费。
该时钟输入不属于前一个无侧通道世界类，不能把其三项报告当成主历史中的免费标量，
也不能将其风险最优设计替换为七读数主词的全域识别结论。

### 推论 6.2（固定退化纤维的附加读取下界）

固定 $q$ 已取得，若实际来源仍可遍历一个完整合法 $\mathbb{RP}^2$ 纤维，
后续固定动作每次只给一个光滑实标量，则少于两次附加读取不能统一恢复来源类。

**证明。** 限制到此纤维的任意二维坐标开片；来源类目标在片上单射，
已有 $q$ 恒定。应用定义 6.1 的共同历史输入，预算至少二。
这不给出两次附加读取的充分性。∎

### 定理 6.3（原子词 $JJJJMJ$ 的七读数泛型局部逆）

令

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\quad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
\quad0<r<1,\ b>0.
$$

增益 $g(t)=h_0+h_1t+h_2t^2+h_3t^3$，漂移为常数 $d$。
时钟零、$A_0=I$，按左乘约定逐个执行并立即读取六个原子：

$$
(E_1,\ldots,E_6)=(J,J,J,J,M,J),\quad A_i=E_iA_{i-1},
\qquad\Phi_i=d+g(i)\operatorname{tr}(A_iP),\quad0\le i\le6.
$$

$\Phi(r,b,h_0,h_1,h_2,h_3,d)$ 的 Jacobian 在非空 Zariski 开集满秩七；
它在实际参数开域内的非零集稠密，并在每个这样的位置有光滑局部逆。

**证明。** 在 $r=1/3,b=2/3,g\equiv1,d=0$ 检验微分核。
写 $c=r(1-r)/b$、$s=b+c$，该点 $c=1/3,s=1$，且

$$
\delta c=(\delta r-\delta b)/2,\qquad
\delta s=(\delta r+\delta b)/2.
$$

设所有报告微分为零，记三次增益微扰多项式为 $p$。
偶数时刻 $0,2,4$ 的累乘矩阵为 $I$，所以
$p(i)+\delta d=0$，从而

$$
p(t)=-\delta d+a\,t(t-2)(t-4).
$$

奇数时刻 $1,3$ 的累乘为 $J$，报告微分给
$3a+\delta s=0$、$-3a+\delta s=0$，故 $a=\delta s=0$、$\delta b=-\delta r$。
时刻五、六的累乘分别为 $M,JM$，迹分别为
$s+1-r=5/3$、$1+c=4/3$。其零微分条件化为

$$
-\tfrac23\delta d-\delta r=0,\qquad
-\tfrac13\delta d+\delta r=0.
$$

相加给 $\delta d=0$，随后所有参数微扰均为零。
Jacobian 行列式为仅以 $b$ 的幂作分母的有理函数，且在此点非零，
其分子不恒零。非零集为非空 Zariski 开，在实际开域的补集无内点。
逆函数定理给逐点局部逆。∎

### 命题 6.4（局部七读数与全域八读数下界相容）

定理 6.3 不构成统一七读数解码；它与定义 6.1 在 $(k,d)=(3,0)$ 时
给出的至少八次统一下界相容。

**证明。** 满秩 Jacobian 只在给定点的一个邻域内保证单射及逆，
不排除其他来源分支映到同一记录，也不控制退化参数。
统一下界要求对整个世界类的每个来源正确。
词中六个新原子及已有初读恰为七项，没有复位、复制或跳读；
缺少全域选层信息不由局部逆定理补给。∎

## 7. 允许切换时的 $\Omega_6/\Omega_7$ 分界

### 定义 7.1（共同 Fock 子空间及切换权限）

取 $V=\operatorname{span}_{\mathbb C}(e_0,\ldots,e_4)$、
$Q=\operatorname{span}_{\mathbb C}(f_+,f_-)$、$W=V\oplus Q$，所有指定基向量正交规范。
沿用[取得覆盖卷，定义 7.4、命题 7.5](AURIC_LANGLANDS_ACQUISITION_COVER_AND_CRITICAL_DOMAIN_THEORY.md#7-hankel-证书与-ω-六维自治实现)
的共同 Fock 实现：$e_4=|101\rangle$、$f_+=|200\rangle$、$f_-=|002\rangle$，

$$
H(g,J)=g a_1^\dagger a_3+\overline g a_3^\dagger a_1+Jn_1n_3,
\quad g\ne0,\quad J\in\mathbb R,
$$

其中 Hamiltonian 保留能量量纲，传播子为 $e^{-itH/\hbar}$。
设 $r_g=|g|$、$u_g=g/r_g$，则

$$
b_g=(u_gf_++\overline u_gf_-)/\sqrt2,\quad
z_g=(u_gf_+-\overline u_gf_-)/\sqrt2,
$$

$$
H(g,J)e_4=Je_4+2r_gb_g,\qquad
H(g,J)b_g=2r_ge_4,\qquad H(g,J)z_g=0,
$$

其余 $V$ 基向量的像仍在 $V$。
固定单个 Hamiltonian 的六维最小实现为上述来源的已有输入。

这里另外给定非空族 $H_a=H(g_a,J_a)$，允许任意有限连续时间混合脉冲词，
目标为复现所有 $V\to V$ 压缩复振幅。
一个有限维自伴切换实现由共同等距嵌入 $\iota:V\hookrightarrow\mathcal H'$
及每个标签 $a$ 的自伴 $H'_a$ 给出，要求每个相同标签、时长的允许词满足

$$
\iota^*e^{-it_kH'_{a_k}/\hbar}\cdots e^{-it_1H'_{a_1}/\hbar}\iota
=P_Ve^{-it_kH_{a_k}/\hbar}\cdots e^{-it_1H_{a_1}/\hbar}|_V,
\qquad t_i\ge0.
$$

若允许中途代码修正 $R$，明确其在共同空间的扩张为酉算子 $R\oplus I_Q$。
仅知道端点修正不提供此中途扩张或 Hamiltonian 切换权限。

### 定理 7.2（全部混合词的最小自伴实现）

令 $B=\operatorname{span}_{\mathbb C}\{b_{g_a}\}\subseteq Q$、$k=\dim B$。
从 $V$ 出发的线性可达张成、以 $V$ 为输出的可观测张成都为 $V\oplus B$。
复现全部允许混合词振幅的最小有限维自伴切换实现维数为

$$
\boxed{d_{\min}=5+k=
\begin{cases}
6,&g_a/g_0\in\mathbb R\setminus\{0\}\text{ 对所有 }a,\\
7,&\operatorname{Im}(g_a\overline{g_0})\ne0\text{ 对某个 }a.
\end{cases}} \tag{7.1}
$$

**证明。** 每个 $H_a$ 把 $V$ 的隐藏像送到 $\mathbb Cb_{g_a}$，把 $Q$ 送回
$\mathbb Ce_4$，故 $V\oplus B$ 对所有 $H_a$ 及所准许的 $R\oplus I_Q$ 不变。
自伴、酉性使它约化，限制到该空间即可实现全部词。
可达张成含 $V$；对任意小正脉冲取右导数，有限维线性空间闭合，故含
$b_{g_a}=(H_ae_4-J_ae_4)/(2r_{g_a})$，于是恰为 $V\oplus B$。
对伴随词同理，可观测张成相同。

最小性用明确 Gram 证书：列族 $[V,H_0V,H_1V,\ldots]$ 张成 $V\oplus B$，
可选有限子族达到秩 $5+k$。其 Gram 块为 $I$、$P_VH_a|_V$、$P_VH_aH_b|_V$。
全部混合词振幅的一阶、混合二阶时间导数决定这些块；
任何同词振幅自伴实现的对应列族具有相同 Gram 矩阵，维数至少为其秩。
限制实现达到此下界。
最后两个 $b$ 复线性相关当且仅当
$u_a/u_0=\overline u_a/\overline u_0$，即该单位复数为 $\pm1$，
等价于 $g_a/g_0$ 为非零实数。∎

### 命题 7.3（端点与互不混合单脉冲的边界）

固定 $H(g,J)$ 的全部端点修正
$R_2P_Ve^{-itH/\hbar}|_VR_1$ 仍由 $V\oplus\mathbb Cb_g$ 实现。
即使加入中途 $R\oplus I_Q$，固定暗线 $\mathbb Cz_g$ 仍不激活。
若只允许分别选择单个 $H_a$ 脉冲、不允许混合词，多种相位不强制七维共同实现。

**证明。** 固定暗线被 $H$ 湮灭且被所述扩张保持，端点修正只改变可见输入输出。
对互不混合的单脉冲族，将每个模型自己的 $b_{g_a}$ 识别为同一个抽象隐藏基向量，
在共同六维空间分别定义各 $H'_a$，即可逐个保持原压缩振幅。
该构造不保持不同隐藏亮向量间的真实内积；这些内积由混合词的 Gram 块检验，
因此不与定理 7.2 冲突。∎

### 命题 7.4（相位解锁的弱通道）

对两种耦合，令 $r_a=|g_a|$、$\alpha=\arg(g_1/g_0)$、
$\Delta_1=\sqrt{J_1^2+16r_1^2}$、$\eta_1=4r_1/\Delta_1$、
$\tau_1=\Delta_1t/(2\hbar)$。则

$$
\|P_Ve^{-itH_1/\hbar}z_{g_0}\|^2
=\eta_1^2\sin^2\tau_1\sin^2\alpha. \tag{7.2}
$$

两个隐藏一阶振幅通道在共同二维 $Q$ 上的 Gram 算子最小特征值为

$$
\lambda_-={2\over\hbar^2}\left(r_0^2+r_1^2-
\sqrt{(r_0^2-r_1^2)^2+4r_0^2r_1^2\cos^2\alpha}\right), \tag{7.3}
$$

固定 $r_0,r_1>0$ 且 $\sin\alpha\to0$ 时，

$$
\lambda_-\sim{4r_0^2r_1^2\sin^2\alpha\over\hbar^2(r_0^2+r_1^2)}.
$$

**证明。** $|\langle b_{g_1},z_{g_0}\rangle|=|\sin\alpha|$，
只有这一亮分量经 $\{e_4,b_{g_1}\}$ 的二能级块进入 $V$。
该块去掉标量 $J_1/2$ 后平方为 $(\Delta_1^2/4)I$，
其转移概率为 $\eta_1^2\sin^2\tau_1$，得 (7.2)。
一阶通道 Gram 算子为

$$
{4\over\hbar^2}\left(r_0^2|b_{g_0}\rangle\langle b_{g_0}|
+r_1^2|b_{g_1}\rangle\langle b_{g_1}|\right).
$$

其迹为 $4(r_0^2+r_1^2)/\hbar^2$，行列式为
$16r_0^2r_1^2\sin^2\alpha/\hbar^4$，给 (7.3)。
将根号写成 $\sqrt{(r_0^2+r_1^2)^2-4r_0^2r_1^2\sin^2\alpha}$ 并展开得渐近式。
所以精确秩跃迁不带来相位近共线时的均匀稳定性。
把 $z_{g_0}$ 用作试验输入仍须另给制备权限；振幅实现维数不是记忆位数。∎

## 8. 同一原命令的任意单调径向截断

### 定义 8.1（固定模型、完整寿命与源规约）

严格采用[奇异占用卷，定义 1.1–1.3](FIB_NATIVE_SINGULAR_OCCUPATION_AND_COMMAND_CAP_LIMITS.md#1-the-fixed-full-model-and-the-observations)
及[变系数 Green 卷，定义 29.1–29.2](FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md)
的双壁模型和附加执行能力。
取 $0<Z<1$、$r=1-Z$、$X=Y=r/2$、$(l,u)\Subset(0,r/2)$，令

$$
\Omega=(l,u)\times(\mathbb R/2\pi\mathbb Z)^2,\quad
X_1=\partial_k,\quad
X_2=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta.
$$

密度 $\rho>0$ 和实对称正定矩阵 $\mathsf A$ 在闭柱邻域光滑，固定任意内点源 $o$，
两高度壁杀死。原自由形式及其闭包域为

$$
\begin{gathered}
d\mu=\rho\,dk\,d\alpha\,d\beta,\qquad
\mathfrak t[f]=\int_\Omega\sum_{i,j=1}^2a^{ij}(X_jf)\overline{X_if}\,d\mu,\\
\mathcal F_{\mathsf A}=
\overline{C_c^\infty(\Omega)}^{\,\|\cdot\|_2^2+\mathfrak t},\qquad
d^j=\rho^{-1}\sum_iX_i(\rho a^{ij}).
\end{gathered}
$$

$L_{\mathsf A}$ 为此闭形式的非负自伴生成子。
$\Gamma=\int_0^\infty p_t^\Omega(o,\cdot)\,dt$ 为同一时钟 $e^{-tL_{\mathsf A}}$
和未归一化测度的完整 Green 场；不加吸引漂移、存活重权或 ground conditioning。
原随机命令取

$$
\delta_n=n^{-2},\quad e_n=n^{-1},\quad m_n=n^3,\quad
v_i=\delta_nd(q_i)+\sqrt{2\delta_n}\,\mathsf A(q_i)^{1/2}\xi_i,
$$

$\xi_i\in\{-1,+1\}^2$ 的两坐标及不同 $i$ 相互独立、各符号等概率。
单元内恒速执行原控制。
相对原控制坐标的每个前缀严格为

$$
(a,b,j)=\left(a_i+\theta v_i^1,\ b_i+\theta v_i^2,
j_i+\theta a_iv_i^2+\tfrac12\theta^2v_i^1v_i^2\right),\qquad0\le\theta\le1.
\tag{8.1}
$$

保留 chronological area 的半乘积项、所有原生守卫及回返；在第一次碰壁处切断。
若活到 $m_n\delta_n=n$，保留原终端高度段，在最后长度 $\delta_n$ 的区间内到上壁。
独立符号、系数及漂移导数求值、规定控制执行均为声明的生产者能力。
记实际首次碰壁时刻为 $\zeta_n$、原插值为 $\bar q_n$，不积分死亡后的保持段，定义

$$
\nu_n(W)=\mathbb E\int_0^{\zeta_n}W(\bar q_n(t))\,dt,\qquad
\nu(W)=\int_\Omega\Gamma W\,d\mu.
$$

源的单射相位图中取

$$
\begin{gathered}
x=k-k_o,\quad y=2(\alpha-\alpha_o),\quad
z=-r\{\beta-\beta_o-(\tfrac12-k_o/r)y\},\quad B=\mathsf A(o)^{-1/2},\\
(\xi,\eta)^{\mathsf T}=B(x,y)^{\mathsf T},\quad
\upsilon=\det(B)(z-xy/2),\quad
R=((\xi^2+\eta^2)^2+16\upsilon^2)^{1/4},\\
m_0=\rho(o)\det\mathsf A(o)/(2r),\qquad c_G=(2\pi m_0)^{-1}.
\end{gathered} \tag{8.2}
$$

这是局部规约，不改变实际相位环。
所引源展开给方向一致的 $\Gamma=c_GR^{-2}(1+O(R))$，
局部体积的径向部分与 $R^3dR$ 可比，齐次体积维数为四。
Green 卷定理 29.6 给完整寿命控制及每个闭柱连续测试的 $\nu_n(f)\to\nu(f)$。
奇异占用卷定理 9.3 给：对该任意固定模型，有 $C,r_0,n_0>0$，

$$
\nu_n(B_\epsilon)\le C(\epsilon^2+e_n\epsilon),
\quad B_\epsilon=\{R\le\epsilon\},\quad
0<\epsilon\le r_0,\quad n\ge n_0. \tag{8.3}
$$

它包括所有回返、壁切单元及原终端段。
常数依赖固定模型，不对全模型类作统一断言。
这是后续一般剖面论证的输入，不要求有限符号链有连续转移密度。

### 定义 8.2（可积径向观测）

设 $w:(0,r_0]\to[0,\infty)$ 连续，随半径增加不增，正半径处有限，且

$$
\int_0^{r_0}r w(r)\,dr<\infty.
$$

令非负 $W$ 在某源邻域等于 $w(R)$，穿孔域连续，并在每个源球补集上有界，
包括靠近两壁的部分。源点取单侧极限，允许无穷。
缩小 $r_0$ 使上述等式成立，定义

$$
v_M(r)=\min(M,w(r)),\qquad H_w(M)=\int_0^{r_0}v_M(r)\,dr.
$$

### 定理 8.3（完整期望占用的一般径向充要条件）

对任意确定性有限正数列 $M_n\to\infty$，
$J=\nu(W)<\infty$，且在定义 8.1 的同一原命令上，

$$
\boxed{\nu_n(W\wedge M_n)\longrightarrow J
\quad\Longleftrightarrow\quad e_nH_w(M_n)\longrightarrow0.} \tag{8.4}
$$

不要求 $M_n$ 单调，也不要求 $w(cr)\asymp w(r)$。
条件成立时，每个固定 $h\in C(\overline\Omega;\mathbb C)$ 满足

$$
\nu_n(h(W\wedge M_n))\longrightarrow\nu(hW).
$$

**证明。** 源展开及径向体积使源附近 $\nu(W)$ 与
$\int_0^{r_0}rw(r)\,dr$ 可比；源外有界且 $\nu(1)<\infty$，故 $J<\infty$。
对固定 $K$，$W\wedge K$ 在源点连续。
若它不连续延拓到壁，先乘高度内截断 $\theta_\eta\in[0,1]$。
固定 $\theta_\eta(W\wedge K)$ 为闭柱连续测试，收敛输入适用。
壁层误差至多 $K\nu_n(1-\theta_\eta)$；先取 $n\to\infty$，
再令 $\eta\downarrow0$，利用完整有限寿命及支配收敛，得到固定截断收敛。

令 $F_n(t)=\nu_n(0<R\le t)$。由 (8.3)，$F_n(t)\le C(t^2+e_nt)$；
同一界令 $t\downarrow0$ 还给大 $n$ 时 $\nu_n(\{o\})=0$。
连续非增 $v_M$ 的 Stieltjes 分部积分给

$$
\begin{aligned}
\nu_n(v_M(R)\mathbf1_{R\le\epsilon})
&=v_M(\epsilon)F_n(\epsilon)
 +\int_{(0,\epsilon]}F_n(t)(-dv_M(t))\\
&\le2C\int_0^\epsilon t v_M(t)\,dt
 +Ce_n\int_0^\epsilon v_M(t)\,dt\\
&\le2C\int_0^\epsilon tw(t)\,dt+Ce_nH_w(M).
\end{aligned} \tag{8.5}
$$

有限 $M$ 保证零端边界项消失；将 $t^2$、$t$ 的分部积分分别展开即可得到系数二、一。
若 $e_nH_w(M_n)\to0$，对固定小 $\epsilon$ 取
$K\ge\sup_{\Omega\setminus B_\epsilon}W$。
充分大 $n$ 时 $M_n\ge K$，两个截断之差仅在源球。
(8.5) 及固定截断收敛给上极限至多
$J+2C\int_0^\epsilon tw(t)dt$，令 $\epsilon\downarrow0$ 得上界 $J$。
对每个固定 $K$ 的单调下界给下极限至少 $J$。
带 $h$ 的结论将尾界乘 $\|h\|_\infty$，对固定截断用同样壁层论证即可。

为证必要性，记首单元贡献

$$
I_n=\mathbb E\int_0^{\delta_n}(W\wedge M_n)(\bar q_n(t))\,dt.
$$

充分大 $n$ 的首单元全部存活且在源图内。
取 $\chi_\epsilon\in[0,1]$，在 $B_\epsilon$ 为零、在 $B_{2\epsilon}$ 外为一，
再取壁内截断 $\theta_\eta$。
$f=\chi_\epsilon\theta_\eta W$ 有界、闭柱连续，大 $n$ 时在首单元为零且 $M_n\ge\|f\|_\infty$。
于是

$$
\nu_n(W\wedge M_n)-I_n\ge\nu_n(f).
$$

先对任意子序列取下极限，再让源、壁截断趋于一，支配收敛给

$$
\liminf_n\bigl(\nu_n(W\wedge M_n)-I_n\bigr)\ge J. \tag{8.6}
$$

所以完整均值若趋于 $J$，必有 $I_n\to0$。
仅由首单元非负且不超过全均值，不能推出这一步。

最后严格使用首单元原插值。源白化后的水平长度为

$$
\ell_{n,\xi}=|\delta_n\mathsf A(o)^{-1/2}d(o)+\sqrt{2\delta_n}\xi|
=2e_n+O(e_n^2),
$$

其中 $|\xi|=\sqrt2$，误差对四种符号一致。
(8.1) 的半乘积使首单元的中心坐标 $\upsilon$ 恰为零，因此
$R(\bar q_n(t))=\ell_{n,\xi}t/\delta_n$ 精确成立。
换元给

$$
I_n=e_n^2\mathbb E_\xi\left[
\ell_{n,\xi}^{-1}\int_0^{\ell_{n,\xi}}v_{M_n}(t)dt\right]. \tag{8.7}
$$

大 $n$ 时 $e_n\le\ell_{n,\xi}\le3e_n$，从而

$$
{e_n\over3}\int_0^{e_n}v_{M_n}(t)dt\le I_n\le e_nH_w(M_n).
$$

另一方面，

$$
e\int_e^{r_0}w(t)dt
=\int_0^{r_0}tw(t){e\over t}\mathbf1_{t\ge e}dt\longrightarrow0
$$

由可积函数 $tw(t)$ 的支配收敛成立。因此
$e_nH_w(M_n)\le3I_n+o(1)$。
首单元贡献趋零恰当于 (8.4) 的右侧，结合 (8.6) 得必要性。∎

### 推论 8.4（方向一致比较与幂次输入）

若源附近只满足 $c\,w(R)\le W\le Cw(R)$，其中 $0<c\le C<\infty$，
其余穿孔连续、源外有界条件保持，则同一充要条件 (8.4) 仍成立。
特别地，[奇异占用卷，定理 8.1、9.4](FIB_NATIVE_SINGULAR_OCCUPATION_AND_COMMAND_CAP_LIMITS.md)
的幂次结论是此处的已知输入特例：$W=\Gamma^p$、$0<p<1$ 时，

$$
\begin{array}{c|c}
0<p<1/2&\text{任意 }M_n\to\infty\text{，也可不截断}\\
p=1/2&\log M_n=o(n)\\
1/2<p<1&M_n=o(n^{2p/(2p-1)}).
\end{array}
$$

$p\ge1$ 时目标无穷，任意 $M_n\to\infty$ 的均值趋于无穷。

**证明。** 对固定 $a>0$，

$$
\min(1,a)\min(M,w)\le\min(M,aw)\le\max(1,a)\min(M,w).
$$

因此 (8.5) 的统一尾估计及 (8.7) 的首单元必要性保持。
若源处的固定截断不连续，可先切除小源球；固定 $K$ 的源球误差由
$K C(\epsilon^2+e_n\epsilon)$ 控制，先 $n\to\infty$ 再 $\epsilon\downarrow0$ 即消失。
其余固定截断和源外扣除论证不变。
对 $w(t)=t^{-2p}$，$H_w$ 分别为有界、与 $\log M$ 同阶、与
$M^{1-1/(2p)}$ 同阶，重现所引幂次输入。
$p<1/2$ 时还可在 (8.5) 直接令 $M\uparrow\infty$ 得未截断收敛。
$p\ge1$ 时，固定截断目标随 $K\uparrow\infty$ 发散，
且大 $n$ 有 $M_n\ge K$，故均值下极限超过任意有限数。∎

## 9. 对数临界帽、原形式域及路径迹边界

### 定理 9.1（对数临界剖面的精确速度与首单元超额）

取 $\beta>1$、$\kappa>0$，缩小 $r_0$ 使 $\log(1/r_0)>\beta/2$，定义

$$
w_\beta(t)=\kappa t^{-2}(\log(1/t))^{-\beta}.
$$

令 $W_\beta=w_\beta(R)$ 于该源邻域，源外作定义 8.2 的非负延拓。
则 $\nu(W_\beta)<\infty$，每个固定原网格的未截断预期占用无穷，而

$$
\boxed{\nu_n(W_\beta\wedge M_n)\to\nu(W_\beta)
\quad\Longleftrightarrow\quad
{M_n\over(\log M_n)^\beta}=o(n^2).} \tag{9.1}
$$

若 $M_n\sim Cn^2(\log n)^\beta$、$C>0$，则首单元贡献趋于 $\sqrt{\kappa C}$，且

$$
\liminf_n\nu_n(W_\beta\wedge M_n)
\ge\nu(W_\beta)+\sqrt{\kappa C}. \tag{9.2}
$$

**证明。** 所选 $r_0$ 保证 $w_\beta$ 随半径增加严格减小。
$\int_0^{r_0}t w_\beta(t)dt=\kappa\int_{\log(1/r_0)}^\infty s^{-\beta}ds<\infty$，
而 $\int_0^{r_0}w_\beta(t)dt=\infty$。
每个固定原网格首单元在源附近是一条线性离源弦；
非零速度给后一发散积分，零速度则在源保持正时间，同样贡献无穷。
源内点及连续性保证存在正的存活初段，故未截断预期占用无穷。

令 $r_M$ 为 $w_\beta(r_M)=M$ 的小根，$L_M=\log(1/r_M)$，则

$$
\log M=\log\kappa+2L_M-\beta\log L_M,\qquad L_M\sim\tfrac12\log M,
$$

$$
r_M\sim2^{\beta/2}\sqrt\kappa M^{-1/2}(\log M)^{-\beta/2}.
$$

分裂 $H$ 并令 $s=\log(1/t)$，得到

$$
\begin{aligned}
H_{w_\beta}(M)
&=Mr_M+\kappa\int_{r_M}^{r_0}t^{-2}(\log(1/t))^{-\beta}dt\\
&=Mr_M+\kappa\int_{\log(1/r_0)}^{L_M}e^ss^{-\beta}ds\\
&\sim2Mr_M\sim
2^{1+\beta/2}\sqrt\kappa\,{\sqrt M\over(\log M)^{\beta/2}}.
\end{aligned} \tag{9.3}
$$

第二项与 $Mr_M$ 等价可用渐近分部积分，或对其与 $e^{L_M}L_M^{-\beta}$ 用洛必达法则。
代入定理 8.3，平方正量即得 (9.1)。
临界帽使 $e_nH_{w_\beta}(M_n)\to2\sqrt{\kappa C}$。
由 (8.7)、$\ell_{n,\xi}/(2e_n)\to1$，并利用
$e_n\int_{e_n}^{r_0}w_\beta\to0$，得
$I_n-\tfrac12e_nH_{w_\beta}(M_n)\to0$。
(8.6) 在此帽下仍给其余占用下极限至少为目标，得 (9.2)。
此下界没有确定后续回返的全部额外量。∎

### 命题 9.2（以完整 Green 场表示的临界观测）

对 $\beta\in\mathbb R$，$W=\Gamma/(\log(e+\Gamma))^\beta$ 的目标
$\nu(W)=\int\Gamma^2/(\log(e+\Gamma))^\beta d\mu$
恰在 $\beta>1$ 有限。
此时对 $M_n=n^a(\log n)^b\to\infty$，收敛条件为
$a<2$，或 $a=2,b<\beta$；$a>2$ 不满足。

**证明。** 源展开给
$W\sim c_G2^{-\beta}R^{-2}(\log(1/R))^{-\beta}$，
源外有界。径向目标积分为常数倍 $\int_0 R^{-1}(\log(1/R))^{-\beta}dR$，
恰在 $\beta>1$ 有限。
对 $a>0$，$\log M_n\sim a\log n$，(9.1) 的比值除以 $n^2$ 与
$n^{a-2}(\log n)^{b-\beta}$ 同阶，得陈述。
$a=0$ 且帽趋无穷时 $b>0$，仅为对数增长，同样满足条件；
$a<0$ 不能使该帽趋无穷。方向一致比较的推论 8.4 将剖面判据传回 $W$。∎

### 定理 9.3（原自由形式域中的临界幅度）

取源附近为一、支撑紧含于源图 $R<r_0$ 的非零光滑径向截断 $\chi$，图外零延拓。
定义

$$
N_\beta^2=\int_\Omega\chi^2R^{-2}(\log(1/R))^{-\beta}d\mu,
\qquad u_\beta=N_\beta^{-1}\chi R^{-1}(\log(1/R))^{-\beta/2},\quad\beta>1.
$$

则 $0<N_\beta<\infty$、$\|u_\beta\|_2=1$、$u_\beta\in\mathcal F_{\mathsf A}$，
且 $\nu(|u_\beta|^2)<\infty$。
其每个原命令的未截断平方幅度占用无穷；截断完整均值收敛恰满足 (9.1)，
其中局部剖面常数为 $\kappa=N_\beta^{-2}$。

**证明。** 平方范数由局部积分
$\int_0^{r_0}t(\log(1/t))^{-\beta}dt$ 控制，且非零，得归一化。
径向幅度导数为

$$
{d\over dt}\bigl(t^{-1}(\log(1/t))^{-\beta/2}\bigr)
=t^{-2}(\log(1/t))^{-\beta/2}
\left(-1+{\beta\over2\log(1/t)}\right).
$$

冻结白化水平场满足 $|\nabla_HR|\le1$；原水平场及光滑正定系数在紧源图上给相应固定比较。
故动能和 Green 加权平方范数均由
$C\int_0^{r_0}t^{-1}(\log(1/t))^{-\beta}dt<\infty$ 控制。

还须证明属于原闭包域。取光滑源切除 $\eta_\epsilon$，在 $R\le\epsilon$ 为零、
在 $R\ge2\epsilon$ 为一，径向导数为 $O(\epsilon^{-1})$。
内区原能量尾为 $O((\log(1/\epsilon))^{1-\beta})$，
新增环带能量为 $O((\log(1/\epsilon))^{-\beta})$，
平方范数尾为 $O(\epsilon^2(\log(1/\epsilon))^{-\beta})$，均趋零。
于是 $\eta_\epsilon u_\beta\in C_c^\infty(\Omega)$ 在原形式范数收敛于 $u_\beta$。
局部 $|u_\beta|^2$ 恰为定理 9.1 的剖面，其余结论直接应用该定理。∎

### 定义 9.4（实际路径迹的既有边界）

对固定网格 $n$，令有限符号历史集合为 $\Xi_n$、概率律为 $\pi_n$，置

$$
\mathcal D_n=\coprod_{\omega\in\Xi_n}\{\omega\}\times[0,\zeta_{n,\omega}),
\qquad d\vartheta_n=\pi_n(\omega)dt.
$$

[原控制稳定卷，定理 8.1](RECURSIVE_RELATIONAL_OBSERVATION_ORIGINAL_CONTROL_INSTRUMENT_STABILITY.md)
供应实际路径限制算子

$$
\mathcal R_n:\mathcal F_{\mathsf A}\supset C_c^\infty(\Omega)
\longrightarrow L^2(\mathcal D_n,\vartheta_n),\qquad
\|\mathcal R_nf\|^2=\nu_n(|f|^2)
$$

不可闭的输入。具体有 $0\le\varphi\le1$ 在源附近为一，
$0<\nu_n(\varphi^2)<\infty$，以及 $u_j\to0$ 于原形式范数，
但 $\mathcal R_nu_j=\mathcal R_n\varphi\ne0$。
该输入包括全部实际分段光滑路径、回返及终端段。

在定理 9.3 的应用中，它排除了从原形式 Hilbert 空间到实际运行时间空间的闭线性延拓：
若延拓存在，其闭图会同时包含 $(u_j,\mathcal R_n\varphi)$ 的极限
$(0,\mathcal R_n\varphi)$，而线性算子在零点只能取零，矛盾。
因此特定固定剖面的完整均值收敛与一般形式范数连续路径读出为不同命题。
一般径向结论只使用同源、同钟、原插值的预期占用，
不推出逐路径收敛、任意随网格变化测试的稳定性或随机总占用的一致可积性。
若观测在首离源方向消失，不存在推论 8.4 的正双边比较，(8.4) 的必要性不随之成立。

## 追加锚（本行以下为增补区）
