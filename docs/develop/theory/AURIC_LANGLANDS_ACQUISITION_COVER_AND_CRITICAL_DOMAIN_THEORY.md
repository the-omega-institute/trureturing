# AURIC–Langlands 取得、覆盖与临界域理论

## 1. 来源、对象与资源合同

**约定 1.1（固定数学输入）。** 下表的项目来源均取提交
`57c4745c00f182a2a5b0fefc30306133b10fc297` 中的
`docs/develop/theory/`，引用号指该快照中的条目。表中的输入陈述在相应应用处展开；它们的证明归原来源。

| 简称 | 来源与所用范围 |
| --- | --- |
| CLOCK | [FIB_LITERAL_CLOCK_CUBIC_MATRIX_POLYNOMIAL_FRAME.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/FIB_LITERAL_CLOCK_CUBIC_MATRIX_POLYNOMIAL_FRAME.md)，定义 7.1、定理 7.2、8.1，§§9–11：字面时钟、环境取得、同源解码及其资源计数 |
| REAL | [FIB_POSITIVE_M_ENTIRE_CHILD_J_OBSTRUCTION.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/FIB_POSITIVE_M_ENTIRE_CHILD_J_OBSTRUCTION.md)，定理 1.1、1.2：整个实际子域的三世界证书 |
| FINITE | [FIB_SINGULAR_RESPONSE_CHILDREN_EXCLUSION.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/FIB_SINGULAR_RESPONSE_CHILDREN_EXCLUSION.md)，§§10–11：有限候选承载、坏因子与终端判别式 |
| CONTEXT | [AURIC_LANGLANDS_CONTEXT_AND_SPECTRAL_RECONSTRUCTION_THEORY.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/AURIC_LANGLANDS_CONTEXT_AND_SPECTRAL_RECONSTRUCTION_THEORY.md)，§6、§§9–11：迹重构、四块稠密性、genus-4 谱系统、中心提升及归一化 |
| STRUCTURE | [AURIC_LANGLANDS_STRUCTURE_ACQUISITION_AND_SPECTRAL_EXTENSION_THEORY.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/AURIC_LANGLANDS_STRUCTURE_ACQUISITION_AND_SPECTRAL_EXTENSION_THEORY.md)，取得、结构态与谱扩张的合同 |
| FUTURE | [FIB_ATOM_ESCAPE_WITNESS_DEPTH_AND_ROBUST_WHITEBOX.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/FIB_ATOM_ESCAPE_WITNESS_DEPTH_AND_ROBUST_WHITEBOX.md)，§§2–3；[FIB_ATOM_WHITEBOX_CERTIFICATE_HORIZON.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/FIB_ATOM_WHITEBOX_CERTIFICATE_HORIZON.md)：未来等价、有限见证与确定性记忆 |
| BAYES | [FIB_ATOM_TASK_INFORMATION_BAYES_RISK_GEOMETRY.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/FIB_ATOM_TASK_INFORMATION_BAYES_RISK_GEOMETRY.md)，定理 5：二元后验风险与信息增益 |
| KRYLOV | [FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_X.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/FIB_ATOM_RECURSIVE_HOLOGRAPHIC_BOUNDARY_GEOMETRY_CONTINUATION_X.md)，§§264–265：压缩缺陷、全未来核及不变闭包 |
| OMEGA | [AURIC_OMEGA_BOSONIC_EXCURSION_RETURN_AND_PHASE_CORRECTION.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/AURIC_OMEGA_BOSONIC_EXCURSION_RETURN_AND_PHASE_CORRECTION.md)，§§1–2、7–8：Fock 嵌入、亮暗模态、返回与权限 |
| GREEN | [FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/FIB_NATIVE_VARIABLE_COEFFICIENT_GREEN_STABILITY.md)，定理 10.2、11.1、12.2、13.1、29.6 与边界 29.7：单位源、临界完成与原命令占用 |

**定义 1.2（模型合同）。** 一个取得问题指定四元组
$\mathfrak C=(\mathsf X,\mathsf P,\mathsf O,\mathsf R)$。
$\mathsf X$ 是完整来源及其持久状态，$\mathsf P$ 是合法操作、组合规则和时钟，
$\mathsf O$ 是每一步实际保留的报告，$\mathsf R$ 指定精度、参考、控制、存储与随机性资源。
两个来源未来等价，是指对所有共同合法的未来操作词，其指定报告相同；若操作资格本身可见，资格也属于报告。
一个确定性充分编码必须在每个编码纤维上使全部这些未来报告不变。

仿射参数维数、有限覆盖次数、线性自治实现维数及信息成本分别在各自合同内定义。
有限 étale 基变换是数学操作；它不自动属于 $\mathsf P$。
复候选评价只有通过完整实逆构造及实际守卫，才表示 $\mathsf X$ 中的来源。

**约定 1.3（推导归属）。** 本卷的组合命题是在上述项目输入与文中具名经典结果上的普通数学推导，记作 `repo-derived`；经典中间步骤记作 `literature-attested`。
这些标记区分引用与推导，不提出历史首创性主张。
用户《AURIC–Langlands 取得、覆盖与临界域理论》第四稿供应了各章的模型及组合目标；下列量词、守卫和资源假设为各命题的组成部分。

## 2. 字面取得、自适应下界与归一化

**定义 2.1（实际来源与扩大环境）。** 令

$$
J=\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
M=\begin{pmatrix}0&1\\1&1\end{pmatrix},\qquad
P(r,b)=\begin{pmatrix}r&b\\r(1-r)/b&1-r\end{pmatrix},
\quad 0<r<1,\ b>0.
$$

$P$ 逐项严格正、迹为一、行列式为零；不要求 Hermitian。
实际世界是 $(P,g,d)$，其中 $0\ne g\in\mathbb R[t]$、$\deg g\le3$，且 $d\in\mathbb R$ 在全历史中固定。
每执行一个 $J$ 或 $M$，绝对时钟增加一，立即保留
$y_t=d+g(t)\operatorname{tr}(Q_tP)$，累乘矩阵按左乘更新。
不另给复位、复制、未读门、物理逆门或空词时钟推进。

扩大环境采用独立实系数

$$
Z(s)=\sum_{h=0}^kZ_hs^h,\qquad
D(s)=\sum_{h=0}^{\delta}d_hs^h,\qquad
Y_i=D(i)+\operatorname{tr}(A_iZ(i)),\qquad
N=4k+\delta+5.
$$

这里不施加秩、正性或同源约束。CLOCK 定义 7.1 与定理 7.2、8.1 供应如下输入：
时间词 $M^{2k+\delta+2}JM^{2k+1}$ 使用 $N-1$ 个新原子，连同当前读数共 $N$ 个标量，线性恢复全部环境系数。
在漂移系数在前、每阶矩阵按 $(11,12,21,22)$ 排列的列序下，观测矩阵满足

$$
\det C_{k,\delta}
=5^{k(k+1)}\left(\prod_{h=0}^kh!\right)^4
\left(\prod_{h=0}^{\delta}h!\right)>0.
$$

这个输入的解码结构也固定如下。置 $q=k+1$、$a=\delta+1$、$s=2q+a$、$m=s-1$，则

$$
A_i=M^i\ (0\le i\le m),\qquad
A_{s+j}=M^jJM^m\ (0\le j<2q).
$$

令 $\lambda=(1+\sqrt5)/2$、$\mu=(1-\sqrt5)/2$、
$S=\left(\begin{smallmatrix}1&1\\\lambda&\mu\end{smallmatrix}\right)$、$K=S^{-1}JS$，则 $K_{12}K_{21}=1/5$。
写 $S^{-1}Z(t)S=\left(\begin{smallmatrix}u(t)&b(t)\\c(t)&e(t)\end{smallmatrix}\right)$。
第一段的 $\lambda^iu(i)+\mu^ie(i)+D(i)$ 由节点重数 $(\lambda:q,\mu:q,1:a)$ 的合流 Vandermonde 逆恢复 $u,e,D$；
第二段扣除这些已知项后为 $\lambda^jF(j)+\mu^jG(j)$，其中

$$
F(t)=\mu^mK_{12}c(s+t),\qquad
G(t)=\lambda^mK_{21}b(s+t).
$$

非零缩放和逆平移恢复余下两项。所用合流行列式为

$$
\prod_b\left[x_b^{n_b(n_b-1)/2}\prod_{h=0}^{n_b-1}h!\right]
\prod_{b<c}(x_c-x_b)^{n_bn_c}.
$$

中间分组 $([u],[e],[D],[c],[b])$ 与普通列序各贡献 $(-1)^q$，因而得到上述正行列式。
这些公式属于 CLOCK 的既有取得输入。

**命题 2.2（扩大环境中的自适应精确下界）。** 设 $\Theta$ 是一个实 $d$ 维仿射空间的非空相对开子集。
一个确定性策略每次根据已有完整记录选择一个实仿射查询，并可根据记录停止。
若该策略精确恢复每个 $\theta\in\Theta$，则每个终止分支至少含 $d$ 次新查询。
因而定义 2.1 的整个环境在已有当前独立等式 $Y_0$ 后，至少需要 $N-1$ 次新查询；CLOCK 的时间词在这个扩大环境及仿射查询合同中达到下界。

证明。采用沿同一实际历史保持不可分辨性的经典自适应下界方法；其有限历史逻辑亦见固定来源提交的
[FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/FIB_SELF_CALIBRATING_RELATION_MATHEMATICS_II.md) 引理 46.2。
固定来源 $\theta$ 的终止分支，假设它只作 $n<d$ 次查询。
沿该分支已选出的仿射函数，其线性部分在仿射方向空间上的公共核含非零 $h$。
相对开性给出非零且足够小的 $t$，使 $\theta+th\in\Theta$。
第一次查询在两点值相同；若前 $j-1$ 次记录相同，策略选择同一第 $j$ 个查询，其线性部分又消去 $h$，故第 $j$ 次记录也相同。
归纳后停止决定和解码输出相同，却有两个不同来源，矛盾。
无需假设策略对报告连续。
已有 $Y_0$ 时，固定该值的切片是 $N-1$ 维仿射空间的相对开集，应用同一论证即可。
原世界的同源性是非线性约束，所以上述证明没有给出其十七读数最优性。$\square$

**定义 2.3（已知前缀与原世界守卫）。** 已知绝对时钟 $t_0$ 和合法前缀的可逆累乘 $Q_0$ 时，原世界嵌入环境为
$Z(s)=Q_0g(t_0+s)P$、$D(s)=d$。
CLOCK §9 供应解码：令

$$
B_h=Q_0^{-1}Z_h,\qquad h_h=\operatorname{tr}B_h.
$$

取任意 $h_a\ne0$，则

$$
P=B_a/h_a,\qquad g(t)=\sum_hh_h(t-t_0)^h.
$$

这里 $Q_0^{-1}$ 仅在数学解码中使用。
原世界守卫要求所有 $B_h=h_hP$、$P$ 满足定义 2.1 的严格正性与秩迹条件、漂移确为常数、$g\ne0$，并满足所有已得历史等式。
环境恢复本身不免除这些守卫。
若绝对时钟未知，则 $(t_0,g)$ 的平移规范尚存，只恢复局部多项式 $s\mapsto g(t_0+s)$。
特别地，三次增益、常漂移使用 $M^8JM^7$，即十六个新门、十七个读数；从已知时钟六延续至二十二，并检查原七历史等式。

**命题 2.4（迹归一化的局部稳定性及其尺度边界）。** 设 $B=hP$、$\operatorname{tr}P=1$、$|h|\ge a>0$，
$\widehat B=B+E$、$\|E\|_F\le\eta$ 且 $\sqrt2\eta\le a/2$。
则 $\operatorname{tr}\widehat B\ne0$，并且

$$
\widehat P=\frac{\widehat B}{\operatorname{tr}\widehat B},\qquad
\|\widehat P-P\|_F
\le\frac{2\eta}{a}\bigl(1+\sqrt2\|P\|_F\bigr).
$$

在没有增益尺度下界的完整来源族中，对固定有限合法观测词的逆映射不存在统一连续模。
该结论包括尚未固定为特定数值的七历史来源族，不断言固定七个给定报告的纤维具有同一反例。

证明。$|\operatorname{tr}E|\le\sqrt2\|E\|_F$，故分母绝对值至少 $a/2$。直接相减得

$$
\widehat P-P=\frac{E-P\operatorname{tr}E}{h+\operatorname{tr}E},
$$

从而得到估计。若误差来自取得矩阵及前缀解码，$\eta$ 须包含 $C_{k,\delta}^{-1}$ 和 $Q_0^{-1}$ 的放大。
反例取两个不同且固定的合法 $P_1,P_2$、同一 $d$ 和非零 $g_0$，令 $g_\varepsilon=\varepsilon g_0$，$\varepsilon>0$。
同一有限观测词下每个报告之差都为
$\varepsilon g_0(t)\operatorname{tr}(Q_t(P_1-P_2))$，故整段记录之差趋于零，而 $\|P_1-P_2\|_F$ 固定为正。
每个 $g_\varepsilon$ 都非零；失稳发生在尺度归一化，并不否定固定环境线性逆的连续性。$\square$

## 3. 整个实际子域的稳健标签

**定义 3.1（三世界输入及其来源域）。** 设七历史的操作词为 $J,M,J,M,M,M$，读数为
$(0,24,147/5,24,18,p,v)$。全部有限小数均按有理数解释，令

$$
p_c=7.27697979572462,\qquad v_c=61.48668743716016,\qquad
\mathcal Q=[p_c-10^{-10},p_c+10^{-10}]
\times[v_c-10^{-10},v_c+10^{-10}].
$$

REAL 定理 1.1、1.2 的输入是：每个 $(p,v)\in\mathcal Q$ 的整个实际子域恰有三个完整世界，按来源宽度递增标为 $W_1,W_2,W_3$，其终端 $J$ 报告 $a$ 满足

$$
\begin{aligned}
a(W_1)&\in(220.965,220.971),\\
a(W_2)&\in(315.408,315.725),\\
a(W_3)&\in(311.432,311.632).
\end{aligned}
$$

$J$ 在每个整个子域上单射；$M$ 碰撞只能发生于 $W_2,W_3$，且矩形内部存在真实局部碰撞分支。
这份完整性输入来自次数十八的宽度多项式、线性 subresultant 及统一有理区间的全正宽度证书；该宽度多项式与第 4 节的十八层承载不是同一多项式的无条件识别。

**命题 3.2（统一阈值与固定参数的三态充分性）。** 对同一世界的终端 $J$ 数值报告 $\widehat a$，若
$|\widehat a-a|<1.888$，则阈值 $266.2015$、$313.52$ 将三个世界按从低到高的次序 $W_1,W_3,W_2$ 正确分类。
对每个固定且已知的 $(p,v)\in\mathcal Q$，在当前时刻把完整世界编码为标签、并以完整未来词为解码器输入的确定性充分编码，恰需三个状态。

证明。两道间隙的中点分别是

$$
\frac{220.971+311.432}{2}=266.2015,\qquad
\frac{311.632+315.408}{2}=313.52.
$$

最小半间隙为 $(315.408-311.632)/2=1.888$；严格误差界保持分类。
终端 $J$ 已区分任意两个世界，故未来等价的编码不能合并它们。
反向地，固定 $(p,v)$ 后，三个标签各指定一个完整 $(P,g,d)$，给定未来词便确定每次累乘与时钟，因而确定全部未来报告，三态足够。
这里的编码是从当前时刻对完整未来词的预测编码，不把累积时钟或任意长动作历史压成三态。
整个连续矩形也未被断言为三态来源空间。$\square$

**推论 3.3（本矩形的双碰撞排除范围）。** $\mathcal Q$ 中没有由不同世界组成的终端 $J$ 碰撞对，因而没有同时要求独立 $J$、$M$ 碰撞对的整个子域。

证明。直接使用定义 3.1 的全子域单射性。其他参数处已有的 $r_0=2/5$ 来源及其碰撞结论不属于本矩形的三世界标签；本推论不给出矩形外的全域双碰撞排除。$\square$

## 4. 候选连接、评价与最小选层

**定义 4.1（良好复基底）。** 从 FINITE §§10–11 的候选代数及终端元素 $M_R$ 出发，局部化到

$$
B=D(\Delta)\subset\mathbb A^2_{\mathbb C},\qquad
R=\mathbb C[p,v,\Delta^{-1}],\qquad
\mathcal A=R[z]/(Q),\quad z=M_R,\quad \deg Q=18,
$$

其中 $Q$ 首一，$\operatorname{disc}Q\in R^\times$。
$\Delta$ 包含 $p-24$、全部系数分母、FINITE 的坏因子 $B_{\rm bad}$、$\delta_M=P_M/T_M$ 的分母 $T_M$ 及原始元判别式分子 $P_M$；冗余因子允许保留。
于是 $\mathcal A/R$ 有限 étale 且 $1,z,\ldots,z^{17}$ 为基。
真实 $M$ 碰撞使该生成元的评价不再互异，故不在这一个良好层中；异常层须另行分层或换生成元。
一个复几何点只有通过定义 2.3 及完整逆构造的严格实守卫，才带实际来源解释。

**命题 4.2（连接与迹重构的运输）。** 对 $i=p,v$，基底导子 $\partial_i$ 唯一延拓为 $\mathcal A$ 上的导子

$$
\nabla_i z=-Q_i(z)Q'_z(z)^{-1}.
$$

这两个延拓交换，保持单位、乘法、迹与迹配对。
设移动幂基为 $e_j=z^j$，写
$\nabla_i e_j=\sum_k(C_i)_{kj}e_k$，并置

$$
G_{jk}=\operatorname{Tr}_{\mathcal A/R}(e_je_k),\qquad
b_j=\operatorname{Tr}_{\mathcal A/R}(ae_j),\qquad a=\sum_jc_je_j.
$$

则 CONTEXT 定理 6.2 的重构 $Gc=b$ 具有运输公式

$$
\partial_iG=C_i^{\mathsf T}G+GC_i,\qquad
\partial_ic+C_ic=G^{-1}(\partial_ib-C_i^{\mathsf T}b).
$$

证明。有限 étale 的唯一无穷小提升性质由 Stacks 00UP 的 formally étale 接口给出。
在当前表示中也可直接使用 Bezout：判别式可逆使 $Q'_z(z)$ 可逆，对 $Q(z)=0$ 求导唯一强制所示公式。
链式法则使这个多项式环导子保持理想 $(Q)$，因此下降至商环。
交换子 $[\nabla_p,\nabla_v]$ 是在 $R$ 上为零的导子，作用于 $Q(z)$ 得
$Q'_z(z)[\nabla_p,\nabla_v]z=0$，故交换子为零。

对乘法矩阵 $m_a$，导子法则在移动基中给出

$$
m_{\nabla_i a}=\partial_im_a+[C_i,m_a].
$$

取矩阵迹，交换子的迹为零，故
$\partial_i\operatorname{Tr}(a)=\operatorname{Tr}(\nabla_i a)$。
再用于 $e_je_k$ 即得 $\partial_iG$ 的公式。
$G$ 非退化是有限 étale 的迹配对性质，亦见 CONTEXT 定理 6.2；对 $Gc=b$ 求导并整理即可得到第二式。$\square$

**命题 4.3（水平原始元的限制）。** 在定义 4.1 的连通基底上，若全局原始元 $z$ 满足 $\nabla_pz=\nabla_vz=0$，则 $Q\in\mathbb C[T]$ 有互异常数根，且 $\mathcal A\simeq R^{18}$。
因而非平凡候选单值排除全局原始读数水平。

证明。迹的水平性给出全部 $\partial_i\operatorname{Tr}(z^j)=0$。
$R$ 中同时被 $\partial_p,\partial_v$ 消去的元素为复常数，Newton 恒等式于是使特征多项式的系数为常数。
因 $z$ 是秩十八代数的原始元，其特征多项式就是首一关系式 $Q$。
判别式非零，复数域上它分解成互异一次因子；中国剩余定理给出 $R^{18}$。
该分裂代数的各图层不发生非平凡单值。$\square$

**命题 4.4（候选评价及其选层承载）。** 对定义 4.1 的良好候选代数的任意特征零域纤维或泛纤维，写作
$\mathcal A=k[z]/(Q)$。给定 $k$-代数评价 $\chi:\mathcal A\to L$ 到域扩张 $L$，
候选选择可由相对迹表达，但它需要 $L$ 上的单个根 $t=\chi(z)$。
具体地，在多项式环 $L[T]$ 中定义

$$
q_t(T)=Q(T)/(T-t),\qquad
e_t=q_t(z)/Q'(t)\in\mathcal A\otimes_kL.
$$

则 $e_t^2=e_t$、$\operatorname{Tr}_{\mathcal A\otimes L/L}(e_t)=1$，且

$$
\chi(a)=\operatorname{Tr}_{\mathcal A\otimes L/L}((a\otimes1)e_t).
$$

证明。使用经典 Lagrange 插值的坐标幂等元作为此候选应用的中间步骤。
$Q'(t)\ne0$。再扩张到分裂域后，$e_t$ 在根 $t$ 处值为一，在其他根处值为零；所以平方、迹及评价公式逐坐标成立，再由忠实域扩张下降。
这里的除法先在 $L[T]$ 中完成；商环中的 $z-t$ 是零因子，不可用它作除法。
未指定 $t$ 的全候选迹只作坐标求和；对图层置换不变，不能自行产生实际标签。$\square$

**命题 4.5（候选曲线上的水平选择与轨道次数）。** 将定义 4.1 的整个候选覆盖拉回到任意光滑连通复曲线 $X$，记所得有限 étale 覆盖为 $\pi:C\to X$，纤维为有限集合 $\Omega$，
$\Gamma=\pi_1(X,x)$ 作用于 $\Omega$。
局部常值代数 $\pi_*\mathbb C_C$ 的纤维是 $\mathbb C^\Omega$。
覆盖截面、$\Gamma$-固定点、水平含幺代数评价到常值 $\mathbb C_X$、水平迹一幂等元相互对应。
连通次数大于一的覆盖没有这种全局选择。

固定 $\omega\in\Omega$、轨道大小 $m=[\Gamma:\Gamma_\omega]$。
一个带基点连通有限 étale 覆盖 $X'\to X$ 对应有限指数子群 $H\le\Gamma$；其拉回有通过指定 $\omega$ 的截面，当且仅当 $H\le\Gamma_\omega$。
此时

$$
\deg(X'/X)=[\Gamma:H]
=m[\Gamma_\omega:H].
$$

若只要求截面落在这个轨道而不指定锚点，条件改为 $H\le\Gamma_{\omega'}$，其中 $\omega'$ 是该轨道中的某一点。
最小选择次数为 $m$，并整除所有这样的连通选择次数；总候选秩十八不强制 $m=18$。

证明。使用 Stacks 0BND 的有限 étale 覆盖与有限基本群集合的等价，复解析情形取通常拓扑单值。
纤维 $\mathbb C^\Omega$ 的含幺代数评价恰是坐标评价，迹一幂等元恰是单个坐标的指示函数；水平条件都等价于该坐标被单值固定。
拉回把作用限制到 $H$，故得到固定点条件及指数乘法公式。
取 $H=\Gamma_\omega$，相应轨道分支本身达到次数 $m$。
连通覆盖的作用传递，次数大于一时无固定点。
归一化迹 $a\mapsto |\Omega|^{-1}\operatorname{Tr}(a)$ 虽水平含幺，但若 $|\Omega|>1$，对一个坐标幂等元的值为 $1/|\Omega|$，不保持平方，故不是代数评价。$\square$

**命题 4.6（候选轨道可执行时的确定性记忆）。** 对命题 4.5 的一个 $m$ 点候选轨道，另加以下控制合同：有限动作字母表的每个动作都置换该轨道，所生成群传递，所有正向词均合法；固定公开参考 $\omega_*$ 不随来源共同输运，报告为 $h=1_{\{\omega_*\}}$。
则任意不同状态都能由长度至多 $m-1$ 的正向词区分；全未来等价恰有 $m$ 类。
精确确定性记忆恰需 $m$ 态，即至少 $\lceil\log_2m\rceil$ 位；要求所有未来报告误差严格小于 $1/2$ 时，下界相同。

证明。有限置换的逆是其正幂，故正向可达关系与群轨道相同。
从 $\omega$ 到 $\omega_*$ 取最短正向路径，其顶点无重复，长度至多 $m-1$。
对应词为双射，不会同时把 $\omega'\ne\omega$ 送到 $\omega_*$，故二者报告分别为一和零。
相同记忆值的解码器不能同时正确给出这两个值，也不能同时逼近到严格 $1/2$ 以内。
存储当前状态标签并按动作置换更新达到 $m$ 态。
这是 FUTURE 的未来等价原则在此可执行合同下的应用，长度界不主张最优。
仅有数学单值表示时，动作可执行性和固定参考尚未给出，不能直接套用该记忆结论。$\square$

**命题 4.7（候选乘法与谱态射的相容边界）。** 一个非平凡候选置换轨道的全部含幺函数代数结构，不能由连通代数群的非平凡代数作用保持。
因而把有限候选乘法加入谱表示合同，必须另证相容性。
另一方面，若 $\rho:\pi_1(X)\to G$，$H$ 为其 Zariski 闭包，$V,W$ 为有限维代数 $G$-表示，则

$$
\operatorname{Hom}_{\rm local}(E_V,E_W)
=\operatorname{Hom}_H(V,W)\supseteq\operatorname{Hom}_G(V,W).
$$

$H=G$ 是等号的充分条件。

证明。经典有限代数事实在本应用中给出
$\operatorname{Aut}_{\mathbb C\text{-alg}}(\mathbb C^m)=S_m$：本原幂等元是单点指示函数，代数自同构恰好置换它们。
连通代数群到有限离散代数群的代数同态像连通，故只含单位元。
局部系统态射恰是与全部单值交换的线性映射；这个交换条件是 Zariski 闭条件，故等价于 $H$-等变。
这也是 Deligne–Milne《Tannakian Categories》§2 的表示纤维函子接口。
这些事实没有把有限候选乘法识别为 $\operatorname{SO}_5$ 的表示态射：一个保持整个有限函数代数结构的稠密连通作用只能平凡，而一般候选单值是有限置换作用。$\square$

## 5. 自适应信息预算与风险

**定义 5.1（报告前计费的自适应实验）。** 令来源 $S$、初始历史 $H_0$、动作 $A_t$、报告 $R_t$ 均有限值，
$H_t=(H_{t-1},A_t,R_t)$。
动作策略满足 $A_t\perp S\mid H_{t-1}$。
每步成本为报告出现前已确定的非负函数 $c_t=c_t(H_{t-1},A_t)$，$C=\sum_{t=1}^Nc_t$。
停止决定作为动作的一部分；有界停止后用零成本常报告补齐到 $N$。
所有可见资格、拒绝或成本信号都计入动作及报告，不能在 $H_t$ 之外泄漏来源信息。
任务 $U=f(S)$ 的每个正概率历史动作对满足，以自然对数计，

$$
I(U;R_t\mid H_{t-1}=h,A_t=a)\le\kappa c_t(h,a),
\qquad 0<\kappa<\infty.
$$

若成本本身随机，则对应假设须改为右侧 $\kappa\mathbb E[c_t\mid h,a]$，并把可见成本的来源信息纳入报告。

**命题 5.2（条件信息的总成本界）。** 在定义 5.1 下，

$$
I(U;H_N\mid H_0)\le\kappa\mathbb E C.
$$

若 $Y=f(S)$ 为二元任务，$\eta_j=\mathbb P(Y=1\mid H_j)$，
$e_j=\mathbb E\min(\eta_j,1-\eta_j)$，则

$$
0\le\Delta e=e_0-e_N,
\qquad \mathbb E C\ge\frac{2(\Delta e)^2}{\kappa}.
$$

证明。链式法则把总信息分解为各步
$I(U;A_t\mid H_{t-1})+I(U;R_t\mid H_{t-1},A_t)$。
前项由动作条件独立性为零；后项按历史动作分布平均，再求和即得总成本界。
二元部分应用 BAYES 定理 5 于嵌套历史 $H_0\subset H_N$。
其相关不等式为

$$
0\le\Delta e\le\mathbb E|\eta_N-\eta_0|,\qquad
I(Y;H_N\mid H_0)
=\mathbb E D_{\rm KL}({\rm Ber}(\eta_N)\Vert{\rm Ber}(\eta_0))
\ge2(\Delta e)^2.
$$

其中风险单调性来自 $\min(p,1-p)$ 的凹性与后验鞅；差值界来自该函数的一阶 Lipschitz 常数一。
自然对数的二元 Pinsker 常数二可由固定 $q\in(0,1)$ 后，对
$D_{\rm KL}({\rm Ber}(p)\Vert{\rm Ber}(q))-2(p-q)^2$ 求二阶导得到
$1/[p(1-p)]-4\ge0$，并用 $p=q$ 时值与一阶导均为零；端点由极限解释。
Jensen 再给出所示期望平方界。这些是该应用中 BAYES 已有风险几何的具体对应。
与第一式组合得到成本结论。$\square$

**命题 5.3（有限实际候选的 Fano 成本）。** 在定义 5.1 中取 $U=S$，设实际来源支撑于 $m\ge2$ 个值。
令 $\widehat S$ 是由 $H_N$ 决定的估计，实际错误率为 $p_e$，二元熵为
$b(p)=-p\log p-(1-p)\log(1-p)$。则

$$
\mathbb E C\ge
\frac{[H(S\mid H_0)-b(p_e)-p_e\log(m-1)]_+}{\kappa}.
$$

只有在 $p_e\le\varepsilon\le1-1/m$ 的区间内，才可直接以 $\varepsilon$ 替换右侧的 $p_e$。

证明。对错误指示变量 $E=1_{\{\widehat S\ne S\}}$，条件熵链式法则及“出错后至多 $m-1$ 个可能值”给出

$$
H(S\mid H_N)\le H(E\mid H_N)+H(S\mid E,H_N)
\le b(p_e)+p_e\log(m-1).
$$

这是经典 Fano 不等式在当前历史上的应用。
以 $I(S;H_N\mid H_0)=H(S\mid H_0)-H(S\mid H_N)$ 代入命题 5.2，并使用成本非负即可。
函数 $b(p)+p\log(m-1)$ 的导数为 $\log((1-p)(m-1)/p)$，只在 $p\le1-1/m$ 保证非负，故得到替换范围。$\square$

**命题 5.4（本地回忆与未记录种子的区别）。** 若每步额外报告还满足 $R_t\perp S\mid(H_{t-1},A_t)$，则所有任务的后验与风险保持不变。
一个最初独立的种子，若未记入历史，不能单凭初始独立性推出这项逐步条件独立。

证明。动作项和报告项都条件独立时，贝叶斯条件分布逐步不变。
反例取独立公平比特 $S,Z$，令 $H_0=S\oplus Z$。初始 $Z\perp S$，但给定 $H_0$ 后 $Z$ 与 $S$ 完全相关；追加报告 $Z$ 便完全恢复 $S$。
所以把相关中间种子称作本地独立随机性不满足定义 5.1 的信息合同。
同理，连续精确实报告可以具有无限互信息；没有额外信道估计时，有限 $\kappa$ 不由连续报告的存在自动成立。$\square$

## 6. 共同底曲线、稠密性与中心提升

**假设 6.1（二通道谱输入）。** 在同一个谱参数下，四块

$$
T(D)=\begin{pmatrix}D&-I_2\\I_2&0\end{pmatrix},\qquad
D\in\{0,E_{11},E_{22},E_{12}+E_{21}\}
$$

可以独立调用、任意重复，且各通道共享同一数学实现。
这是附加的二通道合同，不由原始 $J,M$ 两门权限推出。
CONTEXT 定理 9.2、9.4 供应：四块生成 Zariski 稠密的 $\operatorname{Sp}_4$ 子群；原始外幂
$\Lambda^2_0\mathbb C^4$ 的五维作用给出满射

$$
\varpi:\operatorname{Sp}_4\longrightarrow\operatorname{SO}_5,
\qquad\ker\varpi=\mu_2.
$$

CONTEXT 定义 10.2 与定理 10.4、10.5 另供应一条光滑射影连通复曲线 $X$，$g(X)=4$，其表示为
$\widetilde\rho(a_j)=T(D_j)$、$\widetilde\rho(b_j)=I$，$1\le j\le4$。
曲面关系成立；$\rho=\varpi\widetilde\rho$ 在 $G=\operatorname{SO}_5$ 中稠密，定义无奇点局部系统 $E_X$，并带一个 $\operatorname{Sp}_4$ 提升。
固定到 $E_X$ 的五维识别后，其全部提升类是 $H^1(X,\mu_2)$ 挠集，恰有 $256$ 类；每个提升仍有中心 $\mu_2$ 自同构。

**命题 6.2（共同开曲线与有限覆盖上的稠密性）。** 取定义 4.1 的 $B$。
选 $p_0\in\mathbb C$ 使 $\Delta(p_0,v)$ 不是零多项式，选非恒定亚纯函数 $h:X\to\mathbb P^1$，删去其极点和 $\Delta(p_0,h)$ 的零点，得到非空仿射开曲线 $U$ 及

$$
f=(p_0,h):U\longrightarrow B.
$$

将候选覆盖拉回为 $C_U\to U$，不要求其连通，记其连通分支为 $Z_i\to U$、次数为 $d_i$。
每个分支的规范光滑射影紧化 $Y_i$ 上，有有限映射 $g_i:Y_i\to X$ 延拓 $Z_i\to U$，且

$$
g(Y_i)\ge3d_i+1.
$$

$g_i^*E_X$ 在整个 $Y_i$ 上无分歧且单值仍 Zariski 稠密。
若 $\nu:\pi_1(U)\to F$ 是候选单值的有限像，则 $(\rho|_{\pi_1(U)},\nu)$ 的联合 Zariski 闭包恰为 $G\times F$。

证明。光滑射影连通复曲线的全局正则函数为常数，见 Stacks 04L0；所以从整个 $X$ 到仿射 $B$ 的正则映射只能常值。
非恒定 $h$ 为满射且只有有限极点；非零多项式 $\Delta(p_0,v)$ 只排除有限值，故所述 $U$ 非空。
它删去非空有限集，因而仿射。
包含 $U\hookrightarrow X$ 诱导基本群满射，所以 $\rho|_{\pi_1(U)}$ 仍稠密。

一个有限指数子群在连通代数群中的稠密表示下仍稠密：设限制像的闭包为 $K$，全像由有限多个 $K$ 的陪集覆盖；
连通代数群是不可约簇，不能是有限多个真闭子集的并，所以 $K=G$。
应用到 $\ker\nu$，联合像在 $G\times\{1\}$ 稠密；对每个 $a\in F$ 取一个提升，平移后就在 $G\times\{a\}$ 稠密。
各分量合起来即 $G\times F$。对每个分支子群同样应用有限指数论证，得到限制谱单值稠密。

曲线函数域的有限扩张具有唯一规范光滑射影模型，且映射延拓为有限映射，见 Stacks 0BXX。
紧化可能在 $Y_i\setminus Z_i$ 分歧，但原 $E_X$ 在整个 $X$ 上平坦无奇点，拉回连接在这些点仍无奇点。
拓扑上，删点的 $\pi_1(Z_i)\to\pi_1(Y_i)$ 满射；因此 $g_i^*E_X$ 在紧化后的单值像与限制单值像相同，仍稠密。
最后按特征零的 Riemann–Hurwitz 公式（Stacks 0C1B），

$$
2g(Y_i)-2=d_i(2g(X)-2)+\deg\operatorname{Ram}(g_i)
=6d_i+\deg\operatorname{Ram}(g_i)\ge6d_i.
$$

这同时给出 genus 下界。没有使用候选单值等于 $S_{18}$ 的假设。$\square$

**命题 6.3（继承的中心提升与次数整除）。** 对命题 6.2 的一个分支，记 $d=d_i$、$Y=Y_i$、$g=g_i$，并令

$$
V=\ker\bigl(g^*:H^1(X,\mu_2)\to H^1(Y,\mu_2)\bigr).
$$

保持到给定 $\operatorname{SO}_5$ 系统的识别时，从 $X$ 拉回的不同提升类恰有 $256/|V|$ 个，并且 $|V|\mid d$。
所以 $d$ 为奇数时保持全部 $256$ 类；$d=18$ 时至少保持 $128$ 类。
$Y$ 上全部提升类则有 $2^{2g(Y)}$ 个，不限于继承类；每个对象仍有 $\mu_2$ 自同构。

证明。设 $\Gamma_U=\pi_1(U)$、$\Gamma=\pi_1(X)$，$q:\Gamma_U\twoheadrightarrow\Gamma$，核为 $K$。
分支对应 $H\le\Gamma_U$，$[\Gamma_U:H]=d$。
令 $L=q(H)$。因为 $K$ 正规，$q^{-1}(L)=HK$，所以

$$
[\Gamma:L]=[\Gamma_U:HK],\qquad
d=[\Gamma:L][HK:H].
$$

$\pi_1(Z_i)\twoheadrightarrow\pi_1(Y)$ 表明 $L=g_*\pi_1(Y)$。
将 $H^1(X,\mu_2)$ 识别为 $\operatorname{Hom}(\Gamma,\mu_2)$，则 $V$ 恰是限制到 $L$ 为零的特征群。
置 $N=\bigcap_{\chi\in V}\ker\chi$；有 $L\subseteq N$。
若 $\dim_{\mathbb F_2}V=t$，取特征的一组基，其联合评价
$\Gamma\to\mathbb F_2^t$ 满射，否则像上的非零线性消去关系会给这些特征的线性相关。
故

$$
[\Gamma:N]=2^t=|V|\mid[\Gamma:L]\mid d.
$$

提升挠集的拉回纤维恰是 $V$ 的陪集，因此继承类数为 $256/|V|$。
$|V|$ 是二的幂，给出奇数和十八的结论。
原提升拉回保证 $Y$ 上提升非空，所有提升再由 $H^1(Y,\mu_2)$ 自由传递作用，故总数为 $2^{2g(Y)}$。
保持五维识别是计数条件：稠密 $\operatorname{SO}_5$ 系统的中心化子为平凡群，保持识别的提升同构只能来自 $\mu_2$，不能再合并不同特征扭转。$\square$

**假设 6.4（外部 Hecke 接口）。** 取特征零 de Rham 理论，$Y$ 为光滑完备复曲线，$G_{\rm aut}$ 为连通约化复群，对偶群为 $\check G$。
采用半扭范畴 $\operatorname{D-mod}_{1/2}(\operatorname{Bun}_{G_{\rm aut}})$；选择半典范线丛时按相同规范识别相应范畴。
Mirković–Vilonen，arXiv:math/0401222v5 的几何 Satake 张量等价供应 $\operatorname{Rep}(\check G)$ 的 Hecke 作用。
Gaitsgory–Raskin，arXiv:2405.03599v3，§6.1.1 与定理 6.1.3(1)–(4)，在 GLC 前提下供应不可约 $\check G$ 局部系统 $E$ 的非零 Hecke 本征对象；
GLC 的等价前提由其系列最终篇 arXiv:2409.09856v3 供应，包括推论 2.3.11 对一般约化群的归约及 §5.5 的证明。
“不可约”指不存在到真抛物子群的水平约化。
相关本征结构对表示、态射、张量及多点融合相容：

$$
H_R(\mathcal F_E)\simeq E_R\boxtimes\mathcal F_E.
$$

定理 6.1.3(1)–(4) 还给出正则 holonomic 性、幂零奇异支撑、心中性及按谱参数自同构群的简单分解。
其 (5) 的特征循环断言另要求 $G_{\rm aut}$ 中心连通；$\operatorname{Sp}_4$ 的中心为 $\mu_2$，故这里不采用 (5)。

**推论 6.5（紧化分支上的 Hecke 存在性）。** 在假设 6.1、6.4 下，命题 6.2 的每个 $Y_i$ 上，$g_i^*E_X$ 给出非零 $\operatorname{Sp}_4$ Hecke 本征对象。

证明。取 $G_{\rm aut}=\operatorname{Sp}_4$、$\check G=\operatorname{SO}_5$。
稠密单值不能落入真抛物闭子群，故谱参数不可约；$Y_i$ 光滑完备，且系统无分歧，满足假设 6.4。
其自同构群是稠密像的中心化子，即 $Z(\operatorname{SO}_5)=1$，所以按 (4) 相应对象本身简单，特别非零。
这是外部接口在该分支上的应用；谱侧的 $g_i^*$ 并未构造自守侧的 basechange 函子。$\square$

## 7. Hankel 证书与 Ω 六维自治实现

**定义 7.1（自伴压缩与矩）。** 在有限维复 Hilbert 空间上取 $H=H^*$、等距映射 $U:\mathbb C^m\to\mathbb C^N$，置

$$
P=UU^*,\quad A=U^*HU,\quad D=(I-P)HU,\quad
F(t)=U^*e^{-itH}U,\quad M_j=U^*H^jU,
$$

$$
K_s=[U,HU,\ldots,H^sU],\qquad
\Gamma_s=(M_{i+j})_{0\le i,j\le s},\qquad
\mathcal K_\infty=\operatorname{span}_{j\ge0}H^j\operatorname{im}U.
$$

KRYLOV §265 供应：
$U^*H^2U=A^2+D^*D$，压缩群律的二阶缺陷为泄漏 $D^*D$；
全未来输出 $x\mapsto(U^*e^{-itH}x)_{t\in\mathbb R}$ 的核为 $\mathcal K_\infty^\perp$，且
$\dim(\operatorname{im}U+H\operatorname{im}U)=m+\operatorname{rank}D$。
以下把这些输入与块 Hankel/Gram 实现法结合。

**命题 7.2（自伴实现输入在 Ω 预测编码中的应用）。** 为定义 7.4 的 Ω 模型采用如下自伴 Hankel/Gram 实现输入。
在定义 7.1 的记号中，全时刻群律
$F(t+s)=F(t)F(s)$ 成立，当且仅当 $D=0$。
复现所有矩 $M_j$（等价地复现所有 $F(t)$）的最小有限维自伴实现维数为

$$
d_{\min}=\sup_s\operatorname{rank}\Gamma_s
=\dim\mathcal K_\infty.
$$

特别地 $\operatorname{rank}\Gamma_1=m+\operatorname{rank}D$。
两个具有这些矩的循环最小自伴实现之间存在唯一同时交织 $H$ 和 $U$ 的酉映射。
对任意隐藏初态 $x$，若复线性编码 $Sx$ 足以确定全未来输出，则
$\ker S\subseteq\mathcal K_\infty^\perp$，从而 $\operatorname{rank}S\ge d_{\min}$；
正交投影到 $\mathcal K_\infty$ 达到该界。

证明。自伴实现部分是经典 Gram 构造在本应用中的具体化；KRYLOV 已有的压缩与全未来核结论按定义 7.1 直接复用。
群律和可微性迫使 $F(t)=e^{-itA}$；对二阶导数比较并应用 KRYLOV 的恒等式得 $D^*D=0$。
反之 $D=0$ 使 $\operatorname{im}U$ 为 $H$-不变子空间；自伴性使它约化，故压缩为 $e^{-itA}$。
自伴性还给出 Gram 恒等式

$$
\Gamma_s=K_s^*K_s.
$$

因此秩为有限 Krylov 子空间维数，上确界为 $\dim\mathcal K_\infty$。
任一同矩实现的 $\Gamma_s$ 不变，维数不小于这些秩；限制 $H$ 到约化子空间 $\mathcal K_\infty$ 达到界，并复现矩和指数函数。
这里使用的是经典 Hankel/Gram 最小实现论证在自伴循环子空间上的形式；一般线性系统的 Hankel 最小维数亦见固定来源提交中的 [COMPUTATIONAL_BEHAVIOR_REPRESENTATION_THEORY.md](https://github.com/the-omega-institute/trureturing/blob/57c4745c00f182a2a5b0fefc30306133b10fc297/docs/develop/theory/COMPUTATIONAL_BEHAVIOR_REPRESENTATION_THEORY.md) 定理 5.3。
$[U,HU]=[U,UA+D]$ 的列空间是 $\operatorname{im}U\oplus\operatorname{im}D$，得到首阶秩公式。

对两个同矩最小实现定义

$$
W\left(\sum_jH^jUv_j\right)=\sum_j(H')^jU'v_j.
$$

两边任意这类向量的内积都由 $v_i^*M_{i+j}w_j$ 的和给出，故 $W$ 良定义且等距；循环性使它满射，且满足 $WU=U'$、$WH=H'W$，也使其唯一。
最后，若 $Sx=Sx'$，充分性使 $x-x'$ 的全部输出为零，KRYLOV 的全未来核公式即给出核包含关系和秩下界。
正交投影的核恰为 $\mathcal K_\infty^\perp$，所以达到。$\square$

**命题 7.3（有限噪声矩的维数证书）。** 若另一自伴实现的矩满足
$\max_{0\le j\le2s}\|M_j-M'_j\|\le\varepsilon$，则其维数 $N'$ 满足

$$
N'\ge\#\{k:\lambda_k(\Gamma_s)>(s+1)\varepsilon\}.
$$

证明。对块向量 $v=(v_0,\ldots,v_s)$，每个误差块行的范数不超过 $\varepsilon\sum_j\|v_j\|$，所以
$\|\Gamma_s-\Gamma'_s\|\le(s+1)\varepsilon$。
应用自伴矩阵的经典 Weyl 特征值扰动不等式，所列严格阈值以上的每个特征值在 $\Gamma'_s$ 中仍正。
而 $\Gamma'_s$ 是 $N'$ 维实现的 Gram 矩阵，秩至多 $N'$，故得下界。
这只是已取得矩及其误差界所证的维数证书，不供应这些矩的测量权限或价格。$\square$

**定义 7.4（Ω 的共同 Fock 实现）。** 采用完整三模式 Fock 空间的标准 CCR，$\hbar>0$，

$$
V=\operatorname{span}\{|000\rangle,|100\rangle,|010\rangle,|001\rangle,|101\rangle\},
\quad e_4=|101\rangle,
$$

$$
f_+=|200\rangle,\quad f_-=|002\rangle,\quad
W=V\oplus\operatorname{span}\{f_+,f_-\},
$$

$$
H_{\rm phys}=g a_1^\dagger a_3+\overline g a_3^\dagger a_1+Jn_1n_3,
\quad g\ne0,\ J\in\mathbb R,
\quad H=H_{\rm phys}/\hbar.
$$

令 $r_g=|g|$、$u=g/r_g$，亮、暗向量为

$$
b=\frac{u f_++\overline u f_-}{\sqrt2},\qquad
z_{\rm dark}=\frac{u f_+-\overline u f_-}{\sqrt2}.
$$

OMEGA 命题 2.1 供应 $W$ 约化以及

$$
H_{\rm phys}e_4=Je_4+2r_gb,\qquad
H_{\rm phys}b=2r_ge_4,\qquad H_{\rm phys}z_{\rm dark}=0,
$$

其余 $V$ 基向量被送回 $V$。

**命题 7.5（Ω 的六维最小性）。** 对 $V\hookrightarrow W$ 的等距嵌入，

$$
\mathcal K_\infty=V\oplus\mathbb Cb,\qquad
d_{\min}=6,\qquad
D=\frac{2r_g}{\hbar}|b\rangle\langle e_4|,\qquad
\operatorname{rank}D=1.
$$

暗态的全部可见振幅为零；任何全矩自伴实现及任何全隐藏初态的线性充分编码均至少为六维。

证明。$He_4-(J/\hbar)e_4=(2r_g/\hbar)b$，故亮向量在第一 Krylov 扩张中。
上述输入又使 $V\oplus\mathbb Cb$ 不变；因此它就是整个循环闭包，维数为六。
直接投影得到 $D$，再应用命题 7.2。
暗向量正交于该闭包且为零特征向量，所以 $U^*e^{-itH}z_{\rm dark}=0$ 对所有 $t$ 成立。
特别 $\Gamma_1$ 已有秩六，可配合命题 7.3 给出有噪声的可检验下界。
OMEGA 的个别精确返回时刻不消去 $D\ne0$ 的全时刻群律障碍，也不改变“禁止中途出游”等单独路径权限。
标准 CCR 所在空间为完整 Fock 空间：若有限维矩阵满足 $[a,a^*]=I$，取迹会得到 $0=\dim V$，故不能在有限编码空间内免费保留完整 CCR。$\square$

## 8. 固定 Green 模型与临界完成输入

**定义 8.1（共同圆柱及单位源）。** 固定 $r=1-Z>0$、两个墙条件 $X=Y=r/2$，以及
$I=(l,u)\Subset(0,r/2)$。
令 $\Omega=I\times\mathbb T^2$，实际相位 $\alpha,\beta$ 的周期均为 $2\pi$，测度不作概率归一化。
水平场固定为

$$
X_1=P=\partial_k,\qquad
X_2=Q=\tfrac12\partial_\alpha+(\tfrac12-k/r)\partial_\beta.
$$

密度 $\rho>0$、实对称正定矩阵场 $A=(a^{ij})$ 在闭柱邻域光滑，$d\mu=\rho\,dk\,d\alpha\,d\beta$。
高度两端杀死，实际相位周期保留。
定义

$$
T_A[f]=\int_\Omega\langle A\nabla_Xf,\nabla_Xf\rangle\,d\mu,
\qquad
\mathcal F_A=\overline{C_c^\infty(\Omega)}^{(\|f\|_2^2+T_A[f])^{1/2}},
$$

其非负自伴算子为 $L_A$。
固定内部源点 $o$，令 $p_s^\Omega$ 是相对于 $\mu$ 的完整被杀热核，

$$
\Gamma_{A,o}(q)=\int_0^\infty p_s^\Omega(o,q)\,ds,\qquad
\int_\Omega\Gamma_{A,o}L_A\psi\,d\mu=\psi(o),
$$

$$
q_{A,g}[f]=T_A[f]-g\int_\Omega\Gamma_{A,o}|f|^2d\mu.
$$

时间规范为 $e^{-sL_A}$，水平协方差为 $2A\,ds$。

**定义 8.2（精确源图与冻结角剖面）。** 在同一个源点局部相位提升中，置

$$
x=k-k_o,\quad y=2(\alpha-\alpha_o),\quad
c_o=\tfrac12-k_o/r,\quad
z=-r(\beta-\beta_o-c_oy),\quad t=z-xy/2.
$$

于是精确地

$$
P=\partial_x-\tfrac y2\partial_t,\qquad
Q=\partial_y+\tfrac x2\partial_t,
\qquad dk\,d\alpha\,d\beta=\frac1{2r}\,dx\,dy\,dt.
$$

对一个源点矩阵 $A^0=A(o)$，令 $B=(A^0)^{-1/2}$，

$$
(\xi,\eta)^{\mathsf T}=B(x,y)^{\mathsf T},\quad
\zeta=\det(B)t,\quad
m_0=\frac{\rho(o)\det A^0}{2r},\quad
R=((\xi^2+\eta^2)^2+16\zeta^2)^{1/4}.
$$

取角 $a\in(-\pi/2,\pi/2)$ 满足
$\xi^2+\eta^2=R^2\cos a$、$4\zeta=R^2\sin a$。
令 $\lambda_0$ 为角闭形式

$$
\int_{-\pi/2}^{\pi/2}(4\cos a\,|b'|^2+\cos a\,|b|^2)\,da,
\qquad
b\in L^2\cap AC_{\rm loc},\quad\sqrt{\cos a}\,b'\in L^2
$$

的最低特征值，$\phi>0$ 为 $\phi(0)=1$ 的最低特征函数。
这里自然端点条件而非 Dirichlet 条件给出

$$
-4(\cos a\,\phi')'+\cos a\,\phi=\lambda_0\phi,\quad
\phi'(0)=0,\quad\cos a\,\phi'\longrightarrow0.
$$

GREEN 定理 10.2 供应 $0<\lambda_0<2/\pi$ 及 $\phi$ 在闭角区间光滑、严格正。
定义 $h_0(\xi,\eta,\zeta)=R^{-1}\phi(a)$。
它在穿孔源图包括中心轴上光滑：靠近非零中心轴，
$\pi/2-|a|=\arctan((\xi^2+\eta^2)/(4|\zeta|))$，配合自然端点的光滑分支即可。

**假设 8.3（完整 Green 临界输入）。** 采用 GREEN 定理 10.2、11.1、12.2、13.1 的如下陈述：

$$
\Gamma_{A,o}=(2\pi m_0)^{-1}R^{-2}+O(R^{-1}),\qquad
g_c=2\pi m_0\lambda_0=\frac{\pi\rho(o)\det A(o)\lambda_0}{r}.
$$

若 $0<g<g_c$，原域 $\mathcal F_A$ 上的 $q_{A,g}$ 闭且下半有界，充分平移后的形式范数与自由范数等价，紧预解且归一化下确界取到。
若 $g>g_c$，原穿孔光滑核中有归一化函数列使能量趋于负无穷。
若 $g=g_c$，原域上形式下半有界、可闭而不闭，需采用以下指定完成。

令 $F_A(x,y,t)=(B(x,y),\det B\,t)$，在小源图中置 $h_A=h_0\circ F_A$。
选穿孔柱上的正光滑函数 $H$，近源恰为 $h_A$、远处为一，并置

$$
d\nu=H^2d\mu,\qquad
\mathcal E_H[v]=\int H^2\langle A\nabla_Xv,\nabla_Xv\rangle d\mu,
$$

$$
\mathcal W_H=
\overline{C_c^\infty(\Omega\setminus\{o\})}^{(\|v\|_{L^2(\nu)}^2+\mathcal E_H[v])^{1/2}},
\qquad\mathcal D_A=H\mathcal W_H.
$$

这里 $F_A$ 表示源图的白化映射，不是自由形式域 $\mathcal F_A$。
穿孔区的微分表达式

$$
W=H^{-1}L_AH-g_c\Gamma_{A,o}
$$

满足 $W=O(R^{-1})$，且 $\int|W||Hv|^2d\mu$ 对 $\mathcal E_H$ 有任意小的相对形式界。
临界闭包为

$$
\overline q_c[Hv]=\mathcal E_H[v]+\int W|Hv|^2d\mu,
\qquad
\mathcal F_A\subsetneq\mathcal D_A.
$$

$\mathcal D_A$ 紧嵌入 $L^2(\mu)$；原域与完成域有同一有限归一化下确界，完成域取到，而原域不取到。
该闭包表达式不用两个发散项的 $\infty-\infty$ 定义有限临界能量。
相对小界使充分平移后的临界形式范数与 $\mathcal W_H$ 范数等价。

## 9. 临界完成域的共形分类与预算

**定义 9.1（比较类及函数识别）。** 固定定义 8.1 的同一 $\Omega,r,o,P,Q$、相位周期及两端杀死边界。
取两个闭柱邻域上的光滑正密度 $\rho_i$、光滑实对称正定场 $A_i$，$i=1,2$。
用定义 8.2 的同一个精确 Heisenberg 源图 $q=(w,t)=(x,y,t)$ 及同一 $h_0$，令

$$
A_i^0=A_i(o),\quad B_i=(A_i^0)^{-1/2},\quad
F_i(w,t)=(B_iw,\det B_i\,t),\quad h_i=h_0\circ F_i,\quad R_i=R\circ F_i.
$$

选择 $H_i$ 近源恰为 $h_i$、远处为一，按假设 8.3 的同一穿孔核完成方式定义
$\mathcal W_i,\mathcal D_i=H_i\mathcal W_i$。
所有 $L^2$ 空间以同一可测函数作恒等识别：$\rho_i$ 在闭柱上有统一正上下界，故有同一零测集及相同的 $L^2$ 函数集合。
完成域不因所选 $H_i$ 的远源光滑插值改变；下面的乘子论证也适用于同一 $h_i$ 的两种插值。

**定理 9.2（源点共形的必要充分分类）。** 在定义 9.1 的比较类中，以下条件等价：

$$
\mathcal D_1\subseteq\mathcal D_2
\quad\Longleftrightarrow\quad
\mathcal D_1=\mathcal D_2
\quad\Longleftrightarrow\quad
\mathcal D_2\subseteq\mathcal D_1
\quad\Longleftrightarrow\quad
A_2(o)=cA_1(o)\text{ 对某个 }c>0.
$$

共形时完成域范数等价。不共形时，可取同一个紧支光滑 $\chi$，近源为一，构造
$f_i=\chi h_i$，使

$$
f_1\in\mathcal D_1\setminus\mathcal D_2,\qquad
f_2\in\mathcal D_2\setminus\mathcal D_1.
$$

证明。先记录共同的精确缩放。Heisenberg 膨胀

$$
\delta_s(w,t)=(sw,s^2t),\quad s>0,
$$

使体积 $dq$ 缩放为 $s^4dq$，水平导数次数为一，$F_i$ 与 $\delta_s$ 交换。
因此 $h_i\circ\delta_s=s^{-1}h_i$、$R_i\circ\delta_s=sR_i$。
$\phi$ 严格正且在闭角区间光滑，故 $h_i\asymp R_i^{-1}$，并且各 $R_i$ 相互可比。
源图中原始体积恒为 $(2r)^{-1}dq$。

先证 $f_i$ 属于自己的完成域。将 $\chi$ 的支集取在 $H_1=h_1$、$H_2=h_2$ 的共同区域内。
对 $0<\varepsilon<1$ 取径向光滑截断 $\eta_\varepsilon(R_i)$，在 $R_i\le\varepsilon^2$ 为零、在 $R_i\ge\varepsilon$ 为一，满足

$$
|\eta_\varepsilon'|\le\frac{C}{R_i|\log\varepsilon|}.
$$

则 $\chi\eta_\varepsilon\in C_c^\infty(\Omega\setminus\{o\})$。
利用 Heisenberg 极坐标的体积次数四及 $|\nabla_XR_i|\le C$，

$$
\|\chi(1-\eta_\varepsilon)\|_{L^2(H_i^2\mu_i)}^2
\le C\int_0^\varepsilon R^{-2}R^3dR=O(\varepsilon^2),
$$

$$
\mathcal E_i[\chi(1-\eta_\varepsilon)]
\le\frac{C}{|\log\varepsilon|^2}
\int_{\varepsilon^2}^{\varepsilon}\frac{dR}{R}
=O(|\log\varepsilon|^{-1}).
$$

小 $\varepsilon$ 时 $\nabla\chi$ 的支集与变化区分离，不贡献余项。
于是 $\chi\in\mathcal W_i$，$f_i=H_i\chi\in\mathcal D_i$。
这是临界零容量的对数截断方法在本剖面上的应用；假设 8.3 已供应完成域与临界闭形式的对应。

其次，若 $f\in\mathcal D_2$，则 $v=f/H_2\in\mathcal W_2$，并在穿孔区域具有有限加权弱导数能量。
确实，定义 $\mathcal W_2$ 的逼近列在任意离源紧子域上具有等价的通常水平 Sobolev 范数，
$L^2$ 极限与分部积分识别出 $v$ 的弱水平导数。
这些梯度也是全局加权 $L^2$ 的 Cauchy 列，局部极限相容；穷竭穿孔柱即得

$$
\int_\Omega H_2^2\langle A_2\nabla_Xv,\nabla_Xv\rangle d\mu_2<\infty.
$$

这一必要条件只涉及正能量。

现在假设 $A_1^0,A_2^0$ 不成正比例。比值 $u=h_1/h_2$ 光滑、零次齐次。
在 $t=0$、$w\ne0$ 上，$a=0$、$\phi(0)=1$ 给出

$$
h_i(w,0)=\bigl(w^{\mathsf T}(A_i^0)^{-1}w\bigr)^{-1/2}.
$$

若 $u$ 为常数，这两个正定二次型必成比例，反推 $A_1^0,A_2^0$ 成比例，矛盾。
故 $u$ 不恒定。取连通齐次壳
$K=\{1/2<R_1<1\}$，定义冻结正能量

$$
e_*=
\int_K h_2^2\langle A_2^0\nabla_Xu,\nabla_Xu\rangle dq.
$$

$e_*$ 有限；若它为零，光滑性与正定性使 $Pu=Qu=0$。
又 $[P,Q]=\partial_t$，故 $\partial_tu=\partial_xu=\partial_yu=0$，$u$ 在连通壳上为常数。
每个穿孔点的膨胀轨道与该壳相交，零次齐次性再使 $u$ 全域常值，矛盾。
所以 $e_*>0$。

对每个缩放壳 $\delta_sK$，冻结能量恰等于 $e_*$：$h_2^2$、梯度平方和体积的次数分别为 $-2,-2,4$。
真实 $A_2(q)$、$\rho_2(q)$ 在源点邻域与冻结矩阵及正的常密度统一可比，故每个足够小的二进壳上的真实能量至少为固定正常数乘 $e_*$。
这些壳互不相交，求和得到

$$
\int_{0<R_1<b}h_2^2\langle A_2\nabla_Xu,\nabla_Xu\rangle d\mu_2=\infty.
$$

若 $f_1\in\mathcal D_2$，则近源 $f_1/H_2=u$，与上面的有限能量必要条件冲突。
交换指标得到 $f_2\notin\mathcal D_1$。
这个论证使用精确的共同水平场；变系数只改变壳能量的正比较常数，不改变发散。

最后设 $A_2^0=cA_1^0$。唯一正定平方根给出

$$
F_2=\delta_{c^{-1/2}}\circ F_1,\qquad h_2=\sqrt c\,h_1.
$$

比值 $b=H_2/H_1$ 近源为常数 $\sqrt c$，远处为一；因此 $b,b^{-1}$ 及其水平一阶导数有界。
闭柱上 $A_i,\rho_i$ 也统一可比。
乘积法则 $\nabla_X(b^{-1}v)=b^{-1}\nabla_Xv+v\nabla_Xb^{-1}$ 给出

$$
\|b^{-1}v\|_{\mathcal W_2}\le C\|v\|_{\mathcal W_1},
\qquad
\|bw\|_{\mathcal W_1}\le C'\|w\|_{\mathcal W_2}.
$$

这些映射保持穿孔光滑核，故延拓为完成空间的互逆有界映射。
又 $H_2b^{-1}v=H_1v$，所以它们在实际函数层面给出 $\mathcal D_1=\mathcal D_2$ 及范数等价。
结合非共形时的两个显式反例，得到全部等价关系。$\square$

**推论 9.3（阈值与域的不同不变量）。** 在同一比较类中，临界完成域的分类不变量可写作
$A(o)/\sqrt{\det A(o)}$。
若 $A_2(o)=cA_1(o)$，则

$$
\frac{g_{c,2}}{g_{c,1}}=c^2\frac{\rho_2(o)}{\rho_1(o)}.
$$

特别，固定源点密度及阈值的子族中，两个完成域相同当且仅当两个源点矩阵完全相同。

证明。二阶正定矩阵的正比例类由行列式归一化代表唯一确定；阈值公式直接给出比例。
固定密度和阈值时有 $\det A_1(o)=\det A_2(o)$，再与共形关系组合得 $c^2=1$，即 $c=1$。
域相等只说同一可测函数能否属于指定完成；不推出闭形式、Green 函数、算子或谱相等，也不分类其他边界或任意自伴扩张。$\square$

**命题 9.4（同阈值而互不包含的常场实例）。** 在同一个柱、源点及同一常正密度下，取

$$
A_1=I_2,\qquad A_2=\operatorname{diag}(\sigma,\sigma^{-1}),
\qquad \sigma>0,\ \sigma\ne1.
$$

则自由形式域 $\mathcal F_{A_1}=\mathcal F_{A_2}$，临界阈值相同，而两个临界完成域互不包含。

证明。常正定矩阵的自由能量范数等价，故自由核闭包相同。
$\det A_1=\det A_2=1$，假设 8.3 给出同阈值。
源点矩阵不共形，定理 9.2 给出双向不包含。
具体地，在共同 $t=0$ 平面，

$$
h_1=(x^2+y^2)^{-1/2},\qquad
h_2=(x^2/\sigma+\sigma y^2)^{-1/2},
$$

比值非常数；对应 $\chi h_i$ 正是定理中的两个反例。
不等阈值时也仍适用同一分类；本例只凸显标量阈值不能决定完成域。$\square$

**命题 9.5（固定迹预算的最大临界阈值）。** 固定 $r,\rho(o)$、参考正定矩阵 $G$ 及 $\tau>0$。
在 $\operatorname{tr}(G^{-1}A(o))=\tau$ 的比较类中，

$$
g_c\le\frac{\pi\rho(o)\lambda_0\det G}{4r}\tau^2,
$$

等号当且仅当 $A(o)=\tau G/2$，常场可达到。
若 $\kappa_1,\kappa_2$ 为 $G^{-1/2}A(o)G^{-1/2}$ 的特征值，则精确亏损为

$$
\frac{\pi\rho(o)\lambda_0\det G}{4r}\tau^2-g_c
=\frac{\pi\rho(o)\lambda_0\det G}{4r}(\kappa_1-\kappa_2)^2.
$$

证明。两正特征值之和为 $\tau$；作为此应用的经典二元算术几何平均恒等式，

$$
\det A(o)=\det G\,\kappa_1\kappa_2
=\frac{\det G}{4}\{\tau^2-(\kappa_1-\kappa_2)^2\}.
$$

代入假设 8.3 的阈值公式即得全部结论。
等号迫使两个特征值均为 $\tau/2$，即 $A(o)=\tau G/2$；取该常场满足全部光滑正定条件。
这约束源点的数学协方差预算，不是取得仪器或原命令执行成本。$\square$

## 10. 原命令占用与带实际锚点的组合

**假设 10.1（原命令到 Green 占用的附加资源）。** 在定义 8.1 的同一固定模型中，另给：每阶段有限多个独立公平符号、给定初态、精确实算、
$A^{1/2}$ 及

$$
d^j=\rho^{-1}\sum_iX_i(\rho a^{ij})
$$

的求值，以及原控制和首次碰壁分数的精确执行。
GREEN 定理 29.6 供应有限原命令族 $q_n$，各阶段使用合法分段线性控制，在同一轨迹上保留时间序面积和真实两端杀死，寿命记为 $\zeta_n$。
在其完整联合轨迹与寿命极限中，对每个闭柱上连续函数 $f$，

$$
\lim_{n\to\infty}\mathbb E\int_0^{\zeta_n}f(q_n(s))\,ds
=\mathbb E_o\int_0^\tau f(Q_s)\,ds
=\int_\Omega\Gamma_{A,o}f\,d\mu.
$$

统一寿命尾界使有限时间窗极限延伸到完整时间积分。
其极限生成元为

$$
\mathcal G=-L_A
=\sum_{i,j}a^{ij}X_iX_j+\sum_jd^jX_j.
$$

GREEN 边界 29.7 还供应：每个固定正时间窗上，执行控制的总变差及附加二次控制能量依概率发散。
所以每阶段有限与极限具有统一有限预算是不同命题。
这些资源不由裸候选代数或协方差表推出；占用输入也不供应最小传感器合同、原子树与圆柱的识别或双网格同时极限。

**定义 10.2（相容的实际锚点）。** 给定以下共同实例：

1. 合法取得恢复了一个完整实际来源，严格实守卫已满足，并给出定义 4.1 良好层中的参数 $b_0=(p_0,v_0)$ 与实际评价 $\chi_0$，对应点 $c_0\in C_{b_0}$。
2. 假设 6.1 的四块二通道在同一谱参数和指定模型内共同实现，并给出 genus-4 曲线 $X$ 及稠密 $E_X$。
3. 选非恒定亚纯 $h:X\to\mathbb P^1$、一个 $x_0$ 满足 $h(x_0)=v_0$，并在随后各光滑完备曲线上采用假设 6.4 的半扭归一化。

第二项是独立的实现假设，第三项是数学基变换选择；它们并不由第一项取得免费产生。
$h$ 满射保证所需 $x_0$ 存在。
因为 $\Delta(p_0,v_0)\ne0$，多项式 $\Delta(p_0,v)$ 非零。
删去极点及 $\Delta(p_0,h)$ 的零点后，命题 6.2 的 $U$ 含 $x_0$，且 $f=(p_0,h)$ 经过 $b_0$。

**定理 10.3（带锚选层与谱紧化的组合）。** 对定义 10.2 的相容实例，令 $Z_0$ 是 $C_U\to U$ 中经过 $(x_0,c_0)$ 的连通分支，次数为 $m$。
则 $m$ 是限制到这条参数曲线后锚点轨道的大小，最小带锚有限 étale 选择次数为 $m$，并整除所有通过该锚点的连通选择次数。

设 $R_U=\mathcal O(U)$、$\mathcal A_U$ 为整个候选覆盖的代数、$S=\mathcal O(Z_0)$，商映射记作 $\chi:\mathcal A_U\to S$。
则存在典范水平幂等元

$$
e\in\mathcal A_U\otimes_{R_U}S,\qquad
\operatorname{Tr}_{(\mathcal A_U\otimes S)/S}(e)=1,
$$

使对全部 $a\in\mathcal A_U$，

$$
\chi(a)=\operatorname{Tr}_{(\mathcal A_U\otimes S)/S}((a\otimes1)e).
$$

$Z_0$ 的光滑射影紧化 $Y$ 满足 $g(Y)\ge3m+1$；其拉回 $\operatorname{SO}_5$ 局部系统稠密、全曲线无分歧，并按假设 6.4 具有非零 $\operatorname{Sp}_4$ Hecke 本征对象。
从 $X$ 继承的中心提升数为 $256/|V|$，其中 $|V|\mid m$；全部提升数为 $2^{2g(Y)}$。

证明。定义 10.2 保证拉回覆盖及锚点同时存在。有限 étale 对应将所选连通分支识别为锚点轨道，命题 4.5 给出最小次数与整除关系。
把整个候选覆盖拉回到 $Z_0$ 后，其纤维积包含由包含映射 $Z_0\hookrightarrow C_U$ 所给图像。
有限 étale 覆盖的截面是开闭嵌入，故该图像的指示函数是典范幂等元 $e$。
它每纤维选中一个坐标，故相对于 $S$ 的迹为一，并给出所示评价公式；这是命题 4.4 的相对形式。

连接对 $e^2=e$ 求导得到

$$
(2e-1)\nabla e=0,\qquad (2e-1)^2=1,
$$

所以 $\nabla e=0$。
该幂等元的承载是整个 $\mathcal A_U\otimes S$；若 $m>1$，连通 $S$ 自身只有零、一两个幂等元，
相对于 $R_U$ 的迹分别为零、$m$，不能在那里写一个迹一选层元。
命题 6.2、6.3 与推论 6.5 依次给出紧化、genus、稠密性、提升与 Hecke 结论。
限制参数曲线可以缩小原基底单值轨道，故 $m$ 不预定为十八。$\square$

**推论 10.4（水平幂等元与可变原始根）。** 在定理 10.3 中，记 $z_0=\chi(z)\in S$。
则 $z_0$ 水平当且仅当它为复常数；若 $m>1$，它必不水平。
$m=1$ 允许 $z_0$ 非恒定。

证明。曲线上有限 étale 导子的唯一延拓给出 $S$ 的绝对微分连接；在连通光滑复曲线上，$dz_0=0$ 等价于 $z_0$ 局部常值，继而全局为复常数。
有限态射到仿射曲线使 $Z_0$ 仿射；它是整个候选代数的一个直积分量，故

$$
S=R_U[z_0].
$$

若 $z_0\in\mathbb C$，则 $S=R_U$，从而 $m=1$。
反向“$m=1$ 迫使根常数”不成立：取任意仿射曲线 $U$ 上的非恒定正则函数 $a$，秩一候选代数
$R_U[T]/(T-a)\simeq R_U$ 的根就是 $a$，连接满足 $\nabla T=da$。
因此选层指示函数水平与原始读数水平属于不同断言。$\square$

**定义 10.5（组合结论的实现边界）。** 下列桥梁作为独立数学问题保留：原生权限中四块二通道的共同实现；异常层的完整候选分层及矩形外全域双碰撞；指定参数曲线的实际单值群；含噪声取得的条件数与最小预测态的实际取得成本；自守侧 basechange 函子的构造。
定理 10.3 的评价保持已给实际锚点，不从无标签的全候选迹恢复未知实际标签，也不声称唯一物理重建。
有限函数代数的乘法没有被当作 $\operatorname{SO}_5$ 的普适态射。
第 4 节的可执行置换合同、第 5 节的条件信息预算、第 7 节的线性自治维数和第 10.1 节的原命令资源各自独立；任一结论不免除另一合同的前提。

## 11. 具名外部来源及数学适用范围

**约定 11.1（文献输入）。** 下列 `literature-attested` 结果只作为相应应用的中间步骤。

| 来源 | 本卷中的精确作用 |
| --- | --- |
| [Stacks 00UP](https://stacks.math.columbia.edu/tag/00UP)，§10.150 | 有限表示 étale 代数的 formally étale 唯一提升；用于命题 4.2 的导子延拓 |
| [Stacks 0BND](https://stacks.math.columbia.edu/tag/0BND)，定理 58.6.2 | 有限 étale 覆盖、有限基本群集合及基变换相容性；用于命题 4.5 和定理 10.3 |
| [Stacks 04L0](https://stacks.math.columbia.edu/tag/04L0)，引理 33.26.2 | 适当几何整复簇的正则函数为常数；用于命题 6.2 的开曲线必要性 |
| [Stacks 0BXX](https://stacks.math.columbia.edu/tag/0BXX)，§53.2 | 函数域与规范射影曲线、有限映射的紧化；用于命题 6.2 |
| [Stacks 0C1B](https://stacks.math.columbia.edu/tag/0C1B)，§53.12 | 特征零光滑射影曲线的 Riemann–Hurwitz；用于 $g(Y_i)\ge3d_i+1$ |
| [Deligne–Milne，《Tannakian Categories》，tc2022](https://www.jmilne.org/math/xnotes/tc2022.pdf)，§2，特别命题 2.21 | 代数群表示与张量纤维函子；命题 4.7 只用实际单值闭包决定等变态射，不从个别 Hom 等号反推稠密性 |
| [Mirković–Vilonen，arXiv:math/0401222v5](https://arxiv.org/abs/math/0401222v5)，定理 7.3 及 Appendix B 的条件解释 | 复连通约化群的几何 Satake；在复系数及相应半扭规范下用于假设 6.4 的 Hecke 作用 |
| [Gaitsgory–Raskin I，arXiv:2405.03599v3](https://arxiv.org/html/2405.03599v3)，§1.1、§6.1.1、定理 6.1.3(1)–(4) | 半扭 de Rham 范畴、不可约谱参数的本征对象及简单分解；保留 GLC 前提，不使用中心连通的 (5) |
| [Gaitsgory–Raskin V，arXiv:2409.09856v3](https://arxiv.org/html/2409.09856v3)，推论 2.3.11 与 §5.5 | 一般约化群的归约及 GLC 证明，供应上一行的等价前提；不供应原生控制或自守 basechange |

**约定 11.2（结果间的依赖）。** 取得的环境逆、实际三世界证书、稠密谱系统及 Green 临界完成分别采用约定 1.1 的 CLOCK、REAL、CONTEXT、GREEN 输入。
命题 2.2、2.4、3.2，命题 4.2–4.7 对候选的应用，命题 5.2–5.4 的自适应计费，命题 6.2、6.3 及推论 6.5，命题 7.2–7.5 的自伴与 Ω 应用，定理 9.2 及其推论和预算应用，定理 10.3、推论 10.4 均按所列条件推导。
Green 分类的充分性依靠有界可逆乘子，必要性依靠非共形剖面的严格正齐次壳能量；标量阈值只用于相应应用，未充当域分类的前提。

## 追加锚（本行以下为增补区）
