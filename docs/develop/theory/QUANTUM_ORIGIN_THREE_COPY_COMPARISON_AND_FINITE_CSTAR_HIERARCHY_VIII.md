# 三份原准备比较与全有限复 C* 张量层级 VIII

> **卷际约定。** 本卷承接[第 VII 卷](QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md)。
> 正文中所有“VII卷”编号均指该卷的原条目；未加卷号的第 123 章及其条目、公式属于本卷。
> 原模型与条件供应以所引 VII 卷条目的完整定义域、假设和适用边界为准。
> 本卷只增不减；修订与增补续于文末追加锚之后，保留既有条目、编号与引用。

## 123. 共同源锥系统、完整五份前缀与固定间隙紧致性

**定义 123.1（原定义包的有限截断与两类端口）。** 固定VII卷假设105.1中的有限扇区集
$I$、所有原标签与 $n_i\in\{1,2,3\}$，其中 $\max_i n_i=3$，以及同一保迹局部坐标
$V=\bigoplus_i\operatorname{Herm}_{n_i}$。这里
$\operatorname{Herm}_d$ 始终是复 $d\times d$ Hermitian 矩阵的实向量空间，
实维为 $d^2$；其真正实张量积通过 Kronecker 产品识别为相应复合 Hermitian 空间。
固定原 $\mathsf F_{r,2}$ 的含相位向量、$\Delta_{r,2}$、VII卷定义105.2的实码
$c=(00,01,10)$、$c^*11=0$、所有实际最大块 $s$ 的 $i_s,q_s$ 与 $P$。
每个实际块的计算基固定一次；其中包含所给种子基的相位，不对相位另取商。

截断阶数 $M\ge3$ 的完整定义前缀指 $C_1,\ldots,C_M$ 满足VII卷定义102.1中
总次数不超过 $M$ 的全部条件：闭尖生成、严格正的 $u_N$、整个基 $K_N$、
全部 $P_N=\operatorname{ext}K_N$、整个 $[0,u_N]_{C_N^*}$，以及每个
$a+b\le M$ 的 min/max 双界、所有位置置换及其逆、原配对、张量单位和规范重括号。
低二份取对齐后的整个 $C_1=\mathsf D_1,C_2=\mathsf D_2$，保留整个 $S_2$，
包括纠缠纯点、全部有限准备、零权和重复标签。
三条条件 PAPER 供应仍是VII卷103.1、VII卷104.1的完整接口：

| 条件接口 | 在本定义包中保留的全部输入 |
| --- | --- |
| 低二份 least confirmation 到 Jordan | $q=1,2$ 的整个基、全部极点、全 proper 效应及原下确界；least 性、互反、同框架谱性、projectivity、正面投影及 filter purity；保迹表示与直和 |
| 唯一实际自复合的复型选择 | 同一个 $(W_1,W_1,W_2)$ 的正双线性态产品与效应产品、原单位、全域精确配对、乘积效应分离和局部层析；所有中心扇区限制、框架秩乘法及实维乘法 |
| 实际两因子产品正规形 | 所选复型的每个实际扇区、维数 $n_i,n_j,n_in_j$、实际态／效应乘积、全域配对与单位；固定输出酉和固定输入转置的正规形，含标量因子边界 |

这些条件桥的来源逐项沿VII卷103.1所链的
[least confirmation、谱性及面保纯接口](../../../Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge)
与[实际复合及正规形接口](../../../Library/QuantumStates/barnumhilgert2019spectral.md#actual-two-factor-products-after-complex-type-selection)
使用，不把它们改成三份 Jordan 分类，也不把整条桥归给一个成熟分类定理。
种子要求仍仅为 $\Delta_{r,2}\in C_3$，其归一态为 $\Delta_{r,2}/2$；
不预设原三份极端性。

辅助量子对象记 $Q_k$，实际扇区对象记 $A_i$，分别实现为
$\operatorname{Herm}_k$、$\operatorname{Herm}_{n_i}$。
$Q_k$ 的矩阵维数不计作一条实际原腿；$A_iA_j$ 也不改型为一个九维实际对象。
在任何有限对象字 $w$ 上，记全转置为 $T_w$，普通迹对偶为 $K^*$，并写

$$
b_w(X,Y)=\operatorname{Tr}(X^T Y),\qquad
K^\vee=\{Y:b_w(X,Y)\ge0\ (X\in K)\}=T_w(K^*).
\tag{123.1}
$$

$b_w$ 是非退化实双线性型，不是 Hermitian 实空间上的正定内积。
例如 $Y=\left(\begin{smallmatrix}0&-i\\i&0\end{smallmatrix}\right)$ 满足
$b(Y,Y)=-2$。对实线性 Hermitian 保持映射，$b$ 伴随为
$\Phi^\flat=T\Phi^\dagger T$；特别地
$\operatorname{Ad}_A^\flat=\operatorname{Ad}_{A^T}$，尺寸反向，仍为 CP。
这里 $\operatorname{Ad}_A(X)=AXA^*$，$A$ 可为任意复矩形矩阵。
这种形式对偶不把 $X^T$ 宣布为 PSD；源图式中的帽也不声明物理效应事件存在。

**定理 123.2（同一源实现上的补全与完整五份定义前缀）。** 对定义123.1的任意固定数据，
存在一个同时定义于所有有限对象字的闭尖生成锥族 $E(w)$，迹在每个非零正向量上严格为正，
满足 $E(w)^*=T_wE(w)$。存在一个所有正整数矩阵尺寸上的共同双边族
$\mathcal K_{m,n}$，使

$$
\begin{aligned}
\mathrm{SN}_2(m,n)&\subseteq\mathcal K_{m,n}\subseteq\mathrm{BP}_2(m,n),
&\mathcal K_{m,n}^*&=T\mathcal K_{m,n},\\
E(Q_k)&=\mathrm{PSD}_k,
&E(Q_kA_i)&=\mathcal K_{k,n_i},\\
E(A_iA_j)&=\mathrm{PSD}_{n_in_j},
&\min(m,n)\le2&\ \Longrightarrow\ \mathcal K_{m,n}=\mathrm{PSD}_{mn}.
\end{aligned}
\tag{123.2}
$$

$\mathrm{SN}_2$ 是所有复 Schmidt 秩至多二的 dyad 生成的闭锥，
$\mathrm{BP}_2=\mathrm{SN}_2^*$。
$\mathcal K$ 同时在两个因子上的任意独立复矩形合同及 CP 映射下保持正性。
特别地，同一族
$H_{a;k}=E(Q_kA_s^a)$，$n_s=3$，满足
$H_{0;k}=\mathrm{PSD}_k$、$H_{1;k}=\mathcal K_{k,3}$、$H_{2;1}=\mathrm{PSD}_9$。

该实现保持全部源箭头、实际位置置换与逆、规范重括号，
以及任意旁观对象字中的所有标量角、qubit 角、有限寄存器码和原中心扇区的正 retract，
连同完整迹对偶、proper 上界和真实零扩张。
在每个原 $W_N=V^{\otimes_{\mathbb R}N}$ 上令

$$
C_N=\bigoplus_{(i_1,\ldots,i_N)\in I^N}E(A_{i_1}\cdots A_{i_N}),
\qquad u_N=\sum_{I^N}\operatorname{Tr}.
\tag{123.3}
$$

则 $C_1,\ldots,C_5$ 是定义123.1的完整定义前缀，保留给定种子与全部低二份供应输入。
每个VII卷定义105.2的字面原码角恰为 $D_s=\mathcal K_{3,3}$，其整个迹一基的重叠区间为

$$
\left\{\operatorname{Tr}(Px):x\in D_s,\ \operatorname{Tr}x=1\right\}
 =[-1/15,2/3],\qquad t=2/3.
\tag{123.4}
$$

所有对象字上的 $E$ 是同一个部分满足原产品公理的候选族。
定理断言的是全部次数至多五的原定义条件及下述直接证明的源／retract 后果；
它不把全有限公理的所有低端点推论都列作五份定义条件。

**证明。** 先构造双边资源，再在同一源中强制所有接口相容。

（一）双边初始系统与同时补全。沿VII卷105.2的记号把九维角内的 $R$ 另写为 $\Omega$，令

$$
\begin{aligned}
\eta&=\sum_{a=0}^2|aa\rangle,&\Omega&=|\eta\rangle\langle\eta|,&P&=\Omega/3,\\
B_-&=(2I-\Omega)/5,&B_+&=(I+5\Omega)/8,\\
G_{m,n}&=\overline{\mathrm{SN}_2(m,n)+
 \operatorname{cone}\{(A\otimes B)B_-(A\otimes B)^*:
 A:\mathbb C^3\to\mathbb C^m,\ B:\mathbb C^3\to\mathbb C^n\}}.
\end{aligned}
\tag{123.5}
$$

Schmidt 分解与 Cauchy–Schwarz 给
$|\langle\eta,v\rangle|^2\le2\|v\|^2$，只要 $v$ 的 Schmidt 秩至多二。
所以 $B_-$ 二块正；由 $A^*\otimes B^*$ 拉回测试向量不增加 Schmidt 秩，
每个轨道元素亦二块正。
令 $\Gamma_1$ 仅为矩阵计算中的第一因子部分转置，$F$ 为三维交换矩阵，则

$$
\begin{aligned}
\Gamma_1(B_-)&=(2I-F)/5\succeq0,\\
\Gamma_1\bigl((A\otimes B)B_-(A\otimes B)^*\bigr)
 &=(\overline A\otimes B)\frac{2I-F}{5}(\overline A\otimes B)^*\succeq0.
\end{aligned}
\tag{123.6}
$$

中间矩阵的本征值为 $1/5,3/5$；该等式包括任意复矩形 $A,B$。
两个轨道元素 $X,Y$ 因而满足
$\operatorname{Tr}(XY)=\operatorname{Tr}(\Gamma_1X\,\Gamma_1Y)\ge0$。
两个 $\mathrm{SN}_2$ 元素的迹配对非负，因为二者 PSD；
混合配对由二块正性非负。非负和与闭包保持这些不等式。
全转置通过 $A,B$ 的复共轭保持 $G$，故 $G\subseteq G^\vee$。
独立矩形合同把其生成元送到相同类型生成元；因此这是一个共同系统，
不是按尺寸各自无关选取的锥。

这里使用 Netzer，[*Self-Dual Cone Systems and Tensor Products*, arXiv:2408.07389v1](https://arxiv.org/abs/2408.07389v1)，
定理2.2，作为本构造的中间步骤。其准确条件是 star-autonomous stem
$S:\mathcal C\to\mathrm{FVec}_{\mathbb R}$、每个内禀锥 proper、
有限维实基空间 $X$ 经选定正定配对与 $X'$ 识别，以及一个 $S$-system
$G\subseteq G^\vee$；结论是同时的 $G\subseteq E=E^\vee\subseteq G^\vee$。
此处 $X=\mathbb R$，该正定识别只是标量乘法。
层上的 $b$ 来自对象对偶，不承担这个基空间上的正定性条件。

具体 stem 为两个 operator stem 的乘积，源为
$\mathrm{FHilb}^{\mathrm{op}}\times\mathrm{FHilb}^{\mathrm{op}}$，
层为 $\operatorname{Herm}_m\otimes_{\mathbb R}\operatorname{Herm}_n$，
箭头实现为独立合同；计算共轭基下的对象对偶正是(123.1)。
乘积 stem 的 cointrinsic 锥为可分锥，intrinsic 锥为乘积块正锥 $\mathrm{BP}_1$。
这一对应复用 De les Coves–van der Eyden–Netzer，
[*Beyond Operator Systems*, arXiv:2312.13983v1](https://arxiv.org/abs/2312.13983v1)，
Example 2.10(ii)、Lemma 3.5及§4.2：乘积类别仍 star-autonomous，
$B(c_1,c_2)=B_1(c_1)\otimes_{\min}B_2(c_2)$、
$A(c_1,c_2)=A_1(c_1)\otimes_{\max}A_2(c_2)$。
乘积 dyad 张成整个实空间，乘积测试分离每个 Hermitian 元素，故这两个锥均 proper。
Netzer 的全部条件已满足，得到一个同时的
$G\subseteq\mathcal K=\mathcal K^\vee\subseteq G^\vee$。
由 $\mathrm{SN}_2$ 的包含及其全转置不变性，得(123.2)的双边夹逼；
若一侧尺寸至多二，两端锥都等于 PSD。
源箭头给独立矩形合同正性，非负和给两侧任意 CP 正性。

每个 $\mathcal K$ 包含满维可分锥且包含于尖的 $\mathrm{BP}_1$，所以 proper。
若块正 $X$ 的迹为零，把任意乘积单位向量扩为乘积正交基。
所有基对角读数非负而总和为零，故该向量的读数为零。
乘积 dyad 张成，遂 $X=0$。因此迹在 $\mathrm{BP}_1\setminus\{0\}$ 上严格正，
$\mathcal K$ 的整个迹一基紧；其纯态与效应分别取全部极点和整个迹对偶区间。

端点不另作表示分类。向量
$(|00\rangle+|11\rangle)/\sqrt2$ 的 dyad 在 $\mathrm{SN}_2$ 内，
$U\otimes\overline U$ 平均的迹为一、$P$ 读数为 $2/3$，因而等于 $B_+/3$。
这里直接复用VII卷105.3的各向同性平均及其原始来源
Terhal–Horodecki，[*A Schmidt number for density matrices*, quant-ph/9911117v4](https://arxiv.org/abs/quant-ph/9911117v4)，
式(6)、(9)与秩二阈值。故 $B_-,B_+\in\mathcal K_{3,3}$；
二者实，亦在普通迹对偶内。
其迹均为三，$\operatorname{Tr}(B_-B_+)=0$。
对任意迹一 $X\in\mathcal K_{3,3}$，这两次全对偶测试给

$$
\frac{2-3\operatorname{Tr}(PX)}5\ge0,\qquad
\frac{1+15\operatorname{Tr}(PX)}8\ge0.
\tag{123.7}
$$

$B_-/3=\tau_{-1/15}$、$B_+/3=\tau_{2/3}$ 取得两端点；
凸性给整个区间，严格正迹与VII卷105.4的参数端点论证给
$\mathcal K_{3,3}\cap\operatorname{span}_{\mathbb R}\{I,\Omega\}
=\operatorname{cone}\{\tau_{-1/15},\tau_{2/3}\}$。
这里仅调用VII卷105.4中对一般锥所写的端点计算，不把它的全原模型前提授给 $\mathcal K$。
同样复用VII卷105.5的预算计算：$W=I-\Omega/2=(5/2)B_-$ 的整个基上读数为 $[0,11/10]$，
所以
$E_0=(10/11)W=(25/11)B_-$ 为完整 proper 效应，$E_0(P)=-5/11$。
这个负值在被排除的 $P$ 上，不是已容许状态的负概率。

（二）任意复 Bell 路径的统一收缩。对所有正整数 $m,n,d$、
$X\in\mathcal K_{m,d}$、$Y\in\mathcal K_{n,d}$，令

$$
Z_{i\alpha,j\beta}=\sum_{a,b=1}^d X_{ia,jb}Y_{\alpha a,\beta b}.
\tag{123.8}
$$

共轭该式并交换 $a,b$ 得 $Z$ Hermitian。
任意复系数矩阵 $V:\mathbb C^n\to\mathbb C^m$ 对应
$v=\sum_{i,\alpha}V_{i\alpha}|i\alpha\rangle$；逐指标展开给

$$
\begin{aligned}
\langle v,Zv\rangle
 &=\sum_{i,j,\alpha,\beta,a,b}
 \overline V_{i\alpha}V_{j\beta}X_{ia,jb}Y_{\alpha a,\beta b}\\
 &=\operatorname{Tr}\!\left[X^T(\overline V\otimes I_d)
 Y(\overline V\otimes I_d)^*\right]\ge0.
\end{aligned}
\tag{123.9}
$$

最后一个不等式使用寄存器矩形合同正性和 $\mathcal K^\vee=\mathcal K$。
所以 $Z\succeq0$，量词遍历全部复 $V$。
不等实际尺寸间的纯矩形帽可把其复系数矩阵吸收到实际一体合同中，
一般 CP 路径则作有限 Kraus 和；反向弯曲使用
$\operatorname{Ad}_A^\flat=\operatorname{Ad}_{A^T}$，不会失去 CP。

这个步骤的映射锥字典是 Girard–Kye–Størmer，
[*Convex cones in mapping spaces between matrix algebras*, arXiv:2002.09614v2](https://arxiv.org/abs/2002.09614v2)，
定理3.1、推论3.2，与 Kye，
[*Compositions and tensor products of linear maps between matrix algebras*, arXiv:2204.02516v2](https://arxiv.org/abs/2204.02516v2)，
定理3.1、3.2。它们的条件是 Hermitian 保持映射的闭凸锥，
在所用对偶刻画中位于正映射内并在左右 CP 复合下不变；
此处 Choi 像由 $\mathrm{BP}_1$ 包含与双边不变性满足这些条件。
其结论刻画 $b$ 对偶中的 CP 复合或映射张量积正性，
不声称两个 Choi 元素的张量积属于另一个指定的高阶锥。
上述逐指标证明直接固定了复共轭和尺寸，不以普通迹伴随替换 $b$ 伴随。
2002.09614v2式(1)的双线性配对按其公式使用；
该页称其在 Hermitian 实空间上为内积的句子不满足正定性，
反例已由(123.1)后的 $Y$ 给出，这一句不作为任何步骤的前提。

令 $x=\operatorname{Tr}X>0,y=\operatorname{Tr}Y>0$。
由块正性，实际边缘
$\rho_X=\operatorname{Tr}_{\rm register}X$、$\rho_Y=\operatorname{Tr}_{\rm register}Y$
为 PSD：每个向量读数都是乘积读数之和。
于是

$$
0\le\operatorname{Tr}Z=\operatorname{Tr}(\rho_X^T\rho_Y)\le xy.
\tag{123.10}
$$

归一输入 $X/x,Y/y$ 配 proper 实际帽 $\beta_d/d$ 后，输出为 $Z/(dxy)$，
成功质量在 $[0,1/d]$。只有 $\operatorname{Tr}Z>0$ 才有条件态
$Z/\operatorname{Tr}Z$；零输出不作条件化。
此处原帽缩放沿VII卷104.4，未把正标量重缩放改称确定性事件。
VII卷106.8、VII卷106.9已处理其指定门户网络及预算；这里复用它们的路径／闭环归约机制，
新增输入是全部共同 $\mathcal K$ 资源和(123.9)的全尺寸保证，
不把已发表的门户滤波阈值或有限网络边界再列为新定理。

（三）共同源与所有闭标量。取一个小的自由对称紧闭类别 $\mathcal D$，
其对象由实际 $A_i$ 和量子 $Q_k$ 的有限字及单位生成。
各对象固定计算自对偶，数值实现 $S:\mathcal D\to\mathrm{FVec}_{\mathbb R}$
发送到上述实 Hermitian 张量空间。量子字与 $Q_{k_1\cdots k_a}$
之间加入规范 CP 同构及其逆，$Q_1$ 与张量单位同构。
杯实现为未归一 Bell dyad，帽为(123.1)的 $b$，矩阵单位直接给两条 snake 为恒等。
这使 $S$ 强对称单式且保持紧对偶，因而是 star-autonomous stem，
所用定义沿2312.13983v1的 Definitions 2.8、2.9。

源生成箭头只取：量子字之间的全部普通 CP 映射；实际扇区间的全部一体 CP 映射，
包括复矩形单 Kraus 合同；各实际杯帽；以及每个
$X\in\mathcal K_{k,n_i}$ 的形式态箭头
$s_X:\mathbf1\to Q_kA_i$。所有紧对偶箭头自动包括。
量子杯帽亦在量子 CP／紧结构内。
这里没有把任意多条实际腿上的集体 CP 映射列作生成箭头。
形式态用来生成数学锥，不宣告原物理制备或事件菜单增加。

考虑任意有限闭源图。弯曲端口，把每个混合生成元露为其态张量，
并展开一体实际 CP 的 Kraus 和；每个混合张量只有一条实际端口，
其余实际顶点度为二，普通实际态／效应为端点。
故实际子图的每个连通分量是路径或环。
反向实际映射的 $b$ 伴随仍 CP。
两个混合端点间的路径由(123.9)给出其全部量子端口上的 PSD 张量；
普通实际端点是 $k=1$ 的情形，其块正测试也给 PSD 量子输出。
只有普通 CP 数据的实际环，按 Kraus 展开取值为
$\sum_\nu|\operatorname{Tr}L_\nu|^2\ge0$。

删去这些分量后，余图是任意量子 PSD 张量及 CP 箭头组成的网络。
每个 PSD 张量作有限 dyad 分解，每个 CP 箭头作 Kraus 展开；
固定每项，ket 收缩给一个复振幅，bra 收缩给其共轭，故闭值为绝对值平方。
求和仍非负。跨不同实际路径的纠缠量子布线一直保留，
论证不要求寄存器测试逐站独立，也不要求图有因果定向。
因此每个闭源标量都非负。

记

$$
\begin{aligned}
B_{\mathcal D}(w)&=\overline{\operatorname{cone}
 \{S(s)(1):s:\mathbf1\to w\}},\\
A_{\mathcal D}(w)&=\{z:S(e)(z)\ge0\text{ 对所有 }e:w\to\mathbf1\}.
\end{aligned}
\tag{123.11}
$$

源态与源效应复合即闭图，所以
$B_{\mathcal D}\subseteq A_{\mathcal D}=B_{\mathcal D}^\vee$。
$B_{\mathcal D}$ 在全部源箭头下正且闭，确为一个 $S$-system。
每个初等因子的乘积 PSD 态及其紧对偶效应都是源图；它们的 dyad 张成整个实空间。
因此 $B_{\mathcal D}$ 含满维可分锥，$A_{\mathcal D}$ 包含于尖的乘积块正锥。
闭标量非负性又使 $A_{\mathcal D}$ 含 $B_{\mathcal D}$，故二者在每个字上均 proper。
（一）的乘积基读数论证也在每个有限字上证明迹严格正。
这逐字验证了内禀锥条件，未仅检查几个低阶对象。

再次把 Netzer 定理2.2用于同一 $B_{\mathcal D}$，基空间仍为 $\mathbb R$，得

$$
B_{\mathcal D}\subseteq E=E^\vee\subseteq A_{\mathcal D}.
\tag{123.12}
$$

于是全部固定源箭头均正，有源逆的箭头其逆也正，且普通迹对偶恰为 $TE$。
可分／块正夹逼给每个 $E(w)$ 的 proper 性、严格正迹和紧的整个归一基。
所有极点与整个 proper 区间均取入，未选出一部分测试作为全对偶。

（四）同一实现上的精确低类型。源中已有全部 $\mathcal K_{k,n_i}$ 态及其紧对偶效应，
所以在 $Q_kA_i$ 上，下界含 $\mathcal K$，上界含于
$\mathcal K^\vee=\mathcal K$，迫使 $E=\mathcal K$。
全量子态与效应同样迫使 $E(Q_k)=\mathrm{PSD}_k$。
对实际 $A_iA_j$，每个复向量都可写为
$(I\otimes A)\sum_{a=1}^{n_i}|aa\rangle$，
$A:\mathbb C^{n_i}\to\mathbb C^{n_j}$ 为复矩形矩阵。
故每个纯 dyad 是实际杯后接一体合同的源态；有限谱和给整个 PSD 锥。
其紧对偶效应也都是源效应，反向夹逼给
$B_{\mathcal D}(A_iA_j)=E(A_iA_j)=A_{\mathcal D}(A_iA_j)=\mathrm{PSD}_{n_in_j}$。
这不使用集体两实际腿 CP 生成元；$Q_1\simeq\mathbf1$ 给 $H_{2;1}=\mathrm{PSD}_9$。

（五）角、码、扇区与完整质量预算。对任意实际块中的秩 $d\le2$ 等距嵌入
$J:\mathbb C^d\to\mathbb C^{n_i}$，
$\operatorname{Ad}_J:Q_d\to A_i$ 和
$\operatorname{Ad}_{J^*}:A_i\to Q_d$ 的各自混合 Choi dyad 均有 Schmidt 秩至多二，
分别属于相应源生成资源。两个方向分别支付，不从一个方向的正性推断其迹伴随正。
对于尺寸一、二的实际对象，取满角即得与相应量子对象的数值同构。
张量任意旁观字仍是源箭头。
若相应嵌入、压缩记为 $j,q$，则

$$
qj=\mathrm{id},\quad p=jq,\qquad
q(E(w))=E(w'),\quad
E(w)\cap\operatorname{im}j=j(E(w'))=p(E(w)).
\tag{123.13}
$$

两条正箭头分别给两侧包含，$qj=\mathrm{id}$ 给等号，
因此没有用任意子空间交来猜测角锥。
重型为量子字后，允许其上任意集体量子 CP。
所有有限 $k$ 可嵌入足够多的 qubit，量子等距码与其压缩也都是源箭头。
尤其包括原实码 $c$、码投影 $cc^*$ 和把 $11$ 真正送零的 $c^*$，
以及任意复秩一／秩二角与所有实际扇区的进出。
将扇区逐字直和后，中心选取与补同样正，所有原标签保留。

对任意收缩 Kraus 矩阵 $A$，迹亏损是输入的 PSD 效应 $I-A^*A$。
它与所有旁观迹效应的张量积是一个源效应，因而在整个 $E$ 上非负。
所以压缩及其旁观扩张不增迹，等距嵌入保迹。
对(123.13)的整个角对偶 $f$，$fq$ 在整个母锥上正，并沿 $j$ 精确限制为 $f$。
若 $0\le f\le\operatorname{Tr}_{w'}$，则

$$
0\le fq\le\operatorname{Tr}_{w'}q\le\operatorname{Tr}_w.
\tag{123.14}
$$

反向限制母锥 proper 效应也在角的全 proper 区间内，故全对偶和全上界均精确延拓。
这直接给VII卷104.11的指定角与零扩张结论在本源族中的对应，
不借用其全有限原 Choi 等价来授予未知的补全新增映射正性。

给定相位的三个秩二嵌入将量子 GHZ dyad 送到原 $\Delta_{r,2}$，
每条腿使用原指定向量，所以它是同一个种子，迹恰为二。
按VII卷104.4的预算，归一 $\Delta_{r,2}/2$ 经 proper 确认切片得到
$\Omega_{r,2}/4$，质量 $1/2$；不把它改称归一满维杯。
各实际满杯 $\Omega_i$ 的迹是 $n_i$，帽 $\beta_i/n_i$ proper。
全部对角块杯之和的迹仍为 $R=\sum_i n_i$，全帽 $\beta/3$ proper，
因为每块 $0\preceq\Omega_i\preceq n_iI\preceq3I$，非对角扇区的帽为零。
归一全杯与该帽的 $m$ 次 snake 预算仍是 $(3R)^{-m}$。
这些均为带原质量的子归一资源，不表示确定性后选择或制备事件。

（六）完整原低二份数据和每个五份分块。(123.3)在原实张量坐标中逐扇区直和，
源对称给全部原置换与逆，重括号就是规范识别，原配对与张量迹单位完全不变。
其 $C_1,C_2$ 是全部对齐块 PSD 锥，全部纯点是在单个扇区的秩一迹一 dyad，
全效应是逐块 $[0,I]$。
若 $p$ 为任一这样的纯点，$F$ 为整个 proper 区间中确认它的效应，
则 $Fp=p$ 且 $F-p\succeq0$，而 $p$ 本身为确认效应。
故对全部低份正向量

$$
T_p^{(q)}(x)=\operatorname{Tr}(px),\qquad q=1,2.
\tag{123.15}
$$

互反与线性立刻给整个 $S_2$，包括纠缠二份纯点、任意有限混合、零权和重复标签。
谱框架是完整正交秩一族，面滤波为正投影 $X\mapsto PXP$，纯输入输出为纯或零；
这给定义123.1第一接口的 least、互反、谱、projectivity、面保纯及迹 Jordan 数据。
实际 $(W_1,W_1,W_2)$ 的态／效应双乘积、单位、全域配对、局部层析均为原块矩阵乘积，
所有中心限制保持它们；每个扇区框架秩为 $n_i,n_j,n_in_j$，
实维为相应平方，故第二接口的秩／维数乘法全部成立。
第三接口的正规形可直接取 $U=I$、输入转置位均为零，包括标量因子。
因此没有省略任何低份供应输入，也没有借用高份分类或 $S_3$。

关键是整个一份、二份 $E$ 已由数值源态生成，且 PSD 的每个元素实际都是有限源 dyad 和。
若 $y$ 为其中任意元素，$x\in E(w)$ 为任意补全态，
箭头 $\mathrm{id}_w\otimes s_y$ 及非负和给 $x\otimes y\in E(wv)$。
所以只要 $\min(a,b)\le2$，整个最小锥界成立，任意总次数皆然。
写任意全迹对偶 $f=T_ax\in C_a^*$、$g=T_by\in C_b^*$，则对全部 $z\in C_{a+b}$，

$$
(f\otimes g)(z)=b_{a+b}(x\otimes y,z)\ge0.
\tag{123.16}
$$

这里 $x\otimes y$ 的成员关系正是刚证明的最小界，
所以最大界使用了整个原对偶，而非选出的效应菜单。
不连续位置由原置换运输；空侧由单位处理。
全部非平凡次数至多五的二分逐项为

$$
\begin{array}{c|l}
2&1+1\\
3&1+2,\ 2+1\\
4&1+3,\ 2+2,\ 3+1\\
5&1+4,\ 2+3,\ 3+2,\ 4+1.
\end{array}
\tag{123.17}
$$

每项有一侧至多二，故无遗漏的原截断分块；迭代分块由这些包含组合得到。
原 $i_s,q_s$ 正是（五）的扇区／两 qubit／实三码 retract，
其像内的字面锥是同一 $E(Q_3A_s)=\mathcal K_{3,3}$。
因此(123.7)的整个基端点、普通全对偶与 $E_0$ 的 proper 延拓
确实属于该五份前缀的原三份角，得(123.4)。
$\mathcal K_{3,3}$ 在这里是一寄存器一实际端口，始终不等同于 $E(A_sA_s)$。

（七）补全新增元素的确切边界。任意次数的源态闭锥因子都可按源箭头附加；
闭包由张量连续性处理。这包括全部一／二份态、全部量子态、
整个一实际端口 $\mathcal K$、原种子以及所有有限源协议。
然而 $E$ 新增的 $x\in E(w)$ 不自动成为 $\mathcal D$ 的箭头
$\mathbf1\to w$。所以两个任意补全新增因子的乘积未由此论证支付。
在原次数中，第一个这种分块是

$$
C_3\otimes_{\min}C_3\subseteq C_6,
\quad\text{即}\quad
b_6\bigl(\tau_\pi(x\otimes y),z\bigr)\ge0
\quad(x,y\in C_3,\ z\in C_6,\ \pi\text{ 为原位置置换}).
\tag{123.18}
$$

因 $C_N^*=T_NC_N$，该条件也支付对应的整个普通对偶最大界；
六份中的 $1+5,2+4,4+2,5+1$ 已由（六）支付。
Netzer 定理2.2只给固定源箭头的函子正性；其 Definition 3.1、Theorem 3.2
的自对偶二元张量函子也不供应本题预指定的结合性和所有原产品律。
因此(123.18)尚未证明，也未证明其失败；更高的双侧次数至少三的分块同样未付。
全有限原旁观 Choi 等价对任意补全新增映射可消费更高次数的中间对象，
即使其显示输入／输出较低，也不是本定理五份定义包的结论。∎

**命题 123.3（两种错误扩张的有限反例）。** 定理123.2的共同双边族不能在
同时合并两个矩阵指标的意义下对任意自身张量积封闭。
另一个提案 $H_{2;k}=\mathcal K_{k,9}$，把两个实际 qutrit 合成一个九维实际对象，
不能保持本定理的全部原 qubit 角对应。

**证明。** 写 $\Omega_d=|\sum_{a=0}^{d-1}aa\rangle\langle\sum_{a=0}^{d-1}aa|$。
$\Omega_2\in\mathcal K_{2,2}=\mathrm{PSD}_4$。
若合并双指标的自身张量积封闭，将
$\Omega_2\otimes\Omega_2$ 重组即得 $\Omega_4\in\mathcal K_{4,4}$。
两侧分别压到前三条坐标是已允许矩形合同，遂
$\Omega_3\in\mathcal K_{3,3}$，但其归一 $P$ 重叠为一，违反(123.4)的 $2/3$ 上界。

对于合并九维提案，取 $R_0=\mathbb C^2,A=B=\mathbb C^3$，以及

$$
\psi=|0,0,0\rangle+|0,1,1\rangle+|1,2,0\rangle
 \in R_0\otimes A\otimes B.
\tag{123.19}
$$

它在 $R_0\mid AB$ 的 Schmidt 秩为二，故 dyad 在
$\mathcal K_{2,9}=\mathrm{PSD}_{18}$ 内。
$B$ 的支撑只用前两维原角。将该角重型为量子寄存器并按 $(R_0,B)\mid A$ 排序，
相同向量变为
$|00\rangle|0\rangle+|01\rangle|1\rangle+|10\rangle|2\rangle$，Schmidt 秩为三。
其归一 dyad 正是 $\mathcal K_{4,3}$ 三码内的 $P$，
$\operatorname{Tr}(B_-P)=-1/5$，由(123.7)的全对偶测试被排除；
proper 测试 $E_0$ 的读数为 $-5/11$。
故合并九维提案连这个原角就不能相容。
两例只否定所写扩张机制，不反驳原全有限 $\mathsf{Fusion}_3$，
也不证明(123.18)对定理123.2的同类型共同族失败。∎

**定理 123.4（固定数据、固定间隙的完整前缀紧致性）。** 固定定义123.1的
原 $V$、全部扇区、配对与单位、对齐的整个 $C_1,C_2$、三条低份条件供应数据、
同一含相位种子、全部原码映射 $i_s,q_s$、$P$，以及一个数值 $t_0<1$。
下列两条件等价：

1. 对每个整数 $M\ge3$，存在具有这些固定数据的完整定义前缀
   $C_1^{[M]},\ldots,C_M^{[M]}$，满足
   $q_s^*(t_0I-P)\in(C_3^{[M]})^*$。
2. 存在具有这些相同数据的VII卷定义102.1全有限原层级，保留整个 $S_2$、
   三条供应与原种子，而且其整个实际角满足 $t\le t_0$。

固定的所有最大块可同时要求上述间隙；由原一体块对应，它们的实际极值相同。
各有限前缀之间不要求预先相容，也不要求来自定理123.2的某个特定补全。
若前缀另已指定原角／扇区／码的固定正映射与预算，这些闭包含也同时保留；
未列为有限输入的原已付映射，在取得完整基本层级后按原定理恢复。

**证明。** 全层级限制到前缀给第一条件；原已付映射和预算直接沿VII卷104.7、VII卷104.11、VII卷105.3使用。
证明反向时，所有极限都在同一固定实向量空间和单位下取。

（一）固定紧包络。记

$$
S_N=\underbrace{C_1\otimes_{\min}\cdots\otimes_{\min}C_1}_{N},\qquad
M_N=\underbrace{C_1\otimes_{\max}\cdots\otimes_{\max}C_1}_{N}.
\tag{123.20}
$$

迭代原双界使每个 $M\ge N$ 的 $C_N^{[M]}$ 夹在 $S_N,M_N$ 之间。
令 $d=\dim V$，取 $V^*$ 的基 $g_1,\ldots,g_d$。
因 $u\in\operatorname{int}C_1^*$，可取共同 $\epsilon>0$，使

$$
f_{j,\pm}=\frac{u\pm\epsilon g_j}{2d}\in C_1^*,\qquad
\sum_{j,\pm}f_{j,\pm}=u.
\tag{123.21}
$$

它们张成 $V^*$。其全部 $N$ 次乘积张成 $W_N^*$，在
$M_N^*=(C_1^*)^{\otimes_{\min}N}$ 内，且和为 $u_N$。
有限张成族的严格正系数和在其生成锥内部，故
$u_N\in\operatorname{int}M_N^*$。
这给固定的严格正质量包络，不是把严格正性未经控制地传给极限。

于是 $B_N^{\max}=\{x\in M_N:u_N(x)=1\}$ 是紧凸集，
$B_N^{\min}=\{x\in S_N:u_N(x)=1\}$ 非空紧凸。
位于两者之间的非空紧凸子集的族，在 Hausdorff 距离下紧：
它是紧空间 $B_N^{\max}$ 的非空紧子集超空间中，
由凸性与两个包含关系切出的闭子族。
沿 $M\to\infty$ 对 $N=1,2,\ldots$ 逐项取子列，再取对角子列，
得每个固定次数的基 $B_N^j\to B_N$。
令 $C_N=\operatorname{cone}(B_N)$。
由固定包络，$C_N$ 闭、尖、迹严格正；因含 $S_N$ 而生成整个 $W_N$。
整个归一基就是 $B_N$。

（二）全部最小界与全对偶最大界。对任意极限归一
$x\in B_a,y\in B_b$，取同一子列的 $x_j\in B_a^j,y_j\in B_b^j$ 收敛到它们。
前缀最小界使 $x_j\otimes y_j\in B_{a+b}^j$，其单位质量为一，
故极限 $x\otimes y\in B_{a+b}$。
伸缩、相加、闭包给整个最小锥界。

对任意全极限对偶 $f\in C_a^*$，令

$$
\epsilon_j(f)=\max\{0,-\min_{x\in B_a^j}f(x)\},\qquad
f_j=f+\epsilon_j(f)u_a.
\tag{123.22}
$$

Hausdorff 收敛使 $\epsilon_j(f)\to0$；$f_j\in(C_a^j)^*$，且 $f_j\to f$。
同样对全部 $g\in C_b^*$ 取 $g_j$。
对 $z\in B_{a+b}$ 取 $z_j\in B_{a+b}^j$ 收敛到它，
原前缀最大界给 $(f_j\otimes g_j)(z_j)\ge0$。
取极限得 $(f\otimes g)(z)\ge0$，量词遍历整个两个对偶；伸缩给全部最大界。
固定位置置换及其逆为连续保质量线性映射，分别传给极限。
规范重括号、产品配对、单位一直是相同向量空间的数据，不另作极限选择。
所以所有不连续位置及所有次数的原分块均成立。

（三）整个 proper 区间与全部极点。效应定义为整个极限对偶区间，
而且这些区间确实收敛。若 $f\in[0,u_N]_{C_N^*}$，令

$$
\delta_j=\max\{0,-\min_{B_N^j}f,\ \max_{B_N^j}f-1\},\qquad
\widetilde f_j=\frac{f+\delta_j u_N}{1+2\delta_j}.
\tag{123.23}
$$

则 $\delta_j\to0$，$\widetilde f_j\in[0,u_N]_{(C_N^j)^*}$ 且趋向 $f$。
反向任一收敛前缀效应在极限基上保留两侧不等式。
所有这些区间都包含在共同紧区间 $[0,u_N]_{S_N^*}$ 内；
$S_N$ 满维保证该区间有界。
所以完整 proper 区间既没有遗失效应，也没有遗失单位补的预算。

高份纯集定义为极限整个基的全部极点，不声称极点本身连续变化。
所要求的普遍比较仅为 $S_2$，而 $C_1,C_2$ 及其完整区间、纯集均精确固定。
于是原 least 确认下确界、纠缠纯点、全部有限准备、零权、重复标签与整个 $S_2$
完全不变；没有对未要求的高份 $S_N$ 作虚假的闭性断言。
三条供应中的 least／互反／谱／projective／面保纯数据也是固定的低份数据。
实际 $(W_1,W_1,W_2)$ 的态／效应产品、单位、全域配对、分离、
中心限制、框架秩／维数乘法、固定复型及两因子正规形连同标量边界，
由固定低份与已证全部双界保留。因此VII卷103.1、VII卷104.1的每个完整输入均保留。

（四）同一源、固定映射与原 retract。固定的 $\Delta_{r,2}$ 在每个适当前缀的
$C_3^j$ 内，且质量为二，故在极限 $C_3$ 内；原相位和归一质量未改变。
对任意所指定固定线性映射 $F$，若
$F(C_a^j)\subseteq C_b^j$，对归一输入作上述逼近，输出的质量也收敛。
若极限质量为正，按质量归一后用目标固定紧基包络取极限；
若质量趋零，包络给 $\|F(x_j)\|\le c_bu_b(F(x_j))\to0$。
所以 $F(C_a)\subseteq C_b$。所有固定旁观扩张在足够长前缀内同样处理，
迹预算是闭线性不等式，亦传给极限。

对于固定角锥 $K$，正包含 $j(K)\subseteq C$、$q(C)\subseteq K$
及恒等 $qj=\mathrm{id}$ 均闭，故给精确正 retract。
原三码角不预设固定的 $D_s$。完整基本层级、低份供应与同一种子已经取得，
VII卷104.7、VII卷104.11、VII卷105.3因而按原输入给固定投影 $p_s=i_sq_s$ 的
$p_s(C_3)\subseteq C_3$ 与不增迹预算；若前缀已指定它们，亦由上述固定映射闭性保留。
再定义 $D_s=i_s^{-1}(C_3)$，就有

$$
q_s(C_3)=D_s,\qquad
i_s(D_s)=p_s(C_3)=C_3\cap\operatorname{im}i_s.
\tag{123.24}
$$

用 $q_s$ 拉回整个角对偶和 proper 区间，按(123.14)得精确延拓。
这不是一般子空间交的连续性命题。
原已付扇区／角／码映射亦可在取得完整基本层级之后，
直接按VII卷104.7、VII卷104.11、VII卷105.3的原定理恢复，所有输入均已保留。
因此全部标量、二维、三维扇区，所有指定角与真正丢弃 $11$ 的码，
其整个对偶和预算均在同一个原实现内。

（五）同一个固定间隙。$q_s^*(t_0I-P)$ 是固定泛函，
对每个 $B_3^j$ 非负，故对极限 $B_3$ 非负。
由(123.24)，它恰表示

$$
\operatorname{Tr}(Px)\le t_0\operatorname{Tr}x
\qquad\text{对整个 }x\in D_s.
\tag{123.25}
$$

迹一角基紧，所以其实际最大值 $t\le t_0$。
原全有限定义包、全部低份供应和同一实际种子已逐项保留，得到第二条件。∎

**推论 123.5（逐固定间隙的有限障碍与首个未付次数）。** 对定理123.4的固定数据和
每个固定 $t_0<1$，若不存在 $t\le t_0$ 的全有限原层级，
则某个有限完整原定义截断已经排除该同一间隙。
当 $t_0\in[2/3,1)$ 时，这种截断的次数至少为六。

**证明。** 第一断言是123.4的逆否命题。
第二断言由123.2的完整五份前缀及 $t=2/3\le t_0$，直接排除次数至多五的障碍。
其第一项尚未证明的原产品关系正是(123.18)，
涉及两个独立补全新增三份对象及相应整个对偶和置换条件。
它不是一个已知 $\mathcal K$ 源因子与另一个对象的乘积，因为所有这些源因子已付。
未证明六份矛盾，也未证明每个更长完整前缀存在。

若只有每个截断上的 $t_M<1$，但 $t_M\to1$，不满足123.4的固定间隙前提。
同样，不存在任意 $t<1$ 的全模型，不自动给一个同时排除整个半开区间的统一有限次数；
这里的有限障碍逐个固定 $t_0$ 量化。
两种错误扩张的反例不改变此量词，也不证明原公理中融合命题的独立性。

Netzer 的系统补全与映射锥对偶、Schmidt 数／块正对偶、Choi/Kraus 和各向同性平均
在123.2中仅作所引成熟中间结果。
共同源的逐字相容、完整原五份定义包、两种错误扩张的本题反例，
以及保留全部原数据与整个对偶的固定间隙紧致性，是这些前置上的综合推导，
不主张文献新颖性或优先权。
原全目标仍要求从VII卷假设105.1证明 $t=1$，或核对一个 $t<1$ 的完整全有限原模型；
五份前缀和条件紧致性都未给出其中任一个结论。
静态锥构造未增加集体实际 CP、$S_3$、正逆、事件饱和或物理时间假设，
也未供应实际制备来源、记录／事件可得性、物理时间作用、钟校准与数值 $\hbar$ 的桥梁。∎

## 追加锚（本行以下为增补区）

## 124. 完整原全有限层级的普通匹配 dyad、全转置极性与匹配锥端点障碍

### 124.1 完整原前件与实际对象的固定

**假设 124.1（原 allN 的严格支路）。** 全部采用
[VII卷](QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md)
定义102.1、假设103.1、104.1及105.1的完整条件，另取原参数 $2/3\le t<1$。
具体地，固定非零有限维实空间 $V$；对每个整数 $N\ge1$ 保留同一个

$$
W_N=V^{\otimes_{\mathbb R}N},\quad C_N\subset W_N,\quad
u_N=u^{\otimes N},\quad
K_N=\{x\in C_N:u_N(x)=1\},\quad
P_N=\operatorname{ext}K_N,\quad
\mathcal E_N=[0,u_N]_{C_N^*}.
\tag{124.1}
$$

每个 $C_N$ 闭、尖、生成，$u_N$ 在每个非零正向量上严格正。
每个实际分块 $a+b=N$ 均满足原 min/max 双界；保留所有原位置置换及其逆、
不连续位置的分块、同一规范重括号、固定实张量产品配对和严格张量单位。
$K_N$、$P_N$ 和 $\mathcal E_N$ 始终是整个原对象，不替换为 PSD 部分或选定菜单。
空旁观者采用 $W_0=\mathbb R,C_0=\mathbb R_+,u_0=\mathrm{id}$。

唯一普遍比较前件仍是整个原 $S_2$：$T_p^{(2)}$ 由整个 proper 区间上
$f(p)=1$ 的下确界定义，对每个原 $p\in P_2$、每个有限原纯准备族
$q_\alpha\in P_2$、所有 $a_\alpha\ge0$ 且 $\sum_\alpha a_\alpha=1$，要求

$$
T_p^{(2)}\left(\sum_\alpha a_\alpha q_\alpha\right)
 =\sum_\alpha a_\alpha T_{q_\alpha}^{(2)}(p).
\tag{124.2}
$$

它包括纠缠二份纯态、零权和重复标签。三条条件 PAPER 供应逐条保留完整原输入：

| 条件接口 | 完整参数对应及保留条件 |
| --- | --- |
| 低二份 least confirmation 到 Jordan | 对原 $q=1,2$ 的 $(W_q,C_q,u_q,K_q,P_q,\mathcal E_q)$ 使用 least 确认、互反、同框架谱性、projectivity、正面投影及 filter purity，得到保迹 Jordan 表示与直和；$S_1$ 由纯旁观下降取得 |
| 唯一实际自复合的复型选择 | 只对实际 $(W_1,W_1,W_2)$ 使用正双线性态产品与效应产品、原单位、全域精确配对、乘积效应分离和局部层析，保留所有中心扇区限制、框架秩乘法及实维乘法，包括标量块 |
| 实际两因子产品正规形 | 对所选复型的每个实际扇区 $(i,j)$、维数 $n_i,n_j,n_in_j$，使用实际态／效应产品、全域配对及单位，取得固定输出酉与固定输入转置的正规形，保留标量因子边界 |

来源及各桥条件沿VII卷103.1所链的
[least confirmation 与谱性接口](../../../Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge)、
[面滤波保纯接口](../../../Library/QuantumStates/mullerududec2012selfduality.md#least-confirmation-forces-face-filter-purity)、
[中心扇区复合接口](../../../Library/QuantumStates/barnumhilgert2019spectral.md#sector-composites-without-a-connectedness-input)、
[单个实际自复合复型选择](../../../Library/QuantumStates/barnumhilgert2019spectral.md#complex-sectors-from-a-single-self-composite)及
[实际产品正规形](../../../Library/QuantumStates/barnumhilgert2019spectral.md#actual-two-factor-products-after-complex-type-selection)。
Barnum–Müller–Ududec 定理16只承担该条件桥中所引成熟分类步骤；
产品正规形沿 Xu–Zheng–Fošner，DOI
[10.1017/S1446788714000603](https://doi.org/10.1017/S1446788714000603)。
不把整条条件供应归给其中任一个无前提分类定理。

固定 $L=3$，保留全部原 $n_i\in\{1,2,3\}$ 扇区及原标签。
联合给定同一个含相位 $\mathsf F_{r,2}$ 种子，不取相位商，不要求原三份极端性。
采用VII卷104.7对齐后的同一局部保迹坐标
$V=\bigoplus_i\operatorname{Herm}_{n_i}$、$C_1=\mathsf D_1,C_2=\mathsf D_2$，
对高阶只作此坐标的张量幂识别，不预付高阶 PSD。
VII卷104.6的原杯帽与全局自身 Choi 判据、104.7的一体矩形合同及中心投影、
104.11的有限种子 qubit 寄存器、全部原旁观提升、全对偶和质量预算，均按原条件复用。
有限寄存器是实际种子角腿支付的码，不是免费的一条实际高维腿；
不授予集体实际 qutrit CP，也不授予正逆映射。

VII卷105.2的原码仍为
$ce_0=|00\rangle,ce_1=|01\rangle,ce_2=|10\rangle,c^*|11\rangle=0$，
参考在前、实际输出在后的 Choi 次序、实际基及其相位均固定。
在该实际角内沿用 $\eta=\sum_{i=0}^2|ii\rangle$、$R_3=|\eta\rangle\langle\eta|$、
$P=R_3/3$，以及

$$
\begin{aligned}
\tau_F&=\frac{1-F}{8}(I-P)+FP,&
\ell&=\frac{t-1}{9t-1}<0,&\lambda_*&=\frac1{3t},\\
p&=\frac{9t-1}{8},&r&=-\frac1{9t-1},&pr&=-\frac18,\\
M&=1-\frac\ell t
 =\frac{9t^2-2t+1}{t(9t-1)},&
W_{\lambda_*}&=I-\lambda_*R_3.
\end{aligned}
\tag{124.3}
$$

这些是同一个实际实现中的参数。整个原角迹一基的 $P$ 区间恰为 $[\ell,t]$；
$\tau_\ell,\tau_t$ 的原、对偶成员关系及原 proper 效应
$W_{\lambda_*}/M$ 的真正零扩张，均沿VII卷105.3—105.6复用。
对全原归一输入，其角接受质量 $b\in[0,1]$，读数上界为 $bM\le M$；
$b=0$ 时严格正单位迫使角输出为零。这保留了角外输入及零输出的完整预算。
VII卷106的受限网络结论仍只适用于其指定资源语法。

本章所有关于原 $H$ 的分类和夹逼均要求上述完整原 allN 前件。
第123章的共同 $E(w)$ 只具有该章已证明的部分产品律与五份前缀；
其中同名的 $H_{a;k}=E(Q_kA_s^a)$ 不能据此取得本章的 allN 结论。
尤其杯乘积、任意次压缩和全转置极性所用的全部阶数不能由五份前缀替代。

### 124.2 整个实际混合角、全对偶与压缩预算

**定义 124.2（实际角与普通 dyad）。** 任取有限 $a\ge0,k\ge1$，
选择 $a$ 条实际大小三的块腿；标签可不同，以104.7已支付的一体映射运输其基。
在 $m$ 条种子 qubit 角中取实计算码 $\mathbb C^k$，$2^m\ge k$；$k=1$ 允许 $m=0$。
令 $j$ 为这些实际块、种子角和码的等距 Hermitian 嵌入，$q=j^*$，$\mathsf p=jq$。
定义

$$
\begin{aligned}
H_{a;k}&=j^{-1}(C_{a+m})=q(C_{a+m})
 \subset\operatorname{Herm}((\mathbb C^3)^{\otimes a}\otimes\mathbb C^k),\\
H_{a;k}^*&=j^*(C_{a+m}^*),&q^*(H_{a;k}^*)&\subset C_{a+m}^*.
\end{aligned}
\tag{124.4}
$$

此 $H$ 是整个实际原锥的角，包括非 PSD 元素。
对向量 $\psi$，$r_i(\psi)$ 指单条实际腿 $i$ 对其余所有 Hilbert 因子的普通 Schmidt 秩；
寄存器对所有实际腿的 Schmidt 秩是另一个切口。
普通 dyad 指环境矩阵 $|\psi\rangle\langle\psi|$，不预称原极端射线或原纯点。
低锚为 $H_{0;k}=\mathrm{PSD}_k$、$H_{2;1}=\mathrm{PSD}_9$，
而 $H_{1;3}=D_s$ 按原码、实际腿的位置置换识别。
标量扇区、实际 qubit 扇区及实际三维腿内至多二维支撑，通过已支付的一体进出映射保留。

为说明(124.4)，各实际中心投影与种子码投影交换，
$\mathsf p$ 是每个原旁观者上的正、自伴、不增质量 retract，$qj=\mathrm{id}$。
正像等于角交的证明与VII卷104.11、105.3相同。
任意整个角对偶 $f$ 的原延拓是 $fq$；若 $0\le f\le\operatorname{Tr}$，则

$$
0\le fq\le\operatorname{Tr}q=u_{a+m}\mathsf p\le u_{a+m}.
\tag{124.5}
$$

所以限制与延拓使用整个对偶及完整 proper 区间，且在全部原纠缠输入上保留上界。
反向限制原 proper 效应也介于零与角迹单位之间。

单实际腿的既有中间结论是：在 $t<1$ 时，对每个有限 $k$，
$H_{1;k}$ 及其全对偶中的普通 dyad 恰为实际腿对寄存器 Schmidt 秩至多二的 dyad。
其原类型理由可直接由VII卷105.3、105.4和已支付码映射看出：
秩至多二的向量由种子 Bell 向量分别经寄存器 Kraus 矩阵和实际一体矩阵取得；
任何秩三向量先用寄存器支撑的等距进出码，再用实际可逆矩阵的合同，
可送为原 $3\times3$ 码角的 $\eta$。两个方向分别是已支付的一体或寄存器映射；
各自可缩为收缩矩阵，不假定一般正通道具有正逆。
若原秩三 dyad 已在锥中，则该输出迫使 $P\in D_s$，从而 $t=1$，矛盾。
大寄存器结论经有限码等距嵌入与投影限制至任意 $k$，包括 $k=1,2$。
对偶的相同结论也由下述全转置极性取得。
此处复用单实际结论及其参数对应，不另给它新内容的名义。

后面使用的两行压缩 $L_i:\mathbb C^3\to\mathbb C^2$，
由实际一体矩阵 $E_{\rm seed}L_i$ 实现，绝不作用于实际腿的集体子空间。
令 $c_i=\max(1,\|L_i\|_{\rm op})$，则 $E_{\rm seed}L_i/c_i$ 为收缩。
若 $\psi_L$ 是未缩放的联合压缩向量，归一输入的实际输出与质量分别为

$$
\left(\prod_i c_i^{-2}\right)
 \frac{|\psi_L\rangle\langle\psi_L|}{\|\psi\|^2},\qquad
\frac{\|\psi_L\|^2}{\|\psi\|^2\prod_i c_i^2}\in[0,1].
\tag{124.6}
$$

零输出允许；恢复未缩放 dyad 只是正锥的数乘，不冒领条件分支的确定质量。
已压缩角与旧寄存器合为一个有限寄存器的资格来自VII卷104.11。

### 124.3 两行压缩的有限维刚性

**引理 124.3（两行压缩迫使独立满秩实际对）。** 令
$A=B=\mathbb C^3$，$Q$ 为任意非零有限维复空间，
$\psi\in A\otimes B\otimes Q$ 且 $r_A(\psi)=3$。
若对每个 $L:B\to\mathbb C^2$，压缩向量在 $A\mid\mathbb C^2Q$ 的 Schmidt 秩至多二，
则 $\psi=\chi_{AB}\otimes q_Q$，其中 $\chi$ 的 Schmidt 秩为三，$q\ne0$。

**证明。** 对 $b\in B^*$ 令
$v_b=(\mathrm{id}_A\otimes b\otimes\mathrm{id}_Q)\psi$，
记其在 $A$ 上的列支撑为 $S_b$。将任意 $b,c$ 取为 $L$ 的两行，得
$\dim(S_b+S_c)\le2$，其中也包括 $c=0$。
所以没有三维 $S_b$。若某个 $S_b$ 二维，则所有 $S_c\subseteq S_b$，
总 $A$ 支撑至多二维，与 $r_A(\psi)=3$ 矛盾。
故每个非零 $v_b$ 都是简单张量 $a_b\otimes q_b$。

两个简单张量 $a\otimes q,a'\otimes q'$ 的和若简单或为零，
则 $a,a'$ 或 $q,q'$ 必线性相关。
否则，在 $A$ 上取分别选出 $a,a'$ 的两个对偶泛函，
会得到两个线性无关的 $Q$ 切片，故和的秩为二，矛盾。

切片空间是线性空间，其总 $A$ 支撑三维，所以其中有两个 $A$ 因子线性无关的简单张量。
它们的 $Q$ 因子由刚才的和论证必须相同至非零数乘。
任取其他非零切片，它的 $A$ 因子至少与这两个中的一个无关；
再次对和应用论证，迫使其 $Q$ 因子也在同一条非零射线上。
所有切片于是有共同非零 $q$。按 $B$ 的基重组系数即得
$\psi=\chi_{AB}\otimes q$；$r_A(\psi)=3$ 使 $\chi$ 的 Schmidt 秩恰为三。
这一论证只用有限维线性代数，未调用聚合对象 $Q$ 上的原正映射或正逆。∎

### 124.4 两条实际腿的完整普通 dyad 分类

**定理 124.4（两个实际因子的秩一截面）。** 在假设124.1下，对每个有限 $k\ge1$、
非零 $\psi\in A\otimes B\otimes\mathbb C^k$，
$|\psi\rangle\langle\psi|\in H_{2;k}$ 当且仅当以下之一成立：
$r_A(\psi),r_B(\psi)\le2$；或
$\psi=\chi_{AB}\otimes q$，其中 $\chi$ 的 Schmidt 秩为三。

**证明。** 若 $r_A=3$，对 $B$ 作每个已支付的两行一体压缩。
每个输出 dyad 属于 $H_{1;2k}$，故124.2所复用的单实际结论使其 $A$ 秩至多二。
引理124.3给独立的满秩 $AB$ 对。若先有 $r_B=3$，交换两条实际腿即可。
若两者都不是三，则两者至多二。

反向，第一种情况下在 $A,B$ 各选至多二维支撑。
连同旧有限寄存器，原向量属于一个有限的已支付 qubit 寄存器；
整个寄存器 PSD 锥及已支付的一体支撑嵌入给出其 dyad。
第二种情况下，$|\chi\rangle\langle\chi|$ 属于整个原二实际块的 $\mathrm{PSD}_9$，
$|q\rangle\langle q|$ 属于已支付寄存器锥；原最小界给二者乘积。
分别归一后的态质量均为一；未归一版本由正锥数乘恢复。
这是整个实际 $H_{2;k}$ 的环境秩一截面，包括 $H_{2;4}$，不把整个角宣布为 PSD。∎

### 124.5 任意有限实际腿的匹配必要性与充分性

**定理 124.5（普通匹配 dyad 分类）。** 在假设124.1下，对每个有限
$a\ge0,k\ge1$ 和非零 $\psi\in(\mathbb C^3)^{\otimes a}\otimes\mathbb C^k$，
有 $|\psi\rangle\langle\psi|\in H_{a;k}$ 当且仅当存在实际腿之间不相交配对的匹配
$\mathcal M$，使

$$
\psi=\left(\bigotimes_{ij\in\mathcal M}\chi_{ij}\right)\otimes\zeta,
\qquad \operatorname{SR}(\chi_{ij})=3,\qquad
r_i(\zeta)\le2\quad(i\text{ 未匹配}).
\tag{124.7}
$$

每个满 Schmidt 秩三实际对与其他全部因子独立；$\zeta$ 包括旧寄存器。
零 dyad 也总在锥中，可取空匹配与 $\zeta=0$。
匹配可依赖于向量，不要求所有态共有同一匹配。

**证明。** 先证必要性。若全部实际秩至多二，取空匹配即可。
否则固定一条秩三实际腿 $A$。考虑在其余实际腿中保留未压缩集合 $U$、
对其补集逐腿作两行压缩后仍使 $A$ 秩为三的所有选择。
至少保留其余全部腿时可行；腿数有限，故可取 $|U|$ 最小的选择。

$U$ 不能空：否则输出是 $H_{1;k2^{a-1}}$ 中 $A$ 秩三的 dyad，
违反单实际结论。对 $B\in U$，最小性说明每个进一步的两行 $B$ 压缩都使 $A$ 秩至多二。
仅在线性代数上把其他全部因子合记为 $Q$，引理124.3给当前向量
$\chi_{AB}\otimes\xi$，其中 $\chi$ 的 Schmidt 秩为三。
若 $U$ 还含 $C\ne B$，则可在 $C$ 上取两行坐标压缩使 $\xi$ 仍非零：
保留一个非零系数所用的基指标即可。
这会保留 $A$ 秩三并减少 $|U|$，矛盾。因此 $U=\{B\}$。
已有对 $A,B$ 以外所有实际腿的某组压缩，使 $A$ 秩仍为三。

固定这个 $B$，把其余每个两行压缩矩阵的所有复条目视为独立变量。
上述选择中 $A$ 展平矩阵的某个 $3\times3$ 小行列式 $D$ 非零，故 $D$ 是非零复多项式。
在非空开集 $D\ne0$ 上，每个压缩向量都在 $H_{2;k2^{a-2}}$ 中，且 $A$ 秩三。
定理124.4迫使它在 $AB\mid$ 剩余寄存器切口分解，
所以该展平的每个 $2\times2$ 小行列式均为零。

这些小行列式也是压缩条目的复多项式。
复多项式在非空开集上为零就恒为零：在其中取开多圆盘，
逐变量限制到复直线，用一元多项式恒等原理，再对变量数归纳。
故所有这些小行列式对任意压缩选择都为零，包括 $D=0$ 的选择。

若原向量在 $AB\mid$ 其余因子展平的秩至少二，则存在两个线性无关的系数列。
每列由其余每条实际腿的一个基指标及旧寄存器的一个基指标索引。
在每条其余实际腿上，以两行坐标压缩保留这两个列用到的至多两个指标；
若指标相同，任意补足第二行。
于是两个原列在压缩后仍作为不同列保留，且仍线性无关；
不同之处若只在旧寄存器指标，也仍被保留。
这会使某个 $2\times2$ 小行列式非零，矛盾。
因此原向量本身已分解为 $\chi_{AB}\otimes\xi$，$\chi$ 的 Schmidt 秩仍为三。
当没有其他待压缩腿时，同一结论直接由定理124.4给出。

现在用整个原对偶的 proper 效应剥去这一对。
令 $h=\|\chi\|^2>0$，在原二实际块上取
$E_\chi=|\chi\rangle\langle\chi|/h$，其余二体扇区为零。
整个 $C_2$ 与全对偶都是对齐块 PSD，故 $0\le E_\chi\le u_2$。
原最大界切片给剩余实际角中的 $h|\xi\rangle\langle\xi|$。
对于归一分解输入，该切片的质量为一；未归一锥成员关系可除以 $h>0$。
对剩余实际腿归纳。每次剥去两个秩三实际腿，最终剩余每条实际腿秩至多二，
得到(124.7)，全过程没有改变原实现。

再证充分性。分别归一每个非零配对向量与剩余向量。
每个配对 dyad 是其原二实际 PSD 块中的归一态。
对每条未匹配腿选其维数 $d_i\le2$ 的支撑等距嵌入；
$d_i=1$ 时可将其补在二维角内。
将 $\zeta$ 拉回这些 qubit 支撑与有限 $k$ 寄存器，得到一个有限种子寄存器向量，
其归一 dyad 在整个已支付寄存器 PSD 锥中。
以已支付的实际一体部分等距矩阵 $K_i$ 将各支撑送回，$K_i^*K_i\preceq I$。
它在实际占用支撑上等距，故保留原范数，输出剩余归一态质量恰为一。
旧寄存器仍是同一个码对象，不对实际 qutrit 作集体操作。
最后用原最小界和实际置换将全部归一配对态与剩余态相乘，
所得恰为 $|\psi\rangle\langle\psi|/\|\psi\|^2$。
乘回非负锥标量 $\|\psi\|^2$ 即得结论。
这是静态状态锥及已支付数学映射的成员关系，不增加物理制备事件。∎

该定理包括 $a=0$ 的整个寄存器 PSD、$k=1$ 的标量剩余因子、
空匹配以及各局部秩零、一、二的边界。每个秩三实际腿必须与另一秩三实际腿成独立对，
故此类腿数为偶数。参数端点 $t=2/3$ 在域内，$t=1$ 不在域内；
后者沿VII卷105.4给全部标准 PSD dyad。
结论也不要求寄存器对全部实际腿的 Schmidt 秩至多二。例如

$$
\zeta=\frac{|00\rangle_{AB}|0\rangle_Q+
 |01\rangle_{AB}|1\rangle_Q+|10\rangle_{AB}|2\rangle_Q}{\sqrt3}
\tag{124.8}
$$

在实际 qubit 角中被准入，两个实际局部秩都是二，而寄存器切口的 Schmidt 秩是三。
定理只分类普通 dyad，不分类 $P_N$、原极端射线、整个 $H$、$H\cap\mathrm{PSD}$
或所有 PSD 混合态。

### 124.6 归一匹配锥的闭性、原极性与严格夹逼

**定理 124.6（同原全对偶的匹配包络）。** 令 $\Gamma_{a;k}$ 为定理124.5匹配类的
单位向量 dyad 集，令

$$
\mathcal R_{a;k}=\overline{\operatorname{cone}(\Gamma_{a;k})},\qquad
\mathcal R_{a;k}^*=
 \{Y\in\operatorname{Herm}:\langle\psi,Y\psi\rangle\ge0
       \text{ 对所有匹配向量 }\psi\}.
\tag{124.9}
$$

这里 $\operatorname{cone}$ 指凸锥包。全转置 $\Theta$ 取固定实际基和实码基。
在假设124.1下，同一个整个实际角满足

$$
\begin{gathered}
\mathcal R_{a;k}\subseteq H_{a;k}\subseteq\mathcal R_{a;k}^*,\qquad
\mathcal R_{a;k}\subseteq H_{a;k}^*\subseteq\mathcal R_{a;k}^*,\\
H_{a;k}^*=\Theta H_{a;k},\qquad
\Theta\mathcal R_{a;k}=\mathcal R_{a;k}.
\end{gathered}
\tag{124.10}
$$

尤其 $H^*$ 的普通 dyad 截面与 $H$ 相同，恰为匹配类。

**证明。** 匹配充分性使每个生成元在 $H$ 中；$H$ 的闭凸性给第一条左包含。
VII卷105.3式(105.6)的原杯帽计算适用于每个有限 $N$：
将 $N$ 个已支付杯排列为参考｜输入，得到 $\Omega_N\in C_{2N}$。
由整个 $f\in C_N^*$ 切一半，给 $\Theta_Nf\in C_N$。
另一方面，任意 $x,y\in C_N$ 的原乘积经 $N$ 个已支付帽收缩给
$\operatorname{Tr}((\Theta_Nx)y)\ge0$，所以 $\Theta_Nx\in C_N^*$。
结合 $\Theta_N^2=\mathrm{id}$，得 $C_N^*=\Theta_NC_N$。
若使用归一杯与 proper 帽，只会乘以正因子；原每对杯帽的系数沿104.6为
$(R_{\rm tot}L)^{-1}$，$R_{\rm tot}=\sum_i n_i,L=3$，
不影响上述锥包含。这里没有调用高阶 Jordan 分类。

对混合角，$\mathsf p=jq$ 自伴且正，整个对偶可限制与延拓，
实码投影及实际中心投影均与 $\Theta_N$ 交换，故限制得到 $H^*=\Theta H$。
$\operatorname{Tr}(X^TY)$ 不必正定；本论证没有把它用作正定内积，
也不先假定 $\Theta$ 在 $H$ 上主动正。
匹配向量的复共轭保持每个独立对及每个局部秩，故 $\Theta\mathcal R=\mathcal R$。
于是 $\mathcal R\subseteq\Theta H=H^*$；对偶化给 $H\subseteq\mathcal R^*$。
再对偶化 $\mathcal R\subseteq H$ 给 $H^*\subseteq\mathcal R^*$，完成两个夹逼。
全转置将向量 dyad 变为共轭向量 dyad，结合定理124.5也给对偶的精确秩一截面。

匹配生成集本身紧。对有限个匹配中的每一个，暂允许每个单位配对向量有任意
Schmidt 秩至多三，剩余单位向量满足各未匹配腿局部秩至多二。
这由球面与闭的小行列式条件给紧参数集，张量像亦紧。
秩一或二的配对可吸收到剩余因子中而不增加任何局部秩至三，
故这些有限个紧像的并恰为 $\Gamma$，也包括满秩三配对的极限。
有限维中其凸包紧，且全部迹一；若锥内序列收敛，其非负锥系数就是迹，
从而有界并可取收敛子列，故凸锥包已闭，无须另补非零迹零方向。

$\mathcal R$ 是 PSD 内的 proper 满维锥，含全部乘积 dyad。
乘积投影实张成整个 Hermitian 空间；恒等也在内点。
具体地，在每个维数 $d$ 的局部因子上，使用投影至
$e_i$、$(e_i\pm e_j)/\sqrt2$、$(e_i\pm i e_j)/\sqrt2$ 的有限列表。
它们张成 Hermitian 空间，总和为 $(2d-1)I$。
张量化这些列表，所有系数为正且仍张成，给恒等的内点性。
因此迹在每个非零 $\mathcal R^*$ 元素上也严格正。

低锚为

$$
\mathcal R_{0;k}=\mathrm{PSD}_k,\quad
\mathcal R_{1;k}=\mathrm{SN}_2(k,3),\quad
\mathcal R_{1;1}=\mathrm{PSD}_3,\quad
\mathcal R_{1;2}=\mathrm{PSD}_6,\quad
\mathcal R_{2;1}=\mathrm{PSD}_9.
\tag{124.11}
$$

其对应对偶低锚也为 PSD；标量、qubit 扇区是相同的种子寄存器限制。
$\mathrm{SN}_2$ 指闭 Schmidt 数至多二锥，采用
Terhal–Horodecki，[*A Schmidt number for density matrices*, quant-ph/9911117v4](https://arxiv.org/abs/quant-ph/9911117v4)
的定义、引理1、2及定理2的通常语境；这里不将该文当作原角分类的供应。

$\mathcal R$ 及其对偶均保持码／角正 retract、寄存器 CP、实际一体矩形合同、
原置换和重括号。对 $\mathcal R$，单个 Kraus 或一体矩阵把匹配向量送为零或另一匹配向量：
满秩三对若降至秩至多二，便吸收入剩余因子；CP 的 Kraus 和则给匹配 dyad 的正和。
反向迹伴随具有相同的合法局部类型，故给对偶的对应保持性。
实际腿压入 qubit 后成为寄存器因子，反向支撑嵌入给同一个角锥。
这些保持性不是两个端点满足全部高阶 min/max 的证明。

在 $H_{1;3}$，实际归一态 $\tau_\ell$ 非 PSD，故 $\mathcal R\subsetneq H$。
而 $P=R_3/3$ 为 PSD，故在 $\mathcal R^*$ 中，却因单实际秩三而不在 $H$，
所以 $H\subsetneq\mathcal R^*$。
更一般地，若 $a\ge1$ 且 $k2^{a-1}\ge3$，
把 $\tau_\ell$ 与 $P$ 的三维参考等距编码进旧寄存器与其他实际腿的至多二维支撑。
已支付寄存器 CP 和逐腿嵌入保留 $\tau_\ell$ 的负本征值，
而编码后的 $P$ 只有一条秩三实际腿，被定理124.5排除。
故此时两个包含也都严格。
余下 $a=0$、$(a,k)=(1,1),(1,2),(2,1)$ 正是 PSD 低锚；
对偶的严格性由全转置得到。

当 $t>2/3$ 时，实际 $\tau_t$ 还是 PSD，却有 Schmidt 数三：
它的 $P$ 读数为 $t>2/3$，违反迹一 $\mathrm{SN}_2$ 的通常上界。
故即使 $H_{1;3}\cap\mathrm{PSD}$ 也严格大于匹配锥，
不能用环境谱分解把普通 dyad 分类扩为 PSD 混合态分类。
夹逼是原完整条件下的必要关系，不构造任何中间全有限层级，也不证明其唯一性。∎

### 124.7 匹配锥的六腿最大界失败

**命题 124.7（归一读数 $-1/18$）。** 将 $\mathcal R$ 本身选为原层级的方案，
虽有上述 PSD 低锚、最小张量闭合和局部 retract，仍违反原最大界。

**证明。** 取实际 qutrit $A,B$ 和已支付三维寄存器 $Q,Q'$，令
$\eta_3=\sum_{i=0}^2|ii\rangle$、$R_3=|\eta_3\rangle\langle\eta_3|$、
$P=R_3/3$、$W_0=I_9-R_3/2$。每个单实际混合角是 $\mathrm{SN}_2$。
对任意 Schmidt 秩至多二的向量 $v$，
把 $\eta_3$ 投影至 $v$ 的实际支撑，其范数平方等于支撑维数；Cauchy–Schwarz 给

$$
|\langle\eta_3,v\rangle|^2\le2\|v\|^2.
\tag{124.12}
$$

所以 $W_0\in\mathrm{SN}_2^*$，$I-W_0=R_3/2$ 也在该对偶中。
$P,I-P$ 都是 PSD，亦在该对偶中。因此 $e=W_0,f=P$ 是所提议
$\mathcal R_{1;3}$ 的两个完整对偶 proper 效应，均不需额外缩放。
这不是关于未知实际 $H_{1;3}$ 中同时存在这两个效应的断言。

取质量一的全局匹配态
$\rho=P_{AB}\otimes P_{QQ'}$，按 $(A,Q)\mid(B,Q')$ 重排。
若 $\Omega_9$ 为 $\sum_{i,j}|i,j\rangle_{AQ}|i,j\rangle_{BQ'}$ 的 dyad，
则 $\rho=\Omega_9/9\in\mathcal R_{2;9}$。
它只用原实际对的 PSD Bell 态和已支付寄存器 Bell 态。
以 $\operatorname{Tr}((X\otimes Y)\Omega_9)=\operatorname{Tr}(X^TY)$ 计算，

$$
\begin{aligned}
\operatorname{Tr}[(W_0\otimes P)\rho]
 &=\frac{\operatorname{Tr}(W_0^TR_3)}{27}
 =\frac{3-9/2}{27}=-\frac1{18}.
\end{aligned}
\tag{124.13}
$$

故 $\rho\notin\mathcal R_{1;3}\otimes_{\max}\mathcal R_{1;3}$。
每个 $Q_3$ 是原实码 $c=(00,01,10)$，占两条实际种子角腿。
因此这是两条实际腿加四条种子腿的原六腿角，
失败分块经合法位置置换恰是原 $3\mid3$；没有将两条实际腿融合为一条。
角 proper 效应按(124.5)延拓到整原候选对象，补也正，上界仍是原单位。
上述质量与读数均使用归一态；若另将两个效应分别乘 $0<\alpha,\beta\le1$，
读数相应为 $-\alpha\beta/18$，不能丢掉缩放后还引用未缩放常数。∎

### 124.8 全对偶匹配锥的六腿最小界失败

**命题 124.8（归一读数 $-1/135$）。** 将整个 $\mathcal R^*$ 选为原层级的方案违反原最小界。

**证明。** 在各 $\mathcal R_{1;3}^*=\mathrm{SN}_2^*$ 内，
$x=W_0/(15/2)$、$y=P$ 均为归一候选态，因为
$\operatorname{Tr}W_0=15/2$、$\operatorname{Tr}P=1$。
若有原最小界，它们的乘积必须在全局 $\mathcal R_{2;9}^*$ 中。

在同一六腿实现与同一重排上取
$E=\Omega_9/9=P_{AB}\otimes P_{QQ'}$。
它在 $\mathcal R_{2;9}$ 中，即在所提议全局 $\mathcal R_{2;9}^*$ 的整个迹对偶中。
其补也在 $\mathcal R$ 中，因为

$$
I-E=(I_{AB}-P_{AB})\otimes I_{QQ'}
       +P_{AB}\otimes(I_{QQ'}-P_{QQ'}).
\tag{124.14}
$$

每个因子都是实际对或寄存器上的 PSD，
原二实际低锚和匹配生成元给出两项及其和的锥成员关系。
所以 $E$ 是提议全局锥的 proper 效应，真实零扩张仍有完整单位上界。
其归一输入读数为

$$
\operatorname{Tr}[E(x\otimes y)]
 =\frac{-3/2}{9(15/2)3}=-\frac1{135}.
\tag{124.15}
$$

因此 $x\otimes y\notin\mathcal R_{2;9}^*$，违反原最小包含。
若 proper 测试再乘 $0<\gamma\le1$，负读数为 $-\gamma/135$；输入质量一的归一因子不能省略。

另一方面，$\mathcal R$ 的最小张量闭合对全部对象成立：
两个不相交匹配的并仍是匹配，两个剩余向量的乘积保持每条局部秩至多二，
再取凸锥包与闭包即可。对偶化此最小包含，得 $\mathcal R^*$ 的最大界。
所以两个反例分别指出各端点恰好缺少的另一半界。
这只排除两个规范端点方案，不排除每个原中间层级。∎

### 124.9 原互反源接口对两个端点的独立排除

**命题 124.9（每个原 $2/3\le t<1$ 的双向 $\mathcal D_r$ 障碍）。**
即使不使用124.7、124.8的张量界反例，VII卷105.6的原互反源接口也阻止
用 $\mathcal R$ 或 $\mathcal R^*$ 替换完整原层级。

**证明。** 保留(124.3)的原参数，令

$$
\mathcal D_r(X)=rX+(1-r)\operatorname{Tr}(X)I_3/3,
\qquad J(\mathcal D_r)=3\tau_\ell
 =\frac{W_{\lambda_*}}{3-\lambda_*}.
\tag{124.16}
$$

实际码到实际块、实际块到实际码的真正零扩张，分别是VII卷(105.21)的两条原映射。
它们各自在每个原纠缠旁观者上正、对接受输入保迹且对整个输入不增质量。
正性来自各自原 Choi 成员关系与原置换，不来自通常 CP 或某个正逆。
余字 $11$、码与余字交叉元、其他输入扇区均按原定义消去。

对提议 $\mathcal R$，先取两个已支付三维寄存器间的归一 Bell 态 $P$，
它在 $\mathcal R_{0;9}=\mathrm{PSD}_9$ 中。
在一个寄存器上作用码到实际块的 $\mathcal D_r$，
应得到 $\mathcal R_{1;3}$ 中质量一的 $\tau_\ell$。
但它在 $\eta_3/\sqrt3$ 方向的本征值为 $\ell<0$，而 $\mathcal R\subseteq\mathrm{PSD}$，
故不被准入。等价地，所提议 $\mathcal R$ 的 proper 效应 $P$ 读数为 $\ell<0$。

对提议 $\mathcal R^*$，先取一条实际 qutrit 与一个寄存器间的归一 Bell 态 $P$。
它是 PSD，故与所有 $\mathcal R$ 元素配对非负，属于 $\mathcal R_{1;3}^*$。
对实际腿作用已支付的实际到码 $\mathcal D_r$，
输出应为纯寄存器对象 $\mathcal R_{0;9}^*=\mathrm{PSD}_9$ 中同一个 $\tau_\ell$。
其负本征值在这里被通常寄存器 proper 投影 $P$ 直接检出，故该方向也失败。
两项输出均保持归一质量，输入和输出的位置由原 Choi 次序与合法置换固定。

对 $\mathcal R$ 还有 $t>2/3$ 时的 $p$ 源失败：
同一寄存器 Bell 输入经码到实际块 $\mathcal D_p$ 给 $\tau_t$，
其 $P$ 读数为 $t>2/3$。
由(124.12)，每个迹一 $\mathrm{SN}_2$ 态的 $P$ 读数至多 $2/3$，故它不在提议角中。
$t=2/3$ 只消去这一额外 $p$ 障碍，不能消去 $\ell=-1/15<0$ 的 $r$ 障碍。

以上 $P,W_0$ 在各提议端点中作为状态或效应的资格均由其各自完整锥证明。
对实际未知 $H$，原分离效应仍必须使用 $W_{\lambda_*}/M$ 及其原零扩张；
不得用候选端点效应替换它，也不得抹去 $M$ 后把上述数值读数移植到 $H$。
这给有限、保类型的源映射失败，不给原 $t$ 的排除定理。∎

### 124.10 必要区间、原始来源与未支付的联合关系

**命题 124.10（端点障碍的准确范围）。** 两个规范端点逐扇区恢复标量、qubit、qutrit
时有同一整个 $C_1,C_2$ 块 PSD 锚，因而保留低阶整个基、全效应和通常 $S_2$。
它们也保持匹配定义给出的原置换、规范重括号、实际一体矩形映射、
有限寄存器 CP 和码／角 retract；这些性质仍不足以满足假设124.1。
完整原目标中的中间层级与物理桥梁不由这些端点障碍解决。

**证明。** 低锚与局部保持性已在124.6证明。
对所有分块，$\mathcal R$ 的最小界和 $\mathcal R^*$ 的最大界成立，
而另两界在124.7、124.8给出的实际六腿 $3\mid3$ 分块分别失败。
只需一个原分块失败就足以否定完整层级，不需要把低阶检查误作高阶全称验证。
124.9又给两端点各自违反的原双向全旁观源接口。
另一个必要关系是 $H^*=\Theta H$：
$\mathcal R$ 与 $\mathcal R^*$ 各自全转置不变，却在 $H_{1;3}$ 的大小上不同，
故它们也不能独自满足这一原极性等式。
每个压缩、切片、杯、匹配态和全局见证均置于同一固定原张量层级，
没有按维数把 $Q_3$ 与 $A_3$ 认作同一实际对象，也没有融合两条实际腿。

所余联合问题是：能否找到或排除同一个中间族，满足
$\mathcal R\subseteq H\subseteq\mathcal R^*$、$H^*=\Theta H$、
所有原分块的 min/max 双界、完整原 retract、两条互反源与全部低阶条件供应，
同时保持一个统一严格的 $t<1$。
只证明固定箭头的自极性补全，不会自动补出张量包含。
一个具体的候选关系是以匹配态及实际已支付的互反端点资源出发，
在已支付类型映射、原产品与帽收缩下取最小闭族，再问其是否有张量相容的全转置对偶补全。
正向答案仍须证明标量非负及真正的全部张量相容；
反向答案须给一个原准入输入和一个实际 proper 效应组成的有限负读数图式。
本章既未构造此中间层级，也未排除它。

两端点失败不排除任何原 $t\in[2/3,1)$，不构造六份前缀或 allN 反模型，
也不证明 $\mathsf{Fusion}_3$。原全目标仍要求在完整原域中证明 $t=1$，
或给出一个合法的统一严格间隙 allN 模型；
有限截断参数趋向一不支付后一条件。
静态锥成员关系与数学预算也不供应物理源实现、指定复合／事件仪器、动力学、
物理时间作用、钟校准、单位或数值 $\hbar$。

本章的单实际、映射锥／全对偶字典、可逆产品滤波、proper 分离预算、
单种子 qubit 旁观门测试、$t,\ell,p,r,M$ 关系及有限网络边界，
均作为VII卷104—106的既有中间结果复用。
普通 Schmidt 数与各向同性阈值沿 Terhal–Horodecki 原文复用：
其引理1对应 $d=3,k=2$ 的 $P$ 读数上界 $2/3$，
引理2的通常 $k$ 正映射阈值不等同于本章原全旁观资格；
式(6)、(9)、(10)与定理2的 PSD 各向同性陈述只用于相应 PSD 输入，
负 $F=\ell$ 的原态资格来自VII卷105.4—105.6，而非该文 PSD 定理。
所有所需有限见证的不等式、常数及 proper 补已在本章直接给出。
全实际压缩／小行列式／剥离、同原匹配包络及两个保类型端点障碍为这些前置上的综合推导
（repo-derived）；不主张文献新颖性或优先权。∎

## 追加锚（本行以下为增补区）

## 125. 同一共同源下的六份最小锥、Four 冗余与源饱和条件准则

### 125.A 原对象、完整低份接口与固定共同源

**定义 125.1（固定原域及同一个辅助族）。** 使用VII卷105.1、106.1及本卷123.1的原对象。
有限实际扇区集为 $I$，$n_i\in\{1,2,3\}$ 且至少一个 $n_s=3$；固定

$$
V=\bigoplus_{i\in I}\operatorname{Herm}_{n_i},\qquad
W_N=V^{\otimes_{\mathbb R}N},\qquad
u_N=u^{\otimes N}=\sum_{I^N}\operatorname{Tr},\qquad
(W_0,C_0,u_0)=(\mathbb R,\mathbb R_+,\mathrm{id}).
\tag{125.1}
$$

每个 $\operatorname{Herm}_d$ 是复 Hermitian 矩阵的实空间。
实际字 $v=A_{i_1}\cdots A_{i_N}$ 的实现是这些空间的原实张量积；
矩阵表示只使用同一局部坐标的 Kronecker 识别。
原 allN 目标始终要求每个 $C_N$ 闭、尖、生成，$u_N$ 在非零正向量上严格正，且

$$
K_N=C_N\cap\{u_N=1\},\qquad
P_N=\operatorname{ext}K_N,\qquad
\mathcal E_N=[0,u_N]_{C_N^*}
\tag{125.2}
$$

分别为整个基、全部极点和整个普通对偶 proper 区间。
每个原位置分块都须满足原 min/max 双界；位置置换及其逆、空侧单位、
原产品配对与规范重括号均固定。下文“定义前缀至六”只截取总次数至多六的这些定义条件，
不会据此前缀取得消费更高次数的 allN 推论。

唯一普遍比较前件是整个原 $S_2$。对每个 $p\in P_2$，
以整个 $\mathcal E_2$ 上确认 $p$ 的效应定义原下确界
$T_p^{(2)}(x)=\inf\{f(x):f\in\mathcal E_2,\ f(p)=1\}$，要求

$$
T_p^{(2)}\!\left(\sum_\alpha a_\alpha q_\alpha\right)
 =\sum_\alpha a_\alpha T_{q_\alpha}^{(2)}(p)
\quad(q_\alpha\in P_2,\ a_\alpha\ge0,\ \sum_\alpha a_\alpha=1).
\tag{125.3}
$$

量词包括纠缠二份纯点、任意有限准备族、零权与重复标签。
三条条件供应完整保留VII卷103.1、104.1的输入和条件来源：

| 原条件供应 | 固定的全部输入及参数对应 |
| --- | --- |
| 低二份到保迹 Jordan 表示 | 对 $q=1,2$ 的整个 $(W_q,C_q,u_q,K_q,P_q,\mathcal E_q)$ 和原确认下确界使用 least 性、互反、同框架谱性、projectivity、正面投影及 filter purity；保留保迹表示和直和，$S_1$ 由纯旁观下降 |
| 唯一实际自复合的复型选择 | 对同一个 $(W_1,W_1,W_2)$ 使用正双线性态产品、效应产品、原单位、全域精确配对、乘积效应分离及局部层析；全部中心扇区限制、框架秩乘法和实维乘法均保留 |
| 每个实际两因子的产品正规形 | 对所选复型的每个实际扇区 $(i,j)$ 与尺寸 $n_i,n_j,n_in_j$ 使用实际态／效应乘积、全域配对及单位；正规形含固定输出酉和固定输入转置，标量因子也在域内 |

条件来源沿VII卷103.1所链的
[least confirmation、谱性与面保纯](../../../Library/QuantumStates/mullerududec2012selfduality.md#reciprocal-least-confirmation-and-the-spectrality-bridge)及
[实际复合与产品正规形](../../../Library/QuantumStates/barnumhilgert2019spectral.md#actual-two-factor-products-after-complex-type-selection)接口。
它们不是一条无前提分类定理，也不改成三份 Jordan 分类或 $S_3$。

同一含相位种子为 $\mathsf F_{r,2}$：在原块 $r$ 的固定共同向量基中
$g_{r,2}=|0\rangle_r^{\otimes3}+|1\rangle_r^{\otimes3}$，
$\Delta_{r,2}=|g_{r,2}\rangle\langle g_{r,2}|$ 在其他扇区真正为零，
$\operatorname{Tr}\Delta_{r,2}=2$，归一态是 $\Delta_{r,2}/2$。
不对基的相位取商，不要求原三份极端性。
种子 qubit 嵌入、压缩记 $j_N,q_N$，满足 $q_Nj_N=\mathrm{id}$。
原实码仍逐字为

$$
ce_0=|00\rangle,\qquad ce_1=|01\rangle,\qquad
ce_2=|10\rangle,\qquad c^*|11\rangle=0.
\tag{125.4}
$$

对每个实际最大块 $s$，原 $i_s=(j_2\operatorname{Ad}_c)\otimes\iota_s$、
$q_s=i_s^*$、$\mathsf p_s=i_sq_s$ 及角内 $P=|\sum_{a=0}^2aa\rangle\langle\sum_{a=0}^2aa|/3$
沿VII卷105.2固定；$q_s$ 中的星是普通实迹伴随。
码外、码与余字的交叉元和其他输入扇区都按原映射送零。

固定定理123.2给出的**同一个**共同 $\mathcal K$、源 $\mathcal D$、实现 $S$ 和辅助族 $E$。
对象由实际 $A_i$、量子 $Q_k$ 和单位的所有有限字组成。
量子字可与 $Q_{k_1\cdots k_a}$ 规范分组，实际字不改型为免费量子寄存器。
源只含既定量子 CP、实际一体矩形 CP、杯帽、所有共同
$X\in\mathcal K_{k,n_i}$ 的态生成元及其紧对偶、原置换及逆、重括号、复合和旁观张量扩张。
没有任意多实际腿的集体 CP 生成元，也没有为任意 $x\in E(w)$ 或后文 $G(w)$
增加 $s_x:\mathbf1\to w$。源的复合可以经过任意有限高次数和任意有限量子对象。

记 $T_w$ 为固定基中的同时全转置，$K^*$ 为普通迹对偶，并令

$$
b_w(X,Y)=\operatorname{Tr}(X^TY),\qquad K^\vee=T_wK^*,\qquad
\Phi^\flat=T\Phi^\dagger T.
\tag{125.5}
$$

紧对偶字的反序由原置换识别；下文的 $\flat$ 总含这个固定识别。
$b_w$ 对称、非退化，却通常不正定；不假定它是层上的 Hilbert 内积。
源箭头的紧 $b$ 伴随及其全部旁观扩张仍为同一源箭头。
特别是 $\operatorname{Ad}_A^\flat=\operatorname{Ad}_{A^T}$，尺寸反向。
不假定新锥在全转置或部分转置下不变。

源下、上包络记

$$
B(w)=\overline{\operatorname{cone}\{S(s)(1):s:\mathbf1\to w\}},\qquad
A(w)=\{z:S(e)z\ge0\ (e:w\to\mathbf1)\}=B(w)^\vee.
\tag{125.6}
$$

沿123.2复用 $B\subseteq E=E^\vee\subseteq A$，$B,A,E$ 均在全部源箭头下正。
这里 $S$-system 指各层闭凸锥在每个指定 $S(f)$ 下保持正性，不含任意两补全态的产品律。
逐字的 $B,A$ proper，夹在初等乘积 PSD dyad 锥与乘积块正锥之间，迹严格正。
量子字上 $B=E=A=\mathrm{PSD}$，$Q_kA_i$ 上三者都是同一 $\mathcal K_{k,n_i}$，
两实际腿上三者都是整个 $\mathrm{PSD}_{n_in_j}$。
这些精确低类型由源态和源效应的两向夹逼给出。

令 $C_a^0=\bigoplus_{|v|=a}E(v)$，$0\le a\le5$，
$K_a^0=C_a^0\cap\{u_a=1\}$。它们自 $b$ 极、在全部原位置下不变，
$C_1^0,C_2^0$ 是整个对齐 PSD 直和；完整五份定义包及上述三供应输入均沿123.2保持。
原三码角还是同一 $\mathcal K_{3,3}$，整个迹一基的 $P$ 区间为 $[-1/15,2/3]$。
后文提到“旧 $E_6$”专指这次已经选定的 $\bigoplus_{|v|=6}E(v)$，
不能用另选第六锥代付它的成员关系。

### 125.B 已支付的两输入源检验与实际二腿输出

**引理 125.2（共同源的两输入 currying）。** 对上述同一 $E$，任取两个对象字
$v,w$、$x\in E(v),y\in E(w)$ 及任意源效应 $e:vw\to\mathbf1$，均有
$S(e)(x\otimes y)\ge0$。如果 $x,y$ 各有三条实际腿，把其中两对匹配腿按原帽收缩，
则余下两条实际腿的输出属于整个 $C_2^0$ 的相应 PSD 块。
这复用123.2的共同源性质，不声称 $x\otimes y\in E(vw)$。

**证明（125.2）。** 紧闭 currying 将 $e$ 写成源箭头
$\widehat e:v\to w^\vee$，满足
$S(e)(x\otimes y)=b_w(S(\widehat e)x,y)$，含固定对偶字重排。
$E$ 的源正性把第一输入送进相应 $E$，自 $b$ 极性给非负值。
这里对全部源效应使用同一论证，不只取一个选定菜单。

具体写 $X$ 的腿为 $(i,a,b)$，$Y$ 的腿为 $(a,b,\alpha)$，则双边收缩的分量为

$$
R_{i\alpha,j\beta}
 =\sum_{a,b,c,d}X_{iab,jcd}\,Y_{ab\alpha,cd\beta}.
\tag{125.7}
$$

共轭并交换 $(a,b)$ 与 $(c,d)$ 得 $R$ Hermitian。
任取余下两实际腿上的 $H\succeq0$；其紧对偶效应是源效应，因为
$B(A_iA_j)=A(A_iA_j)=\mathrm{PSD}_{n_in_j}$。
把它附在余腿上，所得标量正是 $b_2(R,H)$，由两输入结论非负。
整个二腿 PSD 锥自 $b$ 极，故 $R\succeq0$。
该式在每条线只收缩相同 ket、bra 指标，没有在某个 $E$ 输入上插入额外转置。
扇区不匹配时值为零；相容扇区逐块成立再求和。
此结论只给二腿输出，不自动给四腿或六腿输出的 $E$ 成员关系。

同时，任意一份或二份 PSD 元素是有限源 dyad 和。
把这一源态附在任意 $E$ 输入上，再取非负和，给出所有总次数的低因子乘积正性；
相应一腿或二腿紧对偶切片也在 $E$ 中正。
这是下文已支付配对的共同依据。∎

### 125.C P1：完整定义界中的最小第六锥

**定理 125.3（P1 的定义前缀准则）。** 对 $1\le a\le5$ 和每个原六位置置换 $\pi$，定义

$$
\begin{aligned}
K_{a,\pi}&=\{\tau_\pi(x\otimes y):x\in K_a^0,\ y\in K_{6-a}^0\},\\
K&=\operatorname{conv}\bigcup_{a,\pi}K_{a,\pi},\qquad
L_6=\{rk:r\ge0,\ k\in K\},\\
F_6&=\overline{\operatorname{cone}}\{\tau_\pi(x\otimes y):
 x\in C_a^0,\ y\in C_{6-a}^0,\ a=1,2\},\\
D_6&=\overline{\operatorname{cone}}\{\tau_\pi(x\otimes y):x,y\in C_3^0\},\\
U_6&=\bigcap_{a=1}^5\ \bigcap_\pi
 \tau_\pi(C_a^0\otimes_{\max}C_{6-a}^0).
\end{aligned}
\tag{125.8}
$$

$\otimes_{\max}$ 使用两个因子的**整个普通迹对偶**：
$z$ 在相应最大锥中当且仅当 $(f\otimes g)(z)\ge0$ 对全部
$f\in(C_a^0)^*,g\in(C_{6-a}^0)^*$ 成立。
反向分割由原置换包含，不连续支撑也在交并范围内。
$L_6=F_6+D_6$，它闭、尖、生成，$u_6$ 严格正，整个归一基恰为紧集 $K$，并有

$$
U_6=L_6^\vee.
\tag{125.9}
$$

定义以下两个全称符号条件。Cross 要求对任意 $x,y\in C_3^0$、
$h\in C_2^0,z\in C_4^0$，当 $h$ 的两条实际腿各取自 $x,y$ 一条时，
在所有原位置上有 $b_6(x\otimes y,\tau_\pi(h\otimes z))\ge0$。
Four 要求对任意 $x,y,x',y'\in C_3^0$ 及每个原 $\pi$，

$$
b_6(x\otimes y,\tau_\pi(x'\otimes y'))\ge0.
\tag{125.10}
$$

下列三项等价：存在保留固定前五层的完整**定义前缀至六**；
$L_6\subseteq L_6^\vee$；Cross 与 Four 同时成立。
等价条件成立时，取 $C_6=L_6$，纯点取全部 $\operatorname{ext}K$，
效应取整个 $[0,u_6]_{L_6^*}$，即满足这些定义条件。
此结论本身不保留全部原源合同；125.4给出这个 $L_6$ 的确切源障碍。

**证明（125.3）。** 各 $K_a^0$ 紧，有限个分割、扇区及置换的连续产品像构成紧并，
其有限维凸包 $K$ 紧且位于 $u_6=1$。
若 $r_jk_j$ 收敛，则 $r_j=u_6(r_jk_j)$ 收敛；正极限时由紧性取 $k_j$ 子列，
零极限时因 $K$ 有界而向量趋零。因此 $\operatorname{cone}K$ 闭，
迹在非零元素上严格正，锥尖。初等一体 PSD 产品张成 $W_6$ 且在锥内，故生成。
分别限制到 $a=1,2$ 或 $a=3$ 的同一基论证也给 $F_6,D_6$ 闭，
相加后的归一基是两基的凸包，所以 $L_6=F_6+D_6$，不遗漏闭包。
全部位置不变性由定义给出。

因 $(C_a^0)^*=T_aC_a^0$，所有低份普通乘积效应的生成锥恰为 $T_6L_6$。
全转置与原张量积及置换交换，故
$U_6=(T_6L_6)^*=T_6L_6^*=L_6^\vee$。
任何定义第六锥必须位于 $L_6$ 与 $U_6$ 之间；存在性因而等价于前者包含于后者。
若包含成立，$L_6$ 自己满足所有第六 min/max 界，基、极点、全 proper 区间按定义取全。
总次数至多五、整个 $S_2$、原种子和三供应不改。

还须逐类求 $b_6(L_6,L_6)\ge0$ 的条件。每个 $F_6$ 生成元的一侧次数至多二，
由125.2的源因子性质属于**旧** $E_6$；旧 $E_6$ 自 $b$ 极，故
$b_6(F_6,F_6)\ge0$。这一步没有把 $D_6$ 放进旧 $E_6$。

把 $x\otimes y$ 的 $3\mid3$ 生成元与任意 $1\mid5$ 生成元 $a\otimes z$ 配对。
一体源效应 $b_1(a,-)$ 切开包含该腿的三腿输入，输出在 $C_2^0$；
再与另一 $C_3^0$ 因子相乘，125.2给 $C_5^0$，与 $z$ 的配对非负。
对 $2\mid4$ 生成元 $h\otimes z$，若 $h$ 的两腿同处一个三腿输入，
整个二体源效应把它切成 $C_1^0$，再乘另一 $C_3^0$ 因子落入 $C_4^0$。
若两腿分属两个三腿输入，余下条件恰为 Cross。
最后 $D_6$ 与 $D_6$ 的全部配对恰为 Four。
$b$ 的对称性、双线性与连续性把这些类覆盖到所有非负和及闭包，得到等价。∎

### 125.D R0：乘积最小锥遗漏已支付的六 qubit 源

**命题 125.4（R0 的精确像与 proper 分离）。** 原种子 qubit 压缩满足

$$
q_6(L_6)=\mathrm{Bisep}_6
 :=\overline{\operatorname{cone}}\{X_J\otimes Y_{J^c}:\varnothing\ne J\subsetneq[6],\
 X_J\succeq0,\ Y_{J^c}\succeq0\}.
\tag{125.11}
$$

右侧是允许不同非空切口正和的六 qubit 二可分锥。
令 $g=(|000000\rangle+|111111\rangle)/\sqrt2$、$\Gamma=|g\rangle\langle g|$。
已支付的源态 $j_6\Gamma\in B_6$ 不在 $L_6$。
普通泛函

$$
f(z)=\operatorname{Tr}\bigl[(I_{64}/2-\Gamma)q_6(z)\bigr]
\tag{125.12}
$$

在 $L_6$ 上满足 $0\le f\le u_6/2$，所以 $2f\in[0,u_6]_{L_6^*}$，
但 $2f(j_6\Gamma)=-1$。

**证明（125.4）。** 对每个 $1\le a\le5$，原低份 retract 给
$q_a(C_a^0)=\mathrm{PSD}_{2^a}$，并且压缩与原产品和位置交换。
因此 $q_6$ 把每个 $L_6$ 产品生成元送到某一非空切口的 PSD 产品；
反向每个这种产品可用两个低份嵌入 $j_a,j_{6-a}$ 得到。
二可分归一基是有限切口的紧产品基之并的凸包，故紧且其锥闭。
连续性给 $q_6(L_6)\subseteq\mathrm{Bisep}_6$，反向嵌入和非负和给等号。

全部 $2^6-2=62$ 个有向非空切口上，$g$ 的两个非零 Schmidt 系数均为 $1/\sqrt2$。
于是对每个切口产品单位向量 $v$，$|\langle g,v\rangle|^2\le1/2$。
谱分解、正和及闭包给所有 $X\in\mathrm{Bisep}_6$ 的
$\operatorname{Tr}(\Gamma X)\le\operatorname{Tr}X/2$。
而 $\operatorname{Tr}\Gamma^2=\operatorname{Tr}\Gamma=1$，故 $\Gamma$ 不在此锥。
六 qubit GHZ 的量子制备加六个分别已付的实际嵌入是原源态，
若 $j_6\Gamma\in L_6$，压回就与上述不等式矛盾。

对 $z\in L_6$，$q_6z\succeq0$ 且 $\operatorname{Tr}q_6z\le u_6(z)$：
在每个低份产品上由两个原压缩预算相乘得到，再对正和及闭包成立。
GHZ 上界给 $f(z)\ge0$，PSD 性给 $f(z)\le\operatorname{Tr}q_6z/2\le u_6(z)/2$。
$q_6j_6=\mathrm{id}$ 给最后的 $-1$。
这只排除固定的乘积选择 $C_6=L_6$；该效应不是任何源相容模型上的负概率。
它不反驳 Cross、Four、另一个第六锥、另一低份族或全部原 allN 模型。∎

### 125.E P2：同一第四锥中的 Bell-Cross 与紧诊断

**命题 125.5（P2 的实际 Bell 归约）。** 固定一个实际最大 qutrit 块 $s$，
$\Omega_s=|\sum_{j=0}^2jj\rangle\langle\sum_{j=0}^2jj|$。
原 proper 帽为 $\beta_s/3$，其普通效应坐标是 $\Omega_s/3$，其他扇区为零。
对 $x,y\in C_3^0$，各选择一条支撑于实际 $s$ 的收缩腿，定义四原腿输出
$\kappa_s(x,y)$ 为

$$
b_4(\kappa_s(x,y),z)
 =b_6\bigl(\tau(x\otimes y),\tau'(\Omega_s/3\otimes z)\bigr)
\quad(z\in W_4),
\tag{125.13}
$$

其中 $\tau,\tau'$ 是该位置的原置换。
$b_4$ 非退化保证唯一性。Bell-Cross 要求每个此类输出属于**同一** $C_4^0$。
Cross 当且仅当 Bell-Cross。

记 $\delta_{\mathrm{cross}}$ 为(125.13)在上述支撑限制下的归一
$x,y\in K_3^0,z\in K_4^0$ 和全部位置上的最小值，
$\delta_{\mathrm{four}}$ 为(125.10)在四个 $K_3^0$ 输入及全部位置上的最小值。
二者均达到；125.3的弱定义前缀存在当且仅当两者非负。
在本章的完整共同源前提下，125.6进一步给 $\delta_{\mathrm{four}}=0$，
所以这个弱准则等价于 $\delta_{\mathrm{cross}}\ge0$。
$\delta_{\mathrm{cross}}$ 的数值未测，也未证明其非负。

**证明（125.5）。** 每个实际 $C_2^0$ 块中的 $h\succeq0$ 都是有限纯 dyad 和。
任意 $v\in\mathbb C^{n_i}\otimes\mathbb C^{n_j}$，因 $n_i,n_j\le3$，Schmidt 分解给矩形
$A:\mathbb C^3\to\mathbb C^{n_i}$、$B:\mathbb C^3\to\mathbb C^{n_j}$，使

$$
|v\rangle\langle v|=(\operatorname{Ad}_A\otimes\operatorname{Ad}_B)(\Omega_s).
\tag{125.14}
$$

这是两条实际最大腿上的 Bell 资源加两个独立一体映射。
对尺寸相容的 $X,Y$，直接循环迹得

$$
\begin{aligned}
b(AXA^*,Y)
 &=\operatorname{Tr}(X^TA^TY\overline A)\\
 &=b(X,A^TY\overline A)
 =b(X,\operatorname{Ad}_{A^T}Y).
\end{aligned}
\tag{125.15}
$$

故跨线拉回的是真正 $b$ 伴随 $\operatorname{Ad}_{A^T}$，不是普通迹伴随。
把 $A,B$ 分别拉到 $x,y$ 的所选实际腿，既定源旁观正性保证所得
$\widetilde x,\widetilde y$ 仍在同一 $C_3^0$，所选腿都在 $s$。
原 $h=|v\rangle\langle v|$ 测试恰为
$3b_4(\kappa_s(\widetilde x,\widetilde y),z)$；系数三来自未归一 $\Omega_s$
与 proper $\Omega_s/3$ 的差。有限 dyad 和覆盖全部 $h$ 和所有矩形实际扇区。
反向 $\Omega_s/3\in C_2^0$，所以 Cross 包含所有 Bell 测试。
$C_4^0=(C_4^0)^\vee$ 将全部 $z$ 的非负测试精确变成该同一锥的成员关系。

任意矩形 Kraus 可乘正标量缩成收缩矩阵；符号不等式的正齐次性再恢复系数。
这不改善物理成功预算。变换后输入若非零，严格正迹允许归一；若为零，测试就是零。
支撑条件是闭线性子空间限制，故归一支撑基是紧 $K_3^0$ 的闭子集。
张量、帽和配对连续，扇区与位置只有有限种，故上述两个最小值都达到。
对所有非零输入用齐次性，对零输入直接取零，得诊断等价。

由125.2，$\kappa_s(x,y)$ 自动在源上包络 $A_4$；这不把 $A_4$ 识别为 $C_4^0$。
非构造 $E$ 没有因此取得数值成员 oracle 或有限半代数描述。
一个负 Bell-Cross 读数只有在同一 $E$ 的全部输入成员资格和原源类型均确证时，
才排除该固定低份族的弱六份前缀；不能以 $A$、块正锥或无关 PSD 空间的成员替代。∎

### 125.F R1：Four 的四种连接均由共同源支付

**定理 125.6（R1 的 Four 冗余及零端点）。** 在定义125.1的完整共同 $E$/源前提下，
原 Four 对全部实际扇区、所有输入及全部六位置成立，而且
$\delta_{\mathrm{four}}=0$。
不要求 Cross，不要求两三腿输入的乘积在 $E_6$，也不要求新锥转置不变。

**证明（125.6）。** 把 Four 的四个输入画成两侧各两个三端口顶点
$X,Y$ 和 $X',Y'$。每条闭配对线从左侧接到右侧。
若 $X$ 与 $X'$ 之间有 $k$ 条线，则度数强制整个边重数表为

$$
\begin{pmatrix}k&3-k\\3-k&k\end{pmatrix},\qquad k=0,1,2,3.
\tag{125.16}
$$

顶点内部的原腿顺序由 $E$ 的置换不变性吸收，不改变实际扇区类型。
不相容扇区贡献零，相容块分别按下列四种情形处理。

| $k$ | 先收缩的顶点对 | 剩余标量及其正性 |
| --- | --- | --- |
| $0$ | $(X,Y')$、$(Y,X')$ 的全部三条线 | 两个原 $b_3$ 配对的乘积，均由 $E_3=E_3^\vee$ 非负 |
| $3$ | $(X,X')$、$(Y,Y')$ 的全部三条线 | 同样是两个非负的 $b_3$ 配对 |
| $1$ | $(X,Y')$、$(Y,X')$ 各自的两条公共线 | 125.2给两个整个实际二腿 PSD 输出 $R,R'$，余两线为 $b_2(R,\tau R')\ge0$ |
| $2$ | $(X,X')$、$(Y,Y')$ 各自的两条公共线 | 同样由双线收缩得到二腿 PSD 输出，再以原两腿重排配对 |

后两行的输出公式正是(125.7)。剩余两条线使用其相同 ket、bra 指标，
所以数值恰为所列 $b_2$，无隐藏的某输入转置。
整个 $C_2^0$ 自 $b$ 极，故这些标量非负。
每个原置换都属于其中一种；所有块的有限和、非归一输入和零输入由多线性覆盖，
闭锥极限由连续性覆盖。使用原 proper 帽只乘固定正预算系数。

所有归一测试遂非负。取一个实际最大块中的源投影
$a=|000\rangle\langle000|$、$d=|111\rangle\langle111|$，它们都在 $K_3^0$。
恒等位置给 $b_6(a\otimes a,d\otimes d)=0$。
125.5的紧最小值因而恰为零。
Four 在这些共同源前提下已付，不能再当成与 Cross 独立的未付条件；
它对不相关的任意有限锥族并非无条件结论。
Cross 是否也从这些前提推出，以及更强的 R3、R4 是否互相独立，均未在此证明。∎

### 125.G R2：单种子的源像饱和

**命题 125.7（R2 的最小源系统）。** 对每个实际字 $v$，若 $0\le|v|\le5$，
取所有 $E(v)$ 元素为旧种子，含 $E(\varnothing)=\mathbb R_+$。
对每个实际六字 $v$，另取
$\mathscr D_v$ 为所有按原 $3\mid3$ 位置放置的 $x\otimes y$，
其中两因子分别来自该位置实际三字的同一 $E$。
$D_6$ 是这些种子的直和闭生成锥。
对**每个**源对象字 $w$ 定义

$$
G(w)=\overline{\operatorname{cone}}\{S(f)r:
 r\text{ 是一个旧种子或一个 }\mathscr D_v\text{ 种子},\
 f:\operatorname{type}(r)\to w\text{ 是原源箭头}\}.
\tag{125.17}
$$

这是一个种子的像取正和及闭包，不免费把两个任意 $G$ 元素相乘，
也不为种子在 $\mathcal D$ 中增加态箭头。
$G$ 是包含全部上述种子的最小闭 $S$-system，且逐字有

$$
B(w)\subseteq G(w)\subseteq A(w),\qquad L_6\subseteq G_6.
\tag{125.18}
$$

每层 $G(w)$ proper、迹严格正，整个归一基紧；$j_6\Gamma\in G_6$。
但尚未证明 $G(a)=E(a)$ 对所有实际 $|a|\le5$ 成立，也未证明 $G_6\subseteq U_6$。

**证明（125.7）。** 原源 $h:w\to w'$ 发送生成元 $S(f)r$ 为 $S(hf)r$。
正和及连续性给 $S(h)G(w)\subseteq G(w')$。
任何含全部种子的闭 $S$-system 都必须含这些像及其闭正和，故最小。
标量种子沿原源态的像生成 $B$，从而 $B\subseteq G$。
旧种子在 $E\subseteq A$；每个新 $\mathscr D_v$ 种子由125.2对**全部**源效应非负，
也在 $A(v)$。$A$ 是 $S$-system，所以全部源像、正和和闭包仍在 $A$。

初等乘积 PSD dyad 属于 $B$ 并张成每个实现空间，故 $G$ 生成。
$A$ 包含于尖的乘积块正锥，故 $G$ 尖。
更明确地，乘积块正的 $z$ 若迹零，在任一乘积正交基上，所有非负对角读数之和为零。
任意乘积单位向量都能扩成这样的基，所以所有乘积 dyad 读数都为零；
它们张成空间，遂 $z=0$。这给 $A$ 以及 $G$ 的严格正迹。
闭锥与严格正迹相交的迹一截面必紧：否则归一化无界序列将产生非零迹零锥向量。
因此所有整个基都紧，不需另选一个有界状态菜单。

$D_6\subseteq G_6$ 由恒等箭头。
每个 $F_6$ 产品的一体或二体因子是有限源 dyad 和，附加在另一旧种子上是源箭头，
故 $F_6\subseteq G_6$，得到 $L_6\subseteq G_6$。
125.4中的 GHZ 是源态，故在 $B_6\subseteq G_6$。
此构造补入了 $L_6$ 的确切漏态，却没有自动保留固定低层或第六最大界。
量子字、$Q_kA_i$ 和两实际腿的 $B=A$ 夹逼则自动保留其精确锥。
源正性不是任意补全态的单式产品正性，故 $G$ 还不是原 allN 模型。∎

### 125.H R3/R4：包含任意高中间次数的精确等价

**定理 125.8（R3/R4 的源相容六份准则）。** 固定定义125.1的完整源和低族。
考虑以下两个符号族：

$$
\begin{aligned}
\mathrm{R3}:\quad&b_a(S(f)d,z)\ge0,\\
&|v|=6,\ d\in\mathscr D_v,\quad a\text{ 为实际字},\ 0\le|a|\le5,\quad
 z\in E(a),\quad f\in\mathcal D(v,a);\\[2mm]
\mathrm{R4}:\quad&b_{v'}(S(f)d,d')\ge0,\\
&|v|=|v'|=6,\quad d\in\mathscr D_v,\ d'\in\mathscr D_{v'},\quad
 f\in\mathcal D(v,v').
\end{aligned}
\tag{125.19}
$$

$\mathscr D$ 包括所有实际扇区、原 $3\mid3$ 位置。
$f$ 遍历原源的**全部**复合：任意有限量子对象、旁观字、任意有限实际中间次数，
包括大于六的次数；跨扇区矩形箭头、紧 $b$ 伴随、原逆置换和重括号均在范围内。
不能仅因显示端点次数至多六而删掉高中间次数。
零输入给零；符号重缩放不改变原源预算，也不构成有限数值测试清单。

本定理中的“源相容六份前缀”严格指存在同一源**每个字**上的闭 proper 锥族 $H(w)$，
满足 $B\subseteq H\subseteq A$，每个原源箭头均正；每个实际 $|a|\le5$ 有
$H(a)=E(a)$；量子及 $Q_kA_i$ 锚保持原精确 PSD／$\mathcal K$；
实际总次数至多六满足125.1的全部原定义条件，且保留所有已支付的原源
retract、旁观、return、真实零扩张和预算合同。
它是具有六份定义产品律的 all-word 源系统；总次数大于六的原 min/max 产品律仍是原目标义务。

下列三种表述等价：

1. 存在上述源相容六份前缀 $H$。
2. (125.17)的显式源饱和满足 $G(a)=E(a)$ 对每个实际 $|a|\le5$，且 $G_6\subseteq U_6$。
3. R3 与 R4 都成立。

等价条件成立时可取 $H=G$。
还可条件性地取得另一个自 $b$ 极的 $S$-system

$$
G\subseteq E'=E'^\vee\subseteq G^\vee,\qquad
E'(a)=E(a)\ (|a|\le5),\qquad L_6\subseteq E'_6\subseteq U_6.
\tag{125.20}
$$

这是另行应用补全定理的结论，不假定 $L_6$ 或 $G$ 自极，也不识别 $E'_6$ 与旧 $E_6$。
R3/R4 的全称符号尚未支付，因此本定理没有给出无条件源相容六份前缀。

**证明（125.8）。** 若存在 $H$，它含所有旧种子；第六最小界使它含全部
$\mathscr D_v$ 种子。125.7的最小性遂给每个字上 $G(w)\subseteq H(w)$。
在低实际字，反向 $E(a)\subseteq G(a)$ 已由种子给出，故 $G(a)=E(a)$。
第六最大界给 $G_6\subseteq H_6\subseteq U_6$。
也可直接看两族必要性：$S(f)d\in H(a)=E(a)$ 与 $z\in E(a)=E(a)^\vee$ 配对给 R3；
$S(f)d\in H(v')\subseteq U_6=L_6^\vee$，而 $d'\in L_6$，给 R4。
此处没有假设 $H_6$ 自极。

反设 R3/R4。对低目标实际字 $a$，旧种子的每个源像由旧 $E$ 的源正性落在 $E(a)$；
新种子的每个源像与所有 $z\in E(a)$ 配对非负，由 R3 和自极性也在 $E(a)$。
正和、闭包给 $G(a)\subseteq E(a)$；恒等像种子给反向，故相等。
反过来，只要这个低层相等成立，就立即有 R3。

证明 $G_6\subseteq U_6=L_6^\vee$ 需对每个源像生成元分别检验整个 $F_6$ 与 $D_6$，
不能只检验裸新种子。分四类如下。

旧种子 $z\in E(a)$ 经 $h:a\to v$ 到六字时，$S(h)z$ 在**旧** $E(v)$。
$F_6$ 也在旧 $E_6$，故该像与所有 $F_6$ 配对非负。
与 $d\in\mathscr D_v$ 的配对则移动紧伴随为

$$
b_v(S(h)z,d)=b_a(z,S(h^\flat)d)\ge0,
\tag{125.21}
$$

最后一步恰为 R3，含原对偶字重排。

新种子 $d$ 经 $g$ 到六字时，每个 $F_6$ 生成元都能写成有限正和
$\sum_\nu S(h_\nu)z_\nu$，其中 $z_\nu$ 为旧低种子，
$h_\nu$ 是附加一体或二体源态并置换的原箭头。
于是

$$
b_6(S(g)d,S(h_\nu)z_\nu)
 =b_{\operatorname{type}(z_\nu)}(S(h_\nu^\flat g)d,z_\nu)\ge0
\tag{125.22}
$$

由 R3 支付。与 $D_6$ 生成元的配对正是 R4。
这些 $h^\flat g$ 可以经过高次数，仍在(125.19)的全称源范围内。
双线性、正和、连续性覆盖全部 $G_6$ 和 $L_6$，所以 $G_6\subseteq U_6$。
反向，若 $G_6\subseteq U_6$，源正性给 $S(f)d\in G_6$，与 $d'\in L_6$ 配对即 R4。
至此第二、三种表述等价。

在第二种表述下，125.7已有每个字的 proper 性、严格迹和源正性。
低层就是固定 $E$；第六最小界由 $L_6\subseteq G_6$，最大界由 $G_6\subseteq U_6$。
低于六的所有界沿固定五份前缀，空侧沿标量单位。
原位置及逆为源箭头，重括号是同一线性识别。
取每层整个迹一基、所有极点和整个普通对偶 proper 区间，便得到余下全部原定义条件。
$C_1,C_2$、整个 $S_2$ 和三条完整供应均不变。
125.9证明完整源 retract 和预算，因此 $H=G$ 给第一种表述，完成全部必要与充分方向。

最后证明可选(125.20)。在任意源字 $w$，取两个源像生成元
$S(h)r,S(g)s$。紧伴随恒等式给

$$
b_w(S(h)r,S(g)s)
 =b_{\operatorname{type}(r)}(r,S(h^\flat g)s).
\tag{125.23}
$$

两个旧种子时，由旧 $E$ 的源正性和自极性非负；一个旧、一个新时，由 R3，
必要时用 $b$ 对称性；两个新时由 R4。
这涵盖任意不同实际种子字和任意源目标字，故正和及闭包给**每个字**的 $G\subseteq G^\vee$。

使用 Netzer，[arXiv:2408.07389v1](https://arxiv.org/abs/2408.07389v1)定理2.2：
同一 $S:\mathcal D\to\mathrm{FVec}_{\mathbb R}$ 是123.2已给的 star-autonomous stem，
每个 intrinsic 锥 $A(w)$ proper，基空间 $X=\mathbb R$ 用普通标量乘法正定识别于 $X'$，
$G$ 是刚证的 $S$-system 且 $G\subseteq G^\vee$。
层上不定 $b_w$ 是对象对偶，绝不拿来充当该定理要求的基空间正定内积。
定理遂给 $E'$。对低实际字，
$E(a)=G(a)\subseteq E'(a)\subseteq G(a)^\vee=E(a)$，故低层精确保持。
$E'_6$ 含 $L_6$，自极性又给 $E'_6\subseteq L_6^\vee=U_6$。
它仍是同一源的 $S$-system，故全部源箭头和旁观扩张仍正；
$B\subseteq E'\subseteq A$ 保证 proper 性、严格迹及125.9的预算。
这里只应用锥系统补全，没有应用任意 $E'$ 输入的结合有序张量积定理。∎

R3 包含 Cross：把一条三腿输入与另一条各抽一腿接原二体源效应，余四腿为输出；
R3 对所有 $E_4$ 测试的非负性，按自极性就是125.5的同一第四锥成员关系。
R4 的恒等及原置换子族包含 Four，125.6已支付这个子族；它不支付全部源布线的 R4。
没有证明裸 Cross 足以推出全部 R3/R4，也不声称 R3 与 R4 独立。
一个负 R3 或 R4 值，只有在**同一固定低族**中所有种子成员及该完整源箭头均准确合型时，
才排除这些固定低锥的源相容六份延伸；不能据此排除别的低族、所有中间匹配锥或全部 allN 模型。

### 125.I 所有已付源合同、全普通对偶与原质量

**命题 125.9（双向 retract 与整个 proper 区间）。** 在125.8的等价条件下，
取 $H=G$ 或条件补全 $E'$。它保留全部既定源态、所有原源箭头及其任意有限旁观扩张，
包括嵌入所有有限 qubit 字的整个量子 PSD、同一含相位种子、有限码和共同 $\mathcal K$ 资源。
全部 quantum-word 和 $Q_kA_i$ 锥分别仍精确为原 PSD 和 $\mathcal K$。
对任一原已支付的源嵌入／压缩 $j:w'\to w,q:w\to w'$，$qj=\mathrm{id}$，有

$$
\begin{aligned}
q(H(w))&=H(w'),\\
H(w)\cap\operatorname{im}j&=j(H(w'))=jq(H(w)),\\
j^*(H(w)^*)&=H(w')^*,\\
j^*([0,u_w]_{H(w)^*})&=[0,u_{w'}]_{H(w')^*}.
\end{aligned}
\tag{125.24}
$$

最后一式使用原 $u_wj=u_{w'}$ 和 $0\le u_{w'}q\le u_w$。
其范围是整个普通对偶与整个 proper 区间。

**证明（125.9）。** $B\subseteq H\subseteq A$ 与已付 $B=A$ 锚给精确量子、混合类型。
两条源箭头 $j,q$ 分别正，故
$qH(w)\subseteq H(w')$、$jH(w')\subseteq H(w)$；$qj=\mathrm{id}$ 给两个等式的反向包含。
这在任意旁观字上仍成立，涵盖实际标量／qubit 角、所有原中心扇区与有限实码。
没有从普通伴随、逆或同维数识别推断任何另一个方向正。

若 $f\in H(w')^*$，则 $fq\in H(w)^*$ 且 $(fq)j=f$；
反向任意母锥正泛函沿 $j$ 限制均正，故全对偶限制恰为全子对偶。
若 $0\le f\le u_{w'}$，则

$$
0\le fq\le u_{w'}q\le u_w.
\tag{125.25}
$$

反向母 proper 效应沿 $j$ 的限制介于零与 $u_wj=u_{w'}$ 之间，给整个 proper 区间等号。

每个已付源预算的迹亏损是源正效应或其非负和，故在 $A$ 上非负，因而在整个 $H$ 上非负。
特别是收缩 Kraus 的亏损 $I-A^*A$ 连同所有旁观迹效应仍为源效应；
压缩不增迹，等距嵌入保迹。原码 $c^*$ 的 $11$ 输出、码外交叉元和其他扇区仍真正为零。
线性映射保持真零；严格正迹保证正输出若质量零则恰为零。
只对质量严格正的支条件化。

两条混合 return 方向各自沿原源实现，而不是以其中一个方向的逆或普通迹伴随代付。
在本固定 $t=2/3$ 族中，沿VII卷105.6取

$$
\mathcal D_a(X)=aX+(1-a)\operatorname{Tr}(X)I_3/3,\qquad
p=5/8,\quad r=-1/5,\quad pr=-1/8.
\tag{125.26}
$$

原参考在前的 $J(\mathcal D_p)=3\tau_{2/3}$、$J(\mathcal D_r)=3\tau_{-1/15}$
是共同 $\mathcal K_{3,3}$ 资源，交换参考／输出后的反向资源也分别在原源中。
经原码的两个真正零扩张仍为

$$
\begin{aligned}
A_a^0(z)&=\iota_s\mathcal D_a(c^*q_2(z)c),\\
B_a^0(y)&=j_2\bigl(c\mathcal D_a(\pi_s y)c^*\bigr),\qquad a\in\{p,r\}.
\end{aligned}
\tag{125.27}
$$

这里 $\pi_s$ 是原块提取。
$u_1A_a^0$ 恰为两种子腿的码接受效应，$u_2B_a^0$ 恰为实际 $s$ 块接受效应；
所有旁观扩张的不增质量和接受部分保迹均沿相同源效应亏损保持。
这只保持已经支付的两方向，不赋予 $\mathcal D_a^{-1}$ 正性，
也不把非 PSD 的 $J(\mathcal D_r)$ 当成普通 CP 资源。
对任意补全新增映射的全局原 Choi 等价，其全高阶原产品前提仍未支付。

原种子 $\Delta_{r,2}$ 的质量二不变。
归一 $\Delta_{r,2}/2$ 经原 proper 确认切片给 $\Omega_{r,2}/4$，质量 $1/2$。
实际块满杯 $\Omega_i$ 的质量为 $n_i$，帽 $\beta_i/n_i$ proper；
全对角杯质量为 $R=\sum_i n_i$，全帽 $\beta/3$ proper，非匹配扇区读数为零。
归一全杯与该帽的 $m$ 次 snake 预算仍是 $(3R)^{-m}$。
所有系数沿123.2及VII卷104.4、104.11保持；符号证明的正重缩放不提升成功概率，
也不授权确定性后选择、物理制备事件或额外误差预算。∎

### 125.J P3：原生连接与 Hilbert 反射的不同符号

**命题 125.10（P3 的原生 signed Gram 与秩惯性）。** 对源边界字 $w$，
令 $\mathcal F_w$ 为源开放态的形式有限实线性组合空间，
$v:\mathcal F_w\to S(w)$ 为其原张量求值。原生连接型为

$$
M_w(F,G)=b_w(v(F),v(G)).
\tag{125.28}
$$

源乘积 dyad 张成 $S(w)$，所以该型的秩为 $\dim_{\mathbb R}S(w)$。
若边界包含非平凡复矩阵因子，它并非 PSD。
在一个实际最大 qutrit 中，置

$$
\psi_\pm=(e_0\pm i e_1)/\sqrt2,\qquad P_\pm=|\psi_\pm\rangle\langle\psi_\pm|,
\tag{125.29}
$$

并在 $e_2$ 和其他扇区上送零。
两个允许一体纯源态的原生矩阵是 $\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$，
按原 proper qutrit 帽缩放后为

$$
\frac13\begin{pmatrix}0&1\\1&0\end{pmatrix},\qquad
\operatorname{spec}=\{1/3,-1/3\},\qquad
(1,-1)M(1,-1)^T=-2/3.
\tag{125.30}
$$

每个单独源标量仍非负。

**证明（125.10）。** $P_+^T=P_-$、$\operatorname{Tr}(P_+P_-)=0$、
$\operatorname{Tr}P_+^2=1$ 直接给(125.30)。
固定扇区字的 Hilbert 维数为 $D$ 时，全转置在 $\operatorname{Herm}_D$ 上的正一空间
是实对称矩阵，维数 $D(D+1)/2$；负一空间是纯虚反对称 Hermitian 矩阵，维数 $D(D-1)/2$。
普通迹内积正定，而 $b(X,Y)=\langle TX,Y\rangle_{\operatorname{Tr}}$，
故这就是 $b$ 的正、负惯性，满秩为 $D^2$。

源乘积 dyad 含一个实基；在这样的基上拉回 $b$ 达到上述惯性及满秩。
任意有限源矩阵都通过 $S(w)$ 分解，故不能超过它们；
形式源空间的冗余只加入零空间。
对实际直和令 $d_0=\sum_i n_i^2$、$r_0=\sum_i n_i$，
$T$ 在 $V$ 上的迹为 $r_0$，在 $W_N$ 上为 $r_0^N$，遂

$$
\operatorname{rank}M_N=d_0^N,\qquad
\operatorname{inertia}_{\pm}(M_N)=\frac{d_0^N\pm r_0^N}{2}.
\tag{125.31}
$$

这是已明确定义的有类型端口连接型的秩，不是顶点识别图代数连接矩阵的秩。
负 signed 组合是在反射正性检验的形式实空间中，不被宣告为物理混合态。

另一个数值核

$$
H_w(F,G)=b_w(T_wv(F),v(G))
 =\operatorname{Tr}(v(F)v(G))
\tag{125.32}
$$

确为正 Hilbert feature Gram，具有同一有限特征秩。
它使用不同反射。要把它解释成 admissible 反射图求值，须构造整个有类型源生成集的 involution，
保持组合、标签、原锚、相位和预算，并在边界上实现 $T_w$。
此桥未给出，且不假定共同 $\mathcal K/E$、$L_6$ 或 $G$ 转置不变。
即使正 Gram 重建了求值实空间，也尚未选择原有序锥，
更未证明任意补全态的产品或整个第六普通对偶的非负性。∎

### 125.K P3：实的 proper 局部矩阵也不必 PSD

**命题 125.11（P3 的六端口 localizer）。** 在同一个实际最大块取
$a=|000\rangle\langle000|$、$d=|111\rangle\langle111|$，其他扇区为零，并令

$$
Z=(a\otimes d+d\otimes a)/2.
\tag{125.33}
$$

$Z$ 同时是源态和普通 proper 源效应；其余量 $I_6-Z$ 为源正效应。
对所有 $x,y\in C_3^0$，所需锥双线性读数非负：

$$
L_Z(x,y)=b_6(x\otimes y,Z)
 =\tfrac12\bigl(b_3(x,a)b_3(y,d)+b_3(x,d)b_3(y,a)\bigr)\ge0.
\tag{125.34}
$$

但在源输入 $(a,d)$ 上的 localizing 矩阵是

$$
\begin{pmatrix}0&1/2\\1/2&0\end{pmatrix},\qquad
\operatorname{spec}=\{1/2,-1/2\},\qquad
(1,-1)L(1,-1)^T=-1.
\tag{125.35}
$$

**证明（125.11）。** $a,d$ 都是原计算基一体投影的产品。
$Z$ 是其有限非负源和。整个六腿分块计算基上，$I_6-Z$ 在两个所选字上的系数为 $1/2$，
在其余字及其他扇区上的系数为一，故是非负的乘积源效应和。
每个 $b_3(-,a),b_3(-,d)$ 是源效应，在 $E_3$ 上非负，得到(125.34)。
又 $b_3(a,a)=b_3(d,d)=1$、$b_3(a,d)=0$，故给(125.35)。
全部矩阵为实，添加数值全转置反射也不改变此反例。
因此“在正锥的两个输入上非负”不能替换成“在所有 signed 输入上的局部矩阵 PSD”。
这排除的是该更强替代条件，不是原层级，也不是负物理概率；
底层源正性仍是已支付结果，没有由此取得六份产品成员关系。∎

### 125.L 原始文献的准确适用面

锥系统框架沿 De les Coves–van der Eyden–Netzer，
[*Beyond Operator Systems*, arXiv:2312.13983v1](https://arxiv.org/abs/2312.13983v1)，
Definitions 2.8–2.9、Lemma 3.5、Definition 3.6、Remark 3.7、Definition 3.16及Theorem 3.17。
其源内禀／余内禀锥是对偶对象上的 $A/B$，对偶反序；
指定箭头下的 $S$-system 不据此成为 star-autonomous 或单式有序锥族。
125.7只用源像闭包；125.8的可选补全才使用
Netzer，[*Self-Dual Cone Systems and Tensor Products*, arXiv:2408.07389v1](https://arxiv.org/abs/2408.07389v1)，定理2.2。
其全部条件及 $X=\mathbb R$ 的正定识别已在125.8中逐项对应。
该文另论二元张量积的 Definition 3.1、Theorem 3.2，
也不支付本题指定的结合性、全部原位置产品律或旧 $E_6$ 中的产品成员。

相关图重建定理具有下列不同的图域和全称前提；它们只作成熟中间理论的适用边界，
没有被应用成125.8以外的新有序锥补全。

Freedman–Lovász–Schrijver，
[*Reflection positivity, rank connectivity, and homomorphism of graphs*, arXiv:math/0404468v1](https://arxiv.org/abs/math/0404468v1)，
§§2.1–2.2、Theorems 2.3–2.4的归一表述，针对所有有限无自环多重图上的实同构不变参数 $f$。
连接矩阵 $M(f,k)$ 的乘法是识别相同标签的**顶点**，要求每个 $k$ 的每个有限主子矩阵 PSD，
且存在同一个正整数 $q$ 使所有 $k\ge0$ 均有 $\operatorname{rank}M(f,k)\le q^k$。
保留 $f(\varnothing)=1$；在此归一前提下，$k=0$ 的秩和 PSD 条件经 Proposition 2.1给乘法性。
结论是具有正顶点权和实对称边权的加权图表示。
该 v1 的 Theorem 2.4显示陈述未重复 Proposition 2.1所需的空图归一，
此处只使用明确归一形式；常数参数 $f(G)=2$ 的连接矩阵秩一且 PSD，
说明仅秩与 PSD 不能补出 $f(\varnothing)=1$。
125.31的原有类型端口秩不是该顶点识别矩阵的秩；所需顶点代数对应与反射正性未给出。

Szegedy，[*Edge coloring models and reflection positivity*, arXiv:math/0505035v1](https://arxiv.org/abs/math/0505035v1)，
§§2.1–2.3、Proposition 2.1与Theorem 2.2，使用包含多重边、自环和无顶点圆的全部有限无向图。
实参数须 $f(\varnothing)=1$、对不交并乘法，并对**每个** $k$ 的全部开放片段的形式实线性组合满足
$f(\operatorname{glue}(F,F))\ge0$，即完整片段矩阵 PSD。
结论为实有限色边模型 $t:\mathbb N^d\to\mathbb R$，颜色数由圆值给出；
该定理不另要求指数秩界。
端口连接虽接近紧源，却用正 Euclidean 色度量及其无类型局部规则。
125.30反驳原生相同装饰直接满足其 Gram 前提；125.32的不同反射仍需完整源 involution。
即使 scalar 模型存在，也不授予实际量子寄存器或任意补全锥产品。

Draisma–Gijswijt–Lovász–Regts–Schrijver，
[*Characterizing partition functions of the vertex model*, arXiv:1102.4985v1](https://arxiv.org/abs/1102.4985v1)，
Theorems 1–2及式(3)–(6)，在代数闭特征零域 $\mathbb F$ 上讨论全部有限无向图，含自环与多重边。
乘法性含 $f(\varnothing)=1$。
对 $G=(V,E)$、$U\subseteq V$、$s:U\to V$，令 $G_s$ 为给每个 $u$ 加边 $us(u)$ 的图，
重边保留。Theorem 1的 $k$ 色刻画要求对所有 $G,U,s$、$|U|=k+1$ 有

$$
\sum_{\pi\in\mathfrak S_U}\operatorname{sgn}(\pi)f(G_{s\circ\pi})=0.
\tag{125.36}
$$

Theorem 2先假设已有一个 $k$ 色表示 $y:\mathbb N^k\to\mathbb F$，
再以所有 $|U|=r+1$、$s:U\to V\setminus U$ 的收缩恒等式

$$
\sum_{\pi\in\mathfrak S_U}\operatorname{sgn}(\pi)f(G/(s\circ\pi))=0
\tag{125.37}
$$

刻画可换取一个矩矩阵 $(y_{\alpha+\beta})$ 秩至多 $r$ 的表示。
这里 $G/s$ 指先形成 $G_s$ 再收缩新加的全部边。
前一定理允许 $s(U)$ 与 $U$ 相交，后一定理要求不交，二者不可混用。
原源未实现这些全部加边／收缩操作及恒等式；有限边界张量维数不是矩矩阵有限秩。
代数闭标量场也不提供保持实有序锥、原种子和预算的变换。

Schrijver，[*Characterizing partition functions of the vertex model by rank growth*, arXiv:1211.3561v1](https://arxiv.org/abs/1211.3561v1)，
Theorem 1及式(3)–(5)，对含自环、多重边和无顶点圆 $\bigcirc$ 的全部图上的复参数要求
$f(\varnothing)=1$、$f(\bigcirc)\in\mathbb R$，以及对**每个** $k$ 的全部 $k$ 片段连接矩阵

$$
C_{f,k}(F,G)=f(F\mathbin{\cdot}G),\qquad
\operatorname{rank}C_{f,k}\le f(\bigcirc)^k.
\tag{125.38}
$$

结论是复有限色 vertex-model 表示，其整数色数由证明取得。
每个矩阵仅仅有限秩不是这一统一增长假设。
125.28尚未与该全部无类型图族识别；即使在复数上把不定对称度量改为标准形式，
也未证明保持原实锥、开放张量、相位种子、全效应或预算。

Draisma–Regts，[*Tensor invariants for certain subgroups of the orthogonal group*, arXiv:1202.3940v1](https://arxiv.org/abs/1202.3940v1)，
Theorems 1–3，先有代数闭特征零域上、标准等价非退化对称形式中的实际标量 vertex model
$h\in(\operatorname{Sym}V^*)^*$。
Theorem 1可替换为 $h'$，保留所有**闭图** partition functions，并使每个边连接秩等于
$\dim(V^{\otimes k})^{\operatorname{Stab}(h')}$。
实版本 Theorem 2使用标准正定形式与紧正交群；非紧形式的相应断言不成立。
原 $b$ 在实域不定，且没有证明替换 $h\mapsto h'$ 保持原类型、开放态张量、
含相位锚、全部普通效应及源预算。
不变张量空间或其秩等式也不单独选出原正锥。

Regts–Schrijver–Sevenster，
[*On partition functions for 3-graphs*, arXiv:1503.00337v1](https://arxiv.org/abs/1503.00337v1)，
式(1)–(3)与主定理，图域为连通三价 cyclic graphs，含自环、多重边和例外的无顶点圆，
并乘法扩张到所有不交并。
$k$-join 对两图的有序不同顶点选择各 $k$ 个；对每一配对，按其 cyclic 顺序将三种重接取**平均**，
再对全部顶点选择求和。因此每个固定选择是 $3^{-k}$ 乘三种重接的全展开和。
weak reflection positivity 要求对每个 $k$，整个
$(f(G\mathbin{\vee^k}H))_{G,H}$ 的每个有限主子矩阵 PSD，等价于全部 signed 图组合的非负二次型。
结论为某个实 $c\in((\mathbb R^n)^{\otimes3})^{C_3}$ 的标量 partition function；圆值为 $n$。
原 $E_3$ 元素带任意实际标签，不预设 cyclic invariance，源还有别的顶点度数与箭头种类。
单个闭源标量非负不支付这些弱反射矩阵 PSD；
$3^{-k}$ 的正系数也不改变125.30、125.35的符号障碍。
该定理重建标量张量，不重建原自极锥族。

这些文献陈述及其既有中间用途属于 literature-attested；
125.3—125.11的原类型综合推导属于 repo-derived，不主张世界范围的新颖性或优先权。
已支付的二元补全、原源路径／匹配／滤波结果依所引条目复用，
没有把它们重命名为新的 allN 证明。

### 125.M 普通解释与仍须满足的原目标

Four 的四个三腿输入只有四种连接形状：要么直接拆成两个已知非负三腿读数，
要么先把两对双线接掉，每对留下一个已知正的二腿对象，再把余线接完。
因此在同一共同源和完整低层前提下，它已经非负，而且正交源输入使最小值恰为零。
这说明 Four 冗余，不能据此宣布 Cross 或所有复杂源布线都已解决。

只收集低层产品的 $L_6$ 太小：六 qubit GHZ 是必须保留的源态，
却被这个锥的一个完整 proper 效应以 $-1$ 分开。
这个负数揭示候选锥漏掉合法源态，不是合法模型产生了负概率。
把每个旧低层元素或每个新 $3\mid3$ 产品，分别沿全部原源箭头推进，再取闭正和，
得到最小源饱和 $G$，于是 GHZ 和全部固定源合同都得到保留。
但源饱和也可能扩大旧低层或冲破第六最大界；R3、R4恰好检验这两个剩余问题。
它们要求所有原源复合，即便途中有任意高次数或任意有限量子处理，也不能漏掉。

这个 iff 的意义是把正确条件写全，并证明两方向都成立。
它没有证明这些条件本身成立。
Cross／Bell-Cross 进入**同一**第四锥的全称非负性、R3/R4全部符号，
以及源饱和实际保持前五层和满足第六最大界，仍为未付义务。
需要数值搜索时，还缺同一非构造 $E_3,E_4$ 的可认证成员接口；
紧最小值存在不提供数值 oracle，$\delta_{\mathrm{cross}}$ 仍未测。
正确合型的负测试只排除该固定低份族，不能提升为所有模型的排除。

另选 $G_6$ 或条件性 $E'_6$ 也不支付旧预选 $E_6$ 的
$C_3^0\otimes_{\min}C_3^0\subseteq E_6$。
所有更高原次数、每个原位置的 min/max 产品律与整个普通对偶、
消费这些高次数的全局原 Choi 推论，仍须在同一个原 allN 实现中成立。
未构造结合、单式的全原层级，未证明 $\mathsf{Fusion}_3$ 或 $t=1$，
也未给出保持全部原合同、具有统一严格 $t<1$ 间隙的合法 allN 模型。
逐有限阶段的结果或趋向一的截断参数不满足统一严格间隙的要求。

原生帽配对、添加转置后的 Hilbert Gram、顶点识别连接矩阵、片段端口矩阵及
$k$-join 矩阵各有自己的运算与假设。
一个有限维标量张量表示不自动选择原正锥，正 feature Gram 也不补出产品成员关系。
最后，数学源图式与锥内成员不提供实际制备来源，
完整记录／事件／控制仪器、物理动力学和实际连续时间作用、Hamiltonian 的选择及其物理能量识别与能量标定、物理钟及其校准、物理单位选择与数值 $\hbar$
仍须另建桥梁。上述条件六份结果不替代这些原目标。

## 追加锚（本行以下为增补区）

## 126. 固定共同源的精确端口标准形与 R3/R4 的量子输出判据

### 126.A 同一源、固定边界与原生指标

**定义 126.1（部分匹配端口数据）。** 固定123.2、125.1中的同一个
$\mathcal D,S,\mathcal K,E$，并沿用式(125.6)的 $B(w),A(w)$ 记号。
所有原 $W_N$、扇区标签、块迹、位置置换及其逆、重括号和空侧单位保持不变。
实际 $A_i$ 与辅助量子 $Q_k$ 是两类对象；实际标量、qubit 和 qutrit 仍有各自原类型。
尺寸一、二的实际对象只经各自已支付的源双向接口重型，
实际 qutrit 字不因同维数而成为免费集体量子寄存器。

本章始终保留125.1的整个基、所有极点、整个普通对偶 proper 区间、
完整 $S_2$（含纠缠、零权与重复标签）及三条完整条件供应，
同一含相位种子 $\Delta_{r,2}$ 的质量二、$\Delta_{r,2}/2$、
实码 $c=(00,01,10)$ 与 $c^*11=0$，以及125.9的双向 retract、
全部旁观、return、真零扩张和原质量预算。
本章只把指定源的效应及125.8的检验重写为精确标准形，不选择另一个 $E$ 或第六锥。

任取有限实际字

$$
w=A_{i_1}\cdots A_{i_m},\qquad n_j=n_{i_j}\in\{1,2,3\},\qquad
W_w=\operatorname{Herm}\!\left(\bigotimes_{j=1}^m\mathbb C^{n_j}\right)
\quad\text{（实向量空间）}.
\tag{126.1}
$$

所有指标、转置和端口顺序均用原固定基；紧对偶字反序由原逆置换运输。
仍用 $b_w(Y,Z)=\operatorname{Tr}(Y^TZ)$、$K^\vee=T_wK^*$ 和
$\Phi^\flat=T\Phi^\dagger T$，特别是
$\operatorname{Ad}_A^\flat=\operatorname{Ad}_{A^T}$。
不假定 $E,\mathcal K,L_6,G$ 或任何新实际锥全转置不变。

一个标准形数据由以下对象组成。

1. 在带标签位置 $[m]$ 上取部分匹配 $\mu$：各对互不相交，每对写成 $(r,s)$、$r<s$。
   令未匹配位置集 $U$ 按原次序排列，$p=|\mu|$、$q=|U|=m-2p$。
2. 对每对 $(r,s)$，任取复向量
   $p_{rs}\in\mathbb C^{n_r}\otimes\mathbb C^{n_s}$，令
   $P_{rs}=p_{rs}p_{rs}^*\succeq0$。
   它是未归一 rank-one PSD dyad，允许向量为零；相应帽为
   $\gamma_{P_{rs}}(H)=b_{rs}(P_{rs},H)=\operatorname{Tr}(P_{rs}^TH)$，
   不是 $\operatorname{Tr}(P_{rs}H)$。
3. 对每个 $j\in U$，任取有限整数 $k_j\ge1$ 和**同一共同族**中的
   $X_j\in\mathcal K_{k_j,n_j}$，量子端口在前、实际端口在后。
   普通实际 PSD 端点用 $k_j=1$ 和 $\mathcal K_{1,n_j}=\mathrm{PSD}_{n_j}$ 表示。
4. 令 $Q=\bigotimes_{j\in U}Q_{k_j}$，$K=\prod_{j\in U}k_j$，
   任取整个联合量子效应的 $b$ 代表 $F\in\mathrm{PSD}_K$。
   它可在全部量子端口间纠缠，对应泛函
   $H\mapsto\operatorname{Tr}(F^TH)$。若 $q=0$，取 $Q=Q_1$、$K=1$。

由 $X\in\mathcal K_{k,n}$ 弯曲其实际端口，定义实线性映射

$$
\begin{aligned}
\Phi_X:\operatorname{Herm}_n&\longrightarrow\operatorname{Herm}_k,\\
[\Phi_X(H)]_{\alpha\beta}
 &=\sum_{a,b}X_{(\alpha,a),(\beta,b)}H_{ab}\\
 &=\left[\operatorname{Tr}_A\bigl(X(I_Q\otimes H^T)\bigr)\right]_{\alpha\beta}.
\end{aligned}
\tag{126.2}
$$

这里的转置是原帽的指标公式，不是新增允许的转置操作；$\Phi_X$ 不必是普通 CP。
令 $\Gamma_{\mu,P}$ 在所有匹配位置上按 $\gamma_{P_{rs}}$ 收缩，
将未匹配实际位置按原次序留下。它由原实际二腿源效应及其旁观扩张复合而成。
定义量子输出映射

$$
\mathcal M_{\mu,P,X}(Z)
 =\left(\bigotimes_{j\in U}\Phi_{X_j}\right)\Gamma_{\mu,P}(Z)
 \in\operatorname{Herm}_K.
\tag{126.3}
$$

写实际多指标 $a=(a_1,\ldots,a_m)$、$b=(b_1,\ldots,b_m)$，
量子多指标 $\alpha,\beta$ 只遍历 $U$，其完整原生公式为

$$
[\mathcal M_{\mu,P,X}(Z)]_{\alpha\beta}
 =\sum_{a,b} Z_{a,b}
 \prod_{(r,s)\in\mu}(P_{rs})_{(a_r,a_s),(b_r,b_s)}
 \prod_{j\in U}(X_j)_{(\alpha_j,a_j),(\beta_j,b_j)}.
\tag{126.4}
$$

对该式共轭，再交换 $a,b$，由 $Z,P_{rs},X_j$ 的 Hermitian 性即得
$\overline{\mathcal M(Z)_{\alpha\beta}}=\mathcal M(Z)_{\beta\alpha}$。
因此任意 Hermitian $Z$ 都给 Hermitian 输出；这个合型结论不要求 $Z$ 已在某个锥中。
空乘积与标量边界均按字面意义解释。

对应标准形效应与边界代表为

$$
\begin{aligned}
N_{\mu,P,X,F}(Z)
 &=b_Q(F,\mathcal M_{\mu,P,X}(Z))
   =\operatorname{Tr}\bigl(F^T\mathcal M_{\mu,P,X}(Z)\bigr),\\
(Y_{\mu,P,X,F})_{a,b}
 &=\prod_{(r,s)\in\mu}(P_{rs})_{(a_r,a_s),(b_r,b_s)}
   \sum_{\alpha,\beta}F_{\alpha,\beta}
   \prod_{j\in U}(X_j)_{(\alpha_j,a_j),(\beta_j,b_j)},\\
N_{\mu,P,X,F}(Z)&=b_w(Y_{\mu,P,X,F},Z).
\end{aligned}
\tag{126.5}
$$

$Y$ 的 Hermitian 性同样由共轭、交换全部行列指标得到。
式中没有对 $Z$、任一 $E$ 输入或任一 $X_j$ 暗加共轭或反射。

### 126.B 全部有限源效应的两向精确标准形

**定理 126.2（固定源的端口部分匹配标准形）。** 在定义126.1的同一源下，
每个有限源效应 $e:w\to\mathbf1$ 都满足有限语法恒等式

$$
S(e)=\sum_{\ell=1}^L c_\ell N_{\mu_\ell,P_\ell,X_\ell,F_\ell},
\qquad L<\infty,\quad c_\ell\ge0.
\tag{126.6}
$$

反向，每个定义126.1的 $N$ 本身就是**不变的原源**中一个箭头的数值实现。
因此闭源余向量锥恰为这些 $N$ 的闭生成锥；经原生 $b$ 识别及原对偶字重排，有

$$
\begin{aligned}
B(w)&=\overline{\operatorname{cone}}
 \{Y_{\mu,P,X,F}:\mu,P,\ k_j\in\mathbb N_{\ge1},\
 X_j\in\mathcal K_{k_j,n_j},\ F\in\mathrm{PSD}_{\prod_jk_j}\},\\
A(w)&=\{Z\in W_w:\mathcal M_{\mu,P,X}(Z)\succeq0
 \text{ 对全部 }\mu,P,\text{全部有限 }k_j\ge1,
 X_j\in\mathcal K_{k_j,n_j}\}.
\end{aligned}
\tag{126.7}
$$

每一标准形项恰有 $q=m-2p\le m$ 个保留的 $\mathcal K$ 槽位，
且可用中间实际腿数至多 $m+1$ 的源图实现。
这里不限制原图的实际中间次数，不限制任何 $k_j$ 或其乘积，
也没有把正和项数与闭包换成一个有限数值判定。
实际宽度界针对等值的每个标准形项及其正线性张成，
不把每个正和宣布为一个原始生成箭头。

**证明（126.2）。** 复用123.2(ii)—(v)及VII卷106.6—106.9的实际路径／闭环机制，
保留完整联合量子张量；以下九步给出开放实际边界上的两向结论。

（一）先展开确切源语法，再数实际端口。
展开所有复合或复用块、紧对偶、字杯帽、规范重括号和导出的码／retract 箭头。
交换就是原线置换，字杯帽分解为初等杯帽，只有量子字可自由规范分组。
尤其，尺寸一、二的 $A_i$ 重型为 $Q_{n_i}$，以及每个允许秩二角的两个方向，
都按123.2(v)分别展开为其已支付、只有**一条实际端口**的混合 Choi 资源与量子布线。
原三腿种子也展开为量子 GHZ 加三个已付秩二嵌入，不是额外多实际端口生成元。
一个混合生成元的紧对偶再弯回全态端口形式，由 snake 恒等式得到的仍是原 $X$ 张量，
此步不在 $X$ 上插入全转置或部分转置。

（二）实际子图只有路径和环。
把全部生成元弯成张量形式后，实际一体 CP、实际杯及实际帽在该子图中度数二；
混合 $\mathcal K$ 张量、普通实际 PSD 态／效应和每条外部实际边界腿都是度数一端点。
纯量子顶点在该子图中度数零。
所以每个有限连通实际分量是连接两个端点的路径或裸环。
经 $Q_2$ 重型接出的分支已是接到量子背景的度一 $\mathcal K$ 端点，
不是更高价实际顶点。
任意旁观字、矩形跨扇区变化、反向箭头，以及任意高的有限实际中间次数均已包含。

（三）移除不触及实际边界的分量。
为一条实际路径选择方向，复合其局部矩形 CP；反向用原生 $b$ 伴随。
$\operatorname{Ad}_A^\flat=\operatorname{Ad}_{A^T}$ 仍 CP，
所以可用**同一**共同 $\mathcal K$ 的独立矩形 CP 稳定性把整条路径吸收到端点。
两 $\mathcal K$ 端点间的路径由(123.8)—(123.10)给出其联合量子端口上的 PSD 张量；
一个或两个端点为普通 PSD 时，使用 $k=1$ 的同一结论。
裸实际环是 CP 超算子的迹；有限 Kraus 展开给
$\sum_\nu|\operatorname{Tr}L_\nu|^2\ge0$。
这些替换保留所有附接量子端口的完整联合张量，不只保留边缘符号，
也不把纠缠量子背景分解成独立局部测试。

（四）分类触及实际边界的分量。
一条含两个边界端点的路径没有别的端点，因而不含混合 $\mathcal K$ 顶点。
内部 CP 弯曲后是普通 PSD 的两实际腿余向量：其 $b$ 代表是定向矩形 CP 的 Choi 张量，
包括边界尺寸不等的情形。对该 PSD 张量作有限向量 dyad 分解。
一条只含一个边界端点的路径，另一端恰为一个 $\mathcal K$ 端点或普通 PSD 端点。
用正确的 $b$ 伴随把路径 CP 移到端点，所得
$X'_j\in\mathcal K_{k_j,n_j}$ 的实际尺寸就是边界尺寸；
其成员资格来自共同族的独立矩形 CP 稳定性。
普通端点取 $k_j=1$、$\mathcal K_{1,n_j}=\mathrm{PSD}_{n_j}$。
因此每条未匹配边界腿至多保留一个 $\mathcal K$。
仅在需要时展开匹配对的 dyad，得到有限非负和。

（五）把全部剩余量子背景吸收为一个 PSD 效应。
前述移除之后，量子背景内部只剩 PSD 态／余向量、普通量子 CP 的 PSD Choi 张量，
以及非负闭标量；开放量子端口只朝向保留的 $\mathcal K$ 张量。
一致地弯曲这些开放端口，把每个内部 PSD 张量作有限 dyad 分解，
每个 CP 作有限 Kraus 展开。对每个展开选择，ket 收缩给开放量子端口上的一个向量，
bra 收缩给它的共轭，于是贡献正好是该向量的 dyad。
有限和给一个 $F\succeq0$；无开放端口时给非负标量。
跨端口纠缠、杯帽、量子分组和环一直包含在此背景中，不要求因果定向。
这只是移除实际分量后的普通量子 Gram 论证，
没有宣称 Hermitian 空间上的原生 $b$-Gram 正定。

（六）由精确指标取得正向包含。
剩余实际边界分量组成部分匹配；匹配对携带 rank-one PSD 帽，
每个未匹配端点携带一个 $X_j$，剩余量子余向量为
$H\mapsto\operatorname{Tr}(F^TH)$。
每次原 Bell $b$ 收缩分别令两侧 ket 指标相等、bra 指标相等，再对乘积求和，
恰给(126.4)—(126.5)。故原效应是有限非负标准形和。
移除环所得标量可吸收到 $F$ 中，包括标量为零的情形。
这是有限源语法的精确数值恒等式，不是正性估计或假设锥成员关系。

（七）在同一源中构造每个标准形，取得反向包含。
对每个 $p\in\mathbb C^{n_r}\otimes\mathbb C^{n_s}$，写
$p=(I\otimes A)\sum_{t=1}^{n_r}|tt\rangle$，
其中 $A:\mathbb C^{n_r}\to\mathbb C^{n_s}$ 矩形。
原实际杯后接实际一体 $\operatorname{Ad}_A$，给源态 $P=pp^*$；
紧对偶给其原 $b$ 帽。等价地，以适当 $b$ 伴随实现一体矩形 CP 后接实际帽。
对未匹配位置，正好使用原
$s_{X_j}:\mathbf1\to Q_{k_j}A_{i_j}$，把其实际输出与该边界腿按原帽接合，
所得箭头就是(126.2)的 $\Phi_{X_j}$。
用原位置映射并置这些箭头和匹配帽，最后接普通量子效应
$H\mapsto\operatorname{Tr}(F^TH)$；$F^T\succeq0$，故该效应是允许的量子 CP。
这在**原来的同一源**内构造 $N$。
没有为任意补全新增输入 $x\in E$ 增加 $s_x$，没有使用集体实际 qutrit CP。

（八）传到锥、闭包和精确 PSD 条件。
两个有限语法方向给相等的生成锥，在固定有限维边界空间取 Euclidean 闭包后仍相等。
紧对偶及原对偶字重排把源效应与源态经 $b$ 识别，给(126.7)的 $B(w)$ 等式；
此处不把 $b$ 认成正定 Hilbert 内积。
对一个固定 Hermitian 矩阵 $M$，

$$
\operatorname{Tr}(F^TM)\ge0\quad(\text{全部 }F\succeq0)
\quad\Longleftrightarrow\quad M\succeq0,
\tag{126.8}
$$

因为全转置置换普通量子 PSD 锥，而其普通迹对偶正是自身。
因此对全部源效应非负，恰等价于(126.7)中全部 $\mathcal M$ 的 PSD 条件，得到 $A(w)$。
只有这里使用普通量子 PSD 的转置不变性，没有在 $E$ 或新实际锥上作此假设。

（九）按不变的源操作给出实际宽度界。
对一个标准形项，先在 $m$ 条输入实际腿上逐对施加匹配帽。
每个帽可由局部矩形 CP 后接实际帽实现，不增加实际腿。
再逐条处理未匹配端点：产生其 $s_X$，只增加一条实际腿与量子端口，
立即把新实际腿与该输入端点接帽，留下量子端口。
全过程至多 $m+1$ 条实际腿，最终 $F$ 是纯量子操作。
被移除的实际分量已经吸收到合法量子 PSD 数据或同一 $\mathcal K$ 元素中。
这给每个等值标准形项的界，即使原语法曾经过任意高实际次数也成立。∎

### 126.C R3/R4 的完整量词、原生 currying 与负见证

**定理 126.3（原 R3/R4 的量子输出等价式）。** 固定125.8中的原种子集 $\mathscr D_v$。
R3 当且仅当下述全部量子矩阵条件成立：对每个实际六字 $v$、每个原位置产品
$d=\tau_\pi(x\otimes y)\in\mathscr D_v$（两个因子遍历其**整个**原 $E$ 三字锥），
每个实际字 $a$、$0\le|a|\le5$ 和每个 $z\in E(a)$，取
$w=va$、$m=6+|a|$、$Z=d\otimes z$，并保持字面原位置顺序，要求

$$
\mathcal M_{\mu,P,X}(d\otimes z)\succeq0
\quad\text{对 }[m]\text{ 上全部部分匹配 }\mu,\text{全部 }P_{rs}=p_{rs}p_{rs}^*,
\text{全部有限 }k_j\ge1,\ X_j\in\mathcal K_{k_j,n_j}.
\tag{126.9}
$$

$|a|=0$ 时 $z$ 是非负标量，此式就是六边界公式乘 $z$；$z=0$ 直接给零，不条件化。

R4 当且仅当：对每对实际六字 $v,v'$、每个原位置
$d=\tau_\pi(x_1\otimes x_2)\in\mathscr D_v$ 和
$d'=\tau_{\pi'}(x_3\otimes x_4)\in\mathscr D_{v'}$，
四个因子各遍历其整个原 $E$ 三字锥，取 $w=vv'$、$Z=d\otimes d'$，要求

$$
\mathcal M_{\mu,P,X}(d\otimes d')\succeq0
\quad\text{对 }[12]\text{ 上全部部分匹配 }\mu,\text{全部 }P_{rs}=p_{rs}p_{rs}^*,
\text{全部有限 }k_j\ge1,\ X_j\in\mathcal K_{k_j,n_j}.
\tag{126.10}
$$

两式保持125.19中每个原源复合的量词：任意有限量子辅助、
任意有限高中间实际次数、矩形跨扇区箭头、全部旁观、紧 $b$ 伴随、
原位置及逆、重括号均未删去。
标准形消掉的是这些中间布线的冗余表示，不是原全称范围。

未删去已付情形前，每项的资源及实际宽度可取

| 检验族 | 保留的 $\mathcal K$ 槽位数 $q$ | 效应标准形的实际宽度 | 反 currying 后原源映射项的实际宽度 |
| --- | --- | --- | --- |
| R3，$r=|a|\le5$ | $q=m-2p\le m=6+r\le11$ | $m+1\le12$ | $6+2r+1\le17$ |
| R4 | $q=12-2p\le12$ | $13$ | $6+12+1=19$ |

这些都是等值源图项的实际腿数界；任一量子 $k_j$ 及其乘积仍无上界。

此外，若某个指定 $\mathcal M(Z)$ 有向量 $h$ 满足
$h^*\mathcal M(Z)h<0$，则存在确切合型的原源效应及反 currying 原源映射，
见证对应 R3 或 R4 失败；反向，任何负的有限原源读数都给一个非 PSD 标准形输出。
此转换要求所有输入在**同一**固定 $E$ 和 $\mathcal K$ 中的精确成员资格，
不提供成员判定 oracle。

**证明（126.3）。** 先在原紧结构中核对 currying 的两个方向。
对实际字 $v,a$，在固定对偶字重排后，

$$
\begin{aligned}
e_f&=\operatorname{ev}_a\circ(f\otimes\mathrm{id}_a),
 &&f:v\to a,\quad e_f:va\to\mathbf1,\\
f_e&=(e\otimes\mathrm{id}_a)\circ(\mathrm{id}_v\otimes\operatorname{coev}_a),
 &&e:va\to\mathbf1,\quad f_e:v\to a,\\
S(e_f)(d\otimes z)&=b_a(S(f)d,z),\\
S(e)(d\otimes z)&=b_a(S(f_e)d,z).
\end{aligned}
\tag{126.11}
$$

两条 snake 恒等式给它们互逆；原反序识别已包含在式中的位置映射。
输入始终是未改动的 $d,z$，不是 $T_az$ 或其他反射替代。
这些等式是全原源箭头的等式，包含所有矩形扇区变化、任意有限量子辅助和实际中间次数。
$d,z$ 是外部测试输入，不被提升为源态生成元。

R3 因而正好是对 $w=va$ 的全部源效应 $e$ 有
$S(e)(d\otimes z)\ge0$。
126.2的反向构造说明它蕴含对所有标准形 $N$ 非负；
对每个 $\mu,P,X$ 再令联合 $F$ 遍历整个 PSD 锥，(126.8)给(126.9)。
反向，若全部(126.9)成立，每项 $N$ 都非负，
(126.6)的有限非负和遂使全部原 $e$ 非负，再用(126.11)回到 R3。
所有成员条件都是原固定 $E$ 的条件。

R4 以输出字 $a=v'$ 使用相同的原生 currying；每个 $f:v\to v'$ 给十二腿效应，
每个十二腿源效应也反 currying 成原 $f$。
再应用126.2的两个方向及(126.8)，即得(126.10)的充要性。
这里没有使用 $L_6,G$ 或任何新第六锥的自极性。

资源数是 $q=m-2p$，效应宽度沿126.2。
把效应反 currying 为 $v\to a$ 时，先产生 $|a|$ 对原实际杯，
留下每对的输出半边作旁观；在其余 $6+|a|$ 条腿上执行标准形。
于是总实际宽度至多 $6+2|a|+1$，保留的 $\mathcal K$ 数仍至多 $m$。
R3、R4分别代入 $|a|\le5$、$|a|=6$ 即给表中界。
这不声称原映射本身的既有语法具有这些宽度。

最后，给定负向量，取

$$
F=|\overline h\rangle\langle\overline h|\succeq0,
\qquad b_Q(F,\mathcal M(Z))=h^*\mathcal M(Z)h<0.
\tag{126.12}
$$

126.2第七步给一个原源效应，(126.11)给确切合型的原源映射，从而给负 R3 或 R4 读数。
反向，将负的有限 $S(e)(Z)$ 按(126.6)分解；有限非负系数和为负，
必有一项 $N(Z)<0$。该项的联合 PSD $F$ 使
$\operatorname{Tr}(F^T\mathcal M(Z))<0$，故对应 $\mathcal M(Z)$ 非 PSD。
成员资格不能用不相关块正锥、未知 $E$ 的外包络或其他 PSD 空间替代。
至此只替换125.8的检验族；检验本身的全称非负性仍未证明，
条件准则仍为条件准则，没有因此取得 $G$ 的低层保持与第六最大界、
$E'$ 的无条件存在或某个合规第六锥。∎

### 126.D 有限拓扑及已付连通分量的精确剔除

**命题 126.4（拓扑计数与联合连通判据）。** 对带标签的 $m$ 条边界腿，
含 $p$ 对的部分匹配数和全部部分匹配数分别为

$$
t_{m,p}=\frac{m!}{(m-2p)!\,2^pp!},\qquad
T_m=\sum_{p=0}^{\lfloor m/2\rfloor}t_{m,p},\qquad q=m-2p.
\tag{126.13}
$$

相关次数的值为

| $m$ | $6$ | $7$ | $8$ | $9$ | $10$ | $11$ | $12$ |
| --- | --- | --- | --- | --- | --- | --- | --- |
| $T_m$ | $76$ | $232$ | $764$ | $2620$ | $9496$ | $35696$ | $140152$ |

R3 在 $|a|=0,\ldots,5$ 的带标签匹配拓扑总数为
$\sum_{m=6}^{11}T_m=48884$。
这些只计拓扑，不计扇区字、向量、$E$ 输入、$\mathcal K$ 参数或量子矩阵层数。

对一个 $E$ 元素的输入产品，把各个输入因子作为顶点，
每个跨因子匹配帽作为一条边；因子内帽不影响连通性，允许重边。
每个因子的腿按原置换后的字面位置识别，不要求支撑连续。
在这个因子图中，最后联合 $F$ 施加之前的量子矩阵输出，
按连通分量分解为张量积，至多差一个原量子端口置换。
含一或两个 $E$ 输入因子的分量，其量子输出已是 PSD。

因此 R3 等价于只保留 $|a|=3,4,5$ 且 $x,y,z$ 三因子图连通的(126.9)。
此时至少两个跨因子帽，故

$$
q\le m-4\le7.
\tag{126.14}
$$

不先假设 R3 时，R4 中所有分量都至多含两个输入因子的匹配已经支付；
任何剩余图有至少三因子的一个分量，至少两个跨因子帽，故 $q\le8$。
一旦 R3 成立，R4 的全部不连通四因子图也已支付；
只剩四个 $E_3$ 因子全连通的(126.10)，它至少有三个跨因子帽，故 $q\le6$。
于是精确的联合等价式是

$$
\mathrm{R3}\land\mathrm{R4}
\quad\Longleftrightarrow\quad
\begin{cases}
\text{全部三因子连通 R3 检验，}\ |a|=3,4,5,\ q\le7;\\
\text{全部四因子连通 R4 检验，}\ q\le6.
\end{cases}
\tag{126.15}
$$

两行仍遍历其全部原输入、匹配帽、有限 $k_j$ 和共同 $X_j$。
它不声称 R3 单独推出整个 R4，也不声称裸 Cross 足够。

**证明（126.4）。** 先选 $2p$ 个配对位置，排列后除去每对内部交换的 $2^p$
和对序的 $p!$，得到 $t_{m,p}$；对 $p$ 求和给 $T_m$ 及表中整数。

因子图不同连通分量间没有匹配帽相连；输入本身是指定因子的张量积，
保留的每个 $\Phi_{X_j}$ 仅作用于其一条实际腿。
所以(126.4)的求和逐分量分离，量子输出是各分量输出的张量积，
原位置映射只重排量子端口。
最后的 $F$ 可以跨这些端口任意纠缠，不要求它作产品分解。

复用125.2证明已付的小分量事实，而不另把旧两输入证明当作新结论。
对一因子 $x\in E$，该分量正是一个不变源箭头 $E\to E(Q)=\mathrm{PSD}$ 的像。
对两因子，先在该分量的量子输出上接任意普通 PSD 效应；
所得标量由125.2的两输入源 currying 非负。
量子效应遍历整个 PSD 对偶，故该分量输出矩阵 PSD。
没有剩余量子端口时，所得就是非负标量。
各分量输出的普通量子张量积 PSD，所以即便最后 $F$ 跨分量纠缠，读数仍非负。
这没有把两个任意 $E$ 输入的产品宣布为某个 $E$ 复合锥的成员。

R3 若 $|a|\le2$，每个 $z$ 是有限源 dyad 和，或是非负标量。
把每个 dyad 吸收到源效应中，余下 $x,y$ 的符号由125.2支付。
若 $|a|=3,4,5$ 且三因子图不连通，各分量至多有两个输入，
刚才的论证支付其全部量子输出。
所以只需三因子连通图；反向它们本来就是 R3 的子族。
三顶点连通图至少两条跨因子边，每个匹配帽消耗两条不同实际腿，
故 $q\le m-4$，在 $m=9,10,11$ 时分别至多 $5,6,7$。

R4 不假设 R3 时，未付图必有至少三输入因子的分量，所以至少两个跨因子帽，
从 $m=12$ 得 $q\le8$。
若 R3 成立，一个含三个 $E_3$ 输入的分量也给 PSD 输出：
接任意量子 PSD 效应，把前两因子作 $d$、第三因子作 $|a|=3$ 的 $z$，
以原生 currying 应用 R3，再用整个 PSD 对偶。
因此四因子图若不连通，每个分量至多三个输入，全都已付。
剩余全连通图至少三条跨因子边，消耗六条实际腿，故 $q\le12-6=6$。
先由(126.15)第一行恢复 R3，再按此论证由第二行恢复 R4；反向是检验子族限制。
这证明联合等价，而没有独立支付任一剩余符号族。∎

### 126.E 原普通对偶、质量预算与极限的范围

(126.7)是原生源余向量与闭锥的等式，不选择低份锥或第六锥。
原 $E$ 的 proper 性、严格正块迹、整个迹一基、所有极点与整个普通对偶 proper 区间，
没有被标准形的某个有限子菜单替代或重新定义。
$K^\vee=TK^*$ 仍把原生 $b$ 表示和普通对偶区分开；
只有纯量子 PSD 输出允许(126.8)那样把全部 $b$ 检验换成普通 PSD 成员条件。
$L_6,G$ 不被假定转置不变或自极。

上包络仍是同一个 $A=B^\vee$，只是取得标准形的精确描述。
这不声称 $B=A$、$E=B$、$E=A$、任意两个 $E$ 元素的产品正性或有序锥全补全，
也不把非构造 $E$ 的成员资格变成数值程序。
所有原 retract、旁观、return 和迹亏损效应还是原映射。
对一个按原规范归一的源图，完整标量求值被精确保留，所以原总预算相同。
标准形项及 $F$ 可以是未归一源张量，不必逐项是同一物理事件或确定性操作。

$\Delta_{r,2}$ 的质量二、$\Delta_{r,2}/2$、原 proper 帽缩放、
$c=(00,01,10)$、$11$ 上真零及所有 snake 成功系数，
均未被重缩放成确定性事件。
若一个已付规范化把图乘正标量，只比较其符号，不改变成功预算；
零标量给零，不对零质量条件化。

固定边界字 $w$ 时，(126.7)的闭包都取在原有限维 $W_w$ 中。
逼近标准形之间允许量子尺寸变化，但比较的是它们在**同一边界空间**中的余向量。
没有对缺少嵌入的变维量子矩阵取极限。
每条量子腿、全部量子纠缠和其共同实现始终保留，
没有把原生接合换成反射后的实际 Gram、顶点连接矩阵、独立站点测试、
标量特征模型或编码实际 qutrit 寄存器上的自由 CP。

### 126.F 来源对应、普通解释与原未付边界

126.1—126.4是既定源上的综合推导（repo-derived），不主张外部原创性或优先权。
原对象、固定相位基、实 Hermitian 张量空间和 $b$ 伴随沿123.1、(123.1)；
共同 $\mathcal K$、全尺寸独立矩形 CP 稳定性和 $\mathcal K_{1,n}=\mathrm{PSD}_n$
沿123.2(i)、(123.2)。
126.2第三步直接复用123.2(ii)的(123.8)—(123.10)，不把已支付的 $\mathcal K$ 路径当作新研究。
确切生成元、闭源正性、纯量子／实际二腿 PSD 锚与分别支付的双向角，
沿123.2(iii)—(v)、(123.11)—(123.14)；
完整低接口与“源 dyad 不等于任意补全新增输入”的界线，沿123.2(vi)—(vii)、(123.15)—(123.18)。
这些源条目的固定版本见
[第VIII卷123.1—123.2](https://github.com/the-omega-institute/trureturing/blob/d76383c383bdab2940819958c033f735a1897881/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md)。
实际路径、环和含纠缠量子背景的 dyad 机制沿
[第VII卷106.6—106.9](https://github.com/the-omega-institute/trureturing/blob/d76383c383bdab2940819958c033f735a1897881/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md)，
允许非因果图式。VII卷105.7保留的边界也不变：局部压缩／张量稳定完全余正性
不等于全局 Schmidt 秩二测试或原旁观正性，不能据此推出 NPPT 等价或压缩定理。
锥系统和条件补全的外部文献仍按125.L的准确适用面引用；本章没有另用图重建或量子压缩结果。

普通地说，展开原源后，实际线路不会分叉：每个内部实际顶点只有两条线，
混合资源只带一条实际线。
不碰边界的路径可以用已知结果移走，碰边界的路径要么配成一对帽，
要么在一条边界腿上留下一个共同 $\mathcal K$ 资源。
所有复杂量子线路则合成一个联合 PSD 效应，它仍可跨全部端口纠缠。
这就是为什么边界固定后只需有限种配对形状，并且每条未配对腿最多留下一个资源。
两向源构造保证这保留了所有原源检验，不只给一个较弱测试菜单。

R3、R4于是成为量子输出矩阵的 PSD 条件。
三因子必须连起来才有新的 R3 检验；R3成立后，四因子必须全连起来才有额外 R4 检验。
相应每项至多七个或六个共同资源，却不是七维或六维量子系统：
每个资源的量子端口尺寸仍可任意大，其乘积也无统一界。
有限拓扑、有限资源数和有限实际宽度不等于有限数值认证，
有限正和与固定边界闭包也不提供 $E$ 或 $\mathcal K$ 的成员 oracle。

尚须证明这些剩余全称 PSD 条件，或以同一 $E,\mathcal K$ 的精确成员给出负见证；
本章既未证明其正性，也未证明其失败。
裸 Cross 的充分性、Cross/Bell-Cross 的同一第四锥成员关系、
$\delta_{\mathrm{cross}}$ 的数值，仍未支付；Four 的恒等／置换子族虽由125.6已付，
它没有替代全部源布线。
旧预选 $E_6$ 中所有 $3\mid3$ 产品的成员资格、该预选族的产品相容性、
$G_6\subseteq U_6$、无条件源相容六份前缀的存在和更高源／原产品闭合仍未建立。
另选条件性 $E'$ 不支付旧 $E_6$ 的成员关系。

原目标仍是完整 allN 的 $\mathsf{Fusion}_3/t=1$，或保持全部原合同且具有统一严格间隙的
合法 allN 模型；每个原位置的全部高阶 min/max 产品律、整个普通对偶和相应全局原 Choi
推论仍须在同一个原实现中成立。逐有限阶段结论、有限拓扑或趋近一的截断参数不满足它。
正确合型的负测试只排除被测试的固定低族，不排除其他低族或全部原模型。

数学源图式、标准形和锥成员仍不给出实际制备来源或记录／事件可取得性，
同一家族上的完整控制仪器及其物理实现、物理动力学和实际连续时间作用、
Hamiltonian 的选择、其物理能量识别及能量标定、物理钟及其校准、
物理单位选择和数值 $\hbar$ 都还需要原问题所要求的桥梁。
静态源标准形不完成这些物理义务，也不完成原 allN 目标。

## 追加锚（本行以下为增补区）

## 127. 精确低类型锚上的连通符号、桥分块与剩余循环

### 127.A 固定原域、端口指标与两输入定位

**定义 127.1（同一源上的连通检验）。** 固定123.1—123.2、125.1中的同一个
实际扇区集 $I$、$n_i\in\{1,2,3\}$、实 Hermitian 张量载体和计算相位基。
仍使用同一个共同族 $\mathcal K$、源 $\mathcal D$、实现 $S$ 和
$B_{\mathcal D}\subseteq E=E^\vee\subseteq A_{\mathcal D}$，其中

$$
\begin{aligned}
b_w(H,G)&=\operatorname{Tr}(H^TG),&K^\vee&=T_wK^*,\\
B_{\mathcal D}(w)&=\overline{\operatorname{cone}\{S(s)(1):s:\mathbf1\to w\}},&
A_{\mathcal D}(w)&=\{H:S(e)H\ge0\text{ 对全部 }e:w\to\mathbf1\}.
\end{aligned}
\tag{127.1}
$$

源生成元恰为量子字间普通 CP、实际扇区间一体复矩形 CP、杯帽、
每个 $X\in\mathcal K_{k,n_i}$ 的 $s_X:\mathbf1\to Q_kA_i$ 及紧对偶；
只再作原位置置换及逆、重括号、复合和任意旁观扩张。
量子字可规范分组；两条实际 qutrit 腿不改型为一个免费量子对象。
不增加任意多实际腿集体 CP，也不为任意补全新增的 $x\in E(w)$ 添加源态生成元。
共同 $\mathcal K$ 在两侧独立复矩形 CP 下稳定，满足
$\mathrm{SN}_2\subseteq\mathcal K=\mathcal K^\vee\subseteq\mathrm{BP}_2$。

原 $W_N=V^{\otimes_{\mathbb R}N}$、$V=\bigoplus_i\operatorname{Herm}_{n_i}$、
块迹 $u_N$、整个迹一基、全部极点和整个普通对偶 proper 区间均保持原定义。
完整 $S_2$ 仍包括纠缠纯点、所有有限准备、零权与重复标签；
123.1、125.1中低二份到 Jordan、实际自复合复型选择、实际两因子产品正规形的
三条条件供应仍保留其全部输入，未用高份分类替代。
含相位种子 $\Delta_{r,2}$ 的迹为二，归一态为 $\Delta_{r,2}/2$；
原实码 $c=(00,01,10)$、$c^*11=0$、所有实际位置、
retract、旁观、return、proper 帽与迹亏损预算均固定。

取有限个输入 $x_t\in E(v_t)$，每个输入遍历其整个原锥，置
$Z=\bigotimes_t x_t$。各输入腿可以在原位置置换后不连续。
按126.1取边界 $[m]$ 上的部分匹配 $\mu$，每对 $r<s$ 配
$P_{rs}=p_{rs}p_{rs}^*$，允许 $p_{rs}=0$；未匹配集记 $U$。
每个 $j\in U$ 配同一个共同族中的
$X_j\in\mathcal K_{k_j,n_j}$，$1\le k_j<\infty$ 任意，无统一上界。
量子输出及最终标量为

$$
\begin{aligned}
\Phi_X(H)_{\alpha\beta}
 &=\sum_{a,b}X_{\alpha a,\beta b}H_{ab},\\
\mathcal M_{\mu,P,X}(Z)_{\boldsymbol\alpha\boldsymbol\beta}
 &=\sum_{\boldsymbol a,\boldsymbol b}Z_{\boldsymbol a,\boldsymbol b}
   \prod_{(r,s)\in\mu}p_{rs}(a_r,a_s)\overline{p_{rs}(b_r,b_s)}
   \prod_{j\in U}(X_j)_{\alpha_ja_j,\beta_jb_j},\\
N_F(Z)&=\operatorname{Tr}\!\left(F^T\mathcal M_{\mu,P,X}(Z)\right),
\qquad F\succeq0\text{ 为全部量子端口上的任意联合矩阵}.
\end{aligned}
\tag{127.2}
$$

全部指标使用原固定基；共轭上式并交换 $\boldsymbol a,\boldsymbol b$ 即得
$\mathcal M$ Hermitian。帽是 $H\mapsto\operatorname{Tr}(P^TH)$。
没有把它换成普通迹帽，也没有转置任何 $E$ 输入。
$U=\varnothing$ 时输出是实标量；零输入或零帽直接给零，不条件化。
由普通量子 PSD 的全转置不变性和迹自对偶，
$\mathcal M\succeq0$ 等价于对全部联合 $F\succeq0$ 有 $N_F\ge0$。
$F$ 可以跨全部端口纠缠。

因子多重图的顶点是这些原 $E$ 输入；每个跨输入帽是一条边，保留重边。
输入内部帽是局部源操作，不计作跨输入边。
删去一条边使其连通分量断开时称该边为桥；双重边中的任一条都不是桥。
删去全部桥后仍保留孤立输入顶点。

**定理 127.2（两输入的原上包络定位及精确源锚）。** 任取原对象字 $u,v,r$、
源箭头 $g:uv\to r$ 和整个原锥中的 $x\in E(u),y\in E(v)$，则

$$
S(g)(x\otimes y)\in A_{\mathcal D}(r).
\tag{127.3}
$$

以下目标类型的上下包络和 $E$ 恰相等：

$$
\begin{aligned}
B_{\mathcal D}(Q_k)&=E(Q_k)=A_{\mathcal D}(Q_k)=\mathrm{PSD}_k,\\
B_{\mathcal D}(Q_kA_i)&=E(Q_kA_i)=A_{\mathcal D}(Q_kA_i)
 =\mathcal K_{k,n_i},\\
B_{\mathcal D}(A_iA_j)&=E(A_iA_j)=A_{\mathcal D}(A_iA_j)
 =\mathrm{PSD}_{n_in_j}.
\end{aligned}
\tag{127.4}
$$

故(127.3)的输出在这些目标上分别是 PSD、共同 $\mathcal K$ 元素和两实际腿 PSD。
量子分组及原端口置换运输这些等式。单输入版本由 $E$ 的源正性直接成立。
第三行没有额外量子参考；不从它推出 $k>1$ 时
$B_{\mathcal D}(Q_kA_iA_j)=E(Q_kA_iA_j)=A_{\mathcal D}(Q_kA_iA_j)$。

**证明（127.2）。** 对每个源效应 $e:r\to\mathbf1$，将 $eg$ 原生 currying 成
$h:v\to u$，其中原计算自对偶字的反序由固定位置映射识别。
snake 恒等式逐指标给

$$
S(eg)(x\otimes y)=b_u\!\left(x,S(h)y\right)\ge0.
\tag{127.5}
$$

源正性使 $S(h)y\in E(u)$，$E(u)=E(u)^\vee$ 给非负，
这正是(127.3)的全部源效应定义；不需要 $x\otimes y\in E(uv)$。
这是125.2两输入事实的目标定位，不另重证源闭标量或共同资源路径定理。

为核对(127.4)的源实现，$s_X$ 和其原紧对偶效应对每个 $X\in\mathcal K$ 都存在，
所以 $\mathcal K\subseteq B_{\mathcal D}(Q_kA_i)$，
而 $A_{\mathcal D}(Q_kA_i)\subseteq\mathcal K^\vee=\mathcal K$。
夹逼给中行。全部量子 PSD 态和效应给首行。
对末行，每个 $p\in\mathbb C^{n_i}\otimes\mathbb C^{n_j}$ 写成
$p=(I\otimes A)\sum_a|aa\rangle$，$A$ 是原实际扇区间复矩形矩阵。
实际杯后接一体 $\operatorname{Ad}_A$ 即给 $pp^*$ 的源态，紧对偶给其帽。
有限谱和给整个 PSD 锥的上下夹逼；两实际腿 PSD 元素因此是有限源 dyad 和。
这里对固定 $x,y$ 定位所得的 $X\in\mathcal K$ 可用既有 $s_X$ 替代，
两实际腿 PSD 则可逐 dyad 替代。前者不要求源箭头对资源参数连续选择，
两者均不提供 $E$ 的成员算法或这些外部输入的物理制备。∎

### 127.B 桥分块的全称量子正性

**定理 127.3（每个无桥块至多两输入）。** 对定义127.1的任意有限输入族和任意正常型数据，
若删去因子多重图的全部桥后，每个连通分量至多包含两个原 $E$ 输入，
则 $\mathcal M_{\mu,P,X}(Z)\succeq0$。
内部帽、重边、标量／qubit／qutrit 扇区及每个未匹配 $\mathcal K$ 资源均任意。
结论对所有有限且无界的 $k_j$ 成立，并允许最终任意联合纠缠 $F$。

**证明（127.3）。** 将每个删桥后的块缩为一个顶点，所得图是森林：
若商图有环，环上原边删去后仍有另一条路相连，就不是桥。
对每棵树选根，从叶块向根处理。
叶块含原来一个或两个 $E$ 输入；保留通向父块的单条实际终端和
该块的**全部**量子输出。内部帽、未匹配的 $\Phi_X$、
以及已经处理的子树所给资源，组成同一个原源箭头，目标经量子分组为 $Q_kA_i$。
127.2将其精确输出定位在原 $\mathcal K_{k,n_i}$。
因此可用这个既有资源的 $s_X$ 替换整块，所有量子端口和相关性都保持。
父桥帽按原源接合，矩形复系数只进入允许的一体 CP；递归至根。
根块剩下至多两个原 $E$ 输入及源资源，目标纯量子，127.2给 PSD 输出。
无量子输出时同一论证给非负标量。

不同原连通分量的输出按(127.2)分离为张量积，至多差原量子端口置换。
各分量 PSD，故其量子张量积 PSD，最后接任意联合 $F$ 仍非负。
没有将 $F$ 分解为局部效应，也没有丢掉子树输出的量子参考。

具体核对一条复矩形桥。令其两侧精确资源分别为
$X\in\mathcal K_{k,d}$、$Y\in\mathcal K_{\ell,e}$，帽向量的系数为
$R_{ac}=p(a,c)$，$R:\mathbb C^e\to\mathbb C^d$。桥后输出为

$$
\begin{aligned}
M_{i\alpha,j\beta}
 &=\sum_{a,b,c,d'}X_{ia,jb}Y_{\alpha c,\beta d'}
       R_{ac}\overline{R_{bd'}},\\
Y'&=(I_\ell\otimes R)Y(I_\ell\otimes R)^*
       \in\mathcal K_{\ell,d},\\
M_{i\alpha,j\beta}&=\sum_{a,b}X_{ia,jb}Y'_{\alpha a,\beta b}\succeq0.
\end{aligned}
\tag{127.6}
$$

最后一步正是已付的(123.8)—(123.9)，包括全部联合量子向量测试。
这是对 $Y$ 的矩形 CP 合同，没有转置 $Y$ 或某个 $E$ 输入。
$R=0$ 时给零；任意 Schmidt 秩及相位均保留。
因此树，以及由桥连接的双输入重边块，都在本定理范围内。∎

### 127.C 已付的连通 R3 与指定双重边 R4

**定理 127.4（有桥 R3 及无条件的双重边对 R4）。** 在126.3的原 R3 量词内，
任取整个原 $E$ 三字锥中的 $x,y$，整个 $E(a)$ 中的 $z$，
$|a|=3,4,5$。其三因子图若连通且有桥，则全部正常型输出 PSD。
原输入位置、所有帽向量、全部有限 $k_j$ 和共同 $X_j$ 均任意。

独立于尚未证明的整个 R3，取四个整个原 $E_3$ 输入，按字面位置为
$x_1$ 的 $(1,2,3)$、$x_2$ 的 $(4,5,6)$、$x_3$ 的 $(7,8,9)$、
$x_4$ 的 $(10,11,12)$。取

$$
\mu=\{(1,4),(2,5),(6,7),(8,10),(9,11)\},\qquad U=\{3,12\}.
\tag{127.7}
$$

五个帽任意，包括尺寸许可时 Schmidt 秩三的帽；
$X_3\in\mathcal K_{k,n_3}$、$X_{12}\in\mathcal K_{\ell,n_{12}}$
对全部有限 $k,\ell$ 任意，则
$\mathcal M(x_1\otimes x_2\otimes x_3\otimes x_4)\succeq0$。
结论沿全部原扇区标签与位置映射运输。

**证明（127.4）。** 三顶点图的一条桥将其分成一个输入和两个输入。
两侧分别保留桥端实际腿及全部量子端口，127.2给两个共同 $\mathcal K$ 资源；
(127.6)给联合输出 PSD。这容许两个输入一侧的平行边，并非只证明树。
也可直接应用127.3。

对(127.7)，只切 $(6,7)$。左侧有 $x_1,x_2$、帽 $(1,4),(2,5)$ 和 $X_3$，
输出在 $Q_kA_{i_6}$，故属于 $\mathcal K_{k,n_6}$。
右侧有 $x_3,x_4$、帽 $(8,10),(9,11)$ 和 $X_{12}$，
输出属于 $\mathcal K_{\ell,n_7}$。
接回任意 $(6,7)$ 帽后用(127.6)。两侧各自的双重边循环都保留，
没有假设单个三腿输入是普通 PSD，也没有使用一般 R3。∎

### 127.D 带四腿内部帽的三角形

**定理 127.5（指定 $(3,3,4)$ 循环族）。** 取整个原锥中的

$$
\begin{aligned}
x&\in E(A_{i_1}A_{i_2}A_{i_3}),&
y&\in E(A_{i_4}A_{i_5}A_{i_6}),\\
z&\in E(A_{i_7}A_{i_8}A_{i_9}A_{i_{10}}),&
\mu&=\{(1,4),(2,7),(5,8),(9,10)\}.
\end{aligned}
\tag{127.8}
$$

每个 $n_j\in\{1,2,3\}$，四个帽向量任意，
$X_3\in\mathcal K_{k,n_3}$、$X_6\in\mathcal K_{\ell,n_6}$ 任意，
则全部有限 $k,\ell$ 上 $\mathcal M(x\otimes y\otimes z)\succeq0$。
跨输入图是三角形，故此结论并非127.3的有桥情形。

**证明（127.5）。** 只对 $z$ 的第九、十腿施加原帽，其余两腿作旁观。
所得

$$
H_{a_7a_8,b_7b_8}
 =\sum_{a_9,a_{10},b_9,b_{10}}
 z_{a_7a_8a_9a_{10},b_7b_8b_9b_{10}}
 p_{9,10}(a_9,a_{10})\overline{p_{9,10}(b_9,b_{10})}
 \in E(A_{i_7}A_{i_8})=\mathrm{PSD}_{n_7n_8}.
\tag{127.9}
$$

成员关系由该原源箭头的正性给出，PSD 由(127.4)给出。
这里 $H$ 上没有量子参考，不能把带参考的两实际腿张量代入同一锚。
将 $H$ 作有限非负 dyad 和，每个 dyad 均是原两实际腿源态。
逐项代回三角形后，整个剩余图是同一源箭头作用于 $x,y$，目标为 $Q_kQ_\ell$。
127.2给每项 PSD，求和仍 PSD。两个量子输出和最终联合 $F$ 完全不受维数或纠缠限制。∎

### 127.E Schmidt 秩至多二的帽之原源分解

**定理 127.6（低秩跨输入帽的量子分解恒等式）。** 对尺寸 $d,e$ 的帽向量
$p=\sum_{a,b}R_{ab}|ab\rangle$，若 $r=\operatorname{rank}R\le2$ 且 $r>0$，
取复矩形分解 $R=JK^T$，$J\in\mathbb C^{d\times r}$、
$K\in\mathbb C^{e\times r}$。则它的原 $b$ 帽等于

$$
\gamma_{pp^*}
 =\beta_{Q_r}\circ\left(\operatorname{Ad}_{J^T}\otimes
                         \operatorname{Ad}_{K^T}\right),
\tag{127.10}
$$

其中 $\beta_{Q_r}$ 是普通量子 Bell 帽，两个混合 CP 箭头分别从对应实际端口到 $Q_r$，
均已在原源中。$r=0$ 是零帽。因而可将此类跨输入边移入量子布线：
删去这些边后的实际因子图若满足127.3的条件，则原完整检验仍正。
标量或 qubit 端点上的跨输入帽自动属于此类。

**证明（127.6）。** 对任意 Hermitian $H\in\operatorname{Herm}_d$、
$G\in\operatorname{Herm}_e$，直接展开给

$$
\begin{aligned}
\gamma_{pp^*}(H\otimes G)
 &=\sum_{a,b,c,d'}R_{ab}\overline{R_{cd'}}H_{ac}G_{bd'}\\
 &=\sum_{s,t=1}^r(J^TH\overline J)_{st}(K^TG\overline K)_{st}\\
 &=\operatorname{Tr}\!\left[(J^TH\overline J)^T
                             (K^TG\overline K)\right].
\end{aligned}
\tag{127.11}
$$

由于 $H\otimes G$ 张成真正实 Hermitian 张量空间，这是带任意旁观的线性映射恒等式。
它用的是 $J^T$ 而非 $J^*$ 作为 Kraus 矩阵；
其 Hermitian 伴随是 $\overline J$，故仍是普通 CP。
两个 Kraus 的秩至多二，混合 Choi dyad 的 Schmidt 秩亦至多二，
属于原 $\mathrm{SN}_2\subseteq\mathcal K$，所以两个方向所需箭头均由原资源实现。
不需要免费实际／量子重型或新增原源操作。

将新量子端口全部保留至最后，所有替换帽和原 $F$ 构成普通量子 CP／PSD 背景。
将其朝剩余输出弯曲并作 dyad／Kraus 展开，每项给一个向量的 dyad，
所以该背景是这些开放量子端口上的联合 PSD 效应；这是126.2的量子背景论证。
沿删边后的实际图应用127.3，叶块仍输出一个实际终端及**全部**量子端口的 $\mathcal K$。
各纯量子输出 PSD，接联合背景仍非负；背景若保留外部量子输出，
对其再接任意 PSD 效应即可由量子自对偶恢复输出 PSD。
全程保持原联合实现，不将跨块量子联系误认为分离态。∎

### 127.F 精确剩余族与资源数五／四的范围

**定理 127.7（剩余 R3 及条件性的额外 R4）。** 在125.8、126.3的完整原量词下，
整个 R3 等价于尚须证明的以下正常型子族：$|a|=3,4,5$，
将所有 Schmidt 秩至多二的跨输入帽按127.6移入量子布线后，
剩余实际图有包含全部 $x,y,z$ 的无桥连通分量；
其剩余跨输入帽均连两个实际 qutrit 端口且有 Schmidt 秩三。
127.5的指定内部帽三角形已经正，可从未付族剔除。
每个这种剩余检验的原未匹配 $\mathcal K$ 槽位数满足

$$
q=m-2|\mu|\le6+|a|-6=|a|\le5.
\tag{127.12}
$$

若上述剩余 R3 正性全部成立，则整个 R4 的额外条件等价于剩余四输入全连通无桥族，
同样先作127.6的低秩帽分解；未付跨输入帽只需取全 qutrit 的 Schmidt 秩三帽。
这些检验满足

$$
q=12-2|\mu|\le12-8=4.
\tag{127.13}
$$

(127.13)是剩余 R3 正性成立后的额外 R4 界，不是整个 R4 已无条件正的断言。
两式计的是原正常型中未匹配的共同资源槽位，不是量子尺寸，
也不是实现分解时每个混合 Choi 箭头的总生成元数。

**证明（127.7）。** 复用126.4：R3的 $|a|\le2$ 由原有限源 dyad 和支付，
三因子不连通时各分量至多两输入，量子输出已正。
作127.6后，若三因子实际图不连通或连通但有桥，
删桥后每块至多两输入，127.3和量子背景论证支付原检验。
若有未付部分，三个输入必在同一个无桥连通分量。
三顶点无桥连通多重图每个顶点的度至少二，故至少三条跨输入边；
每个帽消耗两条互不相同的原实际腿，原 $|\mu|$ 至少三，给(127.12)。
移入量子背景的低秩帽仍是原匹配的一部分，只会继续减少原 $q$，不会增加它。
输出经低秩分解而新增的 $Q_r$ 端口无需假装成额外未匹配槽位。
量子背景的连接虽仍存在，但可在所有已付分量 PSD 后统一接合。
未移走的帽的秩大于二；原实际尺寸至多三，故两端均是 qutrit 且秩恰三。
反向，剩余检验本来就是原 R3 的子族，恢复已付部分即得整个 R3。

再假设剩余 R3 已正。由刚证明的等价得到整个 R3，
于是三个原 $E_3$ 输入经过任意源箭头到纯量子目标均输出 PSD：
接任意量子 PSD 效应，用(126.11)把前两个输入作为 $d$、第三个作为 $|a|=3$ 的 $z$，
R3给非负，整个量子 PSD 对偶给结论。
所以不连通四输入图全正。
连通四输入图的一条桥只可能分成 $2|2$ 或 $1|3$。
$2|2$ 两侧分别由127.2定位到 $\mathcal K$，(127.6)支付。
$1|3$ 时先将单输入一侧定位成 $Q_kA_i$ 上的原 $\mathcal K$ 资源，
替换成已有 $s_X$ 并接回桥；其量子端口始终保留。
余图是原源箭头作用于其余三个 $E_3$ 输入，正由整个 R3 支付。
这一步需要 R3，不能把三输入侧直接当作已付双输入块。
低秩帽移入量子背景后同样适用这些论证。
因此只剩四顶点无桥连通图，每顶点度至少二，至少四条跨输入边，给(127.13)。
反向补回这些已经正的族便恢复整个 R4，故是条件下的等价而非单向估计。∎

### 127.G 原源内的相位与非 PSD 输入实例

**命题 127.8（非 PSD 三腿源输入及精确复收缩）。** 在一个实际 qutrit 块上令
$\eta=\sum_{a=0}^2|aa\rangle$、$B=2I_9-|\eta\rangle\langle\eta|=5B_-$。
定义等距码 $U:\mathbb C^3\to\mathbb C^3\otimes\mathbb C^3$ 为
$Ue_0=|00\rangle,Ue_1=|01\rangle,Ue_2=|10\rangle$，置

$$
T=(U\otimes I_3)B(U\otimes I_3)^*.
\tag{127.14}
$$

则 $T\in E(A_s^3)$，却不是普通 PSD。取三个 $T$ 输入依次在位置
$(1,2,3),(4,5,6),(7,8,9)$，帽为 $(3,4),(6,7)$，系数矩阵依次为

$$
R=\begin{pmatrix}1&i&0\\0&1&1-i\\1&0&2\end{pmatrix},\qquad
S=\begin{pmatrix}1&1&0\\i&0&1\\0&2&1+i\end{pmatrix}.
\tag{127.15}
$$

未匹配第一腿配 $X_1=B\in\mathcal K_{3,3}$；其余未匹配腿 $2,5,8,9$
的 $k=1$ 资源依次是下列向量的 dyad：

$$
v_2=(1,i,1-i)^T,\quad v_5=(1,1+i,-1)^T,\quad
v_8=(i,2,1)^T,\quad v_9=(1,-i,2-i)^T.
\tag{127.16}
$$

原生量子输出恰为

$$
M=\begin{pmatrix}17606&1038-32i&0\\1038+32i&21790&0\\0&0&26264\end{pmatrix}\succ0.
\tag{127.17}
$$

**证明（127.8）。** $B=5B_-\in\mathcal K_{3,3}$ 由(123.5)给出。
将 $B$ 的量子端先用原实码送入两个量子 qubit，再各经已付 rank-two 嵌入进入实际块，
即给(127.14)的三实际腿源态；所有映射都是原源箭头。
令 $w=(U\otimes I_3)\eta$，则 $w^*Tw=\eta^*B\eta=-3$，故非 PSD。
两帽分别有 $\det R=3+i$、$\det S=-1-i$，都是 Schmidt 秩三。

为给出(127.17)的有限展开，所有实际指标取 $0,1,2$，定义
$t_{ab}$ 为三个编码位置 $(0,0),(0,1),(1,0)$ 的指示数，
并令 $c(a,b)=2a+b$，则

$$
T_{abc,a'b'c'}
 =t_{ab}t_{a'b'}\left(2\delta_{aa'}\delta_{bb'}\delta_{cc'}
                  -\delta_{c,c(a,b)}\delta_{c',c(a',b')}\right).
\tag{127.18}
$$

其中 $c(a,b)$ 在其余位置的值不影响公式。
将(127.18)代入(127.2)，取
$p_{3,4}(a_3,a_4)=R_{a_3a_4}$、$p_{6,7}(a_6,a_7)=S_{a_6a_7}$，
其余四槽取(127.16)的 $v_j(a_j)\overline{v_j(b_j)}$，即得(127.17)。
其七个非空主子式按单元、二元、三元次序为

$$
17606,\ 21790,\ 26264,\ 382556272,\ 462403984,\ 572292560,\ 10047457927808,
\tag{127.19}
$$

全都正。取 $h=(1,i,2-i)^T$、$F=\overline h\,\overline h^*$，
则 $\operatorname{Tr}(F^TM)=h^*Mh=170780$，
而 $\operatorname{Tr}(FM)=170652$，说明原生全转置约定在此不能删去。
本实例的正性也由127.3的路径族普遍保证；它不承担一般循环的全称证明。∎

**命题 127.9（内部帽相位与低秩分解的恒等实例）。** 四个实际 qutrit 上取
$z=\Omega_{1,3}\otimes\Omega_{2,4}$，其中每个 $\Omega$ 是原实际 Bell dyad，
并以(127.15)的 $R$ 在第三、四腿施加原帽。则第一、二腿输出为

$$
H=|\operatorname{vec}R\rangle\langle\operatorname{vec}R|,\qquad
\operatorname{rank}H=1,\qquad\operatorname{Tr}H=10.
\tag{127.20}
$$

另外取

$$
\begin{aligned}
J&=\begin{pmatrix}1&i\\0&1\\1-i&2\end{pmatrix},&
K&=\begin{pmatrix}i&1\\1&0\\2&1+i\end{pmatrix},\\
H_0&=\begin{pmatrix}2&1+i&2-i\\1-i&-1&i\\2+i&-i&3\end{pmatrix},&
G_0&=\begin{pmatrix}1&i&2\\-i&2&1-i\\2&1+i&-2\end{pmatrix}.
\end{aligned}
\tag{127.21}
$$

$R_2=JK^T$ 的秩为二，(127.11)两侧在 $H_0,G_0$ 上均等于 $113$。

**证明（127.9）。** $z$ 是两个原实际杯的张量积再作原位置置换，因而是源态。
其非零矩阵元令第三腿 ket、bra 分别等于第一腿 ket、bra，
第四腿分别等于第二腿；代入内部帽即得
$H_{ab,cd}=R_{ab}\overline{R_{cd}}$，不是它的转置。
$\sum_{a,b}|R_{ab}|^2=10$，给秩及迹。
对(127.21)，$J$ 与 $K$ 都满列秩，故 $JK^T$ 秩二。
矩阵乘法给 $\operatorname{Tr}[(J^TH_0\overline J)^T(K^TG_0\overline K)]=113$，
(127.11)给原帽相同值。$H_0,G_0$ 只是该线性恒等式的 Hermitian 自变量，
不赋予它们未知 $E$ 成员资格。∎

### 127.H 原合型对应、来源与未付边界

**定义 127.10（结论的原域解释）。** 127.2—127.7均在固定原源上解释。
对每个上述正常型效应 $e_F:va\to\mathbf1$，原生反 currying 是

$$
f_{e_F}=(e_F\otimes\mathrm{id}_a)\circ
        (\mathrm{id}_v\otimes\operatorname{coev}_a):v\to a,\qquad
S(e_F)(d\otimes z)=b_a\!\left(S(f_{e_F})d,z\right),
\tag{127.22}
$$

含固定对偶字反序的位置识别，$z$ 始终不变。
R3取 $v$ 为两原三字输入的原位置六字，$|a|\le5$；
R4取 $v,a$ 为各由两原三字输入组成的六字。
因此127.4、127.5支付的是原 R3/R4 中确切合型的源映射子族，
不把这些子族等同于所有源映射。

这些桥分块、内部帽循环及剩余族推导是固定源上的综合结果（repo-derived），
不主张外部原创性、优先权或文献检索完备。
其原对象、相位、$b$ 及 $b$ 伴随按
[VIII123.1—123.2](https://github.com/the-omega-institute/trureturing/blob/d76383c383bdab2940819958c033f735a1897881/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VIII.md)
解释：123.2(i)给共同 $\mathcal K$ 和独立矩形 CP 稳定性，
123.2(ii)的(123.8)—(123.9)给全尺寸桥收缩，
123.2(iii)—(v)给确切源生成元、上下包络、低类型锚及分别支付的角，
123.2(vi)—(vii)给完整低接口和源态／补全新增输入的区别。
两输入标量非负性复用125.2，完整正常型及其两向合型对应复用126.1—126.4；
这些前置不另计作新的符号结果。
量子背景的 dyad 论证沿
[VII106.6—106.9](https://github.com/the-omega-institute/trureturing/blob/d76383c383bdab2940819958c033f735a1897881/docs/develop/theory/QUANTUM_ORIGIN_THREE_COPY_COMPARISON_AND_FINITE_CSTAR_HIERARCHY_VII.md)，
不要求因果定向，相关外部锥系统文献只按123.2、125.L的原条件使用。

一般循环的未付局部目标是带量子参考的两实际 qutrit 腿：

$$
E(Q_kA_iA_j),\qquad k>1.
\tag{127.23}
$$

原假设没有在该类型提供 $B_{\mathcal D}=E=A_{\mathcal D}$，
也没有为其任意元素提供源态实现。
若将这样的循环顶点当成一个实际端口的 $\mathcal K$ 资源，便少了这个完整源桥。
127.5之所以可用两实际腿 PSD 锚，正因为内部帽后没有此额外量子参考。
原生 $b$ 不能换成实际腿 Hilbert 反射 Gram；
不假设 $E,G,L_6$ 的全／部分转置或反射不变性，也不替换实际共同 $\mathcal K$。

例如三个全 qutrit 三腿输入的三角形
$\mu=\{(1,4),(2,7),(5,8)\}$、$U=\{3,6,9\}$，
三个跨帽均有 Schmidt 秩三且各 $X_j$ 量子层任意，仍未证明正性。
以四／五腿输入为中心的双重边星形也可留下无桥三输入部分。
四个 $E_3$ 输入的无桥四循环及其完整量子参考同样未付；
R3未成立时，带一个未付三输入块和桥接单输入的四输入图也未付。
未给出具有同一 $E,\mathcal K$ 精确成员资格的负见证。
PSD、可分、PPT 或块正外包络不能代替这些原成员条件。

有限匹配拓扑、(127.12)—(127.13)的有限资源数及126.3的实际宽度界，
都不限制任一 $k_j$ 或其乘积，也不提供数值成员 oracle。
低秩分解中的量子端口须保持共同实现，不能用独立边缘或分别可达的极值替代。
零输入和零预算给零，不作零质量条件化；所有等式保持完整标量，
原 proper 帽缩放、质量二种子、$11$ 真零、retract、旁观、return 和迹预算均不重标定。
源态替代是数学源语法内的替代，不是任意外部输入的实际制备事件。

整个 R3/R4、裸 Cross 的充分性、同一第四锥中的 Cross/Bell-Cross 成员关系、
旧预选 $E_6$ 中全部 $3\mid3$ 产品及其相容性、$G_6\subseteq U_6$、
无条件源相容六份前缀存在及更高原产品律，均仍未由这些子族证明建立。
另选条件性第六锥不支付旧预选 $E_6$。
原目标仍是完整 allN 的 $\mathsf{Fusion}_3/t=1$，或满足全部原合同且具有统一严格间隙的
合法 allN 模型；逐有限阶段存在或趋近一的截断参数不完成该目标。
原普通全对偶、所有原位置 min/max 产品律和全局原 Choi 推论仍须在同一原实现中成立。

条件于原 $\mathrm{Inj}$ 与 attained WidthBound 的局部接触定理不提供(127.23)的源实现；
有限 projection-only Gleason 结论也不提供这些实际／混合源锚或复合锥。
相应 proper-slice、$\mathrm{Inj}$、contact 缺口不由本章循环子族正性消去。
静态数学源图式仍不提供实际制备来源、记录／事件可取得性、同一家族的完整控制仪器，
也不选择物理动力学、实际连续时间作用、物理钟及其校准、Hamiltonian、
物理能量识别及能量标定、物理单位或数值 $\hbar$；这些原物理桥均保持未决。

## 追加锚（本行以下为增补区）
