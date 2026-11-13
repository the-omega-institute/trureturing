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
