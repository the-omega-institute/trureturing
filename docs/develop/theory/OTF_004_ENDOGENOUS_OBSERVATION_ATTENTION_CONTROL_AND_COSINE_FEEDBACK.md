# 正交时间场论 OTF-004：内生观察、注意控制与余弦反馈

> 理论参考输入：本稿为用户提供的研究正文，包含普通数学证明，未作本候选的 Lean/kernel 认证。

OTF RESEARCH SERIES / 004 / VERSION 1.0

正交时间场论

内生观察、注意控制与余弦反馈

仪器选择、记录互补、Zeno 动力学及实复不动点

Endogenous Observation and Attention Control\
Measurement Records and Cosine Feedback

**本轮核心** 把注意定义为整体内部的操作设置与反馈。 同一联合态可以经不同内部读口给出路径信息或条件干涉； 物理耦合、坐标选择、记录条件化和单次结果保持分型。 余弦不动点是指定反馈律的平衡，而单次量子读数与均值反馈具有不同极限。

$$
\mathcal D^2+\mathcal V^2=1,\qquad
 \left(Pe^{-\mathrm iHt/(N\hbar)}P\right)^N
 \longrightarrow e^{-\mathrm iPHPt/\hbar}P.
$$

$$
F_s(x)=s\cos x,\quad x_s=s\alpha,\quad \alpha=\cos\alpha,
 \qquad
 \mathbb E e_{n+1}^2
 \leq \sin^2(1)\,\mathbb E e_n^2+\frac1{N_n}.
$$

**范围** 有限维仪器与每个指定有限协议的内生实现； 理想连续反馈及无限次监测的极限另列条件。 本文不将主观专注直接设为物理定律， 不由复根自动指定能级、反粒子、质量或时间箭头。

2026 年 11 月 8 日 / Asia–Singapore

项目固定于默认分支 dev 的 `6ca7b7300b84a13660977b193b024ca63d92ab06`。

承接 OTF-001–003；普通数学证明与限定来源核读，未运行新的 Lean 构建。

## 摘要

若观察者内生，何时显现粒子式记录、何时显现波动关系，能否归结为注意力？ 本文将可研究的注意定义为内部程序、参考访问、仪器强度、记录读口与反馈规则， 而不是独立于交互的心理变量。首先构造整体内部的受控仪器，证明有限程序空间 不能精确编程连续全部锐 qubit 测量方向。 Bloch 半角概率、可调强度退相干以及记录重叠分别说明： 轴对齐、确定性、路径信息、空间定位与干涉可见度不是同一指标。 一个明确的双 qubit 联合态在不同记录读口下给出路径或条件条纹， 但不分类的局部统计保持不变。 有限维 Zeno 定理给出显式 $O(N^{-1})$ 误差， 并保留高秩子空间内部动力学；移动投影还可实现趋近确定的态输运。 随后证明 $\cos x=\pm x$ 各有唯一实根， 相应实迭代全局收敛且由镜像共轭联系。 然而把单次 $\pm1$ 测量结果直接反馈为新角度并不收敛到该实根； 批量均值反馈、有限精度与噪声分别满足明确误差界。 复方程的全部非实根由一个严格单调的实函数完整参数化， 每个根简单且对直接余弦迭代排斥。 最后给出 Transformer attention 的随机加权表示及非投影反例， 建立可使用的数学类比并限制物理同一性主张。

**关键词：** 内生观察者；量子仪器；注意控制；量子擦除； Zeno 动力学；不动点；统计反馈；可编程测量。

## 目录

- [1　问题分型与完整候选约束](#section-1)
- [2　内生仪器：观察者不是外部的测量指针](#section-2)
- [3　方向、概率与注意强度的分型](#section-3)
- [4　同一联合态的路径读口与干涉读口](#section-4)
- [5　芝诺极限：被限制的是跃迁，不是时间本身](#section-5)
- [6　余弦自反馈：由校准定义的不动点](#section-6)
- [7　实测反馈：单次结果、样本均值与非线性](#section-7)
- [8　复不动点的完整分类及其稳定性](#section-8)
- [9　计算注意力：保留可证明的桥梁](#section-9)
- [10　把注意策略、概念与历史同时内生](#section-10)
- [11　理论地位、可检验内容及下一步问题](#section-11)
- [A　固定来源与有界审计](#section-A)
- [B　原文范围、符号与复现](#section-B)

<a id="section-1"></a>

## 1　问题分型与完整候选约束

OTF-003 把概念单位定义为相对于观察代数的原子， 把概念后的关系分为纤维、切空间和态实际占据的相干。 本轮研究观察者怎样在整体内部选择这些读口，并改变后续演化。 “注意”在本文中是一个待实现的操作术语： 只有它对应可指定的控制状态、交互和记录，才进入概率与动力学方程。

需要区分四种动作：同时变换状态与效应的坐标描述； 实际改变仪器；与系统发生测量交互；按已有记录选取条件子集。 前者保持相同的物理统计，后面三者承担不同的操作任务。 将它们统称为“聚焦”会丢失可以检验的条件。

单次探测的离散记录与重复实验中的干涉条纹也可以共存： 前者描述结果事件，后者描述相位相关的概率分布。 本文不把二者设为一次实验中互斥的本体身份。

### 1.1　候选 AX-004

#### 结构约束 1.1：A1：整体与内部端口

给定有限维复空间

$$
\mathcal H_\Omega=\mathcal H_S\otimes\mathcal H_C\otimes\mathcal H_R
 \otimes\mathcal H_M\otimes\mathcal H_E.
$$

$S$ 是目标端口，$C$ 是控制程序，$R$ 是方向或相位参考， $M$ 是可访问记忆，$E$ 是其他未访问自由度。 这一分解描述访问关系，不在整体外另加观察者。 整体允许相关态，不默认程序与目标独立。

#### 结构约束 1.2：A2：概率与组合规则

态为正的迹一算子，效应满足 $0\leq G\leq I$， 概率为 $\operatorname{tr}(\rho G)$。有限仪器采用完全正、迹不增分支， 其和保迹。张量组合、Born 配对及 Kraus 规则在本稿明确采用， 不是从 $\cos x=x$ 单独推得。

#### 结构约束 1.3：A3：注意作为内部设置

注意设置包含程序、允许仪器、终端效应、可访问参考与记录更新。 正交程序码可以选择有限个设置；相干程序需规定实际相干实现。 一个 qubit 测量轴只是一种设置的部分参数， 不替代测量强度、记录选择和空间位置测量。

#### 结构约束 1.4：A4：记录与条件化

实际结果用内部正交指针编码。 保留全部记录、忽略记录、条件于一个结果以及擦除标记是不同操作。 每个条件概率说明其条件事件及非零分母。 无条件局部统计使用完整仪器之和，不把事后分组误作对先前总统计的改变。

#### 结构约束 1.5：A5：动力学与监测

给定 Hermitian $H$、$\hbar>0$ 及内部时钟校准。 有限维演化为 $e^{-\mathrm iHt/\hbar}$。 理想瞬时投影、频率、强度和有限时长是分别声明的协议条件； 无限次 Zeno 极限只作为一列有限协议的数学极限。

#### 结构约束 1.6：A6：反馈与精度

反馈程序指定从已有记录到下一设置的映射。 理想标量律 $x_{n+1}=s\cos x_n$ 使用弧度数值和单位增益； 真实单次记录、批量估计及量化误差另行建模。 有限寄存器只存有限精度；连续实数控制是理想模型， 不声称一个固定有限程序空间精确存储所有实数角度。

#### 结构约束 1.7：A7：内生闭合与经验桥梁

每个指定的有限操作序列及其记录可置入同一整体的幺正扩张和历史态。 这说明模型相容，不单独选定自然界的实际初态、反馈律或 Hamiltonian。 认知注意、物理仪器和计算注意之间的对应需要各自的实现桥梁； 共同使用内积不自动构成物理同一性。

| 需要回答的问题   | 本稿使用的量                    | 不能替代它的量   |
|:-----------------|:--------------------------------|:-----------------|
| 某标签是否确定   | $\operatorname{tr}(\rho P)=1$ | 空间位置宽度     |
| 是否知道路径     | 路径判别度 $\mathcal D$       | 主观专注程度     |
| 是否出现条纹     | 指定扫描的可见度 $\mathcal V$ | 仅有非零几何面积 |
| 是否改变物理态   | 仪器及其非选择通道              | 被动坐标重写     |
| 是否停止演化     | $H$、监测及所保留子空间       | 单次读出为确定值 |
| 是否达到反馈平衡 | 明确映射的固定点与稳定性        | 名称“自指”本身   |

<a id="section-2"></a>

## 2　内生仪器：观察者不是外部的测量指针

#### 定义 2.1：注意控制合同

以下为书写方便，按 $C\otimes(S\otimes R)\otimes M\otimes E$ 重排整体张量因子，未参与当前公式的因子写作恒等作用。 一个设置 $c$ 指定仪器 $\mathcal I_b^{(c)}$、 终端效应菜单、参考访问和记忆更新规则。 同一设置中的条件分支为

$$
\mathcal I_b^{(c)}(\rho)
 =\sum_\mu K_{b\mu}^{(c)}\rho K_{b\mu}^{(c)\dagger},
 \qquad
 \sum_{b,\mu}K_{b\mu}^{(c)\dagger}K_{b\mu}^{(c)}=I.
$$

参考 $R$ 可并入这些 Kraus 算子作用的目标空间， 其准备与访问必须列在合同中。

#### 定理 2.2：内部受控仪器的幺正实现

给定有限正交程序基 $\{|c\rangle\}$， 用零项补齐各设置的结果和 Kraus 指标。 定义

$$
V=\sum_c|c\rangle\langle c|\otimes
 \left(\sum_{b,\mu}K_{b\mu}^{(c)}\otimes|b,\mu\rangle\right).
$$

则 $V^\dagger V=I$。加入内部准备寄存器后， $V$ 可扩张为整体中的幺正交互。

**证明。**

控制投影正交，因此

$$
V^\dagger V=
 \sum_c|c\rangle\langle c|\otimes
 \sum_{b,\mu}K_{b\mu}^{(c)\dagger}K_{b\mu}^{(c)}
 =I_C\otimes I.
$$

准备子空间和像子空间同维，分别补齐正交归一基， 即可把子空间间的等距映射扩张为总空间幺正。

$\square$

若控制与目标的联合态为

$$
\xi_{CS}=\sum_c|c\rangle\langle c|\otimes\rho_c,
 \qquad \rho_c\geq0,\quad\sum_c\operatorname{tr}\rho_c=1,
$$

则结果 $b$ 的非归一输出是 $\sum_c\mathcal I_b^{(c)}(\rho_c)$。 不能在程序与目标相关时，把所有 $\rho_c$ 擅自替换成同一个系统边缘态乘以程序概率。 相干程序还含 $c\ne d$ 的交叉块， 它们只在相应寄存器被忽略或不可访问后才从该局部描述中消失。

#### 命题 2.3：通道不唯一指定相干控制

两个系统门 $U_0=I$、$U_1=e^{\mathrm i\beta}I$ 具有相同的系统通道，但受控实现作用于 $|+\rangle_C|\psi\rangle$ 后，控制的 $X+$ 概率为 $(1+\cos\beta)/2$。

**证明。**

输出是 $(|0\rangle+e^{\mathrm i\beta}|1\rangle)|\psi\rangle/\sqrt2$。 取控制 $|+\rangle$ 的内积平方得到所给概率。

$\square$

所以“相干注意”需要给出门的相干实现和参考； 不能仅凭相同的 CP 通道就认为跨设置相位已经被确定。

#### 定理 2.4：有限程序不能精确选择连续全部锐轴

设固定装置的二元效应 $G$ 作用于 qubit 与程序空间 $C$。 纯程序 $\eta_{\mathbf m}$ 精确实现 $P_{\mathbf m}=(I+\mathbf m\cdot\boldsymbol{\sigma})/2$。 若 $\mathbf m\ne\mathbf n$，则

$$
\langle\eta_{\mathbf m},\eta_{\mathbf n}\rangle=0.
$$

因此 $\dim C=D$ 时，至多可用纯程序精确实现 $D$ 个不同的锐轴测试 （结果标签固定）。

**证明。**

输入 $|\mathbf m,+\rangle|\eta_{\mathbf m}\rangle$ 对 $G$ 的回答概率为一， 输入 $|\mathbf n,-\rangle|\eta_{\mathbf n}\rangle$ 的概率为零。 因为 $0\leq G\leq I$，前者是 $G$ 的特征值一向量，后者属于其核， 两向量必须正交。因此

$$
\langle\mathbf m,+|\mathbf n,-\rangle
 \langle\eta_{\mathbf m}|\eta_{\mathbf n}\rangle=0.
$$

当 $\mathbf m\ne\mathbf n$， $|\langle\mathbf m,+|\mathbf n,-\rangle|^2 =(1-\mathbf m\cdot\mathbf n)/2>0$， 所以程序正交。有限维空间中的正交非零向量至多有 $D$ 个。

$\square$

这并不禁止有限装置近似测量许多方向， 也不禁止分别给定不同硬件设置。 它限制的是 *同一个固定装置仅靠有限维纯程序精确编程全部连续锐方向* 。 一根可以连续取向的量子参考轴不是自动可完美读取的经典程序表。

<a id="section-3"></a>

## 3　方向、概率与注意强度的分型

#### 命题 3.1：几何乘积的准确类型

定向 Euclidean 空间中的单位向量满足

$$
\mathbf o\mathbf n
 =\mathbf o\cdot\mathbf n+\mathbf o\wedge\mathbf n
 =\cos\theta+B\sin\theta,\qquad 0<\theta<\pi,
$$

其中 $B=(\mathbf o\wedge\mathbf n)/\sin\theta$ 为单位二向量。 第一项是标量，第二项是二向量；$B$ 本身依赖这对方向。

**证明。**

Clifford 关系把乘积分为对称标量与反对称二向量。 单位向量内积为 $\cos\theta$， 其外积范数为 $\sin\theta$；归一化即得。 在共线端点二向量为零，其单位方向没有由该对向量唯一指定。

$\square$

这个代数恒等式不单独定义量子仪器。 三维单位轴自身有两个角坐标； 相对夹角只足够确定某个简单二元概率， 并不包含转动平面的全部信息，也不包含耦合强度和记录访问。

#### 定理 3.2：Bloch 半角与读出互补量

设

$$
\rho=\frac{I+\mathbf r\cdot\boldsymbol{\sigma}}{2},\quad
 P_{\mathbf m}=\frac{I+\mathbf m\cdot\boldsymbol{\sigma}}{2},\quad|\mathbf m|=1.
$$

则

$$
p_+=\frac{1+\mathbf r\cdot\mathbf m}{2}.
$$

在允许平衡横向比较时，定义

$$
\mathcal P_{\mathbf m}=|\mathbf r\cdot\mathbf m|,\qquad
 \mathcal V_{\mathbf m}
 =\sqrt{|\mathbf r|^2-(\mathbf r\cdot\mathbf m)^2}.
$$

有 $\mathcal P_{\mathbf m}^2+\mathcal V_{\mathbf m}^2=|\mathbf r|^2\leq1$。 纯态 Bloch 夹角为 $\theta$ 时，

$$
p_+=\cos^2(\theta/2),\qquad
 \mathcal P=|\cos\theta|,\qquad
 \mathcal V=|\sin\theta|.
$$

**证明。**

由 $\operatorname{tr}\sigma_i=0$、$\operatorname{tr}(\sigma_i\sigma_j)=2\delta_{ij}$ 得到概率式。取 $\mathbf m$ 为 $z$ 轴， 跨块元为 $(r_x-\mathrm ir_y)/2$， 平衡相位扫描的可见度为其模的两倍。 任意轴由共同幺正共轭得到。余下等式为 Euclidean 分解及半角恒等式。

$\square$

$\theta=\pi/2$ 时回答概率是 $1/2$，不是对象消失。 $\theta=0$ 时某个内部概念确定，也没有推出空间位置确定。 例如在 $\mathcal H_{\rm spin}\otimes\mathcal H_{\rm position}$ 中， 同一个自旋态乘以任意不同空间态， 对 $P_{\mathbf m}\otimes I$ 给出完全相同的读数。

#### 命题 3.3：被动转动与实际操作

同时变换 $\rho\mapsto U\rho U^\dagger$、 $G\mapsto UGU^\dagger$ 不改变概率。 实际仪器则须另给状态更新。

**证明。**

循环迹给出 $\operatorname{tr}(U\rho U^\dagger UGU^\dagger)=\operatorname{tr}(\rho G)$。 该式没有包含一个新的相互作用。

$\square$

#### 反例 3.4：正交关注不会自动恢复相干

取 $\rho=|+x\rangle\langle +x|$。 沿 $z$ 真正执行锐测量并忽略结果，得到 $\mathcal D_z(\rho)=I/2$。 此态在任意单 qubit 平衡相位扫描中都有零可见度。 若完全不执行交互，只在语言上改变关注对象，$\rho$ 则不变。 这两种操作均不符合“转到正交方向便自动成为纯波”的普遍断言。

#### 定理 3.5：方向与测量强度相互独立

令 $Z=Z^\dagger$、$Z^2=I$，$0\leq\eta\leq1$，

$$
E_b=\frac{I+b\eta Z}{2},\qquad K_b=\sqrt{E_b},\quad b=\pm1.
$$

非选择通道保持 $Z$ 的对角块，交叉块乘以 $\nu=\sqrt{1-\eta^2}$。 在 $Z=\sigma_z$ 时，

$$
(r_x,r_y,r_z)\longmapsto(\nu r_x,\nu r_y,r_z),
 \qquad\mathbb E[b]=\eta r_z.
$$

**证明。**

在 $Z$ 的本征基中，$K_b$ 的两个对角值为 $\sqrt{(1+b\eta)/2}$ 和 $\sqrt{(1-b\eta)/2}$。 对角概率系数求和为一， 交叉项系数求和为 $\sqrt{1-\eta^2}$。 结果均值为 $\operatorname{tr}\rho(E_+-E_-)=\eta\operatorname{tr}(\rho Z)$。

$\square$

$\eta=0$ 时仪器不给出状态信息且非选择通道为恒等； $\eta=1$ 时完全分块。 对同一测量轴，仅改变 $\eta$ 就产生不同的扰动， 所以一个相对夹角不是全部“注意”的参数。 若每步间隔 $\delta$、$\eta^2=2\kappa\delta+O(\delta^2)$， 则重复监测的交叉块极限为 $e^{-\kappa t}C$， 对应 $\dot\rho=(\kappa/2)(Z\rho Z-\rho)$。 这是物理耦合造成的效应，不以人是否观看为额外条件。

<a id="section-4"></a>

## 4　同一联合态的路径读口与干涉读口

#### 定义 4.1：路径与标记

设整体内部包含

$$
|\Psi_\phi\rangle
 =\sqrt p\,|0\rangle|m_0\rangle
 +e^{\mathrm i\phi}\sqrt q\,|1\rangle|m_1\rangle,
 \qquad p,q\ge0,\quad p+q=1,
$$

标记态归一，$\gamma=\langle m_1|m_0\rangle$。 路径可见度由扫描 $\phi$ 后的平衡比较定义； 路径判别度由允许访问的标记测量定义。

#### 定理 4.2：纯标记互补关系

若完整标记空间可以测量，则

$$
\mathcal V=2\sqrt{pq}|\gamma|,
 \qquad
 \mathcal D=
 \left\|p|m_0\rangle\langle m_0|-q|m_1\rangle\langle m_1|\right\|_1
 =\sqrt{1-4pq|\gamma|^2}.
$$

最佳猜测路径成功率为 $(1+\mathcal D)/2$，且

$$
\boxed{\mathcal D^2+\mathcal V^2=1.}
$$

**证明。**

偏迹后的路径交叉元是 $\sqrt{pq}e^{-\mathrm i\phi}\gamma$， 平衡读出概率为 $1/2+\sqrt{pq}\Re(e^{-\mathrm i\phi}\gamma)$， 给出 $\mathcal V$。 记 $\Delta=p|m_0\rangle\langle m_0|-q|m_1\rangle\langle m_1|$。 猜测路径 $0$ 的效应为 $G$ 时，成功率是 $q+\operatorname{tr}(G\Delta)$，其最大值为 $q+\operatorname{tr}\Delta_+=(1+\left\|\Delta\right\|_1)/2$。 在两标记的张成空间内，$\Delta$ 的迹为 $p-q$、 行列式为 $-pq(1-|\gamma|^2)$， 所以非零特征值给出 $\left\|\Delta\right\|_1=\sqrt{1-4pq|\gamma|^2}$。 线性相关、零先验等边界直接代入或由连续性得到。

$\square$

该结构与标准路径可辨识度–可见度关系一致[\[1\]](#ref-englert)。 若标记只能通过受限菜单访问， $\mathcal D_{\rm acc}\leq\mathcal D$， 故仍有 $\mathcal D_{\rm acc}^2+\mathcal V^2\leq1$， 但不保证等号。 特别地，在 $p=q=1/2$、标记正交的例子中， 不访问标记可使 $\mathcal D_{\rm acc}=0$，而 $\mathcal V=0$ 仍不变。 一般先验下仍有 $\mathcal D_{\rm acc}\ge|p-q|$； 减少知识不会自动解除已经发生的标记耦合。

#### 定理 4.3：对记录的无条件局部处理不改系统边缘

对任意联合态 $\rho_{SM}$ 和记录上的保迹通道 $\Lambda_M$，

$$
\operatorname{tr}_M[(\mathrm{id}\otimes\Lambda_M)(\rho_{SM})]
 =\operatorname{tr}_M\rho_{SM}.
$$

**证明。**

对任意系统效应 $G$， 左边的概率等于 $`\operatorname{tr}[\rho_{SM}(G\otimes\Lambda_M^*(I))]`$。 保迹性给出 $`\Lambda_M^*(I)=I`$，故所有系统效应的概率相同。 效应分离状态，得到边缘态相同。

$\square$

条件选取某个记录结果不属于这个无条件等式； 它能改变所讨论子样本的状态，但总统计是各条件状态的加权和。

#### 定理 4.4：同一内生态的两类读口

固定

$$
|\Omega_\phi\rangle
 =\frac{|0\rangle|+\rangle +e^{\mathrm i\phi}|1\rangle|-\rangle}{\sqrt2},
 \qquad |\pm\rangle=(|0\rangle\pm|1\rangle)/\sqrt2.
$$

有以下两种内部协议：

1.  标记按 $X$ 基读取，两个结果分别指定系统路径 $0,1$， 各以概率 $1/2$ 出现。

2.  标记按 $Z$ 基读取，结果 $r\in\{0,1\}$ 各以概率 $1/2$ 出现， 系统条件态为

    $$
    |\chi_r\rangle=
     \frac{|0\rangle+(-1)^re^{\mathrm i\phi}|1\rangle}{\sqrt2}.
    $$
    对系统的 $X$ 结果 $b=\pm1$，

    $$
    p(b,r\mid\phi)
     =\frac14[1+b(-1)^r\cos\phi].
    $$

无论选择哪一标记读口，不按标记分类的系统 $X$ 概率都是 $1/2$。

**证明。**

第一项直接由联合态在 $|+\rangle,|-\rangle$ 标记基中的展开得到。 将标记改写为计算基，可得

$$
|\Omega_\phi\rangle
 =\frac12\left[
 (|0\rangle+e^{\mathrm i\phi}|1\rangle)|0\rangle+
 (|0\rangle-e^{\mathrm i\phi}|1\rangle)|1\rangle\right].
$$

每个括号范数平方为二，故标记概率为 $1/2$， 归一化即得条件态。与系统 $X$ 本征态取内积平方，得到联合概率。 对 $r$ 求和，正负干涉项抵消。

$\square$

这里两种读口确实决定 *哪一种关系被显现* 。 但这需要实际的量子读口变换和联合记录； 仅改变人的主观兴趣不能替代协议。 两个局部末端测量的算子对易，故交换读取顺序不改变联合概率， 无须把事后条件条纹解释成改写先前的总记录。

项目 v66 已提供相应的相位型记录例子： $M_0=I/\sqrt2$、$M_1=Z/\sqrt2$ 的指定经典结果分布没有路径标签信息， 但完整探针中的 $|+\rangle,|-\rangle$ 正交，换读口后可以区分路径。 对已经取得的无信息经典比特做后处理，不能代替此前的量子读口变换 [\[7\]](#ref-repov66)。

<a id="section-5"></a>

## 5　芝诺极限：被限制的是跃迁，不是时间本身

量子芝诺效应需要实际的系统–仪器交互及其记录机制。 Itano 等的原实验论文明确区分了电磁场中已形成的记录与人是否读取探测器； 其有限脉冲分析也不能被替换为无条件的永久冻结 [\[3\]](#ref-itano)。下面直接证明有限维版本，以明确本理论的范围。 无限维算符的定义域、强极限存在性与连续性不由以下证明覆盖 [\[2\]](#ref-misra), [\[4\]](#ref-facchi)。

#### 定理 5.1：固定子空间的芝诺极限与误差

设 $H=H^\dagger$ 为有限维 Hamiltonian，$\hbar>0$， $P$ 为正交投影，$Q=I-P$，$t\in\mathbb R$。令

$$
A_N=\left(Pe^{-\mathrm iHt/(N\hbar)}P\right)^N .
$$

则

$$
A_N\longrightarrow e^{-\mathrm iPHPt/\hbar}P,
$$

且

$$
\boxed{\;
 \left\|A_N-e^{-\mathrm iPHPt/\hbar}P\right\|
 \le\frac{t^2}{2N\hbar^2}
 \left(\left\|H\right\|^2+\left\|PHP\right\|^2\right)
 \le\frac{t^2\left\|H\right\|^2}{N\hbar^2}.
 \;}
$$

**证明。**

令 $\delta=t/N$，$A=Pe^{-\mathrm iH\delta/\hbar}P$， $B=e^{-\mathrm iPHP\delta/\hbar}P$。两者均为收缩算子。 对任意 Hermitian $K$，积分余项及酉性给出

$$
\left\|e^{-\mathrm iK\delta/\hbar}-I+\mathrm iK\delta/\hbar\right\|
 \le\frac{\delta^2\left\|K\right\|^2}{2\hbar^2}.
$$

$A$ 与 $B$ 的零阶、一阶项均为 $P-\mathrm iPHP\delta/\hbar$， 故单步误差至多为定理右端的 $1/N$ 倍。 使用不要求对易的恒等式

$$
A^N-B^N
 =\sum_{k=0}^{N-1}A^{N-1-k}(A-B)B^k
$$

及收缩性，得到 $N$ 倍单步误差界。 由于 $B^N=e^{-\mathrm iPHPt/\hbar}P$，结论成立。

$\square$

#### 定理 5.2：全程成功记录的泄漏界

若 $\rho=P\rho P$ 且 $\operatorname{tr}\rho=1$，$N$ 次记录均为 $P$ 的概率为 $p_N=\operatorname{tr}(A_N\rho A_N^\dagger)$，并满足

$$
0\le1-p_N\le
 \frac{t^2\left\|QHP\right\|^2}{N\hbar^2}.
$$

**证明。**

令 $H_0=PHP+QHQ$。Duhamel 公式给出

$$
(e^{-\mathrm iH\delta/\hbar}-e^{-\mathrm iH_0\delta/\hbar})P
 =-\frac{\mathrm i}{\hbar}\int_0^\delta
 e^{-\mathrm iH(\delta-u)/\hbar}(H-H_0)
 e^{-\mathrm iH_0u/\hbar}P\,\mathrm du .
$$

右侧中 $(H-H_0)e^{-\mathrm iH_0u/\hbar}P =QHP e^{-\mathrm iPHPu/\hbar}P$。 左乘 $Q$ 后，因 $Qe^{-\mathrm iH_0\delta/\hbar}P=0$，得到

$$
\left\|Qe^{-\mathrm iH\delta/\hbar}P\right\|
 \le|\delta|\left\|QHP\right\|/\hbar .
$$

每个留存的子归一化态支撑于 $P$，其迹至多为一， 故单步失去的概率至多为 $\delta^2\left\|QHP\right\|^2/\hbar^2$。 对 $N$ 个步骤的概率损失求和即得。

$\square$

#### 例 5.3：全程存活不等于末次结果

取 $H=\hbar\Omega\sigma_x/2$、$P=|0\rangle\langle 0|$，初态为 $|0\rangle$。 在 $N$ 次均匀间隔测量中，

$$
p_N^{\rm all}
 =\cos^{2N}\!\left(\frac{\Omega t}{2N}\right).
$$

若忽略中间结果，只问末次是否为 $0$，则

$$
p_N^{\rm final}
 =\frac{1+\cos^N(\Omega t/N)}2 .
$$

第一式来自每次成功后重新落在 $|0\rangle$； 第二式来自每次非选择测量后的 $z$ 分量乘以 $\cos(\Omega t/N)$。它们在固定 $t$、$N\to\infty$ 时都趋于一， 但有限 $N$ 时不是同一个概率。 甚至有限次数的全程存活率不必单调： 取 $\Omega t=2\pi$，则 $p_1^{\rm all}=1$ 而 $p_2^{\rm all}=0$。 此例仅限制无条件单调性表述，并未分析连续谱衰变的反芝诺机制。

#### 反例 5.4：持续确定的标签可以包含持续变化

在 $\mathbb C^3$ 中取

$$
P=|0\rangle\langle 0|+|1\rangle\langle 1|,\qquad
 H=\hbar\omega(|0\rangle\langle 1|+|1\rangle\langle 0|)
   +\hbar g(|1\rangle\langle 2|+|2\rangle\langle 1|).
$$

芝诺极限抑制向 $|2\rangle$ 的泄漏，但从 $|0\rangle$ 出发仍有

$$
e^{-\mathrm iPHPt/\hbar}|0\rangle
 =\cos(\omega t)|0\rangle-\mathrm i\sin(\omega t)|1\rangle.
$$

标签 $P$ 始终确定，子空间内的可区分状态仍在变化。 因此“确定存在”与“所有生成停止”并不等价。

#### 定理 5.5：移动注意设置可以输运状态

设归一化路径 $\psi:[0,T]\to\mathcal H$ 为 $C^1$， $L_\psi=\max_t\left\|\dot\psi(t)\right\|$。 在自由 $H=0$ 时，从 $\psi(0)$ 出发依次测量 $P_k=|\psi(kT/N)\rangle\langle \psi(kT/N)|$。 当全程成功概率 $p_N>0$ 时，条件末态射线恰为 $[\psi(T)]$，且

$$
p_N=\prod_{k=1}^N
 |\langle\psi(kT/N),\psi((k-1)T/N)\rangle|^2
 \ge1-\frac{L_\psi^2T^2}{N}.
$$

**证明。**

每个成功投影给出下一指定射线，故概率相乘。 归一化向量 $u,v$ 满足

$$
1-|\langle u,v\rangle|^2
 \le2(1-\operatorname{Re}\langle u,v\rangle)=\left\|u-v\right\|^2.
$$

路径导数界把每步失败率限制在 $L_\psi^2(T/N)^2$ 以内。 再用 $\prod_k(1-a_k)\ge1-\sum_k a_k$，其中 $0\le a_k\le1$， 即得所述下界。

$\square$

#### 命题 5.6：芝诺约束不会取消内部时钟

设 $\mathcal H_T$ 是内部时钟，整体含 $H_\Omega=H_T\otimes I+I\otimes H_S$， 约束为 $\Pi=I_T\otimes P$。压缩生成元为

$$
\Pi H_\Omega\Pi=H_T\otimes P+I_T\otimes PH_SP.
$$

故时钟仍按 $H_T$ 演化。即使 $P=|\psi\rangle\langle \psi|$ 为秩一， 系统传播算子也保留 $e^{-\mathrm i\langle H_S\rangle_\psi t/\hbar}P$。

**证明。**

直接乘开 $\Pi H_\Omega\Pi$，其两个项对易。 秩一压缩满足 $PH_SP=\langle H_S\rangle_\psi P$。

$\square$

孤立射线的整体相位不可由其自身测量读出；加入可访问的相干参考后， 相应分支相位才可能成为相对相位。以上结论均未使用 “面积为零所以时间消失”的假设。

<a id="section-6"></a>

## 6　余弦自反馈：由校准定义的不动点

#### 定义 6.1：带符号的理想反馈政策

给定内部二值控制 $s\in\{+1,-1\}$，以弧度数值编码控制角， 定义

$$
F_s(x)=s\cos x,\qquad x_{n+1}=F_s(x_n).
$$

其不动点方程 $x=s\cos x$ 等价于 $\cos x=sx$。 这里把归一化平均投影重新编码为下一轮角度，是 *一项指定控制律* 。

#### 定理 6.2：唯一实不动点与全局收敛

令 $I=[-1,1]$、$L=\sin1<1$。 存在唯一 $\alpha\in(0,1)$ 满足 $\cos\alpha=\alpha$。 对每个 $s=\pm1$，$F_s$ 的唯一实不动点为 $s\alpha$； 任意实初值的轨道均收敛于该点，且 $n\ge1$ 时

$$
\boxed{\quad
 |x_n-s\alpha|\le L^{n-1}|x_1-s\alpha|
 \le2L^{n-1}.\quad}
$$

**证明。**

$F_s(\mathbb R)\subset I$，且在 $I$ 上 $|F_s'(x)|=|\sin x|\le L<1$。 从第一步起，相邻轨道差由几何级数控制，故轨道是柯西列。 其极限由连续性为不动点。若 $u,v$ 都是不动点， $|u-v|\le L|u-v|$ 迫使 $u=v$。 正号方程在 $0,1$ 两端异号，故根在 $(0,1)$； 余弦偶性给出负号根 $-\alpha$。 将压缩估计逐次应用于轨道与不动点即得误差界。

$\square$

#### 推论 6.3：停止误差与局部乘子

对 $n\ge1$，

$$
|x_n-s\alpha|\le
 \frac{|x_{n+1}-x_n|}{1-L}.
$$

两个政策的局部乘子相同：

$$
F_+'(\alpha)=F_-'(-\alpha)=-\sin\alpha .
$$

**证明。**

第一式由后续相邻差的几何级数尾和得到； 第二式把 $s\alpha$ 代入 $F_s'(x)=-s\sin x$。

$\square$

#### 命题 6.4：符号政策的共轭

令 $R(x)=-x$，则 $F_-=R\circ F_+\circ R$。 若扩展内部状态为 $(s,x)$，更新 $\mathfrak F(s,x)=(s,s\cos x)$， 则 $J(s,x)=(-s,-x)$ 满足 $\mathfrak FJ=J\mathfrak F$。

**证明。**

均由 $\cos(-x)=\cos x$ 直接计算。

$\square$

这给出一个准确的政策对称性。两个不动点位于守恒控制位 $s$ 标记的两个不变部分；它没有定义电荷共轭、反粒子、 时间反演或热力学箭头，因而不能单凭符号赋予这些物理含义。 若每轮改变 $s_n$，第一步后 $|x_{n+1}|=\cos|x_n|$，所以模长仍趋于 $\alpha$， 但符号持续切换时完整状态可以没有极限。

### 6.1　数值比例的正确解释

$$
\alpha=0.7390851332151606416553\ldots,\qquad
 \alpha\,\frac{180}{\pi}=42.3464588340929\ldots{}^\circ .
$$

以 $x$ 为 Bloch 极角、以 $Z$ 为读出时，

$$
|\psi(x)\rangle=\cos(x/2)|0\rangle+\sin(x/2)|1\rangle.
$$

在 $x=\alpha$ 处，得到

$$
\begin{aligned}
 p_+&=\frac{1+\alpha}{2}=0.8695425666\ldots,\\
 \mathcal P^2&=\alpha^2=0.5462468341\ldots,\\
 \mathcal V^2&=1-\alpha^2=0.453753165860328\ldots .
 \end{aligned}
$$

后两项是指定纯二路径实验中可预测度与最大可见度的平方， 不是“系统以 $54.62\%$ 的概率是粒子、以 $45.38\%$ 的概率是波”。 如果改写态为 $\cos x|0\rangle+\sin x|1\rangle$，则 $p_0=\cos^2x$， 但其 Bloch 极角已经变成 $2x$。

同时必须区分三种几何量：半径 $R$ 下的轴向投影为 $R\cos x$， 有向弧长为 $Rx$，有向扇形面积为 $R^2x/2$； 两单位向量外积的模则为 $|\sin x|$。 令 $R=1$ 并未使这些量具有同一种操作含义。 普通两向量夹角属于 $[0,\pi]$； 使用正负 $x$ 还须给定一个有定向的旋转平面。 平面中的 $\pm\alpha$ 只是两个方向； 完整圆锥需要另加方位角轨道

$$
\mathbf n(\varphi)=
 \cos\alpha\,\mathbf o+
 \sin\alpha(\cos\varphi\,\mathbf e_1+\sin\varphi\,\mathbf e_2).
$$

余弦也不在全实轴为正，例如 $\cos\pi=-1$； 当前实根的正投影来自 $|x|\le1$。 在负根处 $x_-=-\alpha<0$，但 $-x_-=\alpha>0$。

### 6.2　增益、偏置与有限精度

#### 定理 6.5：校准改变固定点及稳定性

对 $b\in\mathbb R$、$0\le g<1$， $F_{s,g,b}(x)=b+sg\cos x$ 是 $\mathbb R$ 上的压缩映射， 故有唯一全局吸引实不动点。 另对任意 $g>0$，在零偏置时，主分支 $a_g\in(0,\pi/2)$ 由 $a_g=g\cos a_g$ 唯一确定，且

$$
\frac{\mathrm da_g}{\mathrm dg}
 =\frac{\cos a_g}{1+g\sin a_g}>0,\qquad
 |F_{s,g,0}'(s a_g)|=a_g\tan a_g.
$$

存在唯一 $a_c\in(0,\pi/2)$ 使 $a_c\tan a_c=1$。 相应 $g_c=a_c/\cos a_c\approx1.31915650489$； 主分支在 $g<g_c$ 时局部吸引，在 $g>g_c$ 时局部排斥。

**证明。**

全局导数模至多为 $g<1$，像落入闭区间 $[b-g,b+g]$， 故与定理 6.2 同样的柯西论证适用。 函数 $a/\cos a$ 在 $(0,\pi/2)$ 上严格递增，值域为 $(0,\infty)$， 给出主分支；隐函数微分给出导数。 使用 $g=a_g/\cos a_g$ 得到乘子公式。 函数 $a\tan a$ 严格从零增至无穷，给出唯一临界值。 乘子模小于一或大于一时的局部结论来自 Taylor 展开。

$\square$

该定理不声称大增益下不存在其他实根，也不单凭临界乘子 $-1$ 就认定分岔类型。它说明单位增益选择必须由额外校准原则来固定； 否则 $\alpha$ 是政策相关数值，不能称为已推导的普适物理常数。 若将弧度坐标改为 $y=kx$，同一政策变成 $y_{n+1}=ks\cos(y_n/k)$；直接写成 $y_{n+1}=s\cos y_n$ 已经更换了政策。

#### 定理 6.6：有限网格的误差管

设 $Q_\epsilon:I\to I$ 取值于有限网格， 且 $|Q_\epsilon(y)-y|\le\epsilon$。 若 $x_0\in I$，$x_{n+1}=Q_\epsilon(F_s(x_n))$，则

$$
|x_n-s\alpha|
 \le L^n|x_0-s\alpha|
   +\epsilon\frac{1-L^n}{1-L},
 \qquad
 \limsup_n|x_n-s\alpha|\le\frac{\epsilon}{1-L}.
$$

有限网格上的确定性轨道最终周期化，但未必固定于一个网格点。

**证明。**

三角不等式给出 $|x_{n+1}-s\alpha|\le L|x_n-s\alpha|+\epsilon$。 递推求和即得界。有限状态的确定性轨道必重访某个状态； 此后由同一更新律重复其周期。

$\square$

<a id="section-7"></a>

## 7　实测反馈：单次结果、样本均值与非线性

#### 定义 7.1：内部制备–读出–再编码协议

在第 $n$ 轮，历史 $\mathcal F_n$ 确定控制角 $x_n$。 使用内部准备资源制备 $|\psi(x_n)\rangle=R_y(x_n)|0\rangle$，测量 $Z$， 结果 $Y_n\in\{-1,+1\}$ 满足

$$
\Pr(Y_n=b\mid\mathcal F_n)
 =\frac{1+b\cos x_n}{2},\qquad
 \mathbb E[Y_n\mid\mathcal F_n]=\cos x_n.
$$

每轮重复样本指条件于当前程序独立制备的新系统； 不默认对同一未知单拷贝反复测量能提供这些样本。

#### 定理 7.2：单次结果反馈不收敛于余弦不动点

若采用 $x_{n+1}=sY_n$，则第一步后 $x_n\in\{-1,+1\}$， 且不可能依概率或几乎必然收敛于 $s\alpha$。 从第二轮测量起，$Y_n$ 为具有参数 $(1+\cos1)/2$ 的非退化独立同分布二值序列。

**证明。**

值域结论由反馈律直接给出。 对任意 $x_n=\pm1$，都有 $\cos x_n=\cos1$， 故后续条件概率与历史无关，联合分布分解为相同的 Bernoulli 因子。 同时 $|x_n-s\alpha|\ge1-\alpha>0$ 恒成立， 因此无法按上述任何一种意义趋近 $s\alpha$。

$\square$

这也是“把观察到的投影喂回去”的关键歧义： 平均读数 $\cos x$ 与实际的一次结果 $Y$ 是不同随机对象。 一般而言，$\mathbb E[\cos X]\ne\cos(\mathbb EX)$， 所以也不能把随机反馈的均值方程直接当成确定性余弦迭代。

#### 定理 7.3：样本均值反馈的误差与收敛

令 $(N_n)$ 为预先给定的确定性正整数序列。 每轮使用 $N_n$ 个条件独立样本，令

$$
\bar Y_n=\frac1{N_n}\sum_{j=1}^{N_n}Y_{n,j},
 \qquad x_{n+1}=s\bar Y_n,\qquad e_n=x_n-s\alpha .
$$

从 $x_n\in I$ 起，

$$
\boxed{\quad
 \mathbb E e_{n+1}^2
 \le L^2\mathbb E e_n^2+\frac1{N_n}.\quad}
$$

若 $N_n\to\infty$，则 $x_n\to s\alpha$ 均方收敛。 若进一步 $\sum_nN_n^{-1}<\infty$，则也几乎必然收敛。 固定 $N_n=N<\infty$ 时，

$$
\limsup_n\mathbb E e_n^2
 \le\frac1{N(1-L^2)},
$$

但不可能均方收敛于 $s\alpha$。

**证明。**

令 $\eta_n=s(\bar Y_n-\cos x_n)$，则 $\mathbb E(\eta_n\mid\mathcal F_n)=0$，且

$$
\mathbb E(\eta_n^2\mid\mathcal F_n)
 =\frac{\sin^2 x_n}{N_n}\le\frac1{N_n}.
$$

因此条件交叉项为零，精确地有

$$
\mathbb E e_{n+1}^2
 =\mathbb E|F_s(x_n)-s\alpha|^2
   +\mathbb E\frac{\sin^2x_n}{N_n},
$$

再用压缩界得到递推不等式。 其迭代是衰减几何项与序列 $1/N_n$ 的几何卷积； 当后者趋零时，把和分为有限头部与任意小的尾部，即得均方收敛。 固定 $N$ 的上界由几何级数求和得到。

若 $\sum N_n^{-1}<\infty$，Chebyshev 不等式给出 $\sum_n\Pr(|\eta_n|>\varepsilon)<\infty$。 对可数个正有理 $\varepsilon$ 使用 Borel–Cantelli 引理， 得到 $\eta_n\to0$ 几乎必然； 递推 $|e_{n+1}|\le L|e_n|+|\eta_n|$ 随即给出路径上的收敛。 最后，若固定 $N$ 却均方趋近 $s\alpha$， 则连续有界函数 $\sin^2x_n$ 的期望趋于 $\sin^2\alpha>0$。 上面的精确等式反而给出 $\liminf\mathbb E e_{n+1}^2\ge\sin^2\alpha/N>0$，矛盾。

$\square$

固定 $N$ 的显示式是 *上界* ，不能称为精确的噪声底。 有限实际协议需要同时选择步数、每轮样本数、角度网格及内部记录容量。 定理 2.4 和定理 6.6 也说明，固定有限程序空间不能未经近似就容纳全部精确实数设置。

#### 定理 7.4：理想余弦态映射不是固定单拷贝通道

令

$$
\rho(x)=\frac12(I+\sin x\,\sigma_x+\cos x\,\sigma_z).
$$

不存在对所有 $x\in[-1,1]$ 都满足 $\Lambda(\rho(x))=\rho(\cos x)$ 的固定线性量子通道 $\Lambda$。

**证明。**

对 $x$ 与 $-x$，目标态相同。 令 $t=\cos x\in[\cos1,1]$，由线性性必须有

$$
\Lambda(D_t)=\rho(t),\qquad
 D_t=\frac{\rho(x)+\rho(-x)}2=\frac{I+t\sigma_z}{2}.
$$

取 $t_1=\cos1$、$t_2=1$ 及 $t_m=(t_1+t_2)/2$。 输入满足 $D_{t_m}=(D_{t_1}+D_{t_2})/2$，故输出必须满足

$$
\rho(t_m)=\frac{\rho(t_1)+\rho(t_2)}2 .
$$

左侧为纯态，右侧为两种不同纯态的等权混合，秩为二， 产生矛盾。

$\square$

该定理不妨碍已知程序控制的制备、统计估计与反馈。 这些协议使用了额外程序、多个准备实例和结果记录； 它们的整体实现仍然线性。它阻止的是把对经典控制参数的非线性更新 直接宣布为未知单份量子态上的普遍固定演化。

这里的禁止范围是没有 $x$ 侧信息、附属系统初态固定的确定性通道。 若内部控制器本来已知 $x$，它可以直接计算 $\cos x$ 并制备目标态； 此时不必再估计一个已知期望，但所用扩展输入已包含参数程序。

<a id="section-8"></a>

## 8　复不动点的完整分类及其稳定性

将控制变量延拓为复数是一项数学扩展；本节尚未赋予虚部 物理时间、面积或能量的单位与读出规则。 以下定理给出比“存在无穷多个复根”更具体的结果。

#### 引理 8.1：复根的单调参数函数

对 $y>0$ 定义

$$
a(y)=\frac{y}{\sinh y},\qquad
 b(y)=\sqrt{1-a(y)^2},\qquad
 \beta(y)=\arcsin a(y),\qquad
 G(y)=b(y)\cosh y+\beta(y).
$$

则 $0<a<1$、$b>0$、$0<\beta<\pi/2$， 且 $G$ 严格递增，值域恰为 $(\pi/2,\infty)$。

**证明。**

$\sinh y>y$ 给出 $0<a<1$。 由 $\tanh y<y$ 得 $a'(y)<0$， 并有 $a(y)\cosh y=y\coth y>1$。 直接微分得

$$
G'(y)
 =b(y)\sinh y+
 \frac{a'(y)}{b(y)}\bigl(1-a(y)\cosh y\bigr)>0.
$$

当 $y\downarrow0$ 时，$a\to1$、$b\to0$、$\beta\to\pi/2$， 故 $G\to\pi/2$。当 $y\to\infty$ 时，$a\to0$、$b\to1$、 $\cosh y\to\infty$，故 $G\to\infty$。 连续性与严格单调性给出值域。

$\square$

#### 定理 8.2：$\cos z=\pm z$ 的全部复根

对每个整数 $n\ge1$，令 $y_n>0$ 为 $G(y_n)=n\pi$ 的唯一解，并定义

$$
x_n=(-1)^n\bigl(n\pi-\beta(y_n)\bigr).
$$

则正号方程的全部根恰为

$$
\boxed{\quad
 \{z:\cos z=z\}
 =\{\alpha\}\cup
 \{x_n+\mathrm iy_n,\ x_n-\mathrm iy_n:n\ge1\}.\quad}
$$

负号方程的根集是上述集合整体取负。

**证明。**

实根已由定理 6.2 给出。 设 $z=x+\mathrm iy$、$y>0$ 是正号根。 分离实虚部：

$$
\cos x\cosh y=x,\qquad-\sin x\sinh y=y.
$$

第二式等价于 $\sin x=-a(y)$。 第一式要求 $\cos x$ 与 $x$ 同号，并排除 $x=0$ 或 $\cos x=0$。 因此全部可能分支只有

$$
\begin{cases}
 x=2k\pi-\beta(y),&k\ge1,\quad \cos x=b(y),\\
 x=-(2k+1)\pi+\beta(y),&k\ge0,\quad \cos x=-b(y).
 \end{cases}
$$

分别代入第一式，得到 $G(y)=2k\pi$ 或 $G(y)=(2k+1)\pi$。 引理 8.1 保证每个分支恰有一个解， 合并偶数、奇数指标即得 $(x_n,y_n)$。 反向代入也立即验证每一所列点确为根，故没有遗漏。 实系数保证下半平面根由共轭得到。 最后，$\cos(-z)=\cos z$ 表明 $\cos z=z$ 当且仅当 $\cos(-z)=-(-z)$， 所以负号根集整体取负。

$\square$

#### 推论 8.3：根的简单性及渐近分布

两方程的全部根都是简单根，非实根序列无有限聚点。并且

$$
y_n=\log(2\pi n)+o(1),\qquad
 \beta(y_n)\sim\frac{\log(2\pi n)}{\pi n}.
$$

**证明。**

令 $f_s(z)=\cos z-sz$。 若 $f_s(z)=f_s'(z)=0$，则 $\cos z=sz$、$\sin z=-s$。 复三角恒等式给出 $z^2=0$， 但 $f_s(0)=1$，矛盾。 由 $G(y_n)=n\pi$ 及严格单调性，$y_n\to\infty$， 因此非实序列无有限聚点。 又 $b(y_n)\to1$、$\beta(y_n)\to0$， 故 $\cosh y_n/(n\pi)\to1$。 于是 $e^{y_n}/(2n\pi)\to1$， 给出第一项渐近式。 最后 $\beta(y)\sim a(y)=y/\sinh y$， 且 $\sinh y_n\sim n\pi$，得到第二项。

$\square$

#### 定理 8.4：全部非实余弦不动点严格排斥

对 $F_s(z)=s\cos z$， 每个非实不动点 $`z_*`$ 均满足 $`|F_s'(z_*)|>1`$。

**证明。**

写 $`z_*=x+\mathrm iy`$，其中 $y\ne0$。 方程给出

$$
\cos x\cosh y=sx,\qquad
 s\sin x=-\frac{y}{\sinh y}<0.
$$

若 $|x|\le\pi/2$，第一式蕴含 $sx\ge0$； 在该区间 $\sin x$ 与 $x$ 同号， 从而 $s\sin x\ge0$，矛盾。因此 $|x|>\pi/2$。 又因 $`\cos^2z_*=z_*^2`$，

$$
|F_s'(z_*)|^2
 =|\sin z_*|^2
 =|1-z_*^2|
 \ge|z_*|^2-1 > \frac{\pi^2}{4}-1>1.
$$

给定 $`1<q<|F_s'(z_*)|`$，Taylor 展开保证 充分小的非零 $w$ 满足 $`|F_s(z_*+w)-z_*|\ge q|w|`$， 这正是局部排斥性。

$\square$

“排斥”是复迭代中以乘子模分类的不动点术语[\[6\]](#ref-bergweiler)。 它不等于已经证明邻近轨道都逃向无穷， 也不完成整个复动力系统的分类。 非实固定点本身作为初值会保持不动， 所以实轴上的全局收敛结论不能推广到全部复初值。

#### 命题 8.5：复零点没有自动的能谱含义

若 $H=H^\dagger$，$H\psi=\lambda\psi$ 且 $\psi\ne0$， 则 $\lambda\in\mathbb R$。

**证明。**

$\lambda=\langle\psi,H\psi\rangle/\left\|\psi\right\|^2$， 而 Hermitian 算子的该二次型为实数。

$\square$

因此把上述非实根直接命名为能量本征值是不成立的。 若要建立复共振解释，需要另给开放系统或非自伴有效算符、 边界条件、量纲标定和可观测响应； 若要以实函数 $E(z_n)$ 编码能量，也须解释为何选择该函数。 求根与谱建模是两个独立的理论步骤。

<a id="section-9"></a>

## 9　计算注意力：保留可证明的桥梁

Transformer 的 scaled dot-product attention 为

$$
A(Q,K)=\operatorname{softmax}\!\left(\frac{QK^\top}{\sqrt{d_k}}\right),
 \qquad Y=A(Q,K)V .
$$

softmax 按行作用。原论文将其输出定义为 value 向量的加权和； 输出词元概率还需要后续的线性映射与 softmax， 多头机制也并不要求一次只保留一个方向[\[5\]](#ref-vaswani)。

#### 命题 9.1：加权读取的凸性与非投影性

对固定有限实 $Q,K$，每行权重 $a_j>0$ 且 $\sum_j a_j=1$， 故一行输出为 $\sum_j a_jv_j$。 该输出不必等于任何一个输入 $v_j$， 注意矩阵即使为方阵，也一般不满足 $A^2=A$。

**证明。**

softmax 权重为 $a_j=e^{\ell_j}/\sum_k e^{\ell_k}$， 直接给出正性及归一化。 对标量 value $v_1=0,v_2=2$ 和相等 logits， 输出为 $1$，不同于两个输入。 再取 $1/2<p<1$，

$$
A=\begin{pmatrix}p&1-p\\1-p&p\end{pmatrix}.
$$

它可由 logits $\begin{psmallmatrix}u&0\\0&u\end{psmallmatrix}$ 产生，其中 $u=\log[p/(1-p)]$。 其特征值为 $1$ 与 $2p-1\in(0,1)$， 所以 $A^2\ne A$。 该 logits 矩阵可取 $Q=\sqrt{d_k}\,\mathrm{diag}(u,u)$、 $K=I_2$、$d_k=2$ 实现。

$\square$

几何上还应保留范数： $q\cdot k=\left\|q\right\|\,\left\|k\right\|\cos\theta$。 没有归一化时，点积不只是夹角余弦； 缩放 $1/\sqrt{d_k}$ 也不等于对每个向量作单位化。 另一方面，余弦函数 $x\mapsto\cos x$ 本身不满足幂等性， 因此也不能仅因其输出是投影坐标，就把它当作线性投影算子。

#### 定理 9.2：注意加权和的对角寄存器表示

固定一行权重 $a_j$ 与实 value 坐标 $V_{j\ell}$，定义

$$
\rho_a=\sum_j a_j|j\rangle\langle j|,\qquad
 D_\ell=\sum_j V_{j\ell}|j\rangle\langle j| .
$$

则输出坐标为

$$
Y_\ell=\operatorname{tr}(\rho_aD_\ell).
$$

**证明。**

两个算子在同一正交基中对角，矩阵乘法及求迹得到 $\sum_j a_jV_{j\ell}$，即所求。

$\square$

这个桥梁精确保留了“按查询改变读取权重”的结构。 它只使用对角概率，不需要量子相干； 也没有证明 Transformer 注意与物理测量具有相同的状态空间、 组成律、更新律或实验预测。跨领域同构若要成立， 必须明确映射的对象与它保持的结构，不能只依靠两边都出现内积。

<a id="section-10"></a>

## 10　把注意策略、概念与历史同时内生

### 10.1　有限策略的整体实现

#### 定理 10.1：记录驱动控制的内部闭合

给定有限程序集、仪器 $\{\mathcal I_b^{(c)}\}$ 及更新函数 $f(c,b)$。对经典控制相关态 $\xi=\sum_c|c\rangle\langle c|\otimes\rho_c$，定义

$$
\mathfrak T(\xi)=
 \sum_{c,b}|f(c,b)\rangle\langle f(c,b)|
 \otimes\mathcal I_b^{(c)}(\rho_c).
$$

该更新是保迹完全正映射，并可在保留旧程序及结果历史的内部 幺正扩张中实现。

**证明。**

抽取控制对角块、应用 CP 仪器、制备新程序并求和， 都是 CP 操作；总迹为 $\sum_c\sum_b\operatorname{tr}\mathcal I_b^{(c)}(\rho_c) =\sum_c\operatorname{tr}\rho_c=1$。 对可逆实现，先用定理 2.2 记录 $b$， 再将

$$
|c\rangle|b\rangle|0\rangle\longmapsto
 |c\rangle|b\rangle|f(c,b)\rangle
$$

扩张为幺正。保留的旧数据使不同输入仍正交， 所以即使 $f$ 非单射也没有可逆性矛盾。 不读取旧数据时得到所示约化通道。

$\square$

有限网格的余弦反馈、有限步样本均值估计和结果依赖的测量选择， 都可在足够大的有限内部寄存器上编排为这一形式。 这是一族逐个有限协议的实现定理； 无限精度、无限次测量或无限样本极限不等于一个固定有限装置的免费能力。 只跟踪系统 $S$ 的边缘一般也不足以闭合预测， 因为下一步设置可能由与 $S$ 相关的控制和历史决定。

#### 定理 10.2：适应性历史的概率一致性

给定有限历史 $h$ 所选择的完备仪器 $\{\mathcal J_{b|h}\}_b$。 从 $\rho_\varnothing=\rho$ 递归定义子归一化态 $\rho_{hb}=\mathcal J_{b|h}(\rho_h)$， $p_h=\operatorname{tr}\rho_h$。则

$$
p_h\ge0,\qquad \sum_b p_{hb}=p_h.
$$

仅当 $p_h>0$ 时，条件态 $\rho_h/p_h$ 与条件概率 $p_{hb}/p_h$ 有定义。任意有限深度的该历史树可用内部仪器扩张实现。

**证明。**

CP 性保正性，完备性给出迹的前缀一致性。 归一化结论由定义直接得到。 对每个节点取有限等距扩张，并按已保留的正交历史记录控制后续扩张； 逐层组合得到整体内部的幺正实现。

$\square$

这保留了“观察者自己的过去改变下一次注意设置”的实质。 然而历史概率的一致性不额外证明一个全局唯一结果如何本体地产生； 本模型使用 A2 的操作概率及 A4 的条件记录语义。 项目关于适应性子仪器、完整输出标签和参考归一化的接口纪律 与这一写法相容[\[8\]](#ref-repofiber), [\[9\]](#ref-repov60), [\[11\]](#ref-repooutputs)。

### 10.2　概念稳定性与可见关系

#### 定义 10.3：注意菜单下的响应等价

设 $\mathcal A$ 为允许的有限适应性协议及其末端读出菜单， 每个输出历史 $h$ 对应效应 $G_h$。 被比较的 $\rho,\sigma$ 位于同一个完整输入端口： 未固定的程序、参考和记忆初态必须包括在内， 不能在它们与 $S$ 相关时只保留 $S$ 的边缘。 定义

$$
\rho\sim_{\mathcal A}\sigma
 \quad\Longleftrightarrow\quad
 \operatorname{tr}(\rho G_h)=\operatorname{tr}(\sigma G_h)
 \ \text{对所有允许的 }h.
$$

其等价类称为该注意合同下的响应纤维。 这一定义关乎可区分性，未把任一等价类直接等同于客观基本粒子。

#### 定理 10.4：注意菜单扩大只能细化响应纤维

若 $\mathcal A\subseteq\mathcal B$，则 $\rho\sim_{\mathcal B}\sigma\Rightarrow \rho\sim_{\mathcal A}\sigma$。 所以每个 $\mathcal B$ 纤维包含于一个 $\mathcal A$ 纤维。

**证明。**

对较大菜单全部效应相等，必然对其子菜单的全部效应相等。

$\square$

这描述了“注意到更多关系”怎样改变描述分辨率。 它与实际实施一个会扰动系统的仪器是两个步骤： 菜单变化本身是一项可访问性约定，实施协议才产生具体联合演化。 来自内部程序的选择可以使这两步在同一整体模型中相联， 但不能省略其区别。

#### 定理 10.5：概念确定不要求概念秩一

以投影 $P$ 表示某个二元概念判断。则

$$
\operatorname{tr}(\rho P)=1
 \quad\Longleftrightarrow\quad
 \operatorname{supp}\rho\subseteq\operatorname{ran}P.
$$

给定完备 Kraus 族 $\{K_b\}$， 对每个支撑于 $P$ 的初态都无分支泄漏到 $Q=I-P$， 当且仅当

$$
QK_bP=0\quad\text{对每个 }b.
$$

**证明。**

$\operatorname{tr}(\rho P)=1$ 等价于 $\operatorname{tr}(\rho Q)=\left\|Q\rho^{1/2}\right\|_{\rm HS}^2=0$， 也就等价于支撑包含。 若 $QK_bP=0$，任意支撑于 $P$ 的态在每个分支后仍支撑于 $P$。 反过来，对每个 $v\in\operatorname{ran}P$， 分支泄漏范数为 $\left\|QK_bv\right\|^2$； 若它总为零，则 $QK_bP=0$。

$\square$

当 $\operatorname{rank}P>1$ 时，$P$ 内可有不同方向、相对相位及干涉读出， 同时概念判断始终为真。 这与上一节的芝诺子空间例子形成同一结构： 一个稳定可重复的标签，并不排除该标签所覆盖的内部关系继续变化。 因此可以把“概念粒子性”限定为 *某些读出下的稳定标签* ， 把“概念波动性”限定为 *需要额外比较菜单才能显现的关系* 。 对真实语言概念，仍须经验地确定状态空间、程序与观测量； 语义标签本身不会自动提供量子模型。

<a id="section-11"></a>

## 11　理论地位、可检验内容及下一步问题

### 11.1　本轮得到的统一命题

本轮的统一对象包含对象、参考、控制、记录、可访问菜单及反馈。 观察轴可以是该整体某个 qubit 接口的一部分； 其余自由度负责设置如何产生、读数如何保存、统计如何估计、 下一次操作如何选择。 因此“何时粒子、何时波”必须先指定所问的量： 是某个结果的确定性、哪径可辨识度、相位扫描可见度、 还是稳定概念标签。把这些问题分型后，才能形成可证伪的理论。

| 问题 | 本文的形式对象 | 可证明的结果 |
|:---|:---|:---|
| 怎样把观察者放进去 | 内部控制、参考、记忆与仪器 | 有限协议有保持历史的幺正扩张 |
| 何时可得路径信息 | 标记态与允许读口 | $D^2+V^2=1$ 的纯标记情形及访问限制 |
| 不看是否恢复干涉 | 记录上的非选择保迹操作 | 系统边缘保持，不自动恢复 |
| 越测是否完全不变 | 固定或移动投影协议 | 固定子空间有 $PHP$ 动力学；移动投影可输运 |
| 余弦自指怎样收敛 | 明确的反馈政策与校准 | 实根唯一吸引；单次结果反馈不收敛于该根 |
| 复根是否稳定模态 | 复延拓的直接迭代 | 全部非实根严格排斥；能谱解释仍需建模 |
| 概念确定是否穷尽状态 | 稳定投影标签与响应纤维 | 高秩标签可保持确定，同时内部关系仍变化 |

### 11.2　三个直接可复核的协议

**协议一：改变标记读口。**

制备定理 4.4 的联合态； 固定系统读出，在标记的 $X$ 与 $Z$ 读口之间改变控制。 检查路径关联、条件正反条纹以及不分类总分布。 本理论预言读口改变关联的呈现方式； 它不预言人的主观注视单独改变相同物理协议的边缘统计。

**协议二：区分三种余弦反馈。**

用同一弧度校准比较精确计算反馈、单次测量反馈和样本均值反馈。 第一种收敛于 $\pm\alpha$，第二种持续取 $\pm1$， 第三种的噪声由定理 7.3 控制。 改变增益后再测定吸引点，可以检验其政策依赖性。 这些是给定装置模型的预言，不是超出标准量子操作模型的新实验定律。

**协议三：固定与移动测量设置。**

比较固定 $P$、高秩 $P$ 和缓慢移动的 $P_k$。 分别检查泄漏抑制、子空间内部振荡和状态输运。 理论预言它们可在相同“频繁测量”概括下呈现不同动力学， 所以注意的方向、频率、强度和结果策略必须独立记录。

### 11.3　仍然需要独立完成的理论任务

若希望把该候选理论提升为新的基础物理，需要补充： 为何采用当前状态空间及 Born 读出；内部参考和仪器如何由更基本动力学形成； 哪些可测量量迫使余弦政策采用单位增益； 是否存在区别于现有操作量子理论且通过实验检验的预测。 若希望建立认知理论，则须另给概念编码、行为任务、 注意操作与经验数据之间的桥接假设。 若希望把复根作为谱，则须给出具体算符问题及其物理读出。 这些任务没有被“内积”“正交”或“自指”几个词自动完成。

可以保留的核心表述是：

> 观察者属于整体；其可实施的控制、可保存的记录与可访问的比较， 共同决定哪些稳定标签以及哪些关系进入它的经验。 当这些控制由先前记录更新时，观察本身成为整体内部的反馈过程。

这里“共同决定”指模型中的概率和可区分结构， 并不把本体存在归结为人的主观注意。

### 11.4　证明依赖与理论范围

仪器扩张与内部策略依赖 A1–A4； Bloch 概率、标记互补与擦除依赖所给 Hilbert/Born 表示； 芝诺部分另依赖 A5 的 Hamiltonian 及指定投影协议； 实、复不动点定理只依赖明确的反馈函数和实／复分析； 样本反馈再用指定制备、条件独立性与 Born 分布； 概念稳定与响应纤维结论依赖已给读出和可访问菜单。 因此余弦定理并没有逆向证明前述量子公理。

本文的“完整”指候选假设、类型、命题、证明及限制在当前有限模型内闭合。 这不表示基础物理、测量本体问题或认知科学已经被完结。 文中的自包含证明可以独立检查；本文没有声称各标准命题的历史首创权， 也没有声称完成了新的 Lean 形式化。

<a id="section-A"></a>

## A　固定来源与有界审计

仓库为 [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing)。 本轮 API 查询的默认分支是 `dev`，固定提交为

`6ca7b7300b84a13660977b193b024ca63d92ab06`

提交时刻：2026-11-07 19:32:58 UTC，即新加坡时间 2026-11-08 03:32:58。 查询时刻：2026-11-07 19:37:52.681 UTC，即新加坡时间 2026-11-08 03:37:52.681。 以下远程文件均在该提交重新取得；旧索引只作导航。

### A.1　实际阅读范围

理论目录 Contents 接口返回 1000 条，故不声称目录穷尽；ConceptDynamics 与 Quantum 的当前索引分别返回 159、83 条。本轮只检索所选文件并读取以下段落。行号对应固定原文件，不能代替声明及其前提。

- **v66[\[7\]](#ref-repov66)** 151–250、333–414、555–641、805–857、1229–1274、1432–1475 行：内部控制、测量仪器、环境重叠、条件选支及公理依赖。

- **静态相融纤维[\[8\]](#ref-repofiber)** 1–25、127–145、198–250、289–320、4860–4875 行：响应商、输出记录、适应性仪器与相位访问范围。

- **v60[\[9\]](#ref-repov60)** 84–103、277–310 行：完整观察者、有限接口与包含失败标签的归一化。

- **内生三轴[\[10\]](#ref-repoaxes)** 1–32、246–273、467–488、679–690 行：操作菜单、面积信息边界、Bloch 关系块及条件性三维接口。

- **输出分辨闭包[\[11\]](#ref-repooutputs)** 1–36、2365–2410、2646–2820 行：开放输入等级、平均核与完整输出历史的差别。

三份 Lean 源全文已读：`EnvironmentRecords.lean`（75 行）、`ObserverAlgebra.lean`（57 行）、`ObserverCommutator.lean`（25 行）[\[12\]](#ref-repolean)。 它们分别给出指定 Gram 条件下的记录退相干、已给置换更新的协变性及交换子公式。本轮没有运行 Lean 构建、内核复核或完整依赖审计；源码中的证明项不等于本文所有物理解释已获形式验证。

<a id="section-B"></a>

## B　原文范围、符号与复现

### B.1　论文审读边界

Misra–Sudarshan 原扫描第 758 页的理想测量与极限假设已读；Itano 等第 2296 页经图像及 OCR 核对，第 2299 页经 OCR 核读；Facchi–Pascazio 作者稿第 3 节的有限维证明已读[\[2\]](#ref-misra), [\[3\]](#ref-itano), [\[4\]](#ref-facchi)。 Vaswani 等第 3.2–3.4 节及 Bergweiler 第 3.1 节已读[\[5\]](#ref-vaswani), [\[6\]](#ref-bergweiler)。 Englert 的官方书目与摘要已核对，正文第 2154–2156 页采用公开第三方转录审读；出版商正文访问未成功，未声称完成原版逐页校勘[\[1\]](#ref-englert)。 这些是指定范围审读，不是全文或全部引文链审计。

### B.2　关键类型与复现约定

$\rho$ 表示约化密度算子，$\mathcal I_a$ 表示未归一结果分支，$h$ 表示已得记录；条件态只在分支概率严格正时定义。 $\mathcal E=\sum_a\mathcal I_a$ 是非选择通道，不能与某一条件分支互换。 路径可辨识度 $D$ 必须注明允许访问的量子系统及优化测量集合；固定读口实际提供的信息可以更少。 例如 v66 的正交探针 $|+\rangle,|-\rangle$ 在计算基读口给相同分布，但其完整量子可辨识度为一。 $x$ 是所声明控制模型的无量纲弧度变量；$\cos x=\pm x$ 的根及乘子不自行携带能量、质量或手性单位。

> Markdown 转换说明：下段保留原稿的 XeLaTeX 排版复现约定；当前交付文件为纯 Markdown。

交付主稿为单一 UTF-8 `.tex` 文件，使用 XeLaTeX；中文采用 Noto CJK，西文采用 TeX Gyre，等宽文字采用 DejaVu 字体族。 安装相应字体及主稿声明的宏包后，连续运行两次 `xelatex -halt-on-error` 处理同一主稿，以解析目录、交叉引用及页码。 参考文献直接使用 `thebibliography`，无需另取 `.bib` 文件。 重编译只复现排版；提交固定、正文证明和实验检验仍是不同的复现层次。

## 参考来源

<a id="ref-englert"></a>

\[1\] B.-G. Englert. Fringe Visibility and Which-Way Information: An Inequality.  *Physical Review Letters*  **77**, 2154–2157 (1996). [DOI](https://doi.org/10.1103/PhysRevLett.77.2154)； [本轮正文转录来源](https://es.scribd.com/document/463351298/englert1996)。

<a id="ref-misra"></a>

\[2\] B. Misra and E. C. G. Sudarshan. The Zeno’s paradox in quantum theory.  *Journal of Mathematical Physics*  **18**, 756–763 (1977). [DOI](https://doi.org/10.1063/1.523304)； [作者扫描稿](https://web2.ph.utexas.edu/~gsudama/pub/1977_005.pdf)。

<a id="ref-itano"></a>

\[3\] W. M. Itano, D. J. Heinzen, J. J. Bollinger, and D. J. Wineland. Quantum Zeno effect.  *Physical Review A*  **41**, 2295–2300 (1990). [DOI](https://doi.org/10.1103/PhysRevA.41.2295)； [NIST 原文](https://tf.nist.gov/general/pdf/858.pdf)。

<a id="ref-facchi"></a>

\[4\] P. Facchi and S. Pascazio. Quantum Zeno dynamics: mathematical and physical aspects.  *Journal of Physics A: Mathematical and Theoretical*  **41**, 493001 (2008). [DOI](https://doi.org/10.1088/1751-8113/41/49/493001)； [作者稿（2009 年上传）](https://arxiv.org/abs/0903.3297)。

<a id="ref-vaswani"></a>

\[5\] A. Vaswani et al. Attention Is All You Need.  *Advances in Neural Information Processing Systems*  **30** (2017). [作者全文与式 (1)](https://arxiv.org/html/1706.03762v7)。

<a id="ref-bergweiler"></a>

\[6\] W. Bergweiler. Iteration of meromorphic functions.  *Bulletin of the American Mathematical Society (N.S.)*  **29**(2), 151–188 (1993). [DOI](https://doi.org/10.1090/S0273-0979-1993-00432-4)； [作者稿，第 3.1 节](https://arxiv.org/pdf/math/9310226)。

<a id="ref-repov66"></a>

\[7\] 项目理论输入：AURIC v66，同一本体中的测量、退相干与经典记录。 [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/6ca7b7300b84a13660977b193b024ca63d92ab06/docs/develop/theory/AURIC_MEASUREMENT_DECOHERENCE_AND_CLASSICAL_RECORDS_IN_ONE_ONTIC_STATE_V66.md)。

<a id="ref-repofiber"></a>

\[8\] 项目理论输入：AURIC $\Omega$ 静态相融纤维理论。 [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/6ca7b7300b84a13660977b193b024ca63d92ab06/docs/develop/theory/AURIC_OMEGA_STATIC_COMPATIBILITY_FIBER_THEORY.md)。

<a id="ref-repov60"></a>

\[9\] 项目理论输入：AURIC v60，参考归一化、完全正更新与内生历史闭包。 [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/6ca7b7300b84a13660977b193b024ca63d92ab06/docs/develop/theory/AURIC_REFERENCE_NORMALIZATION_COMPLETELY_POSITIVE_UPDATES_AND_ENDOGENOUS_HISTORY_CLOSURE_V60.md)。

<a id="ref-repoaxes"></a>

\[10\] 项目理论输入：FIB-ATOM，观察者内生的三轴几何与预测接口。 [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/6ca7b7300b84a13660977b193b024ca63d92ab06/docs/develop/theory/AURIC_FIB_OBSERVER_INTERNAL_THREE_AXIS_GEOMETRY_AND_PREDICTIVE_INTERFACE.md)。

<a id="ref-repooutputs"></a>

\[11\] 项目开放参考输入：FIB-ATOM，输出分辨的 instrument 闭包。 [固定提交原文](https://github.com/the-omega-institute/trureturing/blob/6ca7b7300b84a13660977b193b024ca63d92ab06/docs/develop/theory/AURIC_FIB_ATOM_OUTPUT_RESOLVED_INSTRUMENT_CLOSURE.md)；本文不提升其证明等级。

<a id="ref-repolean"></a>

\[12\] 项目 Lean 源，固定提交同附录A： [EnvironmentRecords](https://github.com/the-omega-institute/trureturing/blob/6ca7b7300b84a13660977b193b024ca63d92ab06/D5/S3/Quantum/EnvironmentRecords.lean)； [ObserverAlgebra](https://github.com/the-omega-institute/trureturing/blob/6ca7b7300b84a13660977b193b024ca63d92ab06/D5/S3/Quantum/ObserverAlgebra.lean)； [ObserverCommutator](https://github.com/the-omega-institute/trureturing/blob/6ca7b7300b84a13660977b193b024ca63d92ab06/D5/S3/Quantum/ObserverCommutator.lean)。 本轮全文阅读，未执行构建。
