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
## 12. 有限方向参考的完整输出复用窗

<a id="otf004-finite-direction-reuse-model"></a>

**定义 12.1（相干方向程序与固定仪器）。** 令 $j\in\frac12\mathbb Z_{>0}$，$d=2j+1$，取参考空间 $R=\operatorname{Sym}^{2j}(\mathbb C^2)$ 及每次输入空间 $S=\mathbb C^2$。对 $n\in S^2$，记 $|n,+\rangle$ 为 $n\cdot\sigma$ 的正本征单位向量，定义

$$
|j,n\rangle=|n,+\rangle^{\otimes 2j},\qquad
\tau_n=|j,n\rangle\langle j,n|,\qquad
P_{n,b}=\frac{I+b\,n\cdot\sigma}{2}\quad(b=\pm).
$$

向量的整体相位不影响上述态。$\sigma=(\sigma_x,\sigma_y,\sigma_z)$ 为 Pauli 矩阵，$J=(J_x,J_y,J_z)$ 为 $R$ 上的无量纲自旋 $j$ 生成元。令 $\Pi_\pm$ 为 $R\otimes S$ 的总自旋 $j\pm\frac12$ 子空间的正交投影。每一槽使用同一仪器

$$
\mathcal A(X)=\sum_{b=\pm}\Pi_bX\Pi_b\otimes|b\rangle\langle b|_H.
\tag{12.1}
$$

其输出保留 $R,S$ 及具有固定正负标签的经典记录 $H$。比较仪器为

$$
\mathcal B_n(X)=
\sum_{b=\pm}(I_R\otimes P_{n,b})X(I_R\otimes P_{n,b})
\otimes|b\rangle\langle b|_H.
\tag{12.2}
$$

这里明确采用有限复 Hilbert 张量复合、密度算子、Born 规则及完全正仪器语义。$R$ 的表示、$\tau_n$ 的准备以及 (12.1) 的耦合是指定模型输入。自旋相干程序的对称张量表示复用 OTF002 定义 11.1；(12.1) 是 Bartlett–Rudolph–Spekkens–Turner 的方向参考模型中的总角动量 Lüders 仪器，参见其第 III 节及附录 B，式 (39)–(41)，[作者全文](https://arxiv.org/html/quant-ph/0602069v2)，[DOI](https://doi.org/10.1088/1367-2630/8/4/058)。

<a id="otf004-finite-direction-reuse-contract"></a>

**假设 12.2（因果控制器及完整比较口）。** 对每个正整数 $N$，允许任意有限维确定性因果网络 $T$，以 $N$ 个有序槽调用 (12.1)。全部非参考初始数据的联合态记为 $\rho_T$，可包含输入 qubit 间及它们与控制器记忆、任意有限维旁观者间的纠缠。初态为

$$
\tau_n\otimes\rho_T.
\tag{12.3}
$$

$\rho_T$ 和全部控制器操作均不依赖实际的 $n$；同一 $T$ 必须对所有 $n$ 定义。控制器操作在 $R$ 上为恒等，只有指定的 $N$ 次仪器调用接触 $R$，不直接读取、控制或重置参考，也不补入携带实际未知 $n$ 的资源。允许对先前量子输出和已得经典结果作任意因果处理及反馈。这里不另要求控制器协变；其准备可使用固定已知坐标，唯独不能依赖实际未知方向。每次仪器的原始正负记录均完整保留，不按结果后选择，不删去零概率以外的分支，不将条件态重新归一后替代全态。

$h=(b_1,\ldots,b_N)$ 为全部仪器记录；$K$ 包含最终保留的所有量子输出、控制器记忆、旁观者及其余保留寄存器，包括控制器自身保留的经典记录。控制器可处理先前输出，但比较口覆盖其最终保留的全部寄存器。在实际实验及理想实验中使用相同的 $\rho_T$ 和控制器，仅将每一槽的 $\mathcal A$ 换成 $\mathcal B_n$。分别记最终态为 $\omega^a_{n,T}$（在 $RKh$ 上）和 $\omega^i_{n,T}$（理想实验的 $Kh$ 边缘态）。理想实验的完整态恰为

$$
I_{n,T}=\tau_n\otimes\omega^i_{n,T}.
\tag{12.4}
$$

以 $D(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$ 定义

$$
E_j(N)=\sup_{n\in S^2,\,T}
D\!\left(\omega^a_{n,T},\,\tau_n\otimes\omega^i_{n,T}\right).
\tag{12.5}
$$

上确界包括任意有限旁观者维数。它同时比较原来未变且与其余输出解耦的参考、全部保留量子输出和完整经典历史，不只比较各自边缘态。每个有限 $N$ 可以使用自己的有限记忆空间；不假设一个固定有限记忆保存无穷历史。对 $0<\delta<\frac14$，当正整数集合 $\{N:E_j(N)\le\delta\}$ 非空且有限时，定义其最大元为 $L_\delta(j)$。

上述控制语义采用本卷定义 2.1、10.3 及定理 10.1–10.2 的有限完整输入、记录和因果闭包范围；本假设另外规定参考的访问限制及初始乘积。OTF003 第 11 节的实际菜单条件和 OTF007 第 9 节的记录容量条件仍分别约束模型的实际供应与有限记忆，均不由符号 $T$ 自动支付。

<a id="otf004-finite-direction-reuse-theorem"></a>

**定理 12.3（全历史、参考返回与解耦的定量复用窗；repo-derived）。** 在定义 12.1 和假设 12.2 下，对每个允许的 $j$ 和每个整数 $N\ge2$，

$$
\frac{1-\sqrt{\,1-\cos^{4j}\!\left(\frac{\pi}{2N}\right)}}{2}
\ \le\ E_j(N)\
\le\ \min\!\left\{1,\ N\sqrt{\frac{2}{2j+1}}\right\}.
\tag{12.6}
$$

右侧上界也对 $N=1$ 成立。固定 $0<\delta<\frac14$，用自然对数定义

$$
q_\delta=4\delta(1-\delta),\qquad
a_\delta(j)=\left\lfloor\delta\sqrt{\frac{2j+1}{2}}\right\rfloor,\qquad
C_\delta=\frac{\pi}{\sqrt{\log(1/q_\delta)}}.
\tag{12.7}
$$

只要 $a_\delta(j)\ge1$，正使用窗 $L_\delta(j)$ 就存在，且

$$
\begin{aligned}
a_\delta(j)\le L_\delta(j)
&\le
\max\!\left\{1,\
\left\lfloor\frac{\pi}
{2\arccos(q_\delta^{1/(4j)})}\right\rfloor\right\}\\
&\le\max\!\left\{1,\left\lfloor C_\delta\sqrt j\right\rfloor\right\}.
\end{aligned}
\tag{12.8}
$$

特别地，对所有半整数 $j\ge4/\delta^2$，

$$
\frac{\delta}{2}\sqrt j
\le L_\delta(j)
\le\max\{1,C_\delta\}\sqrt j.
\tag{12.9}
$$

故在固定 $\delta$ 下，沿允许自旋有 $L_\delta(j)=\Theta_\delta(\sqrt j)$。这里不假设 $E_j(N)$ 对 $N$ 单调；小 $j$ 的正可行集合允许为空。

**证明。** 先给出保留参考与量子输出的单槽估计，再沿理想前缀比较完整网络，最后用同一合法输入区分两个理想方向以约束复用窗。

总自旋分解给出以下标准角动量恒等式。令 $Q=J\cdot\sigma$，则 $Q$ 在两个总自旋子空间上的本征值分别为 $j$ 和 $-(j+1)$，因而

$$
\Pi_+=\frac{Q+(j+1)I}{d},\qquad
\Pi_-=\frac{jI-Q}{d}.
\tag{12.10}
$$

这是上述 Bartlett 等人模型的既有投影系数（literature-attested），在此仅作为新比较关系的中间计算。取 $n=z$，写

$$
e=|j,j\rangle,\qquad f=|j,j-1\rangle,\qquad
a=e\otimes|\downarrow\rangle,\qquad
c=f\otimes|\uparrow\rangle.
$$

由 $J_ze=je$、$J_+e=0$、$J_-e=\sqrt{2j}\,f$ 代入 (12.10)，得到

$$
\begin{aligned}
\Pi_+(e\otimes|\uparrow\rangle)&=e\otimes|\uparrow\rangle,
&
\Pi_-(e\otimes|\uparrow\rangle)&=0,\\
\Pi_+a&=\frac{a+\sqrt{d-1}\,c}{d},
&
\Pi_-a&=\frac{(d-1)a-\sqrt{d-1}\,c}{d}.
\end{aligned}
\tag{12.11}
$$

在相同的相干指针空间 $H$ 中引入两个等距映射

$$
V\psi=\sum_{b=\pm}\Pi_b(e\otimes\psi)\otimes|b\rangle_H,\qquad
W\psi=\sum_{b=\pm}e\otimes P_{z,b}\psi\otimes|b\rangle_H.
\tag{12.12}
$$

对 $H$ 在标签基中退相干，分别得到 (12.1)、(12.2) 在初始参考 $\tau_z$ 上的经典记录仪器，仍保留 $R,S$。由 (12.11)，

$$
(V-W)|\uparrow\rangle=0,\qquad
(V-W)|\downarrow\rangle
=\frac{a+\sqrt{d-1}\,c}{d}
 \otimes(|+\rangle-|-\rangle).
$$

$a,c$ 正交归一，所以

$$
(V-W)^\dagger(V-W)=\frac2d|\downarrow\rangle\langle\downarrow|,
\qquad
\|V-W\|=\sqrt{\frac2d}.
\tag{12.13}
$$

任意旁观者空间 $F$ 上仍有 $\|(V-W)\otimes I_F\|=\sqrt{2/d}$。对任意 $SF$ 联合输入取纯化；两个纯输出的迹距离满足

$$
D(|v\rangle\langle v|,|w\rangle\langle w|)
=\sqrt{1-|\langle v,w\rangle|^2}
\le\|v-w\|.
$$

再对纯化辅助空间取偏迹并对指针退相干，得到完整 $R,S,H,F$ 输出的单槽误差不超过 $\sqrt{2/d}$。这里使用迹距离在确定性完全正保迹映射下的标准收缩性：由
$D(\rho,\sigma)=\max_{0\le G\le I}\operatorname{Tr}[G(\rho-\sigma)]$，
以及这类映射的伴随将效果送到效果，即得该收缩性。总自旋仪器在同时旋转下协变，$\tau_n$ 及 $P_{n,b}$ 也由相同旋转得到，故单槽估计对全部 $n$ 及任意 $SF$ 输入一致成立。此结论只要求该槽输入参考为独立的 $\tau_n$，没有把它推广到已受扰动的任意参考态。

固定 $n,T$，令 $\eta_k$ 为前 $k$ 槽理想、后 $N-k$ 槽实际的数学比较网络的最终完整态，$0\le k\le N$。比较 $\eta_{k-1}$ 和 $\eta_k$ 时，第 $k$ 槽之前有共同的全理想前缀。理想槽和控制器都不作用于参考，故这个前缀的完整态为 $\tau_n\otimes\xi$。$\xi$ 可与待输入 qubit、既往记录、记忆及旁观者任意纠缠，也可经先前理想结果依赖 $n$；单槽估计对这样的 $\xi$ 仍一致成立。第 $k$ 槽后的共同实际后缀，包括全部依记录控制的操作，是全寄存器上的一个完全正保迹映射，因此

$$
D(\eta_{k-1},\eta_k)\le\sqrt{\frac2d}.
$$

三角不等式给

$$
D(\omega^a_{n,T},\tau_n\otimes\omega^i_{n,T})
=D(\eta_0,\eta_N)\le N\sqrt{\frac2d}.
\tag{12.14}
$$

这个比较仅使用数学上的理想前缀，没有在实际实验中重置参考。它比较未后选择的全态；旁观者和全部历史均已包含。取上确界并用 $D\le1$，得到 (12.6) 的上界。这一步复用标准混合网络估计；OTF006 第 4.2 节使用的迹距离比较属于同类中间工具，并非这里另立的新理论。

为证下界，固定 $N\ge2$，令

$$
\theta=\frac{\pi}{N},\qquad
n_0=z,\qquad n_1=(\sin\theta,0,\cos\theta),\qquad
U=e^{-i\theta\sigma_y/2}.
$$

取 $u_\pm=(|0\rangle\pm i|1\rangle)/\sqrt2$，用一个辅助 qubit $A$ 准备

$$
|\Psi_N\rangle=
\frac{u_+^{\otimes N}\otimes|0\rangle_A
      +u_-^{\otimes N}\otimes|1\rangle_A}{\sqrt2}.
\tag{12.15}
$$

这是 Puchała、Pawela、Krawiec、Kukulski、Oszmaniec 的多次标记投影测量区分中两端本征向量构造的特例（literature-attested），见[第 3.1 节及附录 A 式 (39)–(40)](https://arxiv.org/html/1810.05122v4)。以下直接计算所需特例，不使用其最优性结论。

使用同一个非自适应 $T_N$，依次送入这 $N$ 个 qubit，保留每个量子输出、$A$ 和全部标签，从不直接作用于 $R$。准备及接线只依赖已选的两个候选方向和 $N$，不依赖究竟哪个方向是实际的 $n$；它没有第二份实际未知方向资源，因此属于假设 12.2 的网络。

以 $0,1$ 分别编码固定标签 $+,-$。对每个 $h\in\{0,1\}^N$，两个理想实验的未归一化条件辅助向量为

$$
v_h^0=(\langle h|\otimes I_A)|\Psi_N\rangle,\qquad
v_h^1=(\langle h|U^{\dagger\otimes N}\otimes I_A)|\Psi_N\rangle.
\tag{12.16}
$$

由于 $Uu_\pm=e^{\mp i\theta/2}u_\pm$，且
$|\langle h|u_\pm^{\otimes N}\rangle|^2=2^{-N}$，

$$
\|v_h^0\|^2=\|v_h^1\|^2=2^{-N},\qquad
\langle v_h^0,v_h^1\rangle
=2^{-N}\cos\!\left(\frac{N\theta}{2}\right)=0.
\tag{12.17}
$$

因此两种理想输出的 $Ah$ 边缘态
$\sum_h|v_h^r\rangle\langle v_h^r|\otimes|h\rangle\langle h|$
（$r=0,1$）具有正交支撑，迹距离为一。每个标签的完整概率均为 $2^{-N}$，没有选取特定分支。由偏迹收缩性，两种完整理想输出也满足

$$
D(I_{n_0,T_N},I_{n_1,T_N})=1.
\tag{12.18}
$$

上述文献的经典输出测量通道在这里准确对应于理想仪器的 $Ah$ 边缘态；只把其可达输入用于本问题，不把经典输出的最优区分范数或自适应最优性移植到保留量子输出的仪器。

在实际实验中，固定 $T_N$ 和 (12.15) 后，全部仪器与控制器给出同一个与 $n$ 无关的完全正保迹映射 $\Lambda:R\to RKh$。因此

$$
D(\omega^a_{n_0,T_N},\omega^a_{n_1,T_N})
\le D(\tau_{n_0},\tau_{n_1}).
\tag{12.19}
$$

复用 OTF001 定理 5.4 的 qubit 半角重叠及 OTF002 定义 11.1 的对称张量程序，有

$$
|\langle j,n_0|j,n_1\rangle|^2
=\left(\cos^2\frac{\theta}{2}\right)^{2j}
=\cos^{4j}\frac{\theta}{2}.
\tag{12.20}
$$

纯态迹距离公式和三角不等式遂给

$$
\begin{aligned}
1
&\le D(I_{n_0,T_N},\omega^a_{n_0,T_N})
 +D(\omega^a_{n_0,T_N},\omega^a_{n_1,T_N})
 +D(\omega^a_{n_1,T_N},I_{n_1,T_N})\\
&\le2E_j(N)+
\sqrt{1-\cos^{4j}\!\left(\frac{\pi}{2N}\right)}.
\end{aligned}
\tag{12.21}
$$

移项即得 (12.6) 下界。两个方向使用的是同一输入、同一网络和同一实际通道；没有拼接分别最优的输入或分支。

最后，由 (12.14)，每个正整数 $N\le a_\delta(j)$ 都可行，故 $a_\delta(j)\ge1$ 保证非空。对任意可行 $N\ge2$，(12.6) 及 $1-2\delta>0$ 给

$$
\cos^{4j}\!\left(\frac{\pi}{2N}\right)\le
1-(1-2\delta)^2=q_\delta.
\tag{12.22}
$$

余弦在 $[0,\pi/2]$ 上递减，所以

$$
N\le B_\delta(j):=
\frac{\pi}{2\arccos(q_\delta^{1/(4j)})}.
\tag{12.23}
$$

该有限上界连同可能的 $N=1$ 说明正可行集合有限，从而 $L_\delta(j)$ 存在，并给出 (12.8) 的第一行。为估计其中的整数上界，注意 $0\le x\le\pi/4$ 时 $\sec^2t\le2$，故

$$
\tan t\le2t,\qquad
-\log\cos x=\int_0^x\tan t\,dt\le x^2.
\tag{12.24}
$$

对整数 $M\ge2$，若 $\cos^{4j}(\pi/(2M))\le q_\delta$，则

$$
\exp\!\left(-\frac{\pi^2j}{M^2}\right)
\le\cos^{4j}\!\left(\frac{\pi}{2M}\right)\le q_\delta,
\qquad M\le C_\delta\sqrt j.
\tag{12.25}
$$

具体取 $m=\lfloor B_\delta(j)\rfloor$。若 $m\ge2$，由 $m\le B_\delta(j)$ 和余弦递减性，$m$ 满足 (12.25) 的前件，所以 $m\le\lfloor C_\delta\sqrt j\rfloor$；若 $m\le1$，外层的 $\max\{1,\cdot\}$ 已覆盖。这证明 (12.8) 最后的不等式，而无需对误差作单调性假设。

当 $j\ge4/\delta^2$ 时，

$$
a_\delta(j)\ge\delta\sqrt j-1\ge\frac{\delta}{2}\sqrt j\ge1.
$$

同时 $j\ge1$，所以
$\max\{1,\lfloor C_\delta\sqrt j\rfloor\}\le\max\{1,C_\delta\}\sqrt j$。
由 (12.8) 即得 (12.9) 及固定 $\delta$ 的 $\Theta_\delta(\sqrt j)$ 结论。$\square$

定理 12.3 的 repo-derived 范围是 (12.5) 所定义完整比较口下，固定总自旋仪器的有限误差界与正复用窗之间的关系；角动量系数、相干程序重叠、迹距离收缩、混合网络方法和多次测量区分构造均为上述已注明的成熟中间步骤。它不声称给出 $E_j(N)$ 的精确最优值或最优前因子。

作为同一结果的适用域，Bartlett 等人第 III 节的 $j^2$ 寿命使用独立的 $I/2$ 探针，丢弃被测自旋，对结果平均后的参考评估下一次单探针成功率；该质量函数不同于 (12.5)。保留测量记录的条件参考动力学也已由 Ahmadi–Jennings–Rudolph 研究，其式 (13) 仍对被测自旋取偏迹，见[第 II.1 节](https://arxiv.org/html/1005.0798v1)，[DOI](https://doi.org/10.1103/PhysRevA.82.032320)。两种合同的寿命指数不作互相替换。保留测后量子态的区分任务须使用完整仪器口；相关单次区别见 Eid–Quintino，[第 V–VI 节](https://arxiv.org/html/2602.12258v2)，这里的证明只沿 (12.16)–(12.18) 的确切边缘映射使用经典输出区分结论。van Luijk–Werner–Wilming 的[定理 5](https://arxiv.org/html/2301.09877v3)，[DOI](https://doi.org/10.22331/q-2023-11-06-1166)，则允许更换为带协变恢复的实现，并控制近酉任务的参考边缘扰动；(12.1)、(12.4) 固定实现及联合解耦的要求保持独立。

模型的数学适用条件仍是本卷 A1–A7、OTF001 的有限复合与仪器语义、OTF002 的自旋程序、OTF003 的实际效果菜单，以及 OTF005、OTF006、OTF007 各自的来源、控制、参考和记忆边界。若从 OMEGAQ020 第 8 节或 AURIC 的条件表示供应这些接口，必须另满足同一实际来源、相关张量准备、完整完全正过程、指定仪器及全部历史的条件；中央响应卷定义 52.1–52.2 的七项消费者条件不被本定理免除。特别是相干程序准备、指定总自旋耦合和任意允许联合输入的可取得性均是模型前提。$N$ 只计仪器槽数；由 (12.6)–(12.9) 不推出物理秒数、能量、时钟、无限历史实现或新的经验性结论。

## 追加锚（本行以下为增补区）
## 13. 同一运行的混合参考获取与实际返回

**本批导航。** 本批在原有 §12 之后固定一个原始场任务，并给出同一运行中的有限获取、解码、实际终端输出与约化完全正控制器的统一证书。§13 给出原始槽接口、全部记录与资源以及构造的完整证明；§14 分离实际等距输出类和一般约化 CPTP 类，并给出后者的全球必要下界；§15 说明文献对应、适用边界与仍未解决的原始可达区域问题。本批不改判既有条目，也不把一次协议的存在改写为 §12 的最坏情形寿命定理。

### 13.1 原始任务、量词与实际输出

**定义 13.1（固定的原始均匀任务）。** 令 $j\in\frac12\mathbb Z_{>0}$、$D=2j+1$、$R=\operatorname{Sym}^{2j}(\mathbb C^2)$、$\tau_h=|j,h\rangle\langle j,h|$，其中 $h\in S^2$。固定
$$
d=\frac1{64},\quad r=\frac14,\quad B_{\rm field}=2,\quad G=1,\quad
\epsilon=\frac1{16},\quad\beta=\frac1{100},\quad\tau _0=1.
\tag{13.1}
$$
场 $n:U\to S^2$ 的定义域 $U\subset\mathbb R^2$ 是包含两条完整闭轴段 $\{t e_x:|t|\le r\}\cup\{t e_y:|t|\le r\}$ 的开集，$p=0$。$n$ 在 $U$ 上属于 $C^2$ 且秩为二，并满足
$$
\|n_{aa}(t e_a)\|\le B_{\rm field}\quad(a=x,y,\ |t|\le r),\qquad
\|n_x(0)\|,\|n_y(0)\|\le G.
\tag{13.2}
$$
每个点 $z$ 的一次重置供应 $\rho_n(z)=(I+n(z)\cdot\sigma)/2$，重置彼此独立；比较不同 $h$ 时场源的完整概率律不变。$R$ 的初态是唯一含未知 $h$ 的输入，所有设备、初态辅助和控制均不得依赖 $n$ 或 $h$。令
$$
D_h(n)=\left(\frac{h\cdot[n(0)\times n_x(0)]}{2},
\frac{h\cdot[n(0)\times n_y(0)]}{4},0,
\frac{h\cdot n_y(0)}2\right).
\tag{13.3}
$$
任务要求一个与 $n,h$ 无关的固定有限解码器，在每个这样的 $n$ 和每个 $h$ 上以至少 $1-\beta$ 的概率输出 $\widehat D$，使 $\|\widehat D-D_h(n)\|_\infty\le\epsilon$。这是真实同一运行的有限成功事件，不是有限时间精确重建。

取整数 $N$，使
$$
N\ge N_*:=2000(\epsilon d/2)^{-2}=8{,}388{,}608{,}000,\quad
M=10N,\quad L=M,\quad Q=18N+1,\quad D\ge8{,}000{,}000N^2,
\tag{13.4}
$$
并写 $\eta=\epsilon d/2=1/2048$。每个元组先固定，再比较协议。$L,Q$ 是调用上限；所构造协议恰用 $M$ 个获取槽和 $18N+1$ 次场重置。一般原始比较类允许任意有限混合辅助、量子记忆、先前输出回用及因果反馈，但除至多 $L$ 次指定槽和一次强制终端交换外，其操作在原始标记 $R$ 上均为恒等，不直接读取、旋转、拆分、重置或替换 $R$。初始 $R$ 与其余输入独立；固定 $n$ 后非 $R$ 来源、辅助及操作的完整律对所有 $h$ 相同。程序及解码器均与实际 $n,h$ 无关；场值只能经上述共同重置服务取得。原始仪器仍是
$$
\mathcal A(X)=\sum_{b=\pm}\Pi_bX\Pi_b\otimes|b\rangle\langle b|_H,
\qquad
\Pi_+=\frac{J\cdot\sigma+(j+1)I}{D},\quad
\Pi_-=\frac{jI-J\cdot\sigma}{D}.
\tag{13.5}
$$
在本批使用其声明的原生等距输出
$$
V=\sum_{b=\pm}\Pi_b\otimes|b\rangle_H|b\rangle_E,
\tag{13.6}
$$
并保留 $R,S,H,E$。式 (13.6) 是本批所需的原生接口假设；它不由抽象 CP 记号自动提供。

**定义 13.2（约化控制器和返回误差）。** $H$ 的 $|+\rangle,|-\rangle$ 是固定原始标签。每次槽后在 $S,H$ 上施行同一个确定性通道 $\mathcal C$，恒等作用于 $R,E$，其 Kraus 算子为
$$
L_+=I_S\otimes|+\rangle\langle+|,\qquad
L_{ab}=\frac{|a\rangle\langle b|_S}{\sqrt2}\otimes|-\rangle\langle-|_H
\quad(a,b\in\{0,1\}),
\tag{13.7}
$$
$$
\mathcal C(X)=L_+XL_+^\dagger+\sum_{a,b}L_{ab}XL_{ab}^\dagger .
\tag{13.8}
$$
五个 Kraus 项全部求和；它们的平方和为 $I_{S H}$。$H$ 的每一个原始 $b$、$E$、所有槽输出和控制器记录均留在最终口 $K$；(13.7) 的 Kraus 索引是代数求和指标，不是新原始读数。探针初态为明确供给的 $I_S/2$，没有接入不可见纯化。

在 $M$ 槽后用额外的一次场重置于 $+d e_x$，在同一 $R$ 上执行终端交换
$$
U_{\rm term}=\exp\!\left[-\,\frac{i d\tau _0}{2j}\,J\cdot\sigma\right].
\tag{13.9}
$$
该交换不计入 $M$ 个获取槽，计为一个单独的终端接触，其量子输出及其环境均属于 $K$。设同一运行的最终完整态为 $\Omega_{n,h}\in\mathsf D(R\otimes K)$，$\omega_{n,h}=\operatorname{Tr}_R\Omega_{n,h}$，并定义
$$
\Delta_{n,h}=D(\Omega_{n,h},\tau_h\otimes\omega_{n,h}).
\tag{13.10}
$$
这里的 $K$ 是实际最终保留口；没有把未观测的 Kraus 指标或一个证明用环境追加为返回系统。

### 13.2 一槽代数与完全的均匀上界

**定理 13.1（同一运行的约化 CP 获取—返回证书）。** 在定义 13.1–13.2 的接口下，令
$$
\kappa_D=\frac{2D-1}{2D^2},\qquad
e_{\rm CP}=\min\{1,M\kappa_D\},\qquad
\zeta=\min\left\{1,\frac{|d\tau _0|}{\sqrt{D-1}}\right\}.
\tag{13.11}
$$
存在一个只使用上述十个场设置、同一个固定解码器和一个强制终端交换的协议，使得对所有允许的 $n,h$ 及所有 $t>0$，
$$
\Pr\!\left[\|\widehat D-D_h(n)\|_\infty>
\frac{B_{\rm field}d}{4}+\frac{t}{d}\right]
\le\min\{1,20e^{-Nt^2/32}+e_{\rm CP}\},
\tag{13.12}
$$
且
$$
\sup_{n,h}\Delta_{n,h}
\le\min\{1,2(e_{\rm CP}+\zeta)\}
\le\min\left\{1,\frac{2M}{D}+2\zeta\right\}.
\tag{13.13}
$$
这些估计的证明只使用 $|t|\le d$ 上的轴向二阶导数界和五个采样点。因此同一协议与估计也适用于仅在包含两条闭 $d$ 轴段的开集上满足对应 $C^2$、秩二及导数条件的场；定义 13.1 的原始任务仍保留完整半径 $r$ 的域及其全部承诺。这只是一个可达证书；它没有声称最优性、匹配的下界、资源支配关系或任何历史新颖性。

**证明。** 先在 $h=z$ 的坐标计算。令 $e=|j,j\rangle$、$f=|j,j-1\rangle$、$m=D-1$，并把 $S$ 的标准基记为 $\uparrow,\downarrow$。直接由 $J_z e=je$、$J_+e=0$、$J_-e=\sqrt{2j}\,f$ 得
$$
\begin{aligned}
\Pi_+(e\otimes\uparrow)&=e\otimes\uparrow,\\
\Pi_-(e\otimes\uparrow)&=0,\\
\Pi_+(e\otimes\downarrow)&=\frac{e\otimes\downarrow+\sqrt m\,f\otimes\uparrow}{D},\\
\Pi_-(e\otimes\downarrow)&=\frac{m\,e\otimes\downarrow-\sqrt m\,f\otimes\uparrow}{D}.
\end{aligned}
\tag{13.14}
$$
令 $\tau_e=|e\rangle\langle e|$、$\tau_f=|f\rangle\langle f|$、$|++\rangle=|+\rangle_H|+\rangle_E$、$|--\rangle=|-\rangle_H|-\rangle_E$。对一个独立 $I_S/2$ 探针，(13.5)–(13.8) 的完整 $R,S,H,E$ 输出等于
$$
\begin{aligned}
\Omega_z^{(1)}
={}&\left[
\frac{|e\uparrow\rangle\langle e\uparrow|}{2}
+\frac{|e\downarrow+\sqrt m\,f\uparrow\rangle
 \langle e\downarrow+\sqrt m\,f\uparrow|}{2D^2}
\right]\otimes|++\rangle\langle++|\\
&+\frac{m^2\tau_e+m\tau_f}{2D^2}
 \otimes\frac{I_S}{2}\otimes|--\rangle\langle--|.
\end{aligned}
\tag{13.15}
$$
把同一个 $\mathcal C$ 施于理想 $z$-投影仪器，得到
$$
\xi_z=\frac{P_{z,+}}2\otimes|++\rangle\langle++|
+\frac{I_S}{4}\otimes|--\rangle\langle--|,
\tag{13.16}
$$
故理想完整槽态为 $\tau_e\otimes\xi_z$。正负旗标块正交。正块差的迹为 $1/(2D)$；负块差为
$$
\frac{-(2D-1)\tau_e+(D-1)\tau_f}{2D^2}\otimes\frac{I_S}{2},
\tag{13.17}
$$
其迹范数为 $(3D-2)/(2D^2)$。因此
$$
D(\Omega_z^{(1)},\tau_e\otimes\xi_z)
=\frac12\left[\frac1{2D}+\frac{3D-2}{2D^2}\right]
=\kappa_D.
\tag{13.18}
$$
同时旋转 $\Pi_\pm$、$\tau_h$ 和 $P_{h,+}$，而 $\mathcal C$ 的负块是基无关的替换 $S\mapsto I_S/2$，所以 (13.18) 对每个 $h$ 相同。这一步只是在证明中换坐标，没有执行依赖 $h$ 的旋转。

准备 $M$ 个独立 $I/2$ 探针，在每一槽后立即施行 (13.8)。用数学上的混合链把前 $k$ 槽替换成理想槽、其余保持实际槽。每个理想前缀都把 $R$ 留在 $\tau_h$，下一探针仍为 $I/2$；所有较早输出、记忆和旁观者可任意纠缠而不改变 (13.18) 的下一槽计算。共同后缀是全寄存器 CPTP 映射，故三角不等式和迹距离收缩性给出
$$
D(\Omega^{(M)}_{n,h},\tau_h\otimes\Xi_{n,h}^{\,i})
\le\min\{1,M\kappa_D\}=e_{\rm CP}
\tag{13.19}
$$
（右端超过一时取一）。这里没有在实际运行中重置 $R$，也没有把任意受扰动参考替换成 $\tau_h$；混合链只是完整态的比较。

为得到场数据，对四个卫星 $z\in\{+d e_x,-d e_x,+d e_y,-d e_y\}$ 及 $s=\pm1$ 各取 $N$ 个中心—卫星对，在两个场输出上施行
$$
Q_s=\frac{I-i s\,\mathrm{SWAP}}{\sqrt2},
\tag{13.20}
$$
保留两个输出而把第二个输出送入标量测试；在 $y$ 的两个卫星上另取各 $N$ 个直接令牌。中心令牌 $8N$ 个、$x$ 卫星每点 $2N$ 个、$y$ 卫星每点 $3N$ 个，共 $18N$ 个场重置，再加上 (13.9) 的一个令牌。若中心与卫星 Bloch 向量为 $a,b$，第二输出的 Bloch 向量为
$$
v_{z,s}=\frac{n(0)+n(z)+s\,n(0)\times n(z)}2.
\tag{13.21}
$$
每个选定场输出和一枚 $S$ 探针做标量受控 SWAP：固定标量先取 $|0\rangle$，施行 $H$、受控 SWAP、$H$ 和固定 $Y$ 读出；读出指针及其复制环境均保留。保留所有原生 $b,H,E$ 以及两份部分 SWAP 输出。对每次槽定义
$$
X=4\,\mathbf1_{\{b=+\}}Y-1\in\{-5,-1,3\}.
\tag{13.22}
$$
这不是选支或条件归一化。

在理想比较实验中，$b$ 是公平且独立的，$b=+$ 时 $S=P_{h,+}$，$b=-$ 时 $S=I/2$。因而对 Bloch 向量 $v$，
$$
\mathbb E[X]=4\cdot\frac12\cdot
\frac{1+h\cdot v}{2}-1=h\cdot v.
\tag{13.23}
$$
令 $\overline X_{z,s}$ 为八个设置的均值，令 $\overline Z_{y,\pm}$ 为两个直接设置的均值，并令
$$
\begin{aligned}
\widehat C_z&=\overline X_{z,+}-\overline X_{z,-},\\
\widehat D={}&\left(
\frac{\widehat C_{+d e_x}-\widehat C_{-d e_x}}{4d},
\frac{\widehat C_{+d e_y}-\widehat C_{-d e_y}}{8d},
0,
\frac{\overline Z_{y,+}-\overline Z_{y,-}}{4d}
\right).
\end{aligned}
\tag{13.24}
$$
每个均值只需保存两类计数；忽略某个寄存器参与算术不等于删除它。式 (13.24) 是固定的有限有理解码器。

沿每条轴，中心差分的平均值是区间内一阶导数的平均值。由 (13.2) 积分得其偏差不超过 $B_{\rm field}d/2$；代入 (13.24) 后四个坐标的最大偏差不超过 $B_{\rm field}d/4$。在理想比较实验中，$X$ 的宽度为 $8$，中心化对数矩母函数满足 $\log\mathbb E e^{u(X-\mathbb EX)}\le8u^2$。取 $u=t/16$ 并用 Markov 不等式，每个均值的双侧尾概率不超过 $2e^{-Nt^2/32}$，十个设置并合给 $20e^{-Nt^2/32}$。由 (13.19)，同一个完整记录事件在实际运行和理想比较运行之间的概率差不超过 $e_{\rm CP}$，于是得到 (13.12)。注意这里没有假设实际槽之间独立。

最后使用强制的终端令牌。理想 $\tau_h$ 子空间上，(13.9) 的生成元与 $I_R\otimes h\cdot\sigma/2$ 的差的范数不超过 $1/\sqrt{D-1}$；Duhamel 公式给出理想终端演化误差 $\zeta$。对 (13.19) 两个输入同时施行同一终端通道。实际最终 $\Omega_{n,h}$ 因而与某个 $\tau_h\otimes\omega^{\,i}_{n,h}$ 的距离不超过 $e_{\rm CP}+\zeta$；偏迹收缩给实际 $K$ 边缘 $\omega_{n,h}$ 与 $\omega^{\,i}_{n,h}$ 的同一距离上界。再用三角不等式比较 $\Omega_{n,h}$ 与 $\tau_h\otimes\omega_{n,h}$，得到
$$
\Delta_{n,h}\le 2(e_{\rm CP}+\zeta).
\tag{13.25}
$$
所有终端量子输出和环境都仍在 $K$ 中。因为 $\kappa_D<1/D$，(13.13) 随即成立。$\square$

取 $t=\eta$ 时，
$$
\frac{B_{\rm field}d}{4}+\frac{\eta}{d}
=\frac1{128}+\frac1{32}=\frac5{128}<\frac1{16},
\tag{13.26}
$$
且 $N\eta^2\ge2000$、$D\ge8{,}000{,}000N^2$，并有 $D-1>4{,}000{,}000N^2$。式 (13.12) 中 $20e^{-N\eta^2/32}\le20e^{-125/2}<1/1000$，而 $e_{\rm CP}<M/D\le1/(800000N)$，所以失败概率严格小于 $1/100$；(13.13) 仍给出统一的有限返回上界。这些估计包括 $D=8{,}000{,}000N^2$ 的端点。特别地，取
$$
N=N_*,\quad D=8{,}000{,}000N_*^2,\quad
j=(D-1)/2,\quad L=10N_*,\quad Q=18N_*+1
\tag{13.27}
$$
并保留其余参数，得到一个明确非空、有限且获取可行的原始元组。该协议没有声称原生场源、门、校准、噪声汇或物理时钟由这些数学接口自动实现；它们是条件模型前提。

**命题 13.2（资源与原生接口清单）。** 在定理 13.1 的协议中，$R$ 只准备一次，不重置；恰有 $M$ 次 (13.5) 原生槽调用、$M$ 次确定性通道 $\mathcal C$ 调用和一次 (13.9) 终端接触。另准备 $M$ 枚独立混合探针 $I/2$，以及 $M$ 枚标量测试的 $|0\rangle$；这些准备均与 $n,h$ 无关，没有接入其不可见纯化。场重置恰为 $18N+1$，不超过 $Q$；部分 SWAP 门为 $8N$，标量受控 SWAP 为 $M$，标量 Hadamard 为 $2M$，标量读出为 $M$。探针与场令牌合计 $M+(18N+1)=28N+1$ 个 qubit 输出，此外还有维数 $D$ 的原始自旋 $R$、$M$ 枚标量测试 qubit 及全部记录系统。每个槽的 $b,Y$ 原始符号、$M$ 组原生 $H,E$、两份部分 SWAP 输出、标量指针和实际复制/读出环境、二十个 $[0,N]$ 计数器（每个设置的两类计数）、路由/程序/步进/解码工作区全部保留。有限计数与有理解码运算另占这些工作寄存器，不把上述 qubit 小计称为完整辅助维数或全部基本门成本。没有把未使用的上限调用计入，也没有固定有限存储无限历史的主张。若物理实现 $\mathcal C$ 另有实际噪声系统 $F_{\mathcal C}$，则 $F_{\mathcal C}$ 必须加入 $K$ 并重新证明 (13.13)；(13.13) 不因形式上的 Stinespring 环境而自动延伸。

## 14. 实际等距定理与约化类的分离

### 14.1 实际等距定理与约化类的分离

**定理 14.1（带实际完整输出的相干等距返回律）。** 令 $U:R\otimes P\to R\otimes K$ 是一个与 $h$ 无关的等距，且右端就是实际完整返回口；令 $\sigma$ 是任意有限维混合辅助态。写
$$
\Omega_h=U(\tau_h\otimes\sigma)U^\dagger,\quad
\omega_h=\operatorname{Tr}_R\Omega_h,\quad
\overline\delta=\sup_hD(\Omega_h,\tau_h\otimes\omega_h).
\tag{14.1}
$$
则每个反向对满足
$$
D(\omega_h,\omega_{-h})
\le(1+2\pi\sqrt{2j})\,\overline\delta.
\tag{14.2}
$$
若一个固定解码器在两个目标球上的错误均不超过 $\beta<1/2$，且两球由同一输出记录区分，则
$$
\overline\delta\ge\frac{1-2\beta}{1+2\pi\sqrt{2j}}.
\tag{14.3}
$$

**证明。** 令 $e_h=|j,h\rangle$，把算子 $U(e_h\otimes I_P)$ 写成
$$
U(e_h\otimes I_P)=e_h\otimes F_h+B_h,\qquad
(\langle e_h|\otimes I)B_h=0.
\tag{14.4}
$$
等距性给出 $F_h^\dagger F_h+B_h^\dagger B_h=I_P$。置 $p_h=\operatorname{Tr}(B_h\sigma B_h^\dagger)$。由效果 $I-\tau_h$ 对 $\Omega_h$ 的测量及迹距离的变分表示，$p_h\le\overline\delta$。把 $X=\Omega_h$ 与 $\tau_h\otimes\omega_h$ 的差按 $R$ 上 $\tau_h$ 的对角、非对角块分解；用 $2\tau_h-I$ 的共轭取出非对角块，得到
$$
\|F_h\sigma B_h^\dagger\|_1\le\overline\delta.
\tag{14.5}
$$
于是
$$
\|B_h\sigma\|_1
\le\|F_h\sigma B_h^\dagger\|_1+
\|B_h\sigma B_h^\dagger\|_1
\le2\overline\delta .
\tag{14.6}
$$
令 $m=2j$，在相干坐标
$$
e(z)=(1+|z|^2)^{-m/2}(|0\rangle+z|1\rangle)^{\otimes m}
\tag{14.7}
$$
上，把 $F(z)$ 看作 $F_h$ 的算子值函数。相干切向量计算给出
$$
\|\partial_{\bar z}(F(z)\sigma)\|_1
\le\frac{2\overline\delta\sqrt m}{1+|z|^2}.
\tag{14.8}
$$
对 (14.8) 逐矩阵元使用 Cauchy–Pompeiu 公式，或在有限维迹类上直接使用同一积分，得到
$$
\|(F_0-F_\infty)\sigma\|_1\le2\pi\sqrt m\,\overline\delta.
\tag{14.9}
$$
这里的积分常数来自
$\frac1\pi\int_{\mathbb C}[(1+|z|^2)|z|]^{-1}d^2z=\pi$；任一反向对可先用固定旋转送到 $0,\infty$。

偏迹消去 $R$ 上的交叉项，故
$$
\omega_h=F_h\sigma F_h^\dagger+
\operatorname{Tr}_R(B_h\sigma B_h^\dagger).
\tag{14.10}
$$
$F_h$ 是收缩，展开第一项并用 (14.9)，再加上两个正余项的迹，得到
$$
D(\omega_h,\omega_{-h})
\le2\pi\sqrt m\,\overline\delta+
\frac{p_h+p_{-h}}2
\le(1+2\pi\sqrt m)\overline\delta.
\tag{14.11}
$$
固定解码器把两个分离目标球的输出事件分成一项在两端概率分别至少 $1-\beta$ 和至多 $\beta$，所以其可访问记录的迹距离至少 $1-2\beta$；嵌入 $K$ 后仍由收缩性成立。代入 (14.11) 即得 (14.2)–(14.3)。$\square$

定理 14.1 的载荷假设是“等距”以及“等距的右端是实际完整返回口”。把一个约化 CP 通道写成 Stinespring 等距、再把证明环境当作返回口，并不能满足这些假设。定理 13.1 的 $\mathcal C$ 只有约化的实际输出 $S,H,E$；若一个物理噪声实现保留额外环境，则返回误差必须对扩大的实际 $K$ 重新估计。

**命题 14.2（删除等距假设的获取可行反例）。** 在场
$$
n(x,y)=(x,y,\sqrt{1-x^2-y^2})
\tag{14.12}
$$
的半径 $1/3$ 开圆盘内，(13.2) 成立，且 $D_h(n)=(h_2/2,-h_1/4,0,h_2/2)$。在元组 (13.27) 上，定理 13.1 的同一固定解码器在全体 $n,h$ 上成功。若把 (14.2) 错误地用于其约化输出，令 $q=49/50$，则端点分离给出 $D(\omega_+,\omega_-)\ge q$，而 (13.13) 给出
$$
\overline\delta\sqrt{D-1}
\le2M\kappa_D\sqrt{D-1}+2d
\le\frac{2M}{\sqrt{D-1}}+\frac1{32}
<\frac{33}{800}<\frac{49}{400}
\tag{14.13}
$$
这里 $D-1>4{,}000{,}000N^2$ 给出上面的严格数值界；又 $\pi<22/7$ 给 $1+2\pi<51/7<8$，且 $\sqrt{D-1}\ge1$，故 $1+2\pi\sqrt{D-1}<8\sqrt{D-1}$。这与错误延伸所需的 $\overline\delta\sqrt{D-1}\ge49/400$ 矛盾。因此删除“实际等距完整输出”不是无害的记号简化。

### 14.2 一般实际 CPTP 的全球必要下界

**定理 14.3（相干全球泄漏控制实际侧输出）。** 令 $\Lambda:R\to R\otimes K$ 是任意与 $h$ 无关的有限维 CPTP 通道，允许任意固定的混合辅助、因果非 $R$ 处理和终端接触均已吸收进 $\Lambda$。置
$$
\Omega_h=\Lambda(\tau_h),\quad\omega_h=\operatorname{Tr}_R\Omega_h,\quad
p_h=\operatorname{Tr}[((I-\tau_h)\otimes I_K)\Omega_h],
\tag{14.14}
$$
$$
p_*=\sup_h p_h,\qquad
\overline\delta=\sup_hD(\Omega_h,\tau_h\otimes\omega_h).
\tag{14.15}
$$
则
$$
D(\omega_h,\omega_{-h})
\le\pi\sqrt{2j\,p_*}+\frac{p_h+p_{-h}}2
\le\pi\sqrt{2j\,\overline\delta}+\overline\delta
\tag{14.16}
$$
对每个 $h$ 成立。这里没有协变性、纯辅助或实际等距输出假设。

**证明。** 取任一有限 Kraus 表示
$\Lambda(X)=\sum_rA_rXA_r^\dagger$，$\sum_rA_r^\dagger A_r=I$。它只是同一实际通道的代数表示，$r$ 不加入 $K$。对每个 $h$ 写
$$
A_re_h=e_h\otimes f_{r,h}+b_{r,h},\qquad
(\langle e_h|\otimes I)b_{r,h}=0.
\tag{14.17}
$$
把所有 $f_{r,h}$ 堆叠到 $K\otimes\mathbb C^q$，把所有 $b_{r,h}$ 同样堆叠。则
$$
\sum_r\|b_{r,h}\|^2=p_h\le\overline\delta.
\tag{14.18}
$$
使用 (14.7) 的相干符号计算，输入导数中平行分量抵消，正交切向量的范数为 $\sqrt{2j}/(1+|z|^2)$。于是堆叠向量满足
$$
\|\partial_{\bar z}f(z)\|
\le\frac{\sqrt{2j\,p_*}}{1+|z|^2}.
\tag{14.19}
$$
Cauchy–Pompeiu 公式给出
$$
\|f_h-f_{-h}\|\le\pi\sqrt{2j\,p_*}.
\tag{14.20}
$$
在 $R$ 上取偏迹会消去交叉项，故实际侧边缘分解为
$$
\omega_h=Q_h+Z_h,\quad
Q_h=\sum_r|f_{r,h}\rangle\langle f_{r,h}|,\quad
Z_h=\operatorname{Tr}_R\sum_r|b_{r,h}\rangle\langle b_{r,h}|,
\tag{14.21}
$$
其中 $Z_h\ge0$ 且 $\operatorname{Tr}Z_h=p_h$。向量恒有范数不超过一，故
$$
\frac12\|Q_h-Q_{-h}\|_1\le\|f_h-f_{-h}\|,
\qquad
\frac12\|Z_h-Z_{-h}\|_1\le\frac{p_h+p_{-h}}2.
\tag{14.22}
$$
合并 (14.18)–(14.22) 得 (14.16)。这一步没有把 Kraus 指标变成输出，没有接入初始纯化，也没有选支或后选择。$\square$

**推论 14.4（获取可行元组上的正返回排除）。** 若固定解码器在一对反向任务上错误不超过 $\beta$，且目标球相隔大于 $2\epsilon$，置 $a=1-2\beta$，则
$$
\overline\delta\ge
\left(\frac{2a}{\sqrt{\pi^2(2j)+4a}+\pi\sqrt{2j}}\right)^2
\ge\frac{a^2}{(1+\pi\sqrt{2j})^2}.
\tag{14.23}
$$
证明第一式是令 $x=\sqrt{\overline\delta}$ 解
$x^2+\pi\sqrt{2j}\,x-a\ge0$；第二式用 $\overline\delta\le1$。对 (13.12) 的固定获取可行协议，取 $a=q=49/50$。若某同一原始控制器在同一元组上还满足
$$
\overline\delta\le\delta_{\rm test}:=\frac{q^2}{100D},
\tag{14.24}
$$
则 (14.16) 的右端小于
$\delta_{\rm test}+\pi\sqrt{(D-1)\delta_{\rm test}}<q/100+4q/10=41q/100<q$，
矛盾。故 (13.27) 以及整个 (13.4) 可行族上都有一个严格正的排除；它不是把获取任务改成不可行任务。

**推论 14.5（相对于既有成对证书的严格有限增益）。** 固定任一 (13.4) 的元组。比较类仍是：原始 $R$ 只准备一次，场源与任意有限混合辅助在固定 $n$ 时对全部 $h$ 具有同一初始律；一个与 $n,h$ 无关的有限因果控制器及同一个解码器在定义 13.1 的全体场与方向上成功。除至多 $L$ 次总自旋槽及一次强制终端交换外，操作在 $R$ 上均为恒等；允许处理全部非 $R$ 输出、适应性经典与量子记忆以及探针回用。始终用 (13.10) 的同一实际 $R K$ 输出及其实际 $K$ 边缘定义返回误差，并置 $\overline\delta=\sup_{n,h}\Delta_{n,h}$。全部原生 $H,E$、原始 $b,Y$、实际复制、分支、记忆和终端输出保持在 $K$ 中。

这里的整数 $T$ 专指每条运行分支上全部实际 $R$ 接触数的统一上界，不指假设 12.2 的网络符号。每次总自旋槽算一次；终端交换也算一次，故本元组统一可取
$$
T=L+1=M+1=10N+1<m:=2j=D-1.
$$
控制器若少用获取槽，按其实际调用计数，再加这个强制终端接触；用 $L+1$ 作为共同上界不把未执行的槽算成执行。下述支撑修正对任意足够覆盖实际接触数的整数 $0\le T<m$ 成立，包含本族的统一上界。

固定同一个允许的 $n$ 及满足
$\|D_{h_0}(n)-D_{h_1}(n)\|_\infty>2\epsilon$ 的一对方向。令其夹角为 $\theta$，并先取 $0<\theta<\pi$，定义
$$
u=\cos^2\frac\theta2,\qquad
s=|\langle j,h_0|j,h_1\rangle|=u^{m/2},\qquad
\nu=\sqrt{1-s^2},\qquad a=1-2\beta=q=\frac{49}{50}.
$$
把已有解码输出按是否落入 $D_{h_0}(n)$ 的闭 $\epsilon$ 球分组，得到同一个实际记录效果，在两端概率分别至少 $1-\beta$ 和至多 $\beta$。固定 $n$ 后只吸收共同的非 $R$ 来源和辅助，完整运行就是一个 $h$ 无关的 CPTP 映射 $\Lambda_n:R\to R K$，包含终端交换。收缩性因而给出必需的二元获取可行域
$$
0<a\le D(\tau_{h_0},\tau_{h_1})=\nu.
$$
若 $a>\nu$，该对已排除获取，不是可行任务上的返回证书。以下公式及其包络估计实际上对全部 $0<a\le\nu$ 成立；应用本任务时固定取 $a=q$，不改变其成功要求。

在这个可行域上，既有直接混合输出证书为
$$
C(s,a)=\frac{\sqrt{\nu^2+s^2a^2}-\nu}{2}.
\tag{14.25}
$$
有限接触支撑参数的完整定义是
$$
\eta_T(u)=\sum_{k=T+1}^{m}\binom mk u^{m-k}(1-u)^k,\qquad
\kappa_T(u)=\frac{\eta_T(u)}{1-u^m}=\frac{\eta_T(u)}{1-s^2}.
\tag{14.25a}
$$
因为 $0<u<1$、$0\le T<m$，并且从 $k=1$ 到 $m$ 的全和为 $1-u^m$，有 $0<\kappa_T\le1$。相应既有二元生存及支撑证书为
$$
S_T(s,a)=\frac{b(s,a)}{1-\kappa_T(u)/2},\quad
b(s,a)=\frac{1-\sqrt{1-s^2\nu^2(1-\gamma)^2}}2,\quad
\gamma=\sqrt{1-a^2/\nu^2}.
\tag{14.26}
$$
它们的结论是 $\overline\delta\ge C(s,a)$、$\overline\delta\ge S_T(s,a)\ge b(s,a)$，均约束上述同一运行的实际输出。它们不是一个均匀合法优化器。若 $\theta=\pi$，取 $u=s=0,\nu=1,\kappa_T=1$，三份证书均为零，照样纳入比较；$\theta=0$ 不可能给出分离目标。若在其它元组上 $T\ge m$，空尾和取零，支撑修正退为 $S_T=b$，不再声称严格修正。本族无此情形。

**证明。** 先说明两份证书与实际合同的对应，以固定比较对象。对同一 $\Lambda_n$ 的两端输出写 $\Omega_i,\omega_i$，令 $P_i=\tau_{h_i}\otimes\omega_i$、$\Delta_i=D(\Omega_i,P_i)$。上述二元效果在 $\omega_0,\omega_1$ 上的概率记为 $p_0,p_1$，则 $p_0-p_1\ge a$。对任意 $x,y\ge0$，两维秩一计算给
$$
\|x\tau_{h_0}-y\tau_{h_1}\|_1
=\sqrt{\nu^2(x+y)^2+s^2(x-y)^2}.
$$
对 $P_0,P_1$ 的 $K$ 因子作该二元测量，仅作为数学比较，两个正交结果块的这个范数之和由二维三角不等式给出
$D(P_0,P_1)\ge\sqrt{\nu^2+s^2(p_0-p_1)^2}$。
又 $D(\Omega_0,\Omega_1)\le\nu$，所以
$\Delta_0+\Delta_1\ge\sqrt{\nu^2+s^2a^2}-\nu$，得到 (14.25)。这是自足的共同通道计算，不使用输出纯度。

式 (14.26) 的 $b$ 精确复用 Buscemi–Sacchi 的 *Information-Disturbance Tradeoff in Quantum State Discrimination*，[修正版本原文](https://arxiv.org/html/quant-ph/0610196v2) 的式 (1)–(3)、(15)、(21)–(25)：两个等先验纯输入、任意返回同一二维信号的二元 CP 仪器，以平均成功率和平均生存失真为指标。对应取该文 $\sin(2\alpha)=s$、$\cos(2\alpha)=\nu$、$t=a/\nu$，则其 $P_t=(1+a)/2$、$\gamma=\sqrt{1-t^2}$，最小平均生存失真即这里的 $b(s,a)$。该函数在 $0\le a\le\nu$ 上非减，故成功率至少 $(1+a)/2$ 时也得到同一必要下界。这里只复用这个二元定理，不声称其最优仪器能由原始槽实现，也不将该生存指标直接等同于实际乘积返回。

为说明支撑因子及指标转换，置 $\psi_i=|j,h_i\rangle$，选相位使 $\langle\psi_0,\psi_1\rangle=s$，并令
$$
W_t(h)=\operatorname{span}\{|j,j-k\rangle_h:0\le k\le\min(t,m)\},\quad
\mathcal S=\operatorname{span}\{\psi_0,\psi_1\},\quad
v_i=\frac{\psi_{1-i}-s\psi_i}{\nu}.
$$
初始 $R$ 支撑在 $W_0(h)$。式 (13.5) 的两个投影在 $J$ 中仿射，而 $J_h,J_\pm$ 每次至多改变一个降低数；它们把 $W_t(h)$ 送入 $W_{t+1}(h)$，对任意联合探针、记忆和相干指针仍成立。所有非 $R$ Kraus 操作保持这个支撑。$J\cdot\sigma$ 的两个本征值为 $j,-(j+1)$，故 (13.9) 是 $\Pi_+,\Pi_-$ 的标量线性组合，同样只增加一个支撑步。对完整有限因果树归纳，包含混合辅助、适应反馈和回用探针，实际参考边缘 $\rho_i=\operatorname{Tr}_K\Omega_i$ 因而支撑在 $W_T(h_i)$。这也说明为何终端接触不能漏计。

相干对称张量展开在降低数 $k$ 上的平方系数为
$\binom mk u^{m-k}(1-u)^k$。因此
$\|P_{W_T(h_i)^\perp}v_i\|^2=\kappa_T$。
令 $\ell_i=1-\langle\psi_i|\rho_i|\psi_i\rangle$、
$q_i=\operatorname{Tr}(P_{\mathcal S^\perp}\rho_i)$。
在 $W_T(h_i)\cap\psi_i^\perp$ 上，
$P_{\mathcal S^\perp}$ 的压缩为
$I-|P_{W_T(h_i)}v_i\rangle\langle P_{W_T(h_i)}v_i|$，
其下界为 $\kappa_T I$，而与 $\psi_i$ 的交叉项为零，故
$q_i\ge\kappa_T\ell_i$，对任意混合 $\rho_i$ 成立。

在数学比较中保留同一个二元记录，并对返回信号使用
$$
\Phi(X)=P_{\mathcal S}XP_{\mathcal S}
+\operatorname{Tr}(P_{\mathcal S^\perp}X)\frac{P_{\mathcal S}}2.
$$
它是保迹 CP 压缩，保持两个输入和记录概率，把返回失真改为
$\ell'_i=\ell_i-q_i/2$。限制输入到 $\mathcal S$ 后恰是上述二元来源的仪器域。因此
$$
b(s,a)\le\frac{\ell'_0+\ell'_1}{2}
\le(1-\kappa_T/2)\frac{\ell_0+\ell_1}{2}
\le(1-\kappa_T/2)\max_i\Delta_i
\le(1-\kappa_T/2)\overline\delta.
$$
这里 $\ell_i\le\Delta_i$ 来自实际 $R K$ 上的效果
$(I-\tau_{h_i})\otimes I_K$。这证明 (14.26) 的精确支撑证书。分组、偏迹与 $\Phi$ 都只是必要界的比较操作，不是给控制器增加未知方向、直接 $R$ 控制或删除实际输出的许可；没有把 Kraus 指标或初始纯化加入实际端口。

现在对这些证书取整个原始分离对包络。具体地，$\mathcal E_{\rm pair}$ 是所有允许的同场分离对、固定 $a=q$、以及适用于其接触上界 $T\le L+1$ 的上述 $C,b,S_T$ 数值的上确界；没有可用对时上确界取零。即使允许全部整数 $0\le T\le L+1$ 并把二元数值域扩大到全部 $0<a\le\nu$，下面的共同上界仍成立，所以没有以缩小比较域取得增益。每个目标坐标是 $h$ 的线性函数，其行范数不超过 $G/2=1/2$；于是
$$
2\epsilon<\|D_{h_0}(n)-D_{h_1}(n)\|_\infty
\le\frac12\|h_0-h_1\|=\sin\frac\theta2.
$$
因 $2\epsilon=1/8$，相干重叠满足
$$
s^2=\cos^{4j}\frac\theta2<
\left(\frac{63}{64}\right)^m.
\tag{14.27}
$$
在全部二元可行域，$\sqrt{\nu^2+s^2a^2}\le1$，所以
$C\le(1-\nu)/2=s^2/[2(1+\nu)]\le s^2/2$。
又置 $y=s^2\nu^2(1-\gamma)^2\le s^2$，则
$b=y/[2(1+\sqrt{1-y})]\le s^2/2$。
结合 $0<\kappa_T\le1$ 得
$S_T\le2b\le s^2$。
因此 $\mathcal E_{\rm pair}\le(63/64)^m$，包括正交对的零值及所有相应原始接触证书。

另一方面，(14.12) 的同场反向对 $\pm e_2$ 的目标距离为一。对任意在整个原始任务上成功的控制器，(14.23) 在这个固定场上的全方向返回上确界成立，因而也约束 $\overline\delta$。由 $a=q$、$m\ge1$ 及 $\pi<4$，
$$
\overline\delta\ge\frac{q^2}{(1+\pi\sqrt m)^2}
>\frac{q^2}{25m}>\frac9{250m}.
\tag{14.28}
$$
二项式展开 $(64/63)^m=(1+1/63)^m$ 给
$$
\left(\frac{63}{64}\right)^m
\le\frac{2\cdot63^2}{m(m-1)}
<\frac9{250m}\quad\text{当 }m-1>220500.
\tag{14.29}
$$
而 (13.4) 给 $m\ge8{,}000{,}000N^2-1$，同时保证 $L+1<m$ 和这个严格阈值。因此在整个给定的获取可行族上，(14.28) 严格高于上述整个成对证书包络；这些元组的非空均匀获取可行性由定理 13.1 的同一有限协议给出。这个比较只说明全球约化-CPTP 必要关系相对于明确给定的已付证书有严格有限增益，不说明全体成熟定理、最优系数、饱和协议或资源支配关系。$\square$

## 15. 约化类的环境反例、来源对应与剩余缺口

### 15.1 访问外反例、来源对应与剩余缺口

**命题 15.1（一般 CPTP 中的访问外反例）。** 令 $\ell=2j\ge2$。把 $R=\operatorname{Sym}^{\ell}(\mathbb C^2)$ 等距嵌入 $\operatorname{Sym}^{\ell-1}(\mathbb C^2)\otimes\mathbb C^2$，使 $|h\rangle^{\otimes\ell}$ 送到 $|h\rangle^{\otimes(\ell-1)}\otimes|h\rangle_K$。在前一因子施行 universal $(\ell-1)\to\ell$ cloning，保留 $K$。其对对称输入的 CPTP 公式为
$$
\mathcal C_{\ell-1\to\ell}(X)=\frac{\ell}{\ell+1}
P_\ell(X\otimes I_2)P_\ell .
\tag{15.1}
$$
归一化来自 $SU(2)$ 不变性：迹泛函在不可约输入上是迹的常数倍；对 $|0\rangle^{\otimes(\ell-1)}$，两项迹为 $1$ 和 $1/\ell$，乘以 $\ell/(\ell+1)$ 得一。对每个 $h$，输出为
$$
\Omega_h=\rho_h\otimes|h\rangle\langle h|_K,\quad
\rho_h=\frac{\ell}{\ell+1}\tau_h+
\frac1{\ell+1}|{\rm Dicke}_{\ell,1;h}\rangle
\langle{\rm Dicke}_{\ell,1;h}|.
\tag{15.2}
$$
Dicke 向量与 $\tau_h$ 正交，所以返回误差为 $1/(\ell+1)$，而 $K$ 的反向边缘距离为一。若仅凭约化 CPTP 性质套用 (14.2)，在 $\ell\ge64$ 时将得到错误的不等式
$1\le(1+2\pi\sqrt\ell)/(\ell+1)<1$。该通道直接拆分并处理 $R$ 的自旋成分，且把其机器环境约化掉；它不是 (13.5) 的合法槽控制器，也不构成原始任务的反例。它只证明把实际等距定理无条件扩展到抽象 CPTP 的企图必然失败。

**文献与范围。** Werner 的 *Optimal Cloning of Pure States*（[原文](https://arxiv.org/html/quant-ph/9804001v1)） 给出 (15.1) 的对称空间 CP 公式；这里只使用其构造和归一化，不使用最优性。Lemm–Wilde 的 *Information-theoretic limitations on approximate quantum cloning and broadcasting*（[原文](https://arxiv.org/html/1608.07569v2)） 说明对称偏迹与 universal cloning 的恢复对应，但其广播定理的边缘、乘积与度量假设没有移植到本任务。Kretschmann–Schlingemann–Werner 的 *The Information-Disturbance Tradeoff and the Continuity of Stinespring's Representation*（[原文](https://arxiv.org/html/quant-ph/0605009v1)） 需要稳定化或互补通道及解码假设，不能把任意 Stinespring 环境当作实际 $K$。Sacchi 的 *Information-disturbance tradeoff for spin coherent state estimation*（[原文](https://arxiv.org/html/quant-ph/0610246v2)） 使用 Haar 平均操作/估计保真度，和 (13.10) 的均匀实际乘积返回不同。Barnum–Caves–Fuchs–Jozsa–Schumacher 的 exact no-broadcasting（[原文](https://arxiv.org/html/quant-ph/9511010v1)） 只用于说明非对易态的成熟边界，不提供本文的定量界。上述来源均按其公开原文中对应章节或公式使用；没有据此声称文献穷尽或历史新颖性。OTF001–003、005–007 的几何、仪器、控制、记录和时钟前提仅按原卷已声明范围复用；AURIC 的物理源和消费者条件不自动成为本卷额外义务。

**边界与未决问题。** 定理 13.1 的上界是一个固定协议的存在性和资源证书，允许的约化控制器可以有任意有限混合辅助，但不供应其物理噪声汇、校准门或物理时钟。定理 14.1 只适用于实际完整等距输出；定理 14.3 是更大的任意实际 CPTP 类的必要条件，因而可约束原始合法类，却不说明该类能否实现 (15.1) 的访问机制。所有原始 $H,E$、$b,Y$、指针、复制环境和终端输出均已纳入口；没有不可访问初始纯化、$h$ 依赖程序、丢弃固定原生端口或归一化后选择分支。这里的 $\overline\delta$ 是一个协议的实际同一运行返回误差，而非 §12.5 的控制器上确界 $E_j(N)$；终端交换另行计费，故 (12.6)–(12.9) 的最坏情形寿命结论保持原样。

本批真正留下的原始数学缺口是：在保留所有原始 raw-sign 总自旋槽、终端交换和同一完整 $K$ 的条件下，能否证明更强的 $1/\sqrt j$ 返回必要性，或给出合法的较小系数约化 CP 控制器并保持同一个均匀解码器。定理 14.3 的 $1/j$ 级下界与定理 13.1 的 $2M/D+2\zeta$ 上界相容但不匹配；它没有给出共同优化器、完整可达区域或最优系数。

## 追加锚（本行以下为增补区）
## 16. 固定终端输出约化与同一协议的实际返回增益

**定义 16.1（协议、实际端口与终端节点）。** 固定定义 13.1 的任一原始元组，保留完整半径 $r$ 的场域及导数承诺、独立纯场重置服务、唯一初始方向资源 $\tau_h$ 和全部原始访问限制。写
$$
m=2j=D-1,\qquad t=d\tau_0=\frac1{64},\qquad
e=e_{\rm CP}=\min\{1,M\kappa_D\},\qquad
\kappa_D=\frac{2D-1}{2D^2},\qquad \zeta=\frac{t}{\sqrt m}.
\tag{16.1}
$$
这里 $N\ge N_*$、$M=L=10N$、$Q=18N+1$、$D\ge8{,}000{,}000N^2$，均与 (13.4) 相同。记定理 13.1、命题 13.2 的原协议为 $\mathsf P_{\rm raw}$；其十设置获取日程、通道 $\mathcal C$、全部资源和 (13.24) 的有限解码器均固定不变。

令 $K_0$ 为额外终端重置之前、获取与解码结束时的全部实际非参考寄存器，包括所有先前探针和场输出、原生 $H,E$、原始 $b,Y$、标量 qubit、指针与实际复制/读出环境、已保留的噪声系统、全部记录、二十个计数器、路由/程序/步进/解码工作区及旁观者。含解码工作区的实际获取结束态记为 $\eta_{n,h}$。额外重置仍供应独立的纯态
$$
P_v=\frac{I+v\cdot\sigma}{2},\qquad v=n(+d e_x),
$$
并在同一标记 $R$ 上实际执行原定交换 $U_{\rm term}=\exp(-itJ\cdot\sigma/m)$。其后只在同一个输出 qubit $S_t$ 上追加固定确定性节点
$$
\mathcal E(X)=\operatorname{Tr}(X)\frac{I_2}{2},\qquad
K_{ab}=\frac{|a\rangle\langle b|}{\sqrt2}\quad(a,b=0,1).
\tag{16.2}
$$
所得协议记为 $\mathsf P_{\rm dep}$。四个 Kraus 项全部求和，不产生新读数或选择分支。两协议的实际最终口均为 $K=K_0\otimes S_t$，用各自的实际边缘 $\omega_{\rm raw},\omega_{\rm dep}$ 按 (13.10) 定义 $\Delta_{\rm raw},\Delta_{\rm dep}$，并记 $\bar\delta_\bullet=\sup_{n,h}\Delta_\bullet(n,h)$。

本节的端口假设是上述指定约化实现：终端交换为 $R S_t$ 上的幺正原语，$\mathcal E:S_t\to S_t$ 没有另行声明的实际输出；获取阶段的完整口满足 (13.19)。若 $\mathcal C$ 或 $\mathcal E$ 的另一实现产生额外实际噪声、随机记录或工作寄存器 $F$，则必须把 $F$ 纳入实际 $K$ 并重新估计；下述定理不覆盖未经该完整口估计的实现。形式 Kraus 指标和证明用扩张空间不自动成为实际输出，实际存在的输出也不得由此删去。

置
$$
x_D=\frac{Dt}{2m},\qquad
b_D=\frac{2\sqrt m}{D}\sin x_D,\qquad
g_D=\frac{b_D}{2\sqrt{1-b_D^2}},\qquad
D_{\rm tr}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1.
\tag{16.3}
$$

**定理 16.2（原任务保持与完整实际边缘证书；repo-derived）。** 在定义 16.1 的实际约化口假设下，$\mathsf P_{\rm dep}$ 属于原始允许类，精确保留整个 $K_0$ 可观测代数及原解码器的分布。特别是对每个允许的 $n,h$，
$$
\Pr_{\rm dep}\!\left[\|\widehat D-D_h(n)\|_\infty\le\epsilon\right]
=\Pr_{\rm raw}\!\left[\|\widehat D-D_h(n)\|_\infty\le\epsilon\right]
\ge1-\beta,
\tag{16.4}
$$
其中目标仍为初始方向的
$$
D_h(n)=\left(
\frac{h\cdot[n(0)\times n_x(0)]}{2},
\frac{h\cdot[n(0)\times n_y(0)]}{4},0,
\frac{h\cdot n_y(0)}2\right).
$$
定义参考通道
$$
\mathcal T_v(X)=\operatorname{Tr}_{S_t}
\!\left[U_{\rm term}(X\otimes P_v)U_{\rm term}^\dagger\right].
$$
则对实际的、允许相关的 $\eta=\eta_{n,h}$，完整输出及其实际边缘恰为
$$
\begin{aligned}
\Omega_{\rm dep}
&=[(\mathcal T_v\otimes\operatorname{id}_{K_0})(\eta)]
 \otimes I_2/2,\\
\omega_{\rm dep}&=\eta_{K_0}\otimes I_2/2,\\
\Delta_{\rm dep}(n,h)
&=D_{\rm tr}\!\left((\mathcal T_v\otimes\operatorname{id}_{K_0})(\eta),
                   \tau_h\otimes\eta_{K_0}\right).
\end{aligned}
\tag{16.5}
$$
它满足
$$
\bar\delta_{\rm dep}\le\min\{1,2e+g_D\}
<\min\{1,2(e+\zeta)\}.
\tag{16.6}
$$
式 (16.6) 的严格号比较两个统一充分证书；另有逐点实际不等式 $\Delta_{\rm dep}(n,h)\le\Delta_{\rm raw}(n,h)$，其严格最坏情形比较见命题 16.3。

**证明。** $\sum_{a,b}K_{ab}^\dagger K_{ab}=I_2$，故 (16.2) 是一个与 $n,h,v$ 无关的非参考 CPTP 节点。假设 12.2 和定义 13.1 允许因果处理先前量子输出；本节点位于规定纯输入和交换之后，不增加 $R$ 接触、场调用或方向资源，也不改动原始标签。其伴随满足 $\mathcal E^\dagger(C)=\operatorname{Tr}(C)I_2/2$，从而对每个 $A\in\mathcal B(K_0)$，
$$
(\operatorname{id}_{K_0}\otimes\mathcal E)^\dagger
(A\otimes I_{S_t})=A\otimes I_{S_t}.
\tag{16.7}
$$
此等式对相关输入仍成立，故全部早期边缘、原始记录效果及 (13.24) 的同一个成功事件精确保留。定理 13.1 的成功保证遂给 (16.4)。它没有把目标改成终态的导数；$\mathcal E^\dagger$ 对终端无迹可观测量为零，因此也没有声称终端完整矩阵代数被固定。同一输出 qubit 保留在 $K$，其态被实际改变为 $I_2/2$。

对交换后的任意联合态应用 (16.2)，恒有 $\operatorname{Tr}_{S_t}(\,\cdot\,)\otimes I_2/2$ 的代数表达。$\mathcal T_v$ 保迹，所以其非参考边缘仍为 $\eta_{K_0}$。再用 $\|X\otimes I_2/2\|_1=\|X\|_1$，得到 (16.5)；这里的偏迹表达指定约化节点，未从实际口删去 $S_t$ 或任何 $K_0$ 因子。

计算 $\rho_{h,v}=\mathcal T_v(\tau_h)$。仅在证明中选 $h=z$，令 $e_h=|j,j\rangle$、$f_h=|j,j-1\rangle$，并写 $|v,+\rangle=\alpha|\uparrow\rangle+\beta_0|\downarrow\rangle$、
$p=|\beta_0|^2=(1-h\cdot v)/2$。由 (13.5)、(13.14)，$J\cdot\sigma$ 的两个本征值为 $j,-(j+1)$，所以略去公共相位后，
$$
\begin{aligned}
U_{\rm term}&=\Pi_++z_t\Pi_-,\qquad z_t=e^{iDt/m},\\
U_{\rm term}(e_h\uparrow)&=e_h\uparrow,\\
U_{\rm term}(e_h\downarrow)&=A_t e_h\downarrow+B_t f_h\uparrow,\\
A_t&=\frac{1+m z_t}{D},\qquad B_t=\frac{\sqrt m(1-z_t)}{D},\\
|B_t|&=b_D,\qquad |A_t|^2=1-b_D^2.
\end{aligned}
\tag{16.8}
$$
于是交换向量为 $w=\alpha e_h\uparrow+\beta_0 A_t e_h\downarrow+\beta_0 B_t f_h\uparrow$，参考边缘仅支撑于 $e_h,f_h$，其矩阵为
$$
\rho_{h,v}=
\begin{pmatrix}
1-pb_D^2&\alpha\overline{\beta_0}\,\overline{B_t}\\
\overline\alpha\beta_0 B_t&pb_D^2
\end{pmatrix}.
\tag{16.9}
$$
差 $\rho_{h,v}-\tau_h$ 的特征值为 $\pm q(p)$，其中
$$
q(p)=b_D\sqrt{p-(1-b_D^2)p^2}.
\tag{16.10}
$$
$m\ge1$ 给 $0<x_D\le t$、$0<b_D\le t/\sqrt m\le1/64$。对 (16.10) 的二次式配方，其最大点 $p=[2(1-b_D^2)]^{-1}$ 位于 $[0,1]$，故
$$
\max_{0\le p\le1}q(p)=g_D<\zeta.
\tag{16.11}
$$
同时旋转协变性给出任意 $h,v$ 的相同公式；这些坐标及最大化只用于证明，不进入程序。

复用 (13.19)，并把相同非参考解码处理包括在内，有某理想完整 $K_0$ 态 $\Xi^i=\Xi^i_{n,h}$ 使
$$
D_{\rm tr}(\eta,\tau_h\otimes\Xi^i)\le e,\qquad
D_{\rm tr}(\eta_{K_0},\Xi^i)\le e.
$$
对第一对态施行同一个 $\mathcal T_v\otimes\operatorname{id}_{K_0}$。由收缩性及经过 $\rho_{h,v}\otimes\Xi^i$、$\tau_h\otimes\Xi^i$ 的三角不等式，
$$
\Delta_{\rm dep}(n,h)\le e+q(p)+e\le2e+g_D.
\tag{16.12}
$$
两项 $e$ 分别控制完整态与其实际边缘，不能以理想边缘替代后略去后一项。原元组满足 $e<1/(800000N)$、$\zeta<1/(128000N)$，故 $2(e+\zeta)<1$；结合 (16.11) 得 (16.6)。最后，把同一局部节点分别施于 $\Omega_{\rm raw}$ 和 $\tau_h\otimes\omega_{\rm raw}$，第二态成为 $\tau_h\otimes\omega_{\rm dep}$，收缩性给出所述逐点实际不等式。$\square$

**命题 16.3（非空原始子族上的严格实际最坏情形比较；repo-derived）。** 对仍满足全部原始条件且另有
$$
\sqrt m\ge\frac{40M}{t}
\tag{16.13}
$$
的元组，同一固定元组、同一全体原始 $n,h$ 上的两个实际上确界满足
$$
\bar\delta_{\rm dep}<\frac{61}{100}b_D
<\frac{13}{20}b_D<\bar\delta_{\rm raw}.
\tag{16.14}
$$
这个原始子族非空：对每个允许的整数 $N$，可取
$$
m=(2560M)^2=655{,}360{,}000N^2,\qquad D=m+1,\qquad j=m/2.
\tag{16.15}
$$

**证明。** 取 (14.12) 在半径 $1/3$ 开圆盘内的场。它属于 $C^2$，前两个坐标保证秩二，原点两轴导数范数均为一，轴上二阶导数范数为 $(1-s^2)^{-3/2}<2$（$|s|\le1/4$），故满足完整原始场承诺。选一个 $h\perp v=n(+d e_x)$，于是 $p=1/2$；这是上确界中的见证，两个程序均不以它为输入。

对实际获取态和上述理想乘积态施行同一交换，得到
$$
D_{\rm tr}(\Omega_{\rm raw},\Gamma)\le e,\qquad
\Gamma=|w\rangle\langle w|\otimes\Xi^i.
$$
在完整 $R K_0 S_t$ 上令 $\mathsf P=\tau_h\otimes I$。任意 Hermitian $X$ 满足
$$
\|\mathsf P X(I-\mathsf P)\|_1\le\frac12\|X\|_1,
\tag{16.16}
$$
因为 $Z=2\mathsf P-I$ 是幺正，且
$\|X-ZXZ\|_1=4\|\mathsf P X(I-\mathsf P)\|_1\le2\|X\|_1$。
实际乘积 $\tau_h\otimes\omega_{\rm raw}$ 的该交叉块为零，故 (16.16) 先用于返回差、再用于 $\Omega_{\rm raw}-\Gamma$，给出
$$
\begin{aligned}
\Delta_{\rm raw}(n,h)
&\ge\|\mathsf P\Omega_{\rm raw}(I-\mathsf P)\|_1\\
&\ge\|\mathsf P\Gamma(I-\mathsf P)\|_1-e\\
&=b_D\sqrt{\frac12\left(1-\frac{b_D^2}{2}\right)}-e
>\frac7{10}b_D-e.
\end{aligned}
\tag{16.17}
$$
最后一步用 $b_D\le1/64$。这里保留了实际 $\omega_{\rm raw}$ 和全部输出，直接估计原协议的交叉块，未把任何原始口下界经收缩移植到处理后的输出。

同一范围内 $\sqrt{1-b_D^2}>63/64$，故
$g_D<32b_D/63<51b_D/100$。又 $\sin x_D\ge x_D/2$，所以
$$
b_D\ge\frac{t}{2\sqrt m},\qquad
\frac{e}{b_D}<\frac{2M}{t\sqrt m}\le\frac1{20}.
$$
将此代入 (16.12) 和 (16.17)，分别得到 (16.14) 两端的严格界。这一步用原协议的实际下见证与新协议的统一上界分离上确界，并非仅由两个充分证书的大小推出严格实际改善。式 (16.15) 是整数 $m$、允许的半整数 $j$，满足 (16.13) 和 $D\ge8{,}000{,}000N^2$，其余 $L,Q$ 及承诺保持原值，故确为非空原始子族。$\square$

**资源与来源范围。** 命题 13.2 的日程、有限解码和完整资源逐项复用：仍为 $M$ 次获取槽、$M$ 次 $\mathcal C$、包含终端交换的 $M+1$ 次实际 $R$ 接触以及 $18N+1$ 次场重置；唯一增加是一项固定非参考 qubit 到 qubit 的约化 CPTP 节点。全部原始记录与实际保留输出仍在 $K$，没有额外 $R$ 操作、不可见初始纯化、未知方向程序或后选择。

局部保迹、伴随保单位、迹距离收缩及二阶 Hermitian 矩阵和交叉块范数均为成熟输入；局部边缘保持亦见本卷定理 4.3，收缩论证见定理 12.3 的证明。Kretschmann–Schlingemann–Werner 的[原文第 II.1 节、式 (4)](https://arxiv.org/html/quant-ph/0605009v1)给出这里使用的通道对偶语义，不调用其信息—扰动或扩张连续性定理。总自旋投影及角动量系数沿用 (13.5)、(13.14)，对应 Bartlett–Rudolph–Spekkens–Turner 的[原文第 III 节及附录 B、式 (39)–(40)](https://arxiv.org/html/quant-ph/0602069v2)，不移用其丢弃探针后的寿命指标。本节 repo-derived 的范围限于原任务下固定终端节点的完整对应、(16.5) 的实际边缘表达及分开证明的两个有限比较，不主张历史新颖性或文献穷尽。

本节没有消去终端作用后的参考边缘项 $q(p)$。§15 的原始完整输出、原生访问类中的共同可达与必要界缺口仍未解决；这里没有给出均匀 $O(M/D)$ 控制器、更强的全类必要尺度、最优系数或完整可达区域。场源、指定门、校准、实际噪声汇和物理时钟仍是条件模型前提；额外实际输出的资格限制属于定理的适用域。

## 追加锚（本行以下为增补区）

## 17. 两个原生槽的相关补偿与均匀实际返回

**定义 17.1（原始任务内的固定补偿器）。** 固定定义 13.1 的任一元组：$N\ge N_*=8{,}388{,}608{,}000$，$M=L=10N$，$Q=18N+1$，$D=2j+1\ge8{,}000{,}000N^2$。仍取 $d=1/64$、$\tau_0=1$、$t=d\tau_0=1/64$、$r=1/4$、$B_{\rm field}=2$、$G=1$、$\epsilon=1/16$、$\beta=1/100$。场 $n:U\to S^2$ 在包含两条完整闭 $r$ 轴段的开集上为 $C^2$、秩二，并满足 (13.2) 的全部导数界。每次场重置独立供应 $\rho_n(z)=(I+n(z)\cdot\sigma)/2$。唯一初始未知方向资源仍为 $R=\operatorname{Sym}^{2j}(\mathbb C^2)$ 上的 $\tau_h$；固定 $n$ 后，全部非参考来源的完整律对所有 $h$ 相同。目标仍是初始方向的 (13.3)，访问仍限于至多 $L$ 个 (13.6) 原生槽、一次 (13.9) 强制终端交换，其余操作在 $R$ 上为恒等。

采用定义 13.1、假设 12.2 允许的有限因果非 $R$ 处理，以及定义 16.1 的实际约化节点语义。写 $\mathcal E(X)=\operatorname{Tr}(X)I_2/2$，所有被替换的 qubit 仍留在实际口。对三枚非参考 qubit $B,A,F$，置
$$
\begin{aligned}
r_t&=1-\cos t,\qquad s_t=\sin t,\qquad c_t=r_t+i s_t=1-e^{-it},\\
O_i&=-r_t\left[\sigma_{F,i}
+\frac{\sigma_{B,i}(\sigma_A\cdot\sigma_F)
+\sigma_{A,i}(\sigma_B\cdot\sigma_F)}2\right]
+\frac{s_t}{2}\bigl[(\sigma_B-\sigma_A)\times\sigma_F\bigr]_i
\quad(i=x,y,z),\\
\Phi(X)&=\frac{\operatorname{Tr}(X)I_2+
                 \sum_i\operatorname{Tr}(O_iX)\sigma_i}{2},\\
\widehat\Phi(X)&=\frac{I_B}{2}\otimes\Phi(X)_A\otimes\frac{I_F}{2}.
\end{aligned}
\tag{17.1}
$$
不同 qubit 的算子乘积隐含张量积，点积、叉积使用同一固定定向标架。这是一个固定矩阵通道的定义，不含实际 $n,h,D$ 的程序参数。

补偿后缀 $\mathsf S$ 依次如下。准备固定 singlet $|\psi^-\rangle_{BA}=(|\uparrow\downarrow\rangle-|\downarrow\uparrow\rangle)/\sqrt2$，将 $B$ 送入第一个原生槽；对 $H$ 在原始标签基退相干，保留 $H,E$ 和原始符号，仅在负标签上交换 $B,A$。在 $+d e_x$ 独立重置一枚场令牌 $F$，对 $BAF$ 施行 $\widehat\Phi$；将输出 $A$ 送入第二个原生槽，对其 $H$ 作同样退相干，完整保留两组原生记录及其实际副本。随后对 $B,A,F$ 各施行 $\mathcal E$，保留这三枚输出。最后在 $+d e_x$ 另取一枚未经改动的独立纯场令牌 $S_t$，执行规定的 $U_{\rm term}=\exp[-itJ\cdot\sigma/(D-1)]$，再对同一 $S_t$ 施行 $\mathcal E$ 并保留它。没有条件选支或新增校正读数。

记 $Z$ 为两个补偿槽的原始成对标签 $H,E$ 及全部确定性符号副本；$\pi_Z$ 是四个合法历史的均匀比较态，未要求实际标签均匀。固定程序、路由和步进寄存器一并保留；若它们复制标签，归入 $Z$。以 $\sigma_0$ 记三枚替换量子输出和其余固定工作输出的联合固定态；不另外准备工作寄存器的直接实现中，$\sigma_0=(I_2/2)^{\otimes3}$。终端后置 $\sigma_1=\sigma_0\otimes I_{S_t}/2$。这里指定的约化节点没有另行声明的实际环境输出。另一实现若产生额外实际噪声、指针或工作输出，必须纳入 $K$ 并重证完整口界；形式 Kraus 指标及证明用扩张不自动增加实际口，实际存在的输出也不能以此删去。有限复合、CP 仪器和自旋程序仍分别采用 OTF001 假设 2.5–2.7、定理 7.2 与 OTF002 定义 11.1；非 $R$ 处理的许可来自原访问合同，不来自 OTF003 第 11 节所区分的生成代数闭包。

**引理 17.2（固定通道及相关块的三个收缩）。** 式 (17.1) 是对任意相关输入适用的 CPTP 通道。仅在证明坐标中取 $h=z$，令
$$
\chi=|\uparrow\downarrow\rangle_{BA},\quad
\psi=|\uparrow\uparrow\rangle_{BA},\quad
\rho_v=(I+v\cdot\sigma)/2,\quad
a=(v_x-i v_y)/2,
$$
$$
A_0=\Phi(|\chi\rangle\langle\chi|\otimes\rho_v),\qquad
B_0=\Phi(|\chi\rangle\langle\psi|\otimes\rho_v).
$$
则
$$
(A_0)_{\uparrow\uparrow}=(A_0)_{\downarrow\downarrow}=\frac12,\quad
(A_0)_{\uparrow\downarrow}=-c_ta,\quad
(B_0)_{\uparrow\uparrow}=-\frac{c_ta}{2},\quad
(B_0)_{\downarrow\downarrow}=\frac{c_ta}{2},\quad
\operatorname{Tr}B_0=0,\quad \|B_0\|_1<1.
\tag{17.2}
$$

**证明。** 每个 Pauli 点积的范数至多三，每个叉积分量中的四项范数各至多一，故
$$
\|O_i\|\le4r_t+2|s_t|,\qquad
\sum_i\|O_i\|\le12r_t+6|s_t|
\le6t^2+6t=\frac{195}{2048}<1.
\tag{17.3}
$$
输出因子在前的非归一 Choi 矩阵为
$$
C_\Phi=\frac{I_2\otimes I_8+\sum_i\sigma_i\otimes O_i^{\mathsf T}}2
\ge\frac{1-195/2048}{2}I_{16}>0,\qquad
\operatorname{Tr}_{\rm out}C_\Phi=I_8.
\tag{17.4}
$$
由 OTF001 定理 7.2 的 Choi–Kraus 对应及有限酉延拓，$\Phi$ 是固定有限 CPTP 节点；张量附上固定态给出 $\widehat\Phi$。这仅复用标准有限 CP 理论，不赋予直接作用于 $R$ 的恢复操作，也不把证明用延拓宣布为实际返回实现。

在 $|\chi\rangle\langle\chi|\otimes\rho_v$ 上，三个 Pauli 收缩分别为 $h,-h,v$。代入 $O_i$ 得输出 Bloch 向量
$$
-r_t[v-(h\cdot v)h]+s_t(h\times v),
\tag{17.5}
$$
从而得到 $A_0$ 的三个矩阵元。对 $|\chi\rangle\langle\psi|\otimes\rho_v$，$A$ 腿的 Pauli 收缩为 $q=(1,-i,0)$，其迹为零，故
$$
\operatorname{Tr}[O_z(|\chi\rangle\langle\psi|\otimes\rho_v)]
=-\frac{r_t}{2}q\cdot v-\frac{s_t}{2}(q\times v)_z
=-c_ta.
\tag{17.6}
$$
这里 $q\cdot v=2a$、$(q\times v)_z=i q\cdot v$。输出迹为零即给两份相反的对角元。又 $\||\chi\rangle\langle\psi|\otimes\rho_v\|_1=1$，由 (17.1) 和迹范数三角不等式，
$\|B_0\|_1\le\sum_i\|O_i\|<1$。点积和叉积使 $O$ 在同时定向旋转下为向量，因此通道协变；$h=z$ 只是证明的共同坐标变换，没有实施未知方向旋转。$\square$

**定理 17.3（四条保留历史的补偿界）。** 对任意 $h,v\in S^2$，从独立初始参考 $\tau_h$ 运行定义 17.1 的后缀，以 $v$ 供应两枚独立纯场令牌。其实际完整输出 $\Omega_c$ 满足
$$
\left\|\Omega_c-\tau_h\otimes\pi_Z\otimes\sigma_1\right\|_1
<\frac{73}{D},\qquad
D_{\rm tr}\!\left(\Omega_c,\tau_h\otimes\operatorname{Tr}_R\Omega_c\right)
<\frac{80}{D}.
\tag{17.7}
$$
其中 $D_{\rm tr}=\|\cdot\|_1/2$；所有补偿量子输出、原生记录与实际副本均包含在右端口中。

**证明。** 写 $m=D-1$、$\delta=1/D$、$\lambda=\sqrt m/D$，仅取证明坐标 $h=z$，$e=|j,j\rangle$、$f=|j,j-1\rangle$、$\tau_e=|e\rangle\langle e|$、$\tau_f=|f\rangle\langle f|$。由既有 (13.14)，第一槽退相干并按负标签交换后，两条未归一向量为
$$
x_+=\frac{e\chi-\delta e\chi'-\lambda f\psi}{\sqrt2},\qquad
x_-=\frac{(1-\delta)e\chi-\lambda f\psi}{\sqrt2},
\qquad \chi'=|\downarrow\uparrow\rangle.
\tag{17.8}
$$
负分支省去的只是整体负号；实际概率为 $(1+\delta)/2$、$(1-\delta)/2$，没有重新归一。令 $w=(e\chi-\lambda f\psi)/\sqrt2$，则 $\|x_b-w\|=1/(\sqrt2D)$，$\|x_b\|,\|w\|\le1$。利用
$\|xx^\dagger-ww^\dagger\|_1\le(\|x\|+\|w\|)\|x-w\|$，
两条历史合计差小于 $3/D$；再去掉 $ww^\dagger$ 的尾对角项合计只需 $\lambda^2\le1/D$。因此第一槽完整态距下式的迹范数小于 $4/D$：
$$
\frac12\sum_{b=\pm}|bb\rangle\langle bb|_{H_1E_1}\otimes
\left[\tau_e\otimes|\chi\rangle\langle\chi|
-\lambda\bigl(|e\rangle\langle f|\otimes|\chi\rangle\langle\psi|
+\text{h.c.}\bigr)\right].
\tag{17.9}
$$
实际参考边缘恰为 $(1-\lambda^2)\tau_e+\lambda^2\tau_f$；这个小的边缘误差没有使联合态成为乘积。

经 $\widehat\Phi$ 后，(17.9) 方括号的参考—探针对应为
$$
G=\tau_e\otimes A_0-
\lambda\bigl(|e\rangle\langle f|\otimes B_0+\text{h.c.}\bigr).
\tag{17.10}
$$
以上比较算子一般不是正态，尤其不得把 $\tau_e-\lambda K$ 当成所制备的态。它们只用于线性 Hermitian 比较；实际态始终由指定准备、原生槽和 CPTP 节点产生。保迹正映射由正负分解收缩 Hermitian 算子的迹范数，故这些完整余项可以经真实后缀传播。

先计算第二槽对 $\tau_e\otimes A_0$ 的作用，包含退相干和探针替换，略去相同固定量子因子。两份参考块由 (13.14) 精确给出
$$
\begin{aligned}
G_+^{(0)}
&=\left(\frac12+\frac1{2D^2}\right)\tau_e
+\frac{\lambda^2}{2}\tau_f
+\lambda\bigl((A_0)_{\uparrow\downarrow}|e\rangle\langle f|
+\text{h.c.}\bigr),\\
G_-^{(0)}
&=\frac{m^2}{2D^2}\tau_e+\frac{\lambda^2}{2}\tau_f.
\end{aligned}
\tag{17.11}
$$
相对于各自的 $\tau_e/2$ 和所显示交叉项，剩余对角块的总迹范数为 $(2D-1)/D^2<2/D$，因而也小于 $4/D$。

为估计 (17.10) 的交叉输入，令 $W_1=\operatorname{span}\{e,f\}$、$P_\pm=|\uparrow/\downarrow\rangle\langle\uparrow/\downarrow|$。由 (13.5) 的角动量系数，
$$
\|(\Pi_b-I_R\otimes P_b)P_{W_1\otimes S}\|
\le\frac2D+\sqrt2\lambda<4\lambda.
\tag{17.12}
$$
具体地，除 (13.14) 外，$\Pi_+(f\uparrow)=(1-\delta)f\uparrow+\lambda e\downarrow$，而
$\Pi_+(f\downarrow)=2\delta f\downarrow+
\sqrt{2(m-1)}\,|j,j-2\rangle\uparrow/D$；末项不存在时取零。把 $\Pi_b$ 与 $I_R\otimes P_b$ 各按 $|bb\rangle_{H_2E_2}$ 堆叠成原生和理想等距 $V,W$，得到 $\|(V-W)P_{W_1\otimes S}\|<6\lambda$。交叉输入的迹范数为 $2\lambda\|B_0\|_1$，展开 $VYV^\dagger-WYW^\dagger$ 后，两份完整仪器输出合计差小于
$24\lambda^2\|B_0\|_1\le24/D$。此估计同时覆盖两个原始标签；后续退相干、量子替换均收缩该差。

理想交叉输入在两个标签的 $e/f$ 系数分别为 $-\lambda(B_0)_{\uparrow\uparrow}$ 和 $-\lambda(B_0)_{\downarrow\downarrow}$。结合 (17.11) 及 (17.2)，第二槽两份首阶系数分别为
$$
\lambda\bigl[(A_0)_{\uparrow\downarrow}
-(B_0)_{\uparrow\uparrow}\bigr]=-\frac{\lambda c_ta}{2},
\qquad
-\lambda(B_0)_{\downarrow\downarrow}=-\frac{\lambda c_ta}{2}.
\tag{17.13}
$$
这不是在不同原始标签间平均相反误差。连同第一槽的两份 $1/2$ 比较权重，四条未归一历史各有相同的参考块 $(\tau_e-\lambda K_t)/4$，其中
$$
K_t=c_ta|e\rangle\langle f|+\overline{c_ta}|f\rangle\langle e|.
$$
第一槽余项、(17.11) 对角余项及交叉仪器余项相加，给第二槽及替换后的实际完整态 $\Theta$：
$$
\left\|\Theta-(\tau_e-\lambda K_t)\otimes\pi_Z\otimes\sigma_0\right\|_1
\le\frac{4+4+24}{D}=\frac{32}{D}.
\tag{17.14}
$$
实际四条历史的概率偏离 $1/4$ 也包含在这个联合界中，没有重置原始标签。

最后令 $\gamma=tD/m$、$z=e^{i\gamma}$、$c_\gamma=1-e^{-i\gamma}$，并以 $c_\gamma$ 替换 $K_t$ 中的 $c_t$ 定义 $K_\gamma$。由原终端谱分解 (16.8)，略去整体相位后 $U_{\rm term}=\Pi_++z\Pi_-$。终端 qubit 的实际替换使完整参考因子准确为
$$
\mathcal T_v(X)=\operatorname{Tr}_{S_t}
[U_{\rm term}(X\otimes\rho_v)U_{\rm term}^\dagger],
$$
并在实际口附上 $I_{S_t}/2$，正是 (16.5) 的相关输入语义。由
$e\downarrow\mapsto(1+mz)e\downarrow/D+\lambda(1-z)f\uparrow$，得到
$$
\mathcal T_v(\tau_e)=\tau_e+\lambda K_\gamma
+\lambda^2|c_\gamma|^2(\rho_v)_{\downarrow\downarrow}(\tau_f-\tau_e).
\tag{17.15}
$$
取 $U_0=I_R\otimes(P_++zP_-)$。(17.12) 给
$\|(U_{\rm term}-U_0)P_{W_1\otimes S_t}\|\le4|c_\gamma|\lambda$；
而 $\|K_t\|_1=2|c_ta|\le|c_t|$，$U_0$ 的参考边缘作用为恒等。因此
$$
\|\mathcal T_v(K_t)-K_t\|_1\le8|c_\gamma||c_t|\lambda,\qquad
\lambda\|K_\gamma-K_t\|_1
\le\lambda|\gamma-t|=\frac{t}{D\sqrt m}\le\frac{t}{D}.
\tag{17.16}
$$
由 $|c_\gamma|,|c_t|\le2$、$\lambda^2\le1/D$，(17.15) 的尾对角项和 (17.16) 的交叉演化项分别至多 $8/D$、$32/D$，故
$$
\|\mathcal T_v(\tau_e-\lambda K_t)-\tau_e\|_1
\le\frac{40+t}{D}.
\tag{17.17}
$$
把 (17.14) 余项经同一个实际终端通道传播，得到完整输出与真正乘积态
$\tau_e\otimes\pi_Z\otimes\sigma_1$ 的迹范数差至多 $(72+t)/D<73/D$。对其实际 $K$ 边缘再用一次收缩性，两项半迹范数的三角不等式给实际边缘返回误差小于 $73/D<80/D$。协变性把计算送到全部 $h,v$。$W_1$ 只限制比较项，实际更高降低数分量均已包含在完整余项内，不假定真实运行永久支撑于 $W_1$。$\square$

**定理 17.4（原始均匀任务的逆维数充分证书）。** 在定义 17.1 的实际约化口假设下，对每个原始允许元组，存在一个与实际 $n,h$ 无关的有限控制器和固定解码器，对全部原始场与全部 $h$ 满足
$$
\begin{aligned}
\Pr[\|\widehat D-D_h(n)\|_\infty\le1/16]&\ge99/100,\\
D_h(n)&=\left(\frac{h\cdot[n(0)\times n_x(0)]}{2},
\frac{h\cdot[n(0)\times n_y(0)]}{4},0,\frac{h\cdot n_y(0)}2\right),\\
\sup_{n,h}D_{\rm tr}(\Omega_{n,h},
 \tau_h\otimes\operatorname{Tr}_R\Omega_{n,h})
&\le\min\left\{1,\ 2\cdot10(N-1)\kappa_D+\frac{80}{D}\right\}
\le\min\left\{1,\frac{10M}{D}\right\},
\qquad \kappa_D=\frac{2D-1}{2D^2}.
\end{aligned}
\tag{17.18}
$$
同一通道 (17.1) 对所有元组固定。协议只准备一次 $R$，不重置它；实际使用 $10N-8\le L$ 个原生槽、$18N-16\le Q$ 次场重置及恰一次规定终端交换，包含终端的实际 $R$ 接触数为 $10N-7$。

**证明。** 在既有十设置获取中，每设置取 $N'=N-1$ 个样本，完整复用 (13.7)–(13.8)、(13.20)–(13.24) 的仪器和均值差分解码，仅把均值的已知分母改成 $N'$。不重证既有获取理论：(13.14)–(13.19) 的一槽计算与理想前缀混合链给含全部实际获取输出、记录和解码工作区的前缀态 $\eta$ 及某理想完整态 $\Xi^i$ 满足
$$
D_{\rm tr}(\eta,\tau_h\otimes\Xi^i)
\le e_a:=10(N-1)\kappa_D.
\tag{17.19}
$$
复用定理 13.1 证明中的场偏差和宽度八尾估计，对 $\eta_0=1/2048$ 有
$$
\Pr\left[\|\widehat D-D_h(n)\|_\infty>
 \frac1{128}+\frac{\eta_0}{d}\right]
\le20e^{-N'\eta_0^2/32}+e_a<\frac1{100}.
\tag{17.20}
$$
确实 $N'\eta_0^2\ge2000-\eta_0^2>1999$，故指数项小于 $1/1000$，且
$e_a<M/D\le1/(800000N)<1/1000$；阈值为 $5/128<\epsilon$。这直接覆盖 $N=N_*$ 及维数端点，并未对 $N'<N_*$ 误用定理的元组前件。接上 $\mathsf S$ 后，所有旧获取寄存器上均为恒等作用。整个确定性后缀保迹，故旧寄存器的完整边缘及同一解码事件精确保留，复用本卷定理 4.3 的局部边缘保持。

在 (17.19) 两个输入后接同一实际后缀；对乘积输入，完整输出为 $\Omega_c\otimes\Xi^i$，距真实输出至多 $e_a$。实际 $K$ 边缘的相应差也至多 $e_a$。由定理 17.3 及三角不等式，始终与各自实际边缘比较，得到
$$
\Delta_{n,h}\le e_a+\frac{80}{D}+e_a,\qquad
2e_a+\frac{80}{D}\le\frac{2M+60}{D}\le\frac{10M}{D}.
\tag{17.21}
$$
最后用 $\Delta_{n,h}\le1$ 得 (17.18)。中间没有以 $\Xi^i$ 替代最终实际边缘，也没有把理想前缀当成实际参考重置。

资源逐项为：获取的原生槽及 $\mathcal C$ 各 $10(N-1)$ 次，部分 SWAP 为 $8(N-1)$ 次，标量受控 SWAP 为 $10(N-1)$ 次，标量 Hadamard 为 $20(N-1)$ 次，标量读出为 $10(N-1)$ 次，场重置为 $18(N-1)$ 次。后缀增加两个原生槽、一枚 $F$ 和一枚规定终端场令牌，无额外 $R$ 操作；固定 singlet、一次按标签交换、$\widehat\Phi$ 和明示替换均只作用于非 $R$ 系统。于是取得定理所列实际调用数，未使用的上限没有算成已执行调用。

实际 $K$ 保留全部 $10(N-1)$ 组获取 $H,E$ 和原始 $b,Y$，每枚测后探针、每次部分 SWAP 的两份输出、全部场令牌、标量测试 qubit、实际指针与复制/读出系统、二十个 $[0,N-1]$ 计数器、记忆、程序/路由/步进/解码工作区及所声明旁观者；后缀还保留 $B,A,F,S_t$、两组新 $H,E$ 和每份原始符号副本。直接约化实现的获取探针、场及 singlet 输出小计为
$10(N-1)+18(N-1)+2+2=28N-24$ 枚 qubit，另有 $10(N-1)$ 枚标量测试 qubit、原生记录、全部工作寄存器及维数 $D$ 的参考。这个小计不是总辅助维数或全部基本门成本。

式 (17.13)–(17.17) 给出的是指定原生访问下实际生成再使用相关块的充分构造；§16 的终端替换本身未消去 (17.15) 的参考交叉项。既有自旋系数、获取、标准 CP 理论、收缩性及终端约化语义分别由 (13.14)–(13.24)、OTF001 定理 7.2、本卷定理 12.3 的证明及 (16.5)、(16.8) 供应。这里的结论限于这些数学接口及定义 17.1 的实际口；相干参考准备、纯场源、指定耦合、控制与噪声节点、校准及物理钟仍是模型前提。它不延伸为另一实现的额外实际输出定理，不给定理 14.1 的实际完整等距类添加免费约化，也不改变定理 14.3–14.4 的一般 CPTP 必要界或定理 12.3 的控制器最坏情形量词；不含一般控制器分类、两槽必要性、最优系数或历史优先权结论。$\square$

## 追加锚（本行以下为增补区）

## 18. 固定完整通道的弱信息细化与联合返回

**定义 18.1（原始合同与完整输出）。** 固定定义 13.1、17.1 的原始合同，包括整数 $N\ge8{,}388{,}608{,}000$、$M=L=10N$、$Q=18N+1$、$j\in\frac12\mathbb Z_{>0}$、$D=2j+1\ge8{,}000{,}000N^2$，以及
$$
d=t=\frac1{64},\quad \tau_0=1,\quad r=\frac14,\quad
B_{\rm field}=2,\quad G=1,\quad \epsilon=\frac1{16},\quad\beta=\frac1{100}.
\tag{18.1}
$$
场 $n:U\to S^2$ 在包含两条完整闭 $r$ 轴段的开集上为 $C^2$、秩二；对 $a=x,y$、$|u|\le r$，有 $\|n_{aa}(u e_a)\|\le2$，且 $\|n_x(0)\|,\|n_y(0)\|\le1$。每次重置独立供应纯态 $\rho_n(z)=(I+n(z)\cdot\sigma)/2$。唯一初始未知方向资源为 $R=\operatorname{Sym}^{2j}(\mathbb C^2)$ 上的 $\tau_h$，$h\in S^2$；它只准备一次，初始与其余输入独立。固定 $n$ 后，非 $R$ 来源的完整律对所有 $h$ 相同，设备、辅助准备、有限因果控制器和解码器均不以实际 $n,h$ 为参数，不接入未供应的纯化。目标仍为初始方向的
$$
D_h(n)=\left(\frac{h\cdot[n(0)\times n_x(0)]}{2},
\frac{h\cdot[n(0)\times n_y(0)]}{4},0,\frac{h\cdot n_y(0)}2\right).
\tag{18.2}
$$
访问只允许至多 $L$ 个 (13.6) 原生槽和恰一次 (13.9) 强制终端交换 $\exp[-itJ\cdot\sigma/(D-1)]$；其余操作在同一标记 $R$ 上为恒等，不读取、旋转、拆分、重置或替换它。有限张量复合、CP 仪器、自旋准备及实际非参考处理仍采用定义 17.1 的全部前提。

记定理 17.4 的指定协议为 $\mathsf P_{17}$：十设置获取各取 $N-1$ 个样本，使用 (13.24) 的同一解码器及已知分母 $N-1$，再接定义 17.1 的两槽补偿后缀。记其实际完整输出为 $\Omega_{17}$，非参考口为 $K_{\rm old}$。该口保留全部获取 $H,E,b,Y$、测后探针、每次部分 SWAP 的两个输出、场输出、标量测试 qubit、实际指针和复制/读出系统、二十个计数器、记忆、程序/路由/步进/解码工作区及声明的旁观者；还保留补偿的两组 $H,E$、全部原始副本和 $B,A,F,S_t$。这里采用定义 16.1、17.1 的实际约化口语义；形式扩张不是额外实际输出，另有实际输出的实现须另给完整口估计。

**定义 18.2（固定的二支细化）。** 精确取 (17.1) 的原矩阵 $O_i,\Phi$ 及整个三线输出通道 $\widehat\Phi(X)=I_B/2\otimes\Phi(X)_A\otimes I_F/2$。在假设 12.2 允许的固定已知标架中选定单位向量 $k$，令
$$
W=\mathrm{SWAP}_{BA},\qquad Q_0=W\otimes(k\cdot\sigma_F),\qquad
\mu=I_{BAF}/8,\qquad \alpha=1/2.
$$
引入固定正交基 $|s\rangle_T$，$s=\pm1$，并置 $Z_T=\sum_s s|s\rangle\langle s|$，
$$
\begin{aligned}
\Gamma_s(X)&=\frac{\widehat\Phi(X)}2+
                 \frac{s\alpha}{2}\operatorname{Tr}(Q_0X)\mu,\\
\Gamma(X)&=\sum_s\Gamma_s(X)\otimes|s\rangle\langle s|
=\widehat\Phi(X)\otimes\frac{I_T}{2}
 +\alpha\operatorname{Tr}(Q_0X)\mu\otimes\frac{Z_T}{2}.
\end{aligned}
\tag{18.3}
$$
$\Gamma$ 的输入维数为八、输出维数为十六，矩阵不依赖 $N,D,n,h$。协议 $\mathsf P_\Gamma$ 只把 $\mathsf P_{17}$ 的这一个 $\widehat\Phi$ 节点换成 $\Gamma$；第二原生槽、$B,A,F$ 的原替换、独立且未经改动的终端令牌和终端交换及替换均保持原样，之后恒等作用于 $T$，不以 $s$ 路由或选支。声明本节点的实际输出恰为 $B,A,F,T$。最终
$$
K'=K_{\rm old}\otimes T,\quad
\omega_\Gamma=\operatorname{Tr}_R\Omega_\Gamma,\quad
\Delta_\Gamma=D_{\rm tr}(\Omega_\Gamma,\tau_h\otimes\omega_\Gamma),
\qquad D_{\rm tr}=\tfrac12\|\cdot\|_1.
\tag{18.4}
$$
全部原始历史和两个部分 SWAP 输出始终在此口中。

**定理 18.3（可达细化的完整联合证书；repo-derived）。** 在定义 18.1–18.2 的全部条件下，$\Gamma$ 为 CPTP，且对每个输入矩阵及任意相关辅助系统，偏迹 $T$ 精确恢复整个 $\widehat\Phi$，从而 $\operatorname{Tr}_T\Omega_\Gamma=\Omega_{17}$。令 $v=n(+d e_x)$、$v_k=k\cdot v$、$p_b=(1+b/D)/2$。即使真实获取前缀中的参考已受扰动并与记忆相关，实际最终边缘仍满足
$$
\begin{aligned}
\rho_{H_1E_1T}
 &=\sum_{b=\pm1}p_b|bb\rangle\langle bb|\otimes
                  \frac{I_T-b\alpha v_k Z_T/D}{2},\\
\Pr(b,s)&=\frac{p_b}{2}(1-sb\alpha v_k/D),\qquad
\rho_T=\frac{I_T-\alpha v_k Z_T/D^2}{2}.
\end{aligned}
\tag{18.5}
$$
这里的信息来自场；这个显示边缘在固定场时独立于 $h$。对从独立 $\tau_h$ 开始的补偿后缀，沿用定义 17.1 的 $\pi_Z,\sigma_1$，其完整输出满足
$$
\left\|\Omega_{c,\Gamma}
 -\tau_h\otimes\pi_Z\otimes\sigma_1\otimes I_T/2\right\|_1
 <\frac{74}{D},\qquad
D_{\rm tr}(\Omega_{c,\Gamma},\tau_h\otimes\operatorname{Tr}_R\Omega_{c,\Gamma})
 <\frac{80}{D}.
\tag{18.6}
$$
对真实获取前缀接此后缀，同一协议在全部原始场、全部 $h$ 和全部原始元组（包括 $N,D$ 端点）上有
$$
\begin{aligned}
\Pr[\|\widehat D-D_h(n)\|_\infty\le1/16]&\ge99/100,\\
\sup_{n,h}\Delta_\Gamma
&\le\min\{1,2e_a+80/D\}\le\min\{1,10M/D\},\\
e_a&=10(N-1)\kappa_D,\qquad \kappa_D=\frac{2D-1}{2D^2}.
\end{aligned}
\tag{18.7}
$$
并且存在满足完整场承诺的两个场 $n_+,n_-$，使同一个任意 $h$ 的真实运行满足
$$
D_{\rm tr}(\rho_T^+,\rho_T^-)=\frac1{2D^2},\qquad
D_{\rm tr}(\rho_{H_1E_1T}^+,\rho_{H_1E_1T}^-)=\frac1{2D}.
\tag{18.8}
$$
这些分离随 $D$ 消失，只证明该可达场族上的非恒定性，不给出一致信息量、场重建、固定场的 $h$ 估计或相对于整个旧 $K$ 的额外信息。

**证明。** 先复用 (17.3)–(17.4) 的非归一、输出因子在前的 Choi 界。令 $q=195/2048$，则 $C_{\widehat\Phi}\ge(1-q)I_{64}/8$。由于 $Q_0$ 为范数一的 Hermitian 矩阵，
$$
C_{\Gamma_s}=\frac{C_{\widehat\Phi}}2+
 \frac{s\alpha}{2}\mu\otimes Q_0^{\mathsf T}
\ge\frac{1-q-\alpha}{16}I_{64}
=\frac{829}{32768}I_{64}>0.
\tag{18.9}
$$
OTF001 定理 7.2 的有限 Choi–Kraus 对应给完全正性；各支效果为 $(I+s\alpha Q_0)/2$，和为 $I$。故 $\Gamma$ 保迹，而 $\Gamma_++\Gamma_-=\widehat\Phi$ 是全矩阵恒等式，张量任意恒等映射仍成立。后续操作均恒等作用于 $T$，故也给出整个最终旧 $R K_{\rm old}$ 态的精确保持。这是标准仪器扩展的应用：Piani 的 [《Channel Steering》第 II 节定义 1–3、式 (2)](https://arxiv.org/html/1411.0397v1#S2) 中，输入 $C$ 对应输入 $BAF$，旧输出 $B$ 对应输出 $BAF$，附加输出 $A$ 对应 $T$，子通道对应 $\Gamma_s$；第 IX 节区分了输入依赖子通道与输入无关的随机通道。这里不作相干扩展或 steering 主张。

下面计算真正可达的联合差。只在证明坐标取 $h=z$，$k,v$ 也用同一坐标表示；令 $\delta=1/D$、$\lambda=\sqrt{D-1}/D$、$e=|j,j\rangle$、$f=|j,j-1\rangle$。精确复用 (17.8) 的未归一原生向量，$\chi=|\uparrow\downarrow\rangle$、$\chi'=|\downarrow\uparrow\rangle$、$\psi=|\uparrow\uparrow\rangle$：
$$
x_+=\frac{e\chi-\delta e\chi'-\lambda f\psi}{\sqrt2},\qquad
x_-=\frac{(1-\delta)e\chi-\lambda f\psi}{\sqrt2}.
$$
$W$ 交换 $\chi,\chi'$ 并固定 $\psi$；$\langle\chi,W\chi\rangle=\langle\chi',W\chi'\rangle=0$，$\langle\chi,W\chi'\rangle=1$，且 $\psi$ 与这两个向量的全部 $W$ 交叉矩阵元为零。因此实际分支的带符号参考收缩恰为
$$
L_b:=\operatorname{Tr}_{BA}[(I_R\otimes W)x_bx_b^\dagger],\qquad
L_+=-\delta\tau_e+\frac{\lambda^2}{2}\tau_f,\quad
L_-=\frac{\lambda^2}{2}\tau_f.
\tag{18.10}
$$
这些是实际态的线性收缩，未被当成所准备的态。令 $Y_\Gamma,Y$ 为从独立 $\tau_h$ 开始的同一后缀在新、旧节点刚结束时的完整态，暂不写相同的历史副本和固定工作因子。由新鲜 $F=\rho_v$ 的独立性，
$$
\begin{aligned}
Y_\Gamma-Y\otimes I_T/2
 &=\alpha v_k\sum_b|bb\rangle\langle bb|\otimes
                      L_b\otimes\mu\otimes Z_T/2,\\
\|Y_\Gamma-Y\otimes I_T/2\|_1
 &=\alpha|v_k|(\delta+\lambda^2)\le\kappa_D<1/D.
\end{aligned}
\tag{18.11}
$$
两条原始历史均在等式中，没有条件归一化。$W$ 与共同旋转交换，故该式覆盖全部 $h,v$，坐标选择不是程序中的未知方向操作。尤其 $\langle\chi,W\chi\rangle=\langle\psi,W\chi\rangle=0$ 消去了源 (17.9) 的首阶相关项，而有限 $D$ 的 $L_b$ 非零。对任一 $Q_0$ 本征态，(18.3) 相对于 $\widehat\Phi\otimes I_T/2$ 的输出迹范数差却为 $\alpha=1/2$；(18.11) 的小量来自这组可达联合输入，不来自随 $D$ 缩小的通道强度，也不只在不可达输入上改变通道。

用同一个实际 CPTP 后缀传播 (18.11)，保留所有输出和原始记录。定理 17.3 的完整 $73/D$ 乘积比较界直接给 (18.6) 的 $74/D$ 界；没有重作其补偿证明。若该乘积比较的迹范数误差为 $a$，偏迹使其实际 $K'$ 边缘的误差至多 $a$，两项半迹范数的三角不等式给自身实际边缘的返回误差至多 $a<74/D<80/D$。$\pi_Z$ 始终只是四历史比较态，未把实际历史宣布为均匀。

真实前缀无需是乘积。对 (17.19) 的两个完整输入施行同一个新后缀，分别由完整输出和实际边缘产生一项 $e_a$，再用 (18.6) 即得 $\Delta_\Gamma\le2e_a+80/D$。定理 17.4 供应其十设置获取、偏差和尾界 (17.20)、端点处理以及 $2e_a+80/D\le10M/D$；全旧通道恒等式精确保留同一解码事件，给出 (18.7)。这里没有实际重置参考，也未以理想边缘代替最终实际边缘。

为在真正受扰前缀上求侧律，令 $\mathcal J_b:R\to RBA$ 为第一补偿槽的子通道，包含固定 singlet、原生投影、原始标签退相干及负标签 $BA$ 交换。共同旋转保持 singlet、原生投影、路由交换和 $I_R\otimes W$，故 $\mathcal J_b^*(I)$ 与 $\mathcal J_b^*(I_R\otimes W)$ 均与全部自旋 $j$ 旋转交换。不可约性使二者为标量。用上述精确向量求标量，得到
$$
\mathcal J_b^*(I)=p_b I_R,\qquad
\mathcal J_b^*(I_R\otimes W)=c_b I_R,\qquad
c_b=\operatorname{Tr}L_b=-\frac{b p_b}{D}.
\tag{18.12}
$$
这两个效果恒等式也可张量任意旧记忆，故不要求输入参考相干或与记忆独立。固定 $k$ 仅在此不变步骤之后进入 $\Gamma$，未假设 $\Gamma$ 协变。独立 $F$ 和 (18.3) 于是给 $\Pr(b,s)=(p_b+s\alpha v_kc_b)/2$，即 (18.5)。后续操作不作用于 $H_1,E_1,T$，局部保迹边缘保持（定理 4.3）使该律一直成立到终端。每个 $b$ 下两种 $s$ 都有正概率，其律随 $v_k$ 变，因而是输入依赖的随机记录，不能解释为固定独立旗标或原标签的确定性复制；这不声称它优于整个旧输出的信息。

最后取 (14.12) 的 $g(x,y)=(x,y,\sqrt{1-x^2-y^2})$，定义在半径 $1/3$ 的开圆盘上。前两个坐标保证秩二，原点两轴导数范数为一，完整闭 $r$ 轴段上的二阶导数范数为 $(1-u^2)^{-3/2}<2$。取只依赖已知 $k,d$ 的固定正旋转 $O_\pm$，使 $O_\pm g(d,0)=\pm k$，置 $n_\pm=O_\pm g$；全部原始场条件保持。把 $v_k=\pm1$ 代入真实侧律，两种 $T$ 态的差为 $-\alpha Z_T/D^2$，而完整 $H_1E_1T$ 差的各正交块为 $-b p_b\alpha Z_T/D$。取半迹范数并用 $\sum_b p_b=1$，得到 (18.8)。它对同一任意 $h$ 成立，包括两个场产生不同真实获取前缀的情况。$\square$

定理 18.3 的资源条件仍是定理 17.4 的原日程：原生槽 $10N-8\le L$，独立场重置 $18N-16\le Q$，恰一次强制终端交换，共 $10N-7$ 次实际 $R$ 接触；获取的 $\mathcal C$、部分 SWAP、标量受控 SWAP、Hadamard 和标量读出次数分别为 $10(N-1),8(N-1),10(N-1),20(N-1),10(N-1)$。只替换一个固定非 $R$ 节点并多留一个二态寄存器，无额外场源、参考接触或校正读数。全部旧口维数不变，$\dim K'=2\dim K_{\rm old}$；若将 $T$ 编为 qubit，原 $28N-24$ 个获取探针、场及 singlet 输出小计变为 $28N-23$，另有原标量测试、原生记录、工作区和维数 $D$ 的参考，不能把小计当作整体维数或总门数。

本定理的新增关系限于 (18.10)–(18.12) 在源 (17.8) 的实际分支及受扰前缀上的联合后果。原固定补偿器、获取和原返回定理分别由定义 17.1、定理 17.4 和定理 17.3 供应；标准仪器扩展、Choi 余量与有限实现、不变效果的标量性、SWAP 恒等式和收缩性只作中间工具。上述主来源对应不作历史优先权或文献穷尽断言。证书只适用于声明的 $BAF,T$ 约化节点和未改动的后续日程，不是全部环境的返回定理；进一步实际噪声、指针或工作输出必须加入实际口另估。相干参考、独立纯场重置、固定标架、原生耦合、非参考 CP 处理与替换、校准和物理钟仍是前提，不由此取得实验来源。它没有改进原任务的精度、置信度、资源或返回证书，不推得一般控制器或任意扩展的结论，也不改变定理 14.1 的实际完整等距假设、定理 14.3–14.4 的固定场必要界或定理 12.3 的最坏情形量词。

## 追加锚（本行以下为增补区）
## 19. 均匀精度曲线上的实际联合返回必要关系

**定义 19.1（原始合同内的精度曲线）。** 取正有理数 $0<e\le1/100$，请求精度为 $e$、失败率上限为 $b=e$；对数均为自然对数。固定

$$
\begin{aligned}
u_e&=e/8,\qquad
k_e=\left\lceil2048e^{-2}\log(18/e)\right\rceil,\qquad
\ell_e=\left\lceil32768e^{-4}\log(90/e)\right\rceil,\\
N_*&=8{,}388{,}608{,}000,\qquad
N_e=\max\left\{N_*,
 \left\lceil\frac{3k_e+2}{10}\right\rceil,
 \left\lceil\frac{15\ell_e+1}{18}\right\rceil\right\},\\
D_e&=\left\lceil\max\{8{,}000{,}000N_e^2,9k_e/e\}\right\rceil,\qquad
m_e=D_e-1=2j_e,\qquad M_e=L_e=10N_e,\qquad Q_e=18N_e+1.
\end{aligned}
\tag{19.1}
$$

这只指定定义 13.1 合同中的一条曲线及更强的成功请求。公共参数仍为 $d=1/64$、$\tau_0=1$、$r=1/4$、$B_{\rm field}=2$、$G=1$；内部采样步长 $u_e$ 不替代 $d$。场仍遍历全部 $C^2$、秩二映射 $n:U\to S^2$，其中开集 $U$ 包含两条完整闭 $r$ 轴段，并有 $\|n_{aa}(t e_a)\|\le2$（$a=x,y$、$|t|\le r$）及 $\|n_x(0)\|,\|n_y(0)\|\le1$。独立重置供应 $\rho_n(z)=(I+n(z)\cdot\sigma)/2$。初始方向目标仍为

$$
D_h(n)=\left(
 \frac{h\cdot[n(0)\times n_x(0)]}{2},
 \frac{h\cdot[n(0)\times n_y(0)]}{4},0,
 \frac{h\cdot n_y(0)}2\right).
\tag{19.2}
$$

对每个请求及公共元组，比较所有与实际 $n,h$ 无关的有限因果控制器和有限解码器；每一对必须对全部上述 $n$ 及全部 $h\in S^2$ 满足
$\Pr[\|\widehat D-D_h(n)\|_\infty\le e]\ge1-e$。参考 $R=\operatorname{Sym}^{m_e}(\mathbb C^2)$ 只准备一次，初态 $\tau_h=|j_e,h\rangle\langle j_e,h|$ 与其余输入独立，是唯一含未知 $h$ 的输入；除声明的场源外，辅助准备及设备参数均不依赖实际 $n,h$，场信息只经重置服务供给。固定 $n$ 后非参考来源的完整律对全部 $h$ 相同。保留原始混合辅助、量子及经典记忆、反馈和探针回用的允许范围。访问限于至多 $L_e$ 次 (13.6) 的原生 $V=\sum_{b=\pm}\Pi_b\otimes|bb\rangle_{HE}$、至多 $Q_e$ 次场重置，以及恰一次以 $+d e_x$ 的独立原场令牌执行的规定终端交换
$U_{\rm term}=\exp[-id\tau_0J\cdot\sigma/m_e]$；其余操作在原始标记 $R$ 上为恒等，不提供直接读取、旋转、拆分、重置、替换或恢复 $R$ 的许可。

每个控制器用其自己的完整实际口 $K$：全部实际探针、场令牌、原生 $H,E$ 和原始记录、实际读出及复制环境、记忆、程序、计数器、路由和解码工作区、补偿及终端输出均包括在内。约化 CP 节点采用其声明的实际端口；形式 Kraus 指标及证明扩张不充作实际输出，另行产生的实际系统则必须纳入 $K$。对同一运行的最终态定义

$$
\overline\delta=\sup_{n,h}\frac12
 \left\|\Omega_{n,h}-\tau_h\otimes\operatorname{Tr}_R\Omega_{n,h}\right\|_1,
\qquad
R(e)=\inf_{\text{上述成功控制器及解码器}}\overline\delta .
\tag{19.3}
$$

无分支后选择，比较态使用该控制器自身的实际 $K$ 边缘。

此下确界非空。复用 (13.18)–(13.19) 的完整前缀比较、固定标架下的 Pauli 样本和中心差分，以及定义 17.1、定理 17.3–17.4 的同一补偿后缀，已有可达证书给出

$$
R(e)\le\min\left\{1,6k_e\kappa_{D_e}+\frac{80}{D_e}\right\}
 \le\min\left\{1,\frac{6k_e+80}{D_e}\right\},
\qquad \kappa_D=\frac{2D-1}{2D^2}.
\tag{19.4}
$$

该见证实际消耗 $3k_e+2$ 次原生槽、含终端的 $3k_e+3$ 次 $R$ 接触、$15\ell_e+2$ 次场重置、$3k_e$ 次 $\mathcal C$ 及 $3k_e+15\ell_e$ 次 Pauli 观察，另有固定后缀及有限解码和记录空间；未用上限不计为消耗。式 (19.1) 保证两项调用上限和 $3k_e\kappa_{D_e}\le e/3$。该证书的参考、场均值好事件分别要求各坐标误差不超过 $e/16$、$eu_e/16$，理想失败率分别至多 $6\exp(-k_e e^2/2048)$、$30\exp(-\ell_e e^2u_e^2/512)$，均不超过 $e/3$。原 $C^2$ 承诺使中心差分偏差不超过 $u_e$，代入 (19.2) 的误差不超过 $e$；完整前缀比较产生至多 $3k_e\kappa_{D_e}\le e/3$ 的事件概率差，规定后缀保持该解码边缘。此处只复用这一充分证书；$\mathcal C,\widehat\Phi,\mathcal E$ 分别保持定义 13.2、17.1、16.1 的实际约化口语义。

**推论 19.2（全局能量与均匀解码的返回下界；source-derived）。** 在定义 19.1 的精确曲线上，令 $a=1-2e$。每个成功控制器及其完整实际口均满足

$$
a\le\overline\delta+64e\sqrt{m_e\overline\delta},
\qquad
\overline\delta\ge
 \left(\frac{2a}
 {\sqrt{4096m_e e^2+4a}+64e\sqrt{m_e}}\right)^2 .
\tag{19.5}
$$

特别地，

$$
R(e)\ge\frac1{16384(D_e-1)e^2}
       \ge\frac1{16384D_e e^2}.
\tag{19.6}
$$

证明。固定半径 $1/3$ 开圆盘上的原始允许场
$n_*(x,y)=(x,y,\sqrt{1-x^2-y^2})$。前两个坐标保证秩二，原点两轴导数范数为一，完整闭 $r$ 轴段上二阶导数范数为 $(1-t^2)^{-3/2}<2$；其目标为
$D_h(n_*)=(h_y/2,-h_x/4,0,h_y/2)$。
对任一上述成功控制器，吸收这个固定场的全部来源、混合辅助、控制和规定终端，得到同一个 $h$ 无关有限 CPTP 通道
$\Lambda:R\to R\otimes K$，仍保留该控制器自己的完整实际 $K$。记
$\Omega_h=\Lambda(\tau_h)$、$\omega_h=\operatorname{Tr}_R\Omega_h$，并记 $D_{\rm tr}(\rho,\sigma)=\|\rho-\sigma\|_1/2$。这是必要条件的较大 CPTP 比较类。

直接调用定理 14.3 的 (14.17)–(14.22)。对一个固定有限代数 Kraus 表示，令
$f(h)=(f_{r,h})_r$，
$f_{r,h}=(\langle j_e,h|\otimes I_K)A_r|j_e,h\rangle$。
相位在此抵消，故 $f:S^2\to K\otimes\mathbb C^q$ 是全局光滑函数，且 $\|f(h)\|\le1$。令 $p_h=\operatorname{Tr}[((I_R-\tau_h)\otimes I_K)\Omega_h]$。在 (14.7) 的坐标 $z=x+iy$ 中，该定理给出

$$
p_h\le\overline\delta,\qquad
\|\partial_{\bar z}f(z)\|
 \le\frac{\sqrt{m_e\overline\delta}}{1+|z|^2},\qquad
\omega_h=Q_h+Z_h,\quad
Q_h=\sum_r|f_{r,h}\rangle\langle f_{r,h}|,\quad
Z_h\ge0,\quad\operatorname{Tr}Z_h=p_h .
\tag{19.7}
$$

这里 $q$ 只为代数指标数。对任意 $h,h'$，展开堆叠向量的外积之差并对该形式指标取偏迹，范数不超过一给
$\frac12\|Q_h-Q_{h'}\|_1\le\|f(h)-f(h')\|$；
正余项的半迹范数至多 $(p_h+p_{h'})/2$。因此

$$
D_{\rm tr}(\omega_h,\omega_{h'})
 \le\|f(h)-f(h')\|+\overline\delta .
\tag{19.8}
$$

上述代数比较没有给实际口添加环境或接入初始纯化。

令 $\mu$ 为单位球面的归一面积，$\nabla$ 使用其标准圆度量。其球极投影坐标表达为
$d\mu=dA(z)/[\pi(1+|z|^2)^2]$。全局光滑性及 Stokes 公式逐复分量给
$\int_{S^2}d(\operatorname{Re}f_\nu\,d\operatorname{Im}f_\nu)=0$，所以复导数平方中的混合积分项为零，从而

$$
\begin{aligned}
\mathcal E(f)
 :=\int_{S^2}\|\nabla f\|^2\,d\mu
 &=\frac1{4\pi}\int_{\mathbb C}
       (\|f_x\|^2+\|f_y\|^2)\,dA\\
 &=\frac1\pi\int_{\mathbb C}\|\partial_{\bar z}f\|^2\,dA
 \le m_e\overline\delta .
\end{aligned}
\tag{19.9}
$$

末步用 (19.7) 及 $\int_{\mathbb C}(1+|z|^2)^{-2}dA=\pi$。该积分恒等式依赖全局函数 $f$；不要求一个全局连续的相干向量相位，也未作逐点的两种复导数能量等同。

以 $\rho_s$ 表示证明参数绕 $z$ 轴的旋转，其生成向量场
$X(h)=(-h_y,h_x,0)$ 满足 $|X|\le1$。微积分基本定理、Cauchy–Schwarz 及面积不变性给

$$
\int_{S^2}\|f(\rho_\alpha h)-f(h)\|^2\,d\mu(h)
 \le\alpha\int_0^\alpha\int_{S^2}
       \|Xf(\rho_s h)\|^2\,d\mu(h)\,ds
 \le\alpha^2m_e\overline\delta .
\tag{19.10}
$$

取 $\alpha=32e\le0.32<1/3$ 及球冠 $C=\{h:h_x\ge1/2\}$，有 $\mu(C)=1/4$。对每个 $h\in C$，

$$
(\rho_\alpha h)_y-h_y
 \ge\frac12\sin\alpha-(1-\cos\alpha)
 \ge\frac\alpha2-\frac{\alpha^3}{12}-\frac{\alpha^2}{2}
 >\frac\alpha4 .
$$

故第一目标坐标之差大于 $\alpha/8=4e>2e$。固定解码器的两个闭 $e$ 成功球不交；其输出落入 $D_h(n_*)$ 的闭 $e$ 球这一实际效果，在 $h$ 上概率至少 $1-e$，在 $\rho_\alpha h$ 上至多 $e$。于是整个球冠上均有
$D_{\rm tr}(\omega_h,\omega_{\rho_\alpha h})\ge a$。旋转只作用于证明中的自变量；比较效果可依赖所选的 $h$，控制器和解码器始终是同一对，未假定其协变或实施未知方向的物理旋转。

由 (19.8)–(19.10)，

$$
\frac14(a-\overline\delta)_+^2
 \le\int_C\|f(\rho_\alpha h)-f(h)\|^2\,d\mu
 \le\alpha^2m_e\overline\delta .
$$

开方即得 (19.5) 第一式；令 $x=\sqrt{\overline\delta}$ 解二次不等式并有理化正根，得到第二式。又 $a\ge49/50$；若 $\overline\delta<1/4$，则 $a-\overline\delta>1/2$，上式给
$\overline\delta\ge1/(16384m_e e^2)$。若 $\overline\delta\ge1/4$，同一结论由 $m_e e^2\ge1$ 得到；后者在整条曲线上由 $k_e\ge2048e^{-2}$、$D_e\ge9k_e/e$ 保证。最后对非空的成功类取下确界，证明 (19.6)。$\square$

**注记 19.3（定量后果、来源与置信度缺口）。** 定理 14.3 的相干符号、全局泄漏和实际侧边缘是本推论的直接供应者；Stokes、Cauchy–Schwarz、外积范数及同一通道的二元测试是成熟工具。相对于推论 14.4 的逆维数必要证书，这里的正面积解码分离给出额外的 $e^{-2}$ 精度因子。与 (19.4) 合并，存在绝对常数 $c,C>0$，在这条正有理曲线上

$$
\frac{c}{D_e e^2}\le R(e)
 \le\frac{C\log(1/e)}{D_e e^2}.
\tag{19.11}
$$

原置信度问题仍是

$$
\liminf_{\substack{e\downarrow0\\e\in\mathbb Q_{>0}}}
 \frac{D_e e^2R(e)}{\log(1/e)}
 \ \mathop{>}^{?}\ 0 .
\tag{19.12}
$$

证明只通过 $a=1-2e$ 使用失败率，未给出所缺的 $\log(1/e)$ 必要因子；将 (19.6) 归一化所得趋零下界也不能充作反例的上界。正解仍须对所有充分小正有理 $e$、所有成功原始控制器证明统一正倍数的对数下界；反解须给出正有理 $e_r\downarrow0$ 上成功的合法同一运行控制器，使其完整实际返回的上述归一化量趋零。这里均未建立。

相干程序沿用 OTF002 定义 11.1，有限 CP 语义沿用 OTF001 假设 2.5–2.7、定理 7.2；实际菜单及记忆保持 OTF003 第 11 节和 OTF007 定理 9.1 的范围。原生总自旋模型的成熟来源为 Bartlett–Rudolph–Spekkens–Turner，[《Degradation of a quantum reference frame》第 III 节、附录 B 式 (39)–(41)](https://arxiv.org/html/quant-ph/0602069v2)，如定义 12.1 所用。Sacchi 的[《Information-disturbance tradeoff for spin coherent state estimation》式 (8)–(9)、第 IV 节](https://arxiv.org/html/quant-ph/0610246v2)研究 Haar 平均整自旋生存及相干估计保真度；其任意仪器比较可提供必要约束，直接作用于 $R$ 的优化仪器则不由此取得原生实现许可。本节是既有来源的条件推论，历史优先权未建立，不作成熟理论整体不适用或文献穷尽断言。

定义 13.1 的固定精度任务及其逆维数存在性继续直接复用原结果。此处的 CPTP 放宽只用于必要性，不给原生上界见证、物理扩张返回定理、匹配最优性或任意资源曲线结论；相干参考、独立场源、指定耦合、约化 CP 端口、校准和时钟仍为模型前提。

## 追加锚（本行以下为增补区）

## 20. 新鲜独立混合提取的对数返回障碍

**定义 20.1（受限控制类）。** 取正有理数 $0<e\le1/100$，并逐项采用 (19.1) 的精度曲线

$$
\begin{aligned}
u_e&=e/8,\qquad
 k_e=\left\lceil2048e^{-2}\log(18/e)\right\rceil,\qquad
 \ell_e=\left\lceil32768e^{-4}\log(90/e)\right\rceil,\\
N_*&=8{,}388{,}608{,}000,\qquad
N_e=\max\left\{N_*,\left\lceil\frac{3k_e+2}{10}\right\rceil,
 \left\lceil\frac{15\ell_e+1}{18}\right\rceil\right\},\\
D_e&=\left\lceil\max\{8{,}000{,}000N_e^2,9k_e/e\}\right\rceil,
\qquad m_e=D_e-1=2j_e,\\
L_e&=M_e=10N_e,\qquad Q_e=18N_e+1 .
\end{aligned}
\tag{20.1}
$$

公共参数保持 $d=1/64$、$\tau _0=1$、$r=1/4$、$B_{\rm field}=2$、$G=1$。场仍为定义 13.1 的全部 $C^2$、秩二映射 $n:U\to S^2$：$U$ 包含两条完整闭 $r$ 轴段，且
$\|n_{aa}(t e_a)\|\le2$（$a=x,y,|t|\le r$）及
$\|n_x(0)\|,\|n_y(0)\|\le1$。场重置独立供应
$\rho_n(z)=(I+n(z)\cdot\sigma)/2$。目标和原始访问合同分别是

$$
D_h(n)=\left(\frac{h\cdot[n(0)\times n_x(0)]}{2},
\frac{h\cdot[n(0)\times n_y(0)]}{4},0,\frac{h\cdot n_y(0)}2\right),
\tag{20.2}
$$

以及至多 $L_e$ 次原生
$V=\sum_{b=\pm}\Pi_b\otimes|bb\rangle_{HE}$、至多 $Q_e$ 次场重置和恰一次规定终端交换
$U_{\rm term}=\exp[-id\tau _0J\cdot\sigma/m_e]$；其余操作在原始 $R$ 标记上恒等，不直接读取、旋转、拆分、重置、替换或恢复 $R$。控制器、解码器、辅助初态及固定 $n$ 后非 $R$ 来源的完整律均与实际 $n,h$ 无关，且必须对全部上述 $n$ 和 $h\in S^2$ 满足同一运行成功条件
$\Pr[\|\widehat D-D_h(n)\|_\infty\le e]\ge1-e$，不作后选择。

一个控制器属于本类，当且仅当存在运行前固定的整数 $q$，$0\le q\le L_e-2$，使其前缀与后缀满足下列条件。

1. 前缀与 $R$ 的全部接触恰为 $q$ 个原生 $V$ 槽；每槽输入一枚真正新鲜、与 $R$ 及此前全部寄存器独立的 $I_S/2$，并在该槽后立即施行原定义 (13.7)–(13.8) 的同一个约化通道 $\mathcal C$。新鲜探针不被相关、偏置、替换或接入不可见纯化。槽间允许任意有限的、因果的、$h/n$ 无关的非 $R$ 处理，包括保留全部量子记录、集体存储和最终集体解码；这些处理不得增加前缀的 $R$ 接触，也不得把任何旧前缀寄存器送入后缀。$q$ 不随 $n,h$ 或观测结果自适应改变。
2. 前缀后接定义 17.1 的完整固定后缀：其 singlet、固定 $\widehat\Phi$ 及三个替换节点、两枚原生 $V$ 槽、原始 $H,E$ 记录与副本，以及一个使用独立且此前未改动的 $+d e_x$ 场令牌和声明的 $\mathcal E$ 节点的规定终端交换。后缀恰有这两个原生槽和这一个终端，不接收旧前缀记录、内存、标签或控制信号；其规定的两枚场令牌和所有前缀场重置合计不超过 $Q_e$。
3. 每个成员使用自己的完整实际输出口 $K$：所有前缀探针和场令牌、原生 $H,E$ 及原始标签、实际读出和复制环境、保留的处理输出、记忆、程序、计数器、路由、解码工作区、后缀的 $B,A,F,S_t$、两组后缀 $H,E$ 及其实际副本全部计入 $K$。$\mathcal C$、$\widehat\Phi$ 和 $\mathcal E$ 只取各自声明的实际端口；证明用的 dilation 或 Kraus 指标不自动成为实际输出，实际产生的其它系统必须加入 $K$。

对成员的最终实际态 $\Omega_{n,h}\in\mathsf D(R\otimes K)$，仍以其自身的边缘定义

$$
\overline\delta=\sup_{n,h}\frac12\left\|\Omega_{n,h}-
 \tau_h\otimes\operatorname{Tr}_R\Omega_{n,h}\right\|_1 .
\tag{20.3}
$$

本类非空：取 (19.4) 的成功见证，令 $q=3k_e$。由 (20.1)，$q+2\le L_e$；它使用 $q+3$ 次含终端的 $R$ 接触、$15\ell_e+2$ 次场重置、$q$ 次 $\mathcal C$ 及其规定的固定后缀，并满足原始全部 $n,h$ 的成功事件。因此这里的 $K$、端口和终端条件不是空的形式交集。

**定理 20.2（受限类的对数完全返回必要界）。** 对定义 20.1 的每一个成功成员，令
$D=D_e$、$m=D-1$、$\lambda=\sqrt m/D$ 及
$\kappa_D=(2D-1)/(2D^2)$。则

$$
\boxed{\displaystyle
\overline\delta\ \ge\ \frac{\log(1/(8e))}{128D_e e^2}}
\tag{20.4}
$$

其中对数为自然对数。

**证明。** 先给出置信度所迫使的前缀长度。取允许场
$n_*(x,y)=(x,y,\sqrt{1-x^2-y^2})$（半径 $1/3$ 圆盘），则
$D_h(n_*)=(h_y/2,-h_x/4,0,h_y/2)$。令
$h_+=(\cos(4e),\sin(4e),0)$、
$h_-=(\cos(4e),-\sin(4e),0)$。两目标的第一坐标相距 $\sin(4e)>2e$；故同一个解码器的两个闭 $e$-成功球不交。

记 $P_{h,+}=(I+h\cdot\sigma)/2$。由 (13.16)，一枚理想提取槽的完整标记态为

$$
\xi_h=\frac12P_{h,+}\otimes|++\rangle\langle++|
      +\frac14I_2\otimes|--\rangle\langle--| .
\tag{20.5}
$$

两方向的旗标块正交，故其根保真度为

$$
f(\xi_{h_+},\xi_{h_-})=\frac{1+\cos(4e)}2=\cos^2(2e).
\tag{20.6}
$$

逐槽使用 (13.18)–(13.19)，并在理想前缀后接 (17.7) 的固定后缀，得到一个 $h$ 无关的理想 $K$-输出通道，使实际完整输出与该理想输出的迹距离至多

$$
a_q=q\kappa_D+\frac{73}{2D} .
\tag{20.7}
$$

这里所有实际记录、工作区和后缀输出都留在 $K$；理想化只是替换比较态，没有删除任何实际输出。由于 $q\le10N_e-2$、$D\ge8{,}000{,}000N_e^2$ 且 $N_e\ge1/e$，有

$$
a_q\le\frac{10N_e+73/2}{D}<\frac{11}{8{,}000{,}000N_e}<e .
\tag{20.8}
$$

实际成功事件转移到理想输出时至多损失 $a_q$。在理想输出上用同一解码器区分 $h_+$ 和 $h_-$，等先验二元错误不超过 $e+a_q$。Fuchs–van de Graaf 的根保真度单调性、乘法性及其等先验测试不等式给

$$
\cos^{4q}(2e)
 \le f(\text{理想输出}_+,\text{理想输出}_-)^2
 \le4(e+a_q)\le8e .
\tag{20.9}
$$

对 $0<2e\le0.02$，$-\log\cos(2e)\le4e^2$，所以

$$
q\ge\frac{\log(1/(8e))}{16e^2} .
\tag{20.10}
$$

特别地 $q=0$ 不可能成功。

下面计算同一成员的实际参考泄漏。将一个新鲜 $I_S/2$ 槽对 $R$ 的边缘写成 OTF004 (13.5) 的精确通道

$$
T(X)=\frac{2\sum_iJ_iXJ_i+((j+1)^2+j^2)X}{D^2} .
\tag{20.11}
$$

所有非 $R$ 的保迹处理（包括 $\mathcal C$）不改变该边缘；新鲜性使 (20.11) 即使在 $R$ 与旧 $K$ 相关时仍逐槽成立。以 $h$ 为量子化轴，$T^q(\tau_h)$ 在 $|j,j-k\rangle_h$ 基中对角。其精确相邻转移概率为

$$
\Pr(k\mapsto k+1)=\frac{(m-k)(k+1)}{D^2},\qquad
\Pr(k\mapsto k-1)=\frac{k(m-k+1)}{D^2},
\tag{20.12}
$$

越界项取零。令
$p_q=\operatorname{Tr}[(I-\tau_h)T^q(\tau_h)]$。取 $q$ 条不交路径：恰有一次 $0\mapsto1$，其余每步停留在 $0$ 或 $1$。每个停留概率至少 $1-3/D$，而一次跳转的概率为
$\lambda^2=m/D^2$，故

$$
p_q\ge q\lambda^2(1-3/D)^{q-1} .
\tag{20.13}
$$

曲线 (20.1) 给出 $D\ge6q$ 及 $D\ge50$。Bernoulli 不等式、
$(1-3/D)^{q-1}\ge1/2$ 和 $\lambda^2\ge1/(2D)$ 遂给

$$
p_q\ge\frac{q}{4D}\qquad(q\ge1).
\tag{20.14}
$$

考察固定后缀在任一接触处的参考投影
$P=\tau_h\otimes I$ 及其正交投影 $Q=I-P$。由 (13.14) 及同一角动量系数的上移项，原生槽的完整输出满足
$\|PVQ\|=\sqrt2\lambda$；由 (16.8) 的终端谱分解
$U_{\rm term}=\Pi_++z\Pi_-$（$|z|=1$），终端满足
$\|P U_{\rm term}Q\|=|1-z|\lambda\le2\lambda$。后缀中的其它节点只作用于非 $R$ 系统，取其保留全部实际输出的 dilation 后与 $P$ 交换。因此把两枚 $V$ 和终端用望远镜相加，后缀整体 $W$ 满足

$$
\|PWQ\|\le2\sqrt2\lambda+2\lambda<5\lambda .
\tag{20.15}
$$

所以任何支撑在 $Q$ 的归一化输入经固定后缀回到 $P$ 的概率至多
$25\lambda^2<25/D$。前缀边缘由 (20.11) 对角分解为 $\tau_h$ 与其正交部分的混合；由于后缀不读取旧前缀 $K$，其 $R$ 边缘只依赖该混合。由 (20.13)–(20.15)，最终参考泄漏至少为

$$
\operatorname{Tr}[(I-\tau_h)\Omega_{n_*,h}]
 \ge p_q\left(1-\frac{25}{D}\right)
 \ge\frac{q}{8D} .
\tag{20.16}
$$

对效果 $I-\tau_h$ 使用迹距离的变分表述，目标乘积态
$\tau_h\otimes\operatorname{Tr}_R\Omega_{n_*,h}$ 在该效果上的概率为零，故

$$
\overline\delta\ge\frac12\left\|\Omega_{n_*,h}-
\tau_h\otimes\operatorname{Tr}_R\Omega_{n_*,h}\right\|_1
\ge\operatorname{Tr}[(I-\tau_h)\Omega_{n_*,h}]\ge\frac{q}{8D} .
\tag{20.17}
$$

将 (20.10) 代入 (20.17) 即得 (20.4)。证明只使用成员自己的完整实际 $K$；未以理想边缘替换返回定义，也未把证明 dilation 当作输出。$\square$

**注记 20.3（来源、排除的路线与未决范围）。** (13.5)、(13.14)、(13.16)、(13.18)–(13.19)、(16.8) 和 (17.1)–(17.7) 是 OTF004 的既有接口与比较结果；有限完全正语义和相干自旋准备沿用 OTF001–OTF002。Bartlett–Rudolph–Spekkens–Turner, *Degradation of a quantum reference frame*, quant-ph/0602069v2，III.1–III.2 及附录 B (41)–(42)，给出同一独立 $I/2$ 探针的精确有限自旋递推；这里只用该递推，不用其大 $j$ 近似或丢弃输出后的寿命指标。Fuchs–van de Graaf, *Cryptographic Distinguishability Measures for Quantum Mechanical States*, quant-ph/9712042v2，§4.1 (17)、§4.3 (23)–(27) 及定理 1 (46)，供应根保真度、乘法性、单调性和二元测试不等式。成熟来源只作上述中间事实；最新其它 DEV 结果没有被当作本类的原生接口、CP 节点、共同信道或完整返回供应者。

若记本类下确界为 $R_{\rm sub}(e)$，定理 20.2 给出
$R_{\rm sub}(e)\ge\log(1/(8e))/(128D_e e^2)$。它排除的正是“固定数量的新鲜独立 $I/2$ 提取、每槽立即施行 $\\mathcal C$、再接固定 §17.1 后缀，却用全部实际记录作集体解码”这条反例路线。它没有处理原始合同允许的偏置或纠缠探针、探针回用、按结果准备后续探针、自适应停止、把前缀量子或记录反馈到后续 $R$ 接触，以及任何不同后缀或共同控制。因为原始 $R(e)$ 是更大控制类上的下确界，只有 $R(e)\le R_{\rm sub}(e)$；故 (20.4) 不能推出原始 $R(e)$ 的下界。原问题 (19.12)——统一的全控制器对数必要界与合法的归一化趋零反例之间的选择——仍然开放。

## 追加锚（本行以下为增补区）

## 21. 混合提取前缀在任意原生记忆续接下的泄漏障碍

**定义 21.1（固定提取前缀与任意合法续接）。** 逐项采用定义 19.1 的原始精度曲线、全部允许场 $n$、全部 $h\in S^2$、目标 $D_h(n)$ 和完整实际口约定。写

$$
D=D_e,\qquad m=D-1=2j_e,\qquad L=L_e=10N_e,\qquad Q=Q_e,
\qquad D\ge8{,}000{,}000N_e^2 .
\tag{21.1}
$$

初始参考仍为独立于其余输入的 $\tau_h=|j_e,h\rangle\langle j_e,h|$；$h$ 只由这个输入携带。场仍遍历包含两条完整闭 $r$ 轴段的开集上、满足定义 19.1 全部秩、光滑性和导数条件的 $n$，场信息只经原来的独立重置服务供应，所有设备、初态辅助、程序和解码器均不依赖实际 $n,h$。

在运行前固定整数 $0\le q\le L$。前 $q$ 次 $R$ 接触恰为原生 (13.6) 的 $V$ 槽，每槽输入一枚真正新鲜、与 $R$ 及此前全部寄存器独立的 $I/2$ 探针，且立即施行同一个 (13.7)–(13.8) 的 $\mathcal C$。槽间允许任意有限因果的非 $R$ 处理，包括场调用及旧量子、经典记忆的处理。新鲜性只限制下一槽输入探针，不限制保存或处理旧输出。

此后允许任意原始合同内的有限因果续接：全部旧量子及经典记忆均可参与；允许偏置或纠缠探针、探针回用、反馈、续接自身的获取和自适应停止。续接至多再调用 $L-q$ 枚原生 $V$，并恰执行一次规定终端交换，以独立供应且此前未改动的 $+d e_x$ 原场令牌为输入；总场重置不超过 $Q$。除这些接触外，全部操作在原始标记 $R$ 上恒等。不供应未知 $h/n$ 依赖设备、直接 $R$ 操作、逆 $V$、不可见纯化或分支后选择。

$K$ 是同一个控制器自己的完整实际口，包含全部实际探针、场令牌、原生 $H,E$、原始记录和副本、实际读出及复制环境、量子及经典记忆、程序、计数器、路由、输出和解码工作区以及规定终端的全部实际输出。约化 CP 节点保持其声明的端口；代数 Kraus 指标及证明扩张均不作为额外实际端口。对最终实际联合态定义

$$
\Delta_{n,h}=\frac12\left\|\Omega_{n,h}
 -\tau_h\otimes\operatorname{Tr}_R\Omega_{n,h}\right\|_1,
\qquad
p_{\rm final}(n,h)=\operatorname{Tr}[((I_R-\tau_h)\otimes I_K)\Omega_{n,h}] .
\tag{21.2}
$$

本定义不要求续接保持前缀的解码分布，也不预设成功；若讨论成功，仍使用定义 19.1 对全部 $n,h$ 的原成功条件。

**定理 21.2（任意预算内记忆续接不能消去前缀的线性泄漏）。** 对定义 21.1 的每个控制器、每个允许场 $n$ 和每个 $h\in S^2$，均有

$$
\boxed{\displaystyle
\Delta_{n,h}\ge p_{\rm final}(n,h)\ge\frac{q}{8D_e}.}
\tag{21.3}
$$

更精确地，令

$$
\lambda=\frac{\sqrt m}{D},\qquad
\kappa_D=\frac{2D-1}{2D^2},\qquad
\alpha=1-\kappa_D,\qquad \beta=\frac{m}{2D^2},\qquad
\varepsilon_L=\lambda^2(\sqrt2 L+2)^2 .
\tag{21.4}
$$

则同一实际态满足

$$
\begin{aligned}
p_{\rm final}(n,h)
&\ge\beta\sum_{s=1}^{q}\alpha^{s-1}
 \left[1-\lambda^2\bigl(\sqrt2(L-s)+2\bigr)^2\right]\\
&\ge(1-\varepsilon_L)\beta\sum_{s=1}^{q}\alpha^{s-1} .
\end{aligned}
\tag{21.5}
$$

$q=0$ 时两和为空，取值为零。

**证明。** 固定同一个允许 $n,h$。仅在证明坐标中沿 $h$ 量子化，记 $e_h=|j_e,j_e\rangle_h$、$f_h=|j_e,j_e-1\rangle_h$，以及探针的 $\uparrow_h,\downarrow_h$。这不向控制器提供方向、旋转或新的操作。

先对 (13.15) 作正半定分解，而不对实际联合态作参考偏迹。令 $\tau_f=|f_h\rangle\langle f_h|$，并定义非归一化的实际 $S,H,E$ 状态

$$
\begin{aligned}
g_h={}&\frac12|\uparrow_h\rangle\langle\uparrow_h|
                  \otimes|++\rangle\langle++|
 +\frac{m^2}{2D^2}\frac{I_S}{2}\otimes|--\rangle\langle--|,\\
\chi={}&\frac{I_S}{2}\otimes|--\rangle\langle--|,\\
|v_h\rangle={}&e_h\otimes\downarrow_h+\sqrt m\,f_h\otimes\uparrow_h .
\end{aligned}
\tag{21.6}
$$

由完整一槽等式 (13.15)，输入 $\tau_h$ 与新鲜 $I/2$ 时，实际槽输出准确为

$$
\tau_h\otimes g_h
 +\beta\tau_f\otimes\chi
 +\frac{|v_h\rangle\langle v_h|}{2D^2}\otimes|++\rangle\langle++| .
\tag{21.7}
$$

三个加项均为正半定；第一项的迹为
$\operatorname{Tr}g_h=1/2+m^2/(2D^2)=\alpha$，第二项的迹为 $\beta$，第三项保留了其全部参考—探针相干项。这里没有把该相干项删去，也没有给 $\mathcal C$ 添加环境输出。

若旧寄存器状态是任意 $\eta$，且与参考的联合态为 $\tau_h\otimes\eta$，新鲜性使 (21.7) 直接张量 $\eta$。槽后的任意非 $R$ 保迹处理仍把第一项变成 $\tau_h$ 与一个非归一化旧寄存器状态的乘积，其迹为 $\alpha\operatorname{Tr}\eta$。因此只对这个第一项逐槽继续分解，并把每槽第二项和第三项各交给其后的完整实际控制器，可得最终联合态的正分解

$$
\Omega_{n,h}=\Omega_{\rm rem}+\sum_{s=1}^{q}\Phi_s(Z_s),
\qquad \Omega_{\rm rem}\ge0,
\qquad Z_s\ge0,
\qquad \operatorname{Tr}Z_s=\beta\alpha^{s-1} .
\tag{21.8}
$$

其中 $Z_s$ 位于第 $s$ 槽及其立即 $\mathcal C$ 之后，其参考因子准确为 $\tau_f$；$\Phi_s$ 是从该处起、包含其余前缀、全部续接及终端的实际保迹因果通道。$\Omega_{\rm rem}$ 收集其它正项。式 (21.8) 只用线性、完全正和保迹性，对槽间依记录选择的操作也成立：控制和全部旧记忆都包含在通道输入内。各加项是数学上的正分解，无须对应可读取的分支，亦无须在最终 $K$ 中正交；未施行分支测量或后选择。

下面统一限制一个正交参考分量的回流。对接触前后的全部寄存器分别延拓
$P=\tau_h\otimes I$、$P^\perp=I-P$。由 (13.14) 的上移项及原生旗标的正交性，原生槽满足

$$
\|P V P^\perp\|=\sqrt2\lambda .
\tag{21.9}
$$

具体地，只有参考 $f_h$ 的 $f_h\uparrow_h$ 分量可送回 $e_h\downarrow_h$；$\Pi_+,\Pi_-$ 的这两个系数分别为 $\lambda,-\lambda$，它们分别携带正交的 $|++\rangle,|--\rangle$，故平方范数相加为 $2\lambda^2$。其余参考本征矢没有到达 $e_h$ 的矩阵元；张量任意旁观者或记忆不改变此算子范数。由 (16.8)，规定终端在略去整体相位后为 $\Pi_++z\Pi_-$，$|z|=1$，故

$$
\|P U_{\rm term}P^\perp\|
 =|1-z|\lambda\le2\lambda .
\tag{21.10}
$$

任意非 $R$ CPTP 步骤可在证明中写成等距扩张 $W_i$；它满足 $P W_i=W_iP$，因而没有 $P^\perp$ 到 $P$ 的块。扩张指标只用于计算概率，最终取偏迹，不是控制器可用的输入、纯化或实际输出。对一般接触等距 $W_i$，在相邻空间插入 $P+P^\perp$ 并用等距及投影的收缩性，得

$$
\|P W_t\cdots W_1P^\perp\|
 \le\|P W_{t-1}\cdots W_1P^\perp\|
      +\|P W_tP^\perp\| .
\tag{21.11}
$$

所以包含至多 $r$ 次原生 $V$ 和一次终端的任意这样的联合续接 $W$ 满足

$$
\|P W P^\perp\|\le(\sqrt2 r+2)\lambda .
\tag{21.12}
$$

此论证允许在每次接触前由全部记忆选择或相干路由探针，因为这些操作都在非 $R$ 系统上。有限因果树的自适应停止可按调用序号补齐恒等空步，在证明扩张中保留其控制历史；一次“调用或空步”在相应正交控制块上分别为 $V$ 或恒等，其回流块范数仍至多 $\sqrt2\lambda$。规定终端的控制块均满足 (21.10)。故同一上限用于全部分支，不要求确定的实际调用次数或固定的记忆无关后缀。

对任何支撑在 $P^\perp$ 的正算子 $Z$，扩张后再对形式环境取偏迹给

$$
\operatorname{Tr}[P\Phi(Z)]
 =\operatorname{Tr}[(P W P^\perp)Z(P W P^\perp)^\dagger]
 \le(\sqrt2 r+2)^2\lambda^2\operatorname{Tr}Z .
\tag{21.13}
$$

它对任意参考—记忆相关输入成立；没有以参考边缘替代联合输入。

在 (21.8) 的第 $s$ 项上，$Z_s$ 支撑在 $P^\perp$，且其后最多还有 $L-s$ 次原生调用及一个终端。由 (21.13) 和保迹性，该项最终的参考泄漏至少为

$$
\operatorname{Tr}[P^\perp\Phi_s(Z_s)]
 \ge\beta\alpha^{s-1}
 \left[1-\lambda^2\bigl(\sqrt2(L-s)+2\bigr)^2\right] .
\tag{21.14}
$$

在正分解 (21.8) 中相加，$\Omega_{\rm rem}$ 对这个效果的贡献非负，遂得 (21.5)。其它分量中的相干补偿不能抵消这些正项的概率贡献。

原曲线给 $N_e\ge1$、$D\ge4L$ 及 $D\ge3$。对 $q\ge1$，Bernoulli 不等式和 $\kappa_D\le1/D$ 给

$$
\alpha^{q-1}\ge1-\frac{q-1}{D}\ge\frac34,
\qquad \beta=\frac{1-1/D}{2D}\ge\frac1{3D},
\qquad \beta\sum_{s=1}^{q}\alpha^{s-1}\ge\frac{q}{4D} .
\tag{21.15}
$$

又 $\sqrt2\le3/2$、$L=10N_e$，所以

$$
\varepsilon_L
 \le\frac{(\sqrt2 L+2)^2}{D}
 \le\frac{289N_e^2}{D}
 \le\frac{289}{8{,}000{,}000}<\frac12 .
\tag{21.16}
$$

由 (21.5)、(21.15)–(21.16) 得 $p_{\rm final}\ge q/(8D)$。$q=0$ 时此结论直接是概率非负。最后，效果 $(I_R-\tau_h)\otimes I_K$ 在比较态 $\tau_h\otimes\operatorname{Tr}_R\Omega_{n,h}$ 上的概率为零，迹距离的变分表述给 $\Delta_{n,h}\ge p_{\rm final}$。全程使用同一个实际 $\Omega_{n,h}$ 及其自身的实际 $K$ 边缘。$\square$

**推论 21.3（既有成功构造的前缀不能靠任意预算内记忆修复改变返回阶）。** 在同一原曲线上，取 (19.4) 成功构造所用的 $q=3k_e$ 新鲜 $I/2$ 加立即 $\mathcal C$ 前缀。对其后任何满足定义 21.1 的合法续接，无论该续接是否保持原解码器或另外获取信息，对全部允许的 $n,h$ 均有

$$
\Delta_{n,h}\ge\frac{3k_e}{8D_e}
 \ge\frac{768\log(18/e)}{D_e e^2} .
\tag{21.17}
$$

因此沿任何正有理 $e\downarrow0$ 序列，这些控制器的完整返回都不能是 $o(\log(1/e)/(D_e e^2))$；特别地，这排除了保留该前缀再用全部合法旧记忆及剩余预算修复、同时保持原始成功请求的这条趋零反例路线。

**证明。** 式 (19.1) 保证 $3k_e+2\le L_e$，故该前缀属于定义 21.1。将 $q=3k_e$ 及 $k_e\ge2048e^{-2}\log(18/e)$ 代入 (21.3) 即得 (21.17)。其归一化下界为 $768\log(18/e)/\log(1/e)$，极限为 $768$。这个推导没有使用成功性来反推前缀长度。$\square$

**注记 21.4（供应者、迁移边界与原问题）。** 完整槽等式 (13.15)、角动量系数 (13.14)、终端谱关系 (16.8) 及 §20 的单接触投影块范数供应本节的原生接口；正映射保持正序、CPTP 的等距表示和迹距离变分表述是有限 CP 语义中的成熟工具，沿用 OTF001 定理 7.2 及本卷 §§13–16 的语义。式 (21.7)–(21.16) 对这些供应者给出的、允许全部旧记忆参与续接的联合推导为 repo-derived 的普通数学证明，不作 Lean 核验、历史优先权或物理实现来源的主张。

§20 的新鲜槽参考边缘递推仍适用于这个前缀，但仅有该边缘不足以分析任意读入旧量子记忆的续接；(20.16) 中先把参考边缘分成 $\tau_h$ 与正交混合再送入固定后缀的步骤不能如此迁移。式 (21.8) 改在完整实际联合态上提取正分量，并把整个剩余预算纳入 (21.12)，没有要求原续接变成固定三接触后缀。§17 的实际相关补偿仍可作用于其它分量，不与这里的正分量回流界冲突。

此外，任意续接可自己获取方向信息，故 (20.7)–(20.10) 的“理想前缀输出再经固定公共输出通道”比较及其成功所迫使的 $q$ 下界不在本类成立；这里未复用该长度结论。定理 21.2 只限制已经具有指定新鲜立即 $\mathcal C$ 前缀的控制器，未迫使任何成功原始控制器采用此前缀。完全不采用它、从开始就用偏置或纠缠探针、探针回用或其它联合获取的合法控制器仍在 (19.12) 的比较范围内。因此 (21.17) 不给原始全控制器 $R(e)$ 添加对数下界，(19.12) 的两种结算方向仍未解决。

## 追加锚（本行以下为增补区）

## 22. 原生 singlet 弱指针的方向响应与首退出完整返回障碍

**定义 22.1（单脉冲获取及固定完成）。** 保持定义 19.1 的全部原始合同、$D=D_e$、$m=D-1=2j$、$L_e,Q_e$、初态 $\tau_h$ 和目标 (19.2)。固定已知单位轴 $k$、实数 $g$ 和公开正整数上限 $q_{\max}$，其中 $q_{\max}+2\le L_e$。这些设备参数均不以实际 $n,h$ 为输入。获取另备已知 $BA$ singlet $|s_0\rangle=(|\uparrow\downarrow\rangle-|\downarrow\uparrow\rangle)/\sqrt2$ 和指针 $T$ 的 $X_T=+1$ 纯态。第一次只把 $B$ 送入原生 $V$，对原始 $H$ 标签退相干，完整保留 $H,E,b$ 及实际副本，然后施行唯一一次固定非参考脉冲

$$
U_g=\exp[-ig(k\cdot\sigma_B)Z_T].
\tag{22.1}
$$

接着测量 $BA$ 的 $P_s=|s_0\rangle\langle s_0|$、$P_t=I-P_s$ 综合征并保留结果。遇到 singlet 就停止获取；遇到 triplet 时可把同一 $B,A$ 继续用于原生 $V$ 和综合征接触，至多共 $q_{\max}$ 次，不再插入脉冲。每个成功、失败和截止历史都保留。停止后在 $T$ 上读出 Pauli $Y_T$，保留其 $y=\pm1$、测后指针及全部实际读出和复制输出。以 $S_1$ 标记“第一次综合征就是 singlet”；这个原始历史事件以后不改写。

每条停止历史都后接同一个定义 17.1 的补偿器和规定终端。该后缀另备自己的 singlet、两枚独立的 $+d e_x$ 场令牌及所声明的约化节点，不读取获取指针、旧探针或旧历史；获取的 $B,A,T$ 和记录仍在实际 $K$。后缀的两次原生接触及一次规定终端不随历史改变。总原生调用至多 $q_{\max}+2$，这里的场重置为两次，终端恰一次；这些都是实际消耗而非额外预算。辅助及实际约化节点沿用 §§13、16–19 的来源和端口语义，不提供直接 $R$ 操作或未供应的纯化。此定义只指定原比较类中的一个获取族，不缩小 (19.3) 的全部混合辅助、量子和经典记忆、反馈及探针回用比较类。

令 $\mathsf C_v:R\to R K_c$ 为上述完整固定后缀的通道，其中 $v=n(+d e_x)$；$K_c$ 含其全部实际输出。记 $\mathcal F_v=\operatorname{Tr}_{K_c}\mathsf C_v$。获取旧口保持不动，故对任意相关输入，该完成精确为 $\mathsf C_v\otimes\mathrm{id}_{\rm old}$。在数学范数测试中取边缘不改变实际口的定义；任何额外实际输出仍属于 $K$。

**定理 22.2（首退出的精确滤波与原始标签加权方向信号）。** 写

$$
\eta_+=1,\quad\eta_-=-1,\quad
 a_+=\frac{D+1}{2D},\quad a_-=\frac{D-1}{2D},\quad
 c=\cos g,\quad s=\sin g,\quad J_k=J\cdot k.
$$

在 $S_1,b$ 块内、指针读出前，未归一化的 $RT$ 态准确为

$$
M_b(\tau_h\otimes|+x\rangle\langle+x|)M_b^\dagger,
\qquad M_b=a_bcI_R\otimes I_T-i\eta_b\frac{s}{D}J_k\otimes Z_T.
\tag{22.2}
$$

旧 $BA$ 因子为原 singlet。再读出 $Y_T$ 后，$S_1,b,y$ 的未归一化参考态及概率为

$$
\begin{aligned}
\xi_{b,y}(h)&=\frac12
 \left(a_bcI_R+\eta_by\frac{s}{D}J_k\right)\tau_h
 \left(a_bcI_R+\eta_by\frac{s}{D}J_k\right),\\
p_{b,y}(h)&=\frac12\left[
 a_b^2c^2+\frac{s^2}{D^2}\left(j^2u^2+\frac j2(1-u^2)\right)
 +2\eta_by\frac{a_bcsj}{D}u\right],\qquad u=h\cdot k.
\end{aligned}
\tag{22.3}
$$

完成后的同一实际块准确为 $\mathsf C_v(\xi_{b,y}(h))$，张量附上旧 singlet、测后 $Y_T$ 本征态及相应原始标签和实际副本。等价地，实际全输出在 $R,K_c,S_1,b,y$ 上的边缘，其 $S_1$ 部分为

$$
\sum_{b,y}|S_1,b,y\rangle\langle S_1,b,y|
 \otimes\mathsf C_v(\xi_{b,y}(h)).
\tag{22.4}
$$

这是未归一化的块等式，不是条件选支。把其余所有历史的统计量定义为零，则同一个实际有界读数

$$
O=\mathbf1_{S_1}\eta_b y\in[-1,1],\qquad
\mathbb E_{n,h}O=A_g(h\cdot k),\qquad
A_g=\frac jD\sin(2g)
\tag{22.5}
$$

对全部允许 $n,h$ 精确成立。只加权原始数据就得到此信号，不需要原始 $b$ 控制的有符号脉冲。

**证明。** 由 (13.5)，$\Pi_b=a_bI+\eta_bJ\cdot\sigma_B/D$。singlet 的 $B$ 边缘为 $I_2/2$，故

$$
\langle s_0|\sigma_{B,i}|s_0\rangle=0,\qquad
\langle s_0|(k\cdot\sigma_B)\sigma_{B,i}|s_0\rangle=k_i.
$$

把 $U_g=cI-is(k\cdot\sigma_B)Z_T$ 代入 $\langle s_0|U_g\Pi_b|s_0\rangle$ 即得 (22.2)。先退相干 $H$ 不影响这个逐原始标签计算。取 $Z_T$ 基，$|y\rangle=(|0\rangle+iy|1\rangle)/\sqrt2$，于是

$$
\langle y|M_b|+x\rangle
 =\frac{1-iy}{2}\left(a_bcI_R+\eta_by\frac{s}{D}J_k\right).
$$

其标量模平方是 $1/2$。相干自旋满足
$\langle J_k\rangle=ju$、$\langle J_k^2\rangle=j^2u^2+j(1-u^2)/2$：在 $h=z$ 的证明坐标，$J_ze=je$、$J_ke=ju e+\sqrt m(k_x+ik_y)f/2$，$e=|j,j\rangle$、$f=|j,j-1\rangle$；取范数即得，随后共同旋转回任意 $h$。这证明 (22.3)。后缀忽略旧口，故线性性给出 (22.4)。对 (22.3) 乘 $\eta_by$ 并求和，二次项消失，$a_++a_-=1$ 给出 $2csju/D$，即 (22.5)。读数在 $S_1$ 之外取零，没有丢弃任何运行；不再接触旧指针和首退出块的后续操作不能改变其概率。$\square$

**定理 22.3（固定完成后的首退出返回见证）。** 取一个共同合法设备 $k=x$，并在允许的固定场上令 $v=n(+d e_x)=z$。只在以下范数证明中考察初始方向 $h_0=z$，置

$$
\lambda=\frac{\sqrt{D-1}}D,\qquad
 e=|j,j\rangle,\quad f=|j,j-1\rangle,\qquad
 q_D=\langle e|\mathcal F_z(|e\rangle\langle f|)|f\rangle.
\tag{22.6}
$$

对包括所有截止历史、旧记录和完成输出的真实最终态 $\Omega$，令 $\omega=\operatorname{Tr}_R\Omega$。存在一个仅在 $S_1$ 块上非零、范数至多一的 Hermitian 数学测试 $W$，满足

$$
\begin{aligned}
\frac12\left|\operatorname{Tr}W(\Omega-\tau_{h_0}\otimes\omega)\right|
 &=\frac{|cs|\lambda}{2}|q_D|
 =\frac{|A_g|}{2\sqrt{D-1}}|q_D|=:d_1,\\
|q_D-1|&\le40\lambda,\qquad
\left|d_1-\frac{|cs|\lambda}{2}\right|\le20|cs|\lambda^2,\\
\Delta_{n,h_0}&\ge d_1
 \ge\frac{|cs|\lambda}{2}(1-40\lambda)_+.
\end{aligned}
\tag{22.7}
$$

特别地，在非空范围 $D\ge6400$、$0<|g|\le1/4$，

$$
\Delta_{n,h_0}\ge\frac{|g|}{8\sqrt D}.
\tag{22.8}
$$

$W$ 只用于迹范数的变分表述，不是允许控制器直接测量 $R$ 的指令。该下界已包含规定终端；改变较晚 triplet 历史上的重试次数不能改变它。

**证明。** 先估计固定完成对参考交叉算子的作用。令 $W_1=\operatorname{span}\{e,f\}$，证明坐标取 $z$。直接复用 (17.12)：把一次原生接触的 $\Pi_b$ 换成 $I_R\otimes P_{z,b}$，保留相同 $|bb\rangle_{HE}$，所得两个等距 $V,V_0$ 满足

$$
\|(V-V_0)P_{W_1\otimes S}\|<6\lambda.
\tag{22.9}
$$

终端的谱表示仍为 $U=\Pi_++z_\gamma\Pi_-$，其中 $z_\gamma=e^{itD/(D-1)}$。其参考透明比较是
$U_0=I_R\otimes(P_{z,+}+z_\gamma P_{z,-})$。由 (17.12)，

$$
\|(U-U_0)P_{W_1\otimes S_t}\|
 \le4|1-z_\gamma|\lambda\le8\lambda.
\tag{22.10}
$$

在这两个比较原生接触及比较终端中，参考都保持原算子不变。所有其它节点只作用于非参考口，故整个比较完成的参考边缘通道是恒等。对任意支撑于 $W_1$ 的算子 $X$，在三个接触处依次作“理想前缀、实际后缀”比较。理想前缀的输入形为 $X\otimes\rho$，其中 $\rho$ 是非参考态，所以其迹范数为 $\|X\|_1$，参考仍支撑于 $W_1$。两等距的差至多为 $\varepsilon$ 时，展开两边乘积给出的输出迹范数差至多 $2\varepsilon\|X\|_1$。实际后缀为 CPTP，收缩任意算子的迹范数：其伴随是保单位 CP 映射，收缩算子范数，再用 Schatten 范数对偶即可。于是

$$
\|\mathcal F_v(X)-X\|_1
 \le(12+12+16)\lambda\|X\|_1=40\lambda\|X\|_1.
\tag{22.11}
$$

这里的 $W_1$ 只限制比较输入，不限制实际输出的降低数。代入 $X=|e\rangle\langle f|$ 就得到 $|q_D-1|\le40\lambda$。

其次，$\mathcal F_z$ 关于绕 $z$ 的自旋旋转协变：新 singlet、原生投影、负标签交换、(17.1) 的向量通道、替换节点、两枚 $z$ 场令牌和终端逐一保持此关系。原始标签及其副本不承载旋转。故 $\mathcal F_z(\tau_e)$ 和 $\mathcal F_z(\tau_f)$ 没有 $e/f$ 矩阵元，$\mathcal F_z(|f\rangle\langle e|)$ 也不能贡献 $e/f$ 矩阵元；后者具有相反的非零旋转权。由 $J_xe=\sqrt m f/2$，(22.3) 在 $h_0$ 处成为

$$
\xi_{b,y}(h_0)=\frac12
 \left(a_bc e+\eta_by\frac{s\lambda}{2}f\right)
 \left(a_bc\langle e|+\eta_by\frac{s\lambda}{2}\langle f|\right).
$$

因而完成后的实际 $S_1,b,y$ 块满足精确恒等式

$$
\langle e|\mathcal F_z(\xi_{b,y}(h_0))|f\rangle
 =\eta_by\frac{a_bcs\lambda}{4}q_D.
\tag{22.12}
$$

在这些保留标签的正交块中，各取相位匹配 (22.12) 的 $e/f$ 非对角 Hermitian 测试，其他空间取零，直和得到 $\|W\|\le1$。比较态 $\tau_e\otimes\omega$ 在这个测试上的期望严格为零，不涉及以理想边缘替换实际 $\omega$。四个未归一化块的绝对交叉系数之和为
$\sum_{b,y}a_b|cs|\lambda|q_D|/4=|cs|\lambda|q_D|/2$；每块测试的期望为对应系数的两倍。这证明 (22.7) 的第一式及返回下界。真实全态即使另有实际输出，取上述边缘再将测试张量恒等，仍给同一下界；没有任何选支归一化。

由 $||q_D|-1|\le|q_D-1|$ 得其余误差界。若 $D\ge6400$，则 $40\lambda\le1/2$。在 $|g|\le1/4$ 上，$|cs|=|\sin(2g)|/2\ge3|g|/4$，可由 $\sin x\ge x-x^3/6$（$0\le x\le1/2$）得到；且 $\lambda\ge2/(3\sqrt D)$（$D\ge2$）。把这三项代入 (22.7) 即得 (22.8)。较晚历史与 $S_1$ 正交，而后缀在 $S_1$ 上完全固定，所以后来的失败、成功和截止块都不能抵消 (22.12)。$\square$

**命题 22.4（固定允许场上的原目标方向分离）。** 令 $c_d=\sqrt{1-d^2}$，在半径 $1/3$ 的开圆盘上取同一个场

$$
n_\dagger(x,y)=\left(c_dx-d\sqrt{1-x^2-y^2},\ y,\ dx+c_d\sqrt{1-x^2-y^2}\right).
\tag{22.13}
$$

它满足定义 19.1 的全部场条件，且 $n_\dagger(d,0)=z$。设备仍固定 $k=x$。对 $0<\theta\le\pi/6$ 的两个邻近方向 $h_\pm=(\pm\sin\theta,0,\cos\theta)$，同一实际读数 (22.5) 及原目标满足

$$
\begin{aligned}
\mathbb E_{n_\dagger,h_+}O-\mathbb E_{n_\dagger,h_-}O
 &=2A_g\sin\theta,\\
[D_{h_+}(n_\dagger)]_2-[D_{h_-}(n_\dagger)]_2
 &=-\frac{c_d}{2}\sin\theta,\\
\operatorname{TV}(\mathcal L_{h_+}(O),\mathcal L_{h_-}(O))
 &\ge |A_g|\sin\theta.
\end{aligned}
\tag{22.14}
$$

这里 $\operatorname{TV}$ 是实际经典读数律的总变差。故在固定允许场上，信号分辨的方向确实进入原估计目标，不是固定场下独立于 $h$ 的侧律。

**证明。** (22.13) 是既有 $n_*(x,y)=(x,y,\sqrt{1-x^2-y^2})$ 的固定正旋转。它保留秩二、原点一阶导数范数一及闭轴段上的二阶导数界 $(1-u^2)^{-3/2}<2$，并把 $n_*(d,0)$ 送到 $z$。其原点值和导数为
$n_\dagger(0)=(-d,0,c_d)$、$n_{\dagger,x}(0)=(c_d,0,d)$、$n_{\dagger,y}(0)=(0,1,0)$，所以

$$
D_h(n_\dagger)=\left(h_y/2,-(c_dh_x+dh_z)/4,0,h_y/2\right).
\tag{22.15}
$$

(22.5) 和 (22.15) 给出前两式。$|O|\le1$ 意味着任意两个实际律的均值差不超过其总变差的两倍，给出第三式。更具体地，在 $h=(u,0,\sqrt{1-u^2})$、$|u|\le1/2$ 上，(22.5) 的均值除以非零 $A_g$ 就是 $u$，原目标第二分量是 $-(c_du+d\sqrt{1-u^2})/4$；它的导数绝对值至少 $(c_d-d/\sqrt3)/4>0$。这是所测方向量到原目标分量的明确局部映射，不是全场、全方向或高置信度解码器。$\square$

**推论 22.5（二次返回及截止残差的必要比较）。** 对定义 22.1 的获取族，固定任意 $C_0,C_2\ge0$。若一个声称对全部允许场和方向成立的返回证书具有形状

$$
\Delta_{n,h}\le\frac{C_0+C_2g^2}{D}+\rho_{q_{\max}}(g,D),\qquad
\rho_{q_{\max}}(g,D)\ge0,
\tag{22.16}
$$

则在 $D\ge6400$、$0<|g|\le1/4$ 上必须有

$$
\rho_{q_{\max}}(g,D)
 \ge\frac{|g|}{8\sqrt D}-\frac{C_0+C_2g^2}{D}.
\tag{22.17}
$$

若还满足 $\sqrt D\ge16(C_0+C_2g^2)/|g|$，则必要残差至少 $|g|/(16\sqrt D)$。因此，沿原曲线的固定非零 $|g|\le1/4$，不能同时保有 (22.5) 的方向增益、$O(g^2/D)$ 返回成本及 $o(D^{-1/2})$ 截止残差；更一般地，当 $|g|\sqrt D\to\infty$ 时，不能将残差降到 $o(|g|/\sqrt D)$ 而保持 (22.16) 的固定常数。这是首退出加指定完成的障碍，与后续重试算法及截止概率是否已经求出无关。

**证明。** 将同一设备、同一场 (22.13) 和 $h_0=z$ 代入 (22.8)、(22.16) 并比较，得到 (22.17)。第二个条件使 $(C_0+C_2g^2)/D\le|g|/(16\sqrt D)$。最后的渐近断言由此必要残差直接得到，始终要求 $q_{\max}+2\le L_e$。没有假设几何尾，也没有把未计算的截止概率宣告为小量。若 $|g|\sqrt D$ 有界，基线 $C_0/D$ 可以覆盖该下界，这些比较不排除相应证书。$\square$

(22.2)–(22.17) 的供应者是 (13.5)–(13.6) 的原生投影、既有自旋系数、定义 17.1 的同一实际完成、(17.12) 的低降低数比较以及 (19.1)–(19.3) 的原合同。总自旋投影的成熟来源仍为 Bartlett–Rudolph–Spekkens–Turner, *Degradation of a quantum reference frame*, quant-ph/0602069v2，第 III 节及附录 B；有限 CP 通道、范数对偶和旋转权分解只作中间工具。首退出滤波、原始标签加权方向信号与固定完成后未归一化正交块的联合关系是这里的 repo-derived 推导，不主张历史新颖性。一般仪器的方向估计保真度或 Haar 平均整态评分不等于这里对实际 $RK$ 及自身实际边缘的乘积返回距离；静态表示、CAR 或 PB 条件分类和算术存在结果也没有供应本获取族的原生操作或完整输出映射。

本节只约束单脉冲、首个 singlet 即停止且旧口不参与固定完成的获取族；没有建立任意后续控制下的返回下界、任意重试尾、记忆稳定复合或全控制器分类。它也不提供新的原始成功上界见证：局部目标分离不能代替全部场与 $h$ 上的精度及失败率保证，独立弱采样的线性信号与二次边缘成本不能替代完整返回或闭合置信度对数缺口。原 (19.12) 仍保留全部允许辅助、记忆、反馈、探针回用、$L_e,Q_e$、规定终端和全部实际 $K$；既没有对这个全类证明对数必要界，也没有构造合法的归一化趋零反例。

## 追加锚（本行以下为增补区）

## 23. 最终态对数关系的解码后果与直接访问边界

**定义 23.1（原生候选关系及其放宽）。** 固定定义 19.1 的全部精度曲线、允许场、控制器、实际输出和规定终端。在必要条件的比较中固定

$$
n_*(x,y)=(x,y,\sqrt{1-x^2-y^2}),\qquad
\theta_e=32e,\qquad C=\{h\in S^2:h_x\ge1/2\},
$$

其中 $\rho_\theta$ 表示绕 $z$ 轴的正旋转，方向对恰为 $h\in C$、$h'=\rho_{\theta_e}h$。写 $D=D_e$、$m=D-1$、$j=m/2$。对同一个控制器在这个固定场上的最终实际态，记

$$
\begin{aligned}
\Omega_h&\in\mathsf D(R\otimes K),&
\omega_h&=\operatorname{Tr}_R\Omega_h,\\
\Delta_h&=D_{\rm tr}(\Omega_h,\tau_h\otimes\omega_h),&
\delta_*(\mathcal C)&=\sup_{u\in S^2}\Delta_u,\\
F(\rho,\sigma)&=\|\sqrt\rho\sqrt\sigma\|_1.&
\end{aligned}
$$

$F$ 为根保真度，对数为自然对数；$F=0$ 时规定 $-\log F^2=+\infty$，不假设满支撑。以下是一个尚未证明的原生候选关系：存在绝对常数 $A>0$、$B\ge0$，使每个充分小正有理 $e$、每个原始有限控制器及上述每一方向对都满足

$$
-\log F(\omega_h,\omega_{h'})^2
\le A D_e e^2\delta_*(\mathcal C)+B.
\tag{23.1}
$$

这里的控制器不要求已成功；辅助初态、混合性、量子和经典记忆、纠缠、反馈、停止和探针回用仍取原始全部范围。$K$ 包含同一运行的全部实际系统，形式 Kraus 指标不新增实际端口。$\delta_*$ 只对固定 $n_*$ 的方向取上确界，不将它替换为两个端点的误差。

另定义直接访问放宽类：只在原始访问菜单之外增准一次与实际 $n,h$ 无关的 $R\otimes T$ 酉门，其中 $T$ 是独立准备且最终保留的一个辅助量子位；规定终端、场重置上限、原生槽上限及实际端口语义均保留。将 (23.1) 的量词扩至此类是一个更强的断言。这个放宽不授予原始控制器任何新许可。

**命题 23.2（原生条件后果与放宽类的无统一常数反例）。** 有以下两个结论。

1. 若 (23.1) 对原始全部有限控制器成立，则每个原始成功控制器满足

$$
\sup_{n,h}\Delta_{n,h}
\ge\frac{\log(1/(8e))-B}{A D_e e^2}.
\tag{23.2}
$$

因此该候选关系足以推出 (19.12) 的正分支，且相应下极限至少为 $1/A$。

2. (23.1) 在定义 23.1 的直接访问放宽类中不成立。事实上，存在只用两个非平凡实际辅助量子位、一次直接访问门、零次原生槽、一次场重置及恰一次规定终端的等距族 $\mathcal U_e$，以及原球冠旋转族内的方向对 $h_e,h'_e$，使

$$
\begin{aligned}
\delta_*(\mathcal U_e)
&\le\frac{\pi/(16e)+2d}{\sqrt m}
 <\frac1{e\sqrt m},\\
0<F(\omega_{h_e},\omega_{h'_e})^2
&\le4\exp\left(-\frac{49}{2}me^2\right),\\
\frac{-\log F(\omega_{h_e},\omega_{h'_e})^2}
 {D_e e^2\delta_*(\mathcal U_e)+1}
&\longrightarrow+\infty
\quad(e\downarrow0,\ e\in\mathbb Q_{>0}).
\end{aligned}
\tag{23.3}
$$

这些态是实际完整输出的态及其自身的实际边缘；反例不依赖丢弃环境或供应初始纯化。

证明。先核对原始解码消费者。由 (19.2)，$D_h(n_*)=(h_y/2,-h_x/4,0,h_y/2)$。对 $h\in C$ 及 $\theta=32e\le0.32$，

$$
\begin{aligned}
(\rho_\theta h)_y-h_y
&\ge\tfrac12\sin\theta-(1-\cos\theta)\\
&\ge\tfrac\theta2-\tfrac{\theta^3}{12}-\tfrac{\theta^2}{2}
 >\tfrac\theta4.
\end{aligned}
$$

因此第一目标坐标相差大于 $\theta/8=4e$，两个闭 $e$ 成功球不交。取同一实际解码输出落入 $D_h(n_*)$ 的闭 $e$ 球这一效果 $E_h$。原成功条件给出

$$
\operatorname{Tr}(E_h\omega_h)\ge1-e,\qquad
\operatorname{Tr}(E_h\omega_{h'})\le e.
\tag{23.4}
$$

这个效果只用于证明二元测试；控制器和解码器没有依赖未知 $h$。对任意两态 $\rho,\sigma$ 和效果 $0\le E\le I$，插入 $E+(I-E)=I$，再用迹范数三角不等式及 Schatten 范数的 Cauchy–Schwarz 不等式，得到

$$
F(\rho,\sigma)
\le\sqrt{\operatorname{Tr}(E\rho)\operatorname{Tr}(E\sigma)}
 +\sqrt{\operatorname{Tr}((I-E)\rho)\operatorname{Tr}((I-E)\sigma)}.
\tag{23.5}
$$

例如第一项的算子因式分解为
$\sqrt\rho\sqrt E\,\sqrt E\sqrt\sigma$，其迹范数不超过两个 Hilbert–Schmidt 范数的乘积。由 (23.4)–(23.5)，同一实际 $K$ 上有 $F(\omega_h,\omega_{h'})^2\le4e\le8e$。若 (23.1) 成立，移项即给 $\delta_*(\mathcal C)\ge[\log(1/(8e))-B]/(A D_e e^2)$；再用 $\sup_{n,h}\Delta_{n,h}\ge\delta_*(\mathcal C)$，对原成功类取下确界，得到 (23.2)。除以 $\log(1/e)/(D_e e^2)$ 并取正有理下极限即得第一项。

以下构造只属于直接访问放宽类。令

$$
A_y=\frac{J_y}{j},\qquad
 g_e(x)=
 \begin{cases}
 0,&x\le-8e,\\
 \displaystyle\frac{\pi(x+8e)}{32e},&-8e<x<8e,\\
 \pi/2,&x\ge8e,
 \end{cases}
\qquad
 |t_e(x)\rangle=\cos g_e(x)|0\rangle+\sin g_e(x)|1\rangle.
\tag{23.6}
$$

$g_e$ 在 $[-1,1]$ 上的 Lipschitz 常数为 $L_g=\pi/(32e)$。独立准备 $T$ 为 $|0\rangle$，直接访问门明确取为

$$
W_e=\exp[-i g_e(A_y)\otimes Y_T].
\tag{23.7}
$$

它在 $A_y$ 的每个本征值 $a$ 上将 $|0\rangle_T$ 送到 $|t_e(a)\rangle_T$，是有限维、确定性且与实际 $n,h$ 无关的一个酉门。随后从原场源独立重置令牌 $S_t$，其态为 $\rho_n(+d e_x)$，施行恰一次规定的
$U_{\rm term}=\exp[-idJ\cdot\sigma/m]$。全部实际非参考量子系统就是 $K=T\otimes S_t$；如显式携带固定程序、计数和路由因子，则将它们以相同的 $h$ 无关状态张量到 $K$。没有原生槽，因而没有生成任何原生 $H,E$；两个酉门没有被约化掉的实际环境。一次重置不超过 $Q_e$，零次原生槽不超过 $L_e$。额外门 (23.7) 正是本构造超出原菜单的地方。

先证明对全部方向的完整返回上界。相干态可在数学上写成 $|h\rangle^{\otimes m}$。仅为计算谱分布，令 $X_1,\ldots,X_m$ 是独立的 $\pm1$ 变量，其均值为 $h_y$。$A_y$ 在 $\tau_h$ 中的谱律就是 $m^{-1}\sum_iX_i$ 的律，因此

$$
\langle A_y\rangle_{\tau_h}=h_y,\qquad
\langle(A_y-h_y)^2\rangle_{\tau_h}=\frac{1-h_y^2}{m}.
\tag{23.8}
$$

这里没有将参考拆分为可访问的 $m$ 个量子位，也没有产生这组经典变量的实际读数。由 (23.6) 的 Lipschitz 界及 $A_y$ 各谱空间的正交性，

$$
\begin{aligned}
&\left\|W_e(|j,h\rangle|0\rangle)
 -|j,h\rangle|t_e(h_y)\rangle\right\|^2\\
&\qquad=\mathbb E\left\||t_e(m^{-1}\textstyle\sum_iX_i)\rangle
                         -|t_e(h_y)\rangle\right\|^2
 \le L_g^2\frac{1-h_y^2}{m}
 \le\frac{L_g^2}{m}.
\end{aligned}
\tag{23.9}
$$

纯态迹距离不超过这里的向量距离。规定终端的参考透明比较，取只用于证明的
$U_h^0=I_R\otimes u_h$，其中 $u_h=\exp[-id h\cdot\sigma/2]$。对任意 $S_t$ 向量 $\psi$，

$$
\left\|\left(\frac{J\cdot\sigma}{m}
          -I_R\otimes\frac{h\cdot\sigma}{2}\right)
             (|j,h\rangle\otimes\psi)\right\|
\le\frac{\|\psi\|}{\sqrt m}.
\tag{23.10}
$$

在 $h=z$ 的证明坐标，差算子作用于最高权向量时仅剩
$m^{-1/2}|j,j-1\rangle\otimes\sigma_+\psi$；共同旋转给任意 $h$。Duhamel 公式中理想演化始终保持这个最高权参考，故终端的向量误差至多为 $d/\sqrt m$。结合 (23.9)、迹距离收缩性及三角不等式，真实终态与乘积态

$$
\Gamma_h=\tau_h\otimes|t_e(h_y)\rangle\langle t_e(h_y)|
             \otimes u_h\rho_n(+d e_x)u_h^\dagger
$$

的迹距离不超过 $(L_g+d)/\sqrt m$。偏迹给实际 $\omega_h$ 与 $\Gamma_h$ 的 $K$ 边缘同一距离界。因此再用一次三角不等式，

$$
\Delta_h\le\frac{2(L_g+d)}{\sqrt m}
 =\frac{\pi/(16e)+2d}{\sqrt m}
 <\frac1{e\sqrt m}.
\tag{23.11}
$$

这对每个 $h$ 及每个允许场的终端令牌都成立；取固定 $n_*$ 的方向上确界即得 (23.3) 第一式。比较态 (23.11) 的第二因子已经是实际边缘，不是 $\Gamma_h$ 的理想边缘。

再取原球冠旋转族内的精确一对

$$
h_e=(\cos(16e),-\sin(16e),0),\qquad
h'_e=\rho_{32e}h_e=(\cos(16e),\sin(16e),0).
\tag{23.12}
$$

$e\le1/100$ 保证 $h_e\in C$。置 $s=\sin(16e)$，由 $\sin x\ge x-x^3/6$ 得 $s\ge15e$。对均值为 $-s$ 的方向，在 $A_y\le-8e$ 的全部谱空间上，$T$ 准确为 $|0\rangle$；对均值为 $s$ 的方向，在 $A_y\ge8e$ 的全部谱空间上，$T$ 准确为 $|1\rangle$。独立 $\pm1$ 平均的单侧 Hoeffding 界于是给

$$
\Pr_{h_e}(T=1),\quad\Pr_{h'_e}(T=0)
\le\exp\left[-\frac m2(s-8e)^2\right]
\le\exp\left[-\frac{49}{2}me^2\right]=:\varepsilon_e.
\tag{23.13}
$$

这里的概率指最终实际 $T$ 的计算基效果。终端只作用于 $RS_t$，精确保留这个边缘。为核对所用尾界，对任意 $\pm1$ 变量 $X$，函数
$\phi(t)=\log\mathbb E\exp[t(X-\mathbb EX)]$ 满足
$\phi(0)=\phi'(0)=0$、$\phi''(t)=\operatorname{Var}_t(X)\le1$，所以 $\phi(t)\le t^2/2$。独立相乘并以 Markov 不等式优化 $t$，得到平均偏离均值至少 $a>0$ 的单侧概率不超过 $\exp(-ma^2/2)$。故 (23.13) 包括端点谱空间且无需任何近似或实际选支。

将 (23.5) 直接用于完整实际 $K$ 上的效果 $|0\rangle\langle0|_T\otimes I_{S_t}$，得到
$F(\omega_{h_e},\omega_{h'_e})\le2\sqrt{\varepsilon_e}$，即 (23.3) 第二式的上界。同一纯辅助、同一个 $W_e$ 和同一个实际终端保持全态向量的内积，而偏迹不能降低根保真度，故

$$
F(\omega_{h_e},\omega_{h'_e})
\ge|\langle j,h_e|j,h'_e\rangle|
 =\cos(16e)^m>0.
\tag{23.14}
$$

因此这些对数都是有限的，没有利用零支撑的约定制造无穷大。

最后，由 (19.1)，$D\ge9k_e/e\ge2$ 且 $m=D-1\ge D/2$，所以

$$
me^2\ge\frac92 k_e e
 \ge9216 e^{-1}\log(18/e)\longrightarrow+\infty.
$$

置 $z_e=e\sqrt m\to+\infty$。由 (23.11)、$D=m+1\le2m$ 及 (23.13)，对所有充分小的正有理 $e$，

$$
\frac{-\log F(\omega_{h_e},\omega_{h'_e})^2}
 {D_e e^2\delta_*(\mathcal U_e)+1}
\ge\frac{(49/2)z_e^2-\log4}{2z_e+1}
\longrightarrow+\infty.
\tag{23.15}
$$

若存在统一 $A,B$ 使放宽后的 (23.1) 成立，左端反而至多为 $\max\{A,B\}$，矛盾。这排除所有统一常数及任何充分小精度窗口，证明第二项。$\square$

(23.3)–(23.15) 的承重内容是同一原球冠方向对、Lipschitz 谱读出、全部方向上的完整乘积返回和规定终端的联合反例。相干态及原目标复用 §§13、19；谱演算、Hoeffding 尾界、保真度的效果上界、偏迹单调性和 Duhamel 比较是中间成熟工具。此处给出仓内推导，不主张历史新颖性。静态 Hilbert、PB、CAR 条件或算术层和均不提供 (23.7) 的原生实现。

该反例表明：即使保留全部等距输出、唯一初始方向源、原资源曲线、全方向统一返回和规定终端，单凭这些最终态性质也不能推出 (23.1)。未补的对应恰是：能否在至多 $L_e$ 个原生 $V$、至多 $Q_e$ 次场重置及全部实际记录约束下，获得满足相同保真度与返回估计的合法实现；或者原生全历史约束能否证明 (23.1)。门 (23.7) 直接耦合 $R$，不能因其为有限酉门或 CPTP 而取得原生实现许可。本反例未提供上述实现，也未提供全部场及方向上的原成功解码器。因此它只否定直接访问放宽后的关系；原生候选关系 (23.1) 及原始 (19.12) 均仍未解决。

## 追加锚（本行以下为增补区）

## 24. 相干原生标签的有限受控反射与完整截止通道

**定义 24.1（接口、记录与误差域）。** 保持 (19.1) 的正有理数域 $0<e\le1/100$、全部场及方向、$D=D_e$、$m=D-1=2j$、$L=L_e$ 和 $Q_e$。本节只在 (13.6)、定义 19.1 明确供应的相干等距

$$
V=\Pi_+\otimes|++\rangle_{HE}+\Pi_-\otimes|--\rangle_{HE}
\tag{24.1}
$$

后处理其两个非参考输出；不将 (12.1) 的经典仪器当作相干等距。定义

$$
Q_D=\Pi_+-\Pi_-=\frac{I+2J\cdot\sigma_S}{D},\qquad
C Q_D=|0\rangle\langle0|_c\otimes I_{RS}
       +|1\rangle\langle1|_c\otimes Q_D .
\tag{24.2}
$$

$M$ 表示任意有限旧量子及经典记忆和旁观者，包括此前已经产生的原始记录；输入 $X$ 是整个 $RScM$ 上的任意算子，态输入不要求纯、乘积或无纠缠。下述操作恒等作用于 $M$。新输出总口 $Z$ 包含每次实际产生的 $H,E$、原始测量结果及其全部实际副本、测后系统、读出输出、计数、停止和截止标记以及工作空间。比较两通道时使用同一个 $RScMZ$，不对实际输出取边缘来取得结论。记 $\|\cdot\|_\diamond/2$ 为半 diamond 范数。

允许的非 $R$ 处理按定义 19.1 的有限 CP 节点及其声明的实际端口解释。这里选用的读出是两个标签的 $X$ 基 Lüders 仪器，并完整输出测后标签和结果；若为结果制造有限个指针、复制或读出寄存器，全部输出均明确包括。没有先在 $|+\rangle,|-\rangle$ 基退相干、读取或复制总自旋标签 $b$。已有的任何原始经典记录仍在 $M$，不擦除、不改写。定义 13.2、17.1、22.1 的指定协议先退相干并保留 $b$，与这里的这个选择不同。相干接口 (24.1) 和允许处理非 $R$ 输出是本构造的必要前提；命题 24.3 给出先产生且保留 $b$ 时的相反结论。

**定理 24.2（有限原生受控反射的完整通道）。** 对任意整数 $q\ge1$，存在一个只用至多 $q$ 次 forward $V$、零次场重置的有限前缀 $\mathsf G_q$，以及正算子 $\sigma_{s,q},\sigma_{f,q}$，满足

$$
\begin{aligned}
\mathsf G_q(X)
 &=U XU^\dagger\otimes\sigma_{s,q}
   +W U XU^\dagger W^\dagger\otimes\sigma_{f,q},\\
U&=C Q_D\otimes I_M,\qquad W=Q_D\otimes I_{cM},\\
\operatorname{Tr}\sigma_{s,q}&=1-2^{-q},\qquad
\operatorname{Tr}\sigma_{f,q}=2^{-q},\qquad
\sigma_{Z,q}=\sigma_{s,q}+\sigma_{f,q}\in\mathsf D(Z).
\end{aligned}
\tag{24.3}
$$

两个算子的支撑由保留的成功/截止标记分开，且均与每个输入、实际 $n,h$ 无关。新辅助准备均为已知有限态，不接入任何混合输入的纯化；同一 $S$ 在重试中回用。完整输出满足精确等式

$$
\frac12\left\|\mathsf G_q-
       \bigl(X\mapsto UXU^\dagger\otimes\sigma_{Z,q}\bigr)
       \right\|_\diamond=2^{-q}.
\tag{24.4}
$$

这里的范数仍稳定于任意额外参考；因而 (24.3)–(24.4) 覆盖任意混合联合输入、控制位叠加和与 $M$ 的纠缠。取

$$
\eta_e=\frac{e}{D_eL_e},\qquad
q_e=\left\lceil\log_2\frac{D_eL_e}{e}\right\rceil
\tag{24.5}
$$

即得所述半 diamond 误差至多 $\eta_e$，绝对调用常数可取 $C_0=1$。此为前缀，不在其中调用规定终端；接回原控制器时终端仍须恰执行一次。

证明。先固定两个标签的已知基

$$
|x_X\rangle=\frac{|+\rangle+(-1)^x|-\rangle}{\sqrt2},
\qquad x\in\{0,1\}.
$$

第一槽后只在 $cH$ 上施行

$$
F_{cH}=|0\rangle\langle0|_c\otimes I_H
       +|1\rangle\langle1|_c\otimes Z_H,
\qquad Z_H=|+\rangle\langle+|-|-\rangle\langle-|.
\tag{24.6}
$$

它不是 controlled-$V$，也不作用于 $R$。随后测量 $H,E$ 的上述 $X$ 基。具体选择输出原始结果 $B$ 和读出副本 $F$ 的非 $R$ 仪器，其四个完整结果算子为

$$
L_{xy}=P_{xy}\otimes|xy\rangle_B\otimes|xy\rangle_F,
\qquad P_{xy}=|x_Xy_X\rangle\langle x_Xy_X|,
\qquad\sum_{x,y}L_{xy}^\dagger L_{xy}=I_{HE}.
$$

这里 $B,F$ 均由已知空白寄存器开始，$F$ 是确实制造并输出的读出/复制系统；完整节点为 $Y\mapsto\sum_{xy}L_{xy}YL_{xy}^\dagger$，测后 $H,E$、$B,F$ 都保留。它是允许的有限 CP 仪器的具体选择，没有另行声明的实际输出。给定 $(x,y)$ 后，$H,E$ 恰在 $|x_Xy_X\rangle$，$B,F$ 恰在相应基态；进一步的记录复制、奇偶计算及计数只用这些基态作控制，故其保留输出也仅取决于读数。于是条件新辅助态独立于原输入是这个秩一投影及复制的后果，并非预先供应的 clean instrument 假设。该 CP 节点的代数 Kraus 指标不是另一个实际系统。若选用另一个读出实现且有额外实际输出，必须将它们加入完整口重证；不能把包含额外 $b$ 副本的读出冒充这个仪器。

将 (24.1)、(24.6) 与这两个投影相乘，得到在整个 $RSc$ 上的矩阵恒等式

$$
\begin{aligned}
K^{(c)}_{xy}
 &:=(\langle x_Xy_X|\otimes I_{RSc})F_{cH}V\\
 &=\frac12\left(\Pi_+\otimes I_c+
          (-1)^{x+y}\Pi_-\otimes Z_c\right)
  =\frac12(Q_D^{p}\otimes I_c)C Q_D,\qquad
p=x\mathbin\oplus y .
\end{aligned}
\tag{24.7}
$$

特别地，每个结果的效果都是 $I/4$。该等式包括 $|0\rangle\langle1|_c$ 交叉块，不能只用控制位的经典混合证明它。$\Pi_\pm$ 是互补正交投影，故 $Q_D=Q_D^\dagger=Q_D^{-1}$；在 (24.7) 中 $Q_D$ 与 $C Q_D$ 交换。若 $p=0$，已取得所需门；若 $p=1$，只有一个已知的额外 $Q_D$ 待校正。这里没有把这个额外门当作免费操作。

校正每次再调用同一个 forward $V$，不再施行 (24.6)，并作同一完整 $X$ 读出。此时

$$
K^{(u)}_{xy}=\frac12\left(\Pi_++(-1)^{x+y}\Pi_-\right)
           =\frac12 Q_D^{p}.
\tag{24.8}
$$

若 $p=0$，残留的 $Q_D$ 不变，继续；若 $p=1$，$Q_D^2=I$ 消掉残留，立即停止。第一次成功之后不再调用 $V$。共调用 $q$ 次仍未成功则停止并标记截止，保留那条分支。每个后续槽都由已经产生的经典 $(x,y)$ 决定是否执行；没有量子相干的“调用/不调用”门、$V^\dagger$、直接 $R$ 门、后选择或无限等待。

完整历史 $w=((x_1,y_1),\ldots,(x_r,y_r))$ 的长度 $r\le q$，满足以下二者之一：第一奇偶为零，或第一奇偶为一、其后先有若干零而在首次一处停止；截止历史则第一奇偶为一、其后直到 $q$ 都为零。由 (24.7)–(24.8)，每条成功历史的作用算子是 $2^{-r}U$，每条截止历史是 $2^{-q}WU$。因此对包括 $M$ 在内的每个输入，历史概率分别为 $4^{-r}$、$4^{-q}$，没有依赖输入的归一化。

以 $\zeta_w$ 表示该历史的全部新实际输出态，包含所有测后 $H,E$、原始 $(x_i,y_i)$ 和实际副本、读出输出、保留工作空间、调用计数、停止及截止标记。每条历史上的这些系统仅由已知输入和有限的非 $R$ 记录处理制成，故 $\zeta_w$ 固定且不含输入信息。为比较同一输出空间，可以预留 $q$ 组有限空白寄存器，未调用槽保持空白并带未使用标记；这不执行额外原生槽，也不擦除实际输出。定义

$$
\sigma_{s,q}=\sum_{w\ {\rm success}}4^{-|w|}\zeta_w,
\qquad
\sigma_{f,q}=\sum_{w\ {\rm cutoff}}4^{-q}\zeta_w.
\tag{24.9}
$$

长度 $r$ 的成功历史总权重为 $2^{-r}$，截止历史总权重为 $2^{-q}$，给出 (24.3)。这同时证明了所有计数、路由、原始读数和 cutoff 分支上的独立性，而非只证明成功分支的条件门。混合辅助若用于制造指针，直接进入 $\zeta_w$，不为它们引入可访问的纯化。

从 (24.3) 减去比较通道，差恰为

$$
\bigl(\operatorname{Ad}_{WU}-\operatorname{Ad}_U\bigr)(X)
       \otimes\sigma_{f,q}.
\tag{24.10}
$$

任意两通道的 diamond 距离至多二，张量一个正算子按其迹缩放范数，故半范数至多 $2^{-q}$。反向，取 $c=0$，在 $\Pi_\pm$ 的各一个单位向量 $u_\pm$ 上准备
$\psi=(u_++u_-)/\sqrt2$。两投影的秩均非零，因为 $j>0$。$U\psi=\psi$，而 $W\psi=(u_+-u_-)/\sqrt2$ 与它正交；(24.10) 的半迹范数恰为 $\operatorname{Tr}\sigma_{f,q}$。这证明 (24.4)，没有取走任何实际记录。矩阵恒等式及稳定通道范数已证明所有混合与纠缠情形，不需要初态纯化。$\square$

**命题 24.3（先保留总自旋原始读数时，直接擦除路线失效）。** 若在上述第一槽上另行制造并永久保留原始 $b\in\{+,-\}$ 的经典记录 $B_0$，再对两个标签作 (24.6) 及 $X$ 读出，则 (24.7) 不再是该完整仪器的结果算子。精确结果算子应为

$$
K_{xy,b}=\frac12(-1)^{(x+y)\mathbf1_{b=-}}
       \Pi_b\otimes Z_c^{\mathbf1_{b=-}},
\tag{24.11}
$$

并附上原始 $b$、测后标签及所有实际读出。对任何随后仍保留 $B_0$ 的确定性校正，不论其长度，对任何输入无关 $\sigma_Z$，完整通道与
$X\mapsto C Q_D X(C Q_D)^\dagger\otimes\sigma_Z$ 的半 diamond 距离至少 $1/2$。这个结论只针对直接把待作用的 $RS$ 送入上述已记录第一槽的路线，不是全部原生控制器的不可实现性定理。

证明。记录 $B_0$ 使两个 $b$ 不再能够在同一 Kraus 项中相加，立即给出 (24.11)。在 $c=0$ 和两个输入 $|u_\pm\rangle\langle u_\pm|$ 上，实际 $B_0$ 律分别为确定的 $+$ 和 $-$；任何保留该记录的后续操作保持这两个律。理想通道的 $B_0$ 律则在两输入上相同。任一固定二元律到这两个点质量的总变差最大值至少 $1/2$；偏迹和测量的收缩性给出所述下界。亦可取扇区叠加的正、负两种相对相位：已经产生经典记录的第一槽将其变成同一态，后续确定性操作不能恢复二者。这里不把一个 $b$ 副本改名为读出环境后取走，也不借此禁止在第一槽之前用其它探针或编码的控制器。$\square$

因此定理 24.2 使用的是未先产生经典 $b$ 的两个相干标签，而不是擦除定义 12.1 仪器或既有协议必须保留的原始读数。如果所供应的实际接口只有经典仪器，或还强制输出一个不可改写的 $b$ 副本，本节的受控反射实现不成立；正是这个额外输出的对应必须核对。反之，在 (24.1) 的指定相干接口下，原始经典读数是所实施 $X$ 仪器的 $(x,y)$，它们在 (24.9) 中全部保留。物理实现若生成未列出的额外输出，仍须按定义 19.1 补入完整口重新验证，不能以本节的指定 CP 端口替代它。

**命题 24.4（原曲线上的槽数及误差成本）。** 定理 24.2 在整个 (19.1) 的精度域内有 $q_e\le L_e$，且沿正有理 $e\downarrow0$，

$$
\begin{aligned}
N_e&=\Theta(e^{-4}\log(1/e)),\\
D_e&=8{,}000{,}000N_e^2
     =\Theta(e^{-8}\log^2(1/e)),\\
L_e&=10N_e=\Theta(e^{-4}\log(1/e)),\\
q_e&=\Theta(\log(1/e)).
\end{aligned}
\tag{24.12}
$$

但是，对固定 $\kappa>0$，若要求同一几何截止证书的误差至多
$\eta'_e=\exp(-\kappa m_e e^2)$，其充分截止选择为

$$
q'_e=\left\lceil\frac{\kappa m_e e^2}{\log2}\right\rceil
      =\Theta(m_e e^2),\qquad
\frac{q'_e}{L_e}\longrightarrow+\infty .
\tag{24.13}
$$

后式限制这一个证书在原预算内支付指数精度的能力，不是所有原生实现的成本下界。

证明。由 (19.1)，$k_e\le10N_e/3$ 且
$N_e\ge(3/10)2048e^{-2}\log(18/e)\ge1/e$。所以
$9k_e/e\le30N_e/e\le30N_e^2<8{,}000{,}000N_e^2$；后者为整数，证明 $D_e$ 的精确等式。于是

$$
q_e=\left\lceil\log_2\frac{80{,}000{,}000N_e^3}{e}\right\rceil
 \le27+4\lceil\log_2N_e\rceil
 \le27+4N_e\le10N_e,
\tag{24.14}
$$

最后一步使用 $N_e\ge N_*>5$。$\ell_e=\Theta(e^{-4}\log(1/e))$ 比 $k_e$ 和固定 $N_*$ 主导，给出 (24.12)。把 $2^{-q}$ 的充分误差证书设为 $\eta'_e$ 即得 (24.13) 的首式。更明确地，所选充分调用数满足

$$
\frac{q'_e}{L_e}
 \ge\frac{\kappa}{\log2}
    \left(800{,}000N_e e^2-\frac{e^2}{10N_e}\right),
\qquad
N_e e^2\ge\frac56\,32768e^{-2}\log(90/e)\longrightarrow+\infty.
\tag{24.15}
$$

这是充分方案自身所需的截止参数的比较，不将一个上界方案变成原生最优成本下界。$\square$

**定理 24.5（同一完整输出上的有限复合及自身边缘返回）。** 在一个固定有限电路中，令 $s$ 次反射访问各用上述实现，精度为 $\eta_i$，最坏调用数为 $q_i$。每次访问都包括其全部新口 $Z_i$；旧的 $Z_1,\ldots,Z_{i-1}$、旧探针、纠缠和任意记忆属于该次访问的完整输入。其间的允许非 $R$ 操作、记录处理和反馈在实际与比较电路中相同，全部原始记录保持。比较电路只将第 $i$ 次访问换成精确 $Q_D$ 或 $C Q_D$，并在同一 $Z_i$ 准备该次的 $\sigma_{Z,i}$，不删去这些因子。若其余原生调用、前缀场重置的最坏上限分别为 $a,b$，则实际资源满足

$$
T_V\le a+\sum_{i=1}^s q_i,\qquad
T_{\rm reset}\le b+1,\qquad T_R\le a+\sum_{i=1}^s q_i+1,
\tag{24.16}
$$

其中加一是接回原控制器后使用新鲜、独立且此前未经改动的原场 $+d e_x$ 令牌；必须满足 (24.16) 的两项分别不超过 $L_e,Q_e$。规定的
$U_{\rm term}=\exp[-idJ\cdot\sigma/m_e]$ 恰执行一次，不纳入 $T_V$，其量子输出及任何实际环境和记录仍在同一最终口 $K$。前缀不执行终端，也不另供应其逆。

以 $\Omega_{n,h}$、$\widetilde\Omega_{n,h}$ 记两条完整电路在这个终端之后的态，连同全部 $Z_i$、停止标记和截止分支，则

$$
D_{\rm tr}(\Omega_{n,h},\widetilde\Omega_{n,h})
 \le E:=\min\left\{1,\sum_{i=1}^s\eta_i\right\}.
\tag{24.17}
$$

若比较电路相对于其自身实际口的返回证书是
$D_{\rm tr}(\widetilde\Omega_{n,h},\tau_h\otimes
 \operatorname{Tr}_R\widetilde\Omega_{n,h})\le\widetilde\delta_{n,h}$，则真实电路满足

$$
D_{\rm tr}(\Omega_{n,h},\tau_h\otimes
                  \operatorname{Tr}_R\Omega_{n,h})
 \le\min\{1,\widetilde\delta_{n,h}+2E\}.
\tag{24.18}
$$

特别地，各次均取 (24.5) 且 $s q_e+a\le L_e$ 时，

$$
E\le\frac{s e}{D_eL_e}\le\frac{e}{D_e},\qquad
\overline\delta_{\rm actual}
 \le\min\left\{1,\overline{\widetilde\delta}
                +\frac{2s e}{D_eL_e}\right\}
 \le\min\left\{1,\overline{\widetilde\delta}+\frac{2e}{D_e}\right\}.
\tag{24.19}
$$

证明。在每个访问处用 (24.4) 作一次通道替换，把此前全部实际输出纳入稳定化的记忆。逐次采用“已比较前缀、实际后缀”的 telescoping 展开，每项半 diamond 范数至多相应 $\eta_i$；包括条件记录处理和终端在内的公共 CPTP 后缀收缩迹距离。所有截止分支都在通道内求和，所以没有为获得 (24.17) 选取成功运行。反馈即使读取旧 $Z_i$，也在两电路使用相同映射；此时不能再把最终 $Z_i$ 宣称与逻辑系统独立，但 (24.17) 仍然成立。若逻辑电路不读取新记录，则比较输出精确带有 $\bigotimes_i\sigma_{Z,i}$ 的独立因子。

(24.16) 对每一条分支按最坏槽数相加，实际少用的调用不算额外消耗。固定场令牌是纯态，因为 $n:U\to S^2$；这不把其它混合辅助改为纯态。最后，在 (24.18) 中先插入 $\widetilde\Omega_{n,h}$，再插入
$\tau_h\otimes\operatorname{Tr}_R\widetilde\Omega_{n,h}$；第一项由 (24.17) 至多 $E$，最后一项由偏迹收缩性至多 $E$。目标中的边缘因此确为实际的 $\operatorname{Tr}_R\Omega_{n,h}$，没有用理想边缘替换它。所有界对 $n,h$ 一致，得 (24.19)。$\square$

**推论 24.6（特定 QSVT 访问前提及投影边界）。** 在定理 24.2 的相干接口和完整端口下，现有 QSVT 所需的特定逻辑酉、逆和受控酉可以分别取 $Q_D,Q_D,C Q_D$。不受控访问直接由同一实现把 $c$ 固定为 $1$ 取得，$c$ 及其固定输出仍保留；不另假设可调用 $V^\dagger$。取已知逻辑探针 $|+y\rangle_S$ 和

$$
P=I_R\otimes|+y\rangle\langle+y|_S.
$$

其压缩精确为

$$
(\langle+y|_S\otimes I_R)Q_D(|+y\rangle_S\otimes I_R)
 =\frac{I+2J_y}{D}
 =\frac{I}{D}+\frac{D-1}{D}\frac{J_y}{j}
 =:A_D.
\tag{24.20}
$$

$P$ 的相位门 $e^{i\phi(2P-I)}$、$P$ 控制的 NOT 及其所需额外控制只作用于 $S$ 和非参考辅助系统；探针的已知准备和基变换也只作用于非 $R$。因此它们不是 $R$ 门或未知 $h$ 依赖的控制。$A_D$ 是原始 $J_y/j$ 的已知仿射压缩，不能省去其中的 $I/D$ 偏移或 $(D-1)/D$ 尺度。

证明。$Q_D$ 的自伴及逆已由互补投影证明，固定 $c=1$ 的限制在 (24.3) 中直接给 $Q_D$，且保持同样的完整输出误差。$|+y\rangle$ 的三个 Pauli 均值为 $(0,1,0)$，给 (24.20)。其余控制只含上述已知投影及已供应的受控 $Q_D$。

具体采用 Gilyén–Su–Low–Wiebe, [*Quantum singular value transformation and beyond*, arXiv:1806.01838](https://arxiv.org/abs/1806.01838)，定义 15、定理 17、推论 18、引理 19：代入 $U=Q_D$、$\Pi=\widetilde\Pi=P$。定义 15 中的 $U^\dagger$ 在此仍是 $Q_D$；引理 19 的 projector-controlled NOT 只需上述非 $R$ 控制，受控序列的奇数情形所需的一次 controlled-$U$ 由 (24.7) 支付。对满足该文相应相位/奇偶及区间有界条件的多项式，理想交替相位序列具有该文所给的投影块；例如推论 18 要求实多项式具有次数对应的奇偶性且在 $[-1,1]$ 上绝对值不超过一。用本节前缀替换其中 $s$ 次逻辑访问后，完整序列的通道误差和资源由 (24.16)–(24.19) 支付，所有访问记录仍保留。

这只供应特定酉访问与控制的接口。QSVT 的等式是投影块等式，并不把投影块提升为确定性的完整输出通道；本节既没有对任意指定函数证明其逼近次数及相位条件，也没有把 §23 的 clipped 门 (23.7) 构造成合法的原生完整通道。实际近似通道亦没有被宣称为同一输出空间上的精确可逆酉：每个 $Q_D^{-1}$ 调用由新的前缀及新的记录因子实现，并以定理 24.5 比较，不能反向擦除旧记录。$\square$

**注记 24.7（来源、精度与原目标边界）。** 相干原生槽及允许的非参考处理来自 (13.6)、定义 19.1；有限 Lüders 仪器、记录细化、CPTP 复合和稳定通道范数使用本卷及 OTF001 的有限 CP 语义。Paetznick–Svore, [*Repeat-Until-Success: Non-deterministic decomposition of single-qubit unitaries*, arXiv:1311.1074v2，第 3、3.2 节](https://arxiv.org/html/1311.1074v2)，供应成熟的“读出结果—可逆失败—重试”框架，但其原文的单 qubit 门集和期望成本不直接给这里的原生接口、完整口或最坏调用数。(24.7)–(24.10) 给出本接口的实际仪器及有限截止推导；(24.16)–(24.19) 是在同一个完整实际输出上的复合与返回后果。这些是普通数学证明，不主张 Lean 核验、历史新颖性或封闭系统物理实现。

多项式精度 $e/(D_eL_e)$ 只给加性通道误差，不能保持 §23 的 $\exp[-\Theta(m_e e^2)]$ 小保真度；一个加性误差也不能被当作相同指数的相对误差。若为此要求指数小误差，本节这个几何截止充分证书的成本由 (24.13)–(24.15) 给出，超出 $L_e$。这既未排除其它原生实现，也未证明原生候选关系 (23.1)。§§21–22 的指定协议排除范围和 §23 的直接访问放宽反例范围不变。

完整估计器仍须在全部原始 $n,h$ 上满足 (19.2) 的 $e$ 精度、$1-e$ 成功率、原始两项调用上限、规定终端和对全部实际 $K$ 自身边缘的返回要求。二元判别、这个受控反射或一个 QSVT 投影块均不满足这些全部条件。足以推进反例方向的未来完整返回目标是 $O(1/(D_e e^2))$；本节没有给出这一估计器，也没有给出沿合法正有理精度列的 $o(\log(1/e)/(D_e e^2))$ 原始成功见证。因此 (19.12) 的两种结算方向仍未解决。

## 追加锚（本行以下为增补区）

## 25. 有限全方向估计器的直接参考访问反例与精确原生前缀障碍

**定义 25.1（同一实际估计器的风险与返回）。** 全部精度参数沿定义 19.1 的正有理曲线：$0<e\le1/100$，$m=m_e=D_e-1$，$j=m/2$，$L=L_e=10N_e$，$Q=Q_e=18N_e+1$，$d=1/64$，$\tau_0=1$。参考空间仍为 $R=\operatorname{Sym}^m(\mathbb C^2)$，唯一初始未知方向源为 $\tau_h=|e_h\rangle\langle e_h|$。所有准备和控制参数均不依赖实际 $h,n$。固定允许场

$$
 n_*(x,y)=(x,y,\sqrt{1-x^2-y^2}),\qquad x^2+y^2<1/9.
 \tag{25.1}
$$

对这个场，(19.2) 的目标为 $(h_y/2,-h_x/4,0,h_y/2)$。一个固定有限解码器输出两个有理数 $(\widehat a,\widehat b)$，完整输出解释为 $(\widehat a,\widehat b,0,\widehat a)$。对包括规定终端的同一个过程 $\Omega_h$，定义

$$
\begin{aligned}
 \beta_e&=\sup_{h\in S^2}\Pr_h\!\left[
 \max\{|\widehat a-h_y/2|,|\widehat b+h_x/4|\}>e\right],\\
 \delta_e&=\sup_{h\in S^2}D_{\rm tr}\!\left(
 \Omega_h,\tau_h\otimes\operatorname{Tr}_R\Omega_h\right),
 \qquad D_{\rm tr}(X,Y)=\tfrac12\|X-Y\|_1.
\end{aligned}
\tag{25.2}
$$

$K$ 在这里始终是该过程自己的全部实际非参考输出：原始记录、实际副本、解码和工作输出、旧记忆、探针、场令牌、程序、路由、补偿和终端输出均保留。约化 CP 节点的形式 Kraus 指标只标记代数求和；它不自动是实际端口，另行产生的实际环境却必须计入 $K$。

所考察的原生候选必要关系是：存在绝对 $c_0,c_1>0$ 及一个正有理精度窗口，使每个原始有限原生控制器及其实际解码器满足

$$
 \beta_e+\delta_e\ge c_0\exp(-c_1m_e e^2\delta_e).
 \tag{25.3}
$$

它保留定义 19.1 的全部场、混合辅助、量子与经典记忆、反馈、探针回用、最坏调用上限和规定终端。本节另考察一个明确的放宽：在获取阶段允许一个直接作用于 $R$ 的、有限且与 $h,n$ 无关的约化 CPTP 仪器；其余完成过程仍用定义 17.1。这个额外 CP 节点没有被赋予原生槽成本，也不是原合同所许可的 $R$ 操作。

**命题 25.2（原曲线、场及尺度）。** 场 (25.1) 满足定义 19.1 的全部场承诺。在精确原曲线上，

$$
\begin{gathered}
 D=8{,}000{,}000N_e^2,\qquad m\ge D/2,\qquad m>L+1,\\
 N_e\ge600e^{-2}\log(1/e),\qquad
 De^3\ge C_{\rm curve}e^{-1}\log^2(1/e),\qquad
 C_{\rm curve}=2{,}880{,}000{,}000{,}000.
\end{gathered}
\tag{25.4}
$$

特别地 $t:=me^2\to\infty$ 且 $et\to\infty$，极限取正有理 $e\downarrow0$。

证明。$n_*$ 的前两个分量使其微分处处秩二；两条闭 $r=1/4$ 轴段均在开圆盘内。在原点两条轴向一阶导数的范数均为一；沿任一轴段，二阶导数的范数为 $(1-u^2)^{-3/2}<2$。在原点 $n_*=e_z$、$n_{*,x}=e_x$、$n_{*,y}=e_y$，逐项代入 (19.2) 得 (25.1) 后的四分量目标。

由 $N_e\ge(3k_e+2)/10$，有 $k_e<10N_e/3$。又
$N_e\ge(3/10)2048e^{-2}\log(18/e)\ge1/e$，故

$$
 9k_e/e\le30N_e/e\le30N_e^2<8{,}000{,}000N_e^2.
 \tag{25.5}
$$

最后一项本为整数，故定义 19.1 的外层取整给出 (25.4) 的精确 $D$，并非渐近替换。$D-1>10N_e+1$，且 $m=D-1\ge D/2$。同一下界还给
$N_e\ge600e^{-2}\log(1/e)$；平方后乘 $8{,}000{,}000e^3$，即得 $C_{\rm curve}$。所述两个极限随之成立。$\square$

**引理 25.3（平滑振幅与逐输出零流）。** 在复平面上令 $a=1-|w|^2$，并定义

$$
\begin{aligned}
 q(w)&=\begin{cases}\exp(-1/a),&|w|<1,\\0,&|w|\ge1,\end{cases}
 &\alpha(w)&=\bar w/a\quad(|w|<1),\\
 u(\alpha)&=\left(e^{-|\alpha|^2/2}\frac{\alpha^k}{\sqrt{k!}}\right)_{k\ge0},
 &F(w)&=\begin{cases}\sqrt{q(w)}u(\alpha(w)),&|w|<1,\\0,&|w|\ge1.\end{cases}
\end{aligned}
\tag{25.6}
$$

这是紧支撑的平滑 $\ell^2$ 值函数，且

$$
 \|F(w)\|^2=q(w),\qquad
 \langle F(w),\partial_{\bar w}F(w)\rangle=0.
 \tag{25.7}
$$

以下绝对常数只依赖这个固定函数。实导数取算子范数，置

$$
\begin{aligned}
 z_0&=\int_{|w|<1}q(w)\,\frac{dA(w)}\pi>0,\\
 M_F&=\sup_w\bigl(\|F(w)\|+\|DF(w)\|+\|D^2F(w)\|\bigr)<\infty,\\
 A=B&=10{,}000(1+M_F)/\sqrt{z_0},\qquad R_0=4(A+B+2),\\
 C_{\rm fail}&=1+256A^2,\qquad
 C_{\rm return}=3R_0+257A^2+2,\\
 H&=512C_{\rm return}+1,\qquad
 C_{\rm sum}=256C_{\rm fail}+H,\\
 t_*&=256\max\{100,R_0\}.
\end{aligned}
\tag{25.8}
$$

证明。指数级数给 $\|u(\alpha)\|=1$。对 $u$ 的任一固定阶实导数，其 $\ell^2$ 范数至多按 $|\alpha|$ 多项式增长：逐项求导后，范数平方中的求和是 Poisson 权重下固定阶多项式的矩。复合 $\alpha(w)$ 后，每个固定阶导数至多按 $a^{-1}$ 多项式增长，而 $\sqrt q=e^{-1/(2a)}$ 比每个这样的多项式衰减更快。故 $F$ 的所有阶导数在边界延拓为零，特别地 $M_F$ 有限。

采用第一变量共轭线性的内积和 Wirtinger 导数，归一相干向量满足

$$
\begin{aligned}
 \langle u(\alpha),\partial_{\bar w}u(\alpha)\rangle
 &=\tfrac12\bigl(\bar\alpha\,\partial_{\bar w}\alpha
             -\alpha\,\partial_{\bar w}\bar\alpha\bigr)
 =\frac{w}{2a^2},\\
 \partial_{\bar w}\log\sqrt q&=-\frac{w}{2a^2}.
\end{aligned}
\tag{25.9}
$$

两项精确相消，得 (25.7)。在边界及支撑外仍由平滑延拓成立。这个等式在全纯坐标替换下乘以相应的共轭导数因子，故零流性质不变。后面将对每个实际输出分别求 Kraus 分量和，不能只在不同实际输出之间相消。$\square$

**引理 25.4（一次有限截断及正求积）。** 对任意满足 $t\ge t_*$ 的曲线参数，可选一个有理数 $s\in(e/16,e/8)$，令
$\lambda=ms^2$、$\eta=1/\lambda$，并选有限 $K_0$、有限旋转 $g_1,\ldots,g_J\in SU(2)$ 和正权 $w_l$，$\sum_lw_l=1$，得到有限个标量函数 $f_{lk}$（$1\le l\le J$、$0\le k\le K_0$）。以 $f(h)=(f_{lk}(h))$ 记堆叠向量，它们同时满足

$$
\begin{aligned}
 1-\eta&\le\|f(h)\|^2\le1,\\
 \|Df\|&\le A/s,\qquad \|D^2f\|\le B/s^2,\\
 \sum_{l=1}^J\left|\sum_{k=0}^{K_0}
 \overline{f_{lk}(h)}\,\partial_{\bar z}f_{lk}(h)\right|&\le\eta.
\end{aligned}
\tag{25.10}
$$

导数界适用于任意旋转球面坐标图的 $|z|\le1$，末式在以任意 $h$ 为中心的图成立。$c_l=g_l e_z$，每个 $f_{lk}$ 的支撑均在距 $c_l$ 角距离小于 $2s$ 的球冠中。$s$ 还可以同时满足命题 25.11 的非零系数条件。

证明。$d\mu=d\omega/(4\pi)$ 为归一球面面积，$dg$ 为归一 Haar 测度。在北极为 $z=0$ 的立体坐标中，$d\mu=dA(z)/(\pi(1+|z|^2)^2)$。令 $z_g(h)=z(g^{-1}h)$，

$$
\begin{aligned}
 Z_s&=\int_{S^2}q(z(h)/s)\,d\mu(h)
 =s^2\int_{|w|<1}\frac{q(w)}{(1+s^2|w|^2)^2}\frac{dA(w)}\pi,\\
 a_{gk}(h)&=Z_s^{-1/2}F_k(z_g(h)/s).
\end{aligned}
\tag{25.11}
$$

支撑外延拓为零。因为 $s<1/800$，
$z_0s^2/2\le Z_s\le z_0s^2$。旋转不变性给每个 $h$ 上
$\int\sum_k|a_{gk}(h)|^2dg=1$。其支撑距 $ge_z$ 不超过 $2\arctan s<2s$。由 (25.7) 及全纯坐标变换，对于每个固定 $g$，

$$
 \sum_{k\ge0}\overline{a_{gk}}\,\partial_{\bar z}a_{gk}=0.
 \tag{25.12}
$$

在任意旋转图 $|z|\le1$ 中，Möbius 坐标变换在该支撑上的一、二阶实导数分别可界为 $2,4$。支撑的 Haar 测度至多 $s^2$。链式法则因此将积分的一阶导数平方和界为 $8M_F^2/(z_0s^2)$，二阶导数平方和界为 $128M_F^2/(z_0s^4)$。这两个界严格小于 $A^2/s^2,B^2/s^4$，留有统一余量。

先选一个有限正交截断 $0\le k\le K_0$。$F$ 和 $DF$ 的像在 $\ell^2$ 中紧，故截断对这两个像一致收敛。截断损失的平方范数以及 (25.12) 截断后绝对流的 Haar 积分，均可一致小于 $\eta/100$；这里 $s$ 已固定，$Z_s>0$，坐标因子有界。正交截断不增加一、二阶导数范数。

然后对这一个截断选一次有限正 Haar Riemann 和。被积函数包括平方范数、所有图方向上的一、二阶导数平方，以及每个 $g$ 的截断绝对流。参数集可取为旋转群、$|z|\le1$ 及单位实切向量的紧积；零延拓使这些函数连续。因此可用同一个有限正求积同时一致逼近所有这些量，归一化和绝对流的误差均小于 $\eta/100$。导数平方的误差取在上述严格余量内。将所得振幅统一再除以 $\sqrt{1+\eta/100}$，即

$$
 f_{lk}(h)=\frac{\sqrt{w_l}}{\sqrt{Z_s}\sqrt{1+\eta/100}}
                F_k(z_{g_l}(h)/s).
 \tag{25.13}
$$

若需要，可先把求积误差进一步减小；上界成为精确的 $\|f\|^2\le1$，下界至少 $1-\eta$，绝对流至多 $\eta$，导数界仍在余量内，得到 (25.10)。支撑没有改变。这是对每个 $e$ 一次选定的有限数据，非无限维实际装置，也没有把 Haar 参数当成替代统计实验。命题 25.11 只从 $(e/16,e/8)$ 排除一个没有内点的零集，故可以先选满足该条件的有理 $s$，再完成上述有限选择。$\square$

**命题 25.5（同一有限 TP 仪器及其失败支）。** 用 (14.7) 的相干向量

$$
 e_z=(1+|z|^2)^{-m/2}
       (|0\rangle+z|1\rangle)^{\otimes m},\qquad
 T_m(a)=D\int_{S^2}a(u)\tau_u\,d\mu(u)
 \tag{25.14}
$$

定义有限矩阵 $A_{lk}=T_m(f_{lk})$、$S=\sum_{lk}A_{lk}^\dagger A_{lk}$ 和 $A_0=\sqrt{I-S}$。则 $0\le S\le I$，以下仪器精确保迹：

$$
 \Psi(X)=\sum_{l=1}^J\left(\sum_{k=0}^{K_0}A_{lk}XA_{lk}^\dagger\right)
                  \otimes|l\rangle\langle l|
             +A_0XA_0^\dagger\otimes|0\rangle\langle0|.
 \tag{25.15}
$$

其实际量子输出是原标记 $R$，实际原始获取记录是有限经典 $l$；$k$ 是形式 Kraus 指标。失败 $l=0$ 始终保留，且对每个输入态，其概率至多 $C_{\rm fail}/\lambda$。

证明。按归一对称张量基展开 (25.14)，角积分使非对角项为零，径向 beta 积分给每个对角元 $1/D$，故

$$
 D\int\tau_u\,d\mu(u)=I,\qquad
 |\langle e_u,e_h\rangle|=\cos^m(\theta(u,h)/2).
 \tag{25.16}
$$

因此 $T_m$ 是从标量函数代数到有限矩阵的 unital CP 映射。其 Schwarz 不等式给
$S\le T_m(\sum_{lk}|f_{lk}|^2)\le I$，于是 (25.15) 连同失败支精确 TP。可保留 $l$ 的确定性副本、固定程序及实际解码输出；这些是经典记录上的等距复制，不改变下述返回估计。

为估计失败，令相干变换 $V_c\psi(u)=\sqrt D\langle e_u,\psi\rangle$，$P=V_cV_c^\dagger$。这是到平方可积相干截面的等距变换及其正交投影；局部相位选择不影响以下核范数。以 $M_f$ 表示乘以有限向量 $f$，由 $T_m(a)=V_c^\dagger M_aV_c$ 得精确恒等式

$$
 I-S=T_m(1-\|f\|^2)
       +V_c^\dagger M_f^\dagger(I-P\otimes I)M_fV_c.
 \tag{25.17}
$$

第一项范数至多 $\eta$。第二项是一个正平方，其平方根范数不超过
$M_fP-(P\otimes I)M_f$ 的范数。这个算子的核为
$D(f(u)-f(v))\langle e_u,e_v\rangle$。由 (25.10)，$f$ 对角距离为 $A/s$-Lipschitz；沿球面路径可逐点用中心坐标，其中球面单位速度对应的坐标速度至多一。Schur 核估计及 (25.16) 给

$$
 \|M_fP-(P\otimes I)M_f\|
 \le\frac{A}{s}D\int\theta(u,v)\cos^m(\theta(u,v)/2)\,d\mu(v)
 \le\frac{16A}{s\sqrt m}.
 \tag{25.18}
$$

具体地 $r=\sin^2(\theta/2)$ 在归一面积下均匀分布于 $[0,1]$，$\theta\le\pi\sqrt r$、$(1-r)^{m/2}\le e^{-mr/2}$、$D\le2m$，故该积分至多
$2\pi m\int_0^\infty r^{1/2}e^{-mr/2}dr
=2\pi2^{3/2}\Gamma(3/2)/\sqrt m<16/\sqrt m$。
两种 Schur 积分上界相同，亦适用于向量值核。由 (25.17)，

$$
 \|I-S\|\le\eta+\frac{256A^2}{ms^2}
             =\frac{C_{\rm fail}}\lambda.
 \tag{25.19}
$$

失败概率为 $\operatorname{Tr}[(I-S)X]$，结论成立。这里直接声明的是放宽类的约化 CP 原语；没有断言一个等距实现可以省去其实际环境。如果另一个实现产生额外实际系统，其完整输出必须另行估计，不能沿用 (25.15) 的端口结论。$\square$

**定理 25.6（获取阶段的完整自身边缘返回）。** 对同一个有限仪器 (25.15)，令 $\omega_h=\Psi(\tau_h)$。则

$$
 \sup_hD_{\rm tr}\!\left(\omega_h,
                   \tau_h\otimes\operatorname{Tr}_R\omega_h\right)
 \le\frac{C_{\rm return}}\lambda.
 \tag{25.20}
$$

证明。固定任意 $h$，仅在证明中选择以 $h$ 为北极的旋转相干坐标，记 $e_h=e_0$，第一降低向量为 $e_1$。这不是实施一个依赖未知 $h$ 的门。有限向量的 Taylor 展开为

$$
 f(z)=f(0)+zf_z(0)+\bar zf_{\bar z}(0)+r(z),\qquad
 \|r(z)\|\le\frac{A+B+2}{s^2}|z|^2.
 \tag{25.21}
$$

在 $|z|\le1$ 用 (25.10) 的二阶实导数界；在 $|z|\ge1$ 用
$\|f(z)\|,\|f(0)\|\le1$、$\|Df(0)\|\le A/s$ 和 $s<1$，同样得到这个全局界。无穷远点为面积零集。

由二项式展开及角积分，以下矩精确成立：

$$
\begin{gathered}
 T_m(1)e_0=e_0,\qquad T_m(z)e_0=0,\qquad
 T_m(\bar z)e_0=\frac{e_1}{\sqrt m},\\
 D\int |z|^2|\langle e_z,e_0\rangle|\,d\mu(z)
 =\frac{4(m+1)}{m(m+2)}\le\frac4m.
\end{gathered}
\tag{25.22}
$$

例如第三式仅保留基指标一，径向积分为
$D\sqrt m\int_0^\infty u(1+u)^{-m-2}du=1/\sqrt m$；末式为
$D\int_0^\infty u(1+u)^{-m/2-2}du$。这些积分在这里的 $m>2$ 都绝对收敛。

将 (25.21) 代入同一 $T_m$，Minkowski 不等式和末矩给所有 $l,k$ 的堆叠估计

$$
\begin{aligned}
 A_{lk}e_h&=f_{lk}(h)e_h+
                \frac{\partial_{\bar z}f_{lk}(h)}{\sqrt m}e_1+r_{lk,h},\\
 \left(\sum_{lk}\|r_{lk,h}\|^2\right)^{1/2}&\le\frac{R_0}\lambda=:r\le1.
\end{aligned}
\tag{25.23}
$$

记实际成功向量为 $v_{lk}=A_{lk}e_h$，删去余项后的向量为 $w_{lk}$。$\sum\|v_{lk}\|^2\le1$，且堆叠向量之差范数至多 $r$，故各实际 $l$ 块之和与相应领先块之和的迹范数差至多
$(2+r)r\le3R_0/\lambda$。这来自
$\|vv^\dagger-ww^\dagger\|_1\le(\|v\|+\|w\|)\|v-w\|$
以及对 $l,k$ 的 Cauchy–Schwarz，不合并不同实际 $l$ 的相干项。

在第 $l$ 个领先块中置

$$
 q_l=\sum_k|f_{lk}|^2,\qquad
 a_l=\sum_k|\partial_{\bar z}f_{lk}|^2,\qquad
 b_l=\sum_k\overline{f_{lk}}\,\partial_{\bar z}f_{lk}.
 \tag{25.24}
$$

该块恰为
$q_l\tau_h+(a_l/m)\tau_1+(b_l/\sqrt m)|e_1\rangle\langle e_h|+\text{h.c.}$，
其中 $\tau_1=|e_1\rangle\langle e_1|$，h.c. 只补交叉项。其自身 $l$ 边缘权重为 $q_l+a_l/m$。与该权重乘 $\tau_h$ 的迹距离为
$\sqrt{(a_l/m)^2+|b_l|^2/m}\le a_l/m+|b_l|/\sqrt m$。
逐块求和并用 (25.10) 得

$$
 \sum_l\left(\frac{a_l}m+\frac{|b_l|}{\sqrt m}\right)
 \le\frac{A^2}\lambda+\frac\eta{\sqrt m}
 \le\frac{A^2+1}\lambda.
 \tag{25.25}
$$

从领先成功态换回实际成功态，一次付半迹范数差，换回其自身实际成功边缘再付同样的半迹范数差，合计至多 $3R_0/\lambda$。失败块与同迹乘积块的迹距离至多其概率，按 (25.19) 至多 $C_{\rm fail}/\lambda$。因此完整距离至多

$$
 \frac{3R_0+A^2+1+C_{\rm fail}}\lambda
 =\frac{C_{\rm return}}\lambda.
 \tag{25.26}
$$

这一步使用同一个通道的实际边缘；没有用参考泄漏或边缘不保真度替代完整返回。交叉项的小量来自每个实际 $l$ 内的零流及其有限近似，而非在彼此可区分的输出之间求消。$\square$

**定理 25.7（固定有限解码器的全方向尾界）。** 对 $l>0$，将中心目标 $(c_{l,y}/2,-c_{l,x}/4)$ 的两个分量各作有理舍入，误差至多 $e/8$；例如取间距 $e/16$ 的有理格点。$l=0$ 时输出 $(0,0)$。原始 $l$、解码输出、确定性副本和固定工作输出均保留。这个单一有限解码器满足

$$
 \beta_{\rm acq}\le\frac{C_{\rm fail}}\lambda
          +4\exp\!\left(-\frac{(m+2)e^2}4\right),
 \tag{25.27}
$$

其中风险对全部 $h\in S^2$ 取上确界。

证明。固定 $h$。若一个非零结果 $l$ 在 (25.2) 的事件中为坏结果，则其未舍入目标至少有一个坐标距真值大于 $7e/8$。第一坐标迫使 $|c_{l,y}-h_y|>7e/4$，第二坐标则给更强的 $|c_{l,x}-h_x|>7e/2$。故两种情形均有球面角距离 $\theta(c_l,h)\ge|c_l-h|>7e/4$。
由于支撑半径 $2s<e/4$，当 $\theta(u,h)<e$ 时，所有这些坏 $l$ 的 $f_{lk}(u)$ 都为零。实际非零坏结果的概率 $p_{\rm bad}$ 由 (25.15) 给出；对其 Kraus 向量堆叠使用 Minkowski 不等式及 $\|f(u)\|\le1$，得

$$
 \sqrt{p_{\rm bad}}\le
 D\int_{\theta(u,h)\ge e}|\langle e_u,e_h\rangle|\,d\mu(u)
 =\frac{2(m+1)}{m+2}\cos^{m+2}(e/2)
 \le2e^{-(m+2)e^2/8}.
 \tag{25.28}
$$

等号用 (25.16) 径向积分；最后用 $\log\cos x\le-x^2/2$。平方后加上实际失败支的 (25.19)，得 (25.27)。这是真正固定的有限解码器在全部方向上的风险，不是平均风险、局部承诺或按 $h$ 另选最优检验。$\square$

**定理 25.8（同一规定终端、全部实际输出和绝对常数）。** 在 (25.15) 后原样接定义 17.1 的固定后缀，旧获取输出不参与它。得到 (25.2) 的同一个完成过程及解码器，并有

$$
\begin{aligned}
 \delta_e&\le\frac{2C_{\rm return}}\lambda+\frac{80}D\le\frac Ht,\\
 \beta_e&\le\frac{256C_{\rm fail}}t+4e^{-t/4},\\
 \beta_e+\delta_e&\le\frac{C_{\rm sum}}t+4e^{-t/4},
 \qquad t=me^2.
\end{aligned}
\tag{25.29}
$$

证明。对应定理 17.3 的参数精确为 $D=m_e+1$、$t_{\rm term}=d\tau_0=1/64$；其场令牌方向为 $v=n_*(+d e_x)$，并且该定理对任意 $h,v$ 一致。后缀先准备固定 singlet $BA$，用两个原生 $V$ 槽及定义 17.1 的退相干、条件交换、$\widehat\Phi$ 和非参考 $\mathcal E$ 节点；两枚场令牌均在 $+d e_x$ 独立重置，第二枚是此前未经改动的规定终端令牌 $S_t$。规定
$U_{\rm term}=\exp[-idJ\cdot\sigma/m]$ 恰执行一次，不另供逆操作。

最终实际 $K$ 保留旧 $l$、其解码输出和副本、全部旧工作输出，以及 $B,A,F,S_t$、两组新 $H,E$、实际原始及复制记录、程序、路由和所有声明工作输出。后缀约化节点采用定义 17.1 的实际端口；不省去任何实际口，也不把形式 Kraus 指标添成虚构端口。获取中的额外直接 $R$ 节点是唯一访问放宽。后缀实际增加两次 $V$ 和两次场重置，在原 $L,Q$ 内；额外直接 $R$ 节点没有虚构的原生调用数。

记 $\rho_h=\operatorname{Tr}_R\omega_h$，用相同 CPTP 后缀分别作用于 $\omega_h$ 和 $\tau_h\otimes\rho_h$。两完整输出的距离由 (25.20) 至多 $C_{\rm return}/\lambda$。后一个输出是定理 17.3 的完成态张量 $\rho_h$，相对于它自己的实际边缘的返回小于 $80/D$。再把该边缘换成实际完成输出的边缘，由偏迹收缩性再付 $C_{\rm return}/\lambda$。这证明第一行首式，比较端确为最终自己的全部实际边缘。后缀 TP 且不改旧解码记录，故 (25.27) 原样成立。

$s>e/16$ 给 $\lambda>t/256$；又 $80me^2/D<1$。用 (25.8) 得第一行末式及余下两行。所有估计来自同一有限仪器、同一实际解码器及同一完整后缀。$\square$

**定理 25.9（任意 CPTP 充分捷径的有限反例）。** 对任意 $c_0,c_1>0$ 以及任意给定的充分小正有理精度窗口，存在其中的 $e$ 及上述有限完成过程，使 (25.3) 不成立。其 $t\delta_e\le H$ 而 $\beta_e+\delta_e\to0$。这是直接参考 CP 访问放宽类中的全方向两坐标估计器反例。

证明。若有必要，将 $c_0$ 换成更小的 $\min\{c_0,1/2\}$；推翻较小右端也推翻原右端。令 $b=c_0e^{-c_1H}>0$。由命题 25.2，在给定窗口内选正有理 $e$ 使

$$
 t>\max\{t_*,2C_{\rm sum}/b,4\log(8/b)\}.
 \tag{25.30}
$$

由 (25.29)，$\beta_e+\delta_e<b$，而
$c_0\exp(-c_1t\delta_e)\ge c_0e^{-c_1H}=b$，矛盾。每个这样的 $e$ 所用的维数、输出数、截断和求积均有限，常数不依赖它们。还由 $et=me^3\to\infty$ 及 $t/\log(1/e)\to\infty$，(25.29) 给所有充分小 $e$ 上 $\beta_e\le e$。这只是在固定允许场 $n_*$ 上的成功，不是全部原始场上的均匀成功。$\square$

**命题 25.10（原生前缀的参考系数次数）。** 令 $\mathcal P_T$ 为 $I$ 和 $J_x,J_y,J_z$ 中次数至多 $T$ 的全部非交换单项式的复线性张成。任意有限原生前缀若最多使用 $T$ 次前向 $V$，则其每个代数参考系数均属于 $\mathcal P_T$。这包括原始允许的固定混合辅助、量子和经典记忆、纠缠、反馈、探针回用及分支停止；各实际输出分块的 Choi 支撑均在 $\mathcal P_T$ 的向量化子空间内。一个单独计入的规定终端至多增加一次数。

证明。由 (13.5)–(13.6)，每个原生投影对参考算子为仿射：$\Pi_+=(j+1+J\cdot\sigma)/D$、$\Pi_-=(j-J\cdot\sigma)/D$。其余操作在 $R$ 上为恒等。展开有限电路和每个声明的 CP 节点的 Kraus 求和，每个参考系数是至多 $T$ 个这样的仿射系数之积的线性组合。固定混合辅助可作谱分解；所有准备、旧记忆、结果反馈、探针回用及 Kraus 收缩只改变其余腿上的系数，不增加参考次数。分支补齐及求和也保留同一张成空间。对任一实际输出选基取矩阵系数后仍如此。Choi 矩阵是这些 Kraus 向量的正秩一和，故其支撑在上述子空间内。

最后 $J\cdot\sigma$ 只有 $j,-j-1$ 两个本征值；规定终端是这两个投影的固定标量组合，亦为参考一次式，因而至多增加一次数。这里是因果复合的代数约束，不从一个任意有限 CPTP 通道的存在反推原生实现。$\square$

**命题 25.11（展示出的获取块的精确 tensor-rank/Choi 障碍）。** 引理 25.4 可选择为：每个非零实际结果 $l$ 的 $A_{l0}$ 均有非零 rank-$m$ 不可约张量分量。因此获取仪器 (25.15) 没有至多 $L$ 次前向 $V$ 的精确原生前缀实现。结论针对该获取块，不是对整个已完成通道所有可能分解的排除，也不含任何近似误差下界。

证明。$F_0(w)=\sqrt{q(w)}e^{-|\alpha(w)|^2/2}$ 在单位圆盘内为正径向函数。设 $P_m^{\rm Leg}$ 为 Legendre 多项式，定义

$$
 I_m(s)=\int_{|w|<1}F_0(w)
 P_m^{\rm Leg}\!\left(\frac{1-s^2|w|^2}{1+s^2|w|^2}\right)
 (1+s^2|w|^2)^{-2}\,dA(w).
 \tag{25.31}
$$

固定 $m$ 后，它在正实轴附近实解析，并解析延拓到 $s=0$，那里
$I_m(0)=\int F_0dA>0$。积分核在每个局部复邻域上有一致无奇点控制，故可逐项积分解析级数。解析函数的零点不能包含区间；其非零集在 $(e/16,e/8)$ 内含开区间，所以可以选有理 $s$ 使 $I_m(s)\ne0$。有限截断保留 $k=0$，正求积权重及共同正归一化也不使该系数消失。

以 $c_l$ 为极轴，(25.31) 乘以非零归一化因子正是 $f_{l0}$ 的 degree-$m$ 球谐系数。Toeplitz 映射在这些阶数上不会杀掉该系数。具体地，$B_m a(h)=\langle e_h,T_m(a)e_h\rangle$ 的核为
$D((1+x)/2)^m$，在 degree-$r$ 球谐上的乘子为

$$
 b_r=\frac{m+1}{2}\int_{-1}^1
        \left(\frac{1+x}{2}\right)^m P_r^{\rm Leg}(x)\,dx
 =\frac{(m+1)(m!)^2}{(m-r)!(m+r+1)!}>0,
 \quad 0\le r\le m.
 \tag{25.32}
$$

用 Rodrigues 公式 $P_r^{\rm Leg}(x)=(2^rr!)^{-1}(d/dx)^r(x^2-1)^r$，分部积分 $r$ 次，边界项为零；余项是
$(m+1)m!/[2^{m+r+1}r!(m-r)!]$
乘 $\int_{-1}^1(1+x)^m(1-x)^r dx$，beta 积分即给 (25.32)。

旋转作用下 $\operatorname{End}(\operatorname{Sym}^m\mathbb C^2)$ 分解为各一份 rank $0,1,\ldots,m$ 的不可约张量；这就是 spin-$j$ 与其对偶的 Clebsch–Gordan 分解。相干符号映射旋转等变，而 $B_m$ 的 rank-$m$ 分量由 (25.31)–(25.32) 非零，故 $A_{l0}$ 的 rank-$m$ 算子分量非零。每个 $J_a$ 是 rank-one 张量，$T$ 个此类张量的乘积最多含 rank $T$，所以 $\mathcal P_T$ 只含这些低阶分量。由 $m>L$，$A_{l0}\notin\mathcal P_L$。

固定一个非零实际 $l$，其 CP 块的 Choi 矩阵为
$\sum_k|A_{lk}\rangle\!\rangle\langle\!\langle A_{lk}|$；有限正秩一和的支撑恰为这些 Kraus 向量的张成，包含 $|A_{l0}\rangle\!\rangle$。命题 25.10 则把任何 $L$ 次调用原生前缀的相应 Choi 支撑限制在 $\mathcal P_L$ 内。换 Kraus 表示不能改变同一 Choi 支撑，矛盾。

若把规定终端另行计入，次数上界至多变为 $L+1$，且本曲线仍有 $m>L+1$；但这没有证明任意另一种完整通道分解必须保留上述获取块。非零高阶尾也没有任何已给出的定量下界，可能很小。因此结论既不排除近似合成，也不排除另一种已完成原生构造，不是全部原生控制器的分类。$\square$

**推论 25.12（保留原成功域的条件消费者）。** 假设 (25.3) 对全部原始原生控制器及其实际解码器在某个窗口 $0<e\le e_{\rm hyp}$ 成立。不失一般性取 $0<c_0<1$。则对每个原始成功控制器及原来的全部实际输出，

$$
 \overline\delta\ge
 \min\left\{e,\frac{\log(c_0/(2e))}{c_1m_e e^2}\right\}.
 \tag{25.33}
$$

置

$$
 e_0=\min\{e_{\rm hyp},1/100,c_0^2/4,2C_{\rm curve}c_1\}.
 \tag{25.34}
$$

对所有正有理 $0<e\le e_0$，原始下确界满足

$$
 R(e)\ge\frac{\log(1/e)}{2c_1D_e e^2},\qquad
 \liminf_{\substack{e\downarrow0\\e\in\mathbb Q_{>0}}}
 \frac{D_e e^2R(e)}{\log(1/e)}\ge\frac1{c_1}.
 \tag{25.35}
$$

证明。原始成功是对全部场和全部方向的 (19.2) 四坐标成功，故在允许的 $n_*$ 上，同一实际解码器的前两坐标给 (25.2) 的 $\beta_e\le e$；这里没有换成一个二元最优检验。其 $\overline\delta=\sup_{n,h}\Delta_{n,h}$ 至少为 $\delta_e$。若 $\delta_e<e$，由假设
$c_0e^{-c_1m_e e^2\delta_e}\le\beta_e+\delta_e<2e$，解出
$\delta_e\ge\log(c_0/(2e))/(c_1m_e e^2)$。若 $\delta_e\ge e$ 则直接用这个下界，得到 (25.33)。

当 $e\le c_0^2/4$ 时，$\log(c_0/(2e))\ge\tfrac12\log(1/e)$。在第二种情形，(25.4)、$\log(1/e)\ge1$ 及 $e\le2C_{\rm curve}c_1$ 给
$D_e e^3\ge\log(1/e)/(2c_1)$，即
$e\ge\log(1/e)/(2c_1D_e e^2)$。第一种情形用 $m_e<D_e$ 得同一界。这个下界对每个原始成功控制器、解码器和辅助维数一致；由定义 19.1 的原成功类非空，对原来的下确界取值即得 (25.35) 首式。

更精确地，对 (25.33) 先取下确界再乘 $D_e e^2/\log(1/e)$，第一项由 (25.4) 趋于无穷，第二项为
$(D_e/m_e)\log(c_0/(2e))/(c_1\log(1/e))\to1/c_1$，给出所述下极限。全部原始混合辅助、记忆、反馈、探针回用、$L_e,Q_e$、规定终端和实际 $K$ 的量词没有收缩。这只是以原生关系为前提的条件推论，不由放宽类反例推得该前提。$\square$

**命题 25.13（成熟集中工具的范围与剩余转移义务）。** 定理 25.9 与 Frank 的 full-dimension 相干态集中定理相容，不能将后者的维数 $D$ 替换为 $m\delta$ 来获得 (25.3)。若未来在原生菜单内实现以下完整输出近似，则可反驳原生的 (25.3)：对每个 $e$ 有至多 $L_e-2$ 次前向 $V$、至多 $Q_e-2$ 次重置的有限前缀，并有一个固定的、与 $h,n$ 无关的非参考通道 $\mathcal T_e$，保留上述实际解码器并将其输出扩充至该前缀自己的全部实际端口，使在固定 $n_*$ 上

$$
 \sup_hD_{\rm tr}\!\left(\omega_h^{\rm native},
       (\operatorname{id}_R\otimes\mathcal T_e)\Psi(\tau_h)\right)
 \le E_e\le\frac1{m_e e^2}.
 \tag{25.36}
$$

这里全部 $H,E$、场令牌、探针、旧记忆、原始与复制记录、读出、程序及截止输出均在同一个比较空间内，不许删去实际记录。此近似尚未给出，其不可能性亦未证明。

证明。Frank, [arXiv:2210.14798v1，§5 定理 21](https://arxiv.org/html/2210.14798v1)，对不可约 spin-$J$ 表示中的单位向量给出，在 $d\mu=d\omega/(4\pi)$ 下

$$
 (2J+1)\int_E|\langle\psi_h,\psi\rangle|^2d\mu(h)
 \le1-(1-\mu(E))^{2J+1}.
 \tag{25.37}
$$

本节精确对应 $J=j=m/2$、$\psi_h=e_h$、$2J+1=D$。对正算子 $B$ 作谱分解，仅可线性推出

$$
 D\int_E\langle e_h|B|e_h\rangle d\mu(h)
 \le\operatorname{Tr}(B)\,[1-(1-\mu(E))^D].
 \tag{25.38}
$$

它没有给未经所需归一化的 Kraus-symbol 族一个 $m\delta$ 维数的集中界。本节反例同时保留正性、相干态解析结构及同一完成过程的完整输出，故这些最终 CPTP 性质本身不足以供应所需替换。(19.7)–(19.9) 的泄漏和能量界仍按其原域成立，不能充当额外的指数集中定理。§23 的直接访问二元例子也不替代这里的固定有限全方向估计器。

若有 (25.36)，非参考通道收缩完整返回距离，并保留解码事件。事件概率收缩和两次自身边缘比较给

$$
 \beta_{\rm native,acq}\le\beta_{\rm acq}+E_e,\qquad
 \delta_{\rm native,acq}\le\delta_{\rm acq}+2E_e.
 \tag{25.39}
$$

再接同一个定义 17.1 后缀，逐一保留全部旧输出和新端口，可用定理 25.8 的相同三角比较得

$$
 \delta_{\rm native,final}
 \le2\delta_{\rm acq}+4E_e+80/D_e
 =O\!\left(\frac1{m_e e^2}\right).
 \tag{25.40}
$$

连同 (25.27)，这会在原生类内给 $\beta+\delta\to0$ 而 $m_e e^2\delta$ 有界，从而反驳 (25.3)。它仍只在 $n_*$ 上服务该必要关系；若要给原 (19.12) 的负分支，还须构造在全部原始 $n,h$ 上满足 (19.2) 的成功消费者，并支付全部精度、资源、终端和实际输出成本。

本节的中间成熟工具为有限 CP 仪器及 Choi–Kraus 对应、相干态分解与 Toeplitz 压缩、CP Schwarz、Schur 核估计、Taylor 余项、迹距离收缩及自旋张量分解。相干输入和端口语义复用 §§13–14；规定完成逐参数复用定义 17.1、定理 17.3；原成功类及非空性复用定义 19.1。新增推导是这些工具在上述同一有限仪器、实际解码器和完整返回过程上的组合，不主张历史原创或形式核验。

因此下一项有区别作用的数学条件是 (25.36) 的原生访问、定量精度、槽数与全部共同实际输出对应，或者利用真实前向 $V$ 因果复合证明原生必要关系。有限矩阵分解、抽象仪器、静态 Hilbert/PB/CAR 或算术结果本身不供应该对应。展示出的获取块的精确障碍、近似合成、其它完整原生分解及原生关系各是不同命题；后面三者和原 (19.12) 都仍未解决。$\square$

## 追加锚（本行以下为增补区）

## 26. 保留相干工作系统的球冠极分解目标与完整返回缺陷

**定义 26.1（原元组、内部尺度与绝对窗口）。** 精度、场、初始方向、允许控制器、成功事件、实际输出及两项资源上限均取定义 19.1；特别地，公共元组始终是 (19.1) 在 $e$ 处的元组，而非较小内部精度处的元组。置

$$
 a=e/64,\qquad s=a/12=e/768,\qquad m=m_e=D_e-1,\qquad
 t=me^2,\qquad \lambda=ms^2=t/768^2.
 \tag{26.1}
$$

沿用 (25.6) 的 $F,q,\alpha,u$ 以及 (25.8) 的固定函数常数 $z_0,M_F,A,B,R_0,C_{\rm fail},C_{\rm return},t_*$；这些常数不依赖 $e,m$、辅助维数或求积点数。定义

$$
\begin{aligned}
 C_t&=1{,}440{,}000{,}000{,}000,\qquad B_*=3R_0+2C_{\rm fail},\\
 \Lambda&=\max\{t_*,2C_{\rm fail},A^2,64B_*^2,64C_{\rm return}^2\},\\
 K_{\rm risk}&=3\cdot768^2C_{\rm fail}+1,\\
 e_*&=\min\left\{\frac1{100},
 \sqrt{\frac{C_t}{768^2\Lambda}},
 \frac{C_t}{6K_{\rm risk}},\frac{C_t}{393216}\right\},\\
 r_0&=\max\{7,\lceil\log_2(1/e_*)\rceil\}.
\end{aligned}
\tag{26.2}
$$

以下均量化于每个正有理 $0<e\le e_*$，故包含每个 $e_r=2^{-r}$、$r\ge r_0$。命题 25.2 的精确原曲线关系直接给

$$
 t\ge C_t e^{-2}\log^2(1/e)\ge C_t/e^2,\qquad
 \lambda\ge\Lambda,\qquad t\ge6K_{\rm risk}/e.
 \tag{26.3}
$$

又 $\log(24/e)\le24/e$，结合 $e\le C_t/393216$ 得
$t\ge16384\log(24/e)$；同时 $s<1/640$、$ma^2=144\lambda\ge t_*$。这里仅把 (25.4) 用于尺度比较，不改变原 $D_e,L_e,Q_e$。

**定义 26.2（有限球冠堆叠、极分解与实际工作口）。** 在内部球冠精度 $a$、同一个原始 $m=m_e$ 上复用引理 25.4 的有限构造。此时 $a/16<s=a/12<a/8$，且不要求命题 25.11 的可选非零高阶系数条件。取同一有限截断 $0\le k\le K_0$ 和一次正 Haar 求积 $(g_l,w_l)_{l=1}^J$，$\sum_lw_l=1$，令

$$
\begin{aligned}
 Z_s&=s^2\int_{|w|<1}\frac{q(w)}{(1+s^2|w|^2)^2}\frac{dA(w)}\pi,\\
 f_{lk}(h)&=\frac{\sqrt{w_l}F_k(z_{g_l}(h)/s)}
 {\sqrt{Z_s}\sqrt{1+1/(100\lambda)}},\qquad c_l=g_l e_z,\\
 A_{lk}&=T_m(f_{lk}),\qquad
 T_m(b)=D_e\int_{S^2}b(u)\tau_u\,d\mu(u),\\
 A_{\rm stack}\psi&=\sum_{l,k}A_{lk}\psi\otimes|l\rangle_L\otimes|k\rangle_{K_{\rm work}},\\
 S_{\rm op}&=A_{\rm stack}^\dagger A_{\rm stack},\qquad
 W=A_{\rm stack}S_{\rm op}^{-1/2}.
\end{aligned}
\tag{26.4}
$$

有限选择还须满足引理 26.4 的范数乘积条件；其与既有条件的同时可选性由该引理证明。既有供应关系 (25.10)、(25.19)、(25.23)、(25.26) 在这里分别为

$$
\begin{gathered}
 1-1/\lambda\le\sum_{lk}|f_{lk}(h)|^2\le1,\qquad
 \|Df\|\le A/s,\quad\|D^2f\|\le B/s^2,\\
 \sum_l\left|\sum_k\overline{f_{lk}(h)}\partial_{\bar z}f_{lk}(h)\right|
 \le1/\lambda,\qquad \operatorname{supp}f_{lk}\subset\{\theta(\,\cdot\,,c_l)<2s\},\\
 0\le I-S_{\rm op}\le(C_{\rm fail}/\lambda)I,\\
 A_{lk}e_h=f_{lk}(h)e_0+
       \frac{\partial_{\bar z}f_{lk}(h)}{\sqrt m}e_1+r_{lk,h},\qquad
 \left(\sum_{lk}\|r_{lk,h}\|^2\right)^{1/2}\le R_0/\lambda.
\end{gathered}
\tag{26.5}
$$

最后一式只在证明中以 $h$ 为图中心，$e_0=e_h$、$e_1$ 为第一降低向量；它不是未知方向依赖的控制。每个球冠的导数界仍对既有旋转图一致。带实际 $l=0$ 失败支的约化仪器

$$
 \Psi_{\rm loc}(X)=\sum_{lk}A_{lk}XA_{lk}^\dagger\otimes|l\rangle\langle l|
 +\sqrt{I-S_{\rm op}}X\sqrt{I-S_{\rm op}}\otimes|0\rangle\langle0|
 \tag{26.6}
$$

仍有完整自身边缘返回至多 $C_{\rm return}/\lambda$，失败概率至多 $C_{\rm fail}/\lambda$。式 (26.5)–(26.6) 的估计是引理 25.4、命题 25.5 及定理 25.6 在内部尺度 $a$、原始 $m$ 上的对应。

由 (26.3)、(26.5)，$S_{\rm op}$ 可逆，$W$ 是等距。所定义的另一目标先在数学上施行 $W$，再对 $L$ 作 Lüders 读出，保留测后 $L$、原始结果及所有选定副本，并附加旧两坐标解码器和三坐标方向解码器。精确写作

$$
\begin{aligned}
 V_l\psi&=\sum_k A_{lk}S_{\rm op}^{-1/2}\psi\otimes|k\rangle_{K_{\rm work}},\\
 \Phi_{\rm keep}(X)&=\sum_lV_lXV_l^\dagger\otimes|J_l\rangle\langle J_l|,
 \qquad\sum_lV_l^\dagger V_l=I.
\end{aligned}
\tag{26.7}
$$

$|J_l\rangle$ 是互相正交的有限码，包含测后 $L$、原始 $l$、实际副本、旧解码器、引理 26.8 的有理 $\widehat h(l)$ 和固定程序及工作因子。可另声明概率为零的 $l=0$；所有未用或无效经典码的估计固定为零。无分支后选择。若一个实际实现出现失败、停止或截止，该分支仍在无条件态及其误差预算内。

这里 $K_{\rm work}=\operatorname{span}\{|k\rangle:0\le k\le K_0\}$ 是特意生成并保留的相干实际输出，未被测量，也没有原始经典 $k$ 记录或 $k$ 副本。它不把 (26.6) 的代数 Kraus 指标冒充实际口。(26.7) 的实际 CP 读出口恰如所列，没有另行生成的环境；另一实现的额外实际环境必须另行保留。每个公共 $e$ 所用振幅、矩阵、字母表和解码器均有限，选择不依赖实际 $n,h$。这是有限目标的定义，不是原生 $R$ 门、原生程序或其调用数证书。

**引理 26.3（消流导数的正交范数）。** 对 $b=1-|w|^2>0$，用 $\mathfrak a^\dagger$ 表示相干序列上的代数产生算子，则

$$
 \partial_{\bar w}F(w)=\sqrt{q(w)}b^{-2}
       (\mathfrak a^\dagger-\overline{\alpha(w)})u(\alpha(w)),\qquad
 \|F(w)\|\,\|\partial_{\bar w}F(w)\|=q(w)/b^2.
 \tag{26.8}
$$

证明。相干序列的指数级数逐项求和给
$\mathfrak a u=\alpha u$、$\langle u,\mathfrak a^\dagger u\rangle=\bar\alpha$，以及
$\|(\mathfrak a^\dagger-\bar\alpha)u\|=1$；最后一式也由同一序列上的 $[\mathfrak a,\mathfrak a^\dagger]=I$ 得出。所有固定阶矩均有限，故这些运算在相干序列上合法。

直接求导给 $\partial_{\bar w}\alpha=1/b^2$、
$\partial_{\bar w}\log\sqrt q=-w/(2b^2)$。$\partial_{\bar w}u$ 平行于 $u$ 的分量为 $wu/(2b^2)$，恰与后一项相消；剩余正交分量即 (26.8)。所以 $\|F\|=\sqrt q$、$\|\partial_{\bar w}F\|=\sqrt q/b^2$。边界处由引理 25.3 的平坦零延拓成立。这在既有零标量流之外给出其未控制的正交范数；无限序列只用于推导，实际输出仍是有限截断。$\square$

**引理 26.4（所有有限条件的一次同时选择）。** 定义 26.2 的有限选择可同时满足：对每个 $h$ 及每个以 $h$ 为中心的旋转图，记 $f_l=(f_{lk})_k$、$g_l=(\partial_{\bar z}f_{lk})_k$，则

$$
 \sum_l\|f_l(h)\|\,\|g_l(h)\|\ge\frac1{2s}.
 \tag{26.9}
$$

证明。先取未截断的 Haar 族 $a_g=Z_s^{-1/2}F(z_g(h)/s)$。在中心图中，$SU(2)$ Möbius 变换满足
$|z_g'(0)|=1+|z_g(h)|^2$；Haar 测度将 $z_g(h)$ 推前为
$dA(z)/(\pi(1+|z|^2)^2)$。引理 26.3 因而给

$$
 \int\|a_g(h)\|\,\|\partial_{\bar z}a_g(h)\|\,dg
 =\frac{s}{Z_s}\int_{|w|<1}
 \frac{q(w)}{(1-|w|^2)^2(1+s^2|w|^2)}\frac{dA(w)}\pi
 \ge\frac1s.
 \tag{26.10}
$$

末步逐点使用
$[(1-|w|^2)^2(1+s^2|w|^2)]^{-1}\ge(1+s^2|w|^2)^{-2}$，再代入 $Z_s$。

对已固定的公共 $s$，按引理 25.4 对 $F$ 和一阶导数作一致正交截断。零延拓及紧性使范数乘积被积函数在旋转和中心图标架的紧参数集上一致收敛。可选一个 $K_0$，使其 Haar 积分的损失对全部 $h$、标架至多 $1/(8s)$，并使 (26.5) 所需的范数、流误差同时在各自容差内。

再为这同一个截断选一次正有限 Haar 求积，使乘积积分再损失至多 $1/(8s)$，同时满足全部归一化、一阶、二阶导数及绝对流容差。所用连续函数族的参数集是旋转、图及单位切向量的紧积；有限个容差可以同时满足。未共同归一化时乘积和至少 $3/(4s)$。共同归一化将其除以 $1+1/(100\lambda)\le101/100$，故至少 $75/(101s)>1/(2s)$。既有导数界有严格余量，归一化和流容差也可同时进一步缩小，故 (26.5) 与 (26.9) 属于同一个有限选择，而非分别存在的最优值。$\square$

**引理 26.5（该目标的极归一化扰动）。** 令 $\phi_h=\Phi_{\rm keep}(\tau_h)$，并在中心图中置

$$
 v_l=e_0\otimes f_l+e_1\otimes g_l/\sqrt m,\qquad
 \Xi_h=\sum_l|v_l\rangle\langle v_l|\otimes|J_l\rangle\langle J_l|.
 \tag{26.11}
$$

则 $\|W-A_{\rm stack}\|\le C_{\rm fail}/\lambda$，且

$$
 \|\phi_h-\Xi_h\|_1\le B_*/\lambda,\qquad
 \Xi_h\ge0,\qquad\operatorname{Tr}\Xi_h\le1+A^2/\lambda\le2.
 \tag{26.12}
$$

证明。写 $d_0=C_{\rm fail}/\lambda\le1/2$。由 $A_{\rm stack}=W\sqrt{S_{\rm op}}$，
$\|W-A_{\rm stack}\|=\|I-\sqrt{S_{\rm op}}\|\le d_0$。对单位输入 $e_h$，极分解秩一输出与未归一化堆叠秩一输出的迹范数差至多 $2d_0$；这里两向量的范数分别为一及至多一。$L$ 的 Lüders 读出及确定性保留解码收缩此 Hermitian 差。

(26.5) 将堆叠向量与其领先向量之差界为 $r=R_0/\lambda\le1$。前者范数至多一，故秩一差的迹范数至多 $(2+r)r\le3R_0/\lambda$；同一次读出后仍如此。两项相加得到 $B_*/\lambda$。最后由 $e_0\perp e_1$，
$\operatorname{Tr}\Xi_h=\sum_l(\|f_l\|^2+\|g_l\|^2/m)\le1+A^2/\lambda$。$\Xi_h$ 不必归一化。这里用的是有限极分解和秩一迹范数不等式，结论针对同一目标的 (26.11)。$\square$

**引理 26.6（完整工作分辨交叉块）。** 在 (26.7) 的全部实际输出空间上令 $P_h=\tau_h\otimes I$，则

$$
\begin{aligned}
 \|P_h\phi_h(I-P_h)\|_1
 &\ge\frac1{2\sqrt\lambda}-\frac{B_*}{\lambda}
 \ge\frac1{4\sqrt\lambda},\\
 d_{\rm keep}(h)&:=D_{\rm tr}(\phi_h,
                   \tau_h\otimes\operatorname{Tr}_R\phi_h)
 \ge\frac1{4\sqrt\lambda}=\frac{192}{\sqrt t}.
\end{aligned}
\tag{26.13}
$$

证明。$\Xi_h$ 的第 $l$ 个交叉块是
$|e_0\rangle\langle e_1|\otimes|f_l\rangle\langle g_l|/\sqrt m$，附有其自己的正交实际码 $|J_l\rangle$。秩一迹范数为 $\|f_l\|\|g_l\|/\sqrt m$，不同 $l$ 块的迹范数相加。因此 (26.9) 给

$$
 \|P_h\Xi_h(I-P_h)\|_1
 =\frac1{\sqrt m}\sum_l\|f_l\|\|g_l\|
 \ge\frac1{2s\sqrt m}=\frac1{2\sqrt\lambda}.
 \tag{26.14}
$$

左右压缩收缩迹范数，(26.12) 最多损失 $B_*/\lambda$。由 $\lambda\ge64B_*^2$，这个损失至多 $1/(8\sqrt\lambda)$，强于 (26.13) 所需。

对任意态 $\rho$，乘积 $\tau_h\otimes\rho_K$ 的此交叉块为零。取 $P_h\rho(I-P_h)$ 的极分解部分等距及其伴随构成自伴非对角检验，算子范数为一，在 $\rho-\tau_h\otimes\rho_K$ 上的期望为 $2\|P_h\rho(I-P_h)\|_1$。迹范数对偶给
$D_{\rm tr}(\rho,\tau_h\otimes\rho_K)\ge\|P_h\rho(I-P_h)\|_1$，并可取 $\rho_K=\operatorname{Tr}_R\rho$。故比较的是同一态自己的全部实际边缘。此处没有删去实际工作口，也没有在不同 $l$ 间抵消。$\square$

**引理 26.7（与任意扩充约化球冠仪器的定量分离）。** 对任意固定且不依赖 $h$ 的非参考通道 $\mathcal T_e$，若其将 (26.6) 的输出扩充到 (26.7) 的输出空间，则对每个 $h$，

$$
 D_{\rm tr}\!\left(\phi_h,
    (\operatorname{id}_R\otimes\mathcal T_e)\Psi_{\rm loc}(\tau_h)\right)
 \ge\frac1{16\sqrt\lambda}.
 \tag{26.15}
$$

证明。非参考通道收缩完整自身边缘返回，故右侧比较态的返回至多 $C_{\rm return}/\lambda$。自身边缘返回泛函对迹距离是 $2$-Lipschitz：插入另一联合态及其自身边缘，分别用联合距离和边缘收缩性即可。若两态距离为 $E$，则

$$
 2E\ge d_{\rm keep}(h)-C_{\rm return}/\lambda
 \ge\frac1{4\sqrt\lambda}-\frac1{8\sqrt\lambda}
 =\frac1{8\sqrt\lambda},
 \tag{26.16}
$$

其中用 $\lambda\ge64C_{\rm return}^2$。要求 $\mathcal T_e$ 还保持原始标签及解码器只缩小量词域。在保留已有系统的前提下，给 $\phi_h$ 附加固定输出也不能削弱此界，因为可偏迹回已有空间。

这是完整输出尺度的近似分离；沿充分小 $e$，它不容许 $E\le1/t$，也不容许 $E=O(\sqrt{\log(1/e)}/t)$。它不只是非零 tensor-rank 或精确合成障碍，更不推得约化仪器 (26.6) 自身的原生近似下界。$\square$

**引理 26.8（同一有限目标的全方向解码）。** 对每个 $l>0$，将 $c_l$ 的三个坐标各舍入到误差至多 $a=e/64$ 的有理数，保留 $\widehat h(l)$、旧解码器及原始 $l$。这个固定有限解码器满足

$$
 b_{\rm keep}:=\sup_h\Pr_h[\|\widehat h-h\|_\infty>e/16]
 \le\frac{3C_{\rm fail}}\lambda
       +4\exp[-(m+2)e^2/16384].
 \tag{26.17}
$$

证明。先用 (26.6) 的未归一化成功块及其实际 $l=0$ 失败支。若一个非零标签坏，则某个中心坐标距 $h$ 大于 $e/16-a=3a$，从而其角距离大于 $3a$。其振幅支撑半径为 $2s=a/6$，故与 $h$ 的角半径 $a$ 球冠不交。对这些坏结果的 Kraus 向量作堆叠，按 (25.28) 的同一相干核积分得到

$$
 \sqrt{p_{\rm bad,nonzero}}
 \le D\int_{\theta(u,h)\ge a}|\langle e_u,e_h\rangle|\,d\mu(u)
 \le2e^{-(m+2)a^2/8}.
 \tag{26.18}
$$

平方后为 $4e^{-(m+2)a^2/4}$；再加实际失败概率 $C_{\rm fail}/\lambda$。

极分解读出与保留工作成功态的迹范数差至多 $2C_{\rm fail}/\lambda$；为与旧的归一化仪器比较，加入其失败块再付至多 $C_{\rm fail}/\lambda$。仅为计算这个指定经典事件而偏迹工作后，两个归一化解码分布的总变差至多 $3C_{\rm fail}/(2\lambda)\le2C_{\rm fail}/\lambda$。合计得到 (26.17)，因为 $a^2/4=e^2/16384$。计算经典事件的偏迹不构成完整返回上界；(26.13) 仍保留全部工作系统。所有舍入及结果均在给定 $h$ 之前一次固定。$\square$

**引理 26.9（旁观记忆稳定的规定完成）。** 在 $\Phi_{\rm keep}$ 后附加 (19.4) 的独立场采样及保留的有理解码，然后恰接定义 17.1 的后缀。对每个原始允许场 $n$、每个 $h$，理想目标的同一完成态 $\Omega^{\rm keep}_{n,h}$ 满足

$$
 D_{\rm tr}\!\left(\Omega^{\rm keep}_{n,h},
       \tau_h\otimes\operatorname{Tr}_R\Omega^{\rm keep}_{n,h}\right)
 \ge\frac1{4\sqrt\lambda}.
 \tag{26.19}
$$

证明。场采样只作用于独立非参考来源；将其全部输出态张量到 $\phi_h,\Xi_h$ 上。计算并保留最终解码器，同时保持原始标签和全部场数据，是这些非参考系统上的等距。因此它保持交叉块迹范数及差界 $B_*/\lambda$。以下将这些旧口统记为 $M$，并将相应扩充后的领先态仍写作 $\Xi_h$；其迹至多二。

规定后缀不读取旧获取或场输出。令 $\mathcal F_v$ 为它的参考边缘通道，$v=n(+d e_x)$，并置 $\gamma=\sqrt m/D$、$W_1=\operatorname{span}\{e_h,e_1\}$。式 (17.12)、(22.9)、(22.10) 中两个原生等距与终端等距的算子范数差依次为 $6\gamma,6\gamma,8\gamma$；这些算子范数界张量任意旧旁观记忆后不变。

在三个接触处作“理想前缀、实际后缀”的望远镜比较。理想前缀恒等作用于 $R$，故即使 $Y$ 在 $R,M$ 间相关，其参考支撑仍在 $W_1$。任意等距差 $\varepsilon$ 对应的联合迹范数差至多 $2\varepsilon\|Y\|_1$；其余非参考节点及实际后缀均为 CPTP。故直接在联合空间上有

$$
 \| (\mathcal F_v\otimes\operatorname{id}_M)(Y)-Y\|_1
 \le(12+12+16)\gamma\|Y\|_1=40\gamma\|Y\|_1,
 \quad\operatorname{supp}Y\subset W_1\otimes M.
 \tag{26.20}
$$

这是 (22.11) 的原等距证明对任意旁观记忆的稳定延伸，不要求初态纯化，也不假定 $Y$ 是乘积。将它用于正的 $\Xi_h$，至多付 $80\gamma$。为取得下界检验，仅在完成态中偏迹新后缀系统；所得旧 $RM$ 态距 $\Xi_h$ 的迹范数至多 $B_*/\lambda+80\gamma$。于是其交叉块范数至少

$$
 \frac1{2\sqrt\lambda}-\frac{B_*}{\lambda}-80\gamma
 \ge\frac1{2\sqrt\lambda}-\frac1{8\sqrt\lambda}
                         -\frac1{8\sqrt\lambda}
 =\frac1{4\sqrt\lambda},
 \tag{26.21}
$$

因为 $\gamma\le1/\sqrt m=s/\sqrt\lambda$、$80s\le1/8$。引理 26.6 的对偶检验给约化态相对自身边缘的同一下界；迹距离收缩再给全部实际完成口的 (26.19)。偏迹新口只用于下界见证，实际比较仍包含全部新旧口，不删去任何记录，也不在可区分历史间求消。此结论只量化于忽略旧输出的定义 17.1 固定完成，不量化于任意反馈恢复后缀；它不是另一个单脉冲首退出限制。$\square$

**命题 26.10（条件原生供应者的原全场成功与返回缺陷）。** 假设一个有限原生获取前缀 $\Gamma_e$ 用至多 $L_e-2$ 次前向 $V$、零次场重置、不执行规定终端，并保留 (26.7) 的逻辑口，且在仅忘记额外原生访问及工作口后满足

$$
 \sup_hD_{\rm tr}\!\left(\operatorname{Tr}_{\rm extra}\Gamma_e(\tau_h),
                              \Phi_{\rm keep}(\tau_h)\right)
 \le E_e\le1/t.
 \tag{26.22}
$$

前缀不接入场源，故此条件及其输入律对所有原始 $n$ 相同。一个保留这些逻辑系统的完整输出近似证书必然蕴含 (26.22)；此假设没有断言供应者存在。接 (19.4) 的场采样部分、以下固定解码器及定义 17.1 的精确后缀，则同一实际运行在每个原始 $n,h$ 上以失败率至多 $2e/3\le e$ 达到 (19.2) 的 $e$ 精度，且其全部实际输出返回满足

$$
 \Delta_{n,h}\ge\frac1{4\sqrt\lambda}-2E_e
 \ge\frac{192}{\sqrt t}-\frac2t
 \ge\frac{96}{\sqrt t}.
 \tag{26.23}
$$

证明。全部额外口仍在实际 $K$ 中，不假定它们与输入无关。公共场采样、解码及后缀收缩 (26.22) 的距离；投影到保留逻辑口所对应的完整理想完成空间后，距离仍至多 $E_e$。自身边缘返回的 $2$-Lipschitz 性及引理 26.9 给前两项；$t\ge1$ 给最后一项。由偏迹收缩，这个下界同时约束未投影的全部实际输出。

参考方向好事件为 $\|\widehat h-h\|_\infty\le e/16$。引理 26.8 和 (26.22) 的事件概率收缩给其失败率

$$
 \frac{K_{\rm risk}}t+4e^{-t/16384}\le e/6+e/6=e/3,
 \tag{26.24}
$$

这里分别用了 (26.3) 和 $t\ge16384\log(24/e)$。没有换成二元最优检验或依赖 $h$ 的解码器。

仅复用 (19.4) 的场采样部分：在 $z=0,\pm u_e e_x,\pm u_e e_y$ 的每个点，对三个固定 Pauli 轴各取 $\ell_e$ 个样本。保留全部 $15\ell_e$ 枚令牌、测后态、原始结果及实际副本。所有场坐标估计误差至多 $eu_e/16$ 的好事件，其失败率为

$$
 30\exp[-\ell_e e^2u_e^2/512]\le e/3.
 \tag{26.25}
$$

令 $n_0=n(0)$、$n_a=\partial_a n(0)$、$\widehat n_0=\widehat n(0)$、
$\widehat v_a=[\widehat n(+u_e e_a)-\widehat n(-u_e e_a)]/(2u_e)$，保留全部均值与差分，并精确输出有理四元组

$$
 \widehat D=\left(
 \frac{\widehat h\cdot[\widehat n_0\times\widehat v_x]}2,
 \frac{\widehat h\cdot[\widehat n_0\times\widehat v_y]}4,
 0,\frac{\widehat h\cdot\widehat v_y}2\right).
 \tag{26.26}
$$

所有输入估计及 $u_e$ 为有理数，有限算术可以精确完成，不另付舍入误差；旧两坐标解码器、原始标签和实际算术工作输出仍保留。原轴向 $C^2$ 假设给中心差分偏差

$$
 \left\|\frac{n(u_e e_a)-n(-u_e e_a)}{2u_e}-n_a\right\|_2
 \le\frac1{2u_e}\int_{-u_e}^{u_e}2|v|\,dv=u_e.
$$

场采样误差对中心差分再贡献至多 $\sqrt3e/16$。因此两好事件上，

$$
\begin{gathered}
 \|\widehat h-h\|_2\le e/8,\qquad
 \|\widehat n_0-n_0\|_2\le e^2/64,\\
 \|\widehat v_a-n_a\|_2\le u_e+\sqrt3e/16\le e/4,\\
 \|\widehat h\|,\|\widehat n_0\|,\|\widehat v_a\|\le2,
 \qquad\|n_0\|=1,\quad\|n_a\|\le1.
\end{gathered}
\tag{26.27}
$$

具体分解为

$$
\begin{aligned}
 &\left|\widehat h\cdot[\widehat n_0\times\widehat v_a]
               -h\cdot[n_0\times n_a]\right|\\
 &\le\|\widehat h-h\|_2\|n_0\|_2\|n_a\|_2
 +\|\widehat h\|_2\bigl(
 \|\widehat n_0-n_0\|_2\|\widehat v_a\|_2
 +\|n_0\|_2\|\widehat v_a-n_a\|_2\bigr)\\
 &\le e/8+2(2e^2/64+e/4)\le11e/16.
\end{aligned}
$$

所以第一、二坐标误差分别至多 $11e/32,11e/64$；第四坐标误差至多
$[e/8+2(e/4)]/2=5e/16$，第三坐标误差为零，均严格小于 $e$。两个好事件不必独立；联合坏概率由并集界至多 $2e/3$。TP 固定后缀不改实际解码边缘，故这是全部原始场及方向上的同一个成功消费者。

资源也属于同一运行。获取之后，场部分用零次 $V$、$15\ell_e$ 次重置；定义 17.1 再用两次 $V$、两次独立 $+d e_x$ 重置。因此

$$
 T_V\le L_e,\qquad T_{\rm reset}=15\ell_e+2\le18N_e+1=Q_e,
 \qquad T_R\le T_{\rm acq}+3.
 \tag{26.28}
$$

重置界用 $18N_e\ge15\ell_e+1$。后缀的两枚令牌分别是定义 17.1 的 $F,S_t$，均在 $+d e_x$ 独立重置；$d=1/64$、$\tau_0=1$。只在第二枚新鲜且此前未经改动的 $S_t$ 上恰执行一次规定的 $U_{\rm term}=\exp[-idJ\cdot\sigma/m_e]$，不另供应其逆。不添加旧的 $3k_e$ 参考获取阶段；反馈、重试及截止均按最坏分支支付。

若另有一个使用 $\nu_e$ 次 $Q_D$ 或受控 $Q_D$ 的逻辑字，并满足

$$
 q_e=\left\lceil\log_2(D_eL_e/e)\right\rceil,\qquad
 \nu_eq_e\le L_e-2,
 \tag{26.29}
$$

则定理 24.2、24.5 的完整访问替换误差至多
$\nu_e e/(D_eL_e)\le e/D_e\le1/(2t)$。再有至多 $1/(2t)$ 的逻辑完整通道误差，才足以得到 (26.22)。每个逻辑逆仍是一次新的付费访问，使用新鲜记录 $Z_i$；旧记录全部保留。这里没有给出 $W$ 的逻辑字、次数、归一化或原生成本上界，也没有给其成本下界。访问的仿射压缩仍为 $(I+2J_{\rm axis})/D$，保留偏移和尺度；QSVT 投影块不成为确定性通道。

具体地，逻辑获取口包含原标记 $R$、相干 $K_{\rm work}$、测后 $L$、原始 $l$ 及实际副本、旧两坐标解码器、有理 $\widehat h$、固定公共程序及路由和工作输出。条件原生实现还必须把每个实际探针及其回用、每次前向尝试的 $H,E$、$X$ 读出结果和测后系统、原始及复制访问结果、成功/失败/截止/停止寄存器、计数器、编译及 LCU/QSVT 工作区、旧量子及经典记忆、程序、路由和任何额外实际环境一并纳入 $K$。

场与算术部分再加入全部 $15\ell_e$ 枚令牌及其测后态、原始测量结果和实际读出副本、均值、两条中心差分、最终四坐标有理解码及工作输出。规定后缀再加入 $B,A,F,S_t$、两组新的 $H,E$、两套原始符号历史及全部实际副本，以及定义 17.1 的程序、路由和步进输出。其约化节点沿用声明的实际端口；确实生成的额外环境也必须保留。

实际经典记录不被擦除或为返回上界而偏迹。相干工作口也不能以代数求和替代：其领先交叉块范数为
$\sum_l\|f_l\|\|g_l\|/\sqrt m$；只有偏迹该工作口才会变为小标量流
$\sum_k\overline{f_{lk}}g_{lk}$。后者是 (26.6) 的性质，不是 (26.7) 的完整输出性质。

在允许场 $n_*$ 上，用实际最终 (26.26) 的前两坐标定义 (25.2) 的风险，则 $\beta_e\le2e/3$，同一完成态有 $\delta_e\ge96/\sqrt t$，且 $\overline\delta\ge\delta_e$。这是对条件供应者的陈述，既不推翻原生关系 (25.3)，也不改变以它为假设的推论 25.12。

该目标及每个满足上述近似和资源条件的供应者，其返回与 $\sqrt{\log(1/e)}/t$ 的比值趋于无穷，与 $\log(1/e)/t$ 的比值也趋于无穷。特别地，没有绝对常数能给此目标所要求的 $A\sqrt{\log(1/e)}/t$ 获取返回证书。完成后的原归一化量满足

$$
 \frac{D_e e^2\Delta_{n,h}}{\log(1/e)}
 \ge96\frac{D_e}{m_e}\frac{\sqrt t}{\log(1/e)}
 \longrightarrow+\infty,
 \qquad\frac{\sqrt t}{\log(1/e)}\ge\frac{\sqrt{C_t}}e.
 \tag{26.30}
$$

这是该单一保留工作目标的下界，不是下确界 $R(e)$ 的下界。量词不覆盖其它原生构造、改变工作接口的通道或读取旧输出的任意恢复后缀；定理 25.9 的约化直接参考访问放宽类反例也不被此结论否定。原 (19.12)、原生解码依赖关系及其它全方向原生构造仍是未解决命题。

本推导的中间工具为相干振幅指数级数、有限极分解、秩一迹范数、紧集上一致逼近、迹范数对偶和 CP 收缩；其目标特定关系是 (26.9)、(26.13)、(26.15) 及对同一完整完成的 (26.19)、(26.23)。这些关系不以有限高阶分量非零代替近似下界，也不从抽象有限矩阵的存在推得原生实现。$\square$

**定义 26.11（另一约化工作接口的待证候选）。** 可以另定义一个不同的候选通道：在尚未制造任何经典 $k$ 记录或副本前，对未测量的 $K_{\rm work}$ 作非参考的约化替换
$X\mapsto\operatorname{Tr}_{K_{\rm work}}X\otimes\kappa_{K_{\rm work}}$，其中 $\kappa$ 为固定已知态，替换后的同名工作口及全部访问记录仍保留。这改变了 (26.7) 的输出接口；引理 26.6–26.9 对保留相干工作目标的结论不宣称适用于它。

这个候选的付费原生分解、全部共同实际访问及工作输出上的返回界、最坏 $L_e-2$ 调用证书均为待证条件。若其实现确实生成额外实际环境，该环境也须纳入自身边缘比较并另给界。约化 CP 记号不供应上述条件，也不允许擦除已经存在的原始记录。此定义不蕴含候选的可实现性、充分返回率或原 (19.12) 的任一结论。

## 追加锚（本行以下为增补区）

## 27. 原全场成功控制器的 Fourier–beta 返回上界

**定理 27.1（原置信度下极限的负分支）。** 在定义 19.1 的精确原元组、原始全部场及方向、混合辅助、量子与经典记忆、反馈、纠缠和探针回用的完整比较类中，采用其声明的有限 CP 实际端口语义，有

$$
\liminf_{\substack{e\downarrow0\\e\in\mathbb Q_{>0}}}
\frac{D_e e^2R(e)}{\log(1/e)}=0.
\tag{27.1}
$$

证明。调用 [OTF008 定理 1.2](OTF_008_NATIVE_FOURIER_BETA_ACQUISITION_AND_FULL_RETURN.md) 的完整原生控制器。其显式窗口为 OTF008 式 (2.7) 的 $e=2^{-r}$、$r\ge r_0$；$t=m_e e^2$，所有内部精度只用于构造，不替换 (19.1)。同一个与实际 $n,h$ 无关的有限控制器，在全部原始 $n,h$ 上以同一有理四坐标解码器满足失败概率至多 $2e/3\le e$。它按最坏分支使用至多 $L_e$ 次 forward $V$、恰 $15\ell_e+2\le Q_e$ 次场重置，并恰接定义 17.1 的固定后缀，执行一次原规定终端。全部原生访问历史、截止及失败、探针、场、解码、程序、工作、补偿和终端输出都进入该运行自己的完整实际 $K$；原始记录不删除。

该实现使用定义 26.11 的具体选择：在任何经典 $k$ 记录或副本生成前，将未测量的 $K_{\rm work}$ 作声明的非参考替换，并保留同名固定输出；其 CP 节点的代数 Kraus 标签不是另行生成的物理环境。若另一实现生成额外实际环境，须将其纳入 $K$ 并另证界。这里没有把有限 CP 通道的存在直接当作原生访问：OTF008 第 5–8 节给付费的全部正、逆、受控逻辑字及同空间完整输出误差，最终上界来自其第 9–10 节的同一运行。

故以同一个绝对常数
$C_{\rm final}=2\cdot768^2(C_{\rm return}+3C_{\rm fail})+5$，

$$
0\le R(e)\le\frac{C_{\rm final}}{m_e e^2},\qquad
0\le\frac{D_e e^2R(e)}{\log(1/e)}
\le\frac{C_{\rm final}(D_e/m_e)}{\log(1/e)}\longrightarrow0
\quad(e=2^{-r},\ r\to\infty).
\tag{27.2}
$$

这里 $D_e/m_e\to1$，二进精度列属于原正有理域。全域归一化量非负，沿此合法列趋零即得 (27.1)。式 (19.11) 的逆维数精度下界仍成立；失效的是对原全比较类要求统一正对数因子的 (19.12) 正分支。$\square$

**推论 27.2（同一原生成功控制器反驳通用关系 (25.3)）。** 对任意 $c_0,c_1>0$ 及任意正有理精度窗口，存在其中的二进 $e$ 以及上述同一原全场成功控制器，使 (25.3) 不成立。

证明。固定允许场 $n_*$，取实际最终四坐标解码器的前两坐标作为定义 25.1 的 $(\widehat a,\widehat b)$。由定理 27.1 所用控制器的同一成功和返回证书，

$$
\beta_e\le2e/3,\qquad\delta_e\le C_{\rm final}/t,\qquad
\beta_e+\delta_e\longrightarrow0,
\qquad c_0e^{-c_1t\delta_e}\ge c_0e^{-c_1C_{\rm final}}>0.
\tag{27.3}
$$

在任意给定窗口内取充分小的同一二进 $e$ 即严格违反 (25.3)。风险与返回来自同一实际控制器及其完整输出，不组合分别可达的界；该控制器本身仍对全部原场及方向成功。此反例在声明有限 CP 实际端口的原生类内，不是直接 $R$ 访问放宽反例。引理 26.6–26.9 的保留相干工作目标及其固定完成的下界保持原范围；这里使用的是定义 26.11 的不同接口。$\square$

## 追加锚（本行以下为增补区）
