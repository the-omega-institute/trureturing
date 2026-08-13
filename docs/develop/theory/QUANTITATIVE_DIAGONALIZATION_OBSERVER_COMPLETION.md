# 观察者账本量子力学·续编
## 定量对角化与投影完成接口
### Quantitative Diagonalization and the Observer–Completion Interface

> **文档状态。** 本文位于 `docs/develop/theory`，是理论摄入的参考输入，不是数学真源。Lean 内核中的声明、证明项与公理闭包仍是唯一承重数学。本文严格区分：`[已证·Lean]`、`[存量·理论]`、`[定义·新]`、`[命题·待证]`、`[猜想]` 与 `[边界]`。
>
> **续编位置。** 本文不是另起炉灶，而是接续 [GICT](./GICT.md) VII.4–VII.7 的“不动点—定义—分类—自应用”链，以及 [OBSERVER-QUANTUM](./OBSERVER-QUANTUM.md) 第 2 节与 §§42–47 的“有限读数—对角逃逸—可数账本/不可数世界接缝”。
>
> **去重纪律。** 已有冻结声明若足以承担某一结论，本文只绑定和复用，不以“更强、更漂亮、少一个假设”为理由制造重复模块。只有当下游某个具名消费者确实需要新签名时，才提出新的 Lean 声明。

---

## 摘要

存量理论已经分别拥有两台发动机：

1. **定量对角化**：对角逃逸不再只是“存在一个漏项”，而有精确数量、同时捕获乘积律、完整 Hamming 距离剖面、典型边距浓缩与群作用下的轨道分解；
2. **观察者完成结构**：有限观察是带纤维的读数，solenoid 是逆极限型对象，连续路径具有可见实流与恒定隐藏偏移，有限循环窗口具有精确观察者距离。

尚未建立的不是又一个“对角定理”，而是两台发动机之间的**类型正确接口**：

> 当一个整体评价系统被投影、限制、粗粒化或完成时，对角操作是否随之自然下降？若不下降，差异由哪一种结构失配造成，能否被精确计量并沿尺度复合？

本文把这一缺口写成自然性方块：

$$
\boxed{
Q_{j,i}\circ\Delta_j
\quad\text{versus}\quad
\Delta_i\circ P_{j,i}
}
$$

其中 $P_{j,i}$ 投影评价表，$Q_{j,i}$ 投影对角输出，$\Delta_i$ 是第 $i$ 层的扭曲对角算子。两条路径的距离称为**对角投影缺陷**：

$$
\boxed{
\varepsilon^{\Delta}_{j,i}(E)
=
d_i\!\left(
Q_{j,i}(\Delta_jE),
\Delta_i(P_{j,i}E)
\right).
}
$$

本文进一步把总缺陷拆成两个独立来源：

- **对角读取缺陷**：投影是否保持“取自坐标”这一操作；
- **扭曲自然性缺陷**：值变换是否与输出投影交换。

这使“先整体自指再观察”与“先有限观察再自指”的差别不再是一句哲学判断，而成为可证明为零、可构造正反例、可沿尺度累积、也可能阻止极限算子存在的数学对象。

---

# 第一部　继承账：存量理论已经有什么

## 1.1 存量理论承接矩阵

| 存量位置 | 已有内容 | 当前地位 | 本文如何使用 |
|---|---|---|---|
| GICT VII.4–VII.6 | 坐标系不动性、定义算子、分类坐标化、Lawvere/对角线、自应用四衣 | `[存量·理论]`，部分有经典锚与有限证书 | 提供“为什么研究自应用”的语义背景，不重复定义其哲学含义 |
| GICT 7.9–7.12 | 塔即环、自指四命运、自量之钟 | `[存量·理论]` | 只保留为历史来源；本文不把黄金方程等同于一般对角算子 |
| OBSERVER-QUANTUM §2 | finite readout、读数纤维、整体自逼近、可见圆与隐藏纤维 | `[存量·理论]` | 提供观察投影的原始语义；本文把它类型化为 $P,Q$ |
| OBSERVER-QUANTUM §§42–47 | 对角线、逃逸率、边距、可数账本与不可数世界接缝 | `[存量·理论]`，其中若干结论已有 Lean 锚 | 本文不再宣称“发现可定量对角化”，而研究其跨尺度自然性 |
| 评注 27.559 | 归纳/逆极限、状态限制、有限观察的对偶极限叙事 | `[存量·理论/证书]`，并非本文新增的 Lean 定理 | 提供完成方向；本文只新增“对角算子能否下降到该极限”的问题 |
| `D5/S0/Diagonal/*` | 精确逃逸、捕获、距离与浓缩 | `[已证·Lean]` | 作为定量内核直接复用 |
| `D5/S1/Solenoid/*` | 路径分解、路径轨道分类 | `[已证·Lean]` | 作为 projective/hidden-fiber 应用载体，不自动等同量子态空间 |
| `D5/S3/Observer/MetricGeometry/*` | 整数轨道、有限循环窗口、跨可见相位的扩展距离 | `[已证·Lean]` | 提供有限层候选度量；尚缺尺度间映射 |

## 1.2 已证 Lean 锚点

本文依赖但不复制以下声明：

### `[已证·Lean]` 有限定量对角化

- `D5/S0/Diagonal/EscapeCount.escaped_listing_card`；
- `D5/S0/Diagonal/CaptureCount.capture_inter_card`；
- `D5/S0/Diagonal/CaptureCount.capture_independent`；
- `D5/S0/Diagonal/DistanceProfile.distance_profile_card`；
- `D5/S0/Diagonal/TypicalDensity.typical_density_failure_probability_tendsto_zero`；
- `D5/S0/Diagonal/EquivariantEscape.equivariant_escaped_card`。

最后一个声明带有具名的 `OrbitDecomposition` 输入；本文不得把它改写成“任意群作用自动得到该乘积公式”。

### `[已证·Lean]` 观察者有限窗口

- `D5/S3/Observer/MetricGeometry/WindowObserverDistance.window_observer_distance_eq_cycle_distance`。

它证明单一有限循环窗口内部的观察者对偶距离等于循环图距离。它尚未给出不同窗口尺寸之间的 canonical bonding map。

### `[已证·Lean]` solenoid 路径分支

- `D5/S1/Solenoid/PathOrbitClassification.path_joined_iff_real_flow_orbit`。

它分类路径连通性，不自动提供评价表、对角扭曲或量子状态表示。

## 1.3 唯一新增缺口

存量理论已经同时拥有：

$$
\text{对角算子}
\qquad\text{与}\qquad
\text{有限观察/逆极限}.
$$

但尚未拥有以下方块的统一、可复用形式：

$$
\begin{CD}
\mathcal T_j @>{\Delta_j}>> \mathcal O_j\\
@V{P_{j,i}}VV @VV{Q_{j,i}}V\\
\mathcal T_i @>>{\Delta_i}> \mathcal O_i.
\end{CD}
$$

本文的新增对象只有一个：**该方块的自然性、失败方式和定量缺陷**。

---

# 第二部　类型化内核：先把箭头写对

## 2.1 `[定义·新]` 评价表空间

给定地址类型 $A$ 与值类型 $Y$，定义评价表空间

$$
\mathcal T(A,Y)=Y^{A\times A}.
$$

元素

$$
E:A\times A\to Y
$$

可等价写成 curried 形式 $A\to A\to Y$。本文使用二元形式，是为了显式记录对角嵌入。

## 2.2 `[定义·新]` 对角读取

定义对角嵌入

$$
\delta_A:A\to A\times A,
\qquad
\delta_A(a)=(a,a).
$$

对角读取算子为拉回

$$
D_A=\delta_A^*:
\mathcal T(A,Y)\to Y^A,
$$

即

$$
D_A(E)(a)=E(a,a).
$$

## 2.3 `[定义·新]` 扭曲后作用

给定扭曲

$$
\tau:Y\to Y,
$$

定义逐点后作用

$$
T_\tau:Y^A\to Y^A,
\qquad
T_\tau(u)=\tau\circ u.
$$

## 2.4 `[定义·新]` 扭曲对角算子

定义

$$
\boxed{
\Delta_{A,Y,\tau}=T_\tau\circ D_A.
}
$$

所以

$$
\Delta_{A,Y,\tau}(E)(a)=\tau(E(a,a)).
$$

这与现有 `D5/S0/Diagonal/EscapeCount.diagonal` 的数学内容一致；未来 Lean 实现应优先复用或包装现有声明，不另造同义核心。

## 2.5 `[定义·新]` 捕获、逃逸与边距

一行 $E(a,-)$ 捕获对角对象，指

$$
E(a,-)=\Delta(E).
$$

评价表逃逸，指

$$
\Delta(E)\notin\operatorname{range}(a\mapsto E(a,-)).
$$

若输出函数空间带代价 $c_A$，定义行边距

$$
\operatorname{margin}_a(E)
=
c_A(E(a,-),\Delta(E)),
$$

以及最小边距

$$
\operatorname{margin}(E)
=
\inf_{a\in A}\operatorname{margin}_a(E).
$$

`[边界]` KL divergence 等对象不是对称度量；若使用散度，本文称其为 cost/defect，而不使用只有度量才成立的“距离零当且仅当相等”等结论，除非已另证严格性。

---

# 第三部　多尺度观察系统

## 3.1 `[定义·新]` 尺度范畴

令 $I$ 为一个预序或小范畴。符号 $j\succeq i$ 表示 $j$ 是比 $i$ 更细、信息更多或窗口更大的层。

每层给定：

$$
(A_i,Y_i,\tau_i),
$$

评价表与对角输出空间：

$$
\mathcal T_i=Y_i^{A_i\times A_i},
\qquad
\mathcal O_i=Y_i^{A_i},
$$

以及对角算子：

$$
\Delta_i:\mathcal T_i\to\mathcal O_i.
$$

## 3.2 `[定义·新]` 两类投影

对 $j\succeq i$，分别给出：

$$
P_{j,i}:\mathcal T_j\to\mathcal T_i,
$$

$$
Q_{j,i}:\mathcal O_j\to\mathcal O_i.
$$

两者承担不同职责：

- $P$ 投影完整评价表；
- $Q$ 投影已经取完对角后的输出函数。

它们必须满足恒等与复合律：

$$
P_{i,i}=\operatorname{id},
\qquad
P_{k,i}=P_{j,i}\circ P_{k,j},
$$

$$
Q_{i,i}=\operatorname{id},
\qquad
Q_{k,i}=Q_{j,i}\circ Q_{k,j}.
$$

不能只给一个模糊的“观察投影”并在需要时同时扮演二者；这正是旧稿类型不闭合之处。

## 3.3 `[定义·新]` 严格对角自然性

称尺度系统严格对角自然，若对所有 $j\succeq i$：

$$
\boxed{
Q_{j,i}\circ\Delta_j
=
\Delta_i\circ P_{j,i}.
}
$$

这表示整体/细层先做对角化再观察，与先观察再在粗层做对角化完全一致。

## 3.4 `[定义·新]` 对角投影缺陷

若 $\mathcal O_i$ 上给定扩展伪度量或具名 cost $d_i$，定义

$$
\boxed{
\varepsilon^{\Delta}_{j,i}(E)
=
d_i\!\left(
Q_{j,i}(\Delta_jE),
\Delta_i(P_{j,i}E)
\right).
}
$$

必须同时记录 $d_i$ 的性质：metric、pseudometric、ENNReal extended metric、asymmetric divergence，或一般非负 cost。不同性质允许的推论不同。

---

# 第四部　缺陷解剖：不是一个误差桶

## 4.1 `[定义·新]` 对角读取缺陷

记

$$
D_i:\mathcal T_i\to Y_i^{A_i}
$$

为未扭曲的对角读取，并把 $Q_{j,i}$ 同时视为对应函数空间的输出投影。定义

$$
\varepsilon^{D}_{j,i}(E)
=
d_i\!\left(
Q_{j,i}(D_jE),
D_i(P_{j,i}E)
\right).
$$

它只测量：**观察投影是否保留“取自坐标”**。

## 4.2 `[定义·新]` 扭曲自然性缺陷

定义

$$
\varepsilon^{T}_{j,i}(u)
=
d_i\!\left(
Q_{j,i}(T_{\tau_j}u),
T_{\tau_i}(Q_{j,i}u)
\right).
$$

它只测量：**值扭曲是否与输出投影交换**。

## 4.3 `[命题·待证]` 总缺陷分解不等式

假设：

1. $d_i$ 满足三角不等式；
2. $T_{\tau_i}$ 关于 $d_i$ 是 $L_i$-Lipschitz。

则应有

$$
\boxed{
\varepsilon^{\Delta}_{j,i}(E)
\le
\varepsilon^{T}_{j,i}(D_jE)
+
L_i\,\varepsilon^{D}_{j,i}(E).
}
$$

证明路线只有一个三角分解：

$$
QTD
\longrightarrow
TQD
\longrightarrow
TDP.
$$

这条命题是本文第一优先 Lean 目标，因为它把“观察造成了缺陷”拆成两个可独立证伪的来源，而不是定义一个新数再证明它等于自己。

## 4.4 `[命题·待证]` 严格自然性推论

若

$$
\varepsilon^{D}_{j,i}(E)=0
$$

且

$$
\varepsilon^{T}_{j,i}(D_jE)=0,
$$

则

$$
\varepsilon^{\Delta}_{j,i}(E)=0.
$$

若 $d_i$ 只是伪度量，只能推出两条路径在该伪度量下不可区分；不能未经分离性证明就推出函数相等。

## 4.5 `[命题·待证]` 尺度复合不等式

设 $k\preceq i\preceq j$，且 $Q_{i,k}$ 是 $L^Q_{i,k}$-Lipschitz。由 $P,Q$ 的复合律，预期：

$$
\boxed{
\varepsilon^{\Delta}_{j,k}(E)
\le
L^Q_{i,k}\,\varepsilon^{\Delta}_{j,i}(E)
+
\varepsilon^{\Delta}_{i,k}(P_{j,i}E).
}
$$

这条不等式把全尺度缺陷控制为局部尺度缺陷之和。对链

$$
i_0\preceq i_1\preceq\cdots\preceq i_m
$$

反复应用可得到加权 telescoping bound。它是把“观察者逐层展开”从叙述变成可计算账本的关键。

---

# 第五部　限制与商：两类观察不能混为一谈

## 5.1 `[命题·待证]` 嵌入限制系统严格交换

若有限窗口通过嵌入

$$
\iota_{i,j}:A_i\hookrightarrow A_j
$$

进入细层，并定义

$$
P_{j,i}(E)(a,b)
=
q_{j,i}(E(\iota a,\iota b)),
$$

$$
Q_{j,i}(u)(a)
=
q_{j,i}(u(\iota a)),
$$

同时值投影与扭曲交换：

$$
q_{j,i}\circ\tau_j
=
\tau_i\circ q_{j,i},
$$

则预期严格成立：

$$
Q_{j,i}\Delta_j
=
\Delta_iP_{j,i}.
$$

这里自然性的来源是

$$
(\iota a,\iota a)
=
(\iota\times\iota)(a,a).
$$

这应成为第一个无缺陷正例。

## 5.2 `[边界]` 商投影没有 canonical 表投影

若观察是满射/粗粒化

$$
r_{j,i}:A_j\twoheadrightarrow A_i,
$$

仅凭 $r_{j,i}$ 不能自然地把任意细层表

$$
E_j:A_j\times A_j\to Y_j
$$

变成粗层表。还必须选择聚合规则，例如求和、平均、最大值、条件期望或代表元。

因此“完成对象有投影”不自动意味着“评价表有对角自然投影”。聚合规则就是新增结构，也可能正是缺陷来源。

## 5.3 `[命题·待证]` 最小对角读取反例

取：

$$
A_j=\{0,1\},
\qquad
A_i=\{*\},
\qquad
Y=\{0,1\}.
$$

把两个细地址全部压到 $*$，并令粗层聚合为所有矩阵元的 OR。取细层表：

$$
E(0,0)=0,
\quad
E(1,1)=0,
\quad
E(0,1)=1,
\quad
E(1,0)=0.
$$

则：

$$
Q(D_jE)=0,
$$

但

$$
D_i(P_{j,i}E)=1.
$$

因此

$$
\varepsilon^D_{j,i}(E)>0.
$$

这个反例隔离了纯粹的“聚合混入非对角数据”问题，不需要量子、solenoid 或无限对象。

## 5.4 `[命题·待证]` 最小扭曲反例

仍取布尔值，以 OR 聚合输出，扭曲为 `Bool.not`。对

$$
u=(0,1)
$$

有

$$
Q(\neg u)=1,
\qquad
\neg Q(u)=0.
$$

所以即使对角读取本身被保持，非线性粗粒化也可能与扭曲不交换。

这两个最小反例应分别落 Lean，防止所有失败都被塞进一个不可解释的总 defect。

---

# 第六部　投影完成：无穷不是先验算子

## 6.1 `[定义·新]` projective completion

给定表空间逆系

$$
(\mathcal T_i,P_{j,i})
$$

和输出空间逆系

$$
(\mathcal O_i,Q_{j,i}),
$$

定义

$$
\mathcal T_\infty=\varprojlim_i\mathcal T_i,
\qquad
\mathcal O_\infty=\varprojlim_i\mathcal O_i.
$$

本文的“完成”首先只指这种 projective completion；它不自动等同 Cauchy 完备化、Stone–Čech 紧化、profinite completion 或物理宇宙的先验整体。

## 6.2 `[命题·待证/标准极限机制]` 相容对角族诱导唯一极限算子

若每个有限层都有

$$
\Delta_i:\mathcal T_i\to\mathcal O_i
$$

且严格自然：

$$
Q_{j,i}\Delta_j
=
\Delta_iP_{j,i},
$$

则由逆极限的泛性质，应存在唯一映射

$$
\boxed{
\Delta_\infty:
\mathcal T_\infty\to\mathcal O_\infty
}
$$

满足

$$
\pi_i^{\mathcal O}\Delta_\infty
=
\Delta_i\pi_i^{\mathcal T}.
$$

显式地：

$$
\Delta_\infty((E_i)_i)
=
(\Delta_i(E_i))_i.
$$

`[边界]` 这不是一个全新的范畴论原理；项目新增工作的价值在于为具体评价、观察和扭曲验证自然性条件，而不是重新命名逆极限泛性质。

## 6.3 `[定义·新]` 极限存在的障碍读法

若存在 $j\succeq i$ 与 $E_j$ 使

$$
Q_{j,i}\Delta_j(E_j)
\neq
\Delta_iP_{j,i}(E_j),
$$

则有限层对角输出不形成相容族，不能按上述公式直接定义 $\Delta_\infty$。

所以 defect 的第一含义不是“物理误差”，而是：

$$
\boxed{
\text{对角算子下降到 projective limit 的障碍。}
}
$$

## 6.4 `[猜想]` 近似自然性与近似极限

若局部缺陷沿一个 cofinal chain 可求和：

$$
\sum_m
w_m\,
\varepsilon^\Delta_{i_{m+1},i_m}
<\infty,
$$

并且输出空间在相应 metric/cost 结构下完备，预期可以构造一个近似相容的极限输出，且总偏差受该级数控制。

在给出明确的 metric inverse-limit construction 以前，这一条保持猜想状态。

## 6.5 `[存量·语义的精确翻译]` “从无穷开始”

一个整体元素

$$
x_\infty\in\varprojlim X_i
$$

不是“无限大数”，而是一族已经彼此相容的有限坐标：

$$
x_\infty=(x_i)_i.
$$

有限观察者只读其中某个 $x_i$。因此“整体先在、局部逐层显现”可以被严格翻译成 projective-coordinate 语言；但这只是一个数学模型，不是宇宙本体已被实验确认的结论。

---

# 第七部　接回观察者存量理论

## 7.1 有限读数纤维

OBSERVER-QUANTUM 已把有限观察写成带纤维的读数：多个完整历史可压入同一读数。本文将其分成两个不同问题：

1. 读数是否丢信息；
2. 读数是否保持对角操作。

第一问由纤维大小、熵或条件分布描述；第二问由 $\varepsilon^\Delta$ 描述。二者可能相关，但不是同一个定义。

## 7.2 有限循环窗口

`window_observer_distance_eq_cycle_distance` 给出固定 $M$ 内部的精确距离：

$$
d_M(a,b)=d_{\mathrm{cycle},M}(a,b).
$$

要形成多尺度理论，还缺：

- 哪些 $M,N$ 之间允许比较；
- 是嵌入、模商还是其他 coarse-graining；
- 观测量如何在窗口间推送/拉回；
- $d_M$ 与 $d_N$ 之间是否 Lipschitz；
- 对角评价表在这些映射下如何投影。

在这些箭头没有定义以前，“有限窗口趋向 solenoid”只能是研究目标，不能由单窗口距离定理自动推出。

## 7.3 solenoid 路径分支

`path_joined_iff_real_flow_orbit` 已经证明：

$$
x\sim_{\mathrm{path}}y
\iff
\exists t,\ y=\operatorname{realFlow}(t)+x.
$$

它说明隐藏核偏移标签路径分支。要接入本文，还需构造：

- 有限商/有限窗口上的评价表 $E_i$；
- 相容扭曲 $\tau_i$；
- 表投影 $P_{j,i}$ 与输出投影 $Q_{j,i}$；
- 区分同一实流轨道与不同隐藏偏移时的 defect。

路径分类本身不提供这些数据。

## 7.4 跨可见相位的无穷距离

现有 hidden-translation 模型中，跨可见相位的观察者扩展距离可等于 $\infty$。其直接原因是半范数零核包含能分离两点的非恒定观测量。

本文不得把该 $\infty$ 自动解释为：

- 对角完成缺陷发散；
- 物理能量无穷；
- type-II$_\infty$ 分类；
- 超选择定律。

只有构造了同一状态空间上的 $P,Q,\Delta,d$，才能比较两种“无穷”。

---

# 第八部　量子分支：局部—整体障碍不自动等于对角障碍

## 8.1 `[存量·理论]` 上下文性的位置

Kochen–Specker/上下文性通常表达：一族局部合法赋值不能拼成全局非上下文赋值。这是 local-to-global obstruction。

对角化表达：一个自索引评价表经扭曲后生成不在行像中的对象。这是 self-application obstruction。

二者可以相关，但不是定义上相同。

## 8.2 `[定义·新]` 可对角化上下文性适配器

若要把一个上下文模型接入本文，必须额外给出：

1. 上下文/事件的自索引地址类型 $A$；
2. 局部赋值如何组成二元评价表 $E(a,b)$；
3. 一个来源于原模型而非人为安装的扭曲 $\tau$；
4. 对角逃逸如何推出不存在全局截面；
5. 反方向是否成立，或只是一种充分证书。

缺少这些数据时，只能说两者都表现局部—整体张力，不能说“量子就是对角化”。

## 8.3 `[定义·新]` 到经典模型集合的距离

令 $\mathcal C$ 为具名的经典非上下文模型集合，量子/经验数据为 $Q$。定义：

$$
\delta_{\mathrm{ctx}}(Q)
=
\inf_{C\in\mathcal C}c(Q,C).
$$

这是一种 contextuality cost。它与 $\varepsilon^\Delta$ 是两个不同量：

- $\delta_{\mathrm{ctx}}$ 比较量子数据与经典模型集合；
- $\varepsilon^\Delta$ 比较两种操作顺序。

未来只有在证明二者的上界、下界或等价定理后，才能合并叙述。

## 8.4 `[边界]` 经典/量子不只是坐标变换

更换测量基具有坐标意味，但非交换可观测代数、上下文性与 Bell 型限制不能一般地被普通坐标变换消除。本文研究的是“观察顺序是否保持自指结构”，不宣称经典与量子仅是 $0$ 原点和 $\infty$ 原点的替换。

## 8.5 `[开放]` 几何层与矩阵量子层仍缺表示桥

当前 solenoid/观察者几何与有限密度矩阵/通道模型之间，仍缺至少：

- Hilbert 空间 $\mathcal H$；
- 表示 $\pi:C(\Sigma)\to B(\mathcal H)$；
- 实现更新的幺正或通道；
- 状态空间上的距离；
- 将 finite readout 与量子测量联系起来的定理。

对角投影理论可以组织这些证明责任，但不能替代它们。

---

# 第九部　信息率与光速：只允许条件桥

## 9.1 `[定义·新]` 因果过滤

给定离散因果图或局域系统、观察者轨迹 $\gamma(t)$，定义可访问窗口：

$$
W_O(t)\subseteq A.
$$

要求：

$$
t_1\le t_2
\Longrightarrow
W_O(t_1)\subseteq W_O(t_2).
$$

若系统有最大传播半径 $v_{\max}$，则窗口扩张受因果球控制。

## 9.2 `[命题·待证]` 有限字母表的原始信息流上界

若每个新进入窗口的局部单元只有 $q$ 个可能值，则在不加入相关结构时，新增原始状态容量至多：

$$
\Delta I_O(t)
\le
|W_O(t+1)\setminus W_O(t)|\log q.
$$

若再证明窗口新增壳层的大小受传播速度、边界面积与局部密度控制，才能得到一个含 $v_{\max}$ 的速率上界。

## 9.3 `[边界]` 光速不是固定比特率

现有物理中的 $c$ 首先约束因果传播。即使未来把 $v_{\max}$ 取为 $c$，观察者信息率仍一般依赖：

- 可访问边界面积；
- 自由度密度；
- 局部维数/字母表；
- 噪声与相关性；
- 记录和处理机制。

所以本文禁止无条件写：

$$
R_O=c.
$$

可以研究的是条件式：

$$
R_O
\le
F(c,\text{geometry},\text{capacity},\text{noise}).
$$

## 9.4 `[存量·语义]` 光速作为理想边界

在 rapidity 等坐标中，$v\to c$ 可对应坐标趋于无穷；这支持“有限边界可代表某坐标中的理想无穷远”的几何直觉。但它不证明 $c$ 本身是无穷，也不直接参与对角投影缺陷定义。

---

# 第十部　Zeckendorf、正规化与 solenoid：先分开交换子

## 10.1 `[定义·新]` 正规化—投影缺陷

设 $N$ 为数位正规化，$\pi_i$ 为有限数位窗口，$N_i$ 为有限层正规化。先独立研究：

$$
\varepsilon^N_i(x)
=
d_i(\pi_iN(x),N_i\pi_i(x)).
$$

它测量进位传播穿过窗口边界造成的不自然性。

## 10.2 `[边界]` 进位缺额不自动是对角缺陷

三值黄金缺额、底层进位计数与相位 cocycle 已有自己的定义。除非另行构造评价表 $E$、扭曲 $\tau$ 并证明：

$$
\varepsilon^N_i
\quad\text{控制或等于}\quad
\varepsilon^\Delta_i,
$$

否则不得把“进位缺额”改名为“对角完成缺陷”。

## 10.3 `[开放]` 复合交换子

真正可研究的复合对象是：

$$
\pi_iN\Delta
\quad\text{versus}\quad
N_i\Delta_iP_i.
$$

其总缺陷预期可再分解为：

$$
\text{对角投影缺陷}
+
\text{正规化投影缺陷}
+
\text{Lipschitz 放大项}.
$$

这会把黄金数位主线接入统一框架，而不是仅靠词语“完成、缺额、逃逸”相似。

---

# 第十一部　计算理论与有限误差几何

## 11.1 `[已证·Lean/经典机制]` 不存在可计算全能求值器

现有 `D5/S0/Computability/TotalOrbitEvaluator.no_computable_total_orbit_evaluator` 使用部分递归代码固定点与后继变换，排除能够在所有代码—输入对上给出总正确值的可计算求值器。

该结果属于经典不可计算性链，本文不重复证明。

## 11.2 `[开放]` 从不存在推进到误差几何

新的消费者问题是：给定有限资源、有限代码集或有限记录，任何近似求值器至少必须付出什么代价？候选量包括：

- 最少错误坐标数；
- 与对角程序的 Hamming 边距；
- 允许错误率下的最大覆盖规模；
- 记录固定后剩余候选数；
- 捕获事件之间的相关结构。

这些问题可复用 `D5/S0/Diagonal` 的计数工具，但需要先证明程序语义模型与自由函数表模型之间的桥。

---

# 第十二部　解析数论与 RH：最后接入

任何 $\zeta$/RH 适配器必须明确给出：

1. 地址/候选空间 $A$；
2. 值空间 $Y$；
3. 评价 $E(a,b)$ 的经典解析数论意义；
4. 扭曲 $\tau$ 的非人为来源；
5. 有限窗口与完成对象；
6. 对角逃逸或 defect 与经典 $\zeta$ 零点条件之间的双向桥。

尤其必须证明类似：

$$
\text{具名对角障碍}
\iff
\operatorname{Re}\rho=\frac12
$$

或一个足以推出它的严格定理。没有该桥时，对角化只能作为解释语言，不能计作 RH 推进。

---

# 第十三部　Lean 路线：只实现具名消费者需要的最小签名

## 13.1 目录建议

```text
D5/S0/Diagonal/Projection/
  Basic.lean
  Naturality.lean
  Defect.lean
  RestrictionSystem.lean
  QuotientCounterexample.lean
  ProjectiveLimit.lean
```

目录名称只是建议；若仓库现有层级已有可复用位置，应服从现有 MAP 与 FILEMAP，而不是为本文另造分类。

## 13.2 第一批声明候选

### A. 通用定义

```lean
def diagonalRead ...
def diagonalOperator ...
def diagonalProjectionDefect ...
```

在添加前必须先检查 `EscapeCount.diagonal` 等已有声明能否直接承担消费者。

### B. 缺陷分解

```lean
theorem diagonalProjectionDefect_le
    ... :
    totalDefect E ≤ twistDefect (diagonalRead E) + L * readDefect E
```

### C. 尺度复合

```lean
theorem diagonalProjectionDefect_comp_le ...
```

### D. 限制系统零缺陷

```lean
theorem restriction_diagonal_natural ...
```

### E. 两个最小反例

```lean
theorem quotient_or_read_defect_pos ...
theorem or_not_twist_defect_pos ...
```

### F. 极限诱导

```lean
def projectiveLimitDiagonal ...
theorem projectiveLimitDiagonal_unique ...
```

若 Mathlib 已有一般 inverse-limit/map API，应直接实例化，不复制一般范畴论定理。

## 13.3 反重复门

每个待实现声明必须回答：

1. 哪个具名下游定理会使用它？
2. 现有 frozen theorem 为什么不能直接满足该消费者？
3. 新声明是否只是旧声明的重排、去假设或 `Eq.symm`？
4. 两边对象是否有独立锚，而非定义后自证？
5. 反例是否来自给定结构，而非人为造一个必然成立的 classifier？

答不出时，正确产物是 bind report 或 open residual，不是新模块。

---

# 第十四部　阶段计划与杀死条件

## 阶段 0：存量绑定审计

- 建立 GICT、OBSERVER、PZG 与 Lean 声明的承接表；
- 删除被已有 frozen theorem 完整覆盖的“新命题”；
- 给每个真正新增目标指定消费者。

## 阶段 1：纯有限自然性

完成：

- 类型化 $D,T,\Delta,P,Q$；
- 总缺陷分解；
- 尺度复合不等式；
- 嵌入正例；
- OR 商反例；
- OR/NOT 扭曲反例。

这是最小可发表数学核。

## 阶段 2：projective limit

- 相容对角族诱导唯一极限映射；
- 失败时 defect 作为下降障碍；
- 近似自然性的可求和版本是否成立。

## 阶段 3：观察者有限窗口

- 选择具名尺度系统；
- 定义窗口间 $P,Q$；
- 证明 metric Lipschitz 常数；
- 计算 defect。

## 阶段 4：solenoid

- 采用仓库既有 projective presentation；
- 接入路径分支与 hidden kernel；
- 比较同分支/跨分支缺陷。

## 阶段 5：上下文与量子

- 先证明 local-to-global 模型适配器；
- 再比较 contextuality cost 与 diagonal defect；
- 最后才谈经典极限。

## 阶段 6：因果信息率

- 建立离散因果窗口容量上界；
- 单独验证与相对论/光速的物理桥。

## 阶段 7：解析数论

只有双向语义桥出现后才进入。

## 杀死条件

以下任何一项成立，都应收缩或终止相应分支：

1. 新缺陷只是不自然映射的定义展开，不能产生独立分类或界；
2. 所有自然实例都严格交换，正 defect 只能靠任意聚合器人为制造；
3. 现有范畴论/approximate naturality 文献已完整覆盖全部一般定理，而项目没有新的具体实例；
4. 观察者窗口之间不存在自然、物理或算术上具名的尺度映射；
5. quantum contextuality 适配器只能单向类比，无法给出原理论语义桥；
6. 信息率高度依赖任意编码，无法形成不变量；
7. solenoid 与矩阵量子层始终缺少表示定理；
8. RH 适配器无法把 defect 与经典零点性质连接。

失败本身必须进入判负账，不得通过改名扩大主张。

---

# 第十五部　论文拆分

## A. Finite Quantitative Diagonalization

整理既有 Lean 成果：精确逃逸、捕获乘积律、距离剖面、浓缩与等变推广。本文不为该论文重复制造定理。

## B. Diagonal Operators Across Observation Scales

本文真正新增的数学论文：

- 对角读取/扭曲分解；
- 投影自然性；
- 总 defect bound；
- 尺度复合；
- restriction/quotient 二分；
- 最小反例。

## C. Projective Completion of Diagonal Systems

- 相容有限算子诱导极限算子；
- defect 作为下降障碍；
- 近似自然性与可求和误差。

## D. Observer Windows and Solenoidal Realizations

- 具名窗口尺度系统；
- finite observer metric；
- solenoid projective presentation；
- hidden-fiber defect。

## E. Quantitative Contextuality Interface

只有 contextuality cost 与 diagonal defect 之间出现非平凡定理后独立成文。

## F. Causal Observer Information Bounds

只发表条件速率上界，不把 $c$ 定义成比特率。

---

# 总判词

存量理论已经说清：

- 自应用如何生成对角逃逸；
- 对角逃逸如何被定量；
- 有限观察如何压缩完整历史；
- 逆极限如何组织相容有限截面；
- solenoid 如何把可见实流与隐藏地址分层。

本文不再重复这些结论。它只补一条尚未被类型化的接缝：

$$
\boxed{
Q_{j,i}\Delta_j
\quad\text{是否等于}\quad
\Delta_iP_{j,i}？
}
$$

相等时，对角化可以穿过观察并下降到完成对象；不等时，总缺陷可被拆成：

$$
\boxed{
\text{对角读取失配}
+
\text{扭曲自然性失配}.
}
$$

这条接缝提供了一个可证伪、可分层、可落 Lean 的统一研究方向：

> **研究自指对角算子在有限观察、粗粒化与 projective completion 下的自然性，以及自然性失败时的定量障碍。**

它是对存量 GICT—Observer 理论的严格续编，不是用“对角化”重新命名所有分支。
