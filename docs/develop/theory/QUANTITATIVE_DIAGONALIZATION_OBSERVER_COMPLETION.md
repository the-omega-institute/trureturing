# 投影与完成下的对角化
## 自然性、缺陷分解及其素数—Li–Cayley 应用
### Diagonalization under Projection and Completion: Naturality, Defect Decomposition, and Prime–Li–Cayley Applications

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-13

> **文档地位。** 本文是 `docs/develop/theory` 中的正式论文稿与理论摄入源，不是 Lean 数学真源。文中标记为“仓库已形式化”的结果，以现有 Lean 声明为准；本文新增定理均给出完整纸面证明，但在获得 Lean 证明项、依赖闭包与冻结收据以前，不得在仓库治理层宣称为 `Closed`。
>
> **理论承接。** 本文续接 [GICT](./GICT.md) 中的不动点—对角化链和 [OBSERVER-QUANTUM](./OBSERVER-QUANTUM.md) 中的有限观察—完成结构，但不把二者仅凭语义相似直接等同。本文给出它们之间唯一需要的类型化接口，并证明其基本性质。
>
> **核心非主张。** 本文没有证明 Riemann 假设，没有把光速定义成信息处理率，没有把量子上下文性等同于 Cantor 对角化，也没有把欧几里得素数证明冒充为自应用表对角化。

---

## 摘要

本文研究对角自应用在投影、限制、粗粒化与逆极限完成下是否保持自然。对每个观察尺度 \(i\)，设 \(\mathcal T_i\) 为评价表空间，\(\mathcal U_i\) 为对角输出空间，\(\Delta_i:\mathcal T_i\to\mathcal U_i\) 为扭曲对角算子；对细尺度 \(j\succeq i\)，分别以
\[
P_{j,i}:\mathcal T_j\to\mathcal T_i,
\qquad
Q_{j,i}:\mathcal U_j\to\mathcal U_i
\]
投影完整评价表与已生成的对角输出。本文定义对角投影缺陷
\[
\varepsilon^\Delta_{j,i}(E)
=
d_i\!\left(
Q_{j,i}\Delta_j(E),
\Delta_iP_{j,i}(E)
\right),
\]
并证明三类一般定理。

第一，总缺陷分解为“对角读取失配”与“扭曲自然性失配”：
\[
\varepsilon^\Delta_{j,i}(E)
\le
\varepsilon^\tau_{j,i}(D_jE)
+
L_i\varepsilon^D_{j,i}(E).
\]
第二，缺陷沿尺度满足复合不等式，从而得到加权 telescoping bound。第三，严格自然的有限层对角族唯一下降到逆极限；在有限层投影可由极限满射提升时，极限对角算子的存在反过来强制有限层自然性。由此，对角缺陷被刻画为对角算子下降到完成对象的精确障碍，而非模糊的“观察误差”。

本文进一步证明：坐标限制型观察严格保持对角化；非线性商聚合则可以分别破坏对角读取与值扭曲，并给出最小布尔反例。作为算术应用，本文将欧几里得构造
\[
1+\prod_{p\in S}p
\]
刻画为有限素数账本的同时逃逸，并严格区分它与自应用对角化。作为谱应用，本文研究 Li–Cayley 坐标
\[
C(s)=1-\frac1s,
\]
证明临界线恰映到单位圆，函数方程反射变成倒数反射，临界线零点的 Li 镜像对贡献坍缩为模平方；任一离线零点四元轨道则沿某个整数探针子序列产生趋于负无穷的局部贡献。最后，本文证明固定阶截断收敛不足以支持阶数随截断增长的“对角探测”，给出统一对角极限定理与反例，并据此精确定位从 Li 判据走向 RH 所缺失的是全局余项控制，而不是再发明一个对角比喻。

---

## 1. 引言

经典对角论证解决的是一个定性问题：给定一族候选对象，能否利用候选族自己的评价结构构造一个不在该族中的对象？Cantor、Gödel、Turing 与 Lawvere 的不同版本共享同一机制：读取第 \(a\) 个候选在第 \(a\) 个位置上的值，再施加一个适当扭曲。

本仓库已经将这一机制推进到有限定量层。`D5/S0/Diagonal` 中现有 Lean 声明覆盖：

- 逃逸评价表的精确数量；
- 多行同时捕获的乘积律；
- 完整 Hamming 距离剖面；
- 最小逃逸边距的浓缩；
- 带轨道分解输入的等变计数。

另一方面，仓库已经拥有有限观察者窗口、solenoid 逆极限与路径分支等结构。但这两组结果并不会自动融合。一个有限观察者看到的评价表与完整系统中的评价表属于不同类型；“先在整体上对角化再投影”与“先投影再对角化”也不必相同。

本文的主问题因此不是“万物是否都能被称为对角化”，而是下面这个可证明、可反驳的交换问题：
\[
\boxed{
Q_{j,i}\circ\Delta_j
\stackrel{?}{=}
\Delta_i\circ P_{j,i}.
}
\]

这一问题有三个优点。

第一，它区分了真正的结构桥与语言类比。第二，它允许精确测量局部—整体失配。第三，它直接决定有限层对角算子能否下降到 projective completion。

本文的另一目标，是把近期讨论中的两个算术直觉放回严格位置：

1. 欧几里得素数构造确实是有限账本逃逸，但一般不是自应用评价表的对角化；
2. Li 系数确实提供一族能放大离线零点径向缺陷的整数探针，但“为每个零点选择一个阶数”仍不等于全局 Li 正性，更不等于 RH 证明。

---

## 2. 仓库中的已证承重结果

本文复用而不重复以下 Lean 结果。

### 2.1 有限定量对角化

现有声明包括：

- `D5/S0/Diagonal/EscapeCount.escaped_listing_card`；
- `D5/S0/Diagonal/CaptureCount.capture_inter_card`；
- `D5/S0/Diagonal/CaptureCount.capture_independent`；
- `D5/S0/Diagonal/DistanceProfile.distance_profile_card`；
- `D5/S0/Diagonal/TypicalDensity.typical_density_failure_probability_tendsto_zero`；
- `D5/S0/Diagonal/EquivariantEscape.equivariant_escaped_card`。

设有限地址集 \(A\) 满足 \(|A|=n\)，有限值集 \(Y\) 满足 \(|Y|=q\)，扭曲 \(\tau:Y\to Y\) 有 \(k\) 个不动点。现有形式化结果给出逃逸评价表数量
\[
(q^n-k)^n.
\]
因此均匀随机表的逃逸概率为
\[
\left(1-\frac{k}{q^n}\right)^n.
\]
本文不重新证明该精确计数，而把它作为有限层输入。

### 2.2 观察者有限窗口

现有声明
`D5/S3/Observer/MetricGeometry/WindowObserverDistance.window_observer_distance_eq_cycle_distance`
证明：有限循环窗口中，由一步更新缺陷单位球定义的对偶观察者距离，精确等于循环图距离。

### 2.3 Solenoid 路径分支

现有声明
`D5/S1/Solenoid/PathOrbitClassification.path_joined_iff_real_flow_orbit`
证明：universal solenoid 中两个点路径连通，当且仅当它们位于同一实流轨道。该结论分类路径分支，但本身没有定义评价表、扭曲或量子状态表示。

### 2.4 Zeta/Li/Weil 基础

本文后半部分使用仓库中已存在的三类接口：

- `D5/S3/Analytic/LiCausalTrichotomy`：Cayley 坐标、整数 Li symbol 与一侧 Laguerre 因果包；
- `D5/S3/Weil/ZeroSum`：不预设 RH 的非平凡零点数据、反射/共轭对称与对称截断零点和；
- `D5/S3/Weil/WeilIdentity`：通过登记的经典 Weil 显式公式输入，连接零点端、素数端、极点端与 Archimedean 端；该输入不含 Weil 正性或 RH。

---

## 3. 对角系统与观察投影

### 定义 3.1（评价表与输出空间）

给定地址集 \(A\) 与值集 \(Y\)，定义
\[
\mathcal T(A,Y)=Y^{A\times A},
\qquad
\mathcal U(A,Y)=Y^A.
\]

元素 \(E\in\mathcal T(A,Y)\) 称为评价表。其第一个坐标可以理解为候选/命名者，第二个坐标可以理解为被评价地址。

### 定义 3.2（对角读取）

定义
\[
D_A:\mathcal T(A,Y)\to\mathcal U(A,Y),
\qquad
D_A(E)(a)=E(a,a).
\]

### 定义 3.3（值扭曲与扭曲对角）

给定 \(\tau:Y\to Y\)，定义逐点扭曲
\[
\Theta_\tau:\mathcal U(A,Y)\to\mathcal U(A,Y),
\qquad
\Theta_\tau(u)=\tau\circ u,
\]
以及扭曲对角算子
\[
\Delta_{A,Y,\tau}
=
\Theta_\tau\circ D_A.
\]
因此
\[
\Delta(E)(a)=\tau(E(a,a)).
\]

当 \(\tau\) 无不动点时，\(\Delta(E)\) 不可能等于任何一行 \(E(a,-)\)。一般 \(\tau\) 有不动点时，是否逃逸成为定量计数问题。

### 定义 3.4（多尺度对角系统）

令 \(I\) 为预序。对每个尺度 \(i\in I\)，给定：

\[
A_i,\quad Y_i,\quad \tau_i:Y_i\to Y_i,
\]
\[
\mathcal T_i=Y_i^{A_i\times A_i},
\qquad
\mathcal U_i=Y_i^{A_i},
\]
\[
D_i:\mathcal T_i\to\mathcal U_i,
\qquad
\Theta_i:\mathcal U_i\to\mathcal U_i,
\qquad
\Delta_i=\Theta_iD_i.
\]

对每个 \(j\succeq i\)，给定表投影与输出投影
\[
P_{j,i}:\mathcal T_j\to\mathcal T_i,
\qquad
Q_{j,i}:\mathcal U_j\to\mathcal U_i,
\]
并要求
\[
P_{i,i}=\mathrm{id},
\qquad
P_{k,i}=P_{j,i}P_{k,j},
\]
\[
Q_{i,i}=\mathrm{id},
\qquad
Q_{k,i}=Q_{j,i}Q_{k,j}
\]
对 \(k\succeq j\succeq i\) 成立。

这里必须保留 \(P\) 与 \(Q\) 两类映射。评价表投影可能使用两个地址坐标；对角输出投影只作用于一个地址坐标。把二者写成同一个模糊“观察映射”会掩盖对角读取是否被保持这一核心问题。

### 定义 3.5（对角投影缺陷）

设每个 \(\mathcal U_i\) 配备伪度量 \(d_i\)。定义
\[
\varepsilon^\Delta_{j,i}(E)
=
d_i\!\left(
Q_{j,i}\Delta_j(E),
\Delta_iP_{j,i}(E)
\right).
\]

如果 \(d_i\) 是扩展度量，允许缺陷为 \(+\infty\)。如果使用 KL 等非对称散度，则后续只保留其实际满足的性质，不能直接调用对称性或三角不等式。

### 定义 3.6（读取缺陷与扭曲缺陷）

定义
\[
\varepsilon^D_{j,i}(E)
=
d_i\!\left(
Q_{j,i}D_j(E),
D_iP_{j,i}(E)
\right),
\]
以及对 \(u\in\mathcal U_j\)
\[
\varepsilon^\tau_{j,i}(u)
=
d_i\!\left(
Q_{j,i}\Theta_j(u),
\Theta_iQ_{j,i}(u)
\right).
\]

---

## 4. 缺陷分解与尺度复合

### 定理 4.1（总缺陷分解）

假设 \(d_i\) 满足三角不等式，且 \(\Theta_i\) 关于 \(d_i\) 是 \(L_i\)-Lipschitz，即
\[
d_i(\Theta_i x,\Theta_i y)
\le
L_i d_i(x,y).
\]
则对任意 \(E\in\mathcal T_j\)，
\[
\boxed{
\varepsilon^\Delta_{j,i}(E)
\le
\varepsilon^\tau_{j,i}(D_jE)
+
L_i\varepsilon^D_{j,i}(E).
}
\]

#### 证明

由 \(\Delta_j=\Theta_jD_j\) 与 \(\Delta_i=\Theta_iD_i\)，
\[
\varepsilon^\Delta_{j,i}(E)
=
d_i\!\left(
Q_{j,i}\Theta_jD_jE,
\Theta_iD_iP_{j,i}E
\right).
\]
在两端之间插入 \(\Theta_iQ_{j,i}D_jE\)，由三角不等式，
\[
\begin{aligned}
\varepsilon^\Delta_{j,i}(E)
&\le
d_i\!\left(
Q_{j,i}\Theta_jD_jE,
\Theta_iQ_{j,i}D_jE
\right)\\
&\quad+
d_i\!\left(
\Theta_iQ_{j,i}D_jE,
\Theta_iD_iP_{j,i}E
\right).
\end{aligned}
\]
第一项按定义等于
\[
\varepsilon^\tau_{j,i}(D_jE).
\]
第二项由 \(\Theta_i\) 的 Lipschitz 性至多为
\[
L_i
d_i\!\left(
Q_{j,i}D_jE,
D_iP_{j,i}E
\right)
=
L_i\varepsilon^D_{j,i}(E).
\]
合并即得。 \(\square\)

### 推论 4.2（严格自然性判据）

若
\[
Q_{j,i}D_j=D_iP_{j,i}
\]
且
\[
Q_{j,i}\Theta_j=\Theta_iQ_{j,i},
\]
则
\[
Q_{j,i}\Delta_j=\Delta_iP_{j,i}.
\]

#### 证明

两项缺陷同时为零，定理 4.1 给出总缺陷为零。若 \(d_i\) 是分离的度量，则两函数相等。也可直接作算子复合：
\[
Q\Delta
=
Q\Theta_jD_j
=
\Theta_iQD_j
=
\Theta_iD_iP
=
\Delta_iP.
\]
\(\square\)

### 定理 4.3（尺度复合不等式）

设 \(k\preceq i\preceq j\)，且 \(Q_{i,k}\) 是 \(L^Q_{i,k}\)-Lipschitz。则
\[
\boxed{
\varepsilon^\Delta_{j,k}(E)
\le
L^Q_{i,k}\varepsilon^\Delta_{j,i}(E)
+
\varepsilon^\Delta_{i,k}(P_{j,i}E).
}
\]

#### 证明

利用投影复合律，
\[
Q_{j,k}=Q_{i,k}Q_{j,i},
\qquad
P_{j,k}=P_{i,k}P_{j,i}.
\]
在
\[
Q_{i,k}Q_{j,i}\Delta_jE
\]
与
\[
\Delta_kP_{i,k}P_{j,i}E
\]
之间插入
\[
Q_{i,k}\Delta_iP_{j,i}E.
\]
由三角不等式，
\[
\begin{aligned}
\varepsilon^\Delta_{j,k}(E)
&\le
d_k\!\left(
Q_{i,k}Q_{j,i}\Delta_jE,
Q_{i,k}\Delta_iP_{j,i}E
\right)\\
&\quad+
d_k\!\left(
Q_{i,k}\Delta_iP_{j,i}E,
\Delta_kP_{i,k}P_{j,i}E
\right).
\end{aligned}
\]
第一项由 \(Q_{i,k}\) 的 Lipschitz 性至多为
\[
L^Q_{i,k}\varepsilon^\Delta_{j,i}(E),
\]
第二项正是
\[
\varepsilon^\Delta_{i,k}(P_{j,i}E).
\]
故结论成立。 \(\square\)

### 推论 4.4（加权 telescoping bound）

对尺度链
\[
i_m\succeq i_{m-1}\succeq\cdots\succeq i_0,
\]
设 \(Q_{i_r,i_{r-1}}\) 的 Lipschitz 常数为 \(L_r\)。则
\[
\boxed{
\varepsilon^\Delta_{i_m,i_0}(E)
\le
\sum_{r=1}^{m}
\left(
\prod_{s=1}^{r-1}L_s
\right)
\varepsilon^\Delta_{i_r,i_{r-1}}
\!\left(
P_{i_m,i_r}E
\right).
}
\]

#### 证明

对 \(m\) 归纳。\(m=1\) 时为恒等式。归纳步先对中间尺度 \(i_1\) 使用定理 4.3，再对
\(
\varepsilon^\Delta_{i_m,i_1}(E)
\)
应用归纳假设，并乘上 \(L_1\)。整理指标即得。 \(\square\)

这个推论将“观察者逐层压缩”变成了可审计的误差账本：整体缺陷由每一层真正产生的局部缺陷控制，而不是由“观察”这个词自动产生。

---

## 5. 限制观察严格自然，商聚合可以破坏自然性

### 定理 5.1（坐标限制自然性）

设 \(\iota:A_i\hookrightarrow A_j\) 为地址嵌入，\(q:Y_j\to Y_i\) 为值映射。定义
\[
P_{j,i}(E)(a,b)
=
q(E(\iota a,\iota b)),
\]
\[
Q_{j,i}(u)(a)
=
q(u(\iota a)).
\]
若
\[
q\circ\tau_j=\tau_i\circ q,
\]
则
\[
\boxed{
Q_{j,i}\Delta_j
=
\Delta_iP_{j,i}.
}
\]

#### 证明

对任意 \(E\in\mathcal T_j\) 与 \(a\in A_i\)，
\[
\begin{aligned}
Q_{j,i}\Delta_j(E)(a)
&=
q\!\left(
\Delta_j(E)(\iota a)
\right)\\
&=
q\!\left(
\tau_j(E(\iota a,\iota a))
\right)\\
&=
\tau_i\!\left(
q(E(\iota a,\iota a))
\right)\\
&=
\tau_i\!\left(
P_{j,i}(E)(a,a)
\right)\\
&=
\Delta_iP_{j,i}(E)(a).
\end{aligned}
\]
逐点相等即得。 \(\square\)

### 解释 5.2

有限观察本身不会必然制造对角缺陷。若观察只是保留原系统中的一组坐标，且值扭曲与读取映射自然交换，则“先整体自指再观察”与“先观察再自指”严格相同。

因此任何把缺陷归因于观察者的理论，都必须明确指出至少一个非自然结构：

- 地址被识别或合并；
- 非对角信息被聚合进粗层自坐标；
- 值扭曲与粗粒化不交换；
- 使用的代价只识别商类而不识别函数本身。

### 命题 5.3（最小读取反例）

令细地址集 \(A_f=\{0,1\}\)，粗地址集 \(A_c=\{*\}\)，值集 \(Y=\{0,1\}\)。在布尔值上使用离散度量。定义
\[
P(E)=\bigvee_{a,b\in A_f}E(a,b),
\qquad
Q(u)=\bigvee_{a\in A_f}u(a).
\]
取评价表
\[
E(0,0)=0,\quad E(1,1)=0,\quad
E(0,1)=1,\quad E(1,0)=0.
\]
则
\[
Q(D_fE)=0,
\qquad
D_c(P(E))=1.
\]
因此
\[
\boxed{
\varepsilon^D_{f,c}(E)=1.
}
\]

#### 证明

细层对角为 \((0,0)\)，其 OR 为 \(0\)。而全表包含非对角元 \(E(0,1)=1\)，故表聚合 \(P(E)=1\)。粗层只有一个坐标，所以其对角读取仍为 \(1\)。离散距离因此为 \(1\)。 \(\square\)

### 命题 5.4（最小扭曲反例）

仍令
\[
Q(u_0,u_1)=u_0\lor u_1,
\]
并令细层和粗层扭曲都为布尔取反。对
\[
u=(0,1)
\]
有
\[
Q(\neg u)=Q(1,0)=1,
\]
但
\[
\neg Q(u)=\neg1=0.
\]
故
\[
\boxed{
\varepsilon^\tau_{f,c}(u)=1.
}
\]

这两个反例分别隔离了读取失配与扭曲失配。它们说明商映射 \(A_f\twoheadrightarrow A_c\) 本身不足以决定表投影；选择 OR、平均、最大值、条件期望或代表元都会引入额外数学结构。

---

## 6. 对角算子下降到逆极限的充要结构

设
\[
(\mathcal T_i,P_{j,i}),
\qquad
(\mathcal U_i,Q_{j,i})
\]
为集合范畴中的逆系。记
\[
\mathcal T_\infty=\varprojlim_i\mathcal T_i,
\qquad
\mathcal U_\infty=\varprojlim_i\mathcal U_i,
\]
其坐标投影分别为
\[
\pi_i^\mathcal T:\mathcal T_\infty\to\mathcal T_i,
\qquad
\pi_i^\mathcal U:\mathcal U_\infty\to\mathcal U_i.
\]

### 定理 6.1（严格自然族的唯一下降）

若
\[
Q_{j,i}\Delta_j=\Delta_iP_{j,i}
\]
对所有 \(j\succeq i\) 成立，则存在唯一映射
\[
\boxed{
\Delta_\infty:
\mathcal T_\infty\to\mathcal U_\infty
}
\]
满足
\[
\pi_i^\mathcal U\Delta_\infty
=
\Delta_i\pi_i^\mathcal T
\]
对所有 \(i\) 成立。

#### 证明

取任意相容族
\[
E=(E_i)_i\in\mathcal T_\infty.
\]
定义
\[
\Delta_\infty(E)
=
(\Delta_i(E_i))_i.
\]
需要验证右侧属于 \(\mathcal U_\infty\)。对 \(j\succeq i\)，
\[
Q_{j,i}\Delta_j(E_j)
=
\Delta_iP_{j,i}(E_j)
=
\Delta_i(E_i),
\]
其中最后一步使用 \(E\) 的相容性。因此
\((\Delta_i(E_i))_i\)
是相容族，定义良好。坐标等式由定义立即成立。

若 \(\widetilde\Delta_\infty\) 也满足全部坐标等式，则对每个 \(E\) 与每个 \(i\)，
\[
\pi_i^\mathcal U\widetilde\Delta_\infty(E)
=
\Delta_i(E_i)
=
\pi_i^\mathcal U\Delta_\infty(E).
\]
逆极限中的元素由全部坐标唯一决定，故两映射相等。 \(\square\)

### 定理 6.2（满射坐标下的反向判据）

假设每个
\[
\pi_j^\mathcal T:\mathcal T_\infty\to\mathcal T_j
\]
均为满射。若存在映射
\[
\Delta_\infty:\mathcal T_\infty\to\mathcal U_\infty
\]
满足
\[
\pi_i^\mathcal U\Delta_\infty
=
\Delta_i\pi_i^\mathcal T
\]
对所有 \(i\) 成立，则有限层严格自然：
\[
\boxed{
Q_{j,i}\Delta_j
=
\Delta_iP_{j,i}.
}
\]

#### 证明

固定 \(j\succeq i\) 与任意 \(E_j\in\mathcal T_j\)。由 \(\pi_j^\mathcal T\) 满射，存在
\[
E_\infty\in\mathcal T_\infty
\]
使
\[
\pi_j^\mathcal T(E_\infty)=E_j.
\]
于是
\[
\begin{aligned}
Q_{j,i}\Delta_j(E_j)
&=
Q_{j,i}\Delta_j\pi_j^\mathcal T(E_\infty)\\
&=
Q_{j,i}\pi_j^\mathcal U\Delta_\infty(E_\infty)\\
&=
\pi_i^\mathcal U\Delta_\infty(E_\infty)\\
&=
\Delta_i\pi_i^\mathcal T(E_\infty)\\
&=
\Delta_iP_{j,i}\pi_j^\mathcal T(E_\infty)\\
&=
\Delta_iP_{j,i}(E_j).
\end{aligned}
\]
因 \(E_j\) 任意，算子相等。 \(\square\)

### 推论 6.3（缺陷的障碍意义）

在坐标投影满射的逆系中，下列两件事等价：

1. 有限层对角算子严格自然；
2. 存在唯一按坐标实现全部 \(\Delta_i\) 的极限对角算子。

因此非零对角投影缺陷不是“无限对象中的神秘误差”，而是有限层算子不能下降到 projective completion 的精确证书。

若坐标投影不满射，则只需在可提升到极限的评价表上验证自然性。一个不可提升的孤立有限反例，不足以否定极限空间上的坐标算子。

---

## 7. 欧几里得素数构造：有限账本逃逸，而非自动的自应用对角化

### 定义 7.1（素数账本逃逸数）

设 \(S\) 为有限素数集合，定义
\[
P_S=\prod_{p\in S}p,
\qquad
N_S=P_S+1.
\]
空积取 \(1\)。

### 定理 7.2（同时整除逃逸）

对每个 \(p\in S\)，
\[
N_S\equiv1\pmod p.
\]
因此
\[
p\nmid N_S.
\]

#### 证明

因 \(p\mid P_S\)，有
\[
P_S\equiv0\pmod p.
\]
两边加一即得
\[
N_S\equiv1\pmod p.
\]
故 \(p\) 不整除 \(N_S\)。 \(\square\)

### 定理 7.3（新素因子提取）

若 \(q\) 是 \(N_S\) 的任一素因子，则
\[
\boxed{
q\notin S.
}
\]

#### 证明

反设 \(q\in S\)。则 \(q\mid P_S\)。又因 \(q\mid N_S=P_S+1\)，所以
\[
q\mid (P_S+1)-P_S=1,
\]
这与 \(q\) 为素数矛盾。 \(\square\)

### 推论 7.4（严格增长的素数账本）

固定一个素因子选择函数，例如最小素因子：
\[
\delta_{\mathbb P}(S)
=
\operatorname{minFac}(N_S).
\]
定义
\[
S_{n+1}
=
S_n\cup\{\delta_{\mathbb P}(S_n)\}.
\]
则
\[
|S_{n+1}|=|S_n|+1,
\]
因而得到无限多个互不相同的素数。

### 命题 7.5（剩余坐标解释）

设 \(S\neq\varnothing\)。定义有限剩余坐标空间
\[
R_S=\prod_{p\in S}\mathbb Z/p\mathbb Z
\]
与剩余映射
\[
r_S:\mathbb Z\to R_S.
\]
则
\[
r_S(P_S)=0,
\qquad
r_S(N_S)=\mathbf1.
\]
所以 \(+1\) 把“被全部已有素数整除”的零向量同时移动到每个坐标上的 \(1\)。

### 结构边界 7.6

欧几里得构造与表对角化共享“针对有限名单逐坐标逃逸”的结构，但两者不是同一个算子：

- 表对角化包含自应用读取 \(E(a,a)\)；
- 欧几里得构造没有候选评价自身的二维表；
- 素数来自对逃逸整数再次作不可约分解，而不是来自取反本身。

因此最准确的表述是
\[
\boxed{
\text{有限账本逃逸}
+
\text{因子分解}
=
\text{新素数见证}.
}
\]
若要把它实现为一般 \(\Delta=\Theta D\) 的严格实例，必须额外构造一个依赖于素数坐标的评价表编码与解码交换图。

---

## 8. Li–Cayley 坐标中的零点几何

本节只讨论经典完成 zeta/xi 函数的非平凡零点几何。设
\[
s=\beta+i\gamma,
\qquad
s\neq0.
\]

### 定义 8.1（Li–Cayley 坐标）

定义
\[
\boxed{
C(s)=1-\frac1s=\frac{s-1}{s}.
}
\]

### 定理 8.2（临界线—单位圆等价）

有恒等式
\[
\boxed{
|C(s)|^2-1
=
\frac{1-2\beta}{\beta^2+\gamma^2}.
}
\]
从而
\[
\boxed{
\Re s=\frac12
\iff
|C(s)|=1.
}
\]
并且
\[
\Re s>\frac12
\iff
|C(s)|<1,
\]
\[
\Re s<\frac12
\iff
|C(s)|>1.
\]

#### 证明

直接计算：
\[
|C(s)|^2
=
\frac{|s-1|^2}{|s|^2}
=
\frac{(\beta-1)^2+\gamma^2}{\beta^2+\gamma^2}.
\]
减去 \(1\) 得
\[
\frac{(\beta-1)^2-\beta^2}{\beta^2+\gamma^2}
=
\frac{1-2\beta}{\beta^2+\gamma^2}.
\]
分母严格为正，故符号只由 \(1-2\beta\) 决定。 \(\square\)

这一恒等式给出一个严格坐标解释：临界线是 \(0\) 与 \(1\) 的等距垂直平分线，而 \(C\) 把这条线送到单位圆。

### 定理 8.3（反射与共轭）

对 \(s\neq0,1\)，
\[
\boxed{
C(1-s)=C(s)^{-1}.
}
\]
同时
\[
\boxed{
C(\overline s)=\overline{C(s)},
}
\]
因此
\[
\boxed{
C(1-\overline s)=\overline{C(s)}^{-1}.
}
\]

#### 证明

第一式：
\[
C(1-s)
=
1-\frac1{1-s}
=
\frac{-s}{1-s}
=
\frac{s}{s-1}
=
\frac1{C(s)}.
\]
第二式由复共轭与加减乘除交换立即成立。第三式由前两式复合得到。 \(\square\)

因此函数方程反射
\[
s\mapsto1-\overline s
\]
在 \(C\)-平面中变成反演
\[
z\mapsto\frac1{\overline z},
\]
其不动点恰是单位圆。

### 定义 8.4（第 \(n\) 阶 Li 探针）

对 \(n\ge1\)，定义
\[
A_n(s)
=
1-C(s)^n.
\]

仓库 `LiCausalTrichotomy` 中的 `liSymbol` 使用相反号
\[
C(s)^n-1=-A_n(s)
\]
的规范；二者只差整体负号，但在对接既有声明时必须保持规范显式。

### 定理 8.5（镜像乘积恒等式）

对 \(s\neq0,1\)，
\[
\boxed{
A_n(s)+A_n(1-s)
=
A_n(s)A_n(1-s).
}
\]

#### 证明

令 \(z=C(s)\)。由定理 8.3，
\[
C(1-s)=z^{-1}.
\]
于是
\[
A_n(s)+A_n(1-s)
=
(1-z^n)+(1-z^{-n})
=
2-z^n-z^{-n},
\]
而
\[
A_n(s)A_n(1-s)
=
(1-z^n)(1-z^{-n})
=
2-z^n-z^{-n}.
\]
故二者相等。 \(\square\)

### 推论 8.6（临界线上的模平方坍缩）

若
\[
\Re s=\frac12,
\]
则
\[
1-s=\overline s,
\]
并且
\[
A_n(1-s)=\overline{A_n(s)}.
\]
因此
\[
\boxed{
2\Re A_n(s)
=
|A_n(s)|^2
\ge0.
}
\]

#### 证明

临界线条件给出 \(1-s=\overline s\)。由定理 8.3，
\[
A_n(\overline s)=\overline{A_n(s)}.
\]
代入定理 8.5 即得
\[
A_n(s)+\overline{A_n(s)}
=
A_n(s)\overline{A_n(s)}.
\]
左边是 \(2\Re A_n(s)\)，右边是 \(|A_n(s)|^2\)。 \(\square\)

这解释了临界线零点对在 Li/Weil 正性中出现平方结构的局部来源：倒数镜像在单位圆上退化为复共轭。

### 定理 8.7（零点四元轨道贡献）

设
\[
z=C(\rho)=re^{i\theta},
\qquad r>0.
\]
考虑形式四元轨道
\[
\rho,\quad\overline\rho,\quad1-\rho,\quad1-\overline\rho.
\]
其第 \(n\) 阶 Li 探针总贡献为
\[
\boxed{
L_n(\rho)
=
4-2(r^n+r^{-n})\cos(n\theta).
}
\]

#### 证明

四个 Cayley 坐标分别为
\[
z,\quad\overline z,\quad z^{-1},\quad\overline z^{-1}.
\]
因此
\[
\begin{aligned}
L_n(\rho)
&=
4-
\left(
z^n+\overline z^n+z^{-n}+\overline z^{-n}
\right)\\
&=
4-
2r^n\cos(n\theta)
-
2r^{-n}\cos(n\theta),
\end{aligned}
\]
即所述公式。 \(\square\)

若 \(r=1\)，则
\[
L_n(\rho)
=
4-4\cos(n\theta)
=
8\sin^2\!\left(\frac{n\theta}{2}\right)
\ge0.
\]

### 引理 8.8（相位复现）

对任意 \(\theta\in\mathbb R\)，存在严格递增整数序列
\[
n_k\to\infty
\]
使
\[
e^{in_k\theta}\to1,
\qquad
\cos(n_k\theta)\to1.
\]

#### 证明

令
\[
\alpha=\frac{\theta}{2\pi}.
\]
若 \(\alpha\in\mathbb Q\)，取其分母的正整数倍即可使
\[
n_k\alpha\in\mathbb Z.
\]

若 \(\alpha\notin\mathbb Q\)，由 Dirichlet 有理逼近，对每个 \(N\) 存在
\[
1\le q_N\le N
\]
使
\[
\|q_N\alpha\|_{\mathbb R/\mathbb Z}\le\frac1N.
\]
若 \(q_N\) 没有无界子序列，则有某个固定正整数 \(q\) 在无穷多个 \(N\) 上出现，从而
\[
\|q\alpha\|_{\mathbb R/\mathbb Z}=0,
\]
这与 \(\alpha\) 无理矛盾。因此可取 \(q_{N_k}\to\infty\)。令
\[
n_k=q_{N_k},
\]
则 \(n_k\alpha\) 到整数的距离趋于零，故
\[
e^{2\pi i n_k\alpha}=e^{in_k\theta}\to1.
\]
\(\square\)

### 定理 8.9（离线四元轨道的局部指数暴露）

若
\[
|C(\rho)|=r\neq1,
\]
则存在整数子序列 \(n_k\to\infty\)，使
\[
\boxed{
L_{n_k}(\rho)\to-\infty.
}
\]

#### 证明

由引理 8.8，取 \(n_k\) 使
\[
\cos(n_k\theta)\to1.
\]
故对充分大的 \(k\)，
\[
\cos(n_k\theta)\ge\frac12.
\]
又因 \(r\neq1\)，
\[
r^{n_k}+r^{-n_k}\to\infty.
\]
由定理 8.7，
\[
L_{n_k}(\rho)
=
4-2(r^{n_k}+r^{-n_k})\cos(n_k\theta)
\le
4-(r^{n_k}+r^{-n_k}),
\]
右侧趋于 \(-\infty\)。 \(\square\)

这个定理是局部的：它只说明一个离线零点轨道能够被某个整数阶探针指数放大。它没有控制其他所有零点的总贡献，也没有自动证明某个完整 Li 系数为负。

---

## 9. Li 判据中的真正对角问题：探针阶数与完成截断能否同时取极限

### 9.1 经典 Li 判据

对完成 zeta/xi 函数的非平凡零点，Li 系数按对称规范写作
\[
\lambda_n
=
\sum_\rho
\left[
1-\left(1-\frac1\rho\right)^n
\right].
\]
Li 定理及 Bombieri–Lagarias 推广给出经典等价：
\[
\boxed{
\mathrm{RH}
\iff
\lambda_n\ge0
\quad
\text{对全部 }n\ge1.
}
\]

本文不重新证明这一经典判据。本文新增的是：把有限零点截断与随截断增长的探针阶数区分开，并证明固定阶收敛不足以支持“对角选择”。

### 定义 9.1（Li 截断与完成缺陷）

令
\[
\lambda_{n,T}
=
\sum_{\rho\in Z_T}
\left[
1-C(\rho)^n
\right],
\]
其中 \(Z_T\) 是关于反射与共轭封闭的有限对称零点截断。若固定 \(n\) 时
\[
\lambda_{n,T}\to\lambda_n,
\]
定义
\[
\varepsilon^{\mathrm{Li}}_{n,T}
=
|\lambda_n-\lambda_{n,T}|.
\]

仓库 `ZeroSum` 已经提供一般 Weil 测试函数下的对称有限截断框架，但把 Li 探针直接纳入现有 `WeilTestFunction` 仍需处理测试函数类差异：当前 Weil bundle 要求偶、光滑、紧支撑；一侧 Laguerre Li 包并非紧支撑且并非偶函数。

### 定理 9.2（统一控制允许对角取极限）

设 \((X,d)\) 为度量空间，\(x_{n,T},x_n\in X\)。设 \(n(T)\) 为任意整数选择。若存在集合 \(N_T\subseteq\mathbb N\) 满足
\[
n(T)\in N_T
\]
且
\[
\sup_{n\in N_T}d(x_{n,T},x_n)\to0,
\]
则
\[
\boxed{
d(x_{n(T),T},x_{n(T)})\to0.
}
\]

#### 证明

对每个 \(T\)，
\[
d(x_{n(T),T},x_{n(T)})
\le
\sup_{n\in N_T}d(x_{n,T},x_n).
\]
右侧趋于零，结论成立。 \(\square\)

### 命题 9.3（逐点收敛不足以支持对角选择）

存在实数阵列 \(x_{n,T}\) 与极限 \(x_n\)，使对每个固定 \(n\)，
\[
x_{n,T}\to x_n,
\]
但存在 \(n(T)\to\infty\) 满足
\[
|x_{n(T),T}-x_{n(T)}|=1
\]
对全部 \(T\) 成立。

#### 证明

定义
\[
x_n=0,
\qquad
x_{n,T}
=
\begin{cases}
0,&n\le T,\\
1,&n>T.
\end{cases}
\]
固定 \(n\) 后，当 \(T\ge n\) 时 \(x_{n,T}=0=x_n\)，故逐点收敛成立。但取
\[
n(T)=T+1,
\]
则
\[
x_{n(T),T}=1,
\qquad
x_{n(T)}=0.
\]
故误差恒为 \(1\)。 \(\square\)

### 推论 9.4（有限 Li 验证的逻辑边界）

即使对每个固定 \(n\) 都已证明
\[
\lambda_{n,T}\to\lambda_n,
\]
也不能仅由此推出
\[
\lambda_{n(T),T}-\lambda_{n(T)}\to0
\]
对增长阶数 \(n(T)\) 成立。任何利用高阶 Li 探针暴露高位离线零点的论证，都必须给出与 \(n\) 联合的截断余项估计。

### 定理 9.5（离线轨道的全局支配条件）

固定一个离线四元轨道 \(\mathcal O_\rho\)，记其贡献为 \(L_n(\rho)\)。在反射与共轭对称的求和规范下，\(\lambda_n\) 与 \(L_n(\rho)\) 均为实数；把其余零点贡献记为
\[
R_n
=
\lambda_n-L_n(\rho)
\in\mathbb R.
\]
若存在由定理 8.9 得到的子序列 \(n_k\)，满足
\[
\frac{|R_{n_k}|}
{r^{n_k}+r^{-n_k}}
\longrightarrow0,
\]
则
\[
\boxed{
\lambda_{n_k}<0
}
\]
对充分大的 \(k\) 成立。

#### 证明

沿该子序列，
\[
\cos(n_k\theta)\to1,
\]
所以
\[
\frac{L_{n_k}(\rho)}
{r^{n_k}+r^{-n_k}}
=
\frac4{r^{n_k}+r^{-n_k}}
-
2\cos(n_k\theta)
\longrightarrow-2.
\]
而假设给出
\[
\frac{R_{n_k}}
{r^{n_k}+r^{-n_k}}
\longrightarrow0.
\]
因此
\[
\frac{\lambda_{n_k}}
{r^{n_k}+r^{-n_k}}
\longrightarrow-2,
\]
最终必为负。 \(\square\)

定理 9.5 精确定位了从“局部离线零点可被指数放大”到“完整 Li 系数出现负值”的缺口：必须控制其余全部零点、正则化顺序或等价的素数端余项。这个缺口与 RH 本身同等关键，不能被“对角化”一词绕过。

---

## 10. 素数端、零点端与显式公式

素数账本逃逸与 Li 零点探针通过显式公式处于同一研究图中，但两者承担不同角色：

\[
\text{有限素数/素数幂账本}
\longleftrightarrow
\text{测试函数}
\longleftrightarrow
\text{零点谱}.
\]

在仓库当前约定下，`WeilIdentity` 给出
\[
\operatorname{zeroSum}
=
\operatorname{poleTerm}
-
\operatorname{primeTerm}
+
\operatorname{archimedeanTerm},
\]
其经典等式来自登记的 `weil_explicit_formula_classic` 外部输入。该输入没有断言正性，也没有断言 RH。

因此一条真正闭合的 RH 证明链必须至少包含：

1. 合法测试函数类中的 Li/Weil 探针；
2. 零点端 Li 系数或等价二次型；
3. 素数端与 Archimedean 端的精确表达；
4. 对全部探针阶数成立的非负性；
5. 截断、极限与正则化顺序的联合控制。

本文完成的是零点端的局部 Li–Cayley 几何，以及第 5 项中“逐点收敛不允许对角选阶”的一般逻辑定理。本文没有把 Li 包纳入现有紧支撑 Weil 测试类，也没有完成第 3 项的全新内部推导或第 4 项的全阶正性。

---

## 11. 观察者与量子解释的严格边界

### 11.1 观察者效应不是自动缺陷

定理 5.1 表明：若观察只是坐标限制，且扭曲自然，则对角缺陷严格为零。因此“有限观察者”不会仅因有限而改变自指结构。

真正产生缺陷的是具体的非自然机制，例如：

- 多个微观地址被合并；
- 非对角相关被聚合到粗层自坐标；
- 扭曲与条件期望、阈值、OR、最大化等非线性操作不交换；
- 观测代价只在商空间中分离状态。

### 11.2 对角缺陷不等于量子上下文性

量子上下文性通常研究局部测量上下文能否拼接成全局非上下文赋值。对角缺陷研究
\[
Q\Delta
\quad\text{与}\quad
\Delta P
\]
是否相等。二者可以在某个具体模型中建立映射，但在给出双向定理以前不能视为同一概念。

### 11.3 有限观察者距离可作为 \(d_i\)，但不自动给出跨尺度系统

`WindowObserverDistance` 为单个有限循环窗口提供自然度量。要把它用于本文的 \(d_i\)，还必须给出不同窗口之间的 \(P_{j,i},Q_{j,i}\) 并验证 Lipschitz 常数。单窗口精确距离并不自动形成逆系。

### 11.4 Solenoid 提供完成载体，不自动提供量子态空间

solenoid 的路径分支分类适合作为 projective completion 的具体几何载体。但要应用定理 6.1，仍必须构造：

- 有限层评价表；
- 表投影与输出投影；
- 有限层扭曲；
- 与 solenoid bonding maps 相容的自然性证明。

在这些对象出现以前，“隐藏核”“量子地址”与“对角完成”只是潜在适配，不是已证同一性。

---

## 12. 主要结论

本文得到以下闭合结论。

### 结论 A：对角化的局部—整体失配有两个独立来源

\[
\boxed{
\varepsilon^\Delta
\le
\varepsilon^\tau
+
L\varepsilon^D.
}
\]

因此对角缺陷不是一个不可分析的整体误差；它由自坐标读取失配与值扭曲失配组成。

### 结论 B：缺陷可以沿观察尺度精确记账

\[
\boxed{
\varepsilon^\Delta_{j,k}
\le
L^Q_{i,k}\varepsilon^\Delta_{j,i}
+
\varepsilon^\Delta_{i,k}\circ P_{j,i}.
}
\]

### 结论 C：严格自然性正是极限对角算子存在的条件

在坐标投影满射的逆系中，
\[
\boxed{
\text{有限层严格自然}
\iff
\text{存在坐标兼容的极限对角算子}.
}
\]

### 结论 D：素数来自账本逃逸后的不可约提取

\[
\boxed{
S
\longmapsto
1+\prod_{p\in S}p
\longmapsto
q\notin S.
}
\]
这是一种有限坐标逃逸，但不是无需编码即可等同的自应用表对角化。

### 结论 E：RH 在 Li–Cayley 坐标中是单位圆饱和

\[
\boxed{
\Re\rho=\frac12
\iff
\left|1-\frac1\rho\right|=1.
}
\]
临界线轨道产生模平方非负贡献；离线轨道则沿某个整数阶子序列产生局部负无穷放大。

### 结论 F：局部可探测不等于全局已排除

固定阶截断收敛不允许阶数随截断任意增长。要从离线轨道的局部暴露推出完整 Li 系数为负，必须控制其他零点或素数端余项。这个联合控制是 RH 路线中的实质问题。

---

## 13. 形式化状态说明

本文的下列输入已经存在 Lean 证明：

- 有限逃逸计数、捕获乘积律、距离剖面与浓缩；
- 有限循环窗口观察者距离；
- solenoid 路径轨道分类；
- 临界线上的 Cayley 单位模；
- 整数 Li symbol 的因果包；
- 零点反射/共轭对称截断；
- 通过登记经典输入得到的 Weil 显式公式。

本文新增并已在纸面完整证明、但尚未声明为 Lean 真源的结果是：

- 总缺陷分解定理；
- 尺度复合与 telescoping bound；
- 限制自然性定理；
- 两个最小布尔反例；
- 逆极限下降与满射反向判据；
- 素数账本逃逸的本文类型化表述；
- Li–Cayley 镜像乘积、四元轨道公式与局部指数暴露；
- 统一对角取极限定理、逐点反例与全局支配条件。

在这些声明被形式化以前，本文应作为论文稿与理论来源读取，而不应被 Blueprint 或 frozen ledger 自动投影成 `Closed`。

---

## 参考文献

1. G. Cantor, “Über eine elementare Frage der Mannigfaltigkeitslehre,” *Jahresbericht der Deutschen Mathematiker-Vereinigung* 1 (1891), 75–78.
2. F. W. Lawvere, “Diagonal Arguments and Cartesian Closed Categories,” in *Category Theory, Homology Theory and their Applications II*, Lecture Notes in Mathematics 92, Springer, 1969, 134–145.
3. Euclid, *Elements*, Book IX, Proposition 20.
4. X.-J. Li, “The Positivity of a Sequence of Numbers and the Riemann Hypothesis,” *Journal of Number Theory* 65 (1997), 325–333. DOI: 10.1006/jnth.1997.2137.
5. E. Bombieri and J. C. Lagarias, “Complements to Li’s Criterion for the Riemann Hypothesis,” *Journal of Number Theory* 77 (1999), 274–287. DOI: 10.1006/jnth.1999.2392.
6. A. Weil, “Sur les ‘formules explicites’ de la théorie des nombres premiers,” *Communications du Séminaire Mathématique de l’Université de Lund*, supplément (1952), 252–265.

---

## 附录 A　对合、商余与界面：连续结构如何产生离散极性

本附录把“取反是一种商余结构”收紧为一个可证明的命题。精确结论不是“取反等于取商”，而是：

\[
\boxed{
\text{对合型取反是在轨道商的纤维内交换两点；}
\quad
\text{离散极性是相对于一个截面或界面所选出的纤维坐标。}
}
\]

这里的“商”是对合轨道的等价类；“余”不是欧几里得除法中的算术余数，而是选定命名截面以后剩下的 \(\mathbb Z_2\) 极性坐标。若不存在全局连续截面，该极性只能局部定义，或必须通过切开界面、允许不连续、引入随机性等方式显现。

本附录只处理满足
\[
\sigma^2=\mathrm{id}
\]
的对合型取反。一般扭曲可能具有更长周期、固定点或不可逆性，不能自动约化为一个二值余坐标。

### A.1 对合与轨道商

#### 定义 A.1（对合与固定界面）

设 \(X\) 为集合。映射
\[
\sigma:X\to X
\]
称为对合，若
\[
\sigma(\sigma(x))=x
\]
对所有 \(x\in X\) 成立。其固定点集为
\[
\operatorname{Fix}(\sigma)
=
\{x\in X:\sigma(x)=x\}.
\]

定义等价关系
\[
x\sim_\sigma y
\iff
y=x\ \text{或}\ y=\sigma(x).
\]
轨道商记为
\[
B=X/\langle\sigma\rangle,
\]
商映射记为
\[
\pi:X\to B,
\qquad
\pi(x)=[x].
\]

#### 命题 A.2（商纤维结构）

对任意 \(x\in X\)，
\[
\boxed{
\pi(\sigma x)=\pi(x),
}
\]
并且
\[
\boxed{
\pi^{-1}(\pi(x))=\{x,\sigma x\}.
}
\]
若 \(x\notin\operatorname{Fix}(\sigma)\)，该纤维有两个不同元素；若 \(x\in\operatorname{Fix}(\sigma)\)，该纤维退化为单点。

##### 证明

由等价关系定义，\(x\sim_\sigma\sigma x\)，所以二者具有同一商类。反过来，若 \(y\in\pi^{-1}(\pi(x))\)，则 \(y\sim_\sigma x\)，故 \(y=x\) 或 \(y=\sigma x\)。固定点与非固定点情形立即得到。 \(\square\)

因此，\(\sigma\) 不改变商坐标 \([x]\)，只在同一商纤维内部交换代表元。固定界面是二点纤维坍缩成一点的位置。

### A.2 极性比特与命名截面的等价

记
\[
\mathbb S^0=\{-1,+1\}.
\]

#### 定义 A.3（极性函数）

若 \(\sigma\) 无固定点，称函数
\[
\chi:X\to\mathbb S^0
\]
为一个极性函数，若
\[
\boxed{
\chi(\sigma x)=-\chi(x)
}
\]
对所有 \(x\) 成立。

#### 定理 A.4（极性—截面对应）

设 \(\sigma\) 无固定点。下列两类数据自然一一对应：

1. 极性函数 \(\chi:X\to\mathbb S^0\)；
2. 商映射的截面
   \[
   s:B\to X,
   \qquad
   \pi\circ s=\mathrm{id}_B.
   \]

##### 证明

先由极性函数构造截面。每个轨道 \(b\in B\) 有两个元素 \(x,\sigma x\)，且
\[
\chi(\sigma x)=-\chi(x).
\]
所以轨道中恰有一个元素的极性为 \(+1\)。定义 \(s_\chi(b)\) 为该唯一元素。显然 \(\pi(s_\chi(b))=b\)。

反之，给定截面 \(s\)。对任意 \(x\in X\)，命题 A.2 给出
\[
x=s(\pi x)
\quad\text{或}\quad
x=\sigma(s(\pi x)).
\]
由于 \(\sigma\) 无固定点，两种情形互斥。定义
\[
\chi_s(x)
=
\begin{cases}
+1,&x=s(\pi x),\\
-1,&x=\sigma(s(\pi x)).
\end{cases}
\]
则直接有 \(\chi_s(\sigma x)=-\chi_s(x)\)。两个构造互为逆。 \(\square\)

#### 推论 A.5（商—余正规形）

选定截面 \(s\) 后，映射
\[
\Phi_s:B\times\mathbb S^0\to X
\]
定义为
\[
\Phi_s(b,+1)=s(b),
\qquad
\Phi_s(b,-1)=\sigma(s(b)).
\]
它是双射，并且在该坐标中
\[
\boxed{
\sigma(b,\varepsilon)=(b,-\varepsilon).
}
\]

##### 证明

每个商纤维恰有两个不同元素 \(s(b)\) 与 \(\sigma s(b)\)，所以 \(\Phi_s\) 在每个纤维上双射；不同商类的纤维互不相交。对合公式由定义立即成立。 \(\square\)

这给出“商余”一词的精确含义：

\[
\boxed{
x\longleftrightarrow([x],\varepsilon_s(x)).}
\]

商坐标 \([x]\) 是不随取反改变的无向内容；\(\varepsilon_s(x)\) 是依赖命名截面 \(s\) 的离散余坐标。没有选定截面时，不存在一个规范的全局 \(\varepsilon\)。

#### 命题 A.6（命名之间的 \(\mathbb Z_2\) 变换）

若 \(s,t:B\to X\) 是两个截面，则存在唯一函数
\[
g:B\to\mathbb S^0
\]
使
\[
t(b)=\Phi_s(b,g(b)).
\]

##### 证明

对每个 \(b\)，\(t(b)\) 与 \(s(b)\) 位于同一个二点纤维，因此 \(t(b)\) 唯一等于 \(s(b)\) 或 \(\sigma s(b)\)。分别令 \(g(b)=+1\) 或 \(-1\) 即得。 \(\square\)

所以“命名”不是改变商对象，而是改变各商纤维中哪一侧被称为正。不同命名之间的差异由一个 \(\mathbb Z_2\)-值函数记录。

### A.3 连续空间中的全局离散极性障碍

#### 定理 A.7（连通空间不能连续地产生非平凡离散读数）

设 \(X\) 为非空连通拓扑空间，\(D\) 为离散空间。任意连续映射
\[
f:X\to D
\]
都是常值。

##### 证明

连续像 \(f(X)\) 必为连通集。离散空间的连通子集只能是单点，因此 \(f(X)\) 为单点。 \(\square\)

#### 推论 A.8（无全局连续极性）

设 \(X\) 非空且连通，\(\sigma:X\to X\) 为连续对合。不存在连续极性函数
\[
\chi:X\to\mathbb S^0
\]
满足
\[
\chi(\sigma x)=-\chi(x).
\]

##### 证明

由定理 A.7，\(\chi\) 必为常值 \(c\in\{\pm1\}\)。于是极性条件要求 \(c=-c\)，矛盾。 \(\square\)

这说明：一个非平凡离散极性不能作为从连通连续对象到二点集合的全局连续确定函数自动出现。要从连续结构中“抠出”离散对象，至少必须引入界面、切口、局部截面、不连续阈值、随机抽样，或使定义域本身分裂成不同连通分支。

### A.4 界面切割定理

#### 定理 A.9（反不变连续量产生离散极性）

设 \(X\) 为拓扑空间，\(\sigma:X\to X\) 为连续对合，\(h:X\to\mathbb R\) 连续并满足
\[
\boxed{
h(\sigma x)=-h(x).
}
\]
定义
\[
\mathcal I=h^{-1}(0),
\]
\[
X_+=h^{-1}((0,\infty)),
\qquad
X_-=h^{-1}((-\infty,0)).
\]
则：

1. \(\mathcal I\) 闭且 \(\sigma\)-不变；
2. \(X_+\) 与 \(X_-\) 是开集，且
   \[
   \sigma(X_+)=X_-,
   \qquad
   \sigma(X_-)=X_+;
   \]
3. 每个固定点都位于界面：
   \[
   \operatorname{Fix}(\sigma)\subseteq\mathcal I;
   \]
4. 在 \(X\setminus\mathcal I\) 上定义
   \[
   \chi_h(x)=\operatorname{sgn}(h(x))\in\mathbb S^0,
   \]
   则 \(\chi_h\) 连续且
   \[
   \chi_h(\sigma x)=-\chi_h(x).
   \]

##### 证明

因为 \(\{0\}\) 闭且 \(h\) 连续，\(\mathcal I\) 闭。若 \(h(x)=0\)，则 \(h(\sigma x)=-h(x)=0\)，故界面不变。正、负半轴为开集，所以 \(X_\pm\) 开；反不变性把正值送到负值并反之。若 \(\sigma x=x\)，则
\[
h(x)=h(\sigma x)=-h(x),
\]
故 \(h(x)=0\)。最后，\(\chi_h^{-1}(+1)=X_+\) 与 \(\chi_h^{-1}(-1)=X_-\) 在子空间 \(X\setminus\mathcal I\) 中均开，因此 \(\chi_h\) 连续；反不变性给出极性翻转。 \(\square\)

若 \(h\) 同时取正值和负值，则 \(X\setminus\mathcal I\) 至少被 \(X_+\) 与 \(X_-\) 分成两个非空开闭部分。离散极性因此不是无界面的连续坐标，而是连续量跨越零界面以后产生的分区标签。

### A.5 三个基本模型

#### 例 A.10（实数反射）

取
\[
X=\mathbb R,
\qquad
\sigma(x)=-x,
\qquad
h(x)=x.
\]
则
\[
\mathcal I=\{0\},
\qquad
X/\langle\sigma\rangle\cong[0,\infty)
\]
由商坐标 \(|x|\) 实现。在 \(\mathbb R\setminus\{0\}\) 上，
\[
x\longleftrightarrow(|x|,\operatorname{sgn}x),
\]
而取反只改变第二坐标：
\[
(|x|,\varepsilon)\longmapsto(|x|,-\varepsilon).
\]
在 \(x=0\) 处，两点纤维坍缩为一点，极性消失。

#### 例 A.11（布尔取反）

取
\[
X=\{0,1\},
\qquad
\sigma(0)=1,
\quad
\sigma(1)=0.
\]
轨道商只有一个点。因此布尔对象没有剩余的非平凡商坐标，全部信息都是二值纤维极性。这解释了为什么布尔取反看起来像一个原始离散操作：它是“商底空间退化为一点”时的纯纤维交换。

#### 例 A.12（圆周上的对径对合）

取
\[
X=S^1,
\qquad
\sigma(z)=-z.
\]
该对合无固定点，商映射可由
\[
z\longmapsto z^2
\]
表示，每个商纤维为 \(\{z,-z\}\)。但 \(S^1\) 连通，所以由推论 A.8，不存在连续的全局极性函数
\[
\chi:S^1\to\mathbb S^0.
\]
这说明即使每个纤维都恰有两点，也不必存在全局连续的“正片/负片”命名。离散余坐标可能只能在局部坐标图中选择。

### A.6 扭曲对角的商影子

以下定理把本附录直接接回正文的对角算子。

#### 定理 A.13（对合对角的商影子恒等式）

设 \(\tau:Y\to Y\) 为对合，
\[
\pi:Y\to Y/\langle\tau\rangle
\]
为轨道商。对地址集 \(A\)，令
\[
\Pi_A:Y^A\to(Y/\langle\tau\rangle)^A
\]
为逐点商映射。则对任意评价表
\[
E:A\times A\to Y,
\]
有
\[
\boxed{
\Pi_A(\Delta_\tau E)
=
\Pi_A(D_AE).
}
\]

##### 证明

对任意 \(a\in A\)，
\[
\begin{aligned}
\Pi_A(\Delta_\tau E)(a)
&=
\pi(\tau(E(a,a)))\\
&=
\pi(E(a,a))\\
&=
\Pi_A(D_AE)(a),
\end{aligned}
\]
其中第二步使用 \(\pi\circ\tau=\pi\)。逐点相等即得。 \(\square\)

因此，扭曲对角与未扭曲对角在轨道商上具有完全相同的影子。对角逃逸所使用的变化发生在商纤维内部；任何只读取商类的观察者都看不见该变化。

#### 推论 A.14（极性通道精确翻转）

若 \(\tau\) 无固定点，且选定极性函数
\[
\chi:Y\to\mathbb S^0,
\qquad
\chi(\tau y)=-\chi(y),
\]
令
\[
\Chi_A:Y^A\to(\mathbb S^0)^A
\]
为逐点极性读取，则
\[
\boxed{
\Chi_A(\Delta_\tau E)
=-\Chi_A(D_AE)
}
\]
逐坐标成立。

##### 证明

对任意 \(a\)，
\[
\chi(\Delta_\tau E(a))
=
\chi(\tau(E(a,a)))
=
-\chi(E(a,a)).
\]
\(\square\)

结合推论 A.5，在选定截面以后可写
\[
D_AE(a)=(b_a,\varepsilon_a),
\]
\[
\boxed{
\Delta_\tau E(a)=(b_a,-\varepsilon_a).
}
\]
所以对合型对角化的正规形是：**商坐标保持不变，离散余坐标逐点翻转。**

### A.7 自然性不等于忠实性

正文以
\[
Q\Delta=\Delta P
\]
衡量对角算子是否与观察投影交换。但交换并不自动说明观察者保存了扭曲信息。

#### 定义 A.15（扭曲不变与扭曲分离）

给定 \(Q:Y\to Z\)：

- 若
  \[
  Q(\tau y)=Q(y)
  \]
  对所有 \(y\) 成立，称 \(Q\) 为 \(\tau\)-不变；
- 若
  \[
  y\notin\operatorname{Fix}(\tau)
  \Longrightarrow
  Q(\tau y)\neq Q(y),
  \]
  称 \(Q\) 为 \(\tau\)-分离。

#### 定理 A.16（盲自然性）

若 \(Q:Y\to Z\) 为 \(\tau\)-不变，并令粗层扭曲为恒等映射，则
\[
\boxed{
Q_A\Delta_\tau
=
Q_AD_A.
}
\]
更一般地，任何经由 \(Q\) 因子化的观察量都无法区分 \(y\) 与 \(\tau y\)。

##### 证明

第一式逐点为
\[
Q(\tau(E(a,a)))=Q(E(a,a)).
\]
若观察量写成 \(F\circ Q\)，则
\[
F(Q(\tau y))=F(Q(y)).
\]
\(\square\)

因此对角缺陷为零至少有两种完全不同的原因：

1. **忠实自然性**：投影保持了全部相关结构，并且仍能区分扭曲前后；
2. **盲自然性**：投影先把 \(y\) 与 \(\tau y\) 商掉，因而变化在观察层中不可见。

定义度量空间 \((Z,d_Z)\) 上的扭曲分离边际
\[
\operatorname{sep}_\tau(Q)
=
\inf_{y\notin\operatorname{Fix}(\tau)}
 d_Z(Qy,Q\tau y).
\]
只要存在非固定点，\(\tau\)-不变映射必有
\[
\operatorname{sep}_\tau(Q)=0.
\]
而取值于二点离散空间的极性函数满足每个非固定点的分离距离为 \(1\)。

所以正文的自然性缺陷应与一个独立的忠实性条件配合读取：

\[
\boxed{
\text{零缺陷只证明交换，不证明信息未被商掉。}
}
\]

### A.8 Li–Cayley 镜像是精确的连续—离散界面模型

定义
\[
J:\mathbb C^*\to\mathbb C^*,
\qquad
J(z)=\frac1{\overline z}.
\]

#### 定理 A.17（镜像对合与单位圆界面）

映射 \(J\) 是连续对合，其固定点集恰为单位圆：
\[
\boxed{
\operatorname{Fix}(J)=S^1.
}
\]
定义连续径向坐标
\[
b(z)=\log|z|.
\]
则
\[
\boxed{
b(Jz)=-b(z).}
\]
因此
\[
\mathbb C^*_+=\{|z|>1\},
\qquad
\mathbb C^*_- =\{|z|<1\}
\]
被 \(J\) 交换，而单位圆 \(|z|=1\) 是极性消失的固定界面。

##### 证明

直接计算
\[
J(Jz)
=
\frac1{\overline{1/\overline z}}
=z.
\]
又
\[
Jz=z
\iff
z\overline z=1
\iff
|z|=1.
\]
最后
\[
b(Jz)
=
\log\left|\frac1{\overline z}\right|
=
-\log|z|.
\]
其余结论由定理 A.9 得到。 \(\square\)

#### 定理 A.18（镜像轨道商的显式参数）

映射
\[
q:\mathbb C^*\to[0,\infty)\times S^1,
\]
\[
q(z)
=
\left(
|\log|z||,
\frac z{|z|}
\right)
\]
在 \(J\)-轨道上常值，并且恰好分离不同轨道。因此它诱导自然同胚
\[
\boxed{
\mathbb C^*/\langle J\rangle
\cong
[0,\infty)\times S^1.
}
\]

##### 证明

极坐标给出同胚
\[
\Phi:\mathbb C^*\to\mathbb R\times S^1,
\qquad
\Phi(z)=\left(\log|z|,\frac z{|z|}\right),
\]
其逆为
\[
(u,\omega)\longmapsto e^u\omega.
\]
在该坐标中，
\[
J(u,\omega)=(-u,\omega).
\]
实轴关于 \(u\mapsto-u\) 的轨道商由 \(|u|\) 与 \([0,\infty)\) 同胚，因此乘上不变的角坐标 \(\omega\) 即得结论。 \(\square\)

这个商坐标恰好保留：

- 角相位 \(z/|z|\)；
- 离单位圆的无向径向深度 \(|\log|z||\)。

被商掉的是“位于单位圆内侧还是外侧”的极性比特。

#### 推论 A.19（临界线是 Li–Cayley 极性界面）

对
\[
C(s)=1-\frac1s
\]
定义
\[
\beta_C(s)=\log|C(s)|.
\]
对镜像
\[
\mathfrak m(s)=1-\overline s
\]
有
\[
\boxed{
\beta_C(\mathfrak m(s))=-\beta_C(s).
}
\]
并且
\[
\boxed{
\beta_C(s)=0
\iff
\Re s=\frac12.
}
\]
此外
\[
\beta_C(s)>0
\iff
\Re s<\frac12,
\]
\[
\beta_C(s)<0
\iff
\Re s>\frac12.
\]

##### 证明

由正文定理 8.3，
\[
C(\mathfrak m(s))
=
\frac1{\overline{C(s)}}.
\]
取模并取对数得到反不变性。其余等价由定理 8.2 得到。 \(\square\)

因此 Riemann 假设可严格写成
\[
\boxed{
\forall\rho\in Z_{\mathrm{nt}},
\quad
\beta_C(\rho)=0.
}
\]
也就是说：所有非平凡零点都落在镜像对合的固定界面上。离线零点及其镜像具有相同的无向商坐标
\[
\left(
|\beta_C|,
\frac{C(\rho)}{|C(\rho)|}
\right),
\]
但具有相反的内外极性。

#### 推论 A.20（Li 探针的双曲放大形式）

若
\[
C(\rho)=e^{\beta+i\theta},
\qquad
\beta=\beta_C(\rho),
\]
则正文的四元轨道贡献可写成
\[
\boxed{
L_n(\rho)
=
4-4\cosh(n\beta)\cos(n\theta).
}
\]

##### 证明

令 \(r=e^\beta\)。则
\[
r^n+r^{-n}
=e^{n\beta}+e^{-n\beta}
=2\cosh(n\beta).
\]
代入定理 8.7 即得。 \(\square\)

这个公式说明，高阶 Li 探针并不是简单翻转一个布尔标签。它把连续的反不变径向坐标 \(\beta\) 放大为 \(\cosh(n\beta)\)，再由相位 \(\theta\) 决定该放大在具体阶数上如何显现。离散极性
\[
\operatorname{sgn}\beta
\]
只是对“位于界面哪一侧”的粗粒化；真正控制指数尺度的是连续商余深度 \(|\beta|\)。

### A.9 连续状态到离散结果的结构边界

#### 定理 A.21（非平凡离散测量不能只是连通空间上的连续确定函数）

设 \(X\) 为非空连通状态空间，\(D\) 为至少含两个点的有限离散结果集。不存在非恒定连续确定读出
\[
m:X\to D.
\]

##### 证明

这是定理 A.7 的直接应用。 \(\square\)

因此，从连续状态获得非平凡离散结果的模型，必须至少采用以下一种结构：

1. **界面阈值**：先以连续量 \(h:X\to\mathbb R\) 描述状态，再以 \(\operatorname{sgn}h\) 离散化；读出在 \(h=0\) 的界面处不连续或退化；
2. **分支/扇区**：定义域在相关尺度上已经不连通；
3. **局部命名**：离散纤维只在局部截面中有标签，不存在全局连续极性；
4. **随机读出**：连续地映射到概率单纯形 \(\Delta(D)\)，再由一次抽样产生离散结果。

有限维量子测量的 Born 映射
\[
\rho
\longmapsto
\left(
\operatorname{Tr}(\rho P_i)
\right)_i
\]
属于第四类：状态到概率向量的映射是连续的，而单次结果不是一个由连通态空间连续确定的离散坐标。这个事实不把经典与量子约化成坐标变换；它只说明“连续对象直接连续地产生确定离散标签”不是一个非平凡模型。

### A.10 本附录的闭合结论

#### 结论 G：对合型取反的正规形

在选定截面的自由对合系统中，
\[
\boxed{
\text{对象}
=
\text{轨道商坐标}
+
\mathbb Z_2\text{ 极性坐标},
}
\]
且
\[
\boxed{
\text{取反}
=
\text{保持商坐标并翻转极性坐标}.
}
\]

#### 结论 H：离散极性需要命名或界面

在连通连续空间上不存在全局连续的非平凡二值极性。可观察的离散标签必须来自截面、切口、界面、不连续粗粒化、连通分支或随机抽样。

#### 结论 I：对角化在商上可能完全不可见

对合扭曲满足
\[
\boxed{
\Pi_A\Delta_\tau
=
\Pi_AD_A.
}
\]
所以商观察者可以给出零缺陷，同时把逃逸所依赖的全部纤维极性完全删除。自然性与忠实性必须分开审计。

#### 结论 J：Li–Cayley 给出精确实例

镜像
\[
z\mapsto\frac1{\overline z}
\]
保持轨道商坐标
\[
\left(
|\log|z||,
\frac z{|z|}
\right)
\]
并翻转径向极性。单位圆是固定界面，RH 等价于全部非平凡零点的 Cayley 像都位于该界面。Li 探针以
\[
\cosh(n\beta_C)
\]
放大连续径向缺陷，而不是仅仅操作一个离散布尔位。

本附录的定理 A.2—A.21 均为完整纸面证明，尚未新增为 Lean 真源；它们不得在获得形式证明与冻结收据以前被标记为 `Closed`。
