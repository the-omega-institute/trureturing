# RH 离线零点的 Zeckendorf 能量、黄金传递与 Lee–Yang 横向相变理论

## 摘要

本文继续发展 `RH_OFFLINE_ZERO_LEE_YANG_INSTANTANEOUS_PHASE_TRANSITION_THEORY.md`，研究以下问题：为什么 Zeckendorf 表示、黄金比例、PrimeGaps、跳跃能量、Hankel 最小记忆、Lee–Yang 零点与假想的 zeta 离线零点会反复出现在同一理论邻域中。

结论不是“黄金比例直接证明 RH”，也不是“把整数写成 Zeckendorf 表示便会改变 zeta”。恰恰相反，本文首先证明一个否定性结论：Zeckendorf 表示对整数指数的编码是无损双射，因此凡是只通过整数指数取值的标量 Euler 配分函数，在 Zeckendorf 重编码下完全不变。Zeckendorf 本身不会制造任何新零点。

它真正增加的是一个此前被标量指数压扁的关系层：

$$
\boxed{
\text{整数指数}
\quad\longmapsto\quad
\text{唯一的无相邻占据历史}.
}
$$

在这一提升中，同一个有限状态空间自然携带五种不能混同的能量：

1. Fibonacci 指数值能量；
2. 占据数能量；
3. 黄金共轭稳定影子；
4. successor／translation 跳跃能量；
5. prime-frequency 横向关系能量。

第一种能量完整区分状态，却遗忘状态之间的局部关系；第二至第五种能量逐层恢复 hard-core memory、稳定通道、动态转移和 cross-prime 外积结构。项目中已经机器闭合的 `FiniteZeckendorfEulerIdentity`、`GoldenEulerBetaZeckendorf`、`PrimeJumpDecomposition`、`HankelRankMinimality`、`GoldenScalarDihedralBlindness`、`OrderedPrimeHolonomyCasimir` 和 `OffLineOrbitParityDecomposition` 正好落在这条分层链的不同位置。

本文得到四个新的有限理论核心。

第一，有限 Zeckendorf 指数配分函数严格退化为几何级数，其全部非平凡根位于局部 Euler fugacity 单位圆；而 hard-core 占据配分函数由二阶 transfer matrix 控制，其两个本征通道为

$$
\lambda_\pm(z)=\frac{1\pm\sqrt{1+4z}}2,
$$

在 $z=1$ 时恰为

$$
\lambda_+(1)=\varphi,
\qquad
\lambda_-(1)=-\varphi^{-1}.
$$

因此 $\varphi$ 是最小一位记忆系统的 Perron 增长率，$-\varphi^{-1}$ 是精确性所必需、却在大尺度上指数衰减的稳定影子通道。

第二，项目的黄金指数账户具有一个精确的两级创新场。若 $b(v)$ 表示该账户，则

$$
\Delta b_v=b(v+1)-b(v)\in\{\varphi^2,\varphi\},
$$

并且扣除平均漂移 $\sqrt5$ 后，创新只取

$$
\varphi^{-2},\qquad-\varphi^{-1}.
$$

它的累积和始终有界，而长期均方能量恰为 $\varphi^{-3}$。这说明黄金稳定通道不是额外随机噪声，而是一条确定性的、零平均、有限预算的校正流。

第三，Zeckendorf 分解把一个 prime-power translation 精确分解成 Fibonacci 尺度 translation 的乘积，并给出跳跃能量的多尺度上界。它把项目已有的 arithmetic jump Laplacian 与黄金 shell 连接起来，但不提供反向 coercivity；不同 shell 仍可能在标量 translation 中发生抵消。

第四，在有限 Zeckendorf 状态与有限 prime cluster 的联合模型中，横向 susceptibility 的二阶系数严格分解为

$$
\boxed{
\text{Zeckendorf exponent second moment}
\times
\text{prime log-frequency relation energy}.
}
$$

若状态均匀分布，前者随黄金深度约按 $\varphi^{2Q}$ 增长；若使用真实单素数 Euler Gibbs 权，前者却保持有限。因此 combinatorial state count 本身不会产生 zeta 相变；真正的全局临界性必须来自 prime–Gamma 完成对跨尺度状态权的重新组织。

最终得到的统一判断是：

$$
\boxed{
\begin{aligned}
\text{Zeckendorf}
&=\text{标量整数指数的无损关系提升},\\
\varphi
&=\text{最小 hard-core memory 的扩张通道},\\
-\varphi^{-1}
&=\text{被标量大尺度压低的稳定影子},\\
\text{jump / holonomy / odd energy}
&=\text{被反射或交换压掉的一阶信息的二阶显影},\\
\text{假想离线零点}
&=\text{标量完成为零而关系层仍可能带正横向能量的时刻}.
\end{aligned}
}
$$

最后一行仍是条件性的。要把它提升为 RH 证明，必须构造 canonical prime–Zeckendorf–Gamma transfer，并证明其关系能量无条件支配 zero-side 离线奇能量。本文不把该桥藏入“能量”“黄金”“相变”或“Zeckendorf”这些名称中。

---

# 0. 理论地位与真源边界

本文是纯数学理论，不是工程规范，也不新增 Lean 声明。

下列事实已经由仓库 Lean 真源承担：

1. `D5/S0/Tower/GoldenNames`：长度 $Q$ 的合法黄金名字与初始 Fibonacci 区间双射，基数为 $F_{Q+2}$，并具有实值注入读出；
2. `D5/S3/Observer/GoldenCoding/FiniteZeckendorfEulerIdentity`：Zeckendorf Fibonacci 和给出初始整数区间，并把有限 Euler 和精确运输为几何级数；
3. `D5/S3/Analytic/GoldenEulerBetaZeckendorf`：黄金指数账户的闭式、最小 Zeckendorf 指标奇偶读出和 $\varphi/\varphi^2$ 跳跃律；
4. `D5/S1/Deficit/ZeckendorfDisplacementReading`：Fibonacci 指标上移之和等于黄金 Beatty 读数；
5. `D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition`：有限 prime-power 项等于 coherent mass 减去非负 arithmetic jump energy；
6. `D5/S3/Observer/Hankel/HankelRankMinimality` 与 `HankelMinimalStateDimension`：稳定 Hankel rank 计算可见可达维数，并等于同一行为的最小实现维数；
7. `D5/S3/Observer/AgencyHolonomy/GoldenScalarDihedralBlindness`：完整标量黄金世界不能恢复有序 prime-word dihedral holonomy；
8. `D5/S3/Observer/AgencyHolonomy/OrderedPrimeHolonomyCasimir`：一阶有序响应消失，负二阶响应成为平方 winding 的非负加权和；
9. `D5/S3/Weil/HolonomyBridge/OffLineOrbitParityDecomposition`：一个 supplied 离线轨道的 Weil 贡献分解成偶能量减奇能量，且两种能量分别非负。

本文从这些真源出发作有限代数、组合、谱和能量推导。以下内容明确不作为既有 Lean 定理冒充：

- canonical prime–Zeckendorf–Gamma transfer 已经存在；
- Zeckendorf 稳定影子已经等于 zeta zero odd channel；
- prime-side 横向能量已经支配 zero-side 奇能量；
- 黄金比例已经从 Riemann completed function 中被无条件抽取；
- RH 已被证明。

---

# 1. 状态、能量、关系与测度必须分开

## 1.1 四元对象

一个有限统计—谱系统不只是一组状态。其完整数据至少应写成

$$
\boxed{
\mathfrak S=(\Omega,H,\mathcal R,\mu),
}
\tag{1.1}
$$

其中：

- $\Omega$ 是微观状态空间；
- $H:\Omega\to\mathbb R$ 是能量或指数读出；
- $\mathcal R$ 是状态之间的局部约束、转移、顺序或关系结构；
- $\mu$ 是状态权或所选 ensemble。

相应配分函数为

$$
Z_{\mathfrak S}(\beta)
=
\sum_{\eta\in\Omega}
\mu(\eta)e^{-\beta H(\eta)}.
\tag{1.2}
$$

仅知道 $Z_{\mathfrak S}$，一般不能恢复 $\mathcal R$。甚至当 $H$ 对状态是单射时，$Z$ 仍只读取能级及其权重，不读取这些能级是通过何种局部记忆、carry 或 holonomy 连接起来的。

这正是本文所有“看似相关”对象的共同位置：

$$
\boxed{
\text{Zeckendorf 给出 }\Omega\text{ 与 }\mathcal R,
\quad
\text{Euler 给出 }H\text{ 与 }\mu,
\quad
\text{Lee–Yang 读取 }Z\text{ 的复零点},
\quad
\text{信息逃逸检测 }\mathfrak S\mapsto Z\text{ 遗忘了什么}.
}
\tag{1.3}
$$

## 1.2 五类能量

对后文的黄金—素数系统，必须区分：

### （一）指数值能量

$$
E_Q(\eta)=\sum_k\eta_kF_k.
\tag{1.4}
$$

它回答“这个历史代表哪个整数”。

### （二）占据能量

$$
N_Q(\eta)=\sum_k\eta_k.
\tag{1.5}
$$

它回答“这个历史使用了多少个 Fibonacci 原子”。

### （三）稳定影子

$$
S_Q(\eta)=\sum_k\eta_k\psi^k,
\qquad
\psi=-\varphi^{-1}.
\tag{1.6}
$$

它记录主 Fibonacci 值读出中被整数投影压掉的 Galois 共轭校正。

### （四）跳跃／carry 能量

$$
\mathcal D(f)
=
\sum_{\eta\to\eta'}
\left|f(\eta')-f(\eta)\right|^2.
\tag{1.7}
$$

它读取状态之间的变化，而不是单个状态的值。

### （五）横向关系能量

$$
\mathcal E_{p,q}^{\perp}(\delta)
=
\sinh^2\!\left(
\delta\log\frac qp
\right).
\tag{1.8}
$$

它读取两个 prime frequencies 在反射横向偏移下是否仍然不可区分。

五者的输出空间、零集和可加性不同，不能以“都是 energy”为理由直接相等或相加。本文所建立的是它们之间的精确分解、共同二次结构和仍待构造的输运箭头。

---

# 2. Zeckendorf 是整数指数的无损 hard-core 提升

## 2.1 有限合法词空间

固定 $Q\ge0$，定义

$$
\Omega_Q
=
\left\{
(\eta_2,\ldots,\eta_{Q+1})\in\{0,1\}^{Q}:
\eta_k\eta_{k+1}=0
\right\}.
\tag{2.1}
$$

约束 $\eta_k\eta_{k+1}=0$ 是一步 hard-core memory：一位被占据以后，下一位不得被占据。

定义 Fibonacci 指数能量

$$
\boxed{
E_Q(\eta)
=
\sum_{k=2}^{Q+1}\eta_kF_k.
}
\tag{2.2}
$$

记

$$
M_Q=F_{Q+2}.
\tag{2.3}
$$

### 定理 2.1　有限 Zeckendorf 能量双射

映射

$$
E_Q:\Omega_Q\longrightarrow
\{0,1,\ldots,M_Q-1\}
\tag{2.4}
$$

是双射。

#### 证明

这是仓库 `GoldenNames.goldenNameEquiv` 与 `FiniteZeckendorfEulerIdentity` 的数学内容：合法无相邻 Fibonacci 数位恰好唯一表示初始区间中的每一个整数。

### 推论 2.2　状态数与黄金熵

$$
|\Omega_Q|=M_Q=F_{Q+2}.
\tag{2.5}
$$

因此

$$
\log|\Omega_Q|
=Q\log\varphi+O(1).
\tag{2.6}
$$

$\log\varphi$ 不是人为插入的常数，而是最小一步记忆二进制系统的状态熵率。

## 2.2 无损与无记忆不是同一件事

因为 $E_Q$ 是双射，所以若 observer 能读取完整整数值 $E_Q(\eta)$，则任意两个不同状态都可区分：

$$
E_Q(\eta)=E_Q(\xi)
\Longrightarrow
\eta=\xi.
\tag{2.7}
$$

所以在**微观状态层**，Zeckendorf energy 没有信息逃逸。

但双射并不意味着它保存了关系结构。若只保留能量列表

$$
0,1,\ldots,M_Q-1,
$$

则“这些整数来自无相邻数位”“successor 如何 carry”“哪些状态共享最小数位奇偶”“状态图的 Hankel rank 为何”等信息全部不在能量列表中。

因此必须区分：

$$
\boxed{
\text{状态可识别性}
\neq
\text{结构可恢复性}.
}
\tag{2.8}
$$

---

# 3. 凡经由整数指数因子的标量量都不产生新信息

## 3.1 Factor-through-energy 不变性

### 定理 3.1　任意指数函数的 Zeckendorf 重标不变

对任意交换加法目标中的函数 $a$，

$$
\boxed{
\sum_{\eta\in\Omega_Q}a(E_Q(\eta))
=
\sum_{v=0}^{M_Q-1}a(v).
}
\tag{3.1}
$$

#### 证明

由定理 2.1 对有限和重标即可。

这条定理比某个特定配分函数更重要。它说明：任何完全因子化为

$$
\Omega_Q\xrightarrow{E_Q}\{0,\ldots,M_Q-1\}\xrightarrow{a}A
$$

的读出，都只看见整数能量，不看见 Zeckendorf locality。

## 3.2 有限 Zeckendorf–Euler 多项式

取 $a(v)=x^v$，定义

$$
Z_Q^{\mathrm{exp}}(x)
=
\sum_{\eta\in\Omega_Q}x^{E_Q(\eta)}.
\tag{3.2}
$$

则

$$
\boxed{
Z_Q^{\mathrm{exp}}(x)
=
1+x+\cdots+x^{M_Q-1}
=
\frac{1-x^{M_Q}}{1-x}.
}
\tag{3.3}
$$

### 定理 3.2　有限局部 fugacity 圆定位

若 $Q\ge1$，则

$$
Z_Q^{\mathrm{exp}}(x)=0
\Longleftrightarrow
x^{M_Q}=1
\text{ 且 }x\ne1.
\tag{3.4}
$$

从而全部根满足

$$
\boxed{|x|=1.}
\tag{3.5}
$$

这是一条真正的有限圆定位定理，但它来自能量双射和几何级数，不是 Riemann Hypothesis。

## 3.3 无限局部 Euler 因子

令 $\Omega_\infty$ 为有限支撑的无限合法 Zeckendorf 数位。Zeckendorf 定理给出

$$
\Omega_\infty\simeq\mathbb N.
\tag{3.6}
$$

因此当 $|x|<1$ 时，

$$
\boxed{
\sum_{\eta\in\Omega_\infty}x^{E(\eta)}
=
\sum_{v\ge0}x^v
=
\frac1{1-x}.
}
\tag{3.7}
$$

取 $x=p^{-s}$，在 $\Re s>0$ 的单局部收敛域中，

$$
\sum_{\eta\in\Omega_\infty}
p^{-sE(\eta)}
=
(1-p^{-s})^{-1}.
\tag{3.8}
$$

### 否定性结论 3.3　Zeckendorf 重编码不会改变 Euler scalar

Zeckendorf lift 对单个 Euler 因子是无损坐标变化。只要 Hamiltonian 仍然只是 $E(\eta)$ 的函数，它既不改变局部因子，也不改变由这些因子在绝对收敛域内形成的标量乘积。

因此：

$$
\boxed{
\text{Zeckendorf 本身不是新 zeta，也不是离线零点的来源。}
}
\tag{3.9}
$$

新内容只能来自不因子化经过 $E$ 的 readout，例如 occupancy、carry、ordered holonomy、exterior energy 或 Gamma-coupled completion。

---

# 4. 两个“单位圆”必须严格区分

## 4.1 局部 Euler fugacity 圆

在式 (3.3) 中，变量是

$$
x=p^{-s}.
\tag{4.1}
$$

所以

$$
|x|=1
\Longleftrightarrow
\Re s=0.
\tag{4.2}
$$

有限几何级数的单位圆根对应局部 Euler 坐标中的虚轴。

## 4.2 completed Cayley–Lee–Yang 圆

对 completed function 的中心变量

$$
u=s-\frac12,
$$

取 $a>1/2$，定义

$$
w=C_a(u)=\frac{a+u}{a-u}.
\tag{4.3}
$$

则

$$
|w|=1
\Longleftrightarrow
\Re s=\frac12.
\tag{4.4}
$$

这是前一理论卷使用的 RH 临界圆。

### 定理 4.1　两圆非同一

局部变量 $x=p^{-s}$ 的圆与 completed Cayley 变量 $w=C_a(s-1/2)$ 的圆不是同一坐标集合：前者对应 $\Re s=0$，后者对应 $\Re s=1/2$。

所以从式 (3.5) 不能推出 RH。

把两只圆识别起来所需的不是代数换名，而是一个真正承载：

- 全部素数；
- Gamma 因子；
- 函数方程；
- 解析延拓；
- 零点输运；

的 prime–Gamma completion。

这条非同一性是信息逃逸审计中的硬边界：

$$
\boxed{
\text{局部 fugacity circle}
\not\equiv
\text{completed critical circle}.
}
\tag{4.5}
$$

---

# 5. 同一个 Zeckendorf 状态空间具有另一套 hard-core 配分函数

## 5.1 占据多项式

定义占据数

$$
N_Q(\eta)=\sum_{k=2}^{Q+1}\eta_k
\tag{5.1}
$$

以及 hard-core occupation polynomial

$$
H_Q(z)
=
\sum_{\eta\in\Omega_Q}z^{N_Q(\eta)}.
\tag{5.2}
$$

按最高数位是否占据分类，得到

$$
\boxed{
H_Q(z)=H_{Q-1}(z)+zH_{Q-2}(z),
}
\tag{5.3}
$$

初值为

$$
H_0(z)=1,
\qquad
H_1(z)=1+z.
\tag{5.4}
$$

## 5.2 二态 transfer matrix

令

$$
T(z)=
\begin{pmatrix}
1&z\\
1&0
\end{pmatrix}.
\tag{5.5}
$$

其特征值为

$$
\boxed{
\lambda_\pm(z)
=
\frac{1\pm\sqrt{1+4z}}2.
}
\tag{5.6}
$$

并有闭式

$$
H_Q(z)
=
\frac{
\lambda_+(z)^{Q+2}-
\lambda_-(z)^{Q+2}
}{
\lambda_+(z)-\lambda_-(z)
}.
\tag{5.7}
$$

在 $z=1$：

$$
\boxed{
\lambda_+(1)=\varphi,
\qquad
\lambda_-(1)=1-\varphi=-\varphi^{-1}.
}
\tag{5.8}
$$

因此

$$
H_Q(1)=F_{Q+2}
=
\frac{\varphi^{Q+2}-(-\varphi^{-1})^{Q+2}}{\sqrt5}.
\tag{5.9}
$$

$\varphi$ 是扩张通道，$-\varphi^{-1}$ 是稳定通道。后者在相对尺度上指数衰减，却承担精确整数值、边界条件和奇偶振荡。

## 5.3 Hankel 最小记忆维数

序列

$$
a_Q=H_Q(1)=F_{Q+2}
\tag{5.10}
$$

满足二阶递推，故其稳定 Hankel rank 不超过 $2$。另一方面，

$$
\det
\begin{pmatrix}
a_0&a_1\\
a_1&a_2
\end{pmatrix}
=
\det
\begin{pmatrix}
1&2\\
2&3
\end{pmatrix}
=-1\ne0.
\tag{5.11}
$$

所以 Hankel rank 恰为 $2$。

结合仓库的 Hankel 最小实现定理，完整 Fibonacci 计数行为的最小有限状态实现维数正是两维。两维可取为：

- 上一位未占据；
- 上一位已占据。

于是：

$$
\boxed{
\varphi\text{ 不是“神秘常数”，而是最小一步记忆自动机的主本征值。}
}
\tag{5.12}
$$

同时：

$$
\boxed{
-\varphi^{-1}\text{ 是标量大尺度近似最容易遗漏、但精确系统不能删除的第二状态方向。}
}
\tag{5.13}
$$

## 5.4 hard-core 零点与 equimodular locus

由式 (5.7)，若 $H_Q(z)=0$ 且 $z\ne-1/4$，则

$$
\left(
\frac{\lambda_+(z)}{\lambda_-(z)}
\right)^{Q+2}=1.
\tag{5.14}
$$

因此必有

$$
|\lambda_+(z)|=|\lambda_-(z)|.
\tag{5.15}
$$

全部根可写为

$$
\boxed{
z_j
=-\frac1{4\cos^2\!\left(\frac{j\pi}{Q+2}\right)},
\qquad
1\le j\le\left\lfloor\frac{Q+1}{2}\right\rfloor.
}
\tag{5.16}
$$

它们全在负实轴，并在 $Q\to\infty$ 时向边缘

$$
z_c=-\frac14
\tag{5.17}
$$

聚积。在 $z_c$，两个 transfer eigenvalues 合并。

这给出一个严格的有限 Lee–Yang／Fisher 型原型：

$$
\boxed{
\text{零点}
=
\text{两个 transfer channels 等模并满足相位量子化}.
}
\tag{5.18}
$$

它是 Zeckendorf hard-core system 的定理，不是 zeta 的定理。

---

# 6. 二变量 Zeckendorf 配分函数同时保留值与记忆

## 6.1 联合配分函数

定义

$$
\boxed{
\mathcal Z_Q(x,z)
=
\sum_{\eta\in\Omega_Q}
 x^{E_Q(\eta)}z^{N_Q(\eta)}.
}
\tag{6.1}
$$

按最高数位分类得到非齐次 Fibonacci transfer：

$$
\boxed{
\mathcal Z_Q(x,z)
=
\mathcal Z_{Q-1}(x,z)
+z x^{F_{Q+1}}
\mathcal Z_{Q-2}(x,z),
}
\tag{6.2}
$$

其中

$$
\mathcal Z_0=1,
\qquad
\mathcal Z_1=1+zx.
\tag{6.3}
$$

两个截面分别为

$$
\mathcal Z_Q(x,1)=Z_Q^{\mathrm{exp}}(x),
\tag{6.4}
$$

$$
\mathcal Z_Q(1,z)=H_Q(z).
\tag{6.5}
$$

因此同一个状态空间在两个 observer 下呈现完全不同的零点几何：

- 指数 observer 看见单位圆几何级数；
- occupancy observer 看见负实轴 hard-core edge；
- 联合 observer 看见一个二维复零簇。

这证明“零点属于哪一种相变”不能只由状态空间决定，还取决于选择了哪一个 Hamiltonian 和哪一种 ensemble。

## 6.2 反射完成不等于圆定位

令 $z\in\mathbb R$，定义关于 $x$ 的 reciprocal completion

$$
\boxed{
\mathcal C_Q(x,z)
=
\mathcal Z_Q(x,z)\,
 x^{M_Q-1}\mathcal Z_Q(x^{-1},z).
}
\tag{6.6}
$$

则

$$
x^{2(M_Q-1)}
\mathcal C_Q(x^{-1},z)
=
\mathcal C_Q(x,z).
\tag{6.7}
$$

所以根自动以 reciprocal pairs 出现。但这不保证每个根在单位圆上。

最小情形 $Q=1$：

$$
\mathcal Z_1(x,z)=1+zx,
\tag{6.8}
$$

$$
\mathcal C_1(x,z)
=(1+zx)(x+z).
\tag{6.9}
$$

其根为

$$
x_+=-z,
\qquad
x_-=-z^{-1}.
\tag{6.10}
$$

若令 $z=e^h>0$，则

$$
|x_+|=e^h,
\qquad
|x_-|=e^{-h}.
\tag{6.11}
$$

在 $h=0$，两根在 $-1$ 合并；在 $h\ne0$，它们同角、互为倒数、离开单位圆。

然而始终有一阶有符号径向荷抵消：

$$
\log|x_+|+\log|x_-|=0.
\tag{6.12}
$$

而二阶径向能量为

$$
\boxed{
(\log|x_+|)^2+(\log|x_-|)^2
=2h^2.
}
\tag{6.13}
$$

这个最小模型精确说明：

$$
\boxed{
\text{反射函数方程只产生 reciprocal pairing；
正性或稳定性才负责 circle localization。}
}
\tag{6.14}
$$

它与 completed zeta 的函数方程／RH 分工同型，但不是二者的数值同一。

---

# 7. Zeckendorf 的扩张通道与稳定影子

## 7.1 Minkowski 双通道

令

$$
\psi=1-\varphi=-\varphi^{-1}.
\tag{7.1}
$$

对合法词 $\eta$，定义

$$
U(\eta)=\sum_k\eta_k\varphi^k,
\qquad
S(\eta)=\sum_k\eta_k\psi^k.
\tag{7.2}
$$

由 Binet 公式，

$$
\boxed{
E(\eta)
=
\frac{U(\eta)-S(\eta)}{\sqrt5}.
}
\tag{7.3}
$$

若把每个 Fibonacci 指标上移一位，定义

$$
E^+(\eta)=\sum_k\eta_kF_{k+1},
\tag{7.4}
$$

则

$$
\boxed{
E^+(\eta)=\varphi E(\eta)+S(\eta).
}
\tag{7.5}
$$

仓库的 Zeckendorf displacement reading 正是这一关系的整数闭式版本。

对 canonical Zeckendorf 数位，稳定影子满足统一界

$$
\boxed{
-\varphi^{-2}<S(\eta)<\varphi^{-1}.
}
\tag{7.6}
$$

其符号由最小被占据指标的奇偶控制。

所以：

- $U$ 随深度指数增长；
- $S$ 始终在固定有界窗内；
- 但 $S$ 决定上移值落在哪一个相邻整数以及下一次跳跃取哪一支。

这是“稳定通道小但不可删除”的第一个精确实例。

## 7.2 黄金指数账户的两级跳跃

记项目中的黄金指数账户为

$$
b(v)=\operatorname{o5Beta}(v).
\tag{7.7}
$$

仓库已证闭式

$$
\boxed{
 b(v)
=\left\lfloor\frac{v+1}{\varphi}\right\rfloor
+v\varphi
=\sqrt5\,v+\varphi^{-1}
-\operatorname{fract}((v+1)\varphi).
}
\tag{7.8}
$$

定义增量

$$
\Delta b_v=b(v+1)-b(v).
\tag{7.9}
$$

则

$$
\boxed{
\Delta b_v\in\{\varphi^2,\varphi\}.
}
\tag{7.10}
$$

具体分支由 $v+1$ 的 canonical Zeckendorf 最小指标奇偶决定。

## 7.3 精确创新场

扣除平均漂移，定义

$$
\boxed{
\xi_v=\Delta b_v-\sqrt5.
}
\tag{7.11}
$$

由

$$
\varphi^2-\sqrt5=\varphi^{-2},
\qquad
\varphi-\sqrt5=-\varphi^{-1},
\tag{7.12}
$$

得到

$$
\boxed{
\xi_v\in\{\varphi^{-2},-\varphi^{-1}\}.
}
\tag{7.13}
$$

### 定理 7.1　高跳跃的精确计数

令

$$
A_N=\#\{0\le v<N:\Delta b_v=\varphi^2\}.
\tag{7.14}
$$

则

$$
\boxed{
A_N=\left\lfloor\frac{N+1}{\varphi}\right\rfloor.
}
\tag{7.15}
$$

#### 证明

因为 $b(0)=0$，且每个高跳跃比低跳跃多 $1$，故

$$
b(N)=N\varphi+A_N.
$$

与式 (7.8) 比较即得。

因此高跳跃频率与低跳跃频率分别为

$$
\lim_{N\to\infty}\frac{A_N}{N}
=\varphi^{-1},
\tag{7.16}
$$

$$
\lim_{N\to\infty}\frac{N-A_N}{N}
=\varphi^{-2}.
\tag{7.17}
$$

### 定理 7.2　创新累计严格有界

$$
\boxed{
\sum_{v=0}^{N-1}\xi_v
=b(N)-N\sqrt5
=\varphi^{-1}-\operatorname{fract}((N+1)\varphi).
}
\tag{7.18}
$$

从而

$$
-\varphi^{-2}
<
\sum_{v=0}^{N-1}\xi_v
\le
\varphi^{-1}.
\tag{7.19}
$$

所以创新场的积分不会随时间增长。

### 定理 7.3　创新均方能量

$$
\boxed{
\lim_{N\to\infty}
\frac1N\sum_{v=0}^{N-1}\xi_v^2
=\varphi^{-3}.
}
\tag{7.20}
$$

#### 证明

由两种取值和频率，

$$
\varphi^{-1}\varphi^{-4}
+\varphi^{-2}\varphi^{-2}
=
\varphi^{-5}+\varphi^{-4}
=\varphi^{-3}.
$$

这给出一条精确的“漂移—创新”分解：

$$
\boxed{
\Delta b_v
=\sqrt5+\xi_v,
\qquad
\text{累计创新有界，均方创新为 }\varphi^{-3}.
}
\tag{7.21}
$$

它不是热随机过程，而是 balanced Sturmian／Zeckendorf memory 产生的确定性有限预算流。

---

# 8. 项目的 arithmetic jump energy 可由 Zeckendorf shell 分解

## 8.1 已有 prime jump decomposition

项目已经构造

$$
\operatorname{PrimeTerm}
=
2W_L\|f\|_2^2
-
E_{\mathrm{jump},L}(f),
\tag{8.1}
$$

其中

$$
E_{\mathrm{jump},L}(f)
=
\sum_{n\in\mathcal P_L}
\frac{\Lambda(n)}{\sqrt n}
\left\|f-\mathsf T_{\log n}f\right\|_2^2
\ge0.
\tag{8.2}
$$

这里

$$
(\mathsf T_a f)(y)=f(y-a)
\tag{8.3}
$$

是 unitary translation。

## 8.2 prime power 的 Fibonacci shell factorization

取

$$
n=p^v,
\qquad
v=\sum_{k\in Z(v)}F_k
\tag{8.4}
$$

为 $v$ 的 canonical Zeckendorf 分解。因为 translations 构成交换群，

$$
\boxed{
\mathsf T_{v\log p}
=
\prod_{k\in Z(v)}
\mathsf T_{F_k\log p}.
}
\tag{8.5}
$$

这不是近似，而是精确因子分解。

## 8.3 跳跃能量的多尺度上界

设 $Z(v)=\{k_1,\ldots,k_r\}$。恒等式

$$
I-U_1\cdots U_r
=
\sum_{j=1}^{r}
U_1\cdots U_{j-1}(I-U_j)
\tag{8.6}
$$

与 unitary invariance 给出

$$
\left\|
(I-\mathsf T_{v\log p})f
\right\|_2
\le
\sum_{k\in Z(v)}
\left\|
(I-\mathsf T_{F_k\log p})f
\right\|_2.
\tag{8.7}
$$

再由 Cauchy–Schwarz：

$$
\boxed{
\left\|
(I-\mathsf T_{v\log p})f
\right\|_2^2
\le
r(v)
\sum_{k\in Z(v)}
\left\|
(I-\mathsf T_{F_k\log p})f
\right\|_2^2,
}
\tag{8.8}
$$

其中 $r(v)=|Z(v)|$。

因为 Zeckendorf 指标不相邻，

$$
r(v)=O(\log v).
\tag{8.9}
$$

所以任意 prime-power jump 可以被一个稀疏 Fibonacci shell family 上界。

## 8.4 为什么没有自动反向界

式 (8.8) 只有一个方向。多个 shell displacement 可能在总 translation 中相互抵消，因此一般不能由

$$
\|(I-\mathsf T_{v\log p})f\|_2
$$

恢复所有

$$
\|(I-\mathsf T_{F_k\log p})f\|_2.
$$

这又是一次结构信息逃逸：总位移只看见 Fibonacci 原子之和，而 shell energy 读取分解历史。

Zeckendorf normal form 通过“无相邻指标”消除了

$$
F_k+F_{k+1}=F_{k+2}
\tag{8.10}
$$

造成的局部命名冗余，但标量 translation 仍不保留原子分解。

真正的 reverse coercivity 必须加入至少一种额外结构：

- shell orthogonality；
- disjoint frequency support；
- positive Gram completion；
- ordered carry cocycle；
- 或 prime–Gamma 全局约束。

---

# 9. Zeckendorf 与 prime 横向能量的有限联合定理

## 9.1 prime cluster relation energy

固定有限 prime cluster

$$
\mathcal C=\{p_1,\ldots,p_m\}
\tag{9.1}
$$

和非负 pair weights $W_{ij}$。记

$$
\Delta\omega_{ij}
=
\log p_j-\log p_i.
\tag{9.2}
$$

定义 cluster log-frequency 二阶量

$$
\boxed{
\mathcal V_{\mathcal C}
=
\sum_{i<j}W_{ij}(\Delta\omega_{ij})^2.
}
\tag{9.3}
$$

若至少一个不同 prime pair 具有正权重，则

$$
\mathcal V_{\mathcal C}>0.
\tag{9.4}
$$

## 9.2 Zeckendorf 平均横向能量

定义

$$
\boxed{
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)
=
\frac1{M_Q}
\sum_{\eta\in\Omega_Q}
\sum_{i<j}W_{ij}
\sinh^2\!\left(
\delta E_Q(\eta)\Delta\omega_{ij}
\right).
}
\tag{9.5}
$$

由能量双射，也可写为

$$
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)
=
\frac1{M_Q}
\sum_{v=0}^{M_Q-1}
\sum_{i<j}W_{ij}
\sinh^2(\delta v\Delta\omega_{ij}).
\tag{9.6}
$$

### 定理 9.1　严格正性与唯一零相

若 $Q\ge1$ 且 $\mathcal V_{\mathcal C}>0$，则

$$
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)\ge0,
\tag{9.7}
$$

并且

$$
\boxed{
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)=0
\Longleftrightarrow
\delta=0.
}
\tag{9.8}
$$

#### 证明

每一项非负。若 $\delta\ne0$，取 $v=1$ 和一个 $W_{ij}>0$、$p_i\ne p_j$ 的 pair，则对应 $\sinh^2$ 严格为正。

### 定理 9.2　Zeckendorf–prime susceptibility factorization

在 $\delta=0$：

$$
\boxed{
\left.
\frac{d^2}{d\delta^2}
\mathscr E_{Q,\mathcal C}^{\perp}(\delta)
\right|_{\delta=0}
=
\frac{(M_Q-1)(2M_Q-1)}3
\mathcal V_{\mathcal C}.
}
\tag{9.9}
$$

#### 证明

因为

$$
\left.
\frac{d^2}{d\delta^2}
\sinh^2(a\delta)
\right|_{\delta=0}
=2a^2,
$$

而

$$
\frac1{M_Q}
\sum_{v=0}^{M_Q-1}v^2
=
\frac{(M_Q-1)(2M_Q-1)}6.
$$

故得结论。

### 推论 9.3　黄金深度放大律

因为 $M_Q=F_{Q+2}\asymp\varphi^Q$，

$$
\boxed{
\mathscr E_{Q,\mathcal C}^{\perp\prime\prime}(0)
\asymp
\varphi^{2Q}\mathcal V_{\mathcal C}.
}
\tag{9.10}
$$

所以在**均匀有限状态 ensemble** 中：

- Zeckendorf depth 提供指数增长的二阶放大；
- prime cluster 提供 log-frequency 方向方差；
- 二者在最低阶严格乘法分离。

这就是 Zeckendorf 与 PrimeGaps 在能量层真正相遇的位置。

---

# 10. Fibonacci–Lorentz shell tower

## 10.1 同一个复参数的圆周与双曲分量

对不同 primes $p,q$，令

$$
\Delta\omega=\log(q/p),
\qquad
z=\delta+i\frac\tau2.
\tag{10.1}
$$

项目已有复交替核给出

$$
\left|\sinh(z\Delta\omega)\right|^2
=
\sinh^2(\delta\Delta\omega)
+
\sin^2\!\left(\frac\tau2\Delta\omega\right).
\tag{10.2}
$$

在 Fibonacci shell $F_k$ 上定义

$$
a_k=zF_k\Delta\omega.
\tag{10.3}
$$

由于

$$
F_{k+1}=F_k+F_{k-1},
$$

有

$$
\boxed{
a_{k+1}=a_k+a_{k-1}.}
\tag{10.4}
$$

若令

$$
R_k=e^{a_k},
\tag{10.5}
$$

则

$$
\boxed{R_{k+1}=R_kR_{k-1}.}
\tag{10.6}
$$

这是一条精确的 multiplicative Fibonacci rapidity recurrence。

- 当 $\delta=0$ 时，$|R_k|=1$，得到圆周 phase tower；
- 当 $\delta\ne0$ 时，$|R_k|=e^{\delta F_k\Delta\omega}$，得到 hyperbolic radial tower。

因此：

$$
\boxed{
\text{时间相位与离线横向分裂，是同一 Fibonacci 复 rapidity 的虚部和实部。}
}
\tag{10.7}
$$

## 10.2 shell 横向能量

定义归一化 shell detector

$$
\mathcal E_k^{\perp}(\delta;p,q)
=
\sinh^2\!\left(
\delta F_k\log\frac qp
\right).
\tag{10.8}
$$

其零集为

$$
\mathcal E_k^{\perp}=0
\Longleftrightarrow
\delta=0
\tag{10.9}
$$

只要 $F_k>0$ 且 $p\ne q$。

## 10.3 临界 Zeckendorf 深度

令

$$
x=|\delta|\left|\log\frac qp\right|.
\tag{10.10}
$$

定义首次达到非微扰尺度的 shell：

$$
k_*(x)=\min\{k:F_kx\ge1\}.
\tag{10.11}
$$

由 Binet 渐近，

$$
\boxed{
 k_*(x)
=
\log_\varphi\frac{\sqrt5}{x}+O(1)
\qquad(x\downarrow0).
}
\tag{10.12}
$$

相应合法状态数满足

$$
\boxed{
M_{k_*}\asymp\frac1x
=
\frac1{|\delta|\,|\log(q/p)|}.
}
\tag{10.13}
$$

而所需信息熵为

$$
\boxed{
\log M_{k_*}
=
\log\frac1{|\delta|\,|\log(q/p)|}+O(1).
}
\tag{10.14}
$$

这给出一个精确 observer-resolution law：

- 横向偏移越小，需要越深的黄金 memory；
- prime log-gap 越小，需要越深的黄金 memory；
- 深度只对分辨率的对数增长，但状态数按其倒数增长。

若 $q=p+g$ 且 $g\ll p$，则

$$
\log(q/p)=\frac gp+O(g^2/p^2),
\tag{10.15}
$$

所以

$$
\boxed{
 k_*
=
\log_\varphi\frac{p}{|\delta|g}+O(1).
}
\tag{10.16}
$$

这正是 short-gap sticky grain 与 Zeckendorf depth 的定量接点。

---

# 11. 均匀状态 ensemble 与真实 Euler Gibbs ensemble 的分叉

式 (9.10) 容易诱发一个错误结论：因为状态数按 $\varphi^Q$ 增长，横向 susceptibility 按 $\varphi^{2Q}$ 增长，所以黄金递归自动产生相变。

该结论不成立，因为 susceptibility 还依赖状态测度。

## 11.1 均匀 ensemble

在式 (9.5) 中，每个 exponent $v\in[0,M_Q-1]$ 权重相同，因此

$$
\mathbb E_Q[v^2]
=
\frac{(M_Q-1)(2M_Q-1)}6
\asymp M_Q^2.
\tag{11.1}
$$

这确实产生黄金深度放大。

## 11.2 单 Euler 因子的 Gibbs ensemble

固定 $0<x<1$，对 $v\ge0$ 使用几何权

$$
\mu_x(v)=(1-x)x^v.
\tag{11.2}
$$

则

$$
\mathbb E_x[v^2]
=
\boxed{
\frac{x(1+x)}{(1-x)^2}
}<\infty.
\tag{11.3}
$$

取 $x=p^{-\sigma}$，对任一固定 prime 和 $\sigma>0$，该二阶矩有限。

所以在真实局部 Euler 权下，增加 Zeckendorf depth 并不会让单个 prime factor 的横向二阶响应发散。

### 定理 11.1　单局部因子无黄金深度相变

对固定 $p$ 与 $\sigma>0$，Zeckendorf exponent tower 在 Euler Gibbs 权下的二阶 exponent moment 随 $Q\to\infty$ 收敛到式 (11.3)，不按 $\varphi^{2Q}$ 发散。

因此：

$$
\boxed{
\text{组合状态数增长}
\not\Rightarrow
\text{Euler 加权能量增长}.
}
\tag{11.4}
$$

真正的临界现象若存在，必须来自：

- primes 数量随尺度增长；
- prime phases 的 collective alignment；
- Gamma／pole completion；
- analytic continuation 改变了有限局部 Gibbs 直觉；
- 或 zero-side 与 prime-side 之间的非局部谱输运。

---

# 12. 黄金 renormalization 可以稳定几何，却不能自动稳定质量

## 12.1 log-gap 与 Fibonacci shell 的互补缩放

固定 $P_0>0$ 和 additive gap $g>0$，令

$$
P_Q=P_0\varphi^Q.
\tag{12.1}
$$

则

$$
\boxed{
\lim_{Q\to\infty}
F_Q\log\left(1+\frac g{P_Q}\right)
=
\frac g{\sqrt5P_0}.
}
\tag{12.2}
$$

#### 证明

使用

$$
F_Q\varphi^{-Q}\to\frac1{\sqrt5}
$$

与

$$
\log(1+g/P_Q)\sim g/P_Q.
$$

因此若 prime scale 约乘 $\varphi$，同时 Zeckendorf shell 深度增加一层，则

$$
F_Q\Delta\log p
$$

可以保持非退化。

于是归一化横向能量具有有限极限：

$$
\sinh^2\!\left(
\delta F_Q\log(1+g/P_Q)
\right)
\longrightarrow
\sinh^2\!\left(
\frac{\delta g}{\sqrt5P_0}
\right).
\tag{12.3}
$$

这给出一个真正的 golden tangent fixed scale：

$$
\boxed{
\text{Fibonacci shell 增长 }\varphi^Q
\quad\text{抵消}\quad
\text{固定 additive gap 的 log-frequency 收缩 }\varphi^{-Q}.
}
\tag{12.4}
$$

## 12.2 但 Euler 质量超指数衰减

若同一个 $F_Q$ 被解释成 prime-power exponent，则对应 scalar Euler weight 包含

$$
P_Q^{-\sigma F_Q}
=
\exp\!\left(-\sigma F_Q\log P_Q\right).
\tag{12.5}
$$

由于

$$
F_Q\asymp\varphi^Q,
\qquad
\log P_Q\asymp Q,
$$

该权重按

$$
\exp(-cQ\varphi^Q)
\tag{12.6}
$$

超指数衰减。

所以：

$$
\boxed{
\text{归一化几何可以处在 fixed scale，
实际 Euler mass 却可以趋于零。}
}
\tag{12.7}
$$

这条结论非常重要。它说明 Zeckendorf–PrimeGap renormalization 目前只建立了几何／observer 分辨结构，尚未建立 zeta 配分权下的非消失贡献。

要形成真正的 multiscale sticky tower，必须另外证明 completion measure 对这些 shell 提供足够质量。该质量不能由状态数或归一化 kernel 自动生成。

---

# 13. 一阶信息消失、二阶能量显影的统一原理

## 13.1 抽象二次显影定理

设 $d$ 是一个在 involution 下变号的缺陷：

$$
d\longmapsto-d.
\tag{13.1}
$$

若标量 observable $A$ 对该 involution 不变，

$$
A(d)=A(-d),
\tag{13.2}
$$

且 $A$ 在 $0$ 可微，则

$$
\boxed{A'(0)=0.}
\tag{13.3}
$$

若 $A$ 解析，则其 Taylor 展开只含偶次项：

$$
A(d)=A(0)+a_2d^2+a_4d^4+\cdots.
\tag{13.4}
$$

所以被反射压掉的一阶有符号信息，第一种可由 invariant scalar 稳定读取的量通常是平方能量。

## 13.2 项目中的六个实例

### （一）reciprocal roots

$$
\log r+\log r^{-1}=0,
$$

但

$$
(\log r)^2+(\log r^{-1})^2>0.
$$

### （二）ordered holonomy

仓库已证一阶 observer response 为零，负二阶 response 是平方 winding 的非负加权和。

### （三）prime jump

共同 translation 模式被消去以后，剩余量为

$$
\|f-\mathsf T_af\|_2^2\ge0.
$$

### （四）prime transverse split

$$
\sinh^2(\delta\Delta\omega)
=\delta^2\Delta\omega^2+O(\delta^4).
$$

### （五）off-line zero odd channel

仓库已证 supplied 离线轨道的风险项为

$$
E_{\mathrm{odd}}
=4m_\rho|A_{\mathrm{odd}}|^2\ge0.
$$

### （六）golden innovation

$$
\sum\xi_v=O(1),
$$

而

$$
\frac1N\sum\xi_v^2\to\varphi^{-3}>0.
$$

这六个对象并不相等，但它们共享同一结构法则：

$$
\boxed{
\text{有符号／有序／反射信息在一阶 scalar 中冲销，
在二阶正能量中重新显影。}
}
\tag{13.5}
$$

这就是 Zeckendorf、jump energy、holonomy Casimir、Lee–Yang radial defect 和 off-line odd energy 真正相关的原因。

---

# 14. 假想离线零点的联合能量图景

设

$$
\rho_*
=
\frac12+\delta_*+it_*,
\qquad
\delta_*\ne0
\tag{14.1}
$$

是一个假想离线零点。

前一理论卷已经得到：

1. 同高度存在反射零点 $1-\overline{\rho_*}$；
2. Cayley 坐标中出现同角 reciprocal radial pair；
3. scalar visible energy
   
   $$
   V(t_*,\delta_*)=0;
   $$
4. 若中心非零，则发生 $\mathbb Z_2$ reflected phase split；
5. 若零点简单，则发生二次 gap closing、相位翻转和局部涡旋。

另一方面，对任意不同 primes $p,q$：

$$
\sinh^2\!\left(
\delta_*\log\frac qp
\right)>0.
\tag{14.2}
$$

对任意非平凡有限 Zeckendorf depth 与 prime cluster：

$$
\mathscr E_{Q,\mathcal C}^{\perp}(\delta_*)>0.
\tag{14.3}
$$

于是形成一个严格的**并置事实**：

$$
\boxed{
\text{zero-side scalar value}=0,
\qquad
\text{independently defined finite relation detector}>0.
}
\tag{14.4}
$$

但“并置”不是“矛盾”。式 (14.4) 中两边目前没有 canonical identity 或 domination theorem 相连。

因此严谨表述只能是：

$$
\boxed{
\text{离线零点是一个 candidate scalar/relation coercivity-gap closing event。}
}
\tag{14.5}
$$

要把 candidate 变成 theorem，必须证明 relation detector 是 completed explicit formula 中 odd channel 的真实下界或等价范数。

---

# 15. 信息逃逸究竟发生在哪一层

## 15.1 不发生在 Zeckendorf state decode

因为 $E_Q$ 是双射，

$$
\ker(E_Q)=\Delta_{\Omega_Q}.
\tag{15.1}
$$

所以精确指数能量没有微观状态碰撞。

## 15.2 发生在结构到标量配分的投影

考虑带关系的模型类

$$
\mathfrak M=(\Omega_Q,E_Q,\mathcal R).
\tag{15.2}
$$

定义 scalar readout

$$
\Pi_{\mathrm{sc}}(\mathfrak M)
=
\sum_{\eta\in\Omega_Q}x^{E_Q(\eta)}.
\tag{15.3}
$$

它与 $\mathcal R$ 无关。于是任意两个不同关系结构

$$
\mathcal R_1\ne\mathcal R_2
\tag{15.4}
$$

只要共享同一个能量标号，就满足

$$
\Pi_{\mathrm{sc}}(\Omega_Q,E_Q,\mathcal R_1)
=
\Pi_{\mathrm{sc}}(\Omega_Q,E_Q,\mathcal R_2).
\tag{15.5}
$$

这就是一个非平凡 model-level kernel。

若模型空间只含这两个模型，则 scalar readout 对唯一非对角有序 pair 全部碰撞，信息逃逸率为 $1$。若再加入一个能区分 $\mathcal R_1,\mathcal R_2$ 的 Laplacian、Hankel、carry 或 holonomy readout，联合 kernel 退化为对角线，逃逸率降为 $0$。

因此：

$$
\boxed{
\text{Zeckendorf 的信息价值不在重新命名整数，
而在把被 scalar partition 遗忘的 CUT/FLOW 关系重新对象化。}
}
\tag{15.6}
$$

## 15.3 结构读出层级

可以把当前项目中的 readouts 排成：

$$
\begin{aligned}
\mathcal O_0&=\text{整数 exponent / scalar Euler factor},\\
\mathcal O_1&=\text{occupation polynomial / hard-core transfer},\\
\mathcal O_2&=\text{stable shadow / least-index parity},\\
\mathcal O_3&=\text{successor and arithmetic jump Dirichlet form},\\
\mathcal O_4&=\text{ordered holonomy / exterior pair energy},\\
\mathcal O_5&=\text{zero-side off-line odd spectral energy}.
\end{aligned}
\tag{15.7}
$$

它们不是简单的数值精度递增，而是在逐步恢复不同类型的关系：

- $\mathcal O_0$：值；
- $\mathcal O_1$：一步记忆；
- $\mathcal O_2$：Galois 稳定修正；
- $\mathcal O_3$：动态创新；
- $\mathcal O_4$：cross-prime 顺序与二体关系；
- $\mathcal O_5$：zero orbit 的反对称谱风险。

低信息逃逸的最终对象不应选择其中一个替代其余，而应证明哪些层通过 canonical morphism 可以互相恢复。

---

# 16. 两个等价风格的最终开放桥

## 16.1 能量支配形式

需要构造 canonical 权重和完成映射，使

$$
\boxed{
E_{\mathrm{off}}^{\mathrm{odd}}(g)
\le
C\Bigl(
E_{\mathrm{jump}}^{\mathrm{Zeck}}(g)
+
E_{\mathrm{hol}}^{\mathrm{gold}}(g)
+
E_{\mathrm{prime}}^{\perp}(g)
\Bigr)
+\varepsilon(g).
}
\tag{16.1}
$$

并在受控极限中证明

$$
\varepsilon(g)\to0.
\tag{16.2}
$$

式 (16.1) 目前是目标，不是定理。三种 prime-side energy 也不能在未给出共同 Hilbert space 和嵌入以前直接相加；严格版本必须先把它们运输到同一有限 Galerkin 空间。

## 16.2 transfer equimodular confinement 形式

另一种表达是构造 canonical completed prime–Zeckendorf transfer cocycle，其两个主通道具有 Lyapunov exponents

$$
L_+(s),\qquad L_-(s).
\tag{16.3}
$$

Zeckendorf hard-core 原型说明，有限配分零点发生在两个 transfer channels 等模并满足相位量子化的位置。

因此可提出：

### 猜想 16.1　Arithmetic equimodular confinement

对 canonical completed cocycle，

$$
\boxed{
L_+(s)=L_-(s)
\Longrightarrow
\Re s=\frac12.
}
\tag{16.4}
$$

并且 completed determinant 的零点只能出现在该等模集合上。

若两部分均建立，则推出 RH。

这条猜想把三种语言统一：

$$
\boxed{
\begin{aligned}
\text{Weil 语言}&:\text{odd energy 不产生负性},\\
\text{Lee–Yang 语言}&:\text{根不离临界圆},\\
\text{transfer 语言}&:\text{等模集合被限制在反射固定轴}.
\end{aligned}
}
\tag{16.5}
$$

## 16.3 为什么 Zeckendorf 是候选而非答案

Zeckendorf 提供了：

- 唯一 hard-core normal form；
- 最小二态记忆；
- 扩张／稳定 Galois 通道；
- 稀疏 Fibonacci shell factorization；
- 精确 balanced innovation；
- 与 prime log-gap 互补的尺度增长。

但它尚未提供：

- canonical zeta transfer operator；
- Gamma completion channel；
- prime-pair energy 的真实全局权；
- zero-side odd energy 的无条件支配；
- 极限紧性和测试族分离性。

所以最准确的判断是：

$$
\boxed{
\text{Zeckendorf 给出了 RH 相变问题可能需要的最小 memory geometry，
但没有自动给出该 geometry 在 completed }\Xi\text{ 中的动力学权。}
}
\tag{16.6}
$$

---

# 17. 新的统一理论：黄金隐藏通道临界性

前述结构可压缩为一个理论图：

$$
\boxed{
\begin{array}{ccccc}
\text{integer exponent}
&\xrightarrow{\text{Zeckendorf}}
&\text{hard-core history}
&\xrightarrow{\text{Galois split}}
&(\varphi\text{-expanding},\psi\text{-stable})
\\[2mm]
&&\downarrow\text{successor / carry}
&&\downarrow\text{quadratic reveal}
\\[2mm]
\text{scalar Euler}
&\xleftarrow{\text{forget relation}}
&\text{jump energy}
&\longrightarrow
&\text{prime exterior energy}
\\[2mm]
&&&&\downarrow\text{missing transport}
\\[2mm]
&&&&\text{off-line odd energy}.
\end{array}
}
\tag{17.1}
$$

这里最深的结构不是“所有对象数值相等”，而是：

1. 标量读出反复删除有符号关系信息；
2. 被删除的信息在稳定／反对称通道中保留；
3. 对称性使一阶读出归零；
4. 第一忠实读出成为正的二阶能量；
5. 相变发生在 scalar gap 闭合而二阶 relation mode 仍存活的位置。

据此，可以把假想第一离线高度重新表述为：

$$
\boxed{
T_{\mathrm{off}}
=
\text{completed scalar channel 首次允许零值，
同时一个尚未被证明可输运的稳定 relation channel 仍可能携带正能量的高度}.
}
\tag{17.2}
$$

而 RH 的黄金隐藏通道版本是：

$$
\boxed{
\text{completed prime–Gamma dynamics 不允许任何 Zeckendorf／holonomy 稳定影子
在反射固定轴外与主通道达到可产生零点的等模状态}.
}
\tag{17.3}
$$

式 (17.3) 是研究纲领，不是已证等价；其成为严格 RH 等价的前提，是完成第 16 节的 canonical transfer/determinant 构造。

---

# 18. 结论地位总表

| 结论 | 地位 |
|---|---|
| 合法 Zeckendorf words 与 $[0,F_{Q+2})$ 双射 | 仓库机器闭合 |
| 有限 Zeckendorf exponent partition 是几何级数 | 仓库机器闭合 |
| 其非平凡根在局部 fugacity 单位圆 | 直接推论 |
| 该圆等于 RH Cayley 临界圆 | 不成立 |
| Zeckendorf 重编码改变单 Euler factor | 不成立 |
| hard-core occupation partition 满足二阶递推 | 纯有限定理 |
| $z=1$ 的 transfer eigenvalues 为 $\varphi,-\varphi^{-1}$ | 纯有限定理 |
| hard-core zeros 位于负实轴并趋向 $-1/4$ | 纯有限定理 |
| Fibonacci count sequence 的最小 realization dimension 为 $2$ | 有限证明 + 仓库 Hankel 定理 |
| 黄金指数增量取 $\varphi^2$ 或 $\varphi$ | 仓库机器闭合 |
| 扣除 $\sqrt5$ 后创新均方为 $\varphi^{-3}$ | 本文直接推论 |
| prime-power translation 有 Zeckendorf shell 精确因子分解 | 本文有限定理 |
| 总 jump energy 自动下界每个 shell energy | 不成立；只有上界 |
| Zeckendorf–prime susceptibility 二阶乘法分离 | 本文有限定理 |
| 均匀状态 susceptibility 按 $\varphi^{2Q}$ 增长 | 本文直接推论 |
| 单 Euler Gibbs ensemble 同样发散 | 不成立；二阶矩有限 |
| Fibonacci shell 可补偿 short log-gap 的几何收缩 | 本文条件极限定理 |
| 该补偿自动克服 Euler mass 衰减 | 不成立 |
| scalar first-order cancellation 与 quadratic energy reveal 是共同机制 | 抽象定理 + 多个仓库实例 |
| prime transverse energy 已支配 off-line odd energy | 尚未建立 |
| canonical transfer 的等模集合只在临界线 | 新核心猜想 |
| 本文证明 RH | 不成立 |

---

# 19. 最终收束

Zeckendorf、黄金比例、能量、Lee–Yang 和离线零点确实属于同一张结构图，但它们的关系不是：

$$
\text{出现 }\varphi
\Longrightarrow
\mathrm{RH}.
$$

真正的关系是：

$$
\boxed{
\begin{aligned}
\text{Zeckendorf 唯一性}
&\Longrightarrow
\text{整数指数可无损提升为 hard-core history},\\
\text{hard-core history}
&\Longrightarrow
\text{最小二态 transfer 与 }(\varphi,-\varphi^{-1})\text{ 双通道},\\
\text{稳定影子}
&\Longrightarrow
\text{有界一阶校正与正二阶创新能量},\\
\text{prime log-gap}
&\Longrightarrow
\text{同一复核中的时间相位与横向 }\sinh^2\text{ 能量},\\
\text{Zeckendorf depth}\times\text{prime variance}
&\Longrightarrow
\text{有限横向 susceptibility},\\
\text{scalar completion}
&\Longrightarrow
\text{这些关系量可能被压缩或冲销},\\
\text{off-line zero}
&\Longrightarrow
\text{若存在，则 scalar zero 与正 relation detector 在同一高度并置}.
\end{aligned}
}
\tag{19.1}
$$

最后一步还不是矛盾，因为 canonical transport 尚未建立。

因此本理论的最终命题是：

$$
\boxed{
\textbf{RH 的潜在黄金机制，不是 Fibonacci 数值神秘地控制零点，
而是最小 hard-core memory 的稳定影子能否在 prime–Gamma 完成后
被一个正二阶能量完全审计。}
}
\tag{19.2}
$$

若审计完成，则所有反射轴外的 odd relation mode 都必须付出正能量，而 completed scalar zero 无法在该能量仍为正时发生。若审计不能完成，则 Zeckendorf 仍只是一个优美、无损、但与 RH 承重桥分离的坐标系统。

这把下一步研究压缩成唯一问题：

$$
\boxed{
\text{能否从 canonical Zeckendorf carry / golden holonomy / prime jump energy
构造一个由显式公式识别的正算子，
其零空间恰好等于 critical-line phase，
其正空间恰好包含全部 off-line odd modes？}
}
\tag{19.3}
$$

在这条算子桥闭合以前，所有“黄金比例解释 RH”的表述都只能是结构候选；在它闭合以后，Zeckendorf 才会从命名坐标真正升级为 completed zeta 的动力学内核。