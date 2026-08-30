# 黄金素数圆、电荷层析与临界谱理论
## Golden Prime-Circle, Charge Tomography and Critical Spectrum Theory

**版本：** v0.1  
**日期：** 2026-08-30  
**仓库基线：** `dev@51df880637a420c8a973989a0b1c80e704d6fd1c`

> **文档地位。** 本文是理论输入与机器 owner 的解释性索引。Lean 声明及其
> proof term 是唯一数学真源。本文没有证明黎曼猜想，也没有把坐标重写、有限
> 电荷层析、局部 Euler 恒等式或反射配对平衡扩大为 RH 证明。
>
> **来源关系。** 本文承接 `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY`
> 中完成点、完成线程、第一非零 jet 与观察者身份的分层，并承接
> `GOLDEN_OBSERVER_RH_ROUTE` 对 Weil、Li、Cayley、谱正性与未闭合桥梁的边界。
>
> **本轮原则。** 先把可以无条件闭合的代数、函数、坐标和观察者命题写成
> Lean。有关无限 Euler 乘积、显式公式、Dirichlet `L` 值、Frobenius 层析、
> 素数圆稠密性、Weil 完备 frame 与 RH 的命题继续明确登记为条件层或开放层。

---

## 摘要

本文把此前关于“zeta 是压缩”“黄金壳共享电荷但不是同一个观察者”“函数
方程只保证成对平衡，而 RH 要求逐模态中性”的讨论拆成一条严格的观察者链：

\[
\boxed{
\text{split/inert 局部状态}
\longrightarrow
(\text{neutral},\text{charge})
\longrightarrow
\text{局部 Euler 通道}
\longrightarrow
\text{黄金尺度坐标}
\longrightarrow
\text{临界谱圆}
\longrightarrow
\text{配对平衡与逐点酉性的分离}.
}
\]

第一层是二元电荷的有限 Fourier 层析。若 `S` 与 `I` 分别记录 split 与 inert
通道，则：

\[
N=S+I,
\qquad
C=S-I.
\]

反演为：

\[
S=\frac{N+C}{2},
\qquad
I=\frac{N-C}{2}.
\]

因此中性通道单独有损，而中性通道与黄金二次电荷通道联合后是忠实坐标。

第二层是局部 Euler 因子。定义形式局部变量 `X` 与电荷
`χ\in\{1,-1,0\}`：

\[
Z_\chi(X)
=
\frac{1}{(1-X)(1-\chi X)}.
\]

则：

\[
\boxed{
\begin{aligned}
\chi=1
&\Longrightarrow
Z_\chi(X)=(1-X)^{-2},\\
\chi=-1
&\Longrightarrow
Z_\chi(X)=(1-X^2)^{-1},\\
\chi=0
&\Longrightarrow
Z_\chi(X)=(1-X)^{-1}.
\end{aligned}
}
\]

第三层是黄金尺度。令：

\[
L_\varphi=2\log\varphi.
\]

对正实尺度定义：

\[
\ell_\varphi(x)=\frac{\log x}{L_\varphi}.
\]

它满足：

\[
\ell_\varphi(xy)=\ell_\varphi(x)+\ell_\varphi(y),
\qquad
\ell_\varphi(\varphi)=\frac12,
\qquad
\ell_\varphi(\varphi^2)=1.
\]

第四层是临界谱坐标。定义：

\[
\boxed{
Z_\varphi(s)
=
\exp\left(
L_\varphi\left(s-\frac12\right)
\right).
}
\]

其模长是：

\[
\boxed{
|Z_\varphi(s)|
=
\exp\left(
L_\varphi\left(\Re s-\frac12\right)
\right).
}
\]

因此：

\[
\boxed{
|Z_\varphi(s)|=1
\iff
\Re s=\frac12.
}
\]

completed reflection：

\[
\mathcal R(s)=1-\overline s
\]

在该坐标中变为：

\[
\boxed{
Z_\varphi(\mathcal R s)
=
\frac{1}{\overline{Z_\varphi(s)}}.
}
\]

所以一个反射对的径向电荷乘积恒为一。这个成对平衡条件不能推出每个电荷
分别为一。本文用显式二通道传递矩阵证明，行列式为一仍可以同时包含一个增长
方向和一个衰减方向。逐点中性对应更强的等距条件。

---

# 1. 四种压缩必须分开

“zeta 是压缩”需要按信息类型拆分。

## 1.1 状态到电荷的压缩

设局部状态包含比 split/inert 标签更丰富的数据。二次字符只保留：

\[
\chi_5(p)\in\{1,-1,0\}.
\]

这是从完整局部代数状态到三值电荷的压缩。

## 1.2 电荷到中性通道的压缩

如果只保留：

\[
N=S+I,
\]

则：

\[
(S,I)=(1,0)
\quad\text{与}\quad
(S,I)=(0,1)
\]

给出相同的中性输出。中性通道不能重构电荷分配。

## 1.3 局部通道到全局解析对象的压缩

Euler 乘积把所有局部因子组织为一个解析函数。完整函数可以携带大量局部
系数信息；选择平凡字符或一个固定表示时，只读取该表示可见的局部通道。

## 1.4 反射配对的压缩

若法向电荷为 `δ` 与 `-δ`，偶观察者消去一次项：

\[
\delta+(-\delta)=0,
\]

同时保留：

\[
\delta^2+(-\delta)^2=2\delta^2.
\]

所以 completed reflection 可以隐藏有符号破缺，同时在二阶曲率、方差或奇异值
中留下影子。

这四种压缩的 kernel 不同。后续理论不得以一个统一的“有损”标签代替逐层
kernel 审计。

---

# 2. 黄金二元电荷的完整层析

## 2.1 分析映射

定义：

\[
\mathcal F_2(S,I)
=
(S+I,S-I).
\]

第一坐标是中性通道，第二坐标是二次电荷通道。

## 2.2 反演映射

定义：

\[
\mathcal F_2^{-1}(N,C)
=
\left(
\frac{N+C}{2},
\frac{N-C}{2}
\right).
\]

机器层证明：

\[
\mathcal F_2^{-1}\mathcal F_2=\operatorname{id},
\qquad
\mathcal F_2\mathcal F_2^{-1}=\operatorname{id}.
\]

所以联合通道是双射。

## 2.3 观察者解释

\[
\boxed{
\text{neutral channel}
=
\text{总量观察},
}
\]

\[
\boxed{
\text{charge channel}
=
\text{split/inert 极化观察}.
}
\]

在黄金二次扩张的未分歧局部模型中，这两个通道足以恢复二元分裂群体。
该结论是有限线性层析。它不声称仅凭有限个函数值就能恢复完整无限素数序列。

---

# 3. 黄金局部 Euler 三分律

令：

\[
Z_\chi(X)
=
\frac{1}{(1-X)(1-\chi X)}.
\]

## 3.1 split

当 `χ=1`：

\[
Z_1(X)
=
\frac1{(1-X)^2}.
\]

两个相同的一次局部方向被保留。

## 3.2 inert

当 `χ=-1`：

\[
Z_{-1}(X)
=
\frac1{(1-X)(1+X)}
=
\frac1{1-X^2}.
\]

两个共轭方向在底层观察者中合成为一个二次通道。

## 3.3 ramified

当 `χ=0`：

\[
Z_0(X)
=
\frac1{1-X}.
\]

非平凡字符因子在分歧位置退化。

## 3.4 与现有黄金素数分类的连接

仓库现有 `GoldenPrimeClassification` 已经承担
`p mod 5` 与 split/inert/ramified 的算术分类。本轮 owner 只承担上述形式 Euler
恒等式，避免重新证明或复制素数分类。

---

# 4. 同样电荷不等于同一个观察者

设底层对象为 `X`，公共电荷为：

\[
c:X\to C.
\]

第 `r` 个壳层观察者为：

\[
q_r:X\to Y_r.
\]

若存在解码器：

\[
d_r:Y_r\to C
\]

满足：

\[
\boxed{
d_r\circ q_r=c,
}
\]

则所有壳都读取同一个电荷。

但：

\[
\ker q_r
\]

可以随 `r` 改变。有的壳保留隐藏坐标，有的壳只保留电荷。因此：

\[
\boxed{
\text{共享电荷商}
\neq
\text{观察者同一}.
}
\]

机器层给出一个显式有限反例。身份壳读取一个布尔对的两个坐标，电荷壳只读取
第一坐标。两者解码为同一电荷；身份壳单射，电荷壳非单射。

---

# 5. 黄金尺度字符

## 5.1 定义

\[
L_\varphi=2\log\varphi,
\qquad
\ell_\varphi(x)=\frac{\log x}{L_\varphi}
\quad(x>0).
\]

## 5.2 乘法变加法

\[
\boxed{
\ell_\varphi(xy)
=
\ell_\varphi(x)+\ell_\varphi(y).
}
\]

因此每个正素数 `p` 提供一个尺度步长：

\[
\ell_\varphi(p)
=
\frac{\log p}{2\log\varphi}.
\]

整数的素因子指数在该坐标中相加。

## 5.3 黄金周期

\[
\ell_\varphi(\varphi)=\frac12,
\qquad
\ell_\varphi(\varphi^2)=1.
\]

所以：

\[
x\mapsto\varphi^2x
\]

对应尺度坐标平移一。

## 5.4 本轮没有宣称的内容

若进一步模掉整数平移，可以构造尺度圆。证明正有理乘法群到该圆的忠实嵌入，
以及证明其像的稠密性，需要显式建立 quotient circle、整数幂 kernel 和有限精度
分离接口。本轮只关闭其无商版本的加法尺度律。

---

# 6. 黄金临界谱坐标

## 6.1 定义

\[
Z_\varphi(s)
=
\exp\left(
L_\varphi(s-1/2)
\right).
\]

其径向电荷定义为：

\[
Q_\varphi(s)
=
\exp\left(
L_\varphi(\Re s-1/2)
\right).
\]

机器层证明：

\[
|Z_\varphi(s)|=Q_\varphi(s)>0.
\]

## 6.2 临界线与单位圆

因为 `L_φ>0` 且实指数函数单射：

\[
\boxed{
Q_\varphi(s)=1
\iff
\Re s=1/2.
}
\]

等价地：

\[
\boxed{
|Z_\varphi(s)|=1
\iff
\Re s=1/2.
}
\]

这是坐标定理。它把临界线问题运输为单位圆支撑问题，没有加入零点位置的新
正性或谱纯性。

## 6.3 临界带与黄金环域

若：

\[
0<\Re s<1,
\]

则：

\[
\boxed{
\varphi^{-1}
<
|Z_\varphi(s)|
<
\varphi.
}
\]

所以开放临界带映入黄金环域。

## 6.4 completed reflection

令：

\[
\mathcal R(s)=1-\overline s.
\]

机器层证明：

\[
Q_\varphi(\mathcal R s)=Q_\varphi(s)^{-1},
\]

以及：

\[
Z_\varphi(\mathcal R s)
=
\overline{Z_\varphi(s)}^{-1}.
\]

所以反射伙伴具有倒数径向电荷。

---

# 7. 成对平衡与逐模态中性

## 7.1 函数方程型配对只给出乘积守恒

对任意 `s`：

\[
\boxed{
Q_\varphi(s)Q_\varphi(\mathcal R s)=1.
}
\]

这允许：

\[
Q_\varphi(s)>1,
\qquad
Q_\varphi(\mathcal R s)<1.
\]

所以反射对整体平衡仍可以包含增长与衰减分裂。

## 7.2 二通道传递

定义：

\[
M(q)
=
\begin{pmatrix}
q&0\\
0&q^{-1}
\end{pmatrix},
\qquad q>0.
\]

机器层证明：

\[
\det M(q)=1.
\]

同时：

\[
\boxed{
M(q)\text{ 保持欧氏平方范数}
\iff
q=1.
}
\]

取 `q=2` 得到显式反例：行列式等于一，但传递不是等距。

## 7.3 RH 的坐标化含义

对任意候选零点集 `Z`，定义：

\[
\operatorname{Critical}(Z)
\iff
\forall\rho\in Z,
\Re\rho=1/2,
\]

以及：

\[
\operatorname{GoldenUnitary}(Z)
\iff
\forall\rho\in Z,
|Z_\varphi(\rho)|=1.
\]

机器层证明：

\[
\boxed{
\operatorname{Critical}(Z)
\iff
\operatorname{GoldenUnitary}(Z).
}
\]

对于 completed zeta 的非平凡零点集，把 `Z` 实例化为该集合便得到 RH 的黄金
单位圆重写。实例化本身需要复用仓库现有 completed-zeta 零点载体；本轮没有将
坐标等价写成新的 RH 证明声明。

---

# 8. 算术与谱反射之间需要真正的 intertwiner

黄金算术共轭和临界谱反射都具有 `C₂` 型奇偶分解，但两个抽象 `C₂` 同构不足以
证明二者表达同一电荷。

设：

\[
\sigma:X\to X,
\qquad
\tau:Y\to Y
\]

为两个 involution。真正的桥需要：

\[
\boxed{
B\circ\sigma
=
\tau\circ B.
}
\]

机器层证明：

1. 若 `σx=x`，则 `τ(Bx)=Bx`；
2. 若 `B` 为加法同态且 `σx=-x`，则 `τ(Bx)=-Bx`；
3. 若 `B` 单射，目标偶性可以反射回源偶性；
4. 常值桥也可以满足 intertwining，却删除全部源奇偶信息。

因此以后把黄金 Galois 电荷与临界法向电荷认作同一结构时，至少需要给出：

\[
\boxed{
\text{intertwiner}
+
\text{非退化性或忠实性}
+
\text{来源自然性}.
}
\]

该 arithmetic-to-spectral intertwiner 当前仍开放。

---

# 9. zeta、L 函数与导数的严格位置

本文支持以下结构解释：

\[
\boxed{
\zeta
=
\text{素数系统的中性 Euler 通道},
}
\]

\[
\boxed{
L(s,\chi_5)
=
\text{黄金二次电荷通道},
}
\]

以及：

\[
\boxed{
-\frac{L'}{L}
=
\text{该全局通道的局部事件流读出}.
}
\]

最后一式的无限级数、收敛域和素数幂系数展开没有在本轮重新形式化。仓库已有
大量 Euler、Weil、显式公式和局部到全局模块，后续应优先复用并证明一个有限
黄金尺度采样定理，再处理无限极限。

建议的下一机器链为：

```text
D5/S3/PrimeObserver/GoldenScale/
  GoldenScaleCircleQuotient.lean
  PositiveRationalGoldenPhaseKernel.lean
  GoldenPrimePhaseDensity.lean

D5/S3/Analytic/Zeta/GoldenFourier/
  FinitePrimePowerMeasure.lean
  FiniteGoldenFourierCoefficient.lean
  LogDerivativeSamplingCertificate.lean

D5/S3/Weil/GoldenShellFrame/
  GoldenTranslatedTestFamily.lean
  GoldenDilatedTestFamily.lean
  GoldenFrameCompletenessTarget.lean
  GoldenWeilPositivityTransfer.lean
```

其中第三组的完备性与全测试空间正性仍是开放证明义务。

---

# 10. 机器 owner 映射

| 理论对象 | Lean owner | 状态 |
|---|---|---|
| 黄金临界坐标、单位圆、反射、环域 | `D5/S3/Analytic/Zeta/GoldenSpectrum/GoldenCriticalCoordinate` | 本轮目标 |
| 任意谱集的临界支撑与黄金酉支撑等价 | `D5/S3/Analytic/Zeta/GoldenSpectrum/GoldenCriticalSupportCriterion` | 本轮目标 |
| 反射配对 determinant 与 isometry 分离 | `D5/S3/Analytic/Zeta/GoldenSpectrum/ReflectionPairTransfer` | 本轮目标 |
| 二元 neutral/charge 层析 | `D5/S3/PrimeObserver/ChargeTomography/GoldenC2ChargeTomography` | 本轮目标 |
| 同电荷、异观察者 | `D5/S3/PrimeObserver/ChargeTomography/SharedChargeDifferentShells` | 本轮目标 |
| split/inert/ramified Euler 恒等式 | `D5/S3/Analytic/Zeta/GoldenEuler/GoldenLocalEulerFactorTrichotomy` | 本轮目标 |
| 黄金乘法尺度的加法化 | `D5/S3/PrimeObserver/GoldenScale/GoldenLogScaleCharacter` | 本轮目标 |
| involution 奇偶通道运输 | `D5/S3/Observer/Bridges/InvolutionIntertwinerParity` | 本轮目标 |

---

# 11. 严格非主张

本轮没有证明：

1. 普通 RH 或任何 GRH；
2. completed zeta 的非平凡零点全部位于临界线；
3. 黄金坐标提供新的零点排除机制；
4. `L(1,χ₅)=2\log\varphi/\sqrt5`；
5. 正有理乘法群到黄金尺度圆的忠实嵌入；
6. 黄金素数相位在尺度圆上稠密；
7. 黄金垂直采样足以在所需函数空间内稳定恢复全部素数数据；
8. 算术 Galois involution 与临界谱 involution 之间存在自然忠实 intertwiner；
9. determinant 平衡可以推出逐模态酉性；
10. 有限黄金壳上的正性可以无条件延拓到完整 Weil 测试空间。

这些对象被保留为清晰的后续证明目标，不能由本轮已闭合的坐标恒等式偷渡。

---

# 12. 本轮结论

本轮可以安全冻结的理论骨架是：

\[
\boxed{
\begin{aligned}
&\text{中性通道单独丢失二元分裂电荷；}\\
&\text{中性通道与黄金电荷通道联合后完成二元层析；}\\
&\text{三种电荷值给出 split/inert/ramified 局部 Euler 形状；}\\
&\text{不同黄金壳可以读取同一电荷而保留不同 kernel；}\\
&\text{黄金尺度把正乘法变为加法，}\varphi^2\text{ 是一个完整周期；}\\
&\text{黄金临界坐标把临界线精确送到单位圆；}\\
&\text{completed reflection 只保证倒数配对与乘积平衡；}\\
&\text{逐模态单位模是更强的临界支撑条件；}\\
&\text{算术奇偶与谱奇偶要成为同一电荷，仍需忠实 intertwiner。}
\end{aligned}
}
\]

这使后续推理可以从机器关闭的坐标、层析和配对定理出发，集中攻击真正未闭合
的三条桥：黄金尺度圆的忠实低维编码、显式公式中的黄金 Fourier 运输，以及从
配对平衡到逐模态酉性的正性机制。
