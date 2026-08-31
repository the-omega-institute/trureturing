# RH_RESEARCH_LANE_THEORY

## 累积式 RH 研究真理卷

本文件是 `trureturing` 中 RH 研究路线唯一的累积理论文档。后续理论进展只在本文件中追加、修订和标注状态，不再为每个研究波次创建新的 `docs/develop/theory/*THEORY.md` 文档。每个独立 Lean 节点仍可保留仓库要求的 `Blueprint` Scribe 真源与确定性 Markdown 投影。

当前追加基线：`dev` 提交 `6aef3e41d2365d365fd3de24f44f4ba2a8779f96`。

本卷不是 RH 证明声明。它用于区分已经机器闭合的事实、定义性重写、候选桥梁、开放义务、误差预算和目标泄漏风险。

---

## 0. 状态语言

本卷统一使用以下状态：

- **Frozen**：已经存在于 `dev` 的 Lean proof term。
- **Candidate**：当前 PR 中已经给出 Lean 形式化，尚待仓库 admission 或合并。
- **Derived**：可以由 Frozen/Candidate 定理直接推出，但尚未拥有独立 Lean 名称。
- **Bridge target**：连接两个已经形式化对象所需的精确新定理。
- **Open**：当前没有证明，不得作为后续定理的无标注前提。
- **Consumer from RH**：以 RH 或 RH 等价性质为前提，只能用于后果分析，不能作为朝向 RH 的证明边。

RH 路线中的每一个承重命题都应记录：

1. 输入对象来自哪里；
2. 是否使用 RH 或已知等价命题；
3. 结论方向；
4. 有限证书及其严格裕量；
5. 截断、尾项和运输误差；
6. 第一条尚未闭合的边。

---

## 1. 研究主架构

当前 RH 研究被拆成三类彼此独立的桥。

### 1.1 反例检测桥

目标是证明：

\[
\neg\mathrm{RH}
\Longrightarrow
\exists\text{ finite certified negative witness}.
\]

候选观察图表包括：

- Cayley/Li 矩；
- Toeplitz 最小特征值；
- Pick negative square；
- normal jet；
- signed normal support；
- Chebyshev 负支撑分离器；
- Weil 紧支撑测试函数。

检测桥只说明离线零点最终可见。它不解释素数侧为何排除该离线零点。

### 1.2 算术强制桥

目标是从素数、Gamma、pole、边界项和窗口几何推出全部有限观察层非负。当前最精确的开放形式包括：

\[
\texttt{BalancedPrimePickInnovationLowerBound}
\]

和：

\[
\texttt{PrimeArchimedeanBlindSchurCoercivity}.
\]

这部分是目前最主要的 RH 承重开放边。

### 1.3 完成与全局化桥

目标是证明一致的有限正完成在统一预算和紧性条件下产生一个全局正谱对象。必须区分：

- 每个固定深度可行；
- 跨深度兼容；
- 统一 resolvent 预算；
- weighted weak-* 紧性；
- 全局正完成；
- 原子支撑与真实零点的进一步识别。

有限层逐层可行本身不足以推出全局对象。

---

## 2. 负性、负平方与负时间的强类型区分

“负”不是单一对象。它总是相对于某个正锥、允许支撑、二次型、稳定半平面或时间定向定义。

必须区分：

1. 负标量：\(a<0\)。
2. 负质量：signed measure 的某个权重为负。
3. 负支撑：正质量位于禁止区域，例如 \(x<0\)。
4. 负方向：存在 \(v\ne0\) 使 \(Q(v)<0\)。
5. negative square：有限 Hermitian Gram 矩阵拥有一个独立负方向。
6. 负指数：最大负定子空间的维数。
7. 负频率：Fourier 相位的反向绕行。
8. 负时间：相对于选定时间锥的反向参数、逆动力学或历史完成。

这些对象之间可以存在运输定理，不能直接互换。

### 2.1 正锥分离定义

设允许对象形成锥 \(C\)。如果对偶观察器 \(\ell\) 满足：

\[
\ell(c)\ge0\qquad(c\in C),
\]

而：

\[
\ell(x)<0,
\]

则 \(\ell\) 是对象 \(x\) 越过正锥边界的负性证书。

因此有限 RH 反例证书的最终形式应是：

\[
\boxed{
\ell\in C^\vee,
\qquad
\ell(X_\zeta)<-\eta,
\qquad
\eta>0.
}
\]

严格正裕量 \(\eta\) 用于吸收尾项和数值误差。

---

## 3. Frozen：反射增长对与负平方有符号行列式

当前 `dev` 的真源：

```text
D5/S3/Analytic/Adelic/ReflectedGrowthPairNegativeSquare.lean
```

定义反射增长对：

\[
G_\delta(t)
=
\left(e^{\delta t},e^{-\delta t}\right).
\]

已经机器证明：

\[
G_\delta(-t)=\operatorname{swap}G_\delta(t),
\]

\[
e^{\delta t}e^{-\delta t}=1,
\]

以及生成率对 \((\delta,-\delta)\) 满足：

\[
\operatorname{tr}=0,
\qquad
\det=-\delta^2.
\]

这里的 \(-\delta^2\) 是反射生成元的**有符号行列式**。它不是二次多项式的标准判别式。特征多项式为：

\[
(r-\delta)(r+\delta)=r^2-\delta^2,
\]

而标准判别式为：

\[
4\delta^2.
\]

所以：

\[
\boxed{
\text{signed determinant}=-\delta^2,
\qquad
\text{polynomial discriminant}=4\delta^2.
}
\]

函数方程型反射消除了线性方向标签，二阶平方大小仍然保留。

---

## 4. Candidate append 2026-08-31：反射增长对的二阶负谱

当前候选真源：

```text
D5/S3/Analytic/Adelic/ReflectedGrowthPairSecondOrderSpectrum.lean
```

该节点只依赖已经冻结的 `ReflectedGrowthPairNegativeSquare` 和 Mathlib 的实指数 iterated derivative 定理。

### 4.1 两条径向分支

定义：

\[
g_+(t)=e^{\delta t},
\qquad
g_-(t)=e^{-\delta t}.
\]

对任意 \(n\ge0\)：

\[
\frac{d^n}{dt^n}g_+(t)
=
\delta^n g_+(t),
\]

\[
\frac{d^n}{dt^n}g_-(t)
=
(-\delta)^n g_-(t).
\]

特别地：

\[
g_+''(t)=\delta^2g_+(t),
\qquad
g_-''(t)=\delta^2g_-(t).
\]

定义负二阶观察器：

\[
\mathcal L=-\frac{d^2}{dt^2}.
\]

于是：

\[
\boxed{
\mathcal Lg_+(t)=-\delta^2g_+(t),
\qquad
\mathcal Lg_-(t)=-\delta^2g_-(t).
}
\]

结合上一真源：

\[
\operatorname{reflectionPairSignedDeterminant}(\delta)
=-\delta^2,
\]

得到精确 observer agreement：

\[
\boxed{
\text{反射生成元的有符号行列式}
=
\text{负二阶算子的谱值}.
}
\]

这不是类比，而是同一个标量 \(-\delta^2\) 在有限生成元图表和微分算子图表中的完全相同读数。

### 4.2 分支遗忘后的对称读出

定义：

\[
S_\delta(t)
=
g_+(t)+g_-(t)
=
e^{\delta t}+e^{-\delta t}.
\]

该函数已经在前一真源中证明为偶函数。本轮进一步得到：

\[
S_\delta''(t)=\delta^2S_\delta(t),
\]

因此：

\[
\mathcal LS_\delta(t)
=-\delta^2S_\delta(t).
\]

对称观察没有删除负二阶谱值。它只删除了哪一支是增长、哪一支是衰减的方向标签。

### 4.3 一阶盲性与二阶可见性

在反射中心 \(t=0\)：

\[
S_\delta'(0)=0,
\]

而：

\[
\boxed{
S_\delta''(0)=2\delta^2.
}
\]

若 \(\delta\ne0\)，则：

\[
S_\delta''(0)>0.
\]

所以：

\[
\boxed{
\text{对称性压平一阶方向，二阶曲率仍严格检测分裂大小。}
}
\]

这个结论解释了为什么 normal observer 中奇数法向层容易因函数方程对称而消失，而偶数层仍然可能携带离线信息。

### 4.4 当前命题边界

本节点没有证明：

- 参数 \(t\) 是物理时间；
- completed zeta 已经实现为上述二分支系统；
- 任意离线零点已被有限测试函数隔离；
- 二阶局部信号能够压过其他零点、Gamma 因子或截断尾项；
- 负二阶谱值已经产生 Weil、Pick 或 Toeplitz 负方向；
- RH 或其否定。

它关闭的是一个纯表示桥：

\[
\boxed{
\text{reflected split}
\longrightarrow
\text{signed determinant }-\delta^2
\longrightarrow
\text{negative second-order spectral value}.
}
\]

---

## 5. 与 completed-xi normal jet 的关系

当前 `dev` 的 `NormalJetFormula` 已经从真实 completed-xi normal intensity：

\[
I(\delta,t)
=
\left|
\xi\left(\frac12+\delta+it\right)
\right|^2
\]

构造偶阶 Taylor 系数，并机器证明前若干 normal jet 的导数公式。

本轮二阶真源说明了一个局部模型：反射增长率 \(\pm\delta\) 的方向信息在对称和中消失，而平方大小 \(\delta^2\) 在二阶读出中出现。

仍缺少的精确桥是：

\[
\boxed{
\texttt{OffLineCurvatureModeIntertwiner}
}
\]

它应把 phase-flattened reflected zero mode 的二阶对数曲率与已有离线曲率 dipole：

\[
K_{\delta,\gamma}(t)
=
2\frac{(t-\gamma)^2-\delta^2}
{((t-\gamma)^2+\delta^2)^2}
\]

严格连接起来。

在该桥建立以前，以下关系只能标记为结构一致：

- 有符号行列式包含 \(-\delta^2\)；
- 负二阶谱值为 \(-\delta^2\)；
- curvature dipole 的负核心由 \((t-\gamma)^2-\delta^2<0\) 控制；
- signed normal support 候选位置为 \(-\delta^2\)。

---

## 6. 新的结构推论

### 6.1 双曲模式与圆周模式的分界

对二阶算子 \(-D^2\)：

- 振荡模式 \(e^{i\gamma t}\) 的谱值是 \(+\gamma^2\)；
- 反射增长模式 \(e^{\pm\delta t}\) 的谱值是 \(-\delta^2\)。

因此正平方和负平方分别对应：

\[
\boxed{
+\gamma^2
\leftrightarrow
\text{elliptic / oscillatory sector},
}
\]

\[
\boxed{
-\delta^2
\leftrightarrow
\text{hyperbolic / growth-decay sector}.
}
\]

在 RH 的局部模式语言中，临界线对应纯相位旋转。离线位移引入互反的增长与衰减分支。

### 6.2 二阶读出不恢复方向

\(S_\delta''(0)=2\delta^2\) 可以恢复分裂大小，但不能区分 \(\delta\) 和 \(-\delta\)。

因此观察语言分层为：

\[
(\delta,\gamma)
\longrightarrow
\delta
\longrightarrow
\delta^2.
\]

- 完整复模式保存径向方向和频率方向；
- 相位压平保存径向方向；
- 对称二阶观察只保存径向分裂大小。

若后续任务需要恢复时间定向或分支方向，必须增加奇通道，例如：

\[
O_\delta(t)
=
\frac{e^{\delta t}-e^{-\delta t}}{2}.
\]

### 6.3 负平方是稳定化债务

对候选负支撑位置：

\[
x=-\delta^2,
\]

Laplace 时间因子为：

\[
e^{-xt}=e^{\delta^2t}.
\]

要使：

\[
e^{-ut}e^{-xt}
=
e^{-(u-\delta^2)t}
\]

在正半轴可积，需要：

\[
\boxed{u>\delta^2.}
\]

因此可以定义候选稳定化债务：

\[
\operatorname{StabilizationDebt}(-\delta^2)=\delta^2.
\]

这一结论的积分、可积性当且仅当条件和 resolvent 极点仍需独立 Lean 真源。

---

## 7. 下一承重形式化方向

### P0. NegativeSquareLaplaceResolvent

在精确条件 \(u>\delta^2\) 下证明：

\[
\int_0^\infty e^{-(u-\delta^2)t}\,dt
=
\frac1{u-\delta^2}.
\]

并证明可积性阈值：

\[
\operatorname{IntegrableOn}
\left(e^{-(u-\delta^2)t},[0,\infty)\right)
\iff
u>\delta^2.
\]

该节点把负二阶谱值连接到前向增长、附加阻尼预算和 resolvent 极点。

### P1. ReflectedGrowthPairEvenOddObservation

定义偶通道和奇通道：

\[
E_\delta(t)
=
\frac{e^{\delta t}+e^{-\delta t}}2,
\qquad
O_\delta(t)
=
\frac{e^{\delta t}-e^{-\delta t}}2.
\]

目标：

\[
E_\delta(-t)=E_\delta(t),
\qquad
O_\delta(-t)=-O_\delta(t),
\]

\[
E_\delta(t)^2-O_\delta(t)^2=1.
\]

偶通道保存反射不变量。奇通道保存定向。

### P2. OffLineCurvatureModeIntertwiner

把反射模式的二阶对数曲率精确运输到离线 dipole 公式。该节点应明确：

- 目标轨道贡献；
- 其他零点污染；
- Gamma 与 pole 项；
- 正翼和负核心；
- 截断误差；
- 剩余严格负裕量。

### P3. SignedNormalSpectralAtom

构造一个真正的 signed-normal support chart，使临界线轨道落在允许支撑：

\[
[0,\infty),
\]

离线反射轨道产生正质量的负支撑位置：

\[
-\delta^2<0.
\]

随后用 Chebyshev 多项式或 rational separator 将负支撑运输成有限矩和 Gram 负方向。

---

## 8. 当前 theorem DAG

```text
ReflectedGrowthPairNegativeSquare                 Frozen
        |
        v
ReflectedGrowthPairSecondOrderSpectrum            Candidate
        |
        +-----------------------------+
        |                             |
        v                             v
Even/Odd Observation               NegativeSquareLaplaceResolvent
        |                             |
        v                             v
Orientation Recovery               Stabilization Debt / Resolvent Pole
        |                             |
        +---------------+-------------+
                        |
                        v
              OffLineCurvatureModeIntertwiner
                        |
                        v
                SignedNormalSpectralAtom
                        |
                        v
             Chebyshev Negative-Support Witness
                        |
                        v
             Toeplitz / Pick / Weil Negative Direction
```

并行的算术强制链仍为：

```text
Prime / Gamma / Pole data
        |
        v
Balanced finite observer innovation
        |
        v
Blind-sector Schur coercivity
        |
        v
All finite Gram layers nonnegative
        |
        v
Uniform positive completion
        |
        v
Weil positivity
        |
        v
RH
```

检测链和强制链最终需要在同一个有限 master observer 上相遇。

---

## 9. 当前第一开放边

就负平方与时间方向这一子路线而言，下一条最小且无条件的真源是：

\[
\boxed{
\texttt{NegativeSquareLaplaceResolvent}.
}
\]

就整个 RH 路线而言，第一承重开放边仍然不是上述表示恒等式，而是：

\[
\boxed{
\texttt{PrimeArchimedeanBlindSchurCoercivity}
}
\]

或等价的逐层素数侧创新下界。前者负责说明离线缺陷怎样产生有限负证书。后者负责说明真实算术数据为什么不允许该负证书存在。
