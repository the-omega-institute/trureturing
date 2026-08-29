# 动态无理完成、黄金切向喷流与临界曲率的形式化边界

**版本：v0.1，2026-08-29**

本文是 `OBSERVER_ADELIC_COMPLETION_CONSTANT_THEORY` 第 711–730 部的形式化伴随文档。目标是把其中的直觉拆成可独立检查的代数定理、分析定理、条件命题和开放项目桥，避免把局部模型、有限层伪零点线程或导数诊断误写成 completed `ξ` 的全局零点定理。

---

## 0. 四层真值结构

### A. 直接机器闭合层

这一层只使用实数代数、黄金比例恒等式、函数迭代、基本微分和显式有理函数计算：

1. 黄金 Möbius 映射
   \[
   T(x)=1+\frac1x
   \]
   的两个固定点为 `φ` 与 `ψ`；
2. 黄金 cross-ratio 坐标
   \[
   \kappa(x)=\frac{x-\varphi}{x-\psi}
   \]
   满足精确共轭关系
   \[
   \kappa(Tx)=-\varphi^{-2}\kappa(x);
   \]
3. 在正半轴上，迭代线程满足精确公式
   \[
   \kappa(T^n x)=(-\varphi^{-2})^n\kappa(x);
   \]
4. 逆 cross-ratio 完成曲线
   \[
   x_c(h)=\frac{\varphi-hc\psi}{1-hc}
   \]
   满足 `x_c(0)=φ`、`κ(x_c(h))=hc`，并且
   \[
   x_c'(0)=c(\varphi-\psi)=c\sqrt5;
   \]
5. 完成值映射在参数化黄金线程族上不是单射，因此完成点不能恢复线程参数；
6. 反射配对会精确消去奇通道，而平方或张量平方保留二阶信息；
7. 环境稳定模态 `ψ=-φ⁻¹` 与主模态 `φ` 的比值按 `-φ⁻²` 缩放；
8. 一对显式离线点的局部对数势具有可直接计算的二阶法向曲率核。

### B. 抽象分析层

这一层不绑定 Riemann `ξ`，先证明一般函数的结构：

1. 若 `V(-u,t)=V(u,t)` 且 `u ↦ V(u,t)` 在零点可微，则一阶法向导数为零；
2. 若具有足够高阶可微性，则所有奇阶法向导数为零；
3. 对显式局部势，二阶法向导数等于曲率偶极核；
4. Newton 向量与完成速度公式只在相应分母非零时定义。

### C. 条件解析层

以下结论需要把前提完整写入 theorem statement：

1. `F(τ,ρ(τ))=0` 的零点速度公式需要参数方向与空间方向的链式法则，并要求 `∂ₛF ≠ 0`；
2. 保持反射的简单零点留在线上，需要局部零点唯一性、参数连续或解析依赖，以及反射与参数族兼容；
3. 离线分支的出生需要重根，只能在相应局部唯一性框架下从简单根排除分岔；
4. 二次正规形需要非退化二阶与参数方向系数，并受高阶余项控制。

### D. 开放项目桥

以下内容继续保留为 conjecture 或 realization certificate：

1. 仓库中的规范 `F_{r,P,n,π}` 是否存在并收敛到 completed `ξ`；
2. 黄金项目化 forcing 是否具有统一收缩估计；
3. 曲率偶极能否从完整背景中稳定反演；
4. protozero 线程是否对应极限对象的真实谱分岔；
5. 任一结论是否足以推出或反驳 RH。

---

## 1. 必须补入的定义域纪律

### 1.1 Möbius 映射与 cross-ratio

在普通实数模型中，`T(x)=1+1/x` 的几何定义域排除 `x=0`，`κ(x)` 的几何定义域排除 `x=ψ`。Lean 中除法是总函数，若不显式加入这些条件，`x=0` 或 `x=ψ` 会被赋予代数上的总化值，产生与项目ive解释无关的退化恒等式。

因此机器定理采用以下两种方式之一：

- 在 `ℝ` 上显式携带 `x ≠ 0`、`x ≠ ψ`；
- 未来改用 `ProjectiveLine ℝ`，把 `0` 的极点和 `ψ` 的 cross-ratio 极点纳入真正的 Möbius 几何。

本批采用第一种方式。

### 1.2 完成线程

“完成点”是 Cauchy 线程的等价类；“完成线程”是一个具体代表。线程参数只有在指定缩放 `λ^n`、误差阶和规范化后才成为可恢复的 jet 数据。不能从任意收敛序列自动抽取唯一的“第一非零 jet”。

本批先对显式黄金线程族证明非重构。一般线程空间、Cauchy 商和 jet 分类留给后续模块。

### 1.3 第一破缺阶

定义

\[
k_* = \min\{k\ge1:\pi_N\gamma^{(k)}(0)\ne0\}
\]

需要：

1. `γ` 具有所需阶数的导数；
2. 法向投影已经定义；
3. 非零阶集合非空。

若第三项不成立，正确值应进入 `WithTop ℕ`，表示线程在全部有限 jet 上都与完成流形相切。后续形式化将优先使用带 `∞` 的版本。

---

## 2. 临界曲率的严格边界

对

\[
V(u,t)=\log\left|\xi\left(\tfrac12+u+it\right)\right|,
\]

所有微分恒等式只在 `ξ` 非零的开集上陈述。临界线零点处 `log|ξ|` 具有奇性，不能把零点外的普通导数 theorem 直接应用到零点。

离线对核

\[
2\frac{(t-\gamma)^2-\delta^2}{((t-\gamma)^2+\delta^2)^2}
\]

是两项显式局部对数势的二阶法向导数。它本身不等于完整 `ξ` 曲率，也不提供从总曲率到某一零点对的唯一反演。任何全局应用还需要：

1. Hadamard 或局部因子分解；
2. 其余零点与解析背景的控制；
3. 局部化误差界；
4. gauge 与截断顺序稳定性。

---

## 3. 离散速度的解释

对层级函数 `F_r`，

\[
-\frac{F_{r+1}(\rho_r)-F_r(\rho_r)}{F_r'(\rho_r)}
\]

首先是一次 Newton 预测量。它成为真实零点位移的渐近主项，需要额外证明：

1. `ρ_r` 为简单零点；
2. `F_{r+1}` 在邻域内存在对应零点；
3. 二阶余项统一可控；
4. 零点分支选择兼容。

因此形式化中将区分：

- `predictedDiscreteVelocity`：定义；
- `actualZeroDisplacement`：需要存在性；
- `velocityAsymptotic`：需要余项估计。

---

## 4. 本批机器目标

本批新增以下 owner：

```text
D5/S3/CompletionDynamics/GoldenMobius/
  GoldenMobiusMap.lean
  GoldenCrossRatioLinearization.lean
  GoldenProjectiveDerivative.lean
  GoldenThreadBlowup.lean

D5/S3/CompletionDynamics/DynamicReal/
  CompletionThreadFiber.lean

D5/S3/CompletionDynamics/ObserverJet/
  PairedOddJetCancellation.lean

D5/S3/PrimeObserver/ProjectiveMemory/
  GoldenProjectiveMultiplier.lean

D5/S3/Analytic/Zeta/CriticalCurvature/
  CriticalNormalEvenness.lean
  OffLinePairCurvatureKernel.lean
```

这些模块只承担本节 A 层以及 B 层的第一阶对称结论。`ξ` 的函数方程、全局曲率分解、zero-bifurcation IFT 和 RH 条件不进入本批无条件 theorem。

---

## 5. 与 observer completion 的连接

零阶完成读出只保留极限点；加入一阶 blow-up 读出后，接口从

\[
q_0(\mathfrak O)=x_\infty
\]

精化为

\[
(q_0,q_1)(\mathfrak O)=(x_\infty,c).
\]

这正是上一轮 `JointReadoutSupremum` 与 `AgencyEnrichment` 的一般 kernel 演算在黄金线程上的具体实例：

- `q₀` 的 fiber 包含所有到达同一完成点的线程；
- `q₁` 分离其中具有不同切向起源的线程；
- 联合 kernel 等于两个 kernel 的交；
- 完成值上的任何后处理都不能恢复已被 `q₀` 删除的 `c`。

因此“完成点相同，观察者起源不同”被解释为一个严格的接口精化事实，而不需要把观察者身份实体化为 completed 实数点之外的额外静态点。
