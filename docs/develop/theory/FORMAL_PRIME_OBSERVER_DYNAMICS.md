# 形式素数观察者动力学与局部—全局余量理论
## 素数尺度、CRT 联合、\(p\)-进精化、算术层析、行为完成与不可见全局身份
### Formal Prime-Observer Dynamics and Local–Global Remainder Theory

**作者：** Auric  
**机构：** The Omega Institute  
**日期：** 2026-08-21

> **文档地位。** 本文按照 `docs/develop/theory/FORMAL_CONCEPT_DYNAMICS.md` 的单卷、自包含、追加式与无暗账纪律，建立“素数观察者理论”的纸面内核与后续形式化摄入源。本文不是 Lean 数学真源。仓库已有结论以对应 Lean 声明为准；本文新增定义、定理与证明在获得 proof term、依赖闭包、admission 与冻结收据以前，不得标记为 `Closed`。
>
> **单卷约束。** 本理论的基础语言、静态观察、动态完成、局部—全局逻辑、二次型实例、CRT 与张量分解、\(p\)-进几何、solenoid 隐纤维、知识、行动、算法、反模型、Lean 路线及严格非主张全部保存在本文件中。未来修正采用追加式勘误、扩展或替代定理，不静默删除既有段落。
>
> **基础约束。** 本文把“素数观察者”定义为由素数或素数幂索引的局部读出接口，不把素数拟人化，不宣称素数具有意识、意向性或主观体验；也不声称世界本体必为 \(p\)-进、profinite、adelic、solenoid 或二次型结构。
>
> **证明分级。** 本文严格区分：`仓库锚点`、`纸面定理`、`有限证书`、`形式化目标`、`开放猜想`。引用仓库文件仅说明可复用的已核验部件，不表示本文全部结论已经形式化。
>
> **机械范围。** 本稿只生成一个 Markdown 理论文件，不修改 GitHub，不新增 Lean 源码、workflow、临时载荷或平行附录。

---

## 摘要

本文建立一套把素数局部算术、观察者商、动态预测与局部—全局缺陷统一起来的形式理论。其基本对象不是“有意识的素数”，而是一个由全局状态、准入谓词、实际锚点、过程族、素数尺度、局部输出与读出族组成的模型：

\[
\boxed{
\mathfrak P
=
\bigl(
X,\operatorname{Adm},a,U,F,
\mathcal I,O,q,\mathcal T
\bigr).
}
\]

局部索引通常取为：

\[
\mathcal I_{\mathrm{fin}}
=
\sum_{p:\mathbb P}\mathbb N_{>0},
\qquad
i=(p,k),
\]

其中 \(p\) 是素数，\(k\) 是 \(p\)-进精度。每个局部接口为：

\[
q_{p,k}:X\to O_{p,k}.
\]

有限观察预算 \(J\subset_{\mathrm{fin}}\mathcal I\) 的联合读出为：

\[
q_J(x)
=
\bigl(q_i(x)\bigr)_{i\in J},
\]

并规定相对同一性：

\[
x\sim_J y
\iff
q_J(x)=q_J(y)
\iff
\forall i\in J,\ q_i(x)=q_i(y).
\]

其余量纤维为：

\[
R_J(o)
=
\sum_{x:X}(q_J(x)=o).
\]

所有局部观察者共同仍无法消除的全局身份差异构成局部—全局余量：

\[
\operatorname{LGRes}(q)
=
\sum_{x,y:X}
(x\neq y)
\times
\prod_{i:\mathcal I}
(q_i(x)=q_i(y)).
\]

因此：

\[
\operatorname{LGRes}(q)=\varnothing
\iff
q_{\mathrm{all}}\text{ 单射}.
\]

本理论的第一条结构轴是：**不同素数之间为横向独立联合**。对互素模数，CRT 把全局有限窗口精确分解成素数幂坐标；在仓库已有窗口代数中，完整矩阵代数进一步分解为各素数幂矩阵代数的张量积。第二条结构轴是：**同一素数内部为纵向精度过滤**。读出 \(q_{p,k+1}\) 精化 \(q_{p,k}\)，二者不是独立张量因子，而是逆系统中的相邻层。

给定动力学 \(F:X\to X\)，定义素数—时间轨迹：

\[
\operatorname{PTr}(x)(i,n)
=
q_i(F^n x),
\]

以及动态不可区分关系：

\[
x\sim_J^{\infty}y
\iff
\forall n\in\mathbb N,\forall i\in J,
q_i(F^n x)=q_i(F^n y).
\]

它正是静态关系 \(\sim_J\) 的全迭代 congruence kernel。其商：

\[
Z_J^{\infty}
=
X/{\sim_J^{\infty}}
\]

是由这些素数接口决定的规范预测状态空间。有限状态下，若全部素数和全部未来足以区分状态，则存在一个**有限素数幂集合**与一个**有限时间深度**已经足以完成区分。本文称之为有限素数—时间层析定理。

二次算术给出另一种对偶读法。定义局部互反矩阵：

\[
\mathscr R(p,\Delta)
=
\left(\frac{\Delta}{p}\right)
\in\{-1,0,1\}.
\]

固定 \(p\) 时，它是“素数观察者读取判别式”；固定 \(\Delta\) 时，它是“判别式观察者读取素数分裂行为”。Gaussian、Eisenstein 与 Golden 三条已形式化分裂轴共同因子化通过 \(p\bmod 60\)，但其三比特分裂画像在 \((\mathbb Z/60\mathbb Z)^\times\) 上每个纤维恰有两个元素；加入一个模五定向位后才恢复完整模六十单位类。由此得到：

\[
\boxed{
\text{多种素数分裂知识}
\neq
\text{完整剩余类身份}.
}
\]

更一般地，所有只依赖判别式的分裂观察者不能区分同判别式的不同二次型类。本文给出判别式 \(-20\) 的显式反模型：

\[
Q_1(x,y)=x^2+5y^2,
\qquad
Q_2(x,y)=2x^2+2xy+3y^2.
\]

二者判别式相同，因而拥有相同的判别式分裂画像；但 \(Q_1\) 表示 \(1\)，\(Q_2\) 不表示 \(1\)，故二者不是同一个全局表示对象。这说明：

\[
\boxed{
\text{局部类型画像可以完备描述某种接口，}
\text{却仍留下全局类余量。}
}
\]

本文进一步证明或组织以下纸面结果：联合核交定理、观察集合单调精化、有限分离抽取、CRT 有界整数层析、信息容量下界、最小传感器集合覆盖等价、有限素数—时间层析、模 \(60\) 三环画像及其缺失位、crossing 相位的素数幂周期分解、\(p\)-进距离与首次分歧观察距离等价、局部命题知识的因子化刻画，以及有限 CRT 可胶合与一般局部—全局胶合不可偷渡之间的严格区分。

全文的基本方法是：

\[
\boxed{
\text{选择局部接口}
\to
\text{计算联合纤维}
\to
\text{寻找局部—全局缺陷}
\to
\text{加入最小精化}
\to
\text{完成动态行为商}
\to
\text{证明普适性质}.
}
\]

并始终保持：

\[
\boxed{
\text{局部可解}
\ne
\text{兼容局部族}
\ne
\text{可胶合}
\ne
\text{全局对象存在}
\ne
\text{全局对象唯一}.
}
\]

---

# 1. 仓库锚点、理论来源与边界

本文复用但不扩大解释范围的仓库锚点包括：

## 1.1 素数、二次型与 crossing 锚点

- `D5/S3/PrimeForms/GoldenPrimeClassification.lean`：判别式五轴上的 split / inert / ramified 分类；
- `D5/S3/PrimeForms/Splitting/EisensteinCriterion.lean`：判别式负三轴的剩余判据；
- `D5/S3/PrimeForms/SumTwoSquaresClassification.lean`：两平方表示分类；
- `D5/S3/PrimeForms/ThreeModFourDescent.lean`：三模四素数的下降引擎；
- `D5/S3/PrimeForms/Crossing/CrossingNormForm.lean`：crossing 型与 Eisenstein 范数值域的显式统一；
- `D5/S3/PrimeForms/Crossing/ExactPropagation.lean`：正锥 sandwich 的精确 winding-phase 传播；
- `D5/S3/PrimeForms/Crossing/WindingOrbitZero.lean`：偶非负相位轨道的唯一零点；
- `D5/S3/PrimeForms/CrossingPeriodicity/SandwichPhasePeriod.lean`：模十二的最小六步周期；
- `D5/S3/PrimeForms/PellFamilies/*.lean` 与 `BronzeLadderLeg.lean`：Pell 轨道与二次范数不变量。

## 1.2 观察者、记忆与预测锚点

- `D5/S3/ConceptDynamics/ConceptFiberDecomposition.lean`：概念读出的纤维分解；
- `D5/S3/ConceptDynamics/ConceptJoinUniversal.lean`：联合概念的普适性质；
- `D5/S3/Observer/Separation/CongruenceKernel.lean`：全迭代拉回给出最大前向 congruence；
- `D5/S3/ObserverMemory/Prediction/ItineraryCompletion.lean`：有限系统的未来 itinerary、逆极限与有限稳定深度；
- `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean`：受控行为商的规范最小实现；
- `D5/S3/ObserverMemory/Fusion/LeastCommonRefinement.lean`：多个观察商的最小共同精化；
- `D5/S3/Observer/Tomography/FiniteTimeTomography.lean`：有限维渐进观察塔的有限时间完备性；
- `D5/S3/Observer/MetricGeometry/DiscretePredictionUltrametric.lean`：离散未来读出距离的强三角不等式；
- `D5/S3/ConceptDynamics/PolicyCapabilityMonotonicity.lean`：读出精化扩大可实现策略集合；
- `D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff.lean`：精化降低目标风险并提高坐标成本。

## 1.3 CRT、素数幂张量与 solenoid 锚点

- `D5/S3/ObserverMemory/WindowRegisterCRT.lean`：互素窗口 clock / shift 的 CRT Kronecker 分解；
- `D5/S3/ObserverMemory/PrimePowerTensorTower.lean`：有限窗口全矩阵代数的全部素数幂张量分解；
- `D5/S1/Solenoid/ExactSequence.lean`：兼容同余数据恰为可见相位投影的隐藏核；
- `D5/S1/Solenoid/HiddenMotionRigidity.lean`：从连通区间到 \(\prod_p\mathbb Z_p\) 的连续路径必为常值；
- `D5/S1/Solenoid/StreamlineDecomposition.lean` 与相关路径分解文件：可见实流与固定隐藏余量的路径结构。

## 1.4 准确关系

\[
\boxed{
\text{已核验局部定理}
+
\text{本文定义性统一}
+
\text{本文纸面证明}
+
\text{未来 Lean 桥接层}.
}
\]

不得把已有文件名解释成本文总理论已被机器证明。

## 1.5 方法论禁令

### 禁令 1：禁止拟人化偷渡

\[
\boxed{
\text{“由素数索引的观察接口”}
\not\Rightarrow
\text{“素数具有意识”.}
}
\]

### 禁令 2：禁止局部到全局偷渡

\[
\boxed{
(\forall p,\exists x_p)
\not\Rightarrow
\exists x,\forall p.
}
\]

### 禁令 3：禁止把同判别式当作同一二次型类

\[
\boxed{
\operatorname{disc}(Q)=\operatorname{disc}(Q')
\not\Rightarrow
Q\simeq_{\mathrm{GL}_2(\mathbb Z)}Q'.
}
\]

### 禁令 4：禁止把 CRT 地址分解解释成任意物理独立性

\[
\mathbb Z/M\mathbb Z
\simeq
\prod_{p^e\parallel M}\mathbb Z/p^e\mathbb Z
\]

是算术等价；只有在已经证明相应代数或动力学映射也分解时，才能进一步谈算子、通道或策略的独立因子。

### 禁令 5：禁止把“所有当前局部读出相同”当作“未来行为相同”

必须另行证明动力学对该局部等价关系封闭，或取其 congruence kernel / itinerary completion。

---

# Part I：基础语言、证明纪律与素数观察模型

# 2. 定义扩张与证明状态

设基础语言为 \(\mathcal L_0\)，仓库中已核验理论为 \(T_0\)。加入素数观察者术语后的语言记为：

\[
\mathcal L_{\mathbb P\mathrm O}
\supseteq
\mathcal L_0.
\]

## 定义 2.1（定义展开）

存在递归翻译：

\[
(-)^\flat:
\mathcal L_{\mathbb P\mathrm O}
\to
\mathcal L_0
\]

将 `PrimeObserver`、`JointReadout`、`LocalGlobalResidual`、`PrimeTrace` 等新符号展开为类型、函数、等式、乘积与商。

## 定理 2.1（定义性保守性）

若 \(T_{\mathbb P\mathrm O}\) 仅相对 \(T_0\) 加入可展开定义，则对任意旧语言命题 \(\varphi\)：

\[
T_{\mathbb P\mathrm O}\vdash\varphi
\Rightarrow
T_0\vdash\varphi.
\]

### 证明

对推导中的全部新符号做定义展开。所得推导仅使用 \(\mathcal L_0\) 的对象与规则。故命名“素数观察者”本身不能制造任何旧语言中的新数学事实。\(\square\)

## 定义 2.2（五级证明状态）

\[
\mathsf{Def}
<
\mathsf{Paper}
<
\mathsf{Lean}
<
\mathsf{Admitted}
<
\mathsf{Frozen}.
\]

分别表示：只完成定义、纸面证明、kernel proof term、仓库准入、内容寻址冻结。不得把较低状态包装成较高状态。

---

# 3. 七层局部—全局存在纪律

对全局类型 \(X\)、局部类型族 \(X_i\)、局部谓词 \(P_i\) 与全局谓词 \(P\)，区分：

\[
\begin{aligned}
E_0
&:\quad \text{方程、状态与接口可形成};\\
E_1
&:\quad \forall i,\ \|X_i\|;\\
E_2
&:\quad \forall i,\left\|\sum_{x_i:X_i}P_i(x_i)\right\|;\\
E_3
&:\quad \left\|\sum_{(x_i)}\operatorname{Compatible}(x_i)\right\|;\\
E_4
&:\quad \left\|\sum_{x:X}P(x)\right\|;\\
E_5
&:\quad x:\sum_{x:X}P(x);\\
E_6
&:\quad \forall n,\ P(F^n x).
\end{aligned}
\]

分别表示：

\[
\text{可定义、局部非空、逐处局部可解、兼容局部族、全局存在、全局见证、动态持续}.
\]

一般不存在：

\[
E_2\Rightarrow E_3,
\qquad
E_3\Rightarrow E_4,
\qquad
E_4\Rightarrow E_5.
\]

## 原理 3.1（无静默胶合）

任何从局部见证族到全局见证的推理，必须显式给出：

- CRT 或其他胶合定理；
- 兼容条件；
- 紧性、完备性或逆极限存在条件；
- Hasse 原理或相应局部—全局定理；
- 经典选择的使用位置；
- 对整数性、正性、界限与 archimedean 条件的处理。

## 原理 3.2（加入无穷位）

涉及符号、正定性、实可解性、大小或方向的算术问题，有限素数观察者通常不够。定义：

\[
\mathcal V_{\mathbb Q}
=
\{\infty\}\sqcup\mathbb P.
\]

有限素数观察理论与包含 \(\infty\) 的 adelic 观察理论必须分开陈述。

---

# 4. 原始素数观察者模型

## 定义 4.1（素数尺度）

\[
\operatorname{PrimeScale}
=
\sum_{p:\mathbb N}
\operatorname{Prime}(p)
\times
\mathbb N_{>0}.
\]

元素写作 \(i=(p,k)\)。

## 定义 4.2（原始素数观察模型）

\[
\boxed{
\mathfrak P_{\mathrm{raw}}
=
(X,\operatorname{Adm},a,U,F,\mathcal I,O,q,\mathcal T).
}
\]

其中：

\[
\begin{aligned}
X&:\mathsf{Type} &&\text{全局状态类型},\\
\operatorname{Adm}&:X\to\mathsf{Prop} &&\text{准入谓词},\\
a&:\sum_{x:X}\operatorname{Adm}(x) &&\text{实际锚点},\\
U&:\mathsf{Type} &&\text{输入／干预类型},\\
F&:U\to X\to X &&\text{受控更新族},\\
\mathcal I&:\mathsf{Type} &&\text{局部观察索引},\\
O&:\mathcal I\to\mathsf{Type} &&\text{依赖输出族},\\
q&:\prod_{i:\mathcal I}(X\to O_i) &&\text{局部读出族},\\
\mathcal T&:\mathsf{Type} &&\text{目标或任务索引}.
\end{aligned}
\]

标准素数模型取 \(\mathcal I=\operatorname{PrimeScale}\)。

## 定义 4.3（实际局部画像）

\[
\operatorname{profile}_i(a)=q_i(a.1),
\qquad
\operatorname{profile}_{\mathrm{all}}(a)
=
(i\mapsto q_i(a.1)).
\]

## 定义 4.4（有限观察预算）

\[
J\subset_{\mathrm{fin}}\mathcal I,
\qquad
O_J=\prod_{i\in J}O_i,
\qquad
q_J(x)=(q_i(x))_{i\in J}.
\]

## 定义 4.5（静态相对同一性）

\[
x\sim_J y
\iff
q_J(x)=q_J(y)
\iff
\forall i\in J,\ q_i(x)=q_i(y).
\]

## 定义 4.6（观察余量纤维）

\[
R_J(o)
=
\sum_{x:X}(q_J(x)=o).
\]

## 定理 4.1（界面—余量分解）

\[
X
\simeq
\sum_{o:O_J}R_J(o).
\]

### 证明

正向将 \(x\) 送到 \((q_Jx,x,\operatorname{refl})\)；逆向忘记等式证明并返回纤维中的状态。两方向由依赖对消去与函数外延互逆。\(\square\)

## 定义 4.7（有效观察商）

\[
Z_J=X/{\sim_J}.
\]

## 定理 4.2（商—可达画像等价）

\[
Z_J
\simeq
\operatorname{range}(q_J).
\]

这是任意函数的 kernel quotient 与 range 的规范等价。

## 定义 4.8（C-IRPT 的素数化解释层）

在不把下列词声明为逻辑原语的前提下，可作结构对应：

\[
\begin{aligned}
\operatorname{CUT}_{p,k}
&:=q_{p,k},\\
\operatorname{FLOW}_u
&:=F_u,\\
\operatorname{ADMIT}
&:=\operatorname{Compatible}\land\operatorname{Adm},\\
\operatorname{ANCHOR}
&:=a,\\
\operatorname{REMAINDER}
&:=R_J\text{ 或 }\operatorname{LGRes}(q).
\end{aligned}
\]

该对应仅用于统一界面—余量语言，不增加存在、公理或现实实现。

---

# 5. 局部—全局余量

## 定义 5.1（完整局部读出）

\[
q_{\mathrm{all}}:X\to\prod_{i:\mathcal I}O_i,
\qquad
q_{\mathrm{all}}(x)=(q_i(x))_i.
\]

## 定义 5.2（完整局部等价）

\[
x\sim_{\mathrm{loc}}y
\iff
\forall i:\mathcal I,\ q_i(x)=q_i(y).
\]

## 定义 5.3（局部—全局余量型）

\[
\boxed{
\operatorname{LGRes}(q)
=
\sum_{x,y:X}
(x\neq y)
\times
(x\sim_{\mathrm{loc}}y).
}
\]

## 定义 5.4（局部完备）

若 \(\operatorname{Injective}(q_{\mathrm{all}})\)，则称局部接口族对 \(X\) 完备。

## 定理 5.1（余量空当且仅当局部完备）

\[
\operatorname{LGRes}(q)=\varnothing
\iff
\operatorname{Injective}(q_{\mathrm{all}}).
\]

### 证明

若完整读出单射，则不存在不同状态具有相同全部局部输出。反之，若不单射，存在 \(x\neq y\) 且完整输出相同，函数外延给出逐坐标相同，构成 `LGRes` 的项。\(\square\)

## 定义 5.5（目标相对余量）

给定 \(t:X\to T\)：

\[
\operatorname{TargetRes}(q,t)
=
\sum_{x,y:X}
(x\sim_{\mathrm{loc}}y)
\times
(t(x)\neq t(y)).
\]

## 定理 5.2（目标充分性）

以下等价：

\[
\operatorname{TargetRes}(q,t)=\varnothing,
\]

\[
\forall x,y,\ x\sim_{\mathrm{loc}}y\Rightarrow t(x)=t(y),
\]

以及在适当选择原则下存在 \(\bar t\) 使：

\[
t=\bar t\circ q_{\mathrm{all}}.
\]

完整身份不必被恢复；只要目标在局部纤维上稳定，局部观察已经对该任务充分。

---

# 6. 精化、联合与观察格

## 定义 6.1（读出精化）

对 \(q:X\to A\) 与 \(r:X\to B\)，若存在 \(h:B\to A\) 使：

\[
q=h\circ r,
\]

则称 \(r\) 精化 \(q\)，记 \(q\preceq r\)。

## 定理 6.1（精化等价于核包含）

在有效像上：

\[
q\preceq r
\iff
\ker(r)\subseteq\ker(q).
\]

## 定理 6.2（索引增加单调精化）

若 \(J\subseteq K\)，则：

\[
q_J\preceq q_K,
\qquad
\sim_K\subseteq\sim_J.
\]

### 证明

坐标限制投影 \(\pi_{K,J}:O_K\to O_J\) 满足：

\[
q_J=\pi_{K,J}\circ q_K.
\]

故核反向包含。\(\square\)

## 定理 6.3（联合核交定理）

\[
\boxed{
\ker(q_{J\cup K})
=
\ker(q_J)\cap\ker(q_K).
}
\]

联合读出相等，当且仅当 \(J\) 中全部坐标相等且 \(K\) 中全部坐标相等。

## 定理 6.4（最小共同精化）

\(q_{J\cup K}\) 同时精化 \(q_J,q_K\)，且任意同时精化二者的读出都精化 \(q_{J\cup K}\) 的有效像。这与仓库 `LeastCommonRefinement` 的商关系交构造一致。

---

# 7. 同一素数的纵向精度塔

## 定义 7.1（相容 \(p\)-进读出塔）

固定素数 \(p\)。若：

\[
q_{p,k}:X\to O_{p,k}
\]

并有降精度映射：

\[
\rho_{p,k+1,k}:O_{p,k+1}\to O_{p,k}
\]

满足：

\[
q_{p,k}
=
\rho_{p,k+1,k}\circ q_{p,k+1},
\]

则称其为相容精度塔。

## 定理 7.1（精度单调性）

\[
q_{p,k}\preceq q_{p,k+1},
\qquad
\ker(q_{p,k+1})\subseteq\ker(q_{p,k}).
\]

## 定义 7.2（单素数无限精度观察）

\[
q_{p,\infty}(x)
=
(q_{p,k}(x))_{k\ge1}
\in
\varprojlim_kO_{p,k}.
\]

## 原理 7.1（同素数尺度非独立）

旧层由新层决定，因此：

\[
O_{p,k}\times O_{p,k+1}
\]

不是两个独立素数传感器，而是一个冗余联合接口。

---

# 8. 不同素数的横向联合

## 定义 8.1（横向素数预算）

\[
S\subset_{\mathrm{fin}}\mathbb P,
\qquad
\kappa:S\to\mathbb N_{>0},
\]

\[
J(S,\kappa)
=
\{(p,\kappa(p)):p\in S\}.
\]

## 定义 8.2（模素数幂读出）

\[
q_{p,k}(x)=x\bmod p^k.
\]

## 定理 8.1（有限 CRT 联合）

令：

\[
M=\prod_{p\in S}p^{\kappa(p)}.
\]

则：

\[
\boxed{
\mathbb Z/M\mathbb Z
\simeq
\prod_{p\in S}\mathbb Z/p^{\kappa(p)}\mathbb Z.
}
\]

## 定理 8.2（横向联合核）

\[
q_{S,\kappa}(x)=q_{S,\kappa}(y)
\iff
M\mid(x-y).
\]

## 原理 8.1（横向与纵向二分）

\[
\boxed{
\begin{aligned}
\text{不同 }p &: \text{CRT 乘积／张量因子};\\
\text{同一 }p\text{ 的不同 }k &: \text{逆系统／精度过滤}.
\end{aligned}
}
\]

这是素数观察者理论的第一结构定律。

---

# Part II：有限完备性、算术层析与最小观察成本

# 9. 有界整数的 CRT 层析

设：

\[
X_N=\{0,1,\ldots,N-1\}.
\]

## 定理 9.1（有界整数 CRT 完备判据）

令：

\[
M=\prod_{p\in S}p^{\kappa(p)}.
\]

联合剩余读出：

\[
q_{S,\kappa}:X_N
\to
\prod_{p\in S}\mathbb Z/p^{\kappa(p)}\mathbb Z
\]

单射，当且仅当：

\[
\boxed{M\ge N.}
\]

### 证明

若 \(M\ge N\)，且 \(q(x)=q(y)\)，则 \(M\mid x-y\)。但 \(|x-y|<N\le M\)，故 \(x-y=0\)。反之若 \(M<N\)，则 \(0,M\in X_N\)，且二者所有局部剩余相同。\(\square\)

## 推论 9.1（精确信息预算）

\[
\sum_{p\in S}\kappa(p)\log_2p
\ge
\log_2N.
\]

## 反模型 9.1（任意有限预算不能识别无界整数）

对任意有限 \((S,\kappa)\)，取：

\[
M=\prod_{p\in S}p^{\kappa(p)}.
\]

则：

\[
q_{S,\kappa}(0)=q_{S,\kappa}(M),
\qquad
0\neq M.
\]

## 定理 9.2（单素数无限精度可分离整数）

固定任意素数 \(p\)。映射：

\[
\mathbb Z\to\prod_{k\ge1}\mathbb Z/p^k\mathbb Z,
\qquad
x\mapsto(x\bmod p^k)_k
\]

是单射。

### 证明

若 \(x-y\) 被每个 \(p^k\) 整除且 \(x-y\neq0\)，则非零整数的 \(p\)-进赋值大于所有自然数，矛盾。\(\square\)

\[
\boxed{
\text{“有限个素数”与“有限总信息”不是同一约束。}
}
\]

---

# 10. 有限状态上的有限分离抽取

## 定义 10.1（局部坐标区分一对状态）

\[
\operatorname{Dist}_i(x,y)
\iff
q_i(x)\neq q_i(y).
\]

## 定理 10.1（有限局部完备抽取）

设 \(X\) 有限。若 \(q_{\mathrm{all}}\) 单射，则存在有限 \(J\subset_{\mathrm{fin}}\mathcal I\) 使 \(q_J\) 单射。

### 证明

对每一对不同状态选择一个区分坐标 \(i_{x,y}\)。不同状态对有限，故所选坐标集合有限；每对状态至少被其对应坐标区分。\(\square\)

## 备注 10.1（经典选择位置）

若局部输出等式不可判定或未给出显式 witness extractor，上述证明使用有限经典选择。算法版本必须给出可计算的区分坐标搜索。

---

# 11. 信息容量与最小成本

## 定义 11.1（有限输出容量）

若每个 \(O_i\) 有限，定义：

\[
\operatorname{Cap}(J)
=
\prod_{i\in J}|O_i|.
\]

## 定义 11.2（对数观察成本）

\[
\operatorname{Cost}(J)
=
\sum_{i\in J}\log_2|O_i|.
\]

若 \(O_{p,k}=\mathbb Z/p^k\mathbb Z\)，则：

\[
\operatorname{Cost}(J)
=
\sum_{(p,k)\in J}k\log_2p.
\]

## 定理 11.1（有限识别容量下界）

若 \(X\) 有限且 \(q_J\) 单射，则：

\[
\boxed{|X|\le\operatorname{Cap}(J),}
\]

等价地：

\[
\boxed{
\log_2|X|
\le
\operatorname{Cost}(J).
}
\]

## 原理 11.1（身份成本与任务成本分离）

\[
\boxed{
\text{识别对象是谁}
\text{通常比完成指定任务更昂贵。}
}
\]

---

# 12. 最小素数传感器与集合覆盖

设：

\[
\mathcal U_X
=
\{\{x,y\}:x\neq y\}.
\]

对每个局部观察者 \(i\)，定义：

\[
D_i
=
\{\{x,y\}\in\mathcal U_X:q_i(x)\neq q_i(y)\}.
\]

## 定理 12.1（分离—覆盖等价）

有限预算 \(J\) 的联合读出单射，当且仅当：

\[
\boxed{
\bigcup_{i\in J}D_i
=
\mathcal U_X.
}
\]

## 推论 12.1（最小完备素数观察者是集合覆盖问题）

\[
\min_J\sum_{i\in J}c_i
\quad
\text{s.t.}
\quad
\bigcup_{i\in J}D_i=\mathcal U_X.
\]

## 原理 12.1（反例优先）

验证预算不完备，只需给出：

\[
x\neq y,
\qquad
q_J(x)=q_J(y).
\]

验证完备则必须覆盖全部不同状态对，或给出结构性单射证明。

---

# 13. 目标风险、精化成本与行动能力

## 定义 13.1（目标缺陷对）

\[
\operatorname{Defect}(q,t)
=
\{(x,y):q(x)=q(y),\ t(x)\neq t(y)\}.
\]

## 定理 13.1（预算增加降低目标风险）

若 \(J\subseteq K\)，则：

\[
\operatorname{Defect}(q_K,t)
\subseteq
\operatorname{Defect}(q_J,t).
\]

## 定义 13.2（可实现策略）

\[
\operatorname{PolicyCap}(q_J,A)
=
\{\pi:X\to A:\exists h:O_J\to A,\ \pi=h\circ q_J\}.
\]

## 定理 13.2（策略能力单调性）

若 \(J\subseteq K\)，则：

\[
\operatorname{PolicyCap}(q_J,A)
\subseteq
\operatorname{PolicyCap}(q_K,A).
\]

\[
\boxed{
\text{精化增加能力，降低某些风险，}
\text{但不自动降低观察成本。}
\]

---

# Part III：素数—判别式对偶、分裂画像与全局类余量

# 14. 素数观察者的两种对偶读法

## 定义 14.1（素数索引的局部观察）

固定全局对象 \(x\)，由素数 \(p\) 读取：

\[
q_p(x).
\]

## 定义 14.2（观察素数的算术概念）

固定算术结构 \(d\)，读取素数 \(p\) 在其中的行为：

\[
s_d(p).
\]

## 定义 14.3（局部互反矩阵）

\[
\mathscr R:
\mathbb P\times\mathcal D
\to
\{-1,0,1\},
\qquad
\mathscr R(p,\Delta)
=
\left(\frac{\Delta}{p}\right).
\]

值分别解释为 split、inert、ramified。固定行得到“素数观察判别式”，固定列得到“判别式观察素数”。

## 原理 14.1（转置不等于同一）

行方向完备性与列方向完备性是不同问题。不得因互反公式的对称性而偷换状态空间与观察者空间。

---

# 15. 三条二次算术观察轴

## 15.1 Gaussian 观察轴

对奇素数 \(p\)：

\[
\sigma_{-4}(p)
=
\begin{cases}
\mathrm S,&p\equiv1\pmod4,\\
\mathrm I,&p\equiv3\pmod4.
\end{cases}
\]

## 15.2 Eisenstein 观察轴

对 \(p\neq3\)：

\[
\sigma_{-3}(p)
=
\begin{cases}
\mathrm S,&p\equiv1\pmod3,\\
\mathrm I,&p\equiv2\pmod3.
\end{cases}
\]

## 15.3 Golden 观察轴

对 \(p\neq5\)：

\[
\sigma_{5}(p)
=
\begin{cases}
\mathrm S,&p\equiv1,4\pmod5,\\
\mathrm I,&p\equiv2,3\pmod5.
\end{cases}
\]

且：

\[
5=(-1+2\varphi)^2
\]

给出分歧素数五。

## 定义 15.1（三环分裂画像）

对 \(p>5\)：

\[
\Sigma_3(p)
=
\bigl(
\sigma_{-4}(p),
\sigma_{-3}(p),
\sigma_5(p)
\bigr)
\in
\{\mathrm S,\mathrm I\}^3.
\]

---

# 16. 模 \(60\) 三环观察定理

## 定理 16.1（三环画像通过模六十因子化）

存在唯一函数：

\[
\bar\Sigma_3:
(\mathbb Z/60\mathbb Z)^\times
\to
\{\mathrm S,\mathrm I\}^3
\]

使：

\[
\Sigma_3(p)
=
\bar\Sigma_3(p\bmod60)
\]

对所有 \(p>5\) 的素数成立。

## 定理 16.2（三环画像满射且纤维大小为二）

\[
\bar\Sigma_3:
(\mathbb Z/60\mathbb Z)^\times
\twoheadrightarrow
\{\mathrm S,\mathrm I\}^3
\]

满射，且每个纤维恰有两个元素。

### 证明

单位剩余类共有 \(\varphi(60)=16\) 个。附录 B 给出八种分裂模式，每种恰由两个剩余类实现。\(\square\)

## 推论 16.1（三环分裂观察不完备）

例如：

\[
1\not\equiv49\pmod{60},
\qquad
\bar\Sigma_3(1)
=
\bar\Sigma_3(49)
=
(\mathrm S,\mathrm S,\mathrm S).
\]

---

# 17. 模五定向位与最小完成

## 定义 17.1（模五定向位）

\[
\omega_5(r)
=
\begin{cases}
0,&r\bmod5\in\{1,2\},\\
1,&r\bmod5\in\{3,4\}.
\end{cases}
\]

## 定理 17.1（三环画像的单比特完成）

\[
\boxed{
\Theta_{60}(r)
=
\bigl(\bar\Sigma_3(r),\omega_5(r)\bigr)
}
\]

给出双射：

\[
(\mathbb Z/60\mathbb Z)^\times
\simeq
\{\mathrm S,\mathrm I\}^3\times\{0,1\}.
\]

### 证明

Gaussian 位确定模四坐标，Eisenstein 位确定模三坐标。Golden 位把模五单位分成 \(\{\pm1\}\) 与 \(\{\pm2\}\)，定向位在每对中选择具体符号。CRT 唯一恢复模六十单位类。\(\square\)

---

# 18. 判别式观察与二次型类余量

## 定义 18.1（判别式分裂观察者）

对：

\[
Q=[A,B,C],
\qquad
\Delta(Q)=B^2-4AC,
\]

定义：

\[
s_p(Q)
=
\left(\frac{\Delta(Q)}p\right).
\]

## 定理 18.1（同判别式不可由分裂画像区分）

若 \(\Delta(Q)=\Delta(Q')\)，则：

\[
\forall p,\ s_p(Q)=s_p(Q').
\]

## 定义 18.2（表示读出）

\[
\operatorname{Rep}_n(Q)
\iff
\exists x,y\in\mathbb Z,\ Q(x,y)=n.
\]

## 反模型 18.1（判别式负二十的分裂盲区）

\[
Q_1(x,y)=x^2+5y^2,
\]

\[
Q_2(x,y)=2x^2+2xy+3y^2.
\]

二者判别式均为 \(-20\)，故全部判别式分裂读出相同。但：

\[
Q_1(1,0)=1,
\]

而：

\[
Q_2(x,y)
=
x^2+(x+y)^2+2y^2.
\]

若 \(y=0\)，则 \(Q_2=2x^2\neq1\)；若 \(y\neq0\)，则 \(Q_2\ge2\)。故 \(Q_2\) 不表示 \(1\)。

## 定理 18.2（分裂画像不恢复全局表示类）

\[
\boxed{
\text{all-prime splitting profile}
\not\Rightarrow
\text{global form identity}.
}
\]

该结论不声称 \(Q_1,Q_2\) 在所有 \(\mathbb Z_p\) 上局部等价；它只证明分裂型接口过于粗糙。

---

# 19. 局部观察层级：从分裂到全局类

## 定义 19.1（五级二次型观察关系）

分别定义：

1. \(R_{\mathrm{global}}\)：全局整等价；
2. \(R_{\mathrm{disc}}\)：同判别式；
3. \(R_{\mathrm{split}}\)：同全部素数分裂画像；
4. \(R_{\mathrm{loc}}\)：在全部有限与无穷局部处等价；
5. \(R_{\mathrm{spin}}\)：同 spinor genus。

在尚未固定二次型范畴、等价群、primitive 条件和局部化定义前，不预先安装为一条总包含链。

## 定理 19.1（本文已经承诺的关系方向）

在全局整等价保持判别式、且分裂读出只依赖判别式的设定中：

\[
\boxed{
R_{\mathrm{global}}
\subseteq
R_{\mathrm{disc}}
\subseteq
R_{\mathrm{split}}.
}
\]

关于 \(R_{\mathrm{loc}}\)、genus、spinor genus 与 class group 的精确包含、商结构和有限反例均列为形式化目标。本文不由“同判别式”推出“全部局部等价”。

## 定义 19.2（类余量）

\[
\operatorname{ClassResidual}(R)
=
\sum_{Q,Q'}
R(Q,Q')
\times
\neg(Q\simeq_{\mathbb Z}Q').
\]

## 开放问题 19.1

能否把：

\[
\operatorname{ClassResidual}(R_{\mathrm{loc}})
\]

规范识别为 genus group、class group 的某个商、spinor obstruction 或相应上同调对象？

---

# 20. Crossing 型：静态观察的 gauge collapse

仓库证明：

\[
Q_t(P,Q)
=
P^2-(2t+1)PQ+(t^2+t+1)Q^2
\]

通过显式 unimodular 换元化为 Eisenstein 范数：

\[
Q_t(P,Q)=x^2+xy+y^2,
\qquad
x=P-(t+1)Q,\ y=Q.
\]

## 定理 20.1（crossing 表示观察塌缩）

对任意 \(s,t\in\mathbb Z\)：

\[
\operatorname{range}(Q_s)
=
\operatorname{range}(Q_t).
\]

## 定义 20.1（静态 gauge 坐标）

若参数 \(t\) 改变形式表达但不改变指定观察者的全部输出，则称 \(t\) 是相对于该观察者的 gauge 坐标。

## 原理 20.1（观察塌缩不等于对象绝对相同）

从 \(q(Q_s)=q(Q_t)\) 只能推出相对同一。若要恢复参数、矩阵轨道位置、相位或构造历史，必须加入其他读出或动态完成。

---
# Part IV：素数—时间轨迹、因果完成与最小预测状态

# 21. 有限时间素数读出词

先取无控制动力学：

\[
F:X\to X.
\]

## 定义 21.1（素数—时间窗口）

\[
W_{J,m}(x)
=
\bigl(q_i(F^n x)\bigr)_{i\in J,\ 0\le n\le m}.
\]

## 定义 21.2（有限素数—时间等价）

\[
x\sim_{J,m}y
\iff
W_{J,m}(x)=W_{J,m}(y).
\]

## 定理 21.1（双轴单调精化）

若 \(J\subseteq K\) 且 \(m\le n\)，则：

\[
\sim_{K,n}
\subseteq
\sim_{J,m}.
\]

“观察更多素数”和“观察更久”是两种独立但可联合的精化方向。

---

# 22. 完整素数轨迹与 congruence kernel

## 定义 22.1（完整素数轨迹）

\[
\operatorname{PTr}_J(x)(i,n)
=
q_i(F^n x).
\]

## 定义 22.2（动态素数等价）

\[
\boxed{
x\sim_J^{\infty}y
\iff
\forall i\in J,\forall n\in\mathbb N,
q_i(F^n x)=q_i(F^n y).
}
\]

## 定义 22.3（全迭代 congruence kernel）

\[
C_F(R)(x,y)
\iff
\forall n,\ R(F^nx,F^ny).
\]

## 定理 22.1（动态素数等价是 congruence kernel）

\[
\boxed{
\sim_J^{\infty}
=
C_F(\sim_J).
}
\]

## 定理 22.2（最大前向闭合）

\(\sim_J^\infty\) 是包含于 \(\sim_J\) 的最大 \(F\)-前向 congruence：

\[
\sim_J^\infty\subseteq\sim_J,
\]

\[
x\sim_J^\infty y
\Rightarrow
Fx\sim_J^\infty Fy,
\]

且任意前向 congruence \(S\subseteq\sim_J\) 满足：

\[
S\subseteq\sim_J^\infty.
\]

这是仓库 `CongruenceKernel` 的直接实例。

## 定义 22.4（动态局部—全局余量）

\[
\operatorname{DynLGRes}(J)
=
\sum_{x,y:X}
(x\neq y)
\times
(x\sim_J^\infty y).
\]

---

# 23. 预测完成与商动力学

## 定义 23.1（素数预测商）

\[
Z_J^\infty
=
X/{\sim_J^\infty}.
\]

## 定理 23.1（更新下降）

存在唯一：

\[
\bar F_J:Z_J^\infty\to Z_J^\infty
\]

满足：

\[
\pi_J\circ F
=
\bar F_J\circ\pi_J.
\]

### 证明

若 \(x\sim_J^\infty y\)，则 \(Fx\sim_J^\infty Fy\)，故 \([x]\mapsto[Fx]\) 良定义。\(\square\)

## 定义 23.2（完成读出）

\[
\bar q_J([x])=q_J(x).
\]

## 定理 23.2（轨迹左移）

若 \(S\) 删除当前时刻：

\[
S((o_n)_{n\ge0})=(o_{n+1})_{n\ge0},
\]

则：

\[
\operatorname{PTr}_J(Fx)
=
S(\operatorname{PTr}_J(x)).
\]

时间推进在完成画像中就是左移。

---

# 24. 有限系统的素数—时间层析

## 定义 24.1（全素数—全时间可分离）

\[
\forall x\neq y,
\exists i:\mathcal I,\exists n:\mathbb N,
q_i(F^nx)\neq q_i(F^ny).
\]

## 定理 24.1（有限素数—时间层析）

设 \(X\) 有限。若完整素数—时间观察可分离 \(X\)，则存在有限：

\[
J\subset_{\mathrm{fin}}\mathcal I,
\qquad
m\in\mathbb N
\]

使：

\[
W_{J,m}:X\to O_{J,m}
\]

单射。

### 证明

对每一对不同状态选择一个见证 \((i_{x,y},n_{x,y})\)。不同状态对有限，故所选索引集合有限，所选时间有有限最大值 \(m\)。任意状态对都在某个不超过 \(m\) 的见证坐标被区分。\(\square\)

## 定义 24.2（素数—时间证书复杂度）

\[
\operatorname{PTC}(X,F,q)
=
\min
\left\{
\operatorname{Cost}(J)+\lambda m:
W_{J,m}\text{ 单射}
\right\}.
\]

它量化“测哪些素数、测多精、等多久”的联合成本。

---

# 25. 有限稳定深度

定义：

\[
R_m^J(x,y)
\iff
x\sim_{J,m}y.
\]

有下降链：

\[
R_0^J
\supseteq
R_1^J
\supseteq\cdots
\supseteq
R_\infty^J.
\]

## 定理 25.1（一次稳定永久稳定）

若：

\[
R_m^J=R_{m+1}^J,
\]

则：

\[
\forall r,\ R_{m+r}^J=R_m^J.
\]

这是仓库 `PredictionPartitionStability` 的预算实例。

## 定理 25.2（有限状态必有稳定深度）

若 \(X\) 有限，则存在 \(m\) 使：

\[
R_m^J=R_\infty^J.
\]

---

# 26. 受控素数观察者

设：

\[
F:U\to X\to X.
\]

有限输入词 \(w=[u_1,\ldots,u_n]\) 的复合更新记为 \(F_w\)。

## 定义 26.1（受控素数行为）

\[
\operatorname{Beh}_J(x)(w,i)
=
q_i(F_wx).
\]

## 定义 26.2（受控行为等价）

\[
x\approx_Jy
\iff
\forall w\in U^*,\forall i\in J,
q_i(F_wx)=q_i(F_wy).
\]

## 定理 26.1（受控商闭合）

每个输入 \(u\) 在 \(X/{\approx_J}\) 上诱导良定义更新，联合读出下降到该商。

## 定理 26.2（受控最小实现）

在仓库 `ControlledBehaviorUniversality` 的有限与满射实现前件下，任意复现同一受控素数行为的有限系统，都存在唯一满射因子到行为商，并有：

\[
|Z_J^{\mathrm{ctrl}}|
\le
|W|.
\]

一个对象的操作性身份是：

\[
\boxed{
\text{在所有允许干预后，全部选定素数接口的完整响应类。}
}
\]

---

# 27. 动态区分的集合覆盖

对每个素数—时间坐标 \((i,n)\)，定义：

\[
D_{i,n}
=
\{\{x,y\}:q_i(F^nx)\neq q_i(F^ny)\}.
\]

## 定理 27.1（素数—时间覆盖等价）

预算 \(J\) 与时间深度 \(m\) 完整区分有限 \(X\)，当且仅当：

\[
\bigcup_{i\in J,\ n\le m}D_{i,n}
=
\mathcal U_X.
\]

这把实验设计变成带前缀约束的加权覆盖问题。

---

# 28. Crossing 相位的局部观察动力学

仓库已证明：

\[
S(A)=MAM,
\qquad
\Psi(S(A))=\Psi(A)-2.
\]

## 定义 28.1（模 \(m\) 相位观察者）

\[
q_m(A)=\Psi(A)\bmod m.
\]

## 定理 28.1（相位动力学下降到平移）

存在：

\[
T_m(z)=z-2
\]

使：

\[
q_m\circ S
=
T_m\circ q_m.
\]

## 定理 28.2（模 \(m\) 的最小相位周期）

\[
\boxed{
T(m)=\frac{m}{\gcd(m,2)}.
}
\]

### 证明

返回条件为 \(2n\equiv0\pmod m\)，最小正解是 \(m/\gcd(m,2)\)。\(\square\)

## 推论 28.1（素数幂局部周期）

\[
T(p^k)
=
\begin{cases}
p^k,&p\text{ 为奇素数},\\
2^{k-1},&p=2.
\end{cases}
\]

## 定理 28.3（CRT 周期合成）

若：

\[
m=\prod_{p^k\parallel m}p^k,
\]

则：

\[
\boxed{
T(m)
=
\operatorname{lcm}_{p^k\parallel m}T(p^k).
}
\]

## 推论 28.2（六步周期的素数解释）

\[
12=4\cdot3,
\qquad
T(4)=2,
\qquad
T(3)=3,
\]

故：

\[
T(12)=\operatorname{lcm}(2,3)=6.
\]

---

# 29. 局部相位零与全局相位零

## 定义 29.1（局部零事件）

\[
Z_{p,k}(A)
\iff
\Psi(A)\equiv0\pmod{p^k}.
\]

## 定义 29.2（全局零事件）

\[
Z_{\mathbb Z}(A)
\iff
\Psi(A)=0.
\]

全局零蕴含全部局部零，但任意固定有限预算的全部局部零不推出全局零。若：

\[
M=\prod_{(p,k)\in J}p^k,
\qquad
\Psi(A)=M,
\]

则全部已选局部零成立而全局零失败。

## 定理 29.1（有界相位下的局部零证书）

若：

\[
|\Psi(A)|<M,
\qquad
M\mid\Psi(A),
\]

则：

\[
\Psi(A)=0.
\]

有限素数零证书只有在附带全局大小界时才可升级为全局零证明。

---

# 30. Pell 与矩阵轨道的局部周期

## 定义 30.1（整矩阵局部观察）

\[
q_{p,k}(A)=A\bmod p^k.
\]

## 定理 30.1（可逆整矩阵轨道模素数幂纯周期）

若：

\[
G\in\operatorname{GL}_d(\mathbb Z),
\]

则由 \(G\) 诱导的模 \(p^k\) 更新是有限状态空间上的置换。因此每条局部轨道从零时刻起纯周期。

## 推论 30.1（Pell 塔的局部循环画像）

由基本单位或 unimodular 递推矩阵生成的 Pell 序列，在每个模 \(p^k\) 观察者下均呈周期序列。

## 原理 30.1（局部周期不等于全局周期）

整 Pell 轨道可无界增长，而每个固定模 \(p^k\) 画像都周期。这与全局无界身份和有限局部接口中的循环完全相容。

---

# Part V：\(p\)-进观察几何、预测超度量与素数幂张量结构

# 31. 单素数观察距离

固定素数 \(p\)，取：

\[
q_{p,k}(x)=x\bmod p^k.
\]

## 定义 31.1（首次分歧精度）

对 \(x\neq y\)：

\[
\kappa_p(x,y)
=
\min\{k\ge1:q_{p,k}(x)\neq q_{p,k}(y)\}.
\]

## 定理 31.1（首次分歧与赋值）

\[
\boxed{
\kappa_p(x,y)=v_p(x-y)+1.
}
\]

## 定义 31.2（素数观察距离）

\[
d_p(x,y)
=
\begin{cases}
0,&x=y,\\
p^{1-\kappa_p(x,y)},&x\neq y.
\end{cases}
\]

## 定理 31.2（观察距离等于 \(p\)-进距离）

\[
\boxed{
d_p(x,y)=p^{-v_p(x-y)}
}
\]

对 \(x\neq y\) 成立。

## 定理 31.3（球—有限读出纤维对应）

\[
x\equiv y\pmod{p^k}
\iff
d_p(x,y)\le p^{-k}.
\]

模 \(p^k\) 的观察纤维就是 \(p\)-进闭球与整数像的交。

---

# 32. 多素数静态超度量

为每个坐标指定正权重 \(w_i\)，定义：

\[
\delta_i(x,y)
=
\begin{cases}
0,&q_i(x)=q_i(y),\\
1,&q_i(x)\neq q_i(y).
\end{cases}
\]

\[
d_J(x,y)
=
\max_{i\in J}w_i\delta_i(x,y).
\]

## 定理 32.1（加权联合超伪度量）

\[
d_J(x,z)
\le
\max\{d_J(x,y),d_J(y,z)\}.
\]

## 定理 32.2（零距离核）

\[
d_J(x,y)=0
\iff
q_J(x)=q_J(y).
\]

故 \(d_J\) 在观察商上下降为真正超度量。

---

# 33. 素数—时间预测超度量

设 \(0<\gamma\le1\)。

## 定义 33.1（折扣素数—时间距离）

\[
\boxed{
d_{J,\gamma}^{F}(x,y)
=
\sup_{i\in J,\ n\ge0}
w_i\gamma^n
\delta_i(F^nx,F^ny).
}
\]

## 定理 33.1（预测强三角不等式）

\[
d_{J,\gamma}^{F}(x,z)
\le
\max
\left\{
d_{J,\gamma}^{F}(x,y),
d_{J,\gamma}^{F}(y,z)
\right\}.
\]

## 定理 33.2（零距离等于动态不可区分）

若全部权重正且 \(\gamma>0\)，则：

\[
d_{J,\gamma}^{F}(x,y)=0
\iff
x\sim_J^\infty y.
\]

---

# 34. 素数观察拓扑与圆柱集

## 定义 34.1（有限观察圆柱）

\[
\operatorname{Cyl}(J,m,w)
=
\{x:W_{J,m}(x)=w\}.
\]

## 定义 34.2（素数—时间圆柱拓扑）

以全部有限圆柱集为基生成的拓扑，称为素数—时间观察拓扑。

## 原理 34.1（有限局部性不必统一）

\[
\forall x,\exists J_x,m_x
\]

不自动推出：

\[
\exists J,m,\forall x.
\]

有限状态或紧性前件可以提供统一化；无限系统中必须另行证明。

---

# 35. 有限前缀稳定与无限未来脆弱

定义有限前缀局部稳定与完整未来局部稳定。必须保持：

\[
\forall m,\exists\varepsilon_m>0
\]

不推出：

\[
\exists\varepsilon>0,\forall m.
\]

仓库黄金机械读出实例已经证明：每个有限前缀在非边界点附近稳定，但不存在稳定全部无限未来的统一正半径。

---

# 36. 素数幂窗口代数的水平张量分解

仓库 `PrimePowerTensorTower` 已证明：

\[
\boxed{
M_M(\mathbb C)
\simeq_{\mathbb C}
\bigotimes_{p^e\parallel M}
M_{p^e}(\mathbb C).
}
\]

这不仅是地址重标号，而是矩阵单位基、乘法与复代数结构共同分解。

## 原理 36.1（张量分解边界）

该等价不自动推出给定物理态是乘积态、通道逐因子分解、不同素数因子无相关性，或世界的基本自由度就是这些因子。

## 定理 36.1（同素数层不可作为新张量因子）

\[
\ker(q_{p,k},q_{p,k+1})
=
\ker(q_{p,k+1}).
\]

\[
\boxed{
\text{横向 }p\neq q\text{ 用乘积；}
\quad
\text{纵向 }k\to k+1\text{ 用精化。}
}
\]

---

# 37. 完整同余画像与 profinite 隐纤维

\[
q_{\widehat{\mathbb Z}}(x)
=
(x\bmod n)_{n\ge1}
\]

可按素数组织为：

\[
(x_p)_{p\in\mathbb P}
\in
\prod_p\mathbb Z_p.
\]

仓库证明短正合序列：

\[
0
\to
\operatorname{CongruenceData}
\to
\operatorname{UniversalSolenoid}
\to
\mathbb T
\to
0.
\]

## 定义 37.1（素数坐标观察者）

\[
\pi_p:
\prod_q\mathbb Z_q
\to
\mathbb Z_p.
\]

## 定理 37.1（全部素数坐标分离隐藏身份）

\[
\forall p,\pi_p(x)=\pi_p(y)
\Rightarrow
x=y.
\]

## 反模型 37.1（任意有限素数集合不分离完整隐藏纤维）

对有限 \(S\)，选择 \(q\notin S\)，令两个状态只在 \(q\) 坐标不同。则全部 \(S\)-坐标相同而全局状态不同。

---

# 38. 隐运动刚性与连续时间扇区

仓库 `HiddenMotionRigidity` 已证明：

\[
\gamma:I\to\prod_p\mathbb Z_p,
\qquad
\operatorname{Continuous}(\gamma)
\]

推出：

\[
\forall s,t\in I,\gamma(s)=\gamma(t).
\]

在该拓扑模型中，纯素数隐画像沿连通时间常值。该定理不排除离散跳变、非连续映射、改变拓扑后的运动或完整 solenoid 中的可见实流。

---

# 39. 可见实流与固定素数余量

在仓库既有 streamline 分解框架中，solenoid 路径可组织为：

\[
\gamma(t)
=
\operatorname{realFlow}(r(t))+h,
\]

其中 \(h\) 位于隐藏同余核并沿路径固定。

\[
\boxed{
\text{连续时间由实流参数承担，}
\quad
\text{素数画像承担静态扇区身份。}
}
\]

这是 universal-solenoid 模型中的结构解释，不是一般宇宙论断言。

---

# 40. 逆极限完成与有限阶段观察

\[
\widehat{\mathbb Z}
=
\varprojlim_M\mathbb Z/M\mathbb Z.
\]

整数嵌入：

\[
\mathbb Z\hookrightarrow\widehat{\mathbb Z}
\]

通常不是满射。一个兼容全模画像可以是合法 profinite 元素，却不来自普通整数。

\[
\boxed{
\text{所有有限读出兼容}
\ne
\text{存在原始全局整数产生这些读出}.
}
\]

---

# Part VI：局部真理、知识、胶合与 Hasse 型缺陷

# 41. 局部命题与观察者知识

设：

\[
P:X\to B.
\]

## 定义 41.1（预算知识）

\[
\operatorname{Knows}_J(P)
\iff
\exists\bar P:O_J\to B,\ 
P=\bar P\circ q_J.
\]

## 定理 41.1（知识的纤维稳定刻画）

\[
\operatorname{Knows}_J(P)
\iff
\forall x,y,\ q_J(x)=q_J(y)\Rightarrow P(x)=P(y).
\]

## 定理 41.2（知识随精化单调）

若 \(J\subseteq K\)，则：

\[
\operatorname{Knows}_J(P)
\Rightarrow
\operatorname{Knows}_K(P).
\]

粗化可能把 \(P\) 值不同的状态合并，故反向一般失败。

---

# 42. 局部可解、兼容与胶合

设局部化映射：

\[
\ell_i:X\to X_i.
\]

## 定义 42.1（逐处局部可解）

\[
\operatorname{LocSolvable}
\iff
\forall i,\exists x_i:X_i,\ P_i(x_i).
\]

## 定义 42.2（兼容局部族）

\[
\operatorname{Compatible}((x_i)_i).
\]

## 定义 42.3（可胶合）

\[
\exists x:X,\forall i,\ell_i(x)=x_i.
\]

## 原理 42.1（三次量词分离）

\[
\forall i,\exists x_i
\]

只给逐处见证；

\[
\exists(x_i)_i,\operatorname{Compatible}(x_i)
\]

给兼容局部对象；

\[
\exists x,\forall i,\ell_i(x)=x_i
\]

才给全局来源。

---

# 43. 有限 CRT 胶合定理

对两两互素模数 \(m_1,\ldots,m_r\) 与局部数据 \(a_j\bmod m_j\)，存在唯一：

\[
a\in\mathbb Z/M\mathbb Z,
\qquad
M=\prod_jm_j
\]

满足全部局部同余。

对一般模数，有限同余族可胶合，当且仅当每对数据在 \(\gcd(m,n)\) 重叠上兼容；胶合结果模最小公倍数唯一。

CRT 胶合得到的是 \(a\bmod M\)，不是唯一普通整数。恢复整数必须附加有界区间、符号、高度或无穷位信息。

---

# 44. Hasse 接口与局部—全局缺陷

## 定义 44.1（Hasse 完备接口）

若：

\[
P(x)
\iff
\forall i,L_i(x),
\]

则称局部接口族对 \(P\) Hasse 完备。

## 定义 44.2（局部假阳性余量）

\[
\operatorname{HasseDefect}^{+}(P,L)
=
\sum_{x:X}
\left(\prod_iL_i(x)\right)
\times
\neg P(x).
\]

## 定义 44.3（局部假阴性余量）

\[
\operatorname{HasseDefect}^{-}(P,L)
=
\sum_{x:X}
P(x)
\times
\neg\prod_iL_i(x).
\]

## 定理 44.1（Hasse 完备当且仅当双缺陷为空）

\[
P(x)\iff\forall i,L_i(x)
\]

对全部 \(x\) 成立，当且仅当正负缺陷都为空。

## 原理 44.1（Hasse 原理不是定义真理）

定义全部局部条件并不能证明正缺陷为空。每个算术问题都必须单独证明局部—全局桥，或构造缺陷见证。

---

# 45. 分裂知识、表示知识与类知识

必须区分：

1. 分裂知识；
2. 某个整数是否被形式表示的知识；
3. 二次型全局整等价类知识。

反模型 18.1 给出：

\[
\text{同全部判别式分裂知识}
\]

但：

\[
\text{不同表示知识}.
\]

因此：

\[
\boxed{
\text{分裂知识}
\not\Rightarrow
\text{表示知识}.
}
\]

表示知识是否决定类知识需要另行证明，本文不偷推。

---

# 46. 实际锚点与现实实现桥

实际锚点：

\[
a:\sum_{x:X}\operatorname{Adm}(x).
\]

现实系统 \(R\) 到形式状态的实现桥为：

\[
\iota:R\to X
\]

连同：

\[
q_i\circ\iota
=
\widehat q_i.
\]

没有该桥，素数观察理论只是一套内部数学模型。完整局部画像不自动证明传感器忠实、来源真实、锚点合法或现实对象存在。

---

# 47. 因果 carry 与素数观察缺陷

给定：

\[
F:X\to Y,
\qquad
q:X\to O,
\qquad
r:Y\to P.
\]

定义：

\[
\operatorname{Carry}(F;q,r)
=
\sum_{x,y:X}
(q(x)=q(y))
\times
(r(Fx)\neq r(Fy)).
\]

若存在 \(\bar F:O\to P\) 使：

\[
r\circ F
=
\bar F\circ q,
\]

则 carry 为空。

反之，在有限或具有效像消去条件的模型中，carry 为空允许在 \(q\) 的像上定义：

\[
\bar F(qx)=r(Fx).
\]

若当前素数画像存在 carry，则加入更多素数、更高精度、记忆或干预响应，直至目标过程下降。

---

# 48. 解释、预测与最小充分画像

对目标行为 \(t:X\to T\)，一个解释是读出 \(e:X\to E\) 使：

\[
t=\bar t\circ e.
\]

若 \(e=q_J\) 或由 \(W_{J,m}\) 构成，则称为素数局部解释。若删除任一承重接口后不再充分，则为最小解释。

\[
\boxed{
\text{解释的充分性是相对于目标的因子化，}
\text{不是全局本体穷尽。}
}
\]

---
# Part VII：多观察者融合、行动、审计与科学方法

# 49. 多主体素数预算

设主体类型为 \(Agt\)，每个主体 \(a\) 拥有预算：

\[
J_a\subset_{\mathrm{fin}}\mathcal I.
\]

联盟 \(C\subseteq Agt\) 的联合预算为：

\[
J_C=\bigcup_{a\in C}J_a.
\]

若 \(C\subseteq D\)，则：

\[
q_{J_C}\preceq q_{J_D}.
\]

## 定义 49.1（共同可见因子）

读出 \(c:X\to C_0\) 是主体族的共同因子，若：

\[
c\preceq q_{J_a}
\]

对每个主体成立。

## 定义 49.2（融合画像）

融合画像是最小共同精化：

\[
q_{\cup_aJ_a}.
\]

## 原理 49.1（共同知识与融合知识分离）

共同因子是每个人单独都能恢复的内容；融合画像是汇总全部读出后才能恢复的内容。二者类似 meet 与 join，不得混同。

---

# 50. 冗余、故障与来源相关

## 定义 50.1（\(r\)-冗余区分）

若每一对不同状态至少被 \(r\) 个坐标区分，则称观察系统具有 \(r\)-冗余。

## 定义 50.2（删除鲁棒性）

若删除任意至多 \(f\) 个坐标后联合读出仍单射，则称系统 \(f\)-删除鲁棒。

## 定理 50.1（简单冗余充分条件）

若每对不同状态至少被 \(f+1\) 个坐标区分，则系统对任意 \(f\) 个坐标删除仍完备。

## 原理 50.1（算术坐标独立不等于来源独立）

不同素数坐标可能仍依赖同一设备、同一数据源、同一软件实现、同一攻击面或同一错误模型。数学因子与证据来源必须分层审计。

## 形式化目标 50.1（错误修正 CRT 观察者）

建立带错误坐标的重建条件：多余模数、动态范围界、最多 \(f\) 个 Byzantine residue、唯一恢复或列表恢复，以及可验证证书。

---

# 51. 行动策略与干预自然性

## 定义 51.1（局部策略）

\[
\pi=h\circ q_J.
\]

## 定义 51.2（干预后读出自然性）

给定：

\[
F_u:X\to X,
\qquad
G_{u,i}:O_i\to O_i,
\]

若：

\[
q_i\circ F_u
=
G_{u,i}\circ q_i,
\]

则第 \(i\) 个局部观察在干预下自然。

若全部 \(i\in J\) 自然，则联合读出自然。若任一坐标存在 carry，则仅凭当前局部画像无法实现精确局部更新，必须扩大预算、加入记忆、改用集合值／概率更新，或承认模型误差。

---

# 52. 科学实验设计

候选理论状态空间记为 \(\Theta\)。每个素数—精度—干预实验：

\[
e=(p,k,u)
\]

给出：

\[
q_e:\Theta\to O_e.
\]

对当前候选纤维 \(C\subseteq\Theta\)，定义最坏情况区分增益：

\[
V(e\mid C)
=
|C|
-
\max_{o\in O_e}
|C\cap q_e^{-1}(o)|.
\]

下一步实验可依赖已有历史：

\[
e_{n+1}
=
\pi(o_0,\ldots,o_n).
\]

这形成自适应决策树。未来可把素数传感器 set cover、自适应决策树、Bellman contraction、目标风险与观察成本接入 `Observer/DynamicProgramming` 与 `ConceptDynamics/DecisionValue`。

---

# 53. 可审计局部证据

一个证据包包括：

\[
(i,o,\rho,\pi),
\]

其中：

- \(i=(p,k)\)：观察坐标；
- \(o\)：输出；
- \(\rho\)：来源、版本与时间戳；
- \(\pi\)：可验证计算或证明证书。

联合证据一致要求：

- 同素数不同精度经降尺度相容；
- 不同模数在重叠同余上相容；
- 来源与准入规则通过；
- 若声称来自全局状态，则有胶合见证或证明。

必须把：

\[
\operatorname{ArithmeticConsistent},
\quad
\operatorname{ProvenanceValid},
\quad
\operatorname{RealityFaithful}
\]

作为不同谓词。

---

# 54. 素数观察者的计算架构

不同素数坐标适合水平并行；同一素数从 \(k\) 到 \(k+1\) 适合纵向增量缓存：

\[
\boxed{
\text{横轴：不同素数并行；}
\quad
\text{纵轴：同一素数逐级加精。}
}
\]

建议每个坐标保存：读出值、降精度一致性证明、CRT 合成证书、对目标任务的区分贡献与内容哈希。

---

# Part VIII：规范有限模型与反模型

# 55. 模型 A：有界整数的完备素数层析

取：

\[
X=\{0,\ldots,999\}.
\]

选择：

\[
2^3\cdot3^2\cdot5^2
=
1800.
\]

联合读出：

\[
q(x)
=
(x\bmod8,x\bmod9,x\bmod25)
\]

单射，因为 \(1800\ge1000\)。

若删除模 \(25\) 坐标，只剩 \(M=72<1000\)，则：

\[
q(0)=q(72).
\]

该模型给出最小性见证。

---

# 56. 模型 B：三环分裂画像的二元纤维

状态空间：

\[
X=(\mathbb Z/60\mathbb Z)^\times.
\]

读出：

\[
q=\bar\Sigma_3:X\to\{\mathrm S,\mathrm I\}^3.
\]

有：

\[
|X|=16,
\qquad
|\operatorname{range}(q)|=8,
\]

每个纤维大小为二。加入 \(\omega_5\) 后得到双射。

---

# 57. 模型 C：同判别式二次型的分裂盲区

状态：

\[
X=\{Q_1,Q_2\}
\]

与目标：

\[
t(Q)=\operatorname{Rep}_1(Q).
\]

全部素数分裂读出合并 \(Q_1,Q_2\)，但目标值不同。因此：

\[
\operatorname{TargetRes}(q_{\mathrm{all}},t)
\neq
\varnothing.
\]

即使使用全部素数，只要每个传感器读取的概念过粗，增加索引数量仍不能消除概念盲区。

---

# 58. 模型 D：crossing 相位的局部周期与全局唯一零

若：

\[
\Psi(A_0)=2k,
\qquad
A_n=S^n(A_0),
\]

则：

\[
\Psi(A_n)=2(k-n).
\]

全局零恰在 \(n=k\)。模三读出每三步重复，模四每两步重复，模十二最小周期六。局部周期观察者不能无界地认证全局唯一事件。

---

# 59. 模型 E：profinite 隐身份的有限不可见坐标

\[
X=\prod_p\mathbb Z_p.
\]

对有限 \(S\)，取未观察素数 \(r\notin S\)，构造两个只在 \(r\) 坐标不同的状态。它们全部 \(S\)-读出相同而全局不同。

---

# 60. 模型 F：静态同余不闭合的三状态动力学

\[
X=\{0,1,2\},
\]

\[
q(0)=q(1)=A,
\qquad
q(2)=B,
\]

\[
F(0)=0,
\qquad
F(1)=2,
\qquad
F(2)=2.
\]

于是：

\[
q(0)=q(1)
\]

但：

\[
q(F0)\neq q(F1).
\]

加入一步未来读出 \(W_1(x)=(q(x),q(Fx))\) 即可区分 \(0,1\)。这是最小动态完成。

---

# 61. 模型 G：同素数冗余不增加信息

\[
q_{p,1}(x)=x\bmod p,
\qquad
q_{p,2}(x)=x\bmod p^2.
\]

因为 \(q_{p,1}\) 通过 \(q_{p,2}\) 因子化：

\[
\ker(q_{p,1},q_{p,2})
=
\ker(q_{p,2}).
\]

观察接口数量不是信息量；承重的是核是否严格缩小。

---

# 62. 模型 H：不兼容局部见证不能胶合

局部约束：

\[
x\equiv0\pmod2,
\qquad
x\equiv1\pmod2.
\]

每个约束单独可解，但二者在共同模二重叠上不兼容，故不存在全局整数同时满足。

---

# 63. 模型 I：算术一致性与现实来源分离

三个 residues 可以通过 CRT 一致性验证并唯一恢复模三十状态；若三项都来自同一被篡改上游，数学一致性仍不证明来源真实性。

---

# Part IX：Lean 形式化路线、依赖图与证明矩阵

# 64. 建议目录

```text
D5/S3/PrimeObservers/
  Foundation/
    LocalReadout.lean
    JointReadout.lean
    LocalGlobalResidual.lean
    Refinement.lean
  CRT/
    FiniteJoin.lean
    BoundedIntegerTomography.lean
    InformationCapacity.lean
    PrimePowerGrid.lean
  Arithmetic/
    QuadraticCharacterObserver.lean
    ThreeRingSplittingObserver.lean
    OrientedModFiveCompletion.lean
    DiscriminantBlindFormCountermodel.lean
    CrossingRangeGauge.lean
  Dynamics/
    PrimeTrace.lean
    PrimeCongruenceKernel.lean
    FinitePrimeTimeTomography.lean
    ControlledPrimeBehavior.lean
    CrossingPhaseLocalPeriods.lean
  Geometry/
    PadicFirstDisagreement.lean
    PrimePredictionUltrametric.lean
    CylinderTopology.lean
  LocalGlobal/
    LocalSolvability.lean
    GluingDefect.lean
    HasseInterface.lean
    FormClassResidual.lean
  Agents/
    SensorCover.lean
    Redundancy.lean
    PolicyCapability.lean
  Countermodels/
    FiniteBudgetUnboundedIntegers.lean
    SamePrimeRedundancy.lean
    SplittingBlindness.lean
```

对应 Blueprint 放在：

```text
Blueprint/D5/S3/PrimeObservers/...
```

总论放在：

```text
docs/develop/theory/FORMAL_PRIME_OBSERVER_DYNAMICS.md
```

---

# 65. 最小形式化内核

```lean
structure LocalObserver (X : Type u) where
  Output : Type v
  readout : X → Output

structure PrimeScale where
  p : ℕ
  hp : Nat.Prime p
  k : ℕ
  hk : 0 < k
```

```lean
def JointEq
    (q : (i : ι) → X → O i)
    (J : Finset ι)
    (x y : X) : Prop :=
  ∀ i, i ∈ J → q i x = q i y
```

```lean
def LocalGlobalResidual
    (q : (i : ι) → X → O i) : Type _ :=
  {xy : X × X // xy.1 ≠ xy.2 ∧ ∀ i, q i xy.1 = q i xy.2}
```

```lean
def PrimeTraceEq
    (F : X → X)
    (q : (i : ι) → X → O i)
    (J : Finset ι)
    (x y : X) : Prop :=
  ∀ n i, i ∈ J → q i (F^[n] x) = q i (F^[n] y)
```

第一阶段必须证明：

1. `jointEq_union`;
2. `jointEq_mono`;
3. `localGlobalResidual_empty_iff`;
4. `finite_separating_subfamily`;
5. `primeTraceEq_eq_congruenceKernel`;
6. `primeTraceEq_forward`;
7. `finite_prime_time_tomography`.

---

# 66. CRT 与信息容量形式化

目标声明：

```lean
theorem bounded_integer_joint_residue_injective_iff
    (N : ℕ)
    (mods : Finset ℕ)
    (hcoprime : mods.toSet.Pairwise Nat.Coprime) :
    Function.Injective (boundedJointResidue N mods)
      ↔ N ≤ ∏ m in mods, m
```

必须处理非零模数、bounded subtype、CRT 等价、\(M<N\) 时反例 \((0,M)\) 及输出积基数。

集合覆盖等价应使用规范无序状态对，避免重复方向。

---

# 67. 三环模六十观察者形式化

```lean
inductive SplitType
  | split
  | inert
  | ramified
```

目标：

```lean
theorem threeRingProfile_fiber_card_two :
  ∀ b, Fintype.card
    {r : (ZMod 60)ˣ // threeRingProfile r = b} = 2
```

以及：

```lean
theorem threeRingProfile_with_orientation_bijective :
  Function.Bijective fun r =>
    (threeRingProfile r, modFiveOrientation r)
```

必须保留 \(p=2,3,5\) 的边界和 ramified 分支。

---

# 68. 二次型分裂盲区形式化

```lean
structure BinaryQuadraticForm where
  A B C : ℤ

def disc (Q : BinaryQuadraticForm) : ℤ :=
  Q.B^2 - 4 * Q.A * Q.C

def Q1 : BinaryQuadraticForm := ⟨1, 0, 5⟩
def Q2 : BinaryQuadraticForm := ⟨2, 2, 3⟩
```

证明：

```lean
Q1.disc = -20
Q2.disc = -20
represents Q1 1
¬ represents Q2 1
```

最后导出全部 splitting readout 相同但 representation profile 不同。

---

# 69. Crossing 相位 CRT 周期形式化

复用：

- `ExactPropagation`;
- `WindingOrbitZero`;
- `SandwichPhasePeriod`;
- `WindowRegisterCRT`.

先证明：

```lean
theorem translation_neg_two_period (m : ℕ) (hm : 0 < m) :
  minimalPeriod (fun z : ZMod m => z - 2) = m / Nat.gcd m 2
```

再证明素数幂版本、CRT lcm 版本和 crossing phase 半共轭。

---

# 70. \(p\)-进观察距离形式化

目标：

```lean
theorem first_disagreement_eq_valuation_add_one
theorem observerDistance_eq_padicDistance
theorem residueFiber_eq_closedBall
```

随后把 `DiscretePredictionUltrametric` 泛化到依赖素数坐标与时间坐标的双重上确界。

---

# 71. 依赖图

```text
ConceptFiberDecomposition
        │
        ▼
PrimeObservers.Foundation.LocalReadout
        │
        ├────────► JointReadout ─────► Refinement ─────► SensorCover
        │                 │
        │                 ▼
        │          LocalGlobalResidual
        │
        ├────────► CRT.FiniteJoin ───► BoundedIntegerTomography
        │                 │
        │                 └──────────► PrimePowerGrid
        │
        ├────────► Arithmetic.QuadraticCharacterObserver
        │                 ├──────────► ThreeRingSplittingObserver
        │                 │                    ▼
        │                 │          OrientedModFiveCompletion
        │                 └──────────► DiscriminantBlindFormCountermodel
        │
        ├────────► Dynamics.PrimeTrace
        │                 │
CongruenceKernel ─────────┤
        │                 ▼
        │        FinitePrimeTimeTomography
ItineraryCompletion ──────┤
        │                 ▼
ControlledBehaviorUniversality ─► ControlledPrimeBehavior
        │
        ├────────► CrossingPhaseLocalPeriods
        └────────► Geometry.PrimePredictionUltrametric
```

---

# 72. 证明状态矩阵

| 结论 | 状态 | 主要现有锚点 |
|---|---|---|
| 联合核是局部核交 | Paper | ConceptJoinUniversal |
| 索引增加产生精化 | Paper | Concept refinement machinery |
| 有限局部完备抽取 | Paper | finite pair selection |
| 有界整数 CRT 判据 \(M\ge N\) | Paper | WindowRegisterCRT / CRT |
| 输出容量下界 | Paper | finite cardinality |
| 分离等价于 set cover | Paper | finite definitions |
| 动态等价是 congruence kernel | Paper + anchored | CongruenceKernel |
| 有限素数—时间层析 | Paper | ItineraryCompletion pattern |
| 行为商规范最小 | Anchored specialization | ControlledBehaviorUniversality |
| 三环画像模六十因子化 | Paper + anchors | Golden / Eisenstein / Gaussian |
| 三环画像每纤维大小二 | Paper finite certificate | same |
| 加定向位后双射 | Paper | CRT |
| 判别式负二十分裂盲区 | Paper countermodel | form definitions |
| crossing 相位每步降二 | Lean anchor | ExactPropagation |
| 模十二最小六周期 | Lean anchor | SandwichPhasePeriod |
| 一般模 \(m\) 周期公式 | Paper | modular arithmetic |
| \(p\)-进首次分歧距离 | Paper | Mathlib target |
| 素数幂全矩阵张量塔 | Lean anchor | PrimePowerTensorTower |
| solenoid 同余核正合 | Lean anchor | ExactSequence |
| prime-adic 隐路径常值 | Lean anchor | HiddenMotionRigidity |
| genus / class residual 精确分类 | Open | future bridge |
| 有效最小 witness prime 上界 | Open | effective number theory |

---

# 73. 必要有限测试

每个模块至少包含：

1. 非空证书；
2. 非平凡证书；
3. 边界反例；
4. 最小性见证；
5. 小规模枚举；
6. 来源标记。

建议测试：模 \(12,30,60\) CRT、\(p=2\) 的 Golden 边界、\(-20\) 两二次型、crossing 相位模 \(3,4,12\)、同素数冗余、三状态 factorization 失败、小型 prime-time tomography。

---

# 74. 形式化准入纪律

不得：

- 用 `axiom` 安装局部—全局原理；
- 把有限 `decide` 包装成无限分类；
- 把同判别式定义成同类；
- 把所有素数分裂相同定义成全局等价；
- 省略 \(p=2,3,5\) 边界；
- 把窗口张量分解扩大为物理态乘积；
- 把纸面 set-cover 等价声称为已实现最优算法；
- 用文件名或注释替代 proof term。

推荐顺序：基础接口、反模型、CRT 静态完备性、动态 congruence、三环有限分类、crossing 周期、\(p\)-进几何、genus/class 层。

---

# Part X：哲学含义、研究纲领与严格非主张

# 75. 本体论：对象不是其任一局部投影

一个全局对象 \(x\) 在接口 \(i\) 下只显现为 \(q_i(x)\)。完整画像对应候选交纤维：

\[
\bigcap_iq_i^{-1}(o_i).
\]

若交为单点，局部画像恢复全局身份；若含多个对象，局部—全局余量非空。

“隐藏信息”首先指读出纤维中的未区分方向，不自动等于物理隐藏变量。

---

# 76. 认识论：知识是局部画像上的稳定真值

观察者知道 \(P\)，不是因为拥有全部状态，而是因为 \(P\) 在其观察纤维上为常值。

一个主体可以知道所有既定局部分裂事实，却仍不知道全局 form class。这里“局部全知”只量化既定接口，不量化所有可能概念。

---

# 77. 时间论：时间是素数画像轨迹的移位

\[
\operatorname{PTr}(x)
=
(q_i(F^nx))_{i,n},
\]

\[
\operatorname{PTr}(Fx)
=
S(\operatorname{PTr}(x)).
\]

时间推进是删除所有素数坐标的当前切片，并把下一切片移到零时刻。

每个有限素数幂观察者都可能看到周期返回，而全局轨道仍不返回。状态读出重复不等于历史深度归零。

---

# 78. 因果论：局部定律是交换图

局部宏观定律存在，当且仅当：

\[
qF=\bar Fq.
\]

若当前局部同类状态未来产生不同输出，则不存在只依赖当前局部画像的确定宏观定律。记忆、额外素数与干预响应都是修复 carry 的候选精化。

---

# 79. 同一性：局部同一、行为同一与全局同一

\[
\begin{aligned}
x\sim_Jy
&:\quad \text{当前局部同一};\\
x\sim_J^\infty y
&:\quad \text{未来行为同一};\\
x=y
&:\quad \text{全局状态同一}.
\end{aligned}
\]

一般只有：

\[
x=y
\Rightarrow
x\sim_J^\infty y
\Rightarrow
x\sim_Jy.
\]

反向均可能失败。

---

# 80. 科学哲学：局部实验与全局理论

每个新素数实验通过新增读出缩小候选纤维。实验体系可按核包含、目标风险、信息容量、成本、动态完成深度与鲁棒性比较。

发现一对全部既定局部接口都无法区分、但目标值不同的状态，是精确的正知识：它指出缺失概念维度。

---

# 81. 数学哲学：局部—全局问题是观察完备性问题

许多数论问题可重述为：

\[
X
\xrightarrow{q_{\mathrm{loc}}}
\prod_vX_v
\]

是否：

- 单射；
- 满射到兼容族；
- 对指定性质充分；
- 具有有限证书；
- 存在有效重建算法。

单射问题、Hasse 问题、class problem 和 effective witness problem 是不同层次。

---

# 82. 计算哲学：可组合局部执行单元

不同素数坐标并行，同一素数精度增量。最小观察预算是组合优化问题，完整行为商是状态最小化问题。

高效系统不应默认重建全局状态；它应针对任务选择最小充分画像，并保留目标改变时重新精化的能力。

---

# 83. 与量子观察的有限接口

仓库已证明：

\[
M_M(\mathbb C)
\simeq
\bigotimes_{p^e\parallel M}M_{p^e}(\mathbb C).
\]

本文不主张：

- 量子基本粒子就是素数；
- 波函数真实生活在 \(\prod_p\mathbb Z_p\)；
- prime-power tensor factors 必为物理 subsystem；
- 观察者意识由 CRT 产生；
- Born 规则由素数分解推出。

---

# 84. 严格非主张

本文明确不声称：

1. 素数具有意识、感觉、意志或人格；
2. 所有数学对象都由素数观察者生成；
3. 物理宇宙本体是 \(p\)-进或 adelic；
4. 全部局部数据总能胶合成全局对象；
5. 全部素数分裂画像确定二次型类；
6. 同判别式二次型在全部局部处等价；
7. genus、spinor genus 与 class group 层已闭合；
8. CRT 自动提供来源真实性或物理独立性；
9. 有限素数预算能无条件识别无界整数；
10. 模相位为零等于整数相位为零；
11. 局部周期等于全局轨道周期；
12. prime-adic 隐运动刚性排除离散跳变；
13. 形式定义证明现实中存在相应设备；
14. 素数观察者理论证明黎曼猜想；
15. splitting、Pell、crossing 或 solenoid 已构成 RH 的全局正性桥；
16. 本文新增纸面定理已经通过 Lean kernel；
17. 文件长度、定理数量或命名新颖性证明原创性。

---

# 85. 核心定理链

\[
\boxed{
\begin{aligned}
&\text{局部读出族 }(q_{p,k})\\
&\Downarrow\\
&\ker(q_J)=\bigcap_{i\in J}\ker(q_i)\\
&\Downarrow\\
&\text{不同素数 CRT 联合；同素数精度过滤}\\
&\Downarrow\\
&\operatorname{LGRes}(q)
=\text{全部局部接口仍看不见的全局差异}\\
&\Downarrow\\
&\sim_J^\infty=C_F(\sim_J)\\
&\Downarrow\\
&Z_J^\infty=\text{规范预测商}\\
&\Downarrow\\
&\text{有限系统有有限素数—时间证书}\\
&\Downarrow\\
&\text{目标相对最小充分画像、成本与策略能力}.
\end{aligned}
}
\]

算术实例链：

\[
\boxed{
\text{判别式 character}
\to
\text{三环分裂画像}
\to
\text{模 }60\text{ 的二元纤维}
\to
\text{定向位完成}
\to
\text{同判别式全局类余量}.
}
\]

动态 crossing 链：

\[
\boxed{
\Psi(SA)=\Psi(A)-2
\Rightarrow
T(p^k)=\frac{p^k}{\gcd(p^k,2)}
\Rightarrow
T(m)=\operatorname{lcm}_{p^k\parallel m}T(p^k).
}
\]

---

# 86. 最终定义

## 定义 86.1（素数观察者）

\[
\boxed{
\mathcal O_{p,k}
=
(O_{p,k},q_{p,k})
}
\]

是把全局状态压缩为素数 \(p\)、精度 \(k\) 上局部输出的接口，不是拟人主体。

## 定义 86.2（完整素数观察者系统）

\[
\boxed{
\mathcal O_{\mathbb P}
=
\bigl(
(q_{p,k})_{p,k},
\text{降精度图},
\text{CRT 联合图},
\text{动态更新},
\text{目标族},
\text{成本与准入}
\bigr).
}
\]

## 定义 86.3（素数观察者理论）

它研究：

1. 局部接口如何形成观察纤维；
2. 不同素数如何联合；
3. 同一素数精度如何递进；
4. 哪些局部族可胶合；
5. 局部画像是否确定全局身份；
6. 动力学是否下降到局部商；
7. 多少素数、精度与时间足以预测；
8. 局部—全局余量由何种代数对象承载；
9. 观察成本如何限制知识与行动；
10. 哪些局部结论不能升级为全局结论。

---

# 87. 结论

\[
\boxed{
\text{素数提供局部坐标，}
\text{观察者提供商与纤维，}
\text{时间提供轨迹完成，}
\text{局部—全局余量保存无法胶合或无法区分的身份。}
}
\]

最重要的结构是：

\[
\boxed{
\text{横向 prime factorization}
\times
\text{纵向 precision filtration}
\times
\text{前向 temporal completion}.
}
\]

完整全局对象能否由该网格恢复，不由定义保证，而由分离性、兼容性、胶合性、最小性与现实实现逐层决定。

> 每个素数只看见一个局部世界；多个素数可以通过 CRT、逆极限或张量结构联合；但联合读出是否足以恢复全局身份、预测未来、证明存在或支持行动，必须由明确的核、纤维、缺陷、成本与普适性质逐层证明。

---

# Appendix A：记号表

| 记号 | 含义 |
|---|---|
| \(X\) | 全局状态类型 |
| \(\operatorname{Adm}\) | 准入谓词 |
| \(a\) | 实际锚点 |
| \(U\) | 干预／输入类型 |
| \(F\) | 更新或受控更新族 |
| \(\mathbb P\) | 素数类型 |
| \((p,k)\) | 素数—精度坐标 |
| \(O_{p,k}\) | 局部输出类型 |
| \(q_{p,k}\) | 局部读出 |
| \(J\) | 有限观察预算 |
| \(q_J\) | 联合读出 |
| \(R_J\) | 联合读出纤维关系 |
| \(Z_J\) | 静态观察商 |
| \(W_{J,m}\) | 有限素数—时间读出词 |
| \(\sim_J^\infty\) | 完整未来局部等价 |
| \(Z_J^\infty\) | 预测完成商 |
| \(\operatorname{LGRes}\) | 局部—全局身份余量 |
| \(\operatorname{TargetRes}\) | 目标相对余量 |
| \(\mathscr R(p,\Delta)\) | 素数—判别式互反矩阵 |
| \(\Sigma_3\) | Gaussian/Eisenstein/Golden 三环画像 |
| \(\omega_5\) | 模五定向完成位 |
| \(d_p\) | \(p\)-进观察距离 |
| \(\operatorname{PTr}\) | 素数—时间完整轨迹 |
| \(C_F(R)\) | 全迭代 congruence kernel |
| \(\Psi\) | crossing winding phase |

---

# Appendix B：模 \(60\) 三环画像完整表

| \(r\bmod60\) | Gaussian | Eisenstein | Golden | 三环画像 |
|---:|:---:|:---:|:---:|:---:|
| 1  | S | S | S | SSS |
| 7  | I | S | I | ISI |
| 11 | I | I | S | IIS |
| 13 | S | S | I | SSI |
| 17 | S | I | I | SII |
| 19 | I | S | S | ISS |
| 23 | I | I | I | III |
| 29 | S | I | S | SIS |
| 31 | I | S | S | ISS |
| 37 | S | S | I | SSI |
| 41 | S | I | S | SIS |
| 43 | I | S | I | ISI |
| 47 | I | I | I | III |
| 49 | S | S | S | SSS |
| 53 | S | I | I | SII |
| 59 | I | I | S | IIS |

纤维配对：

\[
\begin{aligned}
SSS &: \{1,49\},\\
SSI &: \{13,37\},\\
ISS &: \{19,31\},\\
ISI &: \{7,43\},\\
SIS &: \{29,41\},\\
SII &: \{17,53\},\\
IIS &: \{11,59\},\\
III &: \{23,47\}.
\end{aligned}
\]

---

# Appendix C：核心 Lean 风格接口草案

```lean
namespace D5.S3.PrimeObservers

structure PrimeScale where
  p : ℕ
  hp : Nat.Prime p
  k : ℕ
  hk : 0 < k

structure Model where
  X : Type u
  Admissible : X → Prop
  anchor : {x // Admissible x}
  U : Type v
  step : U → X → X
  Output : PrimeScale → Type w
  readout : (i : PrimeScale) → X → Output i

variable (M : Model)

def StaticEq (J : Finset PrimeScale) (x y : M.X) : Prop :=
  ∀ i, i ∈ J → M.readout i x = M.readout i y

def FullLocalEq (x y : M.X) : Prop :=
  ∀ i, M.readout i x = M.readout i y

def LocalGlobalResidual : Type _ :=
  {xy : M.X × M.X //
    xy.1 ≠ xy.2 ∧ M.FullLocalEq xy.1 xy.2}

def DynamicEq
    (F : M.X → M.X)
    (J : Finset PrimeScale)
    (x y : M.X) : Prop :=
  ∀ n i, i ∈ J →
    M.readout i (F^[n] x) = M.readout i (F^[n] y)

end D5.S3.PrimeObservers
```

---

# Appendix D：开放研究问题

## D.1 有效 witness prime

给定有限判别式或二次型候选族，若全素数画像可区分它们，给出最小区分素数的显式上界。

## D.2 Genus—class 余量

形式化：

\[
\text{global classes}
\to
\text{spinor genera}
\to
\text{genera}
\to
\text{local profiles}.
\]

## D.3 动态 reciprocity observer

把互反 character 随矩阵／Pell／crossing 更新的变化组织成 cocycle，并研究其行为商。

## D.4 Adelic behavior completion

统一有限素数、\(p\)-进精度、无穷位与时间：

\[
\operatorname{Trace}:
X\to
\prod_{v\in\mathcal V_{\mathbb Q},n\in\mathbb N}O_{v,n}.
\]

## D.5 观察成本渐近律

研究最优素数预算成本是否接近 \(\log N\)，以及动态干预能否降低静态传感成本。

## D.6 错误修正 CRT

在局部坐标有噪声、缺失或 Byzantine 错误时，建立唯一恢复与列表恢复理论。

## D.7 自动机最小化

比较 Myhill–Nerode 行为商、prime-time behavior quotient、局部传感器 set cover 与 belief-state completion。

## D.8 素数观察者与量子窗口

只有在明确给出局部代数、态限制、通道分解和可测实现后，研究 prime-power tensor factors 的物理意义。

## D.9 Local–global residual cohomology

寻找统一缺陷对象，使 \(\operatorname{LGRes}=0\) 等价于局部数据有效下降／胶合，非零时产生 obstruction class。

## D.10 与显式公式和 RH 的边界

研究 prime-indexed readouts 与 Weil / heat-trace 的合法桥接，但必须单独证明全局正性、解析延拓与零点定位；不得从局部观察统一直接推出 RH。

---

# Appendix E：版本记录

- **v1.0 — 2026-08-21**：建立单卷素数观察者理论；完成静态联合、CRT 层析、局部—全局余量、动态完成、有限素数—时间层析、三环模六十模型、判别式负二十反模型、crossing 局部周期、\(p\)-进几何、solenoid 隐纤维、知识、行动、算法、Lean 路线与严格非主张。

---

# Part XI：追加式第二阶段——表达饱和、角色秩与观察语言边界

> **追加说明。** 以下各节是 v1.1 的追加式扩展，不改写 v1.0 已有定义与结论。它们进一步回答四个问题：当全部既定素数接口仍不足时，为什么“再加同类接口”必然失败；二次角色究竟能够提供多少独立信息；局部观察之间的代数依赖如何形成错误检测码；以及何种新不变量才是承重修复。

# 88. 观察语言与可表达目标

固定状态类型 \(X\)、索引类型 \(\mathcal I\) 与局部读出族：

\[
q_i:X\to O_i.
\]

定义完整联合读出到有效像：

\[
q_{\mathcal I}^{\operatorname{eff}}:
X\to
\operatorname{Im}(q_{\mathcal I}),
\qquad
q_{\mathcal I}(x)=(q_i(x))_{i:\mathcal I}.
\]

## 定义 88.1（观察语言）

由接口族 \(q\) 可表达的、值域为 \(Y\) 的目标组成：

\[
\boxed{
\operatorname{Expr}_Y(q)
=
\left\{
T:X\to Y
\ \middle|\
\exists\bar T:\operatorname{Im}(q_{\mathcal I})\to Y,
\ T=\bar T\circ q_{\mathcal I}^{\operatorname{eff}}
\right\}.
}
\]

它不是语法字符串集合，而是全部在完整联合观察纤维上常值的目标。

## 定义 88.2（观察语言核）

\[
\boxed{
R_q(x,y)
\iff
\forall i:\mathcal I,
\ q_i(x)=q_i(y).
}
\]

## 定理 88.1（完整观察表达判据）

对任意 \(T:X\to Y\)，以下等价：

1. \(T\in\operatorname{Expr}_Y(q)\)；
2. \(R_q\subseteq\ker T\)；
3. 对任意 \(x,y\)：

\[
\left(\forall i,
q_i(x)=q_i(y)\right)
\Longrightarrow
T(x)=T(y).
\]

### 证明

若 \(T=\bar Tq_{\mathcal I}^{\operatorname{eff}}\)，完整画像相等立即推出目标相等。反之，在有效像上定义：

\[
\bar T(q_{\mathcal I}(x))=T(x).
\]

纤维稳定性保证该定义与代表选择无关。这里使用有效像而非整个形式乘积，因此不需要为未实现画像任意补值。\(\square\)

## 推论 88.1（局部—全局余量的目标版本）

定义：

\[
\operatorname{LGRes}_T(q)
=
\sum_{x,y:X}
R_q(x,y)
\times
(Tx\ne Ty).
\]

则：

\[
\boxed{
\operatorname{LGRes}_T(q)=\varnothing
\iff
T\in\operatorname{Expr}_Y(q).
}
\]

这比“完整读出是否单射”更适合任务相对研究：即使 \(R_q\) 非平凡，某个特定目标仍可能完全可表达。

---

# 89. 水平饱和定理：更多同类接口何时永远无效

对任意子族 \(J\subseteq\mathcal I\)，联合读出 \(q_J\) 都被完整读出精化：

\[
q_J\preceq q_{\mathcal I}.
\]

## 定理 89.1（同族修复不可能性）

若：

\[
T\notin\operatorname{Expr}_Y(q),
\]

则对任意子族 \(J\subseteq\mathcal I\)，包括任意有限、可数或全部允许子族，都有：

\[
\boxed{
T\notin\operatorname{Expr}_Y(q_J).
}
\]

### 证明

存在 \(x,y\) 使所有 \(q_i\) 均相同而 \(T(x)\ne T(y)\)。它们当然在任意子族上仍相同，因此任何 \(q_J\) 都不能决定 \(T\)。\(\square\)

## 原理 89.1（横向饱和）

一旦所有既定类型的局部接口已经联合，剩余目标缺陷不能再由“更多同类型接口”修复。此时需要的不是更大的索引集合，而是新的概念维度。

这精确区分：

\[
\boxed{
\text{预算不足}
\ne
\text{观察语言不足}.
}
\]

预算不足可以通过增加已有传感器修复；观察语言不足必须改变传感器语义。

## 定义 89.1（语义完成）

对目标 \(T:X\to Y\)，定义：

\[
\boxed{
\operatorname{SemComp}_T(q)
=
\left(x\mapsto(q_{\mathcal I}(x),T(x))\right).
}
\]

它是保留完整既有画像并使 \(T\) 可表达的最小共同精化。

## 定理 89.2（语义完成的普适最小性）

若读出 \(e:X\to E\) 同时满足：

\[
q_{\mathcal I}\preceq e,
\qquad
T\preceq e,
\]

则：

\[
\operatorname{SemComp}_T(q)\preceq e.
\]

该定理是形式概念动力学完成算子在素数观察者语言上的直接专门化。

## 实例 89.1（判别式观察语言饱和）

若接口族只允许读取二次型判别式所决定的分裂数据，则同判别式的 \(Q_1,Q_2\) 在全部此类接口上相同，而 `represents 1` 目标不同。由定理 89.1，增加任意数量的同类分裂接口都不能修复；必须加入表示数、form class、ideal class 或其他真正区分类的观察坐标。

---

# 90. 有限阿贝尔群上的二元角色观察

令 \(G\) 为有限阿贝尔群，记：

\[
\mu_2=\{+1,-1\}.
\]

给定二元角色（character）：

\[
\chi_j:G\to\mu_2,
\qquad
j=1,\ldots,m.
\]

定义联合角色画像：

\[
\Phi_{\chi}:G\to\mu_2^m,
\qquad
\Phi_{\chi}(g)
=(\chi_1(g),\ldots,\chi_m(g)).
\]

令：

\[
H
=
\langle\chi_1,\ldots,\chi_m\rangle
\le
\operatorname{Hom}(G,\mu_2).
\]

因为每个元素阶至多为二，\(H\) 是一个 \(\mathbb F_2\)-向量空间。记：

\[
r=\dim_{\mathbb F_2}H.
\]

## 定理 90.1（角色秩—画像基数定理）

在有限群对偶性下：

\[
\boxed{
\begin{aligned}
\ker\Phi_{\chi}
&=
\bigcap_{j=1}^{m}\ker\chi_j,\\
|\operatorname{Im}\Phi_{\chi}|
&=2^r,\\
|\Phi_{\chi}^{-1}(b)|
&=\frac{|G|}{2^r}
\quad
\text{对每个已实现画像 }b.
\end{aligned}
}
\]

### 证明

第一式由乘积映射的核直接得到。把 \(g\in G\) 送到对 \(H\) 的求值函数：

\[
\operatorname{ev}_g:
H\to\mu_2,
\qquad
\chi\mapsto\chi(g).
\]

有限阿贝尔群的对偶性给出：

\[
G/\operatorname{Ann}(H)
\simeq
\widehat H,
\]

而：

\[
|\widehat H|=|H|=2^r.
\]

画像映射与该求值映射只有坐标选择差异，因此像大小为 \(2^r\)。每个非空纤维是核的陪集，故具有统一大小。\(\square\)

## 推论 90.1（均匀输入的信息精确值）

若 \(g\) 在 \(G\) 上均匀分布，则：

\[
\boxed{
H(\Phi_{\chi}(g))=r\text{ bit},
}
\]

以及：

\[
\boxed{
H(g\mid\Phi_{\chi}(g))
=
\log_2|G|-r.
}
\]

因此角色数量 \(m\) 不是信息量；真正的信息量是角色张成空间的秩 \(r\)。

## 定理 90.2（角色冗余判据）

加入新角色 \(\chi\) 不缩小联合观察核，当且仅当：

\[
\boxed{
\chi\in H.
}
\]

等价地，新输出可以由已有输出的乘积恢复。

## 推论 90.2（最小完整角色子族）

产生相同联合核的最小角色子族大小恰为：

\[
r.
\]

任意 \(H\) 的基都是最小充分观察集。

---

# 91. 二次观察者的能力上界：只能看到 \(G/G^2\)

令全部二元角色共同观察：

\[
\Phi_2:
G\to
\prod_{\chi\in\operatorname{Hom}(G,\mu_2)}\mu_2.
\]

定义平方子群：

\[
G^2
=
\langle g^2:g\in G\rangle.
\]

## 定理 91.1（全二次角色核）

\[
\boxed{
\bigcap_{\chi:G\to\mu_2}\ker\chi
=
G^2.
}
\]

因此完整二次角色画像精确决定：

\[
\boxed{
G/G^2,
}
\]

而不是完整的 \(G\)。

### 证明

每个二元角色都杀掉平方：

\[
\chi(g^2)=\chi(g)^2=1,
\]

故 \(G^2\) 包含于公共核。反向，\(G/G^2\) 是有限初等二群，所有到 \(\mu_2\) 的线性泛函分离其不同元素，故公共核不能更大。\(\square\)

## 原理 91.1（二次观察上限）

\[
\boxed{
\text{加入所有可能的二次分裂观察者，}
\text{最多恢复最大初等二商 }G/G^2.
}
\]

若 \(G^2\ne1\)，任何数量的二元角色都不能恢复完整群元素。

## 定理 91.2（一般幂角色层）

令 \(\mu_n\) 为复数中的 \(n\) 次单位根。对有限阿贝尔群 \(G\)：

\[
\boxed{
\bigcap_{\chi:G\to\mu_n}\ker\chi
=
G^n.
}
\]

所以阶除以 \(n\) 的角色共同看到最大指数整除 \(n\) 的商：

\[
G/G^n.
\]

这给出角色阶精化塔：

\[
\text{quadratic}
\preceq
\text{quartic}
\preceq
\cdots
\preceq
\text{full character profile}.
\]

---

# 92. 模六十的三环画像其实已经穷尽全部二次角色

取：

\[
G=(\mathbb Z/60\mathbb Z)^\times.
\]

由 CRT：

\[
G
\simeq
(\mathbb Z/4\mathbb Z)^\times
\times
(\mathbb Z/3\mathbb Z)^\times
\times
(\mathbb Z/5\mathbb Z)^\times
\simeq
C_2\times C_2\times C_4.
\]

因此：

\[
G/G^2\simeq C_2^3.
\]

Gaussian、Eisenstein、Golden 三个 split/inert 角色分别给出三个独立二元角色。其画像已经达到八个可能值，所以它们张成：

\[
\operatorname{Hom}(G,\mu_2).
\]

## 定理 92.1（三环画像的精确公共核）

\[
\boxed{
\ker\bar\Sigma_3
=G^2
=
\{1,49\}.
}
\]

因此每个画像纤维均为：

\[
\boxed{
\{r,49r\}
\quad(\bmod 60).
}
\]

这解释了 Appendix B 中的全部配对，而不需要逐行偶然核对。

## 推论 92.1（再加二次分裂场仍不增加信息）

任何导出自 \((\mathbb Z/60\mathbb Z)^\times\) 的额外二次角色都已是三者的乘积。因此它只增加冗余校验，不缩小二元纤维。

## 定理 92.2（缺失位不是二元群角色）

v1.0 定义的模五定向位 \(\omega_5\) 可以区分每个二元纤维，但它不是：

\[
G\to C_2
\]

的群同态。

### 显式见证

取 \(7\in G\)。其模五值为二，因此：

\[
\omega_5(7)=0.
\]

但：

\[
7^2\equiv49\pmod{60},
\qquad
\omega_5(49)=1.
\]

若 \(\omega_5\) 为二元角色，应有：

\[
\omega_5(7^2)=2\omega_5(7)=0,
\]

矛盾。

## 推论 92.2（真正的群论完成需要四次角色）

要在保持群同态结构的同时恢复 \(C_4\) 因子，必须允许：

\[
\psi_5:G\to\mu_4
\]

这样的四次角色，例如令模五生成元二映到 \(i\)。于是定义：

\[
\Psi_{60}
=
(\chi_{-4},\chi_{-3},\psi_5):
G\to\mu_2\times\mu_2\times\mu_4.
\]

该映射可分离全部模六十单位类。

因此，原有定向位是一个合法的集合值完成；四次角色则是保持群结构的代数完成。二者完成相同身份任务，但携带不同结构。

---

# 93. 算术观察码：角色关系就是奇偶校验

把：

\[
\mu_2\simeq\mathbb F_2,
\qquad
(-1)^b\leftrightarrow b
\]

作为编码。联合角色画像变成线性映射：

\[
b_\chi:G\to\mathbb F_2^m.
\]

## 定义 93.1（角色关系空间）

\[
\boxed{
\mathcal R_\chi
=
\left\{
a\in\mathbb F_2^m
\ \middle|\
\prod_{j=1}^{m}\chi_j^{a_j}=1
\right\}.
}
\]

它记录已有角色之间的全部乘法依赖。

## 定义 93.2（可实现观察码）

\[
\boxed{
\mathcal C_\chi
=\operatorname{Im}(b_\chi)
\le\mathbb F_2^m.
}
\]

## 定理 93.1（角色码对偶性）

相对于标准点积：

\[
\boxed{
\mathcal C_\chi
=
\mathcal R_\chi^{\perp}.
}
\]

### 证明

若 \(a\in\mathcal R_\chi\)，对任意 \(g\)：

\[
1
=
\prod_j\chi_j(g)^{a_j}
=
(-1)^{\langle a,b_\chi(g)\rangle},
\]

故每个可实现画像与每个关系向量正交。又：

\[
\dim\mathcal C_\chi=r,
\qquad
\dim\mathcal R_\chi=m-r,
\]

维数相加为 \(m\)，所以包含关系为等号。\(\square\)

## 推论 93.1（语义信息与传输冗余分离）

\[
\boxed{
\begin{aligned}
r
&=\text{独立语义 bit 数};\\
m-r
&=\text{角色关系／校验 bit 数}.
\end{aligned}
}
\]

加入依赖角色不会增加可区分状态数，却可以增加错误检测能力。

## 定义 93.3（最小距离）

\[
d_{\min}(\mathcal C_\chi)
=
\min\{\operatorname{wt}(c):c\in\mathcal C_\chi,\ c\ne0\}.
\]

标准编码论给出：

- 可检测至多 \(d_{\min}-1\) 个任意 bit 错误；
- 可唯一纠正至多：

\[
\left\lfloor\frac{d_{\min}-1}{2}\right\rfloor
\]

个错误。

## 原理 93.1（语义余量不是噪声）

若两个全局状态落在 \(\ker b_\chi\) 的同一陪集中，它们产生完全相同的合法码字。编码冗余不能区分它们，因为这不是传输错误，而是观察语言本身的语义余量。

因此必须分开：

\[
\boxed{
\text{error correction}
\ne
\text{concept completion}.
}
\]

---

# 94. 角色传感器选择由 set cover 降为线性拟阵

一般观察接口的最小选择是 set cover 型组合问题。但若全部候选接口都是二元角色，则可利用线性结构。

设候选角色集合为 \(E\)，其张成空间为：

\[
H=\langle E\rangle.
\]

## 定理 94.1（完整角色画像的充分子族判据）

对子集 \(B\subseteq E\)，以下等价：

1. \(B\) 与 \(E\) 产生相同观察核；
2. \(B\) 与 \(E\) 产生相同可表达目标族；
3. \(\langle B\rangle=H\).

## 推论 94.1（最小基数）

最小充分子族大小为：

\[
\boxed{
\dim_{\mathbb F_2}H.
}
\]

## 定理 94.2（最小成本角色基）

若每个角色 \(e\in E\) 有非负成本 \(c(e)\)，则在按成本从小到大扫描、只在保持线性独立时加入角色的贪心算法，产生一个最小总成本基。

这是线性拟阵的最小权基定理。它说明：

\[
\boxed{
\text{一般素数传感器选择可能是困难的 set cover；}
\text{角色传感器特例可化为多项式时间线性代数。}
}
\]

## 推论 94.2（自适应最坏情况下界）

若全部 \(2^r\) 个独立角色画像均可能出现，而每次实验只返回一个 bit，则任何确定性自适应策略的最坏情况深度至少为：

\[
r.
\]

选择一组角色基可在恰好 \(r\) 次非自适应实验中达到该下界。

---

# Part XII：Galois 观察、复合域融合与互反校验

# 95. Frobenius 观察者

令 \(L/K\) 为有限 Galois 扩张。对在 \(L\) 中不分歧的有限素位 \(\mathfrak p\)，定义：

\[
q_L(\mathfrak p)
=
\operatorname{Frob}_{\mathfrak p}(L/K).
\]

在一般 Galois 群中，它是共轭类；在阿贝尔扩张中，它是一个规范群元素。

## 定义 95.1（Galois 素数观察者）

\[
\boxed{
\mathcal O_L:
\mathfrak p
\longmapsto
\operatorname{Frob}_{\mathfrak p}(L/K)
}
\]

连同 ramified / unramified 标签，称为由扩张 \(L/K\) 给出的素数观察者。

二次扩张时：

\[
\operatorname{Gal}(L/K)\simeq C_2,
\]

其 Frobenius 读出正是 split / inert 的二元角色；分歧素数属于单独边界分支。

## 原理 95.1（Frobenius 观察不是素数身份）

一个固定有限扩张只产生有限多个共轭类输出，因此必然把无穷多个素数合并。它观察的是素数在该扩张中的局部算术行为，不是素数的完整整数身份。

Mathlib 已提供一般环论框架中的 Frobenius 元素、存在性、共轭变换与 inertia 差异接口；本文提出的桥接层应优先复用 `Mathlib.RingTheory.Frobenius`，而不是重新定义平行 Frobenius 理论。

---

# 96. 复合域是多 Galois 观察者的兼容融合

令 \(L_1/K,L_2/K\) 为有限 Galois 扩张，定义：

\[
L=L_1L_2,
\qquad
E=L_1\cap L_2.
\]

限制映射给出：

\[
\operatorname{res}:
\operatorname{Gal}(L/K)
\to
\operatorname{Gal}(L_1/K)
\times
\operatorname{Gal}(L_2/K).
\]

## 定理 96.1（Galois 兼容纤维积）

\[
\boxed{
\operatorname{Gal}(L_1L_2/K)
\simeq
\operatorname{Gal}(L_1/K)
\times_{\operatorname{Gal}(E/K)}
\operatorname{Gal}(L_2/K).
}
\]

右侧由满足以下兼容性的成对自同构组成：

\[
\sigma_1|_E
=
\sigma_2|_E.
\]

### 证明纲要

一个复合域自同构由其在 \(L_1,L_2\) 上的限制唯一决定，所以限制映射单射。反过来，两个在交域上相同的自同构可以在由 \(L_1,L_2\) 生成的复合域上唯一胶合。\(\square\)

## 推论 96.1（观察者融合像不是任意直积）

两个 Galois 观察者的联合输出一般位于：

\[
\operatorname{Gal}(L_1/K)
\times_{\operatorname{Gal}(E/K)}
\operatorname{Gal}(L_2/K),
\]

而不是完整直积。共同交域 \(E\) 精确承载它们的共享约束。

## 推论 96.2（结构独立判据）

若：

\[
L_1\cap L_2=K,
\]

则：

\[
\operatorname{Gal}(L_1L_2/K)
\simeq
\operatorname{Gal}(L_1/K)
\times
\operatorname{Gal}(L_2/K).
\]

对有限 Galois 扩张，这等价于线性无交。故：

\[
\boxed{
\text{不同扩张名称}
\not\Rightarrow
\text{观察来源独立};
\quad
\text{交域平凡}
\Rightarrow
\text{结构直积分解}.
}
\]

这给第 50 节“来源相关”提供一个精确算术模型：共享子扩张就是共同来源。

## 推论 96.3（阿贝尔 Frobenius 融合）

若 \(L_1,L_2/K\) 阿贝尔，且 \(\mathfrak p\) 在复合域中不分歧，则：

\[
\operatorname{Frob}_{\mathfrak p}(L/K)
\mapsto
\left(
\operatorname{Frob}_{\mathfrak p}(L_1/K),
\operatorname{Frob}_{\mathfrak p}(L_2/K)
\right),
\]

并且该对自动满足交域兼容性。

---

# 97. 二次扩张族的秩就是独立观察 bit 数

设 \(\operatorname{char}K\ne2\)，取：

\[
d_1,\ldots,d_m\in K^\times.
\]

定义复合二次扩张：

\[
L
=
K(\sqrt{d_1},\ldots,\sqrt{d_m}).
\]

令 \([d_j]\) 表示：

\[
K^\times/K^{\times2}
\]

中的平方类，并令：

\[
r
=
\dim_{\mathbb F_2}
\langle[d_1],\ldots,[d_m]\rangle.
\]

## 定理 97.1（二次复合域秩定理）

\[
\boxed{
[L:K]=2^r,
\qquad
\operatorname{Gal}(L/K)\simeq C_2^r.
}
\]

## 推论 97.1（独立平方类等于独立分裂观察）

对不分歧素位，\(m\) 个二次 Frobenius / Legendre 读出的独立信息量恰为 \(r\) bit。若某个 \([d_j]\) 位于其他平方类的线性张成中，则对应分裂角色是其他输出的乘积，不能增加区分能力。

## 实例 97.1（三环扩张）

对：

\[
\mathbb Q(i),
\qquad
\mathbb Q(\sqrt{-3}),
\qquad
\mathbb Q(\sqrt5),
\]

三个相关平方类独立，故复合域次数为八，三环画像具有三 bit 独立信息。这从 Galois 复合域角度重新证明第 92 节的秩结论。

---

# 98. Hilbert 互反律是全局素位奇偶校验

本节调用标准的 Hilbert 互反律作为外部经典数学来源，不标记为仓库 Lean 锚点。

令 \(K\) 为特征不等于二的全局域，\(a,b\in K^\times\)。对每个有限或无穷位 \(v\)，Hilbert 符号为：

\[
(a,b)_v\in\{+1,-1\}.
\]

除有限多个位置外：

\[
(a,b)_v=1.
\]

## 经典定理 98.1（Hilbert 互反乘积公式）

\[
\boxed{
\prod_v(a,b)_v=1.
}
\]

## 推论 98.1（任一局部位由其余全部位决定）

固定 \(v_0\)：

\[
\boxed{
(a,b)_{v_0}
=
\prod_{v\ne v_0}(a,b)_v.
}
\]

因为符号值的逆等于自身。

## 定义 98.1（互反校验码）

可实现 Hilbert 画像位于：

\[
\boxed{
\mathcal C_{\mathrm{Hilb}}
=
\left\{
(s_v)_v:
\text{有限支撑},
\ \prod_vs_v=1
\right\}.
}
\]

这是一个全局偶校验约束。

## 推论 98.2（错误检测能力）

若一份真实画像中恰有一个局部符号被翻转，则报告乘积变为 \(-1\)，错误必被检测。两个符号同时翻转可能重新满足乘积一，所以单个互反校验不能定位错误，也不能检测所有偶数个错误。

## 原理 98.1（二进位与无穷位是承重接口）

只保留奇素数有限位而忽略：

\[
v=2
\quad\text{及}\quad
v\mid\infty
\]

会把它们承担的修正误报为“互反失效”。完整全局校验必须包括所有承重位。

这给项目的无暗账纪律一个数论原型：表面不对称通常由被省略的局部 ledger 承担，而不是由公式凭空破坏。

---

# Part XIII：胶合、规范代表与类群障碍

# 99. Sheaf 等化子：兼容局部族何时必有唯一全局来源

令 \(\mathcal F\) 是某个 site 上的 presheaf，\(\{U_i\to U\}\) 为覆盖。存在两条限制映射：

\[
\prod_i\mathcal F(U_i)
\rightrightarrows
\prod_{i,j}\mathcal F(U_i\times_UU_j).
\]

## 定义 99.1（兼容局部 section）

局部族 \((s_i)_i\) 兼容，当：

\[
s_i|_{U_i\times_UU_j}
=
s_j|_{U_i\times_UU_j}
\]

对所有 \(i,j\) 成立。

## 定义 99.2（零阶胶合余量）

\[
\operatorname{GlueRes}^0(\mathcal F,U)
=
\frac{
\operatorname{Eq}
\left(
\prod_i\mathcal F(U_i)
\rightrightarrows
\prod_{i,j}\mathcal F(U_i\times_UU_j)
\right)
}{
\operatorname{Im}
\left(
\mathcal F(U)\to\prod_i\mathcal F(U_i)
\right)
}.
\]

这里的商是结构记号；在集合语境可以直接使用“兼容但不来自全局 section”的见证类型。

## 定理 99.1（sheaf 胶合等化子）

若 \(\mathcal F\) 为 sheaf，则：

\[
\boxed{
\mathcal F(U)
\simeq
\operatorname{Eq}
\left(
\prod_i\mathcal F(U_i)
\rightrightarrows
\prod_{i,j}\mathcal F(U_i\times_UU_j)
\right).
}
\]

所以兼容局部 sections 存在唯一全局胶合。

## 原理 99.1（局部对象与局部平凡化分离）

即使对象本身能够 sheaf 胶合，其“选择的局部代表、基、坐标或生成元”也可能不能胶合成一个全局代表。后者属于 gauge／torsor 问题，障碍通常出现在一阶 cocycle，而不是对象级零阶等化子。

---

# 100. 局部平凡化的 Čech 接缝

设 \(\mathcal L\) 为线丛或秩一可逆模。在每个 \(U_i\) 上选择局部基：

\[
e_i.
\]

重叠上存在单位：

\[
g_{ij}\in\mathcal O^\times(U_i\cap U_j)
\]

使：

\[
e_i=g_{ij}e_j.
\]

结合一致性给出：

\[
\boxed{
 g_{ij}g_{jk}=g_{ik}
}
\]

即 Čech 一 cocycle。

改变局部基：

\[
e_i'=h_ie_i
\]

会使：

\[
g_{ij}'=h_ig_{ij}h_j^{-1}.
\]

## 定理 100.1（全局平凡化判据）

存在一个全局非消失基，当且仅当过渡 cocycle 为 coboundary：

\[
\boxed{
 g_{ij}=h_i^{-1}h_j
}
\]

对某族局部单位 \((h_i)_i\) 成立。

## 原理 100.1（类不变量记录不可消除接缝）

局部基可以任意改变，但 cocycle 的上同调类不随 gauge 改变。故：

\[
\boxed{
\text{局部都平凡}
\not\Rightarrow
\text{存在全局规范平凡化}.
}
\]

这把 Appendix D.9 的“local–global residual cohomology”从开放口号推进为具体路线：余量不只是一对状态见证，也可以是一个 cocycle class。

---

# 101. Dedekind 域的素理想赋值画像完整恢复理想

令 \(A\) 为 Dedekind 域，\(K\) 为其分式域。非零分式理想形成阿贝尔群：

\[
\operatorname{FracId}(A).
\]

对每个非零素理想 \(\mathfrak p\)，定义指数读出：

\[
v_{\mathfrak p}(I)\in\mathbb Z.
\]

## 经典定理 101.1（分式理想的素理想坐标分解）

\[
\boxed{
I
=
\prod_{\mathfrak p}
\mathfrak p^{v_{\mathfrak p}(I)},
}
\]

且只有有限多个指数非零，分解唯一。

因此：

\[
\boxed{
\operatorname{FracId}(A)
\simeq
\bigoplus_{\mathfrak p}\mathbb Z.
}
\]

## 推论 101.1（全部素理想赋值观察忠实）

\[
\left(
\forall\mathfrak p,
 v_{\mathfrak p}(I)=v_{\mathfrak p}(J)
\right)
\Longrightarrow
I=J.
\]

所以全部 prime-valuation observers 可以完整恢复理想对象身份。

## 原理 101.1（恢复对象不等于恢复生成元）

即使理想 \(I\) 已被全部赋值坐标唯一确定，也不自动存在：

\[
\alpha\in K^\times
\quad\text{使}\quad
I=(\alpha).
\]

“理想是什么”与“理想是否有一个全局单生成元”属于不同目标。

---

# 102. 类群是全局主理想性的最小群值完成

主分式理想组成子群：

\[
\operatorname{Prin}(A)
\le
\operatorname{FracId}(A).
\]

定义理想类群：

\[
\boxed{
\operatorname{Cl}(A)
=
\operatorname{FracId}(A)/\operatorname{Prin}(A).
}
\]

令：

\[
[I]\in\operatorname{Cl}(A)
\]

为理想类。

## 定理 102.1（主理想判据）

\[
\boxed{
I\text{ principal}
\iff
[I]=1.
}
\]

Mathlib 已在 `Mathlib.RingTheory.ClassGroup.Basic` 中实现相应商群，并提供 `ClassGroup.mk_eq_one_iff` 等接口。因此这一方向具有直接形式化入口，而无需从零建设类群。

## 定理 102.2（类群的商普适性质）

若群同态：

\[
f:\operatorname{FracId}(A)\to H
\]

在所有主理想上取单位元，则存在唯一：

\[
\bar f:\operatorname{Cl}(A)\to H
\]

使：

\[
f=\bar f\circ[\cdot].
\]

所以类群是“忽略生成元差异、只保留全局主理想障碍”的规范最小群值观察商。

## 定理 102.3（局部主理想画像的彻底盲性）

Dedekind 域每个非零分式理想在每个非零素理想局部化：

\[
A_{\mathfrak p}
\]

上都是主理想，因为该局部环是 DVR。故布尔读出：

\[
q_{\mathfrak p}^{\operatorname{loc-prin}}(I)
=
\text{“}I_{\mathfrak p}\text{ principal”}
\]

对所有 \(I\) 恒为真。

因此：

\[
\boxed{
\text{全部局部主理想观察者}
\text{不能决定全局主理想性；}
\operatorname{Cl}(A)
\text{是承重完成。}
}
\]

## 定义 102.1（生成元 gauge）

若 \(I=(\alpha)\)，则所有生成元恰为：

\[
\{u\alpha:u\in A^\times\}.
\]

所以生成元空间是单位群 \(A^\times\) 的 torsor。即使主理想性成立，也通常没有规范生成元。

这形成三层严格分离：

\[
\boxed{
\text{理想身份}
\ne
\text{理想类}
\ne
\text{具体生成元 gauge}.
}
\]

---

# 103. 显式类群反模型：\(\mathbb Z[\sqrt{-5}]\)

取：

\[
A=\mathbb Z[\sqrt{-5}],
\]

它是数域 \(\mathbb Q(\sqrt{-5})\) 的整数环，因而为 Dedekind 域。定义理想：

\[
I=(2,1+\sqrt{-5}).
\]

## 定理 103.1（\(I\) 的理想范数为二）

商环中：

\[
2=0,
\qquad
1+\sqrt{-5}=0.
\]

故：

\[
A/I\simeq\mathbb F_2,
\]

从而：

\[
N(I)=2.
\]

## 定理 103.2（\(I\) 非主）

若：

\[
I=(a+b\sqrt{-5}),
\]

则元素范数必须满足：

\[
|N(a+b\sqrt{-5})|
=a^2+5b^2
=2.
\]

但整数方程：

\[
a^2+5b^2=2
\]

无解。因此：

\[
\boxed{I\text{ 非主}.}
\]

## 定理 103.3（每个局部观察都报告主理想）

对任意非零素理想 \(\mathfrak p\)：

\[
I_{\mathfrak p}
\]

是 DVR \(A_{\mathfrak p}\) 上的非零分式理想，故为主理想。

于是：

\[
\boxed{
\forall\mathfrak p,
\ I_{\mathfrak p}\text{ principal},
\qquad
I\text{ not principal}.
}
\]

这给出第 44 节 Hasse 正缺陷的显式见证：

\[
I
\in
\operatorname{HasseDefect}^{+}
\left(
\operatorname{Principal},
(\operatorname{LocallyPrincipal}_{\mathfrak p})_{\mathfrak p}
\right).
\]

## 原理 103.1（对象可胶合，生成元不可胶合）

这里并不是局部理想无法胶合成全局理想：全局理想 \(I\) 已明确存在。失败的是各处局部生成元不能经过单位 gauge 调整后胶合成一个全局生成元。其接缝类正由：

\[
[I]\in\operatorname{Cl}(A)
\]

承载。

---

# Part XIV：独立素数因子的行为完成与时间深度

# 104. 乘积系统的完整轨迹逐坐标分解

令 \(I\) 为有限索引类型。对每个 \(i\)：

\[
X_i,
\qquad
F_i:X_i\to X_i,
\qquad
q_i:X_i\to O_i.
\]

定义独立乘积系统：

\[
X=\prod_iX_i,
\]

\[
F(x)_i=F_i(x_i),
\qquad
q(x)_i=q_i(x_i).
\]

## 定理 104.1（完整轨迹乘积分解）

\[
\boxed{
\operatorname{Tr}_{q,F}(x)
=
\left(
\operatorname{Tr}_{q_i,F_i}(x_i)
\right)_{i:I}.
}
\]

即：

\[
q(F^nx)_i
=
q_i(F_i^n x_i).
\]

## 推论 104.1（动态不可区分逐坐标化）

\[
\boxed{
 x\sim_{q,F}^{\infty}y
\iff
\forall i,
\ x_i\sim_{q_i,F_i}^{\infty}y_i.
}
\]

这是 prime-power 独立因子上完整行为的精确局部—全局原理。

---

# 105. 预测商的乘积定理

记局部预测商：

\[
Z_i
=
X_i/{\sim_{q_i,F_i}^{\infty}}.
\]

全局预测商：

\[
Z
=
X/{\sim_{q,F}^{\infty}}.
\]

## 定理 105.1（独立乘积预测商）

\[
\boxed{
Z
\simeq
\prod_iZ_i.
}
\]

该等价与局部更新诱导的乘积更新相容。

### 证明纲要

定理 104.1 表明全局等价关系正是局部等价关系的逐坐标乘积。商掉乘积关系等价于逐坐标取商，再取有限乘积。\(\square\)

## 推论 105.1（有限状态数乘法）

若所有 \(Z_i\) 有限，则：

\[
\boxed{
|Z|=\prod_i|Z_i|.
}
\]

因此独立素数因子的最小预测状态数相乘，而不是相加。

## 原理 105.1（张量代数分解不自动给出行为分解）

`PrimePowerTensorTower` 给出有限窗口全矩阵代数的素数幂张量分解。要使用定理 105.1，还必须额外证明：

- 状态空间确实为独立乘积；
- 更新逐因子作用；
- 读出逐因子作用；
- 准入集合没有跨因子兼容约束。

缺少这些前件时，代数张量分解不能被偷换为行为商乘积。

---

# 106. 完成深度的最大值定律

定义局部有限词：

\[
W_{i,m}(x_i)
=
\left(
q_i(x_i),q_i(F_ix_i),\ldots,q_i(F_i^m x_i)
\right).
\]

若存在最小 \(m_i\) 使：

\[
W_{i,m_i}(x_i)=W_{i,m_i}(y_i)
\Longrightarrow
x_i\sim_{q_i,F_i}^{\infty}y_i,
\]

称 \(m_i\) 为局部完成深度。

## 定理 106.1（乘积完成深度上界）

令：

\[
m_*=\max_i m_i.
\]

则全局长度 \(m_*\) 的联合读出词决定完整全局行为：

\[
\boxed{
W_{m_*}(x)=W_{m_*}(y)
\Longrightarrow
x\sim_{q,F}^{\infty}y.
}
\]

## 定理 106.2（尖锐最大值定律）

若对每个满足 \(m_i>0\) 的局部因子都有尖锐见证，即存在一对状态在深度 \(m_i-1\) 仍相同、在 \(m_i\) 才被区分；而 \(m_i=0\) 的因子已由当前读出完成，则独立乘积系统的最小全局完成深度恰为：

\[
\boxed{
\max_i m_i.
}
\]

### 证明

上界由逐坐标完成得到。下界取达到最大值的坐标 \(i_0\)，在该坐标放置其尖锐见证，其他坐标取相同状态，即得到全局尖锐见证。\(\square\)

这说明并行素数因子不会把时间深度相加；最慢完成的局部因子决定整体观察深度。

---

# 107. 兼容子系统只能得到 subdirect 行为像

现实全局状态可能不是完整直积，而是兼容子类型：

\[
X
\subseteq
\prod_iX_i.
\]

并假设乘积更新保持 \(X\)。

局部投影给出：

\[
Z_X
\to
\prod_iZ_i.
\]

## 定理 107.1（兼容预测嵌入）

若局部投影联合分离 \(X\) 的全局行为类，则上述映射单射。其像由可同时实现的局部行为类组成，通常是严格子集：

\[
\boxed{
Z_X
\hookrightarrow
\prod_iZ_i.
}
\]

## 原理 107.1（Galois 纤维积与行为 subdirect 的统一）

- 在 Galois 融合中，交域强制局部自同构在重叠上相同；
- 在一般行为系统中，准入谓词强制局部状态满足跨因子约束；
- 在两者中，联合像都是直积中的兼容子对象，而非自由组合。

因此：

\[
\boxed{
\text{local factorization}
\ne
\text{realization independence}.
}
\]

---

# 108. 身份完成、规范完成与行为完成必须分开

前述理想与动力学结果揭示三个不同的完成问题。

## 定义 108.1（身份完成）

寻找读出 \(q\)，使：

\[
q(x)=q(y)
\Rightarrow
x=y.
\]

例如全部素理想赋值完整恢复分式理想。

## 定义 108.2（规范完成）

在对象已经确定后，选择一个代表、基、生成元、截面或 gauge：

\[
s:\operatorname{Im}(q)\to X
\quad\text{或}\quad
\alpha\text{ generating }I.
\]

它可能受 torsor 或 cocycle 障碍影响。

## 定义 108.3（行为完成）

把状态按完整未来读出取商，得到足以闭合更新的最小预测状态。

## 原理 108.1（三完成正交）

\[
\boxed{
\text{识别对象是谁}
\ne
\text{选择对象的规范代表}
\ne
\text{决定对象未来做什么}.
}
\]

- 赋值画像可以完成理想身份，但不提供全局生成元；
- 类群可以判定主理想性，但不选择唯一生成元；
- 未来行为商可以闭合预测，却可能故意合并微观身份不同的对象。

任何“完整观察者”主张必须说明完成的是哪一种任务。

---

# Part XV：Euler 局部因子与解析完成的严格边界

# 109. Euler 因子观察者

设 \(D\subseteq\mathbb C\) 为域。对每个素数 \(p\)，给局部因子：

\[
L_p:D\to\mathbb C.
\]

定义 Euler 局部画像：

\[
\mathcal E(s)
=
(L_p(s))_{p\in\mathbb P}.
\]

有限预算只看到部分积：

\[
L_S(s)
=
\prod_{p\in S}L_p(s).
\]

## 定义 109.1（绝对乘积准入）

写：

\[
L_p(s)=1+u_p(s).
\]

若对每个紧集 \(K\Subset D\)：

\[
\sum_p
\sup_{s\in K}|u_p(s)|
<\infty,
\]

则称局部因子族在 \(D\) 上 normal-convergent。

## 经典定理 109.1（绝对域中的局部乘积完成）

在标准非消失前件下，有限部分积在紧集上一致收敛到全纯函数：

\[
L(s)=\prod_pL_p(s).
\]

若两个局部因子族逐素数相同，则其极限函数在 \(D\) 上相同。

这是真正的局部到全局下降，因为收敛前件提供了合法的无限乘法操作。

## 原理 109.1（形式因子表不等于解析函数）

仅给出全部符号局部因子，不证明：

- 乘积收敛；
- 局部一致收敛；
- 极限非零；
- 可微或全纯；
- 存在更大域上的延拓。

因此：

\[
\boxed{
\text{Euler data}
+
\text{convergence admission}
\Rightarrow
\text{absolute-domain function}.
}
\]

---

# 110. 解析延拓是额外的全局完成

设 \(D\subseteq\Omega\) 且 \(\Omega\) 连通。若 \(L\) 在 \(D\) 上由 Euler 乘积定义，并存在亚纯函数：

\[
\widetilde L:\Omega\to\widehat{\mathbb C}
\]

使其限制等于 \(L\)，则称 \(\widetilde L\) 为解析完成。

## 定理 110.1（延拓唯一性）

若两个亚纯延拓在非空开集 \(D\) 上相同，则它们在连通域 \(\Omega\) 上相同。

这来自恒等定理。

## 原理 110.1（唯一性不提供存在性）

\[
\boxed{
\text{若延拓存在，则唯一；}
\qquad
\text{局部因子本身不构造延拓。}
}
\]

解析延拓的存在需要独立结构：函数方程、积分表示、谱展开、Poisson/Mellin 变换、模性或其他全局机制。

---

# 111. 零点几何不是局部因子的逐坐标性质

在绝对收敛且各局部因子非零的区域，可由正常收敛证明全局乘积非零。但一旦进入仅靠解析延拓定义的区域，函数值不是一个可逐项绝对解释的无限局部乘积。

## 原理 111.1（零点桥梁纪律）

以下推理无效：

\[
\text{每个局部因子非零}
\Longrightarrow
\text{解析延拓在所有点非零}.
\]

也不能从每个局部系数的同号缩放、单位模相位或局部范数界，直接推出延拓后全局零点位置。

合法路线必须包含：

1. 局部因子到绝对域函数的收敛证明；
2. 绝对域函数到更大域解析完成的存在证明；
3. 控制零点的全局正性、谱性或函数方程桥；
4. 对边界项、极点与正则化的独立审计。

这把 Appendix D.10 精化为三层：

\[
\boxed{
\text{local Euler profile}
\to
\text{convergent global function}
\to
\text{analytic completion}
\to
\text{zero geometry}.
}
\]

任何缺失箭头都不能由“素数观察者统一”本身代替。

---

# Part XVI：v1.1 Lean 路线与新增研究命题

# 112. 建议新增模块

在第 64 节目录之上追加：

```text
D5/S3/PrimeObservers/
  Expressivity/
    FullFamilyFactorization.lean
    HorizontalSaturation.lean
    SemanticCompletion.lean
  Characters/
    FiniteBinaryCharacterProfile.lean
    QuadraticObserverCeiling.lean
    CharacterRelationCode.lean
    MinimumWeightCharacterBasis.lean
    ModSixtyQuadraticKernel.lean
  Galois/
    FrobeniusObserver.lean
    CompositumCompatibility.lean
    QuadraticCompositumRank.lean
  Reciprocity/
    HilbertParityInterface.lean
  LocalGlobal/
    SheafEqualizer.lean
    TrivializationCocycle.lean
    ClassGroupPrincipalization.lean
    SqrtNegFiveCountermodel.lean
  Dynamics/
    ProductTraceFactorization.lean
    ProductBehaviorQuotient.lean
    CompletionDepthMaximum.lean
    CompatibleSubdirectBehavior.lean
  Analytic/
    EulerFactorProfile.lean
    NormalProductCompletion.lean
    MeromorphicContinuationUniqueness.lean
```

其中 Hilbert 互反、sheaf cohomology 与完整 Galois compositum桥可能需要较重 Mathlib 基础，应先存放纸面接口与准确依赖审计，不得以 axiom 预装结论。

---

# 113. 第二阶段优先形式化链

## 113.1 纯有限群链

1. 二元角色画像核；
2. 角色张成秩与像基数；
3. 统一纤维大小；
4. 公共二次角色核等于平方子群；
5. 关系码与正交补；
6. 最小角色基与最小成本基；
7. 模六十平方子群恰为 \(\{1,49\}\)。

这条链只需要有限阿贝尔群、有限对偶和 \(\mathbb F_2\) 线性代数，是 v1.1 最适合首先关闭的核心。

## 113.2 类群链

优先复用：

- `Mathlib.RingTheory.ClassGroup.Basic`；
- `ClassGroup.mk_eq_one_iff`；
- Dedekind 域非零分式理想可逆性；
- 局部化为 DVR 的既有接口。

目标：

```lean
theorem principal_iff_class_eq_one

theorem locally_principal_everywhere

theorem sqrt_neg_five_ideal_not_principal

theorem local_principal_profile_not_target_faithful
```

## 113.3 乘积行为链

这条链应只依赖仓库已有：

- `ItineraryCompletion`；
- `ControlledBehaviorUniversality`；
- quotient / product setoid 基础。

优先证明：

```lean
theorem product_trace_eq

theorem product_behavior_relation_iff

theorem product_behavior_quotient_equiv

theorem product_completion_depth_eq_max
```

## 113.4 Galois 链

Mathlib 已有 Frobenius 基础，但复合域的完整 fiber-product 形式可能需要先建设限制映射和交域 API。应先证明纯 Galois 群兼容定理，再把 Frobenius 自然性作为推论，而不是在第一步混合理想分解、ramification 与共轭类技术。

---

# 114. v1.1 证明状态矩阵

| 结论 | 状态 | 推荐依赖 |
|---|---|---|
| 完整观察表达判据 | Paper | effective image factorization |
| 同族修复不可能性 | Paper | kernel inclusion |
| 语义完成最小性 | Paper | ConceptJoinUniversal |
| 二元角色秩—像基数 | Classical paper theorem | finite character duality |
| 每个角色纤维统一大小 | Paper | cosets |
| 全二次角色核为 \(G^2\) | Classical paper theorem | finite abelian duality |
| 模六十核为 \(\{1,49\}\) | Finite certificate | CRT + enumeration/group proof |
| 定向位非群同态 | Finite certificate | \(7^2=49\) |
| 角色码等于关系空间正交补 | Paper | finite linear algebra |
| 最小成本角色基 | Classical | matroid greedy theorem |
| Galois 复合域 fiber product | Classical | finite Galois theory |
| 二次复合域次数 \(2^r\) | Classical | Kummer degree-2 case |
| Hilbert 乘积公式 | External classical | global class field theory |
| sheaf 等化子胶合 | External classical | sheaf axiom |
| 类群判定 principal | Mathlib anchored | ClassGroup.Basic |
| \(\mathbb Z[\sqrt{-5}]\) 局部主而全局非主 | Paper countermodel | norm + DVR localization |
| 乘积行为商分解 | Paper | quotient/product |
| 完成深度最大值 | Paper | finite sharp witnesses |
| Euler 正常乘积完成 | External classical | infinite products |
| 亚纯延拓唯一 | External classical | identity theorem |

---

# 115. v1.1 新增严格非主张

除第 84 节外，再明确：

1. 不声称全部二次角色能恢复任意有限阿贝尔群元素；它们只恢复 \(G/G^2\)。
2. 不声称 v1.0 的模五定向位是 Dirichlet character 或群同态。
3. 不声称角色关系带来的校验冗余能消除观察语言的语义余量。
4. 不声称不同 Galois 扩张自动线性无交或来源独立。
5. 不声称非阿贝尔 Frobenius 有规范元素值；一般只有共轭类。
6. 不声称 Hilbert 互反只量化奇有限素数；二位与无穷位不可省略。
7. 不声称局部平凡对象必有全局规范平凡化。
8. 不声称全部素理想赋值恢复理想后，也自动恢复其生成元。
9. 不声称类群障碍是对象不存在；它阻碍的是全局 principal trivialization。
10. 不声称矩阵代数的 prime-power 张量分解自动推出状态与行为的独立乘积分解。
11. 不声称局部完成深度在存在跨因子约束时仍取简单最大值。
12. 不声称 Euler 局部因子表自动定义收敛函数。
13. 不声称解析延拓唯一性证明解析延拓存在。
14. 不声称绝对收敛域的非零性自动控制延拓域零点。
15. 不声称上述外部经典定理已在当前仓库中获得 Lean proof term。

---

# 116. 第二阶段统一：素数观察者的四种剩余

v1.1 后，可以把局部—全局余量分为四类。

## 116.1 身份余量

\[
R_q(x,y)
\land
x\ne y.
\]

接口无法区分不同对象，例如全部二次角色留下 \(G^2\)。

## 116.2 目标余量

\[
R_q(x,y)
\land
T(x)\ne T(y).
\]

接口对指定任务不充分，例如判别式分裂画像不能决定表示一。

## 116.3 胶合余量

局部数据逐处存在且兼容，但没有全局来源，或局部 trivializations 的 cocycle 非 coboundary。

## 116.4 规范余量

全局对象与性质均已确定，但没有规范代表；所有代表形成某个 gauge 群的 torsor。

因此：

\[
\boxed{
\text{local–global failure}
\ne
\text{identity blindness only}.
}
\]

它可能发生在对象识别、目标决定、局部胶合或规范选择的不同层。

---

# 117. 第二阶段最终命题

素数观察者理论的成熟形式不再只是：

\[
X\to\prod_pO_p.
\]

它应同时记录：

\[
\boxed{
\begin{aligned}
&\text{接口生成的观察语言};\\
&\text{角色／表示张成的有效秩};\\
&\text{局部画像之间的兼容与校验关系};\\
&\text{完整接口仍留下的饱和核};\\
&\text{对象胶合与代表胶合的不同障碍};\\
&\text{独立因子行为商的乘积与兼容子像};\\
&\text{从 Euler 局部数据到解析完成的额外准入。}
\end{aligned}
}
\]

最深的新增结论是：

\[
\boxed{
\text{当全部既定局部接口已经饱和，}
\text{剩余缺陷不会被“更多同类数据”消除；}
\text{它要求一个新的不变量层。}
}
\]

在本文实例中：

\[
\begin{aligned}
\text{二次角色饱和后}
&\Rightarrow
\text{需要四次角色或定向坐标};\\
\text{局部主理想饱和后}
&\Rightarrow
\text{需要 ideal class};\\
\text{局部轨迹饱和后}
&\Rightarrow
\text{需要行为 quotient};\\
\text{Euler 因子饱和后}
&\Rightarrow
\text{仍需要收敛与解析完成桥}.
\end{aligned}
\]

这把“缺什么”从经验猜测升级为核与普适性质能够定位的问题。

---

# Appendix F：v1.1 版本记录与状态勘正

## F.1 版本记录

- **v1.1 — 2026-08-21**：追加观察语言饱和、同族修复不可能性、二元角色秩定理、全二次角色平方子群上限、模六十精确平方核、角色观察码、最小成本角色基、Galois 复合域兼容纤维积、Hilbert 互反校验、sheaf／Čech 胶合、类群 principalization 障碍、\(\mathbb Z[\sqrt{-5}]\) 显式反模型、独立乘积行为商、完成深度最大值与 Euler 解析完成边界。

## F.2 初始机械范围勘正

文件开头“机械范围”描述的是 v1.0 初次生成动作；其后用户已授权把该文件提交到独立分支并建立 pull request。该状态变化不影响任何数学证明等级：文档仍然不是 Lean 真源，所有新增纸面定理仍需独立 proof term、依赖闭包、admission 与冻结收据。

---

# Appendix G：第二阶段外部基础来源

以下来源仅为尚未在本仓库闭合部分的标准数学依据，不替代未来 Lean 证明：

1. J. S. Milne, *Fields and Galois Theory*, v5.10, 2022：有限 Galois 理论、复合域与交域。
2. J. S. Milne, *Algebraic Number Theory*, v3.08, 2020：Dedekind 域、理想分解、赋值与类群背景。
3. J. S. Milne, *Class Field Theory*, v4.03, 2020：局部／全局类域论、Hilbert 互反与 Frobenius 结构。
4. The Stacks Project, Tags `034W`, `034X` 及相关章节：Dedekind 域、局部 DVR 与因子分解。
5. Mathlib documentation：`Mathlib.RingTheory.ClassGroup.Basic`、`Mathlib.RingTheory.Frobenius` 与 Dedekind／FractionalIdeal 模块。

---

# Part XVII：追加式第三阶段——概率素数观察、几乎处处胶合与软完成

> **追加说明。** 以下各节构成 v1.2 的追加式扩展，不改写 v1.0 与 v1.1 的既有定义、定理和边界。本阶段把此前的集合值观察商提升到概率空间、条件期望、随机通道与信息几何；再利用仓库中新闭合的 `PrimeExponentLaw`、`ZetaPrimeIndependence`、`ZetaEntropy` 与 `PrimeSpectrumBoundaryDivergent`，建立素指数画像的乘积概率、全局可实现阈值、精度熵收缩及算术 Fock 观察桥。
>
> **状态约束。** 本阶段明确区分：仓库中已经机器检查的 zeta 边缘律、独立性、熵恒等式和边界发散；本文从这些锚点推出的纸面定理；以及需要 product measure、Borel–Cantelli、条件期望、无限张量或算子代数基础的后续 Lean 目标。

# 118. 从观察纤维到观察 \(\sigma\)-代数

设：

\[
(X,\Sigma_X,\mu)
\]

为概率空间，观察接口为可测映射：

\[
q:X\to O,
\]

其中 \((O,\Sigma_O)\) 为可测空间。

## 定义 118.1（观察 \(\sigma\)-代数）

\[
\boxed{
\mathcal G_q
=
q^{-1}(\Sigma_O)
\subseteq
\Sigma_X.
}
\]

\(\mathcal G_q\) 是观察者能够由输出事件生成的全部可判定事件。集合论纤维描述“哪些点被合并”；\(\sigma\)-代数描述“哪些事件仍可表达”。

## 定义 118.2（概率意义下的精化）

若观察 \(r:X\to R\) 满足：

\[
q=h\circ r
\]

对某个可测 \(h:R\to O\) 成立，则：

\[
\boxed{
\mathcal G_q\subseteq\mathcal G_r.
}
\]

因此确定性概念精化在概率语言中表现为可见事件族的包含。

## 定义 118.3（几乎处处目标充分性）

给定可测目标：

\[
T:X\to Y,
\]

若存在可测：

\[
\overline T:O\to Y
\]

使：

\[
T=\overline T\circ q
\quad\mu\text{-a.e.},
\]

则称 \(q\) 对目标 \(T\) 几乎处处充分。

## 经典定理 118.1（Doob–Dynkin 因子化）

在标准 Borel 目标空间及通常可测性前件下：

\[
T\text{ 对 }\mathcal G_q\text{ 可测}
\]

当且仅当 \(T\) 通过 \(q\) 因子化；在完成 \(\sigma\)-代数中相应结论取几乎处处形式。

## 原理 118.1（点态知识与概率知识分离）

必须区分：

\[
\forall x,y,
q(x)=q(y)\Rightarrow T(x)=T(y)
\]

与：

\[
T=\overline Tq
\quad\mu\text{-a.e.}
\]

前者不允许任何例外状态；后者允许零测纤维缺陷。概率充分性不能被回写成点态充分性。

---

# 119. 条件期望是规范的软完成

设：

\[
T\in L^2(X,\mu;\mathbb R).
\]

若 \(T\) 不能由 \(q\) 精确决定，仍可定义观察者的规范平方损失预测：

\[
\widehat T_q
=
\mathbb E_\mu[T\mid\mathcal G_q].
\]

## 定义 119.1（平方风险余量）

\[
\boxed{
\mathcal R_2(q;T)
=
\mathbb E_\mu
\left[
\left(T-\mathbb E[T\mid\mathcal G_q]\right)^2
\right].
}
\]

## 经典定理 119.1（最小平方风险）

\[
\mathcal R_2(q;T)
=
\inf_{Z\in L^2(\mathcal G_q)}
\mathbb E[(T-Z)^2].
\]

条件期望不是任意预测器，而是 \(L^2\) 中向观察语言闭子空间的正交投影。

## 定理 119.2（零风险判据）

\[
\boxed{
\mathcal R_2(q;T)=0
\iff
T\text{ 对 }\mathcal G_q\text{ 可测，a.e.}
}
\]

因此此前的目标余量获得了定量概率版本：精确因子化失败的程度由条件方差测量。

## 定理 119.3（精化的勾股分解）

若：

\[
\mathcal G_q\subseteq\mathcal G_r,
\]

则：

\[
\boxed{
\mathcal R_2(q;T)
=
\mathcal R_2(r;T)
+
\mathbb E
\left[
\left(
\mathbb E[T\mid\mathcal G_r]
-
\mathbb E[T\mid\mathcal G_q]
\right)^2
\right].
}
\]

故：

\[
\mathcal R_2(r;T)
\le
\mathcal R_2(q;T).
\]

### 证明纲要

\(T-\mathbb E[T\mid\mathcal G_r]\) 与所有 \(\mathcal G_r\)-可测平方可积函数正交，而两个条件期望之差属于 \(L^2(\mathcal G_r)\)。展开平方并消去交叉项。\(\square\)

## 原理 119.1（软完成不等于恢复真状态）

\[
\widehat T_q
\]

只给定损失函数下的最佳可见预测，不消除观察纤维，也不产生被删除的微观状态。

---

# 120. 概率局部—全局胶合质量

设完整局部画像空间为：

\[
O
=
\prod_{i:\mathcal I}O_i,
\]

全局读出为：

\[
q_{\mathrm{all}}:X\to O,
\]

并在 \(O\) 上给定局部模型生成的概率测度 \(\nu\)。假设：

\[
\operatorname{Im}(q_{\mathrm{all}})
\]

为可测集。

## 定义 120.1（全局可实现质量）

\[
\boxed{
\operatorname{RealMass}(q,\nu)
=
\nu\bigl(\operatorname{Im}(q_{\mathrm{all}})\bigr).
}
\]

## 定义 120.2（概率胶合缺陷）

\[
\boxed{
\operatorname{PGlueDefect}(q,\nu)
=
1-
\operatorname{RealMass}(q,\nu).
}
\]

## 定义 120.3（三种胶合强度）

\[
\begin{aligned}
\text{点态全胶合}
&:\quad
\operatorname{Im}(q_{\mathrm{all}})=O;\\
\text{几乎处处胶合}
&:\quad
\operatorname{RealMass}(q,\nu)=1;\\
\text{正质量胶合}
&:\quad
\operatorname{RealMass}(q,\nu)>0.
\end{aligned}
\]

一般只有：

\[
\text{点态全胶合}
\Rightarrow
\text{几乎处处胶合}
\Rightarrow
\text{正质量胶合}.
\]

反向均可能失败。

## 定理 120.1（几乎处处观察同构）

若 \(X,O\) 为标准 Borel 空间，\(q_{\mathrm{all}}\) 为可测单射，且：

\[
\nu(\operatorname{Im}q_{\mathrm{all}})=1,
\]

则可把 \(\nu\) 沿像上的可测逆映射拉回为 \(X\) 上概率测度 \(\mu\)，使：

\[
(q_{\mathrm{all}})_*\mu=\nu,
\]

且 \(q_{\mathrm{all}}\) 在零测集之外给出概率空间同构。

## 原理 120.1（有限边缘相容不等于全局可实现）

Kolmogorov 型扩张只保证相容有限维分布产生乘积路径空间上的测度；它不保证该测度集中在某个具体全局对象类型的画像：

\[
\boxed{
\text{finite-dimensional consistency}
\not\Rightarrow
\nu(\operatorname{Im}q)=1.
}
\]

以下 zeta 素指数模型将给出一个精确阈值实例。

---

# 121. 随机通道、Blackwell 精化与同语言重复极限

确定性读出 \(q:X\to O\) 可视为 Dirac Markov kernel。更一般地，随机观察者为：

\[
K:X\rightsquigarrow O.
\]

## 定义 121.1（Blackwell 精化）

若存在后处理 kernel：

\[
L:O_D\rightsquigarrow O_C
\]

使：

\[
K_C=L\circ K_D,
\]

则称 \(D\) Blackwell-精化 \(C\)。粗观察只是细观察的随机后处理。

## 经典定理 121.1（Blackwell 决策序）

在有限决策问题及其标准推广中，若 \(D\) Blackwell-精化 \(C\)，则对任意先验、行动集和有界损失，使用 \(D\) 的最优 Bayes 风险不高于使用 \(C\) 的最优 Bayes 风险。

## 定理 121.2（同语言重复不可能跨越 kernel）

设基础语义接口：

\[
q:X\to B.
\]

若完整观察 transcript \(Y\) 的条件分布只通过 \(q(x)\) 依赖状态：

\[
K_Y(\cdot\mid x)
=
\overline K_Y(\cdot\mid q(x)),
\]

则：

\[
q(x)=q(y)
\Rightarrow
K_Y(\cdot\mid x)=K_Y(\cdot\mid y).
\]

因此若目标 \(T\) 在某个 \(q\)-纤维内变化，即使重复采集任意多次条件独立或相关噪声样本，只要整个 transcript 仍通过 \(q\) 因子化，就不可能精确决定 \(T\)。

## 推论 121.1（随机版观察语言饱和）

\[
\boxed{
\text{重复测量可以逼近已有语义值，}
\text{但不能创造纤维内不存在于该语言的区别。}
}
\]

---

# Part XVIII：zeta 素指数乘积、全局可实现性与 \(s=1\) 阈值

# 122. 仓库中新闭合的概率锚点

本阶段直接复用以下机器检查结果：

- `D5/S3/Analytic/ZetaGibbs.lean`：在 \(s>1\) 时构造正整数上的 zeta Gibbs 概率；
- `D5/S3/Analytic/Zeta/PrimeExponentLaw.lean`：证明每个素指数具有几何尾分布和点质量；
- `D5/S3/Analytic/Zeta/ZetaPrimeIndependence.lean`：证明全部素数索引的指数坐标构成 `iIndepFun`，不是只证明有限或两两独立；
- `D5/S3/Analytic/Zeta/ZetaEntropy.lean`：证明 zeta 熵有限、Gibbs 熵恒等式及固定对数矩下的最大熵性质；
- `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryDivergent.lean`：把素数倒数级数的边界发散接入一般线性素谱热迹。

以下公式以：

\[
\mathbb P_s(N=n)
=
\frac{n^{-s}}{\zeta(s)},
\qquad
n\ge1,
\qquad
s>1
\]

表示同一概率对象；仓库实现包含零状态但赋予其零质量。

---

# 123. 素指数画像是正整数的完整确定性坐标

对每个素数 \(p\)，定义：

\[
V_p(n)=v_p(n).
\]

定义有限支撑指数空间：

\[
\mathcal E_{\mathrm{fin}}
=
\bigoplus_{p\in\mathbb P}\mathbb N_0
=
\left\{
(e_p)_p:
|\{p:e_p\ne0\}|<\infty
\right\}.
\]

## 定理 123.1（唯一分解画像双射）

\[
\boxed{
\nu:
\mathbb N_{>0}
\overset{\sim}{\longrightarrow}
\mathcal E_{\mathrm{fin}},
\qquad
\nu(n)=(v_p(n))_p.
}
\]

逆映射为：

\[
G(e)
=
\prod_p p^{e_p},
\]

乘积因有限支撑而有限。

## 推论 123.1（全指数语言点态完备）

\[
\forall p,
V_p(m)=V_p(n)
\Rightarrow
m=n.
\]

因此在正整数状态类型上，全部素指数观察者的身份余量为空。

## 原理 123.1（完整指数与粗分裂语言分离）

v1.1 的二次分裂角色只读取有限商或判别式画像；本节的 \(V_p\) 读取每个素数的完整乘法重数。两类“素数观察者”具有不同输出类型与不同 kernel，不得混同。

---

# 124. 任意 \(s>0\) 的独立几何局部模型

对 \(s>0\) 与素数 \(p\)，令：

\[
q_{p,s}=p^{-s}
\in(0,1).
\]

定义零起点几何分布：

\[
\boxed{
\gamma_{p,s}(k)
=
(1-q_{p,s})q_{p,s}^{k},
\qquad
k\in\mathbb N_0.
}
\]

它在每个素数坐标上都是合法概率分布，即使 \(\zeta(s)\) 尚不收敛。

## 定义 124.1（完整独立素指数乘积测度）

在可数乘积空间：

\[
\mathcal E
=
\prod_{p\in\mathbb P}\mathbb N_0
\]

上定义：

\[
\boxed{
\Gamma_s
=
\bigotimes_{p\in\mathbb P}\gamma_{p,s}.
}
\]

## 定理 124.1（有限圆柱质量）

对有限素数集 \(S\) 与指数指定 \(k_p\)：

\[
\Gamma_s
\{e:\forall p\in S,e_p=k_p\}
=
\prod_{p\in S}
(1-p^{-s})p^{-sk_p}.
\]

## 定义 124.2（素数激活事件）

\[
A_p
=
\{e:e_p>0\}.
\]

则：

\[
\Gamma_s(A_p)=p^{-s},
\]

且 \((A_p)_p\) 相互独立。

---

# 125. 几乎处处有限支撑的精确阈值

经典素数倒数发散与普通 \(p\)-级数收敛给出，对 \(s>0\)：

\[
\boxed{
\sum_{p}p^{-s}<\infty
\iff
s>1.
}
\]

## 定理 125.1（素指数画像有限支撑阈值）

\[
\boxed{
\Gamma_s(\mathcal E_{\mathrm{fin}})
=
\begin{cases}
1,&s>1,\\
0,&0<s\le1.
\end{cases}
}
\]

### 证明

有限支撑等价于只有有限多个事件 \(A_p\) 发生。

若 \(s>1\)，则：

\[
\sum_p\Gamma_s(A_p)
=
\sum_pp^{-s}<\infty.
\]

第一 Borel–Cantelli 引理推出几乎必然只有有限多个 \(A_p\) 发生。

若 \(0<s\le1\)，则：

\[
\sum_pp^{-s}=\infty.
\]

因 \(A_p\) 独立，第二 Borel–Cantelli 引理推出几乎必然有无穷多个 \(A_p\) 发生。\(\square\)

## 推论 125.1（有限边缘完全合法但全局对象几乎处处不存在）

当 \(0<s\le1\) 时，每个有限素数集合上的联合几何分布均合法且彼此相容，但乘积测度几乎从不落在任何普通正整数的有限支撑画像上。

这给出：

\[
\boxed{
\text{所有有限局部概率相容}
\not\Rightarrow
\text{几乎处处来自全局整数}.
}
\]

---

# 126. 独立几何素指数的全局可实现定理

## 定理 126.1（全局可实现当且仅当 \(s>1\)）

固定 \(s>0\)。存在正整数值随机变量 \(N\)，使全部指数：

\[
(V_p(N))_{p\in\mathbb P}
\]

相互独立且：

\[
\mathbb P(V_p(N)=k)
=
(1-p^{-s})p^{-sk},
\]

当且仅当：

\[
\boxed{s>1.}
\]

当它存在时，其分布唯一，且：

\[
\boxed{
\mathbb P(N=n)
=
\frac{n^{-s}}{\zeta(s)}.
}
\]

### 证明

若存在这样的 \(N\)，其指数画像必落在 \(\mathcal E_{\mathrm{fin}}\)。独立性与边缘分布迫使画像 law 等于 \(\Gamma_s\)。由定理 125.1，只有 \(s>1\) 时有限支撑具有全质量。

反之若 \(s>1\)，\(\Gamma_s\) 几乎处处落在有限支撑画像上，可沿 \(G\) 推前为正整数概率。对 \(e=\nu(n)\)：

\[
\begin{aligned}
\Gamma_s(\{e\})
&=
\prod_p(1-p^{-s})p^{-se_p}\\
&=
\left(\prod_p(1-p^{-s})\right)n^{-s}\\
&=
\frac{n^{-s}}{\zeta(s)}.
\end{aligned}
\]

唯一性来自全部有限维分布决定乘积测度，以及唯一分解画像的单射性。\(\square\)

## 推论 126.1（zeta 概率的观察者刻画）

\[
\boxed{
\text{zeta law}
=
\text{唯一能够全局实现全部独立几何素指数的正整数 law}.
}
\]

这比 Euler 乘积的形式恒等式更强：它给出局部随机接口、全局可实现性及唯一性三者的统一刻画。

---

# 127. 支撑计数与乘法复杂度

定义：

\[
\omega(N)
=
|\{p:V_p(N)>0\}|,
\]

\[
\Omega(N)
=
\sum_pV_p(N).
\]

前者计算不同素因子数，后者按重数计算总素因子数。

## 定理 127.1（不同素因子数的矩）

在 \(s>1\) 的 zeta law 下：

\[
\boxed{
\mathbb E_s[\omega(N)]
=
\sum_pp^{-s},
}
\]

\[
\boxed{
\operatorname{Var}_s(\omega(N))
=
\sum_pp^{-s}(1-p^{-s}).
}
\]

### 证明

\(\mathbf1_{V_p>0}\) 是相互独立、参数 \(p^{-s}\) 的 Bernoulli 变量，且和几乎处处有限。\(\square\)

## 定理 127.2（总重数期望）

\[
\boxed{
\mathbb E_s[\Omega(N)]
=
\sum_p\frac{1}{p^s-1}.
}
\]

因为：

\[
\mathbb E[V_p]
=
\frac{p^{-s}}{1-p^{-s}}
=
\frac{1}{p^s-1}.
\]

## 定理 127.3（概率生成函数）

对 \(0\le z\le1\)：

\[
\mathbb E[z^{\omega(N)}]
=
\prod_p
\left(1-(1-z)p^{-s}\right).
\]

在收敛允许的 \(z\) 区域：

\[
\mathbb E[z^{\Omega(N)}]
=
\prod_p
\frac{1-p^{-s}}{1-zp^{-s}}.
\]

## 原理 127.1（复杂度是随机激活模式）

在 zeta Gibbs 模型中，一个整数的乘法复杂度可分解为独立素数模态的激活和占据数；这是一种概率编码，不表示现实计算成本必服从同一 law。

---

# 128. 有限素数预算后的精确后验

取有限素数集 \(S\)，观察：

\[
V_p(N)=k_p,
\qquad
p\in S.
\]

令：

\[
a_S
=
\prod_{p\in S}p^{k_p},
\qquad
P_S
=
\prod_{p\in S}p.
\]

则：

\[
N=a_SM,
\qquad
\gcd(M,P_S)=1.
\]

## 定理 128.1（未观察素数保持原 law）

条件于全部已观察指数后，坐标：

\[
(V_p(M))_{p\notin S}
\]

仍相互独立，并保持各自原几何分布：

\[
\mathbb P(V_p(M)=j\mid(V_r)_{r\in S})
=
(1-p^{-s})p^{-sj}.
\]

## 定理 128.2（余因子的 restricted-zeta 后验）

对：

\[
\gcd(m,P_S)=1,
\]

有：

\[
\boxed{
\mathbb P(M=m\mid V_p=k_p,\ p\in S)
=
\frac{m^{-s}}{Z_{S^c}(s)},
}
\]

其中：

\[
Z_{S^c}(s)
=
\prod_{p\notin S}(1-p^{-s})^{-1}
=
\zeta(s)
\prod_{p\in S}(1-p^{-s}).
\]

## 推论 128.1（观察只冻结已读坐标）

在独立 zeta 模型内，观察有限素数不会改变未观察素数的后验；它只把全局整数分解成已知因子 \(a_S\) 与独立余因子 \(M\)。

## 边界 128.1

该后验不适用于一般相关整数 law。它依赖仓库已证明的素指数相互独立性。

---

# Part XIX：素数信息分解、精度收缩与参数几何

# 129. 单素数几何熵

令：

\[
q=p^{-s}.
\]

对：

\[
V_p\sim(1-q)q^k,
\]

其 Shannon 熵（nats）为：

\[
\boxed{
H_p(s)
=
-\log(1-p^{-s})
+
\frac{s\log p}{p^s-1}.
}
\]

### 证明

\[
\begin{aligned}
H(V_p)
&=-\sum_{k\ge0}(1-q)q^k
\bigl(\log(1-q)+k\log q\bigr)\\
&=-\log(1-q)
-\frac{q}{1-q}\log q.
\end{aligned}
\]

代入：

\[
-\log q=s\log p.
\]

\(\square\)

## 原理 129.1（素数越大，完整指数平均信息越小）

函数：

\[
h_{\mathrm{geom}}(q)
=-\log(1-q)-\frac q{1-q}\log q
\]

在 \(0<q<1\) 上严格递增，而 \(p^{-s}\) 随 \(p\) 严格下降。因此固定 \(s>1\) 时：

\[
p<r
\Rightarrow
H_p(s)>H_r(s).
\]

---

# 130. 全局 zeta 熵的 Euler 分解

仓库已证明：

\[
H(N)
=
s\,\mathbb E_s[\log N]
+
\log\zeta(s).
\]

素指数独立与：

\[
\log N
=
\sum_pV_p(N)\log p
\]

进一步给出纸面分解：

## 定理 130.1（全局熵是局部熵之和）

对 \(s>1\)：

\[
\boxed{
H(N)
=
\sum_pH_p(s).
}
\]

即：

\[
\boxed{
H(N)
=
\sum_p
\left[
-\log(1-p^{-s})
+
\frac{s\log p}{p^s-1}
\right].
}
\]

## 定理 130.2（对数能量分解）

\[
\boxed{
\mathbb E_s[\log N]
=
\sum_p\frac{\log p}{p^s-1}
=
-\frac{\zeta'(s)}{\zeta(s)}.
}
\]

## 证明边界

仓库的 `ZetaEntropy.lean` 已闭合全局熵恒等式，但明确把无限素数坐标的熵求和交换留给后续 projective finite-marginal 与可积性发展。本节因此标记为 `Paper + anchored marginals`，不得写成现有 Lean 定理。

---

# 131. Euler 乘积是素数观察码的归一化

定义局部 surprisal：

\[
\ell_{p,s}(k)
=
-\log\gamma_{p,s}(k).
\]

于是：

\[
\boxed{
\ell_{p,s}(k)
=
-\log(1-p^{-s})
+
sk\log p.
}
\]

## 定理 131.1（全局码长可加）

对 \(n\ge1\)：

\[
\boxed{
-\log\mathbb P_s(N=n)
=
\sum_p
\ell_{p,s}(v_p(n)).
}
\]

且：

\[
\boxed{
-\log\mathbb P_s(N=n)
=
\log\zeta(s)+s\log n.
}
\]

### 证明

占据项满足：

\[
\sum_psv_p(n)\log p=s\log n.
\]

零占据基线满足：

\[
\sum_p-\log(1-p^{-s})
=
\log\zeta(s).
\]

\(\square\)

## 原理 131.1（全局常数来自所有未激活通道）

即使某个具体整数只激活有限多个素数，概率归一化常数仍累积所有素数通道的零占据代价。

---

# 132. 同一素数上的截断精度熵

固定素数 \(p\)，令：

\[
V=V_p,
\qquad
q=p^{-s}.
\]

定义深度 \(k\) 的截断观察：

\[
T_k(V)
=
\min(V,k).
\]

其中 \(T_0\) 为常值，\(T_1\) 只判断是否被 \(p\) 整除，\(T_k\) 区分指数 \(0,\ldots,k-1\) 并把全部 \(\ge k\) 合并。

## 定理 132.1（几何无记忆余量）

条件于：

\[
V\ge k,
\]

随机变量：

\[
V-k
\]

仍服从与 \(V\) 相同的几何 law。

## 定理 132.2（截断熵闭式）

\[
\boxed{
H(T_k(V))
=
(1-q^k)H(V).
}
\]

## 定理 132.3（截断后的剩余熵）

\[
\boxed{
H(V\mid T_k(V))
=
q^kH(V).
}
\]

### 证明

只有事件 \(V\ge k\) 的合并纤维仍含不确定性，其概率为 \(q^k\)；在该纤维内，平移后的剩余分布与原几何分布相同。\(\square\)

## 定理 132.4（单层边际收益）

令二元熵：

\[
h_2(q)
=-q\log q-(1-q)\log(1-q).
\]

则：

\[
\boxed{
H(T_{k+1})-H(T_k)
=
q^kh_2(q).
}
\]

因为：

\[
h_2(q)=(1-q)H(V).
\]

## 核心解释

\[
\boxed{
\text{同一素数每增加一层指数精度，}
\text{其平均新增信息按 }p^{-s}\text{ 精确几何衰减。}
}
\]

---

# 133. 全局有限精度预算的精确残余熵

令精度预算：

\[
\kappa:\mathbb P\to\mathbb N_0
\]

只有有限多个 \(p\) 满足 \(\kappa(p)>0\)。定义联合截断画像：

\[
Q_\kappa(N)
=
\bigl(
\min(V_p(N),\kappa(p))
\bigr)_p.
\]

## 定理 133.1（观察信息可加）

\[
\boxed{
H(Q_\kappa(N))
=
\sum_p
\left(1-p^{-s\kappa(p)}\right)H_p(s).
}
\]

## 定理 133.2（身份残余熵）

\[
\boxed{
H(N\mid Q_\kappa(N))
=
\sum_p
p^{-s\kappa(p)}H_p(s).
}
\]

这里约定：

\[
\kappa(p)=0
\Rightarrow
p^{-s\kappa(p)}=1,
\]

即未观察素数保留全部局部熵。

## 推论 133.1（纵向精度是精确熵收缩）

将某个 \(p\) 的精度从 \(k\) 提升到 \(k+1\)，该素数通道的剩余熵从：

\[
q^kH_p
\]

变为：

\[
q^{k+1}H_p.
\]

收缩因子恰为：

\[
\boxed{q=p^{-s}.}
\]

这给出一个精确、非渐近的 prime-specific contraction law。

---

# 134. 最优精度分配是带前缀约束的边际选择

把从深度 \(j\) 提升到 \(j+1\) 视为一个单位成本 refinement cell：

\[
(p,j).
\]

其平均信息收益为：

\[
\boxed{
g_{p,j}
=
p^{-sj}h_2(p^{-s}).
}
\]

对固定 \(p\)：

\[
g_{p,0}>g_{p,1}>g_{p,2}>\cdots.
\]

## 定理 134.1（有限候选区中的贪心最优性）

在有限素数集合与有限最大深度中，若每个 refinement cell 成本均为一，并要求选择集合对每个素数前缀闭合，则任取收益最大的 \(B\) 个 cells 可调整为前缀闭合，且最大化总信息收益。

### 证明

若选择了 \((p,j)\) 却未选择某个 \((p,i)\) 且 \(i<j\)，则：

\[
g_{p,i}\ge g_{p,j}.
\]

以 \((p,i)\) 替换不会降低目标。重复交换得到前缀闭合的 top-\(B\) 集。总熵收益是 cells 收益的和，故最优。\(\square\)

## 推论 134.1（固定完整素数通道数时小素数优先）

若预算允许完整读取恰好 \(m\) 个素指数，且每个完整通道成本相同，则选择最小的前 \(m\) 个素数最大化期望观察信息，因为 \(H_p(s)\) 随 \(p\) 严格下降。

## 边界 134.1（任务目标可能改变排序）

该最优性针对身份 Shannon 信息。若目标只依赖某些大素数、分裂类或特殊同余，目标互信息排序可以完全不同。

---

# 135. radical 观察者与重数余量

定义素数支撑位：

\[
B_p
=
\mathbf1_{V_p>0}.
\]

全部 \((B_p)_p\) 恢复：

\[
\operatorname{rad}(N)
=
\prod_{p:B_p=1}p,
\]

但不恢复重数。

## 定理 135.1（支撑位是独立 Bernoulli）

\[
B_p\sim\operatorname{Bernoulli}(p^{-s}),
\]

且不同素数的 \(B_p\) 相互独立。

## 定理 135.2（支撑熵与完整指数熵）

\[
\boxed{
H(B_p)
=
(1-p^{-s})H_p(s).
}
\]

## 定理 135.3（重数余量）

\[
\boxed{
H(V_p\mid B_p)
=
p^{-s}H_p(s).
}
\]

### 证明

若 \(B_p=0\)，指数确定为零；若 \(B_p=1\)，则 \(V_p-1\) 仍服从原几何 law。\(\square\)

## 推论 135.1（全 radical 观察的剩余身份熵）

\[
\boxed{
H(N\mid\operatorname{rad}(N))
=
\sum_pp^{-s}H_p(s).
}
\]

所以“知道全部出现了哪些素数”仍留下一个可精确计算的重数余量。

---

# 136. zeta 参数之间的 KL 分解

取：

\[
s,t>1.
\]

## 定理 136.1（全局 KL 闭式）

\[
\boxed{
D(\mathbb P_s\Vert\mathbb P_t)
=
\log\zeta(t)-\log\zeta(s)
+
(t-s)\mathbb E_s[\log N].
}
\]

### 证明

\[
\log\frac{\mathbb P_s(n)}{\mathbb P_t(n)}
=
\log\frac{\zeta(t)}{\zeta(s)}
+
(t-s)\log n.
\]

对 \(\mathbb P_s\) 取期望。\(\square\)

## 定理 136.2（KL 的素数可加性）

\[
\boxed{
D(\mathbb P_s\Vert\mathbb P_t)
=
\sum_p
D(\gamma_{p,s}\Vert\gamma_{p,t}).
}
\]

局部项为：

\[
\boxed{
D(\gamma_{p,s}\Vert\gamma_{p,t})
=
\log
\frac{1-p^{-s}}{1-p^{-t}}
+
\frac{(t-s)\log p}{p^s-1}.
}
\]

## 原理 136.1（参数差异由独立素数证据累加）

在 zeta family 内，不同素数通道对区分参数 \(s,t\) 的对数证据严格相加；这不表示现实实验来源彼此独立。

---

# 137. Hellinger 亲和度与 Fisher 观察度量

## 定义 137.1（Hellinger／Bhattacharyya 亲和度）

\[
\mathcal A(s,t)
=
\sum_{n\ge1}
\sqrt{\mathbb P_s(n)\mathbb P_t(n)}.
\]

## 定理 137.1（全局亲和度闭式）

\[
\boxed{
\mathcal A(s,t)
=
\frac{
\zeta\left(\frac{s+t}{2}\right)
}{
\sqrt{\zeta(s)\zeta(t)}
}.
}
\]

## 定理 137.2（局部乘积分解）

\[
\boxed{
\mathcal A(s,t)
=
\prod_p
\frac{
\sqrt{(1-p^{-s})(1-p^{-t})}
}{
1-p^{-(s+t)/2}
}.
}
\]

## 定义 137.2（Fisher 信息）

\[
\mathcal I(s)
=
\mathbb E_s
\left[
\left(
\partial_s\log\mathbb P_s(N)
\right)^2
\right].
\]

## 定理 137.3（Fisher 信息的三种形式）

\[
\boxed{
\mathcal I(s)
=
\operatorname{Var}_s(\log N)
=
\frac{d^2}{ds^2}\log\zeta(s)
}
\]

并且：

\[
\boxed{
\mathcal I(s)
=
\sum_p
(\log p)^2
\frac{p^{-s}}{(1-p^{-s})^2}.
}
\]

## 推论 137.1（多样本信息加法）

对 \(m\) 个独立 zeta 样本：

\[
\mathcal I_m(s)=m\mathcal I(s).
\]

---

# 138. zeta family 的任务相对充分统计量

取独立样本：

\[
N_1,\ldots,N_m
\overset{\mathrm{iid}}{\sim}
\mathbb P_s.
\]

联合似然：

\[
\mathbb P_s(n_1,\ldots,n_m)
=
\zeta(s)^{-m}
\exp
\left(
-s\sum_{j=1}^m\log n_j
\right).
\]

## 定理 138.1（乘积统计量充分）

\[
\boxed{
T(n_1,\ldots,n_m)
=
\sum_{j=1}^m\log n_j
=
\log\prod_{j=1}^mn_j
}
\]

对参数 \(s\) 充分。

## 定理 138.2（最小充分关系）

两组样本 \(n=(n_j)\)、\(m=(m_j)\) 的似然比与 \(s\) 无关，当且仅当：

\[
\prod_jn_j
=
\prod_jm_j.
\]

因此样本乘积是该一参数 family 的最小充分统计量，等价于总对数能量。

## 定义 138.1（聚合素指数）

\[
C_p
=
\sum_{j=1}^mV_p(N_j).
\]

则：

\[
\prod_jN_j
=
\prod_pp^{C_p}.
\]

## 定理 138.3（聚合指数 law）

不同 \(p\) 的 \(C_p\) 相互独立，且：

\[
\boxed{
\mathbb P(C_p=c)
=
\binom{m+c-1}{c}
(1-p^{-s})^m
p^{-sc}.
}
\]

即每个 \(C_p\) 为负二项占据数。

## 核心解释

恢复全部样本身份需要每个样本的全部指数；估计共同参数 \(s\) 只需要聚合乘法能量。充分性严格依赖任务。

---

# Part XX：算术 Fock 观察、prime pinching 与量子语言饱和

# 139. 正整数 Hilbert 基与素数占据数

定义：

\[
\mathcal H_{\mathbb N}
=
\ell^2(\mathbb N_{>0}),
\]

正交基写作：

\[
|n\rangle.
\]

唯一分解画像给出 Hilbert 基等价：

\[
\boxed{
\ell^2(\mathbb N_{>0})
\simeq
\ell^2(\mathcal E_{\mathrm{fin}}).
}
\]

## 定义 139.1（素数数目算子）

对每个素数 \(p\)：

\[
\widehat N_p|n\rangle
=
v_p(n)|n\rangle.
\]

全部 \(\widehat N_p\) 在共同整数基上对角化并彼此交换。

## 定义 139.2（算术 Hamiltonian）

\[
\boxed{
\widehat H
=
\sum_p(\log p)\widehat N_p.
}
\]

在基向量上：

\[
\widehat H|n\rangle
=
\log n\,|n\rangle.
\]

## 定理 139.1（配分函数）

对 \(s>1\)：

\[
\boxed{
\operatorname{Tr}(e^{-s\widehat H})
=
\sum_{n\ge1}n^{-s}
=
\zeta(s).
}
\]

该“自由 Riemann gas／素数占据模态”解释在既有数学物理文献中已有先例；本文新增的是它与仓库观察纤维、prime-time completion 和语言饱和框架的明确接口，不主张首创配分函数解释。

---

# 140. zeta Gibbs 密度算子是素数模态乘积态

定义：

\[
\boxed{
\rho_s
=
\zeta(s)^{-1}e^{-s\widehat H}.
}
\]

于是：

\[
\rho_s
=
\sum_{n\ge1}
\frac{n^{-s}}{\zeta(s)}
|n\rangle\langle n|.
\]

## 定义 140.1（单素数热态）

在占据数空间 \(\ell^2(\mathbb N_0)\) 上：

\[
\boxed{
\rho_{p,s}
=
(1-p^{-s})
\sum_{k\ge0}
p^{-sk}|k\rangle\langle k|.
}
\]

## 纸面定理 140.1（restricted tensor product factorization）

在以全零占据为参考真空的适当 restricted tensor／Fock 实现中：

\[
\boxed{
\rho_s
\simeq
\bigotimes_p\rho_{p,s}.
}
\]

其对角联合 law 正是仓库已经机器检查的全部素指数独立性。

## 推论 140.1（模态热熵可加）

在第 130 节的收敛前件下：

\[
S(\rho_s)
=
\sum_pS(\rho_{p,s})
=
\sum_pH_p(s).
\]

## 边界 140.1

这只是一个对角、交换、无相互作用的数学模型；它不证明现实粒子是素数，也不把任意量子态分解成 prime product state。

---

# 141. 有限素数观察的量子 pinching

取有限素数集 \(S\)。对指数向量：

\[
a=(a_p)_{p\in S},
\]

定义投影：

\[
P_a^S
=
\sum_{n:\,(v_p(n))_{p\in S}=a}
|n\rangle\langle n|.
\]

这些投影完备且两两正交。

## 定义 141.1（有限素数 pinching）

\[
\boxed{
\mathcal E_S(\rho)
=
\sum_aP_a^S\rho P_a^S.
}
\]

## 定理 141.1（固定点刻画）

\[
\boxed{
\mathcal E_S(\rho)=\rho
\iff
P_a^S\rho P_b^S=0
\quad(a\ne b).
}
\]

即观察后稳定态恰为相对于已观察素数画像块对角的态。

## 定理 141.2（精化吸收律）

若：

\[
S\subseteq T,
\]

则：

\[
\boxed{
\mathcal E_T\mathcal E_S
=
\mathcal E_S\mathcal E_T
=
\mathcal E_T.
}
\]

更细 prime observation 吸收更粗 dephasing。

## 定理 141.3（zeta 热态已稳定）

\[
\boxed{
\mathcal E_S(\rho_s)=\rho_s
}
\]

对每个有限 \(S\) 成立，因为 \(\rho_s\) 已在完整整数／素指数基上对角。

## 原理 141.1（未观察纤维保存相干）

\(\mathcal E_S\) 只消除不同已观察指数向量之间的相干；同一 \(S\)-纤维内部的相干仍可存在。

---

# 142. 全部交换素数观察仍不完成量子层析

全部数目算子 \((\widehat N_p)_p\) 的联合本征值唯一标记每个整数基向量，因此它们对经典基标签完备。

但它们生成的观察代数仍是对角交换代数，而不是全部：

\[
B(\mathcal H_{\mathbb N}).
\]

## 定理 142.1（对角观察饱和）

设 \(\mathcal D\) 为由所有 \(\widehat N_p\) 的有界函数生成的对角代数，\(\mathcal E_{\mathcal D}\) 为完整对角 pinching。则对任意态 \(\rho\) 与任意 \(A\in\mathcal D\)：

\[
\boxed{
\operatorname{Tr}(\rho A)
=
\operatorname{Tr}(\mathcal E_{\mathcal D}(\rho)A).
}
\]

因此全部 prime-diagonal 统计都无法区分 \(\rho\) 与其去相干版本。

## 反模型 142.1（相位不可见）

定义：

\[
|\psi_+\rangle
=
\frac{|2\rangle+|3\rangle}{\sqrt2},
\qquad
|\psi_-\rangle
=
\frac{|2\rangle-|3\rangle}{\sqrt2}.
\]

则两个纯态在全部素指数联合测量下具有完全相同分布：

\[
\frac12\delta_{\nu(2)}
+
\frac12\delta_{\nu(3)}.
\]

但非对角 observable：

\[
X_{23}
=
|2\rangle\langle3|
+
|3\rangle\langle2|
\]

满足：

\[
\langle\psi_+|X_{23}|\psi_+\rangle=1,
\]

\[
\langle\psi_-|X_{23}|\psi_-\rangle=-1.
\]

## 推论 142.1（量子版同语言修复不可能）

\[
\boxed{
\text{加入任意多的 valuation、divisibility、radical、character}
\text{ 等对角 prime observables，}
\text{都不能恢复相对相位。}
}
\]

必须加入不属于同一交换观察代数的非对角接口。

## 原理 142.1（经典完备与量子完备分离）

\[
\boxed{
\text{联合本征值分离基状态}
\not\Rightarrow
\text{该交换代数对任意密度算子层析完备}.
}
\]

---

# 143. 观察代数精化与条件期望统一

有限素数集合 \(S\) 生成交换子代数：

\[
\mathcal D_S.
\]

若：

\[
S\subseteq T,
\]

则：

\[
\mathcal D_S
\subseteq
\mathcal D_T.
\]

对应 pinching：

\[
\mathcal E_S,
\qquad
\mathcal E_T
\]

是到这些可见代数的条件期望。

## 统一公式 143.1

经典平方风险中的：

\[
\mathbb E[T\mid\mathcal G_q]
\]

与量子态空间中的：

\[
\mathcal E_{\mathcal D}(\rho)
\]

具有相同结构角色：都把对象投影到观察者允许的可见子空间／子代数，并把正交余量留在不可见方向。

## 原理 143.1（条件期望不是信息创造）

无论经典或量子，条件期望都满足幂等性与可见量保持；它只能删除不可见成分，不能由同一观察代数内部重新生成被删除的余量。

---

# Part XXI：临界边界、统一定理与形式化路线

# 144. \(s=1\) 是全局可实现性的共同边界

对 \(s>0\)，以下条件等价：

\[
\boxed{
\begin{aligned}
1.&\quad s>1;\\
2.&\quad \zeta(s)<\infty;\\
3.&\quad \sum_pp^{-s}<\infty;\\
4.&\quad \prod_p(1-p^{-s})>0;\\
5.&\quad \Gamma_s(\mathcal E_{\mathrm{fin}})=1;\\
6.&\quad \mathbb E_{\Gamma_s}[\omega]<\infty;\\
7.&\quad \text{独立几何素指数可由正整数随机变量全局实现};\\
8.&\quad \sum_pH_p(s)<\infty;\\
9.&\quad \sum_p(\log p)^2\frac{p^{-s}}{(1-p^{-s})^2}<\infty.
\end{aligned}
}
\]

其中第 8、9 项由与 \(p^{-s}\)、\((\log p)^2p^{-s}\) 的比较得到。

## 推论 144.1（边界的四重含义）

\[
\boxed{
\begin{aligned}
s=1
&=\text{zeta 配分函数边界};\\
&=\text{素数激活概率可和边界};\\
&=\text{有限支撑全局整数画像的几乎处处胶合边界};\\
&=\text{素数信息与参数敏感度的发散边界}.
\end{aligned}
}
\]

## 原理 144.1（该边界不是 RH）

这里研究的是实参数 \(s>0\) 上的概率归一化与乘积画像可实现性。它不定位复零点，不提供解析延拓，不证明 Weil 正性，也不推出黎曼猜想。

---

# 145. 第三阶段统一定理

把本阶段的核心压缩如下。

## 定理 145.1（zeta 素数观察统一）

对 \(s>1\)，正整数 zeta Gibbs 模型同时满足：

1. 全部素指数观察者点态分离正整数；
2. 各素指数是相互独立的几何变量；
3. 独立局部乘积测度几乎处处落在有限支撑全局画像；
4. 其全局推前 law 唯一且为 \(n^{-s}/\zeta(s)\)；
5. 全局熵、KL、Fisher 信息和 Hellinger 亲和度均按素数模态分解；
6. 同一素数的精度残余熵每层按 \(p^{-s}\) 精确收缩；
7. zeta 密度算子在算术 Fock 基上是 prime-mode 对角乘积态；
8. 全部交换 prime observables 对经典整数身份完备，却对任意量子相位不完备。

## 定理 145.2（带类型的语言层级）

同一个“素数观察”词至少包含四种严格不同的语言：

\[
\boxed{
\begin{aligned}
\mathcal L_{\mathrm{split}}
&:\quad\text{以素数／判别式为状态的分裂与角色画像};\\
\mathcal L_{\mathrm{support}}
&:\quad\text{以正整数为状态的素因子出现画像};\\
\mathcal L_{\mathrm{valuation}}
&:\quad\text{以正整数为状态的完整素指数};\\
\mathcal L_{\mathrm{operator}}
&:\quad\text{以密度算子为状态的非交换 observable 语言}.
\end{aligned}
}
\]

这些语言一般位于不同状态类型上，因而不能无 transport 地写成一条全局偏序。本文已经得到的严格关系是：

\[
\boxed{
\mathcal L_{\mathrm{support}}
\prec_{\mathbb N_{>0}}
\mathcal L_{\mathrm{valuation}},
}
\]

因为相同 radical 可以具有不同重数；以及：

\[
\boxed{
\mathcal L_{\mathrm{prime\text{-}diagonal}}
\prec_{\operatorname{State}(\mathcal H)}
\mathcal L_{\mathrm{operator}},
}
\]

因为全部对角 prime observables 仍不能读取相对相位。分裂／角色语言则属于 prime-as-state 或 form-as-state 范畴，必须通过显式编码映射后才能与整数支撑语言比较。

## 原理 145.1（禁止跨类型伪排序）

\[
\boxed{
\text{只有在状态类型、目标与 transport 已固定后，}
\text{才能讨论两种观察语言谁更精细。}
}
\]

---

# 146. v1.2 建议新增模块

```text
D5/S3/PrimeObservers/
  Probability/
    ObservationSigma.lean
    ConditionalRisk.lean
    ProbabilisticGluing.lean
    SameLanguageRepetition.lean
    BlackwellRefinement.lean
  Zeta/
    GeometricPrimeProfile.lean
    FiniteSupportThreshold.lean
    ZetaGlobalRealizability.lean
    FinitePrimePosterior.lean
    PrimeSupportStatistics.lean
  Information/
    PrimeGeometricEntropy.lean
    ZetaEntropyPrimeSum.lean
    PrimeSurprisalCode.lean
    TruncatedExponentEntropy.lean
    PrecisionResidualContraction.lean
    OptimalPrecisionAllocation.lean
    RadicalMultiplicityResidual.lean
    ZetaKLPrimeSum.lean
    ZetaHellingerAffinity.lean
    ZetaFisherPrimeSum.lean
    ZetaSufficientStatistic.lean
  Quantum/
    ArithmeticFockBasis.lean
    PrimeNumberOperators.lean
    ZetaGibbsDensity.lean
    FinitePrimePinching.lean
    DiagonalSaturationCountermodel.lean
```

建议复用而不复制：

```text
D5/S3/Analytic/ZetaGibbs
D5/S3/Analytic/Zeta/PrimeExponentLaw
D5/S3/Analytic/Zeta/ZetaPrimeIndependence
D5/S3/Analytic/Zeta/ZetaEntropy
D5/S3/AnalyticClosure/PrimeSpectrumBoundaryDivergent
D5/S3/Quantum/Conditioning
D5/S3/ObserverMemory/Prediction/ItineraryCompletion
D5/S3/ConceptDynamics/TargetRisk
```

---

# 147. 第三阶段优先形式化链

## 147.1 有限几何分布链

优先闭合完全有限或单级数结论：

1. `geometric_entropy_closed_form`；
2. `truncated_geometric_entropy`；
3. `truncated_geometric_condEntropy`；
4. `precision_gain_eq`；
5. `radical_bit_entropy`；
6. `negative_binomial_prime_aggregate`。

这批不需要无限素数乘积。

## 147.2 有限素数联合链

1. 有限 \(S\) 的联合质量乘积；
2. 有限素数后验保持补坐标独立；
3. finite prime entropy sum；
4. finite KL／Hellinger factorization；
5. finite prime pinching 与吸收律。

## 147.3 可数乘积与阈值链

1. 构造 \(\Gamma_s\)；
2. 枚举素数并定义激活事件；
3. 第一 Borel–Cantelli 得到 \(s>1\) 的有限支撑；
4. `Nat.Primes.not_summable_one_div` 与第二 Borel–Cantelli得到 \(0<s\le1\) 的无限支撑；
5. 沿唯一分解画像推前并识别 zeta law；
6. 证明全局可实现的 iff 与唯一性。

Mathlib 已提供第一、第二 Borel–Cantelli 所需主定理；仓库已提供素数倒数边界发散。

## 147.4 无限信息与 Fock 链

在前述可积性闭合后：

1. `zeta_entropy_eq_prime_sum`；
2. `zeta_KL_eq_prime_sum`；
3. `zeta_fisher_eq_prime_sum`；
4. `arithmetic_fock_basis_equiv`；
5. `zeta_partition_trace`；
6. finite truncation 上的 `prime_diagonal_saturation`；
7. 再决定是否进入 restricted infinite tensor product。

---

# 148. v1.2 证明状态矩阵

| 结论 | 状态 | 主要锚点／外部基础 |
|---|---|---|
| 单素指数几何尾与点质量 | Lean anchor | `PrimeExponentLaw` |
| 全素指数相互独立 | Lean anchor | `ZetaPrimeIndependence` |
| zeta 熵有限与 Gibbs 恒等式 | Lean anchor | `ZetaEntropy` |
| 素数倒数边界发散 | Lean anchor | `PrimeSpectrumBoundaryDivergent` / Mathlib |
| 观察 \(\sigma\)-代数与条件风险 | Classical/Paper | conditional expectation |
| 精化平方风险勾股律 | Classical/Paper | Hilbert projection |
| 概率胶合质量 | Definition/Paper | standard Borel image |
| 同语言随机重复不跨 kernel | Paper | kernel factorization |
| product-geometric 测度 \(\Gamma_s\) | Classical/Paper | countable product measure |
| 有限支撑阈值 \(s=1\) | Paper | Borel–Cantelli + prime reciprocal divergence |
| 独立几何指数全局可实现 iff \(s>1\) | Paper | threshold + UFD |
| zeta law 的唯一性刻画 | Paper + anchors | independence + profile bijection |
| finite-prime posterior factorization | Paper + anchored independence | conditional product law |
| 单素数几何熵闭式 | Paper | geometric series |
| 全局熵素数求和 | Paper | `ZetaEntropy` + integrable projective limit |
| 截断指数熵／残余收缩 | Paper | geometric memorylessness |
| 最优 unit precision allocation | Paper finite optimization | decreasing marginal gains |
| radical 重数余量 | Paper | Bernoulli support + memorylessness |
| KL 素数分解 | Paper | product law |
| Hellinger 闭式 | Paper | direct zeta summation |
| Fisher 素数分解 | Paper | derivative/interchange audit |
| 多样本乘积最小充分 | Paper | factorization criterion |
| 算术 Fock 基等价 | Paper | UFD basis equivalence |
| zeta Gibbs restricted product state | Paper/Open Lean bridge | infinite tensor/Fock |
| finite prime pinching | Anchored specialization target | `Quantum/Conditioning` |
| prime-diagonal 相位盲区 | Paper finite countermodel | two-state calculation |

---

# 149. 第三阶段必要反模型与测试

## 149.1 相容边缘但无整数实现

取：

\[
s=1.
\]

每个有限素数集合上的独立几何分布合法，但 \(\Gamma_1\) 几乎必然有无穷支撑，故没有正整数来源。

## 149.2 同语言无限重复仍盲

取两个状态：

\[
x\neq y,
\qquad
q(x)=q(y),
\qquad
T(x)\neq T(y).
\]

让所有重复噪声样本只依赖 \(q\)。任意 transcript law 对 \(x,y\) 完全相同。

## 149.3 radical 不恢复重数

\[
\operatorname{rad}(12)
=
\operatorname{rad}(18)
=6,
\]

但：

\[
12\neq18.
\]

## 149.4 截断精度余量

对任意固定 \(k\)：

\[
V_p=p\text{-exponent }k
\]

与：

\[
V_p=k+1
\]

在 \(T_k\) 下相同但全指数不同。

## 149.5 全 prime-diagonal 量子盲区

使用：

\[
|\psi_+\rangle,
\qquad
|\psi_-\rangle
\]

验证全部对角 prime 统计相同而 \(X_{23}\) 期望相反。

## 149.6 有限数值检查

对截断素数集 \(p\le P\) 与指数深度 \(k\le K\)，检查：

- 几何质量归一化；
- joint mass product；
- 熵增量 \(q^kh_2(q)\)；
- residual \(q^kH_p\)；
- KL 与 Hellinger 局部／全局有限乘积一致；
- posterior complement law；
- finite pinching 的 trace-preserving 与 idempotent。

---

# 150. v1.2 新增严格非主张

本文进一步明确不声称：

1. 条件期望恢复真实微观状态；
2. 零条件风险等于点态无例外因子化；
3. Kolmogorov 扩张保证局部画像来自指定全局对象类型；
4. 任意 \(s>0\) 的独立几何素指数都能由正整数实现；
5. \(s=1\) 的全局不可实现性是复解析零点结论；
6. 素指数概率独立等于物理子系统独立；
7. prime-mode Fock 表示是本文首创；
8. zeta 配分函数模型证明现实存在“素数粒子”；
9. 对角 zeta Gibbs 态代表所有量子态；
10. 全部素指数观察完成任意量子态层析；
11. diagonal prime observables 能读取相对相位；
12. Fisher 信息发散本身证明相变、意识或宇宙临界性；
13. 小素数在所有目标与所有成本模型下总是最优；
14. Shannon 熵最优等于算法时间最优；
15. Blackwell 精化允许从粗通道反演任意细状态；
16. 本阶段纸面无限乘积、Borel–Cantelli、Fock 与算子结论已经通过 Lean kernel；
17. 概率意义上的几乎处处胶合等于点态全胶合；
18. 本阶段对 zeta law 的概率刻画构成 RH 的证明。

---

# 151. 第三阶段最终命题

素数观察者理论现在具有三种相互嵌套但不可混同的完成：

\[
\boxed{
\begin{aligned}
\text{确定性完成}
&:\quad
\text{全部局部坐标是否点态分离全局对象};\\
\text{概率完成}
&:\quad
\text{局部乘积 law 是否几乎处处集中于全局画像};\\
\text{算子完成}
&:\quad
\text{观察代数是否足以区分一般量子态与相干余量}.
\end{aligned}
}
\]

在 zeta 素指数模型中：

\[
\boxed{
\begin{aligned}
\text{UFD}
&\Rightarrow
\text{确定性指数画像完备};\\
s>1
&\Rightarrow
\text{独立几何画像几乎处处可胶合};\\
\text{全部交换 }\widehat N_p
&\not\Rightarrow
\text{量子层析完备}.
\end{aligned}
}
\]

最深的新结论是：

\[
\boxed{
\text{全局对象的存在不仅要求局部接口相容，}
\text{还要求局部概率质量集中在可实现画像；}
\text{而即使经典画像已经完备，}
\text{交换观察语言仍可能留下不可见相位。}
}
\]

因此完整的素数观察链应写为：

\[
\boxed{
\text{prime coordinates}
\to
\text{product law}
\to
\text{realizability mass}
\to
\text{conditional completion}
\to
\text{operator algebra}
\to
\text{noncommutative completion}.
}
\]

---

# Appendix H：v1.2 版本记录、仓库锚点与外部基础

## H.1 版本记录

- **v1.2 — 2026-08-21**：追加观察 \(\sigma\)-代数、条件期望软完成、概率胶合质量、Blackwell 精化与同语言重复极限；建立独立几何素指数的全局可实现 iff \(s>1\)、zeta law 唯一性、有限素数后验、支撑计数、素数熵／surprisal／KL／Hellinger／Fisher 分解、截断指数精度熵和精确 residual contraction、最优 unit refinement allocation、radical 重数余量、多样本乘积充分统计量、算术 Fock 基、zeta Gibbs 对角乘积态、finite prime pinching 及交换 prime 观察的量子相位盲区。

## H.2 本阶段仓库真值锚点

1. `D5/S3/Analytic/ZetaGibbs.lean`。
2. `D5/S3/Analytic/Zeta/PrimeExponentLaw.lean`。
3. `D5/S3/Analytic/Zeta/ZetaPrimeIndependence.lean`。
4. `D5/S3/Analytic/Zeta/ZetaEntropy.lean`。
5. `D5/S3/AnalyticClosure/PrimeSpectrumBoundaryDivergent.lean`。
6. `D5/S3/Quantum/Conditioning.lean` 及相关正交投影／pinching 文件。
7. `D5/S3/ObserverMemory/Prediction/ItineraryCompletion.lean`。
8. `D5/S3/ConceptDynamics/TargetRisk/RefinementRiskCostTradeoff.lean`。

## H.3 外部经典基础

以下文献只支撑尚未在本仓库闭合的标准数学背景，不替代未来 Lean proof term：

1. D. Blackwell, “Equivalent Comparisons of Experiments,” *Annals of Mathematical Statistics* 24 (1953), 265–272, DOI `10.1214/aoms/1177729032`。
2. S. Kullback and R. A. Leibler, “On Information and Sufficiency,” *Annals of Mathematical Statistics* 22 (1951), 79–86, DOI `10.1214/aoms/1177729694`。
3. Mathlib, `Mathlib/Probability/BorelCantelli.lean`：第一／第二 Borel–Cantelli 接口。
4. Mathlib, `Mathlib/NumberTheory/SumPrimeReciprocals.lean`：素数倒数级数发散。
5. O. Kallenberg, *Foundations of Modern Probability*, 3rd ed.：可数乘积测度、条件期望与零一律背景。
6. T. Cover and J. Thomas, *Elements of Information Theory*, 2nd ed.：熵、KL、充分性与数据处理背景。
7. B. L. Julia, “Statistical Theory of Numbers,” in *Number Theory and Physics*, Springer Proceedings in Physics 47 (1990), 276–293：Riemann gas／zeta 配分函数解释。
8. J.-B. Bost and A. Connes, “Hecke Algebras, Type III Factors and Phase Transitions with Spontaneous Symmetry Breaking in Number Theory,” *Selecta Mathematica* 1 (1995), 411–457, DOI `10.1007/BF01589495`。
---

# Part XXII：追加式第四阶段——可观察代数、有限商完成与 prime-primary 边界

> **追加说明。** 以下各节构成 v1.3 的追加式第四阶段。它们不改写 v1.0 的局部读出内核、v1.1 的观察语言饱和结论或 v1.2 的概率完成层，而是进一步回答：一个观察语言究竟生成了哪些可判定事件；全部有限商观察与全部素数幂商观察之间差多少；为何 CRT 的 prime-primary 分解不能无条件推广到任意代数系统；以及怎样定量比较“能否区分”“多大比例的素数能区分”“抗多少错误”和“需要等多久”。

# 152. 可观察事件代数

固定状态类型 \(X\) 与读出：

\[
q:X\to O.
\]

令有效像为：

\[
O_{\mathrm{eff}}=\operatorname{Im}(q).
\]

## 定义 152.1（\(q\)-可观察事件）

事件 \(A\subseteq X\) 称为 \(q\)-可观察，当存在：

\[
B\subseteq O_{\mathrm{eff}}
\]

使：

\[
A=q^{-1}(B).
\]

等价地，\(A\) 在每个 \(q\)-纤维上为常值：

\[
q(x)=q(y)
\Longrightarrow
\bigl(x\in A\iff y\in A\bigr).
\]

记全部可观察事件为：

\[
\operatorname{ObsAlg}(q)
=
\{A\subseteq X:A\text{ 为 }q\text{-可观察}\}.
\]

## 定理 152.1（可观察事件代数表示）

存在规范 Boolean 代数同构：

\[
\boxed{
\operatorname{ObsAlg}(q)
\cong
\mathcal P(O_{\mathrm{eff}}).
}
\]

### 证明

正向把 \(B\subseteq O_{\mathrm{eff}}\) 送到 \(q^{-1}(B)\)。反向把饱和事件 \(A\) 送到：

\[
\{o\in O_{\mathrm{eff}}:\exists x,\ q(x)=o\land x\in A\}.
\]

由于 \(A\) 在纤维上为常值，反向定义与代表选择无关。逆像保持并、交与补，二者互逆。\(\square\)

## 推论 152.1（有限情形的原子）

若 \(X\) 有限，则 \(\operatorname{ObsAlg}(q)\) 的非零原子恰是 \(q\) 的非空纤维：

\[
q^{-1}(o),
\qquad
o\in O_{\mathrm{eff}}.
\]

因此一个有限观察语言的逻辑原子不是单个全局状态，而是该语言仍无法分开的最小状态块。

---

# 153. 精化等价于可观察代数包含

给定两个读出：

\[
q:X\to O,
\qquad
r:X\to P.
\]

## 定理 153.1（精化—事件代数对偶）

在有效像上，以下等价：

\[
q\preceq r,
\]

\[
\ker(r)\subseteq\ker(q),
\]

以及：

\[
\boxed{
\operatorname{ObsAlg}(q)
\subseteq
\operatorname{ObsAlg}(r).
}
\]

### 证明

若 \(q=h\circ r\)，则任一 \(q\)-可观察事件都是 \(r\)-可观察事件。

反之，假设全部 \(q\)-可观察事件均为 \(r\)-可观察。若 \(r(x)=r(y)\) 但 \(q(x)\neq q(y)\)，取事件：

\[
A=q^{-1}(\{q(x)\}).
\]

它是 \(q\)-可观察，因而是 \(r\)-可观察；但 \(x\in A\)、\(y\notin A\)，与二者属于同一 \(r\)-纤维矛盾。故 \(\ker(r)\subseteq\ker(q)\)，从而在有效像上存在因子映射。\(\square\)

## 原理 153.1（信息增长就是事件代数增长）

概念精化不仅增加输出标签，还严格扩大主体可判定事件的 Boolean 代数：

\[
q\preceq r
\Longrightarrow
\operatorname{ObsAlg}(q)
\subseteq
\operatorname{ObsAlg}(r).
\]

若加入一个新接口后事件代数不变，则它没有增加语义区分能力；它最多增加计算便利、冗余校验或来源审计。

---

# 154. 目标族的最小充分商

设目标索引类型为 \(T\)，每个目标为：

\[
K_t:X\to Y_t.
\]

## 定义 154.1（目标族等价）

\[
x\sim_{\mathcal K}y
\iff
\forall t:T,
K_t(x)=K_t(y).
\]

## 定义 154.2（联合目标读出）

\[
K_{\mathrm{all}}(x)
=
(K_t(x))_{t:T}.
\]

## 定理 154.1（最小充分目标状态）

商：

\[
Z_{\mathcal K}=X/{\sim_{\mathcal K}}
\]

是同时决定全部目标 \(K_t\) 的最粗概念。

更精确地，若读出 \(q:X\to O\) 对全部目标充分，即：

\[
\forall t,\exists\bar K_t,
\qquad
K_t=\bar K_t\circ q,
\]

则：

\[
\ker(q)
\subseteq
\sim_{\mathcal K},
\]

因而 \(q\) 精化目标商投影：

\[
X\to Z_{\mathcal K}.
\]

### 证明

若 \(q(x)=q(y)\)，每个 \(K_t\) 都由 \(q\) 计算，所以 \(K_t(x)=K_t(y)\)。故 \(x\sim_{\mathcal K}y\)。联合目标读出自身显然决定每个分量，因此其 kernel quotient 满足普适最小性。\(\square\)

## 推论 154.1（任务身份与本体身份分离）

对任务族 \(\mathcal K\)，操作上必要的身份是：

\[
[x]_{\mathcal K},

\]

而不是完整微观状态 \(x\)。只有当目标族联合忠实时：

\[
\sim_{\mathcal K}=\operatorname{Eq}_X,
\]

任务身份才等于全局身份。

---

# 155. 有限商观察者与有限剩余

令 \(G\) 为群。对每个有限指数正规子群：

\[
N\trianglelefteq G,
\qquad
[G:N]<\infty,
\]

定义有限商观察者：

\[
q_N:G\to G/N.
\]

## 定义 155.1（有限剩余）

\[
\boxed{
R_{\mathrm{fin}}(G)
=
\bigcap_{
N\trianglelefteq G,
[G:N]<\infty
}N.
}
\]

## 定理 155.1（全部有限商观察的 kernel）

全部有限商联合读出的 kernel 恰为：

\[
R_{\mathrm{fin}}(G).
\]

因此：

\[
\boxed{
G\text{ residually finite}
\iff
R_{\mathrm{fin}}(G)=\{1\}
\iff
\text{全部有限商观察联合忠实}.
}
\]

## 定义 155.2（profinite 观察完成）

\[
\widehat G
=
\varprojlim_{N}G/N.
\]

存在规范映射：

\[
\iota_G:G\to\widehat G,
\]

且：

\[
\ker(\iota_G)=R_{\mathrm{fin}}(G).
\]

## 原理 155.1（profinite 完成的观察含义）

\(\widehat G\) 不是在 \(G\) 外随意添加的“隐藏世界”，而是所有有限商读出之间的相容联合状态空间。它记住全部有限观察能够记住的内容，并精确忘掉有限剩余。

---

# 156. 单素数语言与 pro-\(p\) 完成

固定素数 \(p\)。考虑全部满足：

\[
[G:N]=p^k
\]

的正规子群 \(N\)。

## 定义 156.1（\(p\)-剩余）

\[
R_p(G)
=
\bigcap_{
N\trianglelefteq G,
[G:N]=p^k
}N.
\]

## 定义 156.2（pro-\(p\) 观察完成）

\[
\widehat G_p
=
\varprojlim_{[G:N]=p^k}G/N.
\]

规范映射：

\[
\iota_{G,p}:G\to\widehat G_p
\]

满足：

\[
\ker(\iota_{G,p})=R_p(G).
\]

## 定义 156.3（全 prime-primary 观察）

\[
\iota_{G,\mathrm{pp}}:
G\to
\prod_p\widehat G_p.
\]

其 kernel 为：

\[
\boxed{
R_{\mathrm{pp}}(G)
=
\bigcap_pR_p(G).
}
\]

## 原理 156.1（全部 pro-\(p\) 不等于 profinite）

一般只有：

\[
R_{\mathrm{fin}}(G)
\subseteq
R_{\mathrm{pp}}(G).
\]

因为 \(p\)-群商只是全部有限商中的一部分。等号需要额外结构，不能由“每个有限群的阶分解为素数幂”偷渡得到。

---

# 157. 有限群的 prime-power 完备性恰好刻画幂零性

设 \(G\) 为有限群。

## 定理 157.1（有限 prime-power 观察完备判据）

以下等价：

1. 全部有限 \(p\)-群商观察联合忠实；
2. \(R_{\mathrm{pp}}(G)=\{1\}\)；
3. \(G\) 能嵌入某个有限 \(p\)-群直积；
4. \(G\) 是有限幂零群；
5. \(G\) 是其 Sylow 子群的直积。

即：

\[
\boxed{
\text{有限群可由 prime-power 商完全重建}
\iff
G\text{ 幂零}.
}
\]

### 证明

若全部 \(p\)-群商联合忠实，由于 \(G\) 有限，可从所有区分状态对的商中抽取有限子族，得到嵌入：

\[
G\hookrightarrow
P_{p_1}\times\cdots\times P_{p_r},
\]

其中每个 \(P_{p_i}\) 为有限 \(p_i\)-群。有限 \(p\)-群幂零，有限直积幂零，有限幂零群的子群仍幂零，故 \(G\) 幂零。

反之，若 \(G\) 有限幂零，则：

\[
G\cong\prod_{p\mid|G|}S_p,
\]

其中 \(S_p\) 为正规 Sylow \(p\)-子群。各坐标投影：

\[
G\to S_p
\]

都是 \(p\)-群商，联合投影为同构，故 prime-power 观察忠实。其余等价是有限幂零群的标准刻画。\(\square\)

## 推论 157.1（CRT 是幂零／阿贝尔结构的特殊胜利）

\[
(\mathbb Z/n\mathbb Z,+)
\]

是有限 Abelian 群，因而幂零，并分解为 Sylow 素数幂因子。这解释了 CRT 为何在整数模环的加法地址上完全成立；它不能被无条件提升为任意非交换对象的 prime-primary 分解原理。

---

# 158. 完全盲反模型：\(A_5\) 的所有 prime-power 商均平凡

取交错群：

\[
G=A_5,
\qquad
|G|=60.
\]

## 定理 158.1（\(A_5\) 的 \(p\)-群商盲性）

对任意素数 \(p\) 和任意群同态：

\[
\varphi:A_5\to P,
\]

若 \(P\) 是有限 \(p\)-群，则：

\[
\varphi\text{ 为平凡同态}.
\]

### 证明

\(A_5\) 是非 Abelian 单群，所以 \(\ker\varphi\) 只能是 \(\{1\}\) 或 \(A_5\)。若 kernel 为 \(\{1\}\)，则 \(A_5\) 嵌入 \(P\)，从而 \(|A_5|=60\) 必整除 \(|P|=p^k\)，不可能。故 kernel 为全部 \(A_5\)。\(\square\)

## 推论 158.1（prime-power 完成可完全删除非幂零身份）

\[
R_p(A_5)=A_5
\]

对每个 \(p\) 成立，因此：

\[
R_{\mathrm{pp}}(A_5)=A_5.
\]

全部 pro-\(p\) 观察把 \(A_5\) 压成单点；但完整有限商语言包含恒等商：

\[
A_5\to A_5,
\]

所以：

\[
R_{\mathrm{fin}}(A_5)=\{1\}.
\]

这给出严格分离：

\[
\boxed{
\text{all prime-power observations}
\ll
\text{all finite-quotient observations}.
}
\]

---

# 159. 有限商语言的残余层级

定义三类有限目标群：

\[
\mathcal F_{\mathrm{all}},
\qquad
\mathcal F_{\mathrm{sol}},
\qquad
\mathcal F_{\mathrm{nil}},
\]

分别为全部有限群、有限可解群和有限幂零群。

对任意群 \(G\)，定义：

\[
R_{\mathcal C}(G)
=
\bigcap_{
\varphi:G\to H,
H\in\mathcal C
}
\ker\varphi.
\]

## 定理 159.1（观察语言包含与 residual 反序）

因为：

\[
\mathcal F_{\mathrm{nil}}
\subseteq
\mathcal F_{\mathrm{sol}}
\subseteq
\mathcal F_{\mathrm{all}},
\]

所以：

\[
\boxed{
R_{\mathrm{fin}}(G)
\subseteq
R_{\mathrm{sol}}(G)
\subseteq
R_{\mathrm{nil}}(G).
}
\]

## 定理 159.2（幂零 residual 等于全 prime-power residual）

\[
\boxed{
R_{\mathrm{nil}}(G)
=
\bigcap_pR_p(G).
}
\]

### 证明

任意 \(p\)-群都是幂零群，所以右侧至少包含幂零 residual 的信息。反之，若某元素在一个有限幂零商 \(H\) 中非平凡，将 \(H\) 分解为 Sylow 直积；该元素至少有一个非平凡 \(p\)-分量，投影到相应 Sylow \(p\)-群即可用一个 \(p\)-群商区分它。\(\square\)

## 原理 159.1（观察语言类型决定可见结构层）

不同目标范畴产生不同“完成”：

\[
\boxed{
\begin{aligned}
\text{有限群商}
&\Rightarrow
\text{profinite 可见性};\\
\text{有限可解群商}
&\Rightarrow
\text{prosolvable 可见性};\\
\text{有限幂零／}p\text{-群商}
&\Rightarrow
\text{pronilpotent 可见性};\\
\text{有限 Abelian 商}
&\Rightarrow
\text{pro-Abelian 可见性}.
\end{aligned}
}
\]

不能把其中任何一层称为“全部有限信息”，除非已经证明目标对象在该商语言中 residual。

---

# Part XXIII：分离谱、见证密度与随机素数观察能力

# 160. 一对状态的素数分离谱

给定素数索引读出：

\[
q_p:X\to O_p.
\]

## 定义 160.1（分离谱）

对 \(x,y\in X\)：

\[
\operatorname{Sep}_q(x,y)
=
\{p\in\mathbb P:q_p(x)\neq q_p(y)\}.
\]

## 定义 160.2（盲素数集）

\[
\operatorname{Blind}_q(x,y)
=
\{p\in\mathbb P:q_p(x)=q_p(y)\}.
\]

于是：

\[
\mathbb P
=
\operatorname{Sep}_q(x,y)
\sqcup
\operatorname{Blind}_q(x,y).
\]

## 定义 160.3（四级分离强度）

对不同状态 \(x\neq y\)，依次区分：

1. **存在分离**：\(\operatorname{Sep}_q(x,y)\neq\varnothing\)；
2. **无限分离**：\(\operatorname{Sep}_q(x,y)\) 无限；
3. **余有限分离**：\(\operatorname{Blind}_q(x,y)\) 有限；
4. **密度分离**：分离素数具有指定自然或 Dirichlet 密度。

联合忠实只要求第一级；随机实验效率与鲁棒性需要更强的后三层。

## 定义 160.4（最坏分离密度）

若每对状态的分离素数 Dirichlet 密度存在，定义：

\[
\delta_{\min}(q)
=
\inf_{x\neq y}
\delta\bigl(\operatorname{Sep}_q(x,y)\bigr).
\]

\(\delta_{\min}>0\) 表示任意两种全局状态都被正比例的素数实验区分；单射本身不提供这一保证。

---

# 161. 整数剩余观察几乎处处分离

取：

\[
X=\mathbb Z,
\qquad
q_p(n)=n\bmod p.
\]

## 定理 161.1（整数对的盲素数精确分类）

对 \(x\neq y\)，令：

\[
d=x-y\neq0.
\]

则：

\[
\boxed{
q_p(x)=q_p(y)
\iff
p\mid d.
}
\]

所以：

\[
\operatorname{Blind}_q(x,y)
=
\{p:p\mid d\}.
\]

是有限集，而：

\[
\operatorname{Sep}_q(x,y)
\]

为余有限集，具有自然密度与 Dirichlet 密度一。

## 推论 161.1（盲素数数量上界）

若 \(\omega(d)\) 是 \(|d|\) 的不同素因子数，则：

\[
2^{\omega(d)}
\le
\prod_{p\mid d}p
\le
|d|.
\]

因此：

\[
\boxed{
\omega(d)
\le
\lfloor\log_2|d|\rfloor.
}
\]

## 定义 161.1（水平见证素数复杂度）

按递增顺序记素数：

\[
p_1=2,p_2=3,p_3=5,\ldots
\]

定义：

\[
h(x,y)
=
\min\{j:p_j\nmid(x-y)\}.
\]

## 定理 161.2（primorial 见证界）

令：

\[
P_r=\prod_{j=1}^{r}p_j.
\]

若：

\[
P_r>|x-y|,
\]

则：

\[
\boxed{h(x,y)\le r.}
\]

### 证明

若前 \(r\) 个素数全部不能区分 \(x,y\)，则每个 \(p_j\mid(x-y)\)。它们两两互素，故：

\[
P_r\mid(x-y),
\]

从而 \(P_r\le|x-y|\)，矛盾。\(\square\)

## 推论 161.2（有界整数的水平单精度层析）

若：

\[
P_r\ge N,
\]

则读出：

\[
q(n)
=
(n\bmod p_1,\ldots,n\bmod p_r)
\]

在：

\[
\{0,\ldots,N-1\}
\]

上单射。

---

# 162. 同一素数的盲精度由赋值完全控制

固定 \(p\)。定义：

\[
q_{p,k}(n)=n\bmod p^k.
\]

## 定理 162.1（精度盲区）

对 \(x\neq y\)：

\[
q_{p,k}(x)=q_{p,k}(y)
\iff
k\le v_p(x-y).
\]

因此第一个区分精度为：

\[
\boxed{
\kappa_p(x,y)=v_p(x-y)+1.
}
\]

## 原理 162.1（水平与纵向证书）

整数差异可以通过两种正交方式显现：

\[
\boxed{
\begin{aligned}
\text{横向}
&:\quad
\text{寻找不整除差值的新素数};\\
\text{纵向}
&:\quad
\text{超过该差值的 }p\text{-进赋值深度}.
\end{aligned}
}
\]

前者产生多个 CRT 独立坐标，适合冗余编码；后者是单一嵌套塔，适合增量加精但不自动产生独立抗错坐标。

---

# 163. 代数整数的约化观察也几乎处处分离

设 \(K\) 为数域，整数环为 \(\mathcal O_K\)。对非零素理想 \(\mathfrak p\)，定义：

\[
q_{\mathfrak p}(\alpha)
=
\alpha\bmod\mathfrak p.
\]

## 定理 163.1（代数整数的有限盲素理想定理）

若：

\[
\alpha,\beta\in\mathcal O_K,
\qquad
\alpha\neq\beta,
\]

则：

\[
q_{\mathfrak p}(\alpha)
=
q_{\mathfrak p}(\beta)
\iff
\mathfrak p\mid(\alpha-\beta).
\]

非零主理想：

\[
(\alpha-\beta)
\]

只有有限多个素理想因子。因此除有限多个 \(\mathfrak p\) 外，约化观察都能区分 \(\alpha,\beta\)。

## 推论 163.1（元素观察与性质观察的分叉）

底层元素约化可以在几乎所有素理想处分离不同元素；但从约化结果再压缩出的粗性质——例如 split/inert、局部主性、迹、特征多项式——仍可能对全部素数都合并不同全局对象。

所以：

\[
\boxed{
\text{素数数量很多}
\not\Rightarrow
\text{所选局部性质足够精细}.
}
\]

---

# 164. 二次角色之间的分离密度为二分之一

设：

\[
\chi_1,\chi_2
\]

为两个不同的二次 Dirichlet 角色。忽略有限多个分歧素数，定义分裂输出：

\[
q_p(\chi)=\chi(p)\in\{\pm1\}.
\]

## 经典定理 164.1（二次角色分离密度）

若 \(\chi_1\neq\chi_2\)，则：

\[
\chi=\chi_1\chi_2
\]

是非平凡二次角色，并且：

\[
\chi_1(p)\neq\chi_2(p)
\iff
\chi(p)=-1.
\]

由二次扩张的 Chebotarev 密度定理：

\[
\boxed{
\delta
\{p:\chi_1(p)\neq\chi_2(p)\}
=
\frac12.
}
\]

## 原理 164.1（忠实性之外的实验频率）

两个不同二次结构不仅可由某个素数区分，而且随机选择一个未分歧大素数时，渐近约有一半机会立即区分。该频率信息不包含在 kernel 单射性中。

---

# 165. Chebotarev 把 Galois 观察频率变成群计数

设：

\[
L/K
\]

为有限 Galois 扩张，群为：

\[
G=\operatorname{Gal}(L/K).
\]

令：

\[
f,g:G\to S
\]

为共轭不变函数。对未分歧素理想 \(\mathfrak p\)，读取：

\[
f(\operatorname{Frob}_{\mathfrak p}),
\qquad
g(\operatorname{Frob}_{\mathfrak p}).
\]

## 经典定理 165.1（Galois 分离密度公式）

令：

\[
U_{f,g}
=
\{\sigma\in G:f(\sigma)\neq g(\sigma)\}.
\]

由于 \(f,g\) 共轭不变，\(U_{f,g}\) 是共轭类之并。Chebotarev 密度定理给出：

\[
\boxed{
\delta
\{\mathfrak p:
f(\operatorname{Frob}_{\mathfrak p})
\neq
g(\operatorname{Frob}_{\mathfrak p})\}
=
\frac{|U_{f,g}|}{|G|}.
}
\]

## 推论 165.1（局部实验价值可由有限群预计算）

在有限 Galois 模型中，随机素理想区分两个共轭不变目标的渐近成功率，可以先在有限群 \(G\) 上通过计数计算，再由 Chebotarev 转移到素理想频率。

---

# 166. 素数观察器的多轴能力向量

单一“信息量”不能完整排序观察系统。定义能力向量：

\[
\boxed{
\mathcal A(q)
=
\bigl(
\operatorname{Ker}(q),
\delta_{\min}(q),
\operatorname{Cost}(q),
\operatorname{Dist}(q),
\operatorname{Depth}(q),
\operatorname{Defect}(q)
\bigr).
}
\]

其中分别表示：

1. **语义 kernel**：哪些状态仍被合并；
2. **最坏分离密度**：随机素数实验多常见地给出见证；
3. **观察成本**：读取、存储、验证与胶合代价；
4. **编码距离**：能检测或纠正多少错误；
5. **动态完成深度**：需要观察多久；
6. **自然性缺陷**：局部读出是否尊重过程。

## 原理 166.1（不可用单标量支配）

两个系统可能：

- kernel 相同但一个具有更高错误距离；
- 都忠实但一个分离密度极低；
- 静态成本较高却动态完成更浅；
- 信息更多但自然性缺陷更大。

所以传感器设计应寻找 Pareto 前沿，而不是把所有能力压成一个未经证明的总分。

---

# Part XXIV：CRT 观察码的精确距离、纠错与容量边界

# 167. 有界整数的 CRT 观察码

取两两互素且大于一的模数：

\[
2\le m_1<m_2<\cdots<m_n.
\]

令总 CRT 模数为：

\[
M=\prod_{i=1}^{n}m_i,
\]

并固定非平凡且可唯一编码的动态范围：

\[
2\le K\le M.
\]

定义：

\[
X_K=\{0,1,\ldots,K-1\}.
\]

定义编码：

\[
C_K(x)
=
(x\bmod m_1,\ldots,x\bmod m_n).
\]

在输出积上使用 Hamming 距离：

\[
d_H(a,b)
=
|\{i:a_i\neq b_i\}|.
\]

## 定义 167.1（最大可同时盲坐标数）

对 \(A\subseteq\{1,\ldots,n\}\)，记：

\[
M_A=\prod_{i\in A}m_i.
\]

定义：

\[
\boxed{
t(K)
=
\max
\{|A|:M_A<K\}.
}
\]

空集积取一。

---

# 168. CRT 观察码的精确最小距离

## 定理 168.1（精确距离公式）

\[
\boxed{
d_{\min}(C_K)=n-t(K).}
\]

### 证明

对 \(x\neq y\)，令一致坐标集：

\[
A(x,y)
=
\{i:x\equiv y\pmod{m_i}\}.
\]

因为模数两两互素：

\[
M_{A(x,y)}
\mid(x-y).
\]

又因：

\[
0<|x-y|<K,
\]

故：

\[
M_{A(x,y)}<K,
\]

所以一致坐标数至多为 \(t(K)\)，Hamming 距离至少为 \(n-t(K)\)。

反之，取达到 \(t(K)\) 的集合 \(A\)，令：

\[
x=0,
\qquad
y=M_A<K.
\]

对 \(i\in A\)，两者模 \(m_i\) 相同；对 \(j\notin A\)，由于 \(m_j\) 与 \(M_A\) 互素且 \(m_j>1\)，有 \(m_j\nmid M_A\)，故对应坐标不同。于是距离恰为 \(n-|A|=n-t(K)\)。\(\square\)

## 推论 168.1（排序后的闭式）

由于固定大小子集的最小乘积由最小模数组成：

\[
\boxed{
t(K)
=
\max
\left\{
r:
\prod_{i=1}^{r}m_i<K
\right\}.
}
\]

## 推论 168.2（满 CRT 动态范围无纠错余量）

若：

\[
K=\prod_{i=1}^{n}m_i,
\]

则：

\[
t(K)=n-1,
\qquad
d_{\min}=1.
\]

完整使用 CRT 容量只保证唯一编码，不提供任何坐标错误检测能力。

---

# 169. 错误检测、唯一纠正与擦除

设最小距离为：

\[
d=d_{\min}(C_K).
\]

## 定理 169.1（错误检测）

任意少于 \(d\) 个坐标的篡改不能把一个合法码字变成另一个合法码字。因此最多：

\[
d-1
\]

个任意坐标错误可被保证检测。

## 定理 169.2（唯一纠错半径）

若接收词与真实码字的 Hamming 距离至多：

\[
e
\]

且：

\[
2e<d,
\]

则真实码字是唯一距离不超过 \(e\) 的合法码字。因此可保证纠正：

\[
\boxed{
\left\lfloor\frac{d-1}{2}\right\rfloor
}
\]

个任意错误坐标。

## 定理 169.3（错误与擦除联合条件）

若有 \(e\) 个未知错误和 \(s\) 个已知擦除坐标，只要：

\[
\boxed{2e+s<d,}
\]

则合法消息仍唯一。

### 证明

若两个候选码字都与接收结果相容，则在未擦除坐标上它们至多相差 \(2e\) 个位置，加上擦除位置总差异至多 \(2e+s<d\)，与最小距离矛盾。\(\square\)

---

# 170. 动态范围—距离的精确 Pareto 阶梯

## 定理 170.1（给定目标距离的最大动态范围）

要保证：

\[
d_{\min}(C_K)\ge d,
\qquad
1\le d\le n,
\]

当且仅当：

\[
\boxed{
K
\le
\prod_{i=1}^{n-d+1}m_i.
}
\]

### 证明

\(d_{\min}\ge d\) 等价于：

\[
t(K)\le n-d.
\]

这又等价于任一大小为 \(n-d+1\) 的模数子集乘积都不小于 \(K\)。最小的此类乘积是前 \(n-d+1\) 个最小模数之积。\(\square\)

## 推论 170.1（纠正 \(e\) 个错误的容量上限）

若要保证纠正 \(e\) 个任意错误坐标，需要：

\[
d_{\min}\ge2e+1,
\]

因此：

\[
\boxed{
K
\le
\prod_{i=1}^{n-2e}m_i.
}
\]

## 原理 170.1（冗余不是免费信息）

固定模数集合时：

\[
\boxed{
\text{扩大可表示动态范围}
\Longleftrightarrow
\text{减少最小距离与抗错余量}.
}
\]

CRT 观察系统存在精确的容量—鲁棒性阶梯，而不是“模数越多，容量和鲁棒性同时无条件变好”。

---

# 171. 显式 CRT 纠错模型

取：

\[
(m_1,m_2,m_3,m_4,m_5)
=
(3,5,7,11,13),
\]

以及：

\[
K=100.
\]

有：

\[
3\cdot5=15<100,
\]

但：

\[
3\cdot5\cdot7=105\ge100.
\]

所以：

\[
t(K)=2,
\qquad
d_{\min}=5-2=3.
\]

该系统能保证：

- 检测两个任意错误 residue；
- 纠正一个任意错误 residue；
- 或恢复两个已知擦除坐标。

达到最小距离的状态对为：

\[
x=0,
\qquad
y=15.
\]

二者在模 \(3,5\) 上相同，在模 \(7,11,13\) 上不同，故距离恰为三。

---

# 172. 精确擦除鲁棒性

对剩余坐标集：

\[
R\subseteq\{1,\ldots,n\},
\]

定义剩余乘积：

\[
M_R=\prod_{i\in R}m_i.
\]

## 定理 172.1（指定擦除集后的可恢复判据）

删除 \(R^c\) 中的坐标后，剩余观察在 \(X_K\) 上仍单射，当且仅当：

\[
\boxed{M_R\ge K.}
\]

## 推论 172.1（任意 \(s\) 个擦除的鲁棒判据）

系统对任意 \(s\) 个坐标擦除仍忠实，当且仅当：

\[
\boxed{
K
\le
\prod_{i=1}^{n-s}m_i.
}
\]

最坏擦除会删除最大的 \(s\) 个模数，使保留乘积最小。

## 原理 172.1（坐标价值依赖任务）

大模数通常提供更高静态容量；但在“任意坐标可能失效”的最坏情形中，系统鲁棒性由最小模数子族控制。传感器价值不能只按单坐标 bit 数排序，还必须审计其在最坏保留子集中的承重性。

---

# Part XXV：自适应素数实验、决策树与横纵观察预算

# 173. 自适应观察协议

设有限状态空间为 \(X\)，观察器族为：

\[
q_i:X\to O_i.
\]

## 定义 173.1（自适应协议）

一个确定性自适应协议是一棵决策树。每个内部节点根据此前输出历史选择下一个观察器 \(i\)，边由输出 \(o\in O_i\) 标记，叶节点输出候选状态或任务值。

## 定义 173.2（精确识别协议）

若每个可达叶节点对应的状态纤维是单点，则协议精确识别 \(X\)。

## 定义 173.3（自适应最坏深度）

\[
D_{\mathrm{ad}}(X,q)
=
\min_{\Pi}
\max_{x\in X}
\operatorname{depth}_{\Pi}(x),
\]

其中 \(\Pi\) 遍历精确识别协议。

## 定义 173.4（静态传感器数）

\[
D_{\mathrm{stat}}(X,q)
=
\min
\{|J|:q_J\text{ 单射}\}.
\]

静态协议必须预先读取同一组坐标；自适应协议可以根据前一输出决定后续读取哪个素数。

---

# 174. 决策树容量下界

假设每个观察器输出数至多为：

\[
|O_i|\le B.
\]

## 定理 174.1（最坏深度信息下界）

任何深度至多 \(h\) 的确定性协议最多拥有：

\[
B^h
\]

个叶节点。因此若协议精确识别 \(X\)：

\[
|X|\le B^h.
\]

所以：

\[
\boxed{
D_{\mathrm{ad}}(X,q)
\ge
\left\lceil
\log_B|X|
\right\rceil.
}
\]

## 原理 174.1（自适应不能突破信息容量）

自适应可以避免读取与当前分支无关的坐标，但不能让一个至多 \(B\) 分支的询问携带超过 \(\log_2B\) bit 的最坏情况区分能力。

---

# 175. 自适应严格优于任意固定二素数预算的显式 CRT 模型

取状态集合：

\[
X=\{0,10,15,21\}.
\]

使用三个单精度剩余观察器：

\[
q_2(x)=x\bmod2,
\qquad
q_3(x)=x\bmod3,
\qquad
q_5(x)=x\bmod5.
\]

完整画像为：

\[
\begin{array}{c|ccc}
x&q_2&q_3&q_5\\
\hline
0&0&0&0\\
10&0&1&0\\
15&1&0&0\\
21&1&0&1
\end{array}
\]

## 定理 175.1（任意固定两个坐标都不完备）

- \((q_2,q_3)\) 合并 \(15,21\)；
- \((q_2,q_5)\) 合并 \(0,10\)；
- \((q_3,q_5)\) 合并 \(0,15\)。

因此：

\[
D_{\mathrm{stat}}(X,q)=3.
\]

## 定理 175.2（两步自适应协议）

先读取 \(q_2\)：

- 若输出为零，候选为 \(\{0,10\}\)，再读 \(q_3\)；
- 若输出为一，候选为 \(\{15,21\}\)，再读 \(q_5\)。

两条分支都在第二步结束。又因为单独的 \(q_2,q_3,q_5\) 均不单射，任何一步协议都不可能精确识别四个状态，所以：

\[
D_{\mathrm{ad}}(X,q)=2.
\]

故：

\[
\boxed{
D_{\mathrm{ad}}(X,q)
<
D_{\mathrm{stat}}(X,q).
}
\]

## 原理 175.1（融合预算与执行预算分离）

联盟为了覆盖所有可能分支，可能需要拥有 \(\{2,3,5\}\) 三个传感器；但每次实际识别只需调用其中两个。设备可用集合、单次执行成本和最坏静态并行成本是三个不同量。

---

# 176. 素数见证搜索与 primorial 观察深度

对有界整数：

\[
X_N=\{0,\ldots,N-1\},
\]

定义：

\[
r(N)
=
\min
\left\{
r:\prod_{j=1}^{r}p_j\ge N
\right\}.
\]

## 定理 176.1（单精度水平完备深度）

假设 \(N\ge2\)。

前 \(r(N)\) 个素数的一次剩余读出联合忠实，而前 \(r(N)-1\) 个不忠实：

\[
\boxed{
D_{\mathrm{horizontal}}(N)=r(N).
}
\]

### 证明

前 \(r\) 个素数乘积即其 CRT 模数。第 9.1 节的有界整数判据给出乘积不小于 \(N\) 当且仅当联合读出单射。\(\square\)

## 定义 176.1（单素数纵向完备深度）

固定 \(p\)：

\[
k_p(N)
=
\min\{k:p^k\ge N\}
=
\lceil\log_pN\rceil.
\]

## 定理 176.2（横纵 bit 成本下界一致）

水平方案成本：

\[
\sum_{j=1}^{r(N)}\log_2p_j
=
\log_2P_{r(N)}
\ge
\log_2N.
\]

纵向方案成本：

\[
k_p(N)\log_2p
\ge
\log_2N.
\]

两者都服从身份识别的容量下界，但其错误几何不同。

## 原理 176.1（同 bit 数的结构并不相同）

\[
\boxed{
\begin{aligned}
\text{单素数高精度}
&:\quad
\text{嵌套、增量、单通道失效};\\
\text{多素数低精度}
&:\quad
\text{CRT 独立、并行、可构造编码距离}.
\end{aligned}
}
\]

bit 数只度量容量，不度量故障域、来源独立和纠错能力。

---

# 177. 素数—时间自适应完成

对动力系统：

\[
F:X\to X,
\]

自适应协议在每一步可选择：

\[
(i,n)
\]

并读取：

\[
q_i(F^nx).
\]

## 定义 177.1（自适应 prime-time 复杂度）

\[
D_{\mathrm{PT}}^{\mathrm{ad}}(X,F,q)
\]

是精确识别初始预测状态所需的最小最坏查询次数，其中查询坐标可依赖此前全部素数—时间输出。

## 定义 177.2（时间等待成本）

若读取未来时刻 \(n\) 必须真实等待，则查询代价可写为：

\[
c(i,n)=c_i+\lambda n.
\]

若可通过模拟、回放或并行实验访问，则时间代价模型必须另行指定。

## 原理 177.1（观察次数与物理等待不同）

一个协议可能只需两个读数，却需要等到很远的未来；另一个协议读数更多但在当前时刻完成。查询复杂度、时间延迟与计算模拟成本不能混为同一个“深度”。

---

# Part XXVI：赋值画像、乘积公式与单位 gauge

# 178. 有理数的乘法素数观察者

对：

\[
x\in\mathbb Q^\times,
\]

定义每个有限素数的赋值读出：

\[
q_p(x)=v_p(x)\in\mathbb Z.
\]

每个有理数只有有限多个非零赋值。

## 定义 178.1（有限赋值画像）

\[
\nu(x)
=
(v_p(x))_{p\in\mathbb P}
\in
\bigoplus_p\mathbb Z.
\]

## 定理 178.1（有理数由赋值画像与符号唯一恢复）

\[
\boxed{
\mathbb Q^\times
\cong
\{\pm1\}
\times
\bigoplus_p\mathbb Z.
}
\]

显式恢复为：

\[
\boxed{
x
=
\operatorname{sgn}(x)
\prod_p p^{v_p(x)}.
}
\]

### 证明

将分子、分母分别作唯一素因数分解。正指数来自分子，负指数来自分母；约分保证同一素数不同时出现在两侧。剩余单位恰为 \(\pm1\)。\(\square\)

## 推论 178.1（有限素数赋值画像的 kernel）

若只读全部有限赋值：

\[
\nu(x)=\nu(y),
\]

则：

\[
x=\pm y.
\]

因此有限赋值观察的唯一余量是有理单位群：

\[
\mathbb Z^\times=\{\pm1\}.
\]

一个 archimedean 符号位完成全局身份。

---

# 179. 乘积公式是跨所有 place 的校验方程

对有理数采用标准归一化：

\[
|x|_p=p^{-v_p(x)},
\qquad
|x|_\infty=\text{通常绝对值}.
\]

## 经典定理 179.1（有理数乘积公式）

对任意：

\[
x\in\mathbb Q^\times,
\]

有：

\[
\boxed{
|x|_\infty
\prod_p|x|_p
=1.
}
\]

取对数：

\[
\boxed{
\log|x|_\infty
-
\sum_pv_p(x)\log p
=0.
}
\]

该和实际为有限和。

## 原理 179.1（乘积公式校验而不增加独立秩）

若已知全部有限赋值，则 archimedean 绝对值由乘积公式决定；它提供一致性校验，但不增加新的自由坐标。符号仍不由绝对值恢复。

因此：

\[
\boxed{
\text{冗余约束}
\ne
\text{独立语义信息}.
}
\]

## 定义 179.1（乘积公式缺陷）

对候选局部读数 \((a_v)_v\)，定义：

\[
\epsilon_{\mathrm{PF}}
=
\sum_v\log a_v.
\]

合法全局非零有理数必须满足：

\[
\epsilon_{\mathrm{PF}}=0.
\]

非零值是来源错误、归一化不一致或局部画像不能来自单个全局元素的证书。

---

# 180. 数域中的有限赋值画像恢复主理想而非元素

设 \(K\) 为数域，整数环为 \(\mathcal O_K\)。对：

\[
x\in K^\times,
\]

定义有限 place 赋值族：

\[
(v_{\mathfrak p}(x))_{\mathfrak p}.
\]

## 定理 180.1（有限赋值画像的对象层）

有限赋值画像唯一决定主分式理想：

\[
\boxed{
(x)
=
\prod_{\mathfrak p}
\mathfrak p^{v_{\mathfrak p}(x)}.
}
\]

但：

\[
(v_{\mathfrak p}(x))_{\mathfrak p}
=
(v_{\mathfrak p}(y))_{\mathfrak p}

\iff
x/y\in\mathcal O_K^\times.
\]

所以 finite-place 观察的 kernel 是单位群：

\[
\boxed{
\ker\nu_K
=
\mathcal O_K^\times.
}
\]

## 推论 180.1（理想身份、主性与生成元三层）

必须区分：

\[
\boxed{
\begin{aligned}
\text{全部理想赋值}
&\Rightarrow
\text{恢复分式理想};\\
\text{类群为零}
&\Rightarrow
\text{判断该理想是否可取全局生成元};\\
\text{单位坐标}
&\Rightarrow
\text{在全部生成元中恢复具体元素}.
\end{aligned}
}
\]

v1.1 的 class-group residual 处理“理想是否主”；本节的 unit-gauge residual 处理“主理想的哪个生成元”。

---

# 181. 主除子正合观察序列

令：

\[
\operatorname{Div}_f(K)
=
\bigoplus_{\mathfrak p}\mathbb Z[\mathfrak p]
\]

为有限素理想上的 divisor 群。定义主除子映射：

\[
\operatorname{div}:K^\times
\to
\operatorname{Div}_f(K),
\qquad
x\mapsto
\sum_{\mathfrak p}v_{\mathfrak p}(x)[\mathfrak p].
\]

## 经典定理 181.1（观察正合序列）

存在正合序列：

\[
\boxed{
1
\to
\mathcal O_K^\times
\to
K^\times
\xrightarrow{\operatorname{div}}
\operatorname{Div}_f(K)
\to
\operatorname{Cl}(K)
\to
0.
}
\]

其观察含义为：

- kernel \(\mathcal O_K^\times\)：素理想赋值看不见的生成元 gauge；
- image：能够来自全局元素的 principal divisor；
- cokernel \(\operatorname{Cl}(K)\)：局部整数指数族不能由单个全局元素产生的 principalization 障碍。

## 原理 181.1（kernel 与 cokernel 是两种不同盲区）

\[
\boxed{
\begin{aligned}
\ker(\operatorname{div})
&=\text{多个全局元素给出同一局部画像};\\
\operatorname{coker}(\operatorname{div})
&=\text{合法局部画像没有全局元素来源}.
\end{aligned}
}
\]

前者是身份／gauge 余量，后者是胶合余量。它们不能由同一个“局部—全局失败”词覆盖。

---

# 182. Dirichlet 单位定理把 unit gauge 变成 archimedean 格

设：

\[
r_1=\text{实嵌入数},
\qquad
r_2=\text{共轭复嵌入对数}.
\]

## 经典定理 182.1（单位群结构）

\[
\boxed{
\mathcal O_K^\times
\cong
\mu_K
\times
\mathbb Z^{r_1+r_2-1},
}
\]

其中 \(\mu_K\) 是 \(K\) 中的有限根单位群。

定义 logarithmic embedding：

\[
\lambda(u)
=
\bigl(
\log|\sigma_1(u)|,
\ldots,
2\log|\tau_{r_2}(u)|
\bigr).
\]

乘积公式使其像落在超平面：

\[
\sum_jx_j=0.
\]

自由单位部分在该超平面中形成格。

## 原理 182.1（archimedean 完成的两层）

有限赋值画像恢复 \((x)\) 后，要恢复 \(x\) 还需：

1. logarithmic archimedean 坐标，用于定位自由单位格中的点；
2. 相位／符号或根单位坐标，用于恢复 \(\mu_K\) torsion。

有理数情形：

\[
r_1=1,
\qquad
r_2=0,
\qquad
\mathcal O_{\mathbb Q}^\times=\{\pm1\},
\]

因此退化为第 178 节的单一符号位。

---

# 183. 数域乘积公式作为高维观察校验

对每个 place \(v\) 取规范绝对值 \(|\cdot|_v\)。

## 经典定理 183.1（数域乘积公式）

对任意：

\[
x\in K^\times,
\]

有：

\[
\boxed{
\prod_v|x|_v=1.
}
\]

等价地：

\[
\sum_v\log|x|_v=0.
\]

## 定义 183.1（place-observer code）

把局部对数绝对值视为坐标：

\[
L(x)=(\log|x|_v)_v.
\]

合法像落在一个余维一的线性约束超平面中。乘积公式因此是跨有限位和无穷位的全局 parity check。

## 原理 183.1（校验不等于重建）

满足：

\[
\sum_v\ell_v=0
\]

只是局部数据来自某个乘积公式相容画像的必要条件；它通常不足以证明存在 \(x\in K^\times\) 实现全部 \(\ell_v\)。还需离散赋值整数性、单位格、主除子与局部嵌入兼容等条件。

---

# Part XXVII：谱观察、迹语言饱和与扩张类余量

# 184. 幂迹观察者与 Newton 完成

设 \(K\) 为特征零域，\(A\in M_n(K)\)。定义幂迹读出：

\[
s_k(A)=\operatorname{tr}(A^k).
\]

## 定义 184.1（前 \(n\) 阶谱画像）

\[
\operatorname{SpecTr}_n(A)
=
(s_1(A),\ldots,s_n(A)).
\]

## 经典定理 184.1（Newton 身份的谱充分性）

前 \(n\) 个幂和：

\[
s_1(A),\ldots,s_n(A)
\]

唯一决定特征多项式：

\[
\chi_A(t)=
\det(tI-A).
\]

### 证明纲要

设特征值的基本对称多项式为 \(e_k\)。Newton identities 递归给出：

\[
k e_k
=
\sum_{i=1}^{k}
(-1)^{i-1}e_{k-i}s_i,
\qquad
1\le k\le n.
\]

特征零保证可除以 \(k\)。从 \(s_1,
\ldots,s_n\) 递归恢复全部 \(e_k\)，从而恢复 \(\chi_A\)。\(\square\)

## 推论 184.1（高阶幂迹不增加特征多项式信息）

由 Cayley–Hamilton 定理，\(A^n\) 是低次幂的线性组合，因此：

\[
s_{n+1},s_{n+2},\ldots
\]

都由：

\[
\chi_A,
\quad
s_1,\ldots,s_n
\]

递归决定。完整幂迹语言在“恢复特征多项式”这一目标上于深度 \(n\) 饱和。

---

# 185. 全部幂迹仍不能恢复矩阵相似类

取：

\[
A=
\begin{pmatrix}
0&0\\
0&0
\end{pmatrix},
\qquad
N=
\begin{pmatrix}
0&1\\
0&0
\end{pmatrix}.
\]

## 定理 185.1（幂迹完全盲反模型）

对每个 \(k\ge1\)：

\[
\operatorname{tr}(A^k)=0,
\qquad
\operatorname{tr}(N^k)=0.
\]

并且：

\[
\chi_A(t)=\chi_N(t)=t^2.
\]

但 \(A,N\) 不相似，因为：

\[
\operatorname{rank}(A)=0,
\qquad
\operatorname{rank}(N)=1.
\]

因此：

\[
\boxed{
\text{全部幂迹}
\not\Rightarrow
\text{矩阵相似类}.
}
\]

## 原理 185.1（谱语言饱和后的新不变量）

对上述状态对，继续增加任意高阶 \(\operatorname{tr}(A^k)\) 都无效。必须加入不通过特征多项式因子化的接口，例如：

- 最小多项式；
- kernel／rank 塔；
- Jordan block 数据；
- 受控扰动响应。

这是观察语言饱和定理在线性代数中的最小反模型。

---

# 186. nilpotent rank 塔完整恢复 Jordan 分块

设 \(N\in M_n(K)\) 为 nilpotent。定义：

\[
a_k(N)=\dim\ker(N^k),
\qquad
a_0=0.
\]

## 定理 186.1（kernel 增量计数）

令：

\[
b_k=a_k-a_{k-1}.
\]

则 \(b_k\) 等于 Jordan 分块中大小至少为 \(k\) 的 block 数。

### 证明

单个大小为 \(r\) 的 nilpotent Jordan block 对 \(\dim\ker N^k\) 的贡献是：

\[
\min(k,r).
\]

从 \(k-1\) 到 \(k\) 的增量为一，当且仅当 \(r\ge k\)。对全部 block 求和即得。\(\square\)

## 推论 186.1（rank／kernel 塔对 nilpotent 相似类忠实）

序列：

\[
(a_1,a_2,\ldots,a_n)
\]

唯一决定每种 block 大小的数量，因为大小恰为 \(k\) 的 block 数是：

\[
(b_k-b_{k+1}).
\]

所以 nilpotent 矩阵的相似类可由有限 kernel 塔恢复。

## 原理 186.1（新不变量应精确击穿旧 kernel）

幂迹语言把所有 nilpotent 矩阵压入同一零画像；kernel 塔恰好读取 nilpotent 轨道中被迹语言删除的增长结构。修复不是“加入更多数字”，而是加入一个横切旧 kernel 的新型读出。

---

# 187. 群表示的迹观察只能看见半单化

令：

\[
G=\mathbb Z
\]

由生成元 \(1\) 生成。考虑两个二维表示：

\[
\rho_0(1)=I_2,
\]

\[
\rho_u(1)
=
U
=
\begin{pmatrix}
1&1\\
0&1
\end{pmatrix}.
\]

## 定理 187.1（全群迹画像相同）

对任意 \(m\in\mathbb Z\)：

\[
U^m
=
\begin{pmatrix}
1&m\\
0&1
\end{pmatrix},
\]

故：

\[
\operatorname{tr}(\rho_u(m))=2
=
\operatorname{tr}(\rho_0(m)).
\]

所以两个表示的完整 character 画像相同。

## 定理 187.2（表示并不同构）

\(\rho_0\) 的生成元作用为恒等，最小多项式为：

\[
t-1.
\]

\(\rho_u\) 的生成元作用具有非零 nilpotent 部分，最小多项式为：

\[
(t-1)^2.
\]

因此二者不相似，表示不同构。

但它们的 semisimplification 都是：

\[
\mathbf1\oplus\mathbf1.
\]

## 原理 187.1（trace saturation 与 extension residual）

\[
\boxed{
\text{在 Brauer--Nesbitt 型适用前件下，完整 character}
\text{可以决定半单化，}
\text{却可能看不见非平凡扩张类。}
}
\]

在 Galois 表示语境中，Frobenius 迹观察若要升级为完整表示身份，必须显式加入 semisimplicity 或读取 extension／cohomology 数据；不得仅凭“几乎所有素数迹相同”无条件宣布原表示同构。

---

# 188. 素数模迹观察的双重边界

对整矩阵 \(A\in M_n(\mathbb Z)\)，定义：

\[
q_{p,k,j}(A)
=
\operatorname{tr}(A^j)\bmod p^k.
\]

## 定理 188.1（有界幂迹的 CRT 恢复）

若已知：

\[
|\operatorname{tr}(A^j)|<B_j,
\]

并选择模数乘积：

\[
M_j>2B_j,
\]

则对应 CRT 画像唯一恢复整数 \(\operatorname{tr}(A^j)\)。

## 原理 188.1（整数恢复与结构恢复分离）

即使全部整数幂迹都被精确恢复，仍只得到谱语言能够表达的对象；第 185 节的 Jordan 余量仍然存在。

所以完整过程分两层：

\[
\boxed{
\begin{aligned}
\text{局部 residues}
&\xrightarrow{\text{CRT+高度界}}
\text{全局整数迹};\\
\text{全局整数迹}
&\xrightarrow{\text{Newton}}
\text{特征多项式};\\
\text{特征多项式}
&\not\Rightarrow
\text{矩阵相似类}.
\end{aligned}
}
\]

每层都有不同前件与不同 residual。

---

# Part XXVIII：第四阶段统一——prime decomposition 的适用判据与失败分类

# 189. prime-primary 分解不是普遍本体公理

v1.0 的 CRT 和 prime-power tensor tower 展示了强分解：

\[
\text{global object}
\simeq
\prod_p\text{prime-primary factor}.
\]

v1.3 的反模型说明，该公式只有在目标范畴、对象和过程满足相应分解条件时才成立。

## 定义 189.1（prime-generated 观察范畴）

若对象 \(X\) 存在局部对象 \(X_p\) 与联合映射：

\[
q:X\to\prod_pX_p
\]

满足：

1. \(q\) 单射；
2. \(\operatorname{Im}(q)\) 的兼容条件被明确刻画；
3. 若宣称直积，则 \(q\) 还必须满射；
4. 过程、代数与准入结构逐坐标自然；

则称该对象在指定语言中 prime-generated。

## 原理 189.1（必须证明四件事）

任何“对象由所有素数坐标组成”的主张都必须分别证明：

\[
\boxed{
\text{分离}
+
\text{兼容像}
+
\text{胶合}
+
\text{结构自然性}.
}
\]

仅有元素个数分解、阶的素因数分解或一个地址双射，不足以推出对象、动力学和状态空间的 prime-primary 本体分解。

---

# 190. 四种 prime decomposition 失败

## 190.1 非幂零交互失败

\(A_5\) 的所有 \(p\)-群商都平凡。失败不是精度不足，而是非幂零群结构根本不在 prime-power quotient 语言中。

## 190.2 单位 gauge 失败

数域元素的全部有限赋值只恢复主理想，仍留下：

\[
\mathcal O_K^\times.
\]

失败位于 kernel。

## 190.3 类群胶合失败

任意 divisor 画像未必是 principal divisor，障碍位于：

\[
\operatorname{Cl}(K).
\]

失败位于 cokernel。

## 190.4 扩张类失败

全部迹或 semisimple 数据可以相同，但非平凡 extension class 不同。失败由 cohomology／Jordan 数据承载。

## 190.5 解析完成失败

全部 Euler 因子可以形式给定，但无限乘积、解析延拓、正性和零点几何仍需全局准入。失败位于收敛与解析结构，而非有限局部坐标缺失。

## 原理 190.1（失败类型决定修复类型）

\[
\boxed{
\begin{aligned}
\text{非幂零 residual}
&\Rightarrow
\text{加入更一般有限商};\\
\text{unit kernel}
&\Rightarrow
\text{加入 archimedean／单位坐标};\\
\text{class cokernel}
&\Rightarrow
\text{加入 principalization 不变量};\\
\text{extension residual}
&\Rightarrow
\text{加入 cohomology／Jordan 接口};\\
\text{analytic residual}
&\Rightarrow
\text{加入收敛、延拓与正性桥}.
\end{aligned}
}
\]

---

# 191. 观察完成的 kernel—image—cokernel 三联

给定结构保持映射：

\[
q:X\to L.
\]

必须同时审计：

\[
\boxed{
\ker(q),
\qquad
\operatorname{Im}(q),
\qquad
\operatorname{Coker}(q)
}
\]

或其非加性对应物。

## 191.1 kernel 问题

两个全局对象是否产生同一局部画像？

\[
q(x)=q(y),
\qquad
x\neq y.
\]

## 191.2 image 问题

哪些形式局部画像实际来自全局对象？

\[
\ell\in L,
\qquad
\ell\in\operatorname{Im}(q)?
\]

## 191.3 cokernel／obstruction 问题

若局部画像满足基本兼容条件却不在 image 中，哪个商、上同调类或障碍对象记录失败？

## 原理 191.1（忠实不等于满，满不等于规范）

\[
\boxed{
\text{单射}
\ne
\text{可实现像为全积}
\ne
\text{存在规范逆映射}.
}
\]

- 全部素理想赋值对理想身份可单射；
- 任意整数赋值族却不一定 principal；
- principal 以后生成元仍只确定到单位。

这三层分别是 kernel、image 和 gauge 问题。

---

# 192. 观察者升级的类型化阶梯

当某层观察语言饱和后，升级不能只写作“加入更多信息”，而应指明新信息的类型。

\[
\boxed{
\begin{array}{ccl}
\text{residue value}
&\longrightarrow&
\text{higher precision / new prime};\\
\text{quadratic character}
&\longrightarrow&
\text{higher-order character};\\
\text{prime-power quotient}
&\longrightarrow&
\text{general finite quotient};\\
\text{local ideal generator}
&\longrightarrow&
\text{ideal class};\\
\text{finite valuations}
&\longrightarrow&
\text{unit / archimedean coordinate};\\
\text{power traces}
&\longrightarrow&
\text{Jordan / extension invariant};\\
\text{finite trajectory}
&\longrightarrow&
\text{behavior quotient};\\
\text{Euler factors}
&\longrightarrow&
\text{analytic completion and positivity}.
\end{array}
}
\]

## 原理 192.1（新层必须横切旧 kernel 或填补旧 image）

一个候选升级只有在以下至少一项成立时才承重：

1. 严格缩小旧观察 kernel；
2. 扩大可实现局部画像的已证明 image；
3. 消除一个明确 cokernel／cohomology 障碍；
4. 降低动态 carry；
5. 增加错误距离而不冒充语义秩。

否则它只是同义重编码、冗余校验或未证实的本体解释。

---

# Part XXIX：v1.3 Lean 路线、有限证书与第四阶段研究纲领

# 193. 建议新增模块

在既有建议目录 `D5/S3/PrimeObservers/` 下追加：

```text
PrimeObservers/
  Logic/
    ObservableEventAlgebra.lean
    RefinementObservableAlgebra.lean
    TargetFamilyQuotient.lean
  Quotients/
    FiniteQuotientObserver.lean
    ProPObserver.lean
    PrimePowerResidual.lean
    FiniteNilpotentCompleteness.lean
    A5PrimePowerBlindness.lean
  Density/
    SeparationSpectrum.lean
    IntegerBlindPrimes.lean
    AlgebraicIntegerReductionSeparation.lean
    QuadraticCharacterSeparationDensity.lean
  Codes/
    CRTObservationCode.lean
    CRTMinimumDistance.lean
    CRTErrorErasureCorrection.lean
    CRTRangeDistanceFrontier.lean
  Adaptive/
    PrimeDecisionTree.lean
    AdaptiveCRTExample.lean
    PrimorialWitnessDepth.lean
    PrimeTimeAdaptiveProtocol.lean
  Valuations/
    RationalValuationProfile.lean
    PrincipalDivisorObservation.lean
    ProductFormulaChecksum.lean
    UnitGaugeResidual.lean
  Spectral/
    PowerTraceObserver.lean
    NewtonTraceCompletion.lean
    NilpotentTraceBlindness.lean
    NilpotentKernelTower.lean
    UnipotentExtensionResidual.lean
```

对应 Blueprint 建议保持同构目录：

```text
Blueprint/D5/S3/PrimeObservers/...
```

---

# 194. 第一优先：纯有限、低依赖定理链

## 194.1 可观察代数链

1. 饱和事件定义与逆像闭包；
2. `observableEventAlgebra_equiv_powerset_range`；
3. `refines_iff_observableAlgebra_le`；
4. 有限纤维等于 Boolean 原子；
5. 目标族商的最小充分普适性质。

## 194.2 有限群链

1. 有限 \(p\)-群商观察定义；
2. 幂零群 Sylow 乘积给出 joint injectivity；
3. 嵌入有限 \(p\)-群乘积推出幂零；
4. `finite_prime_power_observers_faithful_iff_nilpotent`；
5. \(A_5\) 对任意 \(p\)-群同态平凡的显式证明。

## 194.3 CRT code 链

1. 一致坐标集乘积整除差值；
2. `crt_minDistance_eq_card_sub_maxAgreement`；
3. 排序模数的闭式；
4. error／erasure 唯一性；
5. 动态范围—距离尖锐边界；
6. \((3,5,7,11,13),K=100\) 的 `native_decide` 有限证书。

## 194.4 自适应模型链

1. 决策树叶数上界；
2. 静态传感器集定义；
3. 状态 \(\{0,10,15,21\}\) 的三个二坐标 collision；
4. 两步自适应协议；
5. `adaptiveDepth_lt_staticSensorCard` 显式反模型。

---

# 195. 第二优先：数论基础复用链

## 195.1 整数分离谱

目标声明：

```lean
theorem blindPrimes_eq_primeDivisors_sub
    {x y : ℤ} (hxy : x ≠ y) :
    {p : ℕ | Nat.Prime p ∧ x ≡ y [ZMOD p]} =
      {p : ℕ | Nat.Prime p ∧ (p : ℤ) ∣ x - y}
```

随后证明有限性、不同素因子数的 \(\log_2\) 上界与 primorial witness。

## 195.2 代数整数约化分离

复用 Dedekind 域非零理想的有限素因子分解，证明：

```lean
theorem reduction_separates_away_from_finite_support
    {α β : 𝓞 K} (h : α ≠ β) :
    Set.Finite {P : HeightOneSpectrum (𝓞 K) |
      algebraMap _ (ResidueField P) α =
      algebraMap _ (ResidueField P) β}
```

具体 API 应按 pinned Mathlib 的 prime spectrum／maximal ideal 接口校正。

## 195.3 有理数赋值画像

证明有限支持等价：

```lean
theorem rat_mulEquiv_sign_directSum_valuation :
  ℚˣ ≃* Multiplicative (ZMod 2) ×
    Multiplicative (DirectSum ℕ fun p => ℤ)
```

正式实现可改用 `Associates`、`FreeAbelianMonoid` 或只陈述逐元素重建，避免不必要的类型工程。

## 195.4 数域 product formula 接口

优先复用仓库依赖中已经存在的：

```text
Mathlib.NumberTheory.NumberField.ProductFormula
```

把其定理包装为 prime-observer checksum，而不复制数域 product formula 的证明。

---

# 196. 第三优先：线性代数与表示余量链

## 196.1 Newton trace completion

复用 symmetric polynomial／characteristic polynomial API，证明：

```lean
theorem powerTraces_determine_charpoly
    (A B : Matrix (Fin n) (Fin n) K)
    (h : ∀ k : Fin n,
      Matrix.trace (A ^ (k.1 + 1)) =
      Matrix.trace (B ^ (k.1 + 1))) :
    Matrix.charpoly A = Matrix.charpoly B
```

## 196.2 nilpotent 反模型

```lean
def zero₂ : Matrix (Fin 2) (Fin 2) K := 0

def jordanNilpotent₂ : Matrix (Fin 2) (Fin 2) K :=
  !![0, 1; 0, 0]
```

证明全部正幂迹相同、charpoly 相同、rank 不同。

## 196.3 kernel 塔恢复 nilpotent partition

可先在显式 Jordan block multiset 模型中证明组合定理，再连接一般 nilpotent matrix 的 Jordan normal form。不要把尚未在 Mathlib 完备的 Jordan API 暗装为公理。

## 196.4 unipotent extension residual

对 \(\mathbb Z\) 的二维表示，只需证明：

\[
U^m=I+mN,
\qquad
N^2=0,
\]

即可关闭 character 相同而 minimal polynomial 不同的有限代数证书。

---

# 197. v1.3 证明状态矩阵

| 结论 | 状态 | 主要依赖／证书 |
|---|---|---|
| 可观察事件代数同构有效像幂集 | Paper | inverse image / fiber saturation |
| 精化等价于事件代数包含 | Paper | kernel-factorization |
| 目标族商为最小充分状态 | Paper | concept join / quotient |
| 全部有限商 kernel 为 finite residual | Standard + Paper packaging | finite-index normal subgroups |
| 全部 \(p\)-群商 faithful iff有限群幂零 | Paper | finite nilpotent/Sylow |
| \(A_5\) 全 prime-power 商盲 | Paper finite group proof | simplicity + order |
| 整数盲素数恰为差值素因子 | Paper | divisibility |
| 整数约化分离密度一 | Paper | finite prime divisors |
| 代数整数仅有限素理想盲 | Standard | Dedekind factorization |
| 不同二次角色分离密度 \(1/2\) | Classical, not Lean-closed here | Chebotarev/Dirichlet |
| Galois class-function 分离密度群计数 | Classical, not Lean-closed here | Chebotarev |
| CRT code 精确最小距离 | Paper | exact divisibility witness |
| CRT error/erasure 条件 | Paper | coding distance argument |
| range-distance Pareto 阶梯 | Paper | sorted subset products |
| 自适应两步优于静态三坐标 | Finite certificate | residues mod 2,3,5 |
| 有理数赋值 + 符号恢复 | Paper | unique factorization |
| 数域有限赋值 kernel 为单位群 | Standard | principal fractional ideals |
| divisor exact sequence | Classical | units/divisors/class group |
| product formula checksum | Lean infrastructure exists | NumberField.ProductFormula |
| 前 \(n\) 幂迹决定 charpoly | Classical paper bridge | Newton identities |
| 全幂迹不决定相似类 | Finite countermodel | zero vs Jordan block |
| nilpotent kernel 塔恢复 block sizes | Paper | Jordan combinatorics |
| character 不见 extension class | Finite countermodel | unipotent \(\mathbb Z\)-representation |

---

# 198. 第四阶段有限测试表

## 198.1 有限群测试

1. \(C_{12}\)：prime-power 商联合忠实；
2. \(C_2\times C_3\)：Sylow 投影恢复；
3. \(S_3\)：全部 \(p\)-群商至少留下 \(A_3\) residual；
4. \(A_5\)：全部 \(p\)-群商平凡；
5. 验证“有限 prime-power faithful iff nilpotent”的小群枚举不产生反例。

## 198.2 CRT code 测试

对：

\[
(3,5,7,11,13),
\qquad
K=100,
\]

枚举全部消息对，验证：

\[
d_{\min}=3.
\]

再测试阈值：

\[
K=105
\]

仍有：

\[
d_{\min}=3,
\]

而：

\[
K=106
\]

降为：

\[
d_{\min}=2,
\]

因为前三个最小模数乘积 \(105<K\)。

## 198.3 自适应测试

验证三个二坐标投影分别存在 collision，而决策树：

```text
mod 2
├── 0 → mod 3
└── 1 → mod 5
```

四个叶子均为单点。

## 198.4 谱反模型

验证：

\[
N^2=0,
\qquad
\operatorname{rank}(N)=1,
\]

以及全部 \(k\ge1\) 的 trace 在可归约证明中为零。

## 198.5 valuation 测试

对随机非零有理数：

\[
\frac{a}{b},
\]

从符号和有限赋值重建约分值，并验证 product formula 的有限乘积等于一。

---

# 199. v1.3 新增严格非主张

本文第四阶段明确不声称：

1. 任意对象都能由其 prime-power 商恢复；
2. profinite completion 等于全部 pro-\(p\) completion 的无条件直积；
3. 群阶的素因数分解自动给出群结构的 Sylow 直积分解；
4. 所有有限群都是幂零或可解；
5. 分离素数密度存在于任意观察系统；
6. 单射性自动给出正的最坏分离密度；
7. Chebotarev 密度定理已在本文新增 Lean 模块中关闭；
8. CRT 满动态范围同时具有非平凡任意错误纠正能力；
9. Hamming 错误模型覆盖模拟噪声、幅值扰动、相关攻击或来源伪造；
10. 多个模数数学互素即表示设备来源独立；
11. 自适应协议总比静态协议便宜；
12. 决策树查询次数等于真实物理等待时间；
13. 全部有限赋值唯一恢复数域元素；
14. product formula 的单一校验方程足以保证局部画像可全局实现；
15. archimedean 绝对值恢复复相位或单位 torsion；
16. 全部幂迹唯一恢复矩阵相似类；
17. Frobenius 迹相同在没有连续性、半单性和系数前件时推出 Galois 表示同构；
18. semisimplification 等于原表示；
19. extension class、class group、unit group 与解析障碍是同一种余量；
20. v1.3 新增纸面定理已经获得 kernel proof term、admission 或冻结收据。

---

# 200. 第四阶段统一定理图

静态逻辑链：

\[
\boxed{
q:X\to O
\Longrightarrow
\operatorname{ObsAlg}(q)
\cong
\mathcal P(\operatorname{Im}q)
\Longrightarrow
q\preceq r
\iff
\operatorname{ObsAlg}(q)
\subseteq
\operatorname{ObsAlg}(r).
}
\]

有限商链：

\[
\boxed{
G
\to
\widehat G
\to
\prod_p\widehat G_p,
\qquad
R_{\mathrm{fin}}(G)
\subseteq
R_{\mathrm{pp}}(G),
}
\]

且对有限群：

\[
\boxed{
R_{\mathrm{pp}}(G)=1
\iff
G\text{ 幂零}.
}
\]

分离频率链：

\[
\boxed{
\text{kernel 分离}
\to
\text{分离谱}
\to
\text{素数密度}
\to
\text{随机实验成功率}.
}
\]

纠错链：

\[
\boxed{
\text{CRT 动态范围 }K
\to
\text{最大一致坐标数 }t(K)
\to
 d_{\min}=n-t(K)
\to
\text{error/erasure 能力}.
}
\]

赋值链：

\[
\boxed{
1
\to
\mathcal O_K^\times
\to
K^\times
\to
\operatorname{Div}_f(K)
\to
\operatorname{Cl}(K)
\to
0.
}
\]

谱链：

\[
\boxed{
\text{power traces}
\to
\text{characteristic polynomial}
\not\to
\text{Jordan / extension identity}.
}
\]

---

# 201. 第四阶段最终命题

v1.0 建立了：

\[
\text{prime-indexed local readout}.
\]

v1.1 建立了：

\[
\text{observation-language saturation}.
\]

v1.3 进一步证明，所谓“全部素数信息”并不是单一概念。它至少依赖所允许的目标范畴：

\[
\boxed{
\begin{aligned}
\text{全部 residues}
&\neq
\text{全部 characters};\\
\text{全部 }p\text{-群商}
&\neq
\text{全部有限群商};\\
\text{全部有限 valuations}
&\neq
\text{全局元素};\\
\text{全部 traces}
&\neq
\text{完整表示};\\
\text{全部 Euler factors}
&\neq
\text{解析完成对象}.
\end{aligned}
}
\]

因此“素数观察者是否完备”必须写成带类型的问题：

\[
\boxed{
\operatorname{Complete}
(
\text{state type},
\text{observer language},
\text{target family},
\text{compatibility doctrine},
\text{dynamics}
).
}
\]

最深的第四阶段结论是：

\[
\boxed{
\text{prime-primary 分解不是世界的无条件语法；}
\text{它是一个必须由分离、胶合、幂零性、}
\text{单位、类群、扩张类与解析准入共同审计的定理。}
}
\]

换言之：

> 素数可以提供极强的局部坐标；但“所有素数坐标”究竟恢复对象、恢复商、恢复主理想、恢复半单化，还是只恢复一个形式 Euler 表，取决于接口类型。真正承重的工作不是不断增加素数，而是证明这些局部坐标的 kernel、image、cokernel、错误距离与动态自然性。

---

# Appendix I：v1.3 版本记录

- **v1.3 — 2026-08-21**：追加可观察事件代数与精化对偶、目标族最小充分商、有限商／pro-\(p\) 观察完成、有限群 prime-power 忠实当且仅当幂零、\(A_5\) 全 prime-power 盲反模型、有限商 residual 层级、素数分离谱与密度、整数与代数整数的余有限分离、二次角色及 Galois class-function 的 Chebotarev 分离密度、CRT 观察码精确最小距离与 range-distance Pareto 阶梯、自适应 CRT 决策树反模型、primorial 水平见证深度、有理数赋值—符号重建、数域单位 kernel／class cokernel／product formula checksum、幂迹 Newton 完成、nilpotent Jordan 余量、unipotent extension 反模型、prime decomposition 适用判据及 v1.3 Lean 路线。

---

# Appendix J：第四阶段外部基础来源

以下来源仅支持本文标记为经典或标准、且尚未在本仓库新模块中关闭的基础；它们不替代未来 Lean proof term：

1. J. S. Milne, *Algebraic Number Theory*, v3.08：Dedekind 分解、赋值、单位定理、global fields 与 Chebotarev 背景。
2. J. S. Milne, *Class Field Theory*, v4.03：Frobenius、局部—全局互反与 place 结构。
3. Mathlib documentation, `Mathlib.GroupTheory.FiniteIndexNormalSubgroup`：有限指数正规子群及 profinite completion 的索引基础。
4. Mathlib documentation, `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits`：profinite 群作为有限商逆极限。
5. Mathlib documentation, `Mathlib.GroupTheory.Nilpotent`：有限幂零群、Sylow 正规性与 Sylow 直积刻画。
6. Mathlib documentation, `Mathlib.GroupTheory.FiniteAbelian.Basic`：有限 Abelian 群的素数幂分解。
7. Mathlib documentation, `Mathlib.NumberTheory.NumberField.ProductFormula`：数域规范绝对值的乘积公式。
8. Jeremy J. Stone, “Multiple-Burst Error Correction with the Chinese Remainder Theorem,” *Journal of the Society for Industrial and Applied Mathematics* 11 (1963), 74–81：CRT 编码与纠错的早期来源。本文的有界整数精确距离公式在当前文稿中另给自包含证明。

---

# Appendix K：v1.3 形式化问题清单

## J.1 finite group prime-language classifier

形式化有限群 \(G\) 的以下等价：

\[
G\text{ nilpotent}
\iff
G\hookrightarrow\prod_iP_i,
\quad P_i\text{ finite }p_i\text{-groups}.
\]

并计算小群的 prime-power residual。

## J.2 separation-density bridge

建立从有限 Galois 群中共轭类计数到 prime separation density 的 paper-to-Lean 依赖图；在 Chebotarev 尚未进入 pinned Mathlib 完整接口前，不把密度结论标记为 Lean-closed。

## J.3 CRT observation code library

把 `boundedJointResidue` 从单射判据扩展为：

- Hamming distance；
- exact agreement support；
- error／erasure decoder uniqueness；
- weighted reliability；
- adaptive query trees。

## J.4 unit-gauge completion

连接：

\[
K^\times
\to
\operatorname{FractionalIdeal}(\mathcal O_K)
\to
\operatorname{ClassGroup}(\mathcal O_K),
\]

并把 kernel 明确识别为 \(\mathcal O_K^\times\)。

## J.5 trace-language saturation

在不依赖完整 Jordan normal form API 的前提下，先关闭二维 nilpotent／unipotent 反模型；随后再研究 kernel-dimension sequence 与 Jordan partition 的组合桥。

## J.6 typed observer escalation

为每个理论对象登记：

```text
state type
observer family
target family
kernel residual
image condition
cokernel / obstruction
gauge group
dynamic descent
proof status
```

使“增加新不变量层”的理由可以由结构字段自动审计，而不是由说明文字事后补充。
---

# Part XXX：追加式第五阶段——统计素数观察、似然商与决策完成

> **追加说明。** 以下各节构成 v1.4 的追加式第五阶段，从第 202 节开始连续编号。它们不改写此前的确定性纤维、概率胶合、prime-primary 边界、CRT 纠错或谱语言结论，而是处理一个此前尚未完全展开的问题：当每个素数接口本身带噪、同一状态只决定输出分布而不决定单次输出时，何谓“观察相同”、何谓“无限观察最终完成”、何谓“应当主动选择下一个素数”。
>
> **核心区分。** 本阶段严格区分：
>
> \[
> \boxed{
> \text{单次输出相同}
> \neq
> \text{输出 law 相同}
> \neq
> \text{有限样本可判别}
> \neq
> \text{无限乘积几乎处处可判别}.
> }
> \]
>
> **证明状态。** 有限离散 Hellinger、总变差、KL 乘积、Le Cam 紧界、Bhattacharyya 幂指数、固定观察套件 Bayes 风险下界以及折扣 Bellman 收缩均有仓库锚点；Kakutani 无限乘积二分、Chernoff 精确误差指数、后验鞅、静态／自适应次模优化及其本阶段综合结论仍按“经典定理 + 纸面推导 + 未来 Lean 桥”分级处理。

# 202. 从确定性读出到统计实验

此前的接口：

\[
q_i:X\to O_i
\]

把状态 \(x\) 映为一个确定输出。带噪接口应改写为 Markov kernel：

\[
K_i:X\rightsquigarrow O_i,
\qquad
x\longmapsto K_i(x,\cdot).
\]

其中 \(i\) 可以是素数 \(p\)、素数幂 \((p,k)\)、place、字符、谱坐标或任意类型化局部接口。

## 定义 202.1（统计素数观察系统）

一个统计素数观察系统为：

\[
\boxed{
\mathfrak E
=
\bigl(
X,\Theta,\pi,\mathcal I,
(O_i,\Sigma_i)_{i\in\mathcal I},
(K_i)_{i\in\mathcal I},
T,c
\bigr),
}
\]

其中：

- \(X\) 是真实状态空间；
- \(\Theta\) 是需要决策或估计的目标空间；
- \(\pi\) 是先验；
- \(K_i\) 是第 \(i\) 个观察实验；
- \(T:X\to\Theta\) 是任务目标；
- \(c_i\ge0\) 是调用接口的成本。

## 定义 202.2（Dirac 嵌入）

确定性读出是统计实验的特殊情形：

\[
K_i(x,\cdot)
=
\delta_{q_i(x)}.
\]

所以第五阶段不是替代前四阶段，而是把它们嵌入更一般的概率通道语言。

## 原理 202.1（输出随机不等于状态随机）

即使 \(x\) 固定，输出仍可随机；随机性属于接口 law：

\[
K_i(x,\cdot),
\]

而不是自动属于状态本体。必须把“状态不确定”“测量噪声”“先验不确定”分开建模。

---

# 203. law 相等才是统计观察同一性

对单个实验 \(K:X\rightsquigarrow O\)，定义 law map：

\[
\Lambda_K:X\to\mathcal P(O),
\qquad
\Lambda_K(x)=K(x,\cdot).
\]

## 定义 203.1（统计不可区分关系）

\[
\boxed{
x\sim_K^{\mathrm{law}}y
\iff
K(x,\cdot)=K(y,\cdot).
}
\]

这不是说两次实验恰好产生同一个样本，而是说所有输出事件的概率都相同：

\[
\forall A\in\Sigma_O,
\quad
K(x,A)=K(y,A).
\]

## 定理 203.1（统计 kernel 判据）

对任意后处理、任意样本量和任意随机决策器，若：

\[
x\sim_K^{\mathrm{law}}y,
\]

则由 \(K\) 生成的全部 transcript 在 \(x,y\) 下具有相同分布。

### 证明

任何 transcript law 都由 \(K(x,\cdot)\) 经乘积、条件抽样或 Markov 后处理得到。输入 measure 相等时，所有这些函子性构造保持相等。 \(\square\)

## 推论 203.1（单次偶合不能证明 law 相等）

观察到：

\[
Y_x=Y_y
\]

只是一个样本事件，既不推出：

\[
K(x,\cdot)=K(y,\cdot),
\]

也不推出状态相同。

---

# 204. 统计实验的规范有效状态商

## 定义 204.1（实验有效像）

\[
\operatorname{Eff}(K)
=
\operatorname{Im}(\Lambda_K)
\subseteq
\mathcal P(O).
\]

## 定义 204.2（统计有效状态商）

\[
\boxed{
Z_K
=
X/{\sim_K^{\mathrm{law}}}.
}
\]

由商映射 \(\eta_K:X\to Z_K\) 与单射：

\[
\overline\Lambda_K:Z_K\hookrightarrow\mathcal P(O)
\]

满足：

\[
\Lambda_K
=
\overline\Lambda_K\circ\eta_K.
\]

## 定理 204.1（规范性）

若某个表示 \(r:X\to R\) 足以决定完整输出 law，即存在：

\[
\Phi:R\to\mathcal P(O)
\]

使：

\[
\Lambda_K=\Phi\circ r,
\]

则：

\[
r(x)=r(y)
\Longrightarrow
x\sim_K^{\mathrm{law}}y.
\]

因此 \(Z_K\) 是该统计实验真正看到的最细状态，不包含任何实验无法改变其输出 law 的额外身份。

## 原理 204.1（统计状态是 law，不是样本）

\[
\boxed{
\text{sample}
\in O,
\qquad
\text{statistical state}
\in\mathcal P(O).
}
\]

把二者混同，会把偶然输出误当成本体坐标。

---

# 205. 目标充分性与后验充分性

给定目标：

\[
T:X\to\Theta.
\]

## 定义 205.1（结构性目标可识别）

称 \(K\) 对 \(T\) 结构性可识别，当：

\[
\boxed{
K(x,\cdot)=K(y,\cdot)
\Longrightarrow
T(x)=T(y).
}
\]

等价地，存在唯一映射：

\[
\overline T:Z_K\to\Theta
\]

使：

\[
T=\overline T\circ\eta_K.
\]

这只是说明不同目标值对应不同 law；它不保证一个有限样本即可无误恢复目标。

## 定义 205.2（目标后验）

对观测 \(Y=y\)，目标后验为：

\[
\Pi_y
=
T_*\pi(\cdot\mid Y=y)
\in\mathcal P(\Theta).
\]

## 经典原理 205.1（后验是 Bayes 决策的规范统计量）

在正则条件分布存在的标准 Borel 前件下，只要损失函数仅依赖目标 \(T(x)\) 与行动 \(a\)，则所有 Bayes 决策只需要 \(\Pi_y\)，不需要保留原始 transcript 的其他细节。

## 推论 205.1（任务状态与实验状态再次分离）

\[
\boxed{
Z_K
\quad\text{决定完整实验 law，}
\qquad
\Pi_y
\quad\text{决定给定先验和损失族的当前决策。}
}
\]

二者不是同一个对象：前者在状态侧，后者在证据侧。

---

# 206. Blackwell 序与决策风险

设两个实验：

\[
K:X\rightsquigarrow O,
\qquad
L:X\rightsquigarrow R.
\]

## 定义 206.1（Blackwell 精化）

若存在后处理 kernel：

\[
M:O\rightsquigarrow R
\]

使：

\[
L=M\circ K,
\]

则记：

\[
L\preceq_{\mathrm B}K.
\]

即 \(L\) 可由 \(K\) 的输出随机后处理得到。

## 经典定理 206.1（决策序）

在标准有限决策问题中：

\[
L\preceq_{\mathrm B}K
\]

蕴含对任意先验与任意有界损失：

\[
R_\pi^*(K)
\le
R_\pi^*(L).
\]

## 仓库锚点 206.1

`D5/S3/Estimation/DecisionRisk/FixedSuiteBayesRiskFloor.lean` 已把 Mathlib 的 `bayesRisk_le_avgRisk` 接到固定观察套件：任何只使用同一套件的学习器，其平均风险不低于该套件的 Bayes floor。

## 原理 206.1（更多信息不保证更低实现成本）

Blackwell 序只比较决策信息，不自动比较：

- 采样成本；
- 延迟；
- 计算复杂度；
- 鲁棒性；
- 隐私；
- 物理破坏性。

因此实验选择仍需要风险—成本联合目标。

---

# 207. 缺陷距离与近似模拟

精确 Blackwell 因子化过强。定义总变差模拟缺陷：

\[
\boxed{
\delta(K,L)
=
\inf_M
\sup_{x\in X}
\operatorname{TV}
\bigl(
L(x,\cdot),
(M\circ K)(x,\cdot)
\bigr),
}
\]

其中下确界遍历所有后处理 kernel \(M\)。

## 定理 207.1（有界风险稳定性，纸面）

若损失取值于 \([0,1]\)，则由一个满足：

\[
\sup_x
\operatorname{TV}
\bigl(
L_x,(MK)_x
\bigr)
\le\varepsilon
\]

的模拟器，可把任意基于 \(L\) 的决策器移植到 \(K\)，并使每个状态的风险增加至多 \(\varepsilon\)。

### 证明

对固定状态，决策后的期望损失是输出 law 上的 \([0,1]\)-值可测函数期望。两概率测度之间此类期望差由总变差控制。 \(\square\)

## 推论 207.1

\[
\delta(K,L)=0
\]

是近似 Blackwell 支配；但在缺少紧致性或 kernel 闭性时，不应无条件把下确界为零升级为存在精确模拟器。

---

# 208. 后处理不能创造统计区别

给定后处理：

\[
M:O\rightsquigarrow R,
\]

定义：

\[
P'=MP,
\qquad
Q'=MQ.
\]

## 仓库锚点 208.1

`D5/S3/TotalVariation/HellingerDataProcessing.lean` 已在有限归一化质量函数上证明：

\[
H^2(P',Q')
\le
H^2(P,Q),
\]

等价地 Bhattacharyya affinity 不减。

`D5/S3/TotalVariation/DataProcessing.lean` 与 `D5/S3/Divergence/ClassicalDPI.lean` 分别提供总变差与经典 KL 的数据处理方向。

## 原理 208.1（统计语言饱和）

若：

\[
K_x=K_y,
\]

则任意后处理后仍有：

\[
MK_x=MK_y.
\]

若：

\[
K_x\neq K_y,
\]

后处理可能保留、压缩或完全删除区别，但不能放大任何满足数据处理不等式的区分量。

## 推论 208.1（格式升级不等于观察升级）

把相同数据重新编码、摘要、可视化或交给更复杂模型：

\[
\boxed{
\text{post-processing complexity}
\not\Rightarrow
\text{new experimental information}.
}
\]

---

# 209. 四种成对证据几何

对有限输出概率质量函数 \(P,Q\)，定义：

\[
\operatorname{TV}(P,Q)
=
\frac12\sum_o|P(o)-Q(o)|,
\]

\[
\rho(P,Q)
=
\sum_o\sqrt{P(o)Q(o)},
\]

\[
H^2(P,Q)
=
\sum_o
\bigl(\sqrt{P(o)}-\sqrt{Q(o)}\bigr)^2
=
2(1-\rho(P,Q)),
\]

\[
D(P\|Q)
=
\sum_oP(o)\log\frac{P(o)}{Q(o)}.
\]

## 定义 209.1（\(\lambda\)-Chernoff 系数与能量）

对 \(0\le\lambda\le1\)：

\[
C_\lambda(P,Q)
=
\sum_o
P(o)^\lambda Q(o)^{1-\lambda},
\]

\[
E_\lambda(P,Q)
=
-\log C_\lambda(P,Q).
\]

Chernoff 信息为：

\[
C(P,Q)
=
\sup_{\lambda\in[0,1]}E_\lambda(P,Q).
\]

## 原理 209.1（各几何回答不同问题）

- \(\operatorname{TV}\)：一次最优二元检验；
- \(\rho\)／\(H^2\)：乘积 law 与平方根几何；
- \(D(P\|Q)\)：有方向的对数证据；
- \(C(P,Q)\)：i.i.d. 最优误差指数。

这些量不能因都“衡量差异”而互相替代。

---

# 210. Hellinger—总变差—检验误差桥

## 仓库锚点 210.1

`D5/S3/TotalVariation/Hellinger.lean` 已在有限归一化非负质量函数上证明：

\[
\boxed{
\frac{H^2(P,Q)}2
\le
\operatorname{TV}(P,Q),
}
\]

以及：

\[
\boxed{
\operatorname{TV}(P,Q)^2
\le
H^2(P,Q)-\frac{H^4(P,Q)}4
=
1-\rho(P,Q)^2.
}
\]

`D5/S3/Estimation/LeCamTight.lean` 给出达到总变差检验 floor 的显式 likelihood 比较事件。

## 定理 210.1（等先验 Bayes 错误）

对两个简单假设和等先验：

\[
\boxed{
P_e^*(P,Q)
=
\frac{1-\operatorname{TV}(P,Q)}2.
}
\]

因此：

\[
\frac{1-\sqrt{1-\rho(P,Q)^2}}2
\le
P_e^*(P,Q)
\le
\frac{\rho(P,Q)}2.
\]

右侧来自：

\[
\sum_o\min(P(o),Q(o))
\le
\sum_o\sqrt{P(o)Q(o)}.
\]

## 原理 210.1

Hellinger affinity 不只是“另一个距离”；它是有限检验误差与无限乘积可分性的共同乘法坐标。

---

# 211. 独立乘积实验的精确分解

设：

\[
P=P_1\otimes\cdots\otimes P_m,
\qquad
Q=Q_1\otimes\cdots\otimes Q_m.
\]

## 定理 211.1（affinity 乘法）

\[
\boxed{
\rho(P,Q)
=
\prod_{j=1}^m\rho(P_j,Q_j).
}
\]

## 推论 211.1（Hellinger 乘积公式）

\[
\boxed{
H^2(P,Q)
=
2\left(
1-
\prod_{j=1}^m
\left(1-\frac{H_j^2}{2}\right)
\right).
}
\]

所以 Hellinger 平方一般不逐坐标相加；真正可加的是：

\[
-\log\rho(P,Q)
=
\sum_j-\log\rho(P_j,Q_j).
\]

## 仓库锚点 211.1（KL）

`D5/S3/Divergence/ProductAdditivity.lean` 已证明严格正有限概率质量函数的：

\[
\boxed{
D(P_1\otimes P_2\|Q_1\otimes Q_2)
=
D(P_1\|Q_1)+D(P_2\|Q_2).
}
\]

## 定理 211.2（固定 \(\lambda\) Chernoff 能量可加）

\[
E_\lambda(P,Q)
=
\sum_jE_\lambda(P_j,Q_j).
\]

但：

\[
C(P,Q)
=
\sup_\lambda\sum_jE_{\lambda,j}
\]

一般不等于：

\[
\sum_j\sup_\lambda E_{\lambda,j},
\]

因为异质坐标必须共享同一个 \(\lambda\)。

---

# 212. 有限素数套件的精确错误坐标

对有限素数实验集 \(J\)，假设给定状态 \(x,y\) 时各坐标条件独立。记：

\[
P_{x,J}
=
\bigotimes_{p\in J}K_p(x,\cdot),
\qquad
P_{y,J}
=
\bigotimes_{p\in J}K_p(y,\cdot).
\]

定义局部 affinity：

\[
\rho_p(x,y)
=
\rho\bigl(K_p(x),K_p(y)\bigr).
\]

## 定义 212.1（有限 Bhattacharyya 证据预算）

\[
\boxed{
\mathcal B_J(x,y)
=
-\sum_{p\in J}\log\rho_p(x,y).
}
\]

于是：

\[
\rho(P_{x,J},P_{y,J})
=
e^{-\mathcal B_J(x,y)}.
\]

## 定理 212.1（有限套件误差夹逼）

\[
\boxed{
\frac{
1-\sqrt{1-e^{-2\mathcal B_J(x,y)}}
}{2}
\le
P_{e,J}^*(x,y)
\le
\frac12e^{-\mathcal B_J(x,y)}.
}
\]

## 原理 212.1（预算是能量和，不是坐标数）

两个套件即使含有相同数量的素数，也可能拥有完全不同的：

\[
\mathcal B_J(x,y).
\]

统计观察容量不能只用 \(|J|\) 衡量。

---

# 213. 重复实验不跨越 law kernel

对单实验 \(K\)，令 \(K^{\otimes n}\) 为条件独立重复 \(n\) 次。

## 定理 213.1（重复 kernel 不变）

\[
\boxed{
K_x^{\otimes n}
=
K_y^{\otimes n}
\iff
K_x=K_y
}
\qquad
(n\ge1).
\]

### 证明

反向显然。正向对乘积 law 取任意一个坐标边缘，即恢复原 law。 \(\square\)

## 推论 213.1

有限重复可以把非零区别放大，却不能使原本满足：

\[
K_x=K_y
\]

的状态变得可分。

## 定理 213.2（affinity 幂）

\[
\rho(K_x^{\otimes n},K_y^{\otimes n})
=
\rho(K_x,K_y)^n.
\]

`D5/S3/Estimation/BhattacharyyaExponent.lean` 已对仓库有限 i.i.d. 编码证明 affinity 的 \(n\) 次幂及相应检验错误下界和样本复杂度反演。

---

# 214. Chernoff 精确误差指数

设 \(P,Q\) 为不同的有限字母概率 law，先验均为正，\(P_e^*(n)\) 为 \(n\) 个 i.i.d. 样本的最优 Bayes 错误。

## 经典定理 214.1（Chernoff）

\[
\boxed{
\lim_{n\to\infty}
-\frac1n\log P_e^*(n)
=
C(P,Q).
}
\]

其中：

\[
C(P,Q)
=
-\log
\inf_{0\le\lambda\le1}
\sum_oP(o)^\lambda Q(o)^{1-\lambda}.
\]

## 原理 214.1（下界与精确指数分级）

仓库 `BhattacharyyaExponent.lean` 在 \(\lambda=\frac12\) 处给出可机器检查的乘法 affinity 与误差 floor；Chernoff 定理进一步对全部 \(\lambda\) 优化并识别精确渐近指数。不得把前者自动标记成后者已经 Lean-closed。

## 推论 214.1（同 law 的指数为零）

\[
P=Q
\iff
C(P,Q)=0.
\]

因此任何正误差指数都来自真实的 law 区别，而不是重复次数自身。

---

# 215. 异质素数实验的 Chernoff 能量

对有限 \(J\)，定义：

\[
E_{\lambda,J}(x,y)
=
\sum_{p\in J}
E_{\lambda,p}(x,y).
\]

## 定理 215.1（异质乘积）

\[
\boxed{
C(P_{x,J},P_{y,J})
=
\sup_{\lambda\in[0,1]}
E_{\lambda,J}(x,y).
}
\]

注意：

\[
\sup_\lambda\sum_pE_{\lambda,p}
\le
\sum_p\sup_\lambda E_{\lambda,p}.
\]

右侧逐坐标分别选取最优 \(\lambda\)，一般不是一个合法联合检验指数。

## 定义 215.1（保守可加证据）

选择固定：

\[
\lambda=\frac12,
\]

得到：

\[
\mathcal B_J(x,y)
=
E_{1/2,J}(x,y),
\]

它虽然未必达到 Chernoff 最优，却具有完全可加、对称和直接连接 Kakutani 乘积的优点。

---

# 216. 统计分离谱与证据谱

此前确定性分离谱只记录：

\[
q_p(x)\neq q_p(y).
\]

带噪情形需分为两层。

## 定义 216.1（\(\varepsilon\)-统计分离谱）

\[
\boxed{
\operatorname{Sep}^{\mathrm{TV}}_\varepsilon(x,y)
=
\left\{
p:
\operatorname{TV}(K_p(x),K_p(y))
\ge\varepsilon
\right\}.
}
\]

## 定义 216.2（素数证据谱）

\[
\boxed{
b_p(x,y)
=
-\log\rho_p(x,y)
\in[0,\infty].
}
\]

## 原理 216.1（集合谱不足，权重谱才决定累积）

\[
\operatorname{Sep}^{\mathrm{TV}}_0(x,y)
\]

只回答哪些素数带有非零区别；而：

\[
\sum_pb_p(x,y)
\]

回答全部独立素数证据能否累积到无限。

## 推论 216.1

- 无限多个极弱坐标可能总证据有限；
- 密度零的稀疏坐标也可能总证据无限；
- “有多少素数能区分”与“能否无限完成”不是同一命题。

---

# Part XXXI：无限素数乘积、Kakutani 二分与几乎处处统计完成

# 217. 无限素数 transcript law

枚举相关素数：

\[
p_1,p_2,\ldots
\]

并假设给定状态 \(x\) 时，各素数输出条件独立。

## 定义 217.1（无限 transcript）

\[
Y_\infty
=
(Y_{p_1},Y_{p_2},\ldots)
\in
\prod_{n\ge1}O_{p_n}.
\]

## 定义 217.2（状态乘积 law）

\[
\boxed{
\mathbf P_x
=
\bigotimes_{n\ge1}
K_{p_n}(x,\cdot).
}
\]

在标准可测空间和通常乘积测度前件下，该 law 由所有有限柱事件唯一确定。

## 原理 217.1（有限相容只构造路径 law）

乘积测度存在说明局部随机实验可组成无限 transcript；它不自动说明 transcript 来自某个更细的物理本体，也不自动说明不同状态可被它区分。

---

# 218. Kakutani 素数观察二分

固定两个状态 \(x,y\)。记：

\[
P_n=K_{p_n}(x,\cdot),
\qquad
Q_n=K_{p_n}(y,\cdot).
\]

假设每个坐标上：

\[
P_n\sim Q_n
\]

相互绝对连续。定义 Hellinger affinity：

\[
\rho_n
=
\int
\sqrt{
\frac{dP_n}{d\nu_n}
\frac{dQ_n}{d\nu_n}
}
\,d\nu_n,
\]

其中 \(\nu_n\) 可取 \(P_n+Q_n\)。

## 经典定理 218.1（Kakutani 二分）

\[
\boxed{
\mathbf P_x
\sim
\mathbf P_y
\iff
\prod_{n\ge1}\rho_n>0,
}
\]

而：

\[
\boxed{
\mathbf P_x
\perp
\mathbf P_y
\iff
\prod_{n\ge1}\rho_n=0.
}
\]

因此不存在第三种介于等价与互奇之间的 product-law 关系，前提是所有坐标 law 两两等价。

## 定义 218.1（无限证据质量）

\[
\boxed{
\mathcal B_\infty(x,y)
=
\sum_{n\ge1}
-\log\rho_n
\in[0,\infty].
}
\]

于是：

\[
\mathbf P_x\sim\mathbf P_y
\iff
\mathcal B_\infty(x,y)<\infty,
\]

\[
\mathbf P_x\perp\mathbf P_y
\iff
\mathcal B_\infty(x,y)=\infty.
\]

---

# 219. product-equivalent 区域

若：

\[
\mathcal B_\infty(x,y)<\infty,
\]

则：

\[
\mathbf P_x\sim\mathbf P_y.
\]

## 定理 219.1（无零错误分离事件）

不存在可测事件 \(A\) 使：

\[
\mathbf P_x(A)=1,
\qquad
\mathbf P_y(A)=0.
\]

### 证明

若存在，则 \(A^c\) 在 \(\mathbf P_x\) 下为零测集但在 \(\mathbf P_y\) 下为全测集，违背相互绝对连续。 \(\square\)

## 定义 219.1（无限 transcript Bayes 余量）

等先验时：

\[
\boxed{
\operatorname{BayesRes}_\infty(x,y)
=
\frac{
1-\operatorname{TV}(\mathbf P_x,\mathbf P_y)
}{2}.
}
\]

在等价区域：

\[
\operatorname{BayesRes}_\infty(x,y)>0.
\]

无限多坐标可以显著降低错误，却不必把错误压到零。

---

# 220. product-singular 区域

若：

\[
\mathcal B_\infty(x,y)=\infty,
\]

则：

\[
\mathbf P_x\perp\mathbf P_y.
\]

## 定理 220.1（几乎处处零错误分类）

存在可测事件 \(A_{x,y}\) 使：

\[
\mathbf P_x(A_{x,y})=1,
\qquad
\mathbf P_y(A_{x,y})=0.
\]

因此完整无限 transcript 在 measure-one 意义下精确区分 \(x,y\)。

## 原理 220.1（几乎处处完成不是有限证明）

该分类器可以依赖整个无限序列，且允许每个状态下的零测异常。它不产生有限时间的一致停机证书。

## 推论 220.1

\[
\boxed{
\text{infinite a.s. identifiability}
\not\Rightarrow
\text{finite exact tomography}.
}
\]

---

# 221. 无有限精确见证的无限完成

假设每个坐标上：

\[
P_n\sim Q_n.
\]

则对任意有限 \(m\)：

\[
P_1\otimes\cdots\otimes P_m
\sim
Q_1\otimes\cdots\otimes Q_m.
\]

所以没有有限前缀事件能以零错误区分两个状态。

但若：

\[
\prod_n\rho_n=0,
\]

无限乘积 law 却互奇。

## 定理 221.1（有限前缀／无限完成严格分离）

存在统计观察系统满足：

\[
\forall m<\infty,
\quad
P_{x,\le m}\sim P_{y,\le m},
\]

同时：

\[
\mathbf P_x\perp\mathbf P_y.
\]

Bernoulli 弱信号模型将在第 230—231 节给出显式族。

## 原理 221.1

确定性有限状态中的“全族分离蕴含有限子族分离”依赖有限性与点态分离。对无限随机 transcript，measure singularity 可以通过无穷多个微弱区别累积出现，不能搬用有限抽取定理。

---

# 222. Hellinger 能量判据

在离散有限坐标上：

\[
H_n^2
=
2(1-\rho_n).
\]

若每个：

\[
\rho_n>0,
\]

则无限乘积的一般判据给出：

\[
\prod_n\rho_n>0
\iff
\sum_n(1-\rho_n)<\infty.
\]

因此：

\[
\boxed{
\mathbf P_x\sim\mathbf P_y
\iff
\sum_nH_n^2<\infty,
}
\]

\[
\boxed{
\mathbf P_x\perp\mathbf P_y
\iff
\sum_nH_n^2=\infty.
}
\]

## 仓库锚点 222.1

`D5/S3/TotalVariation/Countable/HellingerCountableComparison.lean` 已证明绝对差级数可和推出平方根差级数可和，并给出逆命题失败的显式见证。该文件提供 countable Hellinger series 的比较基础，但不等同于 Kakutani product-measure theorem 已经形式化。

## 原理 222.1（平方根几何是临界几何）

无限 product law 的等价／互奇边界由：

\[
\sum H_n^2
\]

控制，而不是由：

\[
\sum \operatorname{TV}_n
\]

的某个无条件等价判据控制。

---

# 223. 坐标绝对连续前件不能省略

Kakutani 二分的整洁形式假设：

\[
P_n\sim Q_n
\quad\forall n.
\]

## 情形 223.1（单坐标互奇）

若存在 \(n\)：

\[
P_n\perp Q_n,
\]

则完整乘积立即互奇；无需无穷累积。

## 情形 223.2（只有单向绝对连续）

若：

\[
P_n\ll Q_n
\]

但：

\[
Q_n\not\ll P_n,
\]

则一般 product-law 的 Lebesgue 分解更复杂，不能直接引用“等价或互奇”的二分版本。

## 严格边界 223.1

本文后续所有基于：

\[
\prod\rho_n
\]

的 iff 判据，均显式附带坐标 law 等价或单坐标互奇已先行排除的前件。

---

# 224. 有限前缀似然比鞅

假设：

\[
P_n\ll Q_n.
\]

令：

\[
\ell_n(Y_n)
=
\frac{dP_n}{dQ_n}(Y_n),
\]

有限前缀似然比为：

\[
\boxed{
L_m
=
\prod_{n=1}^m\ell_n(Y_n).
}
\]

在 \(\mathbf Q=\bigotimes Q_n\) 下：

\[
\mathbb E_{\mathbf Q}[L_m]=1,
\]

且：

\[
\mathbb E_{\mathbf Q}[L_{m+1}\mid\mathcal F_m]
=
L_m.
\]

所以 \((L_m)\) 是非负鞅，因而几乎处处收敛到某个：

\[
L_\infty\in[0,\infty).
\]

## 原理 224.1（证据不是单调数列）

单个新样本可以暂时支持任一假设；似然比不要求逐步单调。真正稳定的是其条件期望结构与长期极限。

## 经典结论 224.1

- 在 product-equivalent 区域，极限给出有限正的 Radon–Nikodym 密度；
- 在 product-singular 区域，按适当方向有 \(L_m\to0\) 几乎处处。

该结论需要 product measure 与鞅收敛接口，尚不由当前有限 Lean 文件自动给出。

---

# 225. 后验 collapse 的精确条件

考虑二元状态：

\[
X\in\{x,y\},
\]

先验：

\[
\Pr(X=x)=a,
\qquad
0<a<1.
\]

在以 \(Q=\mathbf P_y\) 为基准的似然比 \(L_m\) 下，后验为：

\[
\boxed{
\pi_m(x)
=
\frac{aL_m}{aL_m+(1-a)}.
}
\]

## 定理 225.1（互奇区后验完成，经典推论）

若：

\[
\mathbf P_x\perp\mathbf P_y,
\]

则：

\[
\pi_m(x)\to1
\quad
\mathbf P_x\text{-a.s.},
\]

\[
\pi_m(x)\to0
\quad
\mathbf P_y\text{-a.s.}
\]

## 定理 225.2（等价区后验不完全 collapse）

若：

\[
\mathbf P_x\sim\mathbf P_y,
\]

则在混合先验 law 下，极限后验落在：

\[
(0,1)
\]

内几乎处处；不存在把两个状态零错误分开的后验极限。

## 原理 225.1

\[
\boxed{
\text{posterior collapse}
\]

不是“观察次数趋于无限”单独保证的，而由 product-law 互奇性保证。

---

# 226. 无限 Bayes 余量与观察完备性

## 定义 226.1（二元统计余量）

\[
\operatorname{StatRes}(x,y)
=
\inf_{\varphi}
\frac12
\left(
\mathbf P_x[\varphi=y]
+
\mathbf P_y[\varphi=x]
\right),
\]

其中 \(\varphi\) 遍历无限 transcript 上可测分类器。

由 Le Cam 公式：

\[
\boxed{
\operatorname{StatRes}(x,y)
=
\frac{
1-\operatorname{TV}(\mathbf P_x,\mathbf P_y)
}{2}.
}
\]

## 定理 226.1（零余量判据）

\[
\boxed{
\operatorname{StatRes}(x,y)=0
\iff
\mathbf P_x\perp\mathbf P_y.
}
\]

### 证明

概率测度总变差等于 \(1\) 当且仅当两测度互奇；代入等先验 Bayes 错误公式。 \(\square\)

## 原理 226.1（统计完备性是 measure-class 命题）

确定性完备性检查：

\[
q(x)\neq q(y).
\]

统计无限完备性检查：

\[
\mathbf P_x\perp\mathbf P_y.
\]

从点分离到测度类分离，是观察理论的一次类型跃迁。

---

# 227. 有限状态族的同时统计完成

设状态集合为有限集：

\[
X=\{x_1,\ldots,x_m\},
\]

每个状态产生无限 transcript law：

\[
\mathbf P_i
=
\mathbf P_{x_i}.
\]

## 定义 227.1（同时零错误识别）

若存在可测分类器：

\[
\Phi:\Omega\to X
\]

使：

\[
\mathbf P_i[\Phi=x_i]=1
\qquad
\forall i,
\]

则称该状态族在无限观察下同时统计完成。

## 定理 227.1（有限族 pairwise singular 即 simultaneous completion）

对有限状态族，以下条件等价：

\[
\boxed{
\forall i\neq j,
\quad
\mathbf P_i\perp\mathbf P_j
}
\]

与：

\[
\boxed{
\exists\Phi,
\quad
\mathbf P_i[\Phi=x_i]=1
\quad\forall i.
}
\]

### 证明

必要性显然：若同一个分类器在两个状态下均零错误，则事件：

\[
A_i=\{\Phi=x_i\}
\]

满足：

\[
\mathbf P_i(A_i)=1,
\qquad
\mathbf P_j(A_i)=0.
\]

充分性方面，对每个无序对 \(i<j\)，取可测集 \(B_{ij}\) 使：

\[
\mathbf P_i(B_{ij})=1,
\qquad
\mathbf P_j(B_{ij})=0.
\]

令：

\[
A_i
=
\bigcap_{j>i}B_{ij}
\cap
\bigcap_{j<i}B_{ji}^{\mathrm c}.
\]

则：

\[
\mathbf P_i(A_i)=1,
\]

且各 \(A_i\) 两两不交。把 \(A_i\) 上的输出定义为 \(x_i\)，其余零测区域任意赋值，即得 \(\Phi\)。 \(\square\)

## 原理 227.1（pairwise 与 global 在有限族中闭合）

有限状态下，不必额外寻找一个神秘的“全局识别事件”；所有成对互奇证书可以有限交汇成一个共同分类器。

---

# 228. 可数状态族的支配测度构造

设：

\[
X=\{x_0,x_1,x_2,\ldots\},
\]

且：

\[
\mathbf P_n\perp\mathbf P_m
\qquad(n\neq m).
\]

## 定义 228.1（共同支配混合）

取严格正权重：

\[
a_n>0,
\qquad
\sum_na_n=1,
\]

并定义：

\[
\lambda
=
\sum_{n=0}^{\infty}a_n\mathbf P_n.
\]

则：

\[
\mathbf P_n\ll\lambda
\qquad
\forall n.
\]

令 Radon–Nikodym 密度为：

\[
f_n
=
\frac{d\mathbf P_n}{d\lambda}.
\]

## 定理 228.1（可数 pairwise singular 的共同分割）

成对互奇推出：

\[
f_nf_m=0
\quad
\lambda\text{-a.e.}
\qquad(n\neq m).
\]

因此存在两两不交的可测集 \((A_n)_n\)，满足：

\[
\boxed{
\mathbf P_n(A_n)=1
\qquad
\forall n.
}
\]

### 证明纲要

令：

\[
S_n=\{f_n>0\}.
\]

成对互奇使：

\[
\lambda(S_n\cap S_m)=0
\qquad(n\neq m).
\]

递归定义：

\[
A_n
=
S_n\setminus\bigcup_{m<n}S_m.
\]

则 \(A_n\) 两两不交，且从 \(S_n\) 中只删除 \(\mathbf P_n\)-零测集，故 \(\mathbf P_n(A_n)=1\)。 \(\square\)

## 推论 228.1（可数无限状态也可零错误完成）

在通常可测前件下，可数状态族只要所有 transcript laws 成对互奇，就存在一个共同的几乎处处精确分类器。

## 原理 228.1（支配 measure 是共同坐标系）

这里的关键不是状态数量有限，而是可以把全部 laws 放进一个可数混合：

\[
\lambda=\text{common reference measure}.
\]

相对于该坐标系，互奇性表现为密度支撑的几乎处处不相交。

---

# 229. 不可数状态的可测统一不能由 pairwise singular 偷渡

当参数空间 \(\Theta\) 不可数时，成对结论：

\[
\mathbf P_\theta\perp\mathbf P_{\theta'}
\qquad
(\theta\neq\theta')
\]

仍然只是每一对 measure 的陈述。

## 定义 229.1（联合可测识别器）

需要的是单个可测映射：

\[
\Phi:\Omega\to\Theta
\]

满足：

\[
\mathbf P_\theta[\Phi=\theta]=1
\qquad
\forall\theta.
\]

## 原理 229.1（成对证书不自动给出不可数分割）

不可数个 pairwise separating sets 不能无条件通过不可数交并组成可测分割。还必须控制：

\[
\boxed{
\begin{aligned}
&\Theta\text{ 的可测结构};\\
&\theta\mapsto\mathbf P_\theta\text{ 的 kernel 可测性};\\
&\text{共同支配性或可测选择};\\
&\text{所需结论是逐点、几乎处处还是先验几乎处处}.
\end{aligned}
}
\]

## 定义 229.2（先验几乎处处完成）

给定先验 \(\pi\)，若：

\[
\int_\Theta
\mathbf P_\theta[\Phi=\theta]\,
\pi(d\theta)
=1,
\]

则称 \(\Phi\) 对 \(\pi\) 几乎处处完成。

它弱于：

\[
\forall\theta,
\quad
\mathbf P_\theta[\Phi=\theta]=1.
\]

## 严格边界 229.1

本文不把：

\[
\text{pairwise product singularity}
\]

直接升级为任意不可数模型的全参数 measurable tomography。该升级需要独立的标准 Borel、domination、identifiability 或 measurable-selection 定理。

---

# Part XXXII：弱素数信号、平方证据阈值与带噪剩余层析

# 230. 对称 Bernoulli 素数信号

考虑单个局部接口在两个候选状态下给出：

\[
P_\delta(1)=\frac12+\delta,
\qquad
P_\delta(0)=\frac12-\delta,
\]

\[
Q_\delta(1)=\frac12-\delta,
\qquad
Q_\delta(0)=\frac12+\delta,
\]

其中：

\[
|\delta|<\frac12.
\]

## 定理 230.1（四种局部证据的闭式）

有：

\[
\boxed{
\operatorname{TV}(P_\delta,Q_\delta)
=2|\delta|,
}
\]

\[
\boxed{
\rho(P_\delta,Q_\delta)
=\sqrt{1-4\delta^2},
}
\]

\[
\boxed{
H^2(P_\delta,Q_\delta)
=2\left(1-\sqrt{1-4\delta^2}\right),
}
\]

以及：

\[
\boxed{
D_{\mathrm{KL}}(P_\delta\Vert Q_\delta)
=2\delta
\log\frac{1+2\delta}{1-2\delta}.
}
\]

### 证明

直接在两点空间展开定义。Bhattacharyya affinity 为：

\[
2\sqrt{
\left(\frac12+\delta\right)
\left(\frac12-\delta\right)
}
=
\sqrt{1-4\delta^2}.
\]

其余公式随即得到。 \(\square\)

## 定理 230.2（弱信号二阶展开）

当 \(\delta\to0\) 时：

\[
\boxed{
H^2(P_\delta,Q_\delta)
=4\delta^2+O(\delta^4),
}
\]

\[
\boxed{
-\log\rho(P_\delta,Q_\delta)
=2\delta^2+O(\delta^4),
}
\]

\[
\boxed{
D_{\mathrm{KL}}(P_\delta\Vert Q_\delta)
=8\delta^2+O(\delta^4).
}
\]

## 原理 230.1（无限弱信号按平方积累）

单坐标总变差是一阶量：

\[
2|\delta|,
\]

但无限乘积的等价／互奇阈值由 Hellinger 能量控制，因而是二阶量：

\[
\delta^2.
\]

---

# 231. 素数衰减信号的 \(\alpha=\frac12\) 相变

对每个素数 \(p\)，取：

\[
\delta_p
=c p^{-\alpha},
\]

其中：

\[
0<c<\frac12,
\qquad
\alpha\ge0.
\]

令两种全局状态的第 \(p\) 个输出分别服从：

\[
P_{\delta_p},
\qquad
Q_{\delta_p},
\]

并假设坐标条件独立。

## 定理 231.1（弱素数信号完成阈值）

由于每个坐标两 law 严格正，Kakutani 前件成立。于是：

\[
\boxed{
\bigotimes_pP_{\delta_p}
\perp
\bigotimes_pQ_{\delta_p}
\iff
\sum_p\delta_p^2=\infty.
}
\]

而：

\[
\sum_p\delta_p^2
=c^2\sum_pp^{-2\alpha}.
\]

故：

\[
\boxed{
\begin{aligned}
\alpha\le\frac12
&\Rightarrow
\text{无限 transcript 零错误完成};\\
\alpha>\frac12
&\Rightarrow
\text{两 product laws 等价，保留正 Bayes 余量}.
\end{aligned}
}
\]

### 证明纲要

由第 230 节：

\[
H_p^2\asymp\delta_p^2.
\]

Kakutani 判据把 product singularity 等价为：

\[
\sum_pH_p^2=\infty.
\]

素数 Dirichlet 级数：

\[
\sum_pp^{-s}
\]

在 \(s>1\) 收敛，在 \(s\le1\) 发散，代入 \(s=2\alpha\)。 \(\square\)

## 推论 231.1（临界点没有有限奇异坐标）

在：

\[
\alpha=\frac12
\]

时，每个有限素数前缀的两 law 都互相绝对连续，但无限乘积互奇。

这给出一个最干净的例子：

\[
\boxed{
\text{every finite stage is noisy-overlapping,}
\quad
\text{the infinite stage is exact}.
}
\]

---

# 232. \(s=1\) 与 \(\alpha=\frac12\) 是两种不同的临界机制

第三阶段得到 zeta 素指数模型的 realizability 阈值：

\[
s=1.
\]

本阶段得到弱 Bernoulli 区分的 statistical-completion 阈值：

\[
\alpha=\frac12.
\]

二者数值不同，但结构来源可以统一。

## 定义 232.1（一次事件质量）

在 zeta 指数画像中：

\[
\mathbb P_s(V_p>0)
=p^{-s}.
\]

全局整数实现要求活跃素数几乎处处有限，因此检查：

\[
\sum_pp^{-s}.
\]

这是一次事件的发生概率累积。

## 定义 232.2（二次统计能量）

在弱 Bernoulli 观察中，单坐标偏差为 \(\delta_p\)，但可区分能量为：

\[
H_p^2\asymp\delta_p^2.
\]

因此检查：

\[
\sum_p\delta_p^2.
\]

## 统一原理 232.1（临界指数由被累积量的阶数决定）

\[
\boxed{
\begin{aligned}
\text{finite-support realizability}
&:\quad
\sum_p\text{activation probability};\\
\text{infinite statistical separation}
&:\quad
\sum_p\text{quadratic local evidence}.
\end{aligned}
}
\]

所以：

\[
1
\quad\text{与}\quad
\frac12
\]

不是同一相变的两种写法，而是两种不同 local-to-global functor 对同一素数谱的响应。

## 严格非主张 232.1

本节不声称：

\[
\alpha=\frac12
\]

与 Riemann 临界线具有解析等价、零点等价或物理因果关系。这里只存在“二次证据导致指数折半”的结构类比。

---

# 233. 带噪剩余观察的局部证据坐标

令隐藏整数状态为：

\[
n\in X\subseteq\mathbb Z.
\]

确定性剩余接口为：

\[
r_p(n)=n\bmod p.
\]

加入素数相关噪声通道：

\[
W_p:
\mathbb Z/p\mathbb Z
\rightsquigarrow
O_p.
\]

于是实际观察 law 为：

\[
K_p(n,\cdot)
=
W_p(r_p(n),\cdot).
\]

## 定义 233.1（成对局部 Hellinger 能量）

对 \(n\neq m\)，定义：

\[
\boxed{
e_p(n,m)
=
H^2\bigl(K_p(n,\cdot),K_p(m,\cdot)\bigr).
}
\]

## 定义 233.2（噪声后不可见素数）

\[
\operatorname{Blind}(n,m)
=
\{p:e_p(n,m)=0\}.
\]

它包括两种机制：

1. 算术碰撞：
   \[
   n\equiv m\pmod p;
   \]
2. 通道碰撞：不同 residue 经 \(W_p\) 后产生同一 law。

## 定理 233.1（带噪剩余的无限完成判据）

假设各坐标条件独立，且对每个 \(p\)，两局部 laws 互相绝对连续，则：

\[
\boxed{
\mathbf P_n\perp\mathbf P_m
\iff
\sum_pe_p(n,m)=\infty.
}
\]

## 原理 233.1（CRT 单射被 evidence series 替代）

无噪声时，单个不整除 \(n-m\) 的素数即可区分两整数。带噪后，每个素数可能只提供有限软证据；全局完成问题变成：

\[
\boxed{
\text{arithmetically different coordinates}
\to
\text{channel-distorted local energies}
\to
\text{divergence or convergence of their sum}.
}
\]

---

# 234. 证据加权分离谱

此前的分离谱只记录：

\[
p\in\operatorname{Sep}(x,y)
\iff
q_p(x)\neq q_p(y).
\]

带噪后需要保留强度。

## 定义 234.1（证据谱 measure）

对状态对 \(x,y\)，定义离散 measure：

\[
\boxed{
\mathcal E_{x,y}
=
\sum_pe_p(x,y)\,\delta_{\log p}.
}
\]

其截止总质量为：

\[
E_{x,y}(P)
=
\sum_{p\le P}e_p(x,y).
\]

## 定义 234.2（完成率）

若极限存在，可定义：

\[
\gamma(x,y)
=
\liminf_{P\to\infty}
\frac{E_{x,y}(P)}{\log\log P}.
\]

该归一化适用于局部能量近似 \(1/p\) 的临界族；其他尺度应使用相应归一化函数。

## 原理 234.1（计数密度不是充分统计量）

只知道 informative primes 的数量或自然密度，不能决定统计完成。真正的判据是：

\[
\boxed{
\sum_pe_p(x,y).
}
\]

例如：

\[
e_p=p^{-2}
\]

在所有素数上都正，却总能量有限；反之，某些相对密度为零的素数子集仍可拥有发散的 reciprocal evidence mass。

## 定理 234.1（临界加权正下密度充分性，纸面）

若某素数集合 \(S\) 在素数中具有正下相对密度，且对充分大 \(p\in S\)：

\[
e_p(x,y)\ge\frac{c}{p}
\]

对某个 \(c>0\) 成立，则：

\[
\sum_pe_p(x,y)=\infty,
\]

因而两无限 transcript laws 互奇。

---

# 235. 稀疏素数也能完成，稠密素数也可能失败

## 命题 235.1（零密度发散证据集存在）

存在素数子集：

\[
S\subseteq\mathbb P
\]

满足相对密度为零，但：

\[
\sum_{p\in S}\frac1p=\infty.
\]

因此若：

\[
e_p(x,y)\asymp\frac1p
\quad(p\in S),
\]

即使 informative primes 在计数意义上极稀疏，仍可统计完成。

### 一个显式纸面构造

记第 \(n\) 个素数为 \(p_n\)。对充分大的 \(k\)，令：

\[
n_k
=
\left\lfloor
k\log\log k
\right\rfloor,
\qquad
S
=
\{p_{n_k}:k\ge k_0\}.
\]

由素数定理：

\[
p_n\sim n\log n.
\]

因此：

\[
p_{n_k}
\asymp
k\log k\log\log k,
\]

从而：

\[
\sum_{p\in S}\frac1p
\asymp
\sum_{k\ge k_0}
\frac1{
k\log k\log\log k
}
=\infty.
\]

另一方面：

\[
\#\{k:n_k\le N\}
\asymp
\frac{N}{\log\log N},
\]

故 \(S\) 在全部素数索引中的相对密度为零。

## 命题 235.2（全素数正证据仍可能不完成）

若：

\[
e_p(x,y)=p^{-2},
\]

则每个素数都提供非零信息，但：

\[
\sum_pe_p(x,y)<\infty.
\]

于是 product laws 仍等价。

## 最终原理 235.1（观察资源的本体量是总证据，不是接口数）

\[
\boxed{
\text{number of sensors}
\neq
\text{total distinguishability}.
}
\]

一个无限但快速衰减的传感器族可能弱于一个零密度但临界发散的传感器族。

---

# Part XXXIII：后验状态、主动素数实验与决策动力学

# 236. 后验 belief 是主动观察的规范状态

设隐藏状态空间为有限或标准 Borel 空间 \(X\)，先验为：

\[
\pi_0\in\mathcal P(X).
\]

在历史：

\[
h_t=(i_0,y_0,\ldots,i_{t-1},y_{t-1})
\]

之后，定义后验：

\[
\boxed{
\pi_t(A)
=
\mathbb P[X\in A\mid h_t].
}
\]

## 定义 236.1（belief state）

主动观察系统的状态不是未知的真实 \(x\)，也不是原始 transcript 字符串，而是：

\[
\pi_t\in\mathcal P(X).
\]

## 定理 236.1（历史压缩）

若未来实验输出只通过隐藏状态和所选实验决定，则给定当前后验 \(\pi_t\)，未来的：

- 预测分布；
- Bayes 风险；
- 任意后续 policy 的期望成本；
- 最优 continuation value

均与产生该后验的具体历史无关。

## 原理 236.1（主动观察的最小动态商）

所有产生同一后验的 histories 对未来决策等价：

\[
\boxed{
h\sim_{\mathrm{belief}}h'
\iff
\pi_h=\pi_{h'}.
}
\]

这是统计版 predictive quotient。

---

# 237. 单步 Bayes 更新算子

选择实验 \(i\)，观察输出 \(y\)。令：

\[
k_i(y\mid x)
\]

为相对于适当基准 measure 的 likelihood。

## 定义 237.1（Bayes update）

\[
\boxed{
\mathsf B_i(\pi,y)(dx)
=
\frac{k_i(y\mid x)\pi(dx)}
{\int_Xk_i(y\mid z)\pi(dz)}.
}
\]

分母为零的输出位于当前 predictive law 的零测区域，可在其上任意定义版本。

## 定义 237.2（predictive output law）

\[
\boxed{
M_i^\pi(dy)
=
\int_XK_i(x,dy)\pi(dx).
}
\]

## 定理 237.1（belief Markov 性）

给定 \(\pi_t=\pi\) 并选择 \(i\)：

\[
Y_t\sim M_i^\pi,
\]

随后：

\[
\pi_{t+1}
=
\mathsf B_i(\pi,Y_t).
\]

因此主动观察在 belief 空间上成为完全可见 Markov 决策过程。

## 原理 237.1（观察不是读出一个值，而是移动一个 measure）

\[
\boxed{
\pi
\xrightarrow{\text{choose }i}
Y\sim M_i^\pi
\xrightarrow{\text{Bayes}}
\mathsf B_i(\pi,Y).
}
\]

---

# 238. belief 商对所有 Bayes 决策同时充分

给定行动空间 \(A\) 与损失：

\[
\ell:X\times A\to[0,\infty],
\]

定义当前停止风险：

\[
R_{\mathrm{stop}}(\pi)
=
\inf_{a\in A}
\int_X\ell(x,a)\pi(dx).
\]

## 定理 238.1（posterior universal sufficiency）

若两个 histories \(h,h'\) 产生同一后验：

\[
\pi_h=\pi_{h'},
\]

则对任意行动空间、任意损失函数和任意未来实验 policy，它们具有完全相同的条件 Bayes value。

### 证明

所有关于隐藏状态的条件期望都只依赖 conditional law：

\[
\mathcal L(X\mid h)=\pi_h.
\]

实验的未来输出 law 又由 \(\pi_h\) 与 kernel family 决定，因此递归 continuation value 相同。 \(\square\)

## 推论 238.1（task-independent dynamic quotient）

belief quotient 不是只对某个单独目标充分，而是对全部 Bayes decision problems 同时充分。

## 边界 238.1

若模型参数、噪声机制或未来环境还包含未进入 \(X\) 的隐藏变量，则只保存 \(\pi(X)\) 可能不充分；必须把所有影响未来 law 的隐变量并入 belief state。

---

# 239. 自适应素数观察 policy

## 定义 239.1（自适应 policy）

一个 policy \(\Pi\) 在每个 belief \(\pi\) 选择：

1. 停止并输出行动；或
2. 调用某个实验 \(i\in\mathcal I\)。

随机 policy 可写为：

\[
\Pi:\mathcal P(X)
\rightsquigarrow
A\sqcup\mathcal I.
\]

## 定义 239.2（总风险—成本目标）

对折扣因子 \(0<\gamma<1\)，可定义：

\[
J_\Pi(\pi)
=
\mathbb E_\pi^\Pi
\left[
\sum_{t<\tau}\gamma^tc_{I_t}
+
\gamma^\tau\ell(X,A_\tau)
\right].
\]

对不折扣的 sequential testing，也可使用：

\[
\mathbb E[\text{sample cost}]
+
\lambda\,\mathbb P[\text{decision error}].
\]

## 原理 239.1（静态 suite 与自适应 tree 不同）

静态设计选择一个集合：

\[
S\subseteq\mathcal I.
\]

自适应设计选择一棵依输出分支的实验树。前者的成本是所有被选接口之和；后者的成本是路径随机变量。

---

# 240. belief 空间 Bellman 方程

令停止值为：

\[
G(\pi)
=R_{\mathrm{stop}}(\pi).
\]

对继续实验 \(i\)，定义：

\[
Q_iV(\pi)
=
c_i
+
\gamma
\int_{O_i}
V\bigl(\mathsf B_i(\pi,y)\bigr)
M_i^\pi(dy).
\]

## 定义 240.1（主动观察 Bellman operator）

\[
\boxed{
(\mathcal TV)(\pi)
=
\min\left\{
G(\pi),
\inf_{i\in\mathcal I}Q_iV(\pi)
\right\}.
}
\]

## 原理 240.1（停止与精化竞争）

每一步都比较：

\[
\boxed{
\text{current irreducible decision risk}
\quad\text{vs}\quad
\text{price of one more refinement + future risk}.
}
\]

## 定理 240.1（形式 Bellman 最优性）

在有限状态、有限实验、有限输出和有界损失下，折扣最优值满足：

\[
V^*=\mathcal TV^*.
\]

任何在每个 belief 上达到右侧最小值的 stationary policy 都是最优的。

---

# 241. 折扣收缩给出唯一主动观察值

设 \(V,W\) 为 belief 空间上的有界函数。由于停止项相同，而每个 continuation 只把未来值乘以 \(\gamma\)，有：

\[
\boxed{
\|\mathcal TV-\mathcal TW\|_\infty
\le
\gamma\|V-W\|_\infty.
}
\]

## 定理 241.1（唯一固定点）

若：

\[
0<\gamma<1,
\]

则 \(\mathcal T\) 是严格收缩，因而存在唯一：

\[
V^*=\mathcal TV^*.
\]

价值迭代：

\[
V_{n+1}=\mathcal TV_n
\]

以几何速度收敛：

\[
\|V_n-V^*\|_\infty
\le
\gamma^n\|V_0-V^*\|_\infty.
\]

## 仓库桥 241.1

仓库已有有限状态 discounted prediction Bellman operator 的 contraction 与 unique fixed point。主动观察版本需要把固定 update 提升为 belief kernel 与动作极小化，但核心 max/min 的 Lipschitz 机制相同。

## 原理 241.1（递归观察不是无限回归）

只要未来权重严格小于一，递归的“再观察一次”不是无底循环，而是一个唯一可解的固定点：

\[
\boxed{
\text{recursive observation policy}
=
\text{contractive value equation}.
}
\]

---

# 242. 信息增益是 log-loss 下的观察价值

对离散隐藏状态 \(X\) 与实验输出 \(Y_i\)，定义：

\[
\operatorname{IG}_i(\pi)
=
I_\pi(X;Y_i).
\]

## 定理 242.1（互信息等于期望后验 KL）

\[
\boxed{
I_\pi(X;Y_i)
=
\mathbb E_{Y_i\sim M_i^\pi}
\left[
D_{\mathrm{KL}}
\bigl(
\mathsf B_i(\pi,Y_i)
\Vert
\pi
\bigr)
\right].
}
\]

## 定理 242.2（互信息等于期望熵下降）

在有限熵条件下：

\[
\boxed{
I_\pi(X;Y_i)
=
H(\pi)
-
\mathbb E[H(\pi_{i,Y_i})].
}
\]

## 原理 242.1（信息价值依赖损失）

互信息精确对应 log-loss 下的 Bayes risk reduction。对一般任务损失 \(\ell\)，真正的实验价值应定义为：

\[
\operatorname{VoI}_i^\ell(\pi)
=
R_{\mathrm{stop}}^\ell(\pi)
-
\mathbb E
\left[
R_{\mathrm{stop}}^\ell
\bigl(\mathsf B_i(\pi,Y_i)\bigr)
\right].
\]

所以：

\[
\boxed{
\text{maximum mutual information}
\neq
\text{universally optimal experiment}.
}
\]

---

# 243. 条件独立时静态信息函数次模

设有限实验集合为 \(\mathcal I\)。对：

\[
S\subseteq\mathcal I,
\]

定义联合输出：

\[
Y_S=(Y_i)_{i\in S}
\]

以及集合函数：

\[
F(S)=I(X;Y_S).
\]

假设在给定隐藏状态 \(X\) 后，各实验条件独立。

## 定理 243.1（单调性）

若 \(S\subseteq T\)，则：

\[
F(S)\le F(T).
\]

## 定理 243.2（次模性）

对：

\[
S\subseteq T,
\qquad
e\notin T,
\]

有：

\[
\boxed{
F(S\cup\{e\})-F(S)
\ge
F(T\cup\{e\})-F(T).
}
\]

### 证明

边际增益为：

\[
I(X;Y_e\mid Y_S)
=
H(Y_e\mid Y_S)
-
H(Y_e\mid X,Y_S).
\]

条件独立使：

\[
H(Y_e\mid X,Y_S)=H(Y_e\mid X).
\]

而条件熵随 conditioning 增加不增：

\[
H(Y_e\mid Y_S)
\ge
H(Y_e\mid Y_T).
\]

故得 diminishing returns。 \(\square\)

## 原理 243.1（冗余由已有 transcript 吸收）

同一实验在空历史下可能很有信息；在相关实验已经读取后，它的新增价值下降。这是静态 sensor selection 可优化性的结构来源。

---

# 244. 基数预算下的 greedy 近似

设：

\[
F(\varnothing)=0,
\]

且 \(F\) 单调次模。给定最多选择 \(k\) 个实验的预算，greedy 递归选择最大边际增益：

\[
e_t
\in
\operatorname*{argmax}_{e\notin S_t}
\left(
F(S_t\cup\{e\})-F(S_t)
\right),
\]

\[
S_{t+1}=S_t\cup\{e_t\}.
\]

## 经典定理 244.1（\(1-1/e\) 保证）

若 \(S^*\) 是大小不超过 \(k\) 的最优集合，则：

\[
\boxed{
F(S_k)
\ge
\left(1-\frac1e\right)F(S^*).
}
\]

## 证明骨架

次模性推出当前最优集合剩余元素的总边际增益至少覆盖当前 gap：

\[
\sum_{e\in S^*\setminus S_t}
\Delta(e\mid S_t)
\ge
F(S^*)-F(S_t).
\]

其中最多有 \(k\) 项，故 greedy 单步至少缩小 \(1/k\) 的剩余 gap。迭代得到：

\[
F(S^*)-F(S_k)
\le
\left(1-\frac1k\right)^kF(S^*)
\le
e^{-1}F(S^*).
\]

## 应用 244.1（静态素数套件）

在条件独立的有限 prime experiment family 中，最大化：

\[
I(X;Y_S)
\]

且每个接口等成本时，greedy prime selection 具有上述保证。

---

# 245. 非等成本预算不能由朴素 greedy 偷渡

若每个实验成本为：

\[
c_i>0,
\]

预算约束变为：

\[
\sum_{i\in S}c_i\le B.
\]

## 原理 245.1（最大增益与最大增益率不同）

可考虑：

\[
\frac{\Delta(i\mid S)}{c_i},
\]

但单纯按该比率排序不自动继承基数预算的全部结论。

## 反例机制 245.1

一个高成本实验可能单独接近最优，却被多个局部高比率小实验提前耗尽预算；反之，单纯选最大绝对增益也可能浪费成本。

## 严格结论 245.1

带 knapsack 约束的单调次模优化仍有常数近似算法，但通常需要：

- 部分枚举；
- 连续松弛；
- modified greedy；
- 与最佳单元素方案取最大；
- 或其他专门算法。

本文不把：

\[
\text{unit-cost }(1-1/e)
\]

无条件复制到任意 prime-dependent cost 模型。

---

# 246. 自适应次模性是逐 transcript 的更强性质

静态次模性比较的是集合的先验期望价值。自适应情形需要比较具体 partial realization。

## 定义 246.1（partial realization）

记：

\[
\psi
=
\{(i,y_i):i\in S\}
\]

为已观察实验及其实际输出。若 \(\psi\subseteq\psi'\)，则 \(\psi'\) 包含更多已实现信息。

## 定义 246.2（自适应边际价值）

\[
\Delta(i\mid\psi)
=
\mathbb E
\left[
U(\psi\cup\{(i,Y_i)\})-U(\psi)
\mid\psi
\right].
\]

## 定义 246.3（adaptive submodularity）

若对所有：

\[
\psi\subseteq\psi',
\qquad
i\notin\operatorname{dom}(\psi'),
\]

都有：

\[
\boxed{
\Delta(i\mid\psi)
\ge
\Delta(i\mid\psi'),
}
\]

则称效用自适应次模。

## 原理 246.1（期望 diminishing returns 不等于路径 diminishing returns）

静态：

\[
\mathbb E_\psi[\Delta(i\mid\psi)]
\]

可能随集合变小；但某个罕见输出可以使后验进入一个新区域，让另一个实验突然更有价值。因此 static submodularity 不自动推出 adaptive submodularity。

---

# 247. 自适应次模性的三状态反模型

取隐藏状态：

\[
X\in\{a,b,c\},
\]

先验：

\[
\mathbb P(a)=1-2\varepsilon,
\qquad
\mathbb P(b)=\mathbb P(c)=\varepsilon,
\]

其中：

\[
0<\varepsilon<\frac12.
\]

定义两个无噪声实验：

\[
A:
\quad
a\text{ vs }\{b,c\},
\]

\[
B:
\quad
c\text{ vs }\{a,b\}.
\]

## 定理 247.1（实验 \(B\) 的条件价值可以上升）

在任何观察之前：

\[
I(X;B)=h_2(\varepsilon),
\]

因为 \(B\) 只报告事件 \(X=c\)。

若先观察 \(A\)，并得到罕见输出：

\[
A=\text{not-}a,
\]

则后验在 \(\{b,c\}\) 上均匀：

\[
\mathbb P(b\mid A\neq a)
=
\mathbb P(c\mid A\neq a)
=\frac12.
\]

此时实验 \(B\) 完全区分 \(b,c\)，故：

\[
I(X;B\mid A\neq a)=\log2.
\]

当 \(\varepsilon\neq1/2\) 时：

\[
h_2(\varepsilon)<\log2.
\]

于是：

\[
\boxed{
\Delta(B\mid\varnothing)
<
\Delta(B\mid A=\text{not-}a).
}
\]

## 推论 247.1

即使实验在给定状态后确定性独立，基于实际后验的 entropy utility 也可以违反 adaptive diminishing returns。

## 原理 247.1（稀有分支会放大专用传感器）

一个接口的价值可能不是被已有观察“消耗”，而是被已有观察“激活”。主动观察必须允许这种 gating effect。

---

# 248. 自适应树可以严格降低期望调用数

继续使用第 247 节模型。

## 静态精确识别

任何固定的单个实验都不能区分全部三个状态，因此静态零错误 suite 必须同时调用：

\[
\{A,B\}.
\]

调用数恒为：

\[
2.
\]

## 自适应精确识别

策略：

1. 先调用 \(A\)；
2. 若输出 \(a\)，立即停止；
3. 若输出 not-\(a\)，再调用 \(B\)。

其期望调用数为：

\[
\boxed{
1+\mathbb P(X\neq a)
=1+2\varepsilon.
}
\]

由于：

\[
0<\varepsilon<\frac12,
\]

有：

\[
1+2\varepsilon<2.
\]

## 定理 248.1（自适应严格优势）


a) 两种方案均达到零错误；

b) 自适应方案的 worst-case 调用数仍为 \(2\)；

c) 自适应方案的平均调用数严格更低。

## 原理 248.1（平均成本优势来自提前停止）

自适应性不必增加单个实验的信息内容；它通过让常见 posterior region 提前终止，降低期望路径长度。

---

# 249. 鲁棒素数实验设计

先验、噪声或状态模型可能不精确。令模型不确定集为：

\[
\mathfrak M.
\]

## 定义 249.1（minimax policy）

\[
\boxed{
\Pi_{\mathrm{rob}}
\in
\operatorname*{argmin}_\Pi
\sup_{M\in\mathfrak M}
J_M(\Pi).
}
\]

## 定义 249.2（distributionally robust belief）

若当前知识不是单一后验，而是一组可能后验：

\[
\mathcal B_t\subseteq\mathcal P(X),
\]

则实验更新作用于集合：

\[
\mathcal B_{t+1}
=
\left\{
\mathsf B_i^M(\pi,y):
\pi\in\mathcal B_t,
M\in\mathfrak M
\right\}.
\]

## 原理 249.1（高信息但脆弱的 prime 不一定鲁棒最优）

一个接口可能在名义模型下具有很高互信息，却对小型 channel misspecification 极敏感。鲁棒设计应考虑：

\[
\boxed{
\text{nominal information gain}
-
\text{model sensitivity}
-
\text{cost}
-
\text{adversarial blind risk}.
}
\]

## 定理 249.1（共同 kernel 的 minimax 下界）

考虑二元 \(0\)-\(1\) 识别损失。若不确定集中包含一个允许模型 \(M_0\) 与两个状态 \(x\neq y\)，使对所有可用实验均有：

\[
K_i^{M_0}(x,\cdot)
=
K_i^{M_0}(y,\cdot),
\]

则对任意自适应 policy 和任意最终分类器：

\[
\boxed{
\max\{
\mathbb P_x^{M_0}(\widehat X\neq x),
\mathbb P_y^{M_0}(\widehat X\neq y)
\}
\ge\frac12.
}
\]

若采用在 \(x,y\) 上权重分别为 \(a,1-a\) 的 Bayes 风险，则下界为：

\[
\min\{a,1-a\}.
\]

### 证明

全部 adaptive transcript law 在 \(x,y\) 下相同，因为每一步所选 action 是同一历史的函数，而该 action 的输出 kernel 在两状态下相同。于是分类器在两状态下具有同一输出分布，不可能同时以超过 \(1/2\) 的概率正确。 \(\square\)

这是随机版的观察语言饱和：模型不确定性不能由同一共同 kernel 内部消除。

---

# 250. 后验停止边界与顺序 Hellinger 完成

## 定义 250.1（\(\varepsilon\)-完成停止）

对有限状态识别，定义 posterior error：

\[
r(\pi)
=
1-\max_{x\in X}\pi(x).
\]

停止时刻：

\[
\boxed{
\tau_\varepsilon
=
\inf\{t:r(\pi_t)\le\varepsilon\}.
}
\]

## 定理 250.1（Bayes 错误保证）

若在 \(\tau_\varepsilon\) 输出 MAP 状态，则：

\[
\mathbb P[\widehat X\neq X]
\le
\varepsilon.
\]

### 证明

给定停止历史，MAP 条件错误恰为：

\[
1-\max_x\pi_{\tau_\varepsilon}(x)
\le\varepsilon.
\]

再取全期望。 \(\square\)

## 定义 250.2（open-loop 成对证据完成）

若实验序列：

\[
i_0,i_1,\ldots
\]

预先固定，且给定状态后输出独立，则对状态对 \(x\neq y\) 定义：

\[
\mathcal H_\infty^{x,y}
=
\sum_{t=0}^{\infty}
H^2\bigl(
K_{i_t}(x,\cdot),
K_{i_t}(y,\cdot)
\bigr).
\]

## 定理 250.2（open-loop 有限状态完成）

设：

1. \(X\) 有限；
2. 每个坐标上两局部 laws 互相绝对连续；
3. 对每个 \(x\neq y\)：
   \[
   \mathcal H_\infty^{x,y}
   =
   \infty.
   \]

则各状态的无限 transcript laws 成对互奇；因此存在共同零错误分类器。对任意全支撑先验，在通常 posterior consistency 版本下：

\[
\pi_t(x_{\mathrm{true}})
\to1
\quad\text{a.s.}
\]

### 证明

对每一状态对应用第 222 节 Hellinger 能量判据，再用第 227 节有限状态同时分类定理。 \(\square\)

## 定义 250.3（自适应 conditional affinity process）

对共同历史 \(h_t\)，policy 选择：

\[
i_t=\Pi(h_t).
\]

定义该历史下状态对 \(x,y\) 的下一步 conditional affinity：

\[
\rho_t^{x,y}(h_t)
=
\rho\bigl(
K_{i_t}(x,\cdot),
K_{i_t}(y,\cdot)
\bigr),
\]

以及 predictable evidence process：

\[
\boxed{
A_n^{x,y}
=
\sum_{t<n}
-\log\rho_t^{x,y}(H_t).
}
\]

## 纸面目标 250.3（顺序 Kakutani／Hellinger 判据）

在有限 transcript laws 互相绝对连续、regular conditional kernels 存在，并满足相应顺序 Hellinger-process 二分定理的前件下：

\[
A_n^{x,y}\to\infty
\]

在两状态 path laws 下几乎处处，足以推出：

\[
\mathbf P_x^\Pi
\perp
\mathbf P_y^\Pi.
\]

该结论不是固定 product Kakutani 定理的字面实例，因为自适应 action 依赖随机历史；未来 Lean 形式化必须通过 likelihood-ratio martingale 或 sequential Hellinger process 单独证明。

## 原理 250.1（主动完成要求 pathwise persistent excitation）

正确条件不是：

\[
\text{policy 运行无限久},
\]

也不是：

\[
\text{每个 prime 曾被调用一次},
\]

而是：

\[
\boxed{
\text{对每个仍可混淆的状态对，}
\quad
\text{沿实际决策树持续积累发散的 conditional evidence}.
}
\]

## 边界 250.1

即使某个实验在先验下很有信息，policy 也可能因早期随机输出而永久避开区分某一状态对所需的接口。静态 coverage、期望信息增益与 pathwise 完成必须分别审计。

---

# 251. 第五阶段最终命题：观察完成是证据能量、belief 动力学与决策成本的共同固定点

此前四阶段分别建立了：

\[
\begin{aligned}
\text{确定性完成}
&:\quad
\text{局部坐标是否分离状态};\\
\text{概率可实现完成}
&:\quad
\text{乘积 law 是否集中在合法全局画像};\\
\text{prime-primary 完成}
&:\quad
\text{观察语言是否覆盖所需商类型};\\
\text{谱／算子完成}
&:\quad
\text{交换不变量是否遗漏相位或扩张余量}.
\end{aligned}
\]

第五阶段加入：

\[
\text{统计决策完成}
:\quad
\text{不同状态的 transcript laws 是否互奇，}
\]

以及：

\[
\text{主动完成}
:\quad
\text{policy 是否以可接受成本积累足够证据并在正确 belief 区域停止}.
\]

## 最终统一式 251.1

\[
\boxed{
\begin{aligned}
\text{typed state}
&\to
\text{experiment kernel};\\
\text{experiment kernel}
&\to
\text{law quotient};\\
\text{finite suite}
&\to
\text{TV/Hellinger/KL/Chernoff evidence};\\
\text{infinite suite}
&\to
\text{product measure class};\\
\text{history}
&\to
\text{posterior belief};\\
\text{belief}
&\to
\text{Bellman continuation};\\
\text{policy}
&\to
\text{pathwise evidence accumulation};\\
\text{stopping}
&\to
\text{task-relative completion}.
\end{aligned}
}
\]

## 最深结论 251.1

\[
\boxed{
\text{无限局部观察之所以能够产生精确全局知识，}
\text{不是因为“无限”本身，}
\text{而是因为局部 law 差异的乘积几何}
\text{把有限软证据累积成互奇的全局 measure class。}
}
\]

进一步：

\[
\boxed{
\text{主动观察的真实状态不是 transcript，}
\text{而是 posterior belief；}
\text{其最优行为不是固定传感器列表，}
\text{而是 belief 空间 Bellman 方程的 policy。}
}
\]

## 第五阶段严格非主张

本文不声称：

1. 任意无限重复都能消除噪声；
2. 每个坐标 law 不同就必然 product-singular；
3. pairwise singularity 无条件给出不可数参数的联合可测分类器；
4. Hellinger 能量发散意味着有限样本零错误；
5. product equivalence 意味着两状态本体相同；
6. posterior collapse 只由样本量决定而与 policy 无关；
7. 最大互信息实验对任意损失都最优；
8. 静态次模性自动推出自适应次模性；
9. unit-cost greedy 保证自动适用于任意成本；
10. nominal Bayes 最优自动等于 minimax 鲁棒最优；
11. \(\alpha=1/2\) 阈值构成 RH、量子测量或物理相变的证明；
12. 本阶段 Kakutani、Chernoff、posterior consistency、adaptive-submodular 与 belief-MDP 综合定理已经全部通过 Lean kernel；
13. 统计可识别自动等于计算上可高效识别；
14. 零 Bayes error 自动给出有限期望停止时间；
15. 单一 scalar divergence 能完全替代 typed kernel、image、gauge 与 task 信息。

---

# Appendix L：v1.4 版本记录与仓库锚点

## L.1 版本记录

- **v1.4 — 2026-08-22**：追加统计素数实验、law quotient、Blackwell／deficiency 序、有限测试几何、KL／Hellinger／Bhattacharyya／Chernoff 乘积证据、Kakutani product-equivalence／singularity 二分、无限 Bayes 余量、弱 Bernoulli prime signal 的 \(\alpha=1/2\) 阈值、带噪 residue evidence series、证据加权分离谱、belief-state 压缩、Bayes update、主动实验 Bellman 方程、互信息次模选择、adaptive-submodularity 反模型、提前停止优势及鲁棒观察边界。

## L.2 本阶段仓库真值锚点

1. `D5/S3/TotalVariation/Hellinger.lean`：有限 squared Hellinger 定义及与 total variation 的双边桥。
2. `D5/S3/TotalVariation/HellingerDataProcessing.lean`：随机通道下 affinity 增长与 Hellinger contraction。
3. `D5/S3/TotalVariation/Countable/HellingerCountableComparison.lean`：可数 Hellinger series 与 absolute-difference series 的单向比较及 converse failure witness。
4. `D5/S3/TotalVariation/ProductSubadditive.lean`：product total variation 次可加与严格性实例。
5. `D5/S3/Divergence/ProductAdditivity.lean`：有限正概率 law 的 KL product additivity。
6. `D5/S3/Entropy/MutualInformation.lean`：有限 mutual information 定义与非负性。
7. `D5/S3/Entropy/MutualInformationProduct.lean`：product law 的 mutual information 为零。
8. `D5/S3/Estimation/LeCam.lean` 与 `LeCamTight.lean`：二点测试 total-error floor 与显式达到者。
9. `D5/S3/Estimation/BhattacharyyaExponent.lean`：i.i.d. affinity 乘法、测试下界与 sample-complexity inversion。
10. `D5/S3/Estimation/DecisionRisk/FixedSuiteBayesRiskFloor.lean`：固定观察 suite 的 Bayes risk floor。
11. `D5/S3/Observer/DynamicProgramming/BellmanContraction.lean`：折扣 prediction Bellman operator 的 contraction 与 unique fixed point。
12. `D5/S3/Observer/MetricGeometry/FinitePredictionTruncation.lean` 及相关预测距离文件：有限截断与未来余量的度量控制。

## L.3 证明等级说明

上述 Lean 文件只锚定其实际声明。本文的：

- 无限 product measure 二分；
- Bernoulli prime threshold；
- countable simultaneous classifier；
- belief-space controlled Bellman operator；
- static/adaptive submodularity 综合；
- robust policy 与 posterior stopping

仍须按各自依赖建立独立 proof term，不因相邻有限定理已经闭合而自动升级为 `Closed`。

---

# Appendix M：第五阶段外部经典基础

以下来源只支撑标准背景和 paper-level bridge，不替代仓库中的未来 Lean 证明：

1. S. Kakutani, “On Equivalence of Infinite Product Measures,” *Annals of Mathematics* 49 (1948), 214–224, DOI `10.2307/1969123`。
2. H. Chernoff, “A Measure of Asymptotic Efficiency for Tests of a Hypothesis Based on the Sum of Observations,” *Annals of Mathematical Statistics* 23 (1952), 493–507, DOI `10.1214/aoms/1177729330`。
3. D. Blackwell, “Equivalent Comparisons of Experiments,” *Annals of Mathematical Statistics* 24 (1953), 265–272, DOI `10.1214/aoms/1177729032`。
4. L. Le Cam, *Asymptotic Methods in Statistical Decision Theory*：experiment comparison、deficiency 与 asymptotic equivalence 背景。
5. T. Cover and J. Thomas, *Elements of Information Theory*, 2nd ed.：KL、mutual information、Chernoff information 与 hypothesis testing 背景。
6. G. L. Nemhauser, L. A. Wolsey and M. L. Fisher, “An Analysis of Approximations for Maximizing Submodular Set Functions—I,” *Mathematical Programming* 14 (1978), 265–294, DOI `10.1007/BF01588971`。
7. D. Golovin and A. Krause, “Adaptive Submodularity: Theory and Applications in Active Learning and Stochastic Optimization,” *Journal of Artificial Intelligence Research* 42 (2011), 427–486, DOI `10.1613/JAIR.3278`。
8. O. Kallenberg, *Foundations of Modern Probability*, 3rd ed.：product measures、Radon–Nikodym、martingales、regular conditional distributions 与 measurable kernels。
9. A. Wald, *Sequential Analysis*：sequential probability ratio、stopping 与 sample-cost tradeoff 背景。

---

# Appendix N：v1.4 Lean 形式化路线与有限测试

## N.1 建议模块树

```text
D5/S3/Observer/Statistical/
  ExperimentKernel.lean
  LawQuotient.lean
  TargetSufficiency.lean
  BlackwellOrder.lean
  Deficiency.lean
  PairwiseEvidence.lean
  FiniteSuiteTesting.lean

D5/S3/Observer/Statistical/Product/
  AffinityFiniteProduct.lean
  HellingerEnergy.lean
  KakutaniCriterion.lean
  ProductSingularity.lean
  CountableClassifier.lean
  BernoulliPrimeThreshold.lean
  NoisyResidueEvidence.lean

D5/S3/Observer/Active/
  BeliefState.lean
  BayesUpdate.lean
  BeliefSufficiency.lean
  AdaptivePolicy.lean
  BeliefBellman.lean
  InformationGain.lean
  StaticSubmodularity.lean
  AdaptiveSubmodularity.lean
  AdaptiveFailureWitness.lean
  PosteriorStopping.lean
  RobustObservation.lean
```

## N.2 优先依赖顺序

1. finite kernel law equality 与 law quotient；
2. finite output affinity／Hellinger／TV 的统一 API；
3. finite product affinity multiplicativity；
4. finite prefix evidence sums；
5. countable product measure 与 Kakutani bridge；
6. Bernoulli closed forms 与 prime-series threshold；
7. finite belief update 与 posterior sufficiency；
8. finite belief Bellman contraction；
9. mutual-information set function 与 conditional-independence submodularity；
10. explicit adaptive countermodel；
11. robust and stopping extensions。

## N.3 定理状态矩阵

| 结论 | 当前状态 | 主要依赖 |
|---|---|---|
| law equality is the statistical kernel | Paper / finite direct | kernel extensionality |
| Blackwell postprocessing monotonicity | Classical + finite anchors | Markov kernel composition |
| Hellinger data processing | Lean-closed finite | `HellingerDataProcessing` |
| KL product additivity | Lean-closed finite positive | `ProductAdditivity` |
| Le Cam exact finite total-error floor | Lean-closed finite | `LeCamTight` |
| Bhattacharyya i.i.d. exponent | Lean-closed finite | `BhattacharyyaExponent` |
| Kakutani product dichotomy | Classical / Open Lean bridge | countable products, RN densities |
| finite pairwise singular classifier | Paper direct | finite measurable intersections |
| countable pairwise singular classifier | Paper | dominating mixture, RN theorem |
| Bernoulli local evidence formulas | Finite certificate / Lean target | two-point arithmetic |
| prime signal \(\alpha=1/2\) threshold | Paper | Kakutani + prime Dirichlet series |
| noisy residue evidence criterion | Paper schema | product criterion |
| belief is universal Bayes state | Classical / finite Lean target | conditional distributions |
| belief Bellman contraction | Paper + analogous Lean anchor | bounded functions, kernels |
| static MI submodularity | Classical / finite Lean target | entropy chain rule, CI |
| greedy \(1-1/e\) | Classical | finite submodular optimization |
| adaptive-submodularity failure witness | Finite certificate | three-state enumeration |
| adaptive expected-cost advantage | Finite certificate | decision-tree calculation |
| robust common-kernel lower bound | Paper direct | law quotient saturation |

## N.4 必要有限测试

对每次形式化实现至少检查：

1. Bernoulli closed forms：
   \[
   \rho=\sqrt{1-4\delta^2},
   \quad
   \operatorname{TV}=2|\delta|;
   \]
2. 小 \(\delta\) 数值比率：
   \[
   H^2/\delta^2\to4,
   \quad
   -\log\rho/\delta^2\to2;
   \]
3. finite product affinity 等于局部 affinity 乘积；
4. local Hellinger energy 增加时 Bayes lower bound 单调下降；
5. 三状态 adaptive countermodel 中：
   \[
   I(X;B)=h_2(\varepsilon),
   \quad
   I(X;B\mid A\neq a)=\log2;
   \]
6. 静态精确 suite 调用数为 \(2\)；
7. 自适应精确 policy 期望调用数为：
   \[
   1+2\varepsilon;
   \]
8. belief update 后质量归一化；
9. Bellman operator 的 sup-norm Lipschitz 常数不超过 \(\gamma\)；
10. common-law kernel 中任何 transcript classifier 的输出 law 相同。

## N.5 机器可审计字段

每个 statistical observer theorem 应登记：

```text
hidden state type
parameter / target type
prior
experiment kernel
output measurable space
sampling dependence assumption
law-equivalence kernel
finite evidence metric
infinite product criterion
decision loss
observation cost
policy class
stopping rule
measurability assumptions
proof status
```

这防止把：

\[
\text{finite discrete formula}
\]

静默外推为：

\[
\text{arbitrary measurable infinite theorem}.
\]

---

# Part XXXIII：追加式第六阶段——因果素数观察、干预商与反事实余量

> **追加说明。** 以下各节构成 v1.5 的追加式第六阶段，从第 252 节开始连续编号。它们不改写此前的确定性读出、概率胶合、统计 law quotient、无限 Hellinger 完成或 belief Bellman 结论，而是处理更高一层的断裂：观测一个系统、主动改变一个系统、以及询问同一单位在未发生世界中的结果，是三种不同的查询语言。
>
> **核心纪律。** 本阶段严格区分：
>
> \[
> \boxed{
> \text{observational law}
> \neq
> \text{interventional law}
> \neq
> \text{counterfactual coupling}.
> }
> \]
>
> **素数角色。** “素数干预”仍只表示由素数、素数幂或 place 索引的类型化局部实验；素数标签本身不提供因果方向、机制独立、无混杂、可运输性或反事实同一性。
>
> **证明状态。** 有限函数因子化、law quotient、mutual information、data processing、Bayes risk、动态行为商与 causal-state factorization 可由仓库现有结果锚定；do-calculus、interventional Markov equivalence、transportability、g-formula 与完整 counterfactual identification 仍按“经典外部定理、本文纸面专门化、未来 Lean 桥”分级。

# 252. 三层因果观察语言

令 \(\mathfrak M\) 为结构因果模型的候选类型。对模型 \(M\in\mathfrak M\)，定义三类画像。

## 定义 252.1（观测画像）

\[
\boxed{
\operatorname{Obs}(M)
=
\mathcal L_M(V),
}
\]

即在不主动修改机制时，全部可见变量 \(V\) 的联合 law。

## 定义 252.2（干预画像）

给定允许干预族 \(\mathcal A\)，定义：

\[
\boxed{
\operatorname{Int}_{\mathcal A}(M)
=
\bigl(
\mathcal L_M(V\mid\operatorname{do}(a))
\bigr)_{a\in\mathcal A}.
}
\]

空干预 \(a=\varnothing\) 若被包含，则其分量正是观测画像。

## 定义 252.3（反事实画像）

给定反事实查询族 \(\mathcal Q\)，定义：

\[
\boxed{
\operatorname{CF}_{\mathcal Q}(M)
=
\bigl(
\mathcal L_M(Q)
\bigr)_{Q\in\mathcal Q},
}
\]

其中 \(Q\) 可以同时包含多个互相冲突的潜在结果，如：

\[
(Y_0,Y_1),
\qquad
Y_{x,M_{x'}},
\qquad
(Y_x\mid X=x',Y=y').
\]

## 定义 252.4（三层等价关系）

\[
M\sim_{\mathrm{obs}}N
\iff
\operatorname{Obs}(M)=\operatorname{Obs}(N),
\]

\[
M\sim_{\mathrm{int},\mathcal A}N
\iff
\operatorname{Int}_{\mathcal A}(M)
=
\operatorname{Int}_{\mathcal A}(N),
\]

\[
M\sim_{\mathrm{cf},\mathcal Q}N
\iff
\operatorname{CF}_{\mathcal Q}(M)
=
\operatorname{CF}_{\mathcal Q}(N).
\]

## 原理 252.1（层级方向）

若 \(\mathcal A\) 包含空干预，且 \(\mathcal Q\) 包含每个 \(a\in\mathcal A\) 的单世界结果，则：

\[
\boxed{
\ker(\operatorname{CF}_{\mathcal Q})
\subseteq
\ker(\operatorname{Int}_{\mathcal A})
\subseteq
\ker(\operatorname{Obs}).
}
\]

后续两个显式反模型将证明两次包含都可严格。

---

# 253. 有限结构因果模型

取有限有向无环图：

\[
G=(V,E).
\]

每个节点 \(v\in V\) 有：

\[
X_v\in\mathcal X_v,
\qquad
U_v\in\mathcal U_v.
\]

## 定义 253.1（有限 SCM）

\[
\boxed{
M=
\left(
G,
(\mathcal U_v)_v,
P_U,
(f_v)_v
\right),
}
\]

其中：

\[
f_v:
\mathcal X_{\operatorname{pa}(v)}
\times
\mathcal U_v
\to
\mathcal X_v.
\]

结构方程为：

\[
X_v
=
f_v(X_{\operatorname{pa}(v)},U_v).
\]

DAG 的拓扑顺序保证给定 \(u\) 后，全部内生变量唯一求值。

## 定义 253.2（Markovian 与混杂）

若：

\[
P_U=\bigotimes_{v\in V}P_{U_v},
\]

则称模型在该表示下具有独立外生噪声。若外生变量相关，或多个结构方程共享同一外生源，则可以产生未观测混杂。

## 原理 253.1（图与模型分离）

同一个 DAG 可以承载许多不同机制和噪声 law；同一个观测 law 也可以由不同 DAG 或不同 SCM 产生。因此：

\[
\boxed{
\text{graph}
\neq
\text{mechanism family}
\neq
\text{observational distribution}.
}
\]

## 原理 253.2（表示 gauge）

不同外生变量参数化可能诱导完全相同的内生观测、干预与反事实查询。恢复某个特定 \(U\) 的名字或坐标通常不是因果目标；真正应审计的是查询画像的 kernel，而不是外生表示的字面同一。

---

# 254. 完美干预与截断机制

对节点集合 \(I\subseteq V\) 和取值 \(x_I\)，完美干预：

\[
\operatorname{do}(X_I=x_I)
\]

删除被干预节点原有的生成机制，并用常值机制替代。

## 定义 254.1（干预后 SCM）

\[
M^{\operatorname{do}(I=x_I)}
\]

保留：

\[
f_v
\quad(v\notin I),
\]

并替换：

\[
f_i^{\operatorname{do}}
\equiv x_i
\quad(i\in I).
\]

## 定理 254.1（结构求值语义）

对每个外生状态 \(u\)，干预后系统仍沿 DAG 拓扑顺序唯一求值；所得变量记为：

\[
X_v^{I=x_I}(u).
\]

## 经典定理 254.2（截断因子化，Markovian 有限情形）

若观测 law 按 DAG 因子化：

\[
P(x_V)
=
\prod_{v\in V}
P(x_v\mid x_{\operatorname{pa}(v)}),
\]

并且干预是模块化的完美干预，则：

\[
\boxed{
P(x_{V\setminus I}\mid\operatorname{do}(x_I))
=
\prod_{v\notin I}
P(x_v\mid x_{\operatorname{pa}(v)})
}
\]

在把 \(x_I\) 固定代入父坐标后成立。

## 边界 254.1

截断公式不是任意 joint law 的代数恒等式。它依赖：

- 已指定的因果图；
- 机制模块性；
- 相应 Markov／无未表示混杂前件；
- 干预确实替换机制，而不是仅条件化于事件 \(X_I=x_I\)。

---

# 255. 观测 law quotient

定义 law map：

\[
\Lambda_{\mathrm{obs}}:
\mathfrak M
\to
\mathcal P(\mathcal X_V),
\qquad
M\mapsto\operatorname{Obs}(M).
\]

## 定义 255.1（观测有效状态）

\[
\boxed{
Z_{\mathrm{obs}}
=
\operatorname{Im}(\Lambda_{\mathrm{obs}}).
}
\]

## 定义 255.2（观测余量）

\[
\operatorname{ObsRes}
=
\sum_{M,N:\mathfrak M}
(M\neq N)
\times
\bigl(
\operatorname{Obs}(M)=\operatorname{Obs}(N)
\bigr).
\]

## 定理 255.1（观测商普适性质）

若目标：

\[
T:\mathfrak M\to Y
\]

在每个观测 law 纤维上为常值，则存在唯一作用在有效像上的函数：

\[
\bar T:
Z_{\mathrm{obs}}\to Y
\]

使：

\[
\boxed{
T
=
\bar T\circ\Lambda_{\mathrm{obs}}.
}
\]

### 证明

这是函数对其 range 的 kernel-factorization。若两个模型具有同一观测 law，纤维常值性保证 \(\bar T(P)=T(M)\) 与代表选择无关；range surjectivity 给出唯一性。 \(\square\)

## 原理 255.1

观测数据能够识别的最细对象不是 SCM 本身，而是其观测 law 类。任何不在该商上稳定的因果目标，都不能仅由更多同分布被动样本恢复。

---

# 256. 干预画像与因果等价

给定允许干预族 \(\mathcal A\)，定义：

\[
\Lambda_{\mathcal A}^{\mathrm{int}}:
\mathfrak M
\to
\prod_{a\in\mathcal A}
\mathcal P(\mathcal X_V),
\]

\[
\Lambda_{\mathcal A}^{\mathrm{int}}(M)
=
\operatorname{Int}_{\mathcal A}(M).
\]

## 定义 256.1（\(\mathcal A\)-因果商）

\[
\boxed{
Z_{\mathcal A}^{\mathrm{causal}}
=
\operatorname{Im}
\left(
\Lambda_{\mathcal A}^{\mathrm{int}}
\right).
}
\]

## 定义 256.2（允许干预相对因果等价）

\[
M\sim_{\mathcal A}^{\mathrm{causal}}N
\iff
\forall a\in\mathcal A,
\quad
P_M^a=P_N^a.
\]

## 定理 256.1（干预目标因子化）

目标 \(T:\mathfrak M\to Y\) 可由允许干预的完整 law 画像决定，当且仅当：

\[
\ker
\left(
\Lambda_{\mathcal A}^{\mathrm{int}}
\right)
\subseteq
\ker T.
\]

此时 \(T\) 唯一因子化通过：

\[
Z_{\mathcal A}^{\mathrm{causal}}.
\]

## 原理 256.1（因果身份是干预语言相对的）

两个模型可以对一组干预完全等价，却被另一种未允许干预区分。因此“因果模型已经识别”必须写成：

\[
\operatorname{Identified}
(
\mathcal A,
T,
\mathfrak M
).
\]

---

# 257. 因果商的最小充分性

## 定义 257.1（干预充分接口）

读出：

\[
q:\mathfrak M\to O
\]

对干预族 \(\mathcal A\) 充分，若存在：

\[
g:
O
\to
\prod_{a\in\mathcal A}\mathcal P(\mathcal X_V)
\]

使：

\[
\Lambda_{\mathcal A}^{\mathrm{int}}
=
g\circ q.
\]

## 定理 257.1（因果状态因子化）

若 \(q\) 对 \(\mathcal A\) 充分，则存在唯一映射：

\[
\bar g:
\operatorname{Im}(q)
\to
Z_{\mathcal A}^{\mathrm{causal}}
\]

满足：

\[
\operatorname{rangeFactorization}
\left(
\Lambda_{\mathcal A}^{\mathrm{int}}
\right)
=
\bar g
\circ
\operatorname{rangeFactorization}(q).
\]

并且：

\[
\Lambda_{\mathcal A}^{\mathrm{int}}(M)
\neq
\Lambda_{\mathcal A}^{\mathrm{int}}(N)
\Longrightarrow
q(M)\neq q(N).
\]

## 仓库桥 257.1

这正是仓库 `CausalStateFactorization.lean` 的模式：任何预测／law 接口若足够充分，就唯一映射到规范 law image。这里把 `futureLaw` 专门化为完整允许干预画像。

## 原理 257.1

最小因果状态不是“最短参数向量”，而是：

\[
\boxed{
\text{所有允许干预下具有同一 law 的模型类。}
}
\]

---

# 258. 观测等价不推出干预等价

取二元变量：

\[
X,Y\in\{0,1\},
\qquad
U\sim\operatorname{Bernoulli}(1/2).
\]

构造两个 SCM。

## 模型 258.A（\(X\to Y\)）

\[
X=U,
\qquad
Y=X.
\]

## 模型 258.B（\(Y\to X\)）

\[
Y=U,
\qquad
X=Y.
\]

## 定理 258.1（观测 law 完全相同）

两模型都满足：

\[
P(X=0,Y=0)
=
P(X=1,Y=1)
=
\frac12,
\]

其余状态概率为零。因此：

\[
M_A\sim_{\mathrm{obs}}M_B.
\]

## 定理 258.2（干预 law 不同）

在模型 \(A\) 中：

\[
P_A(Y=x\mid\operatorname{do}(X=x))
=
1.
\]

在模型 \(B\) 中，干预 \(X\) 不改变 \(Y\) 的生成机制，所以：

\[
P_B(Y=1\mid\operatorname{do}(X=x))
=
\frac12.
\]

因此：

\[
\boxed{
M_A
\not\sim_{\{do(X=0),do(X=1)\}}^{\mathrm{causal}}
M_B.
}
\]

## 推论 258.1（第一层严格性）

\[
\boxed{
\ker(\operatorname{Int})
\subsetneq
\ker(\operatorname{Obs})
}
\]

在有限二元 SCM 类中已经严格。

## 原理 258.1

无限多被动样本只能把观测 joint law 估计得更精确；它不能在同一观测 law 纤维内部决定箭头方向。

---

# 259. 干预族精化与同族饱和

若：

\[
\mathcal A\subseteq\mathcal B,
\]

则限制投影满足：

\[
\Lambda_{\mathcal A}^{\mathrm{int}}
=
\pi_{\mathcal B,\mathcal A}
\circ
\Lambda_{\mathcal B}^{\mathrm{int}}.
\]

## 定理 259.1（干预精化单调性）

\[
\boxed{
\ker
\left(
\Lambda_{\mathcal B}^{\mathrm{int}}
\right)
\subseteq
\ker
\left(
\Lambda_{\mathcal A}^{\mathrm{int}}
\right).
}
\]

所以允许更多干预只能缩小或保持因果余量。

## 定义 259.1（干预语言饱和）

若目标 \(T\) 不在完整允许族 \(\mathcal A\) 的画像上因子化，则称 \(\mathcal A\) 对 \(T\) 已饱和但不充分。

## 定理 259.2（重复同族干预不能跨越 kernel）

若存在 \(M,N\) 满足：

\[
\forall a\in\mathcal A,
\quad
P_M^a=P_N^a,
\]

但：

\[
T(M)\neq T(N),
\]

则任意重复次数、样本量、随机后处理或自适应重排，只要每一步仍只调用 \(\mathcal A\)，都不能精确决定 \(T\)。

### 证明

每次 transcript kernel 都只依赖同一族 \(P_M^a=P_N^a\)。由统计 law kernel 的函子性，完整 transcript laws 在 \(M,N\) 下相同。 \(\square\)

## 原理 259.1

\[
\boxed{
\text{更多样本}
\neq
\text{更多干预类型}.
}
\]

前者降低估计误差；后者才可能缩小语义 kernel。

---

# 260. 目标相对因果余量

给定目标：

\[
T:\mathfrak M\to Y,
\]

例如：

\[
T(M)
=
P_M(Y=1\mid do(X=1))
-
P_M(Y=1\mid do(X=0)).
\]

## 定义 260.1（因果目标余量）

\[
\boxed{
\operatorname{CausalTargetRes}
(\mathcal A,T)
=
\sum_{M,N:\mathfrak M}
\left(
\forall a\in\mathcal A,
P_M^a=P_N^a
\right)
\times
\bigl(
T(M)\neq T(N)
\bigr).
}
\]

## 定理 260.1（目标可识别判据）

\[
\boxed{
\operatorname{CausalTargetRes}
(\mathcal A,T)
=
\varnothing
}
\]

当且仅当 \(T\) 因子化通过：

\[
Z_{\mathcal A}^{\mathrm{causal}}.
\]

## 定义 260.2（完全模型识别与目标识别）

完全模型识别要求：

\[
\Lambda_{\mathcal A}^{\mathrm{int}}
\quad\text{单射}.
\]

目标识别只要求：

\[
\ker
\left(
\Lambda_{\mathcal A}^{\mathrm{int}}
\right)
\subseteq
\ker T.
\]

## 原理 260.1

\[
\boxed{
\text{恢复全部 SCM}
\quad\text{通常严格强于}\quad
\text{恢复一个指定因果效应}.
}
\]

实验设计应优先覆盖目标差异，而不是无条件恢复全部机制细节。

---

# 261. 有限模型类的干预层析与集合覆盖

设候选模型类 \(\mathfrak M_0\subseteq\mathfrak M\) 有限，目标为 \(T\)。

定义需区分的模型对：

\[
\mathcal U_T
=
\left\{
\{M,N\}:
T(M)\neq T(N)
\right\}.
\]

对每个干预 \(a\)，定义其分离集：

\[
D_a
=
\left\{
\{M,N\}\in\mathcal U_T:
P_M^a\neq P_N^a
\right\}.
\]

## 定理 261.1（干预覆盖等价）

有限干预族 \(J\) 对目标 \(T\) 充分，当且仅当：

\[
\boxed{
\bigcup_{a\in J}D_a
=
\mathcal U_T.
}
\]

### 证明

若覆盖成立，则任意目标值不同的模型对都被至少一个干预 law 区分，所以相同 \(J\)-画像必有相同目标。反之，若有未覆盖模型对，则其全部 \(J\)-laws 相同而目标不同。 \(\square\)

## 推论 261.1（最小成本因果实验设计）

给每个干预成本 \(c_a\ge0\)，最小目标充分设计为：

\[
\boxed{
\min_{J}
\sum_{a\in J}c_a
\quad
\text{s.t.}
\quad
\bigcup_{a\in J}D_a
=
\mathcal U_T.
}
\]

这是 target-relative weighted set cover。

## 定理 261.2（有限干预抽取）

若全部允许干预族能区分有限模型类中的全部目标差异，则存在有限子族已经足够。证明只需为有限多个目标差异对各选一个见证干预。

---

# Part XXXIV：随机化、调整、混杂与机制模块性

# 262. 随机化把条件 law 提升为干预 law

取处理 \(X\)、结果 \(Y\) 与潜在结果 \(Y_x\)。

## 假设 262.1（随机分配）

\[
X
\perp
(Y_x)_{x\in\mathcal X}.
\]

## 假设 262.2（一致性）

\[
X=x
\Longrightarrow
Y=Y_x.
\]

## 假设 262.3（正概率）

\[
P(X=x)>0.
\]

## 定理 262.1（随机化桥）

在上述前件下：

\[
\boxed{
P(Y=y\mid X=x)
=
P(Y_x=y)
=
P(Y=y\mid do(X=x)).
}
\]

### 证明

由一致性：

\[
P(Y=y\mid X=x)
=
P(Y_x=y\mid X=x).
\]

由随机分配：

\[
P(Y_x=y\mid X=x)
=
P(Y_x=y).
\]

SCM 干预语义把 \(Y_x\) 的 law 识别为 \(do(X=x)\) law。 \(\square\)

## 原理 262.1

随机化不是“相关性变成因果性”的语言魔法；它通过切断处理分配与潜在结果之间的共同来源，使条件化与干预在指定目标上相等。

---

# 263. Back-door 调整作为局部胶合

设 \(Z\) 是处理前协变量，满足标准 back-door 条件，并假设离散有限状态与 positivity。

## 经典定理 263.1（调整公式）

\[
\boxed{
P(y\mid do(x))
=
\sum_z
P(y\mid x,z)P(z).
}
\]

## 观察者解释

每个 \(z\)-层给出局部条件效应：

\[
P(y\mid x,z).
\]

全局干预 law 不是简单平均于观测处理组的 \(P(z\mid x)\)，而是按干预前总体层权重：

\[
P(z)
\]

重新胶合。

## 定义 263.1（调整胶合缺陷）

若候选模型在所有可观测条件 laws：

\[
P(y\mid x,z),
\qquad
P(z)
\]

上相同，却给出不同 \(P(y\mid do(x))\)，则标准 back-door 前件至少有一项未满足或未被模型类编码。

## 原理 263.1

\[
\boxed{
\text{分层观察值}
+
\text{正确胶合权重}
+
\text{图形阻断前件}
\Rightarrow
\text{干预 law}.
}
\]

缺少其中任一项，局部条件统计不能被静默升级为因果效应。

---

# 264. Positivity 是因果 image 条件

调整公式中的条件项只有在相应处理值出现在该层时才由数据约束。

## 定义 264.1（positivity）

对所有 \(P(Z=z)>0\) 的层，要求：

\[
P(X=x\mid Z=z)>0
\]

对目标干预值 \(x\) 成立。

## 反模型 264.1（零支持盲区）

令观测分配恒为：

\[
X=0.
\]

考虑两个模型：

\[
M_0:
\quad
Y=0,
\]

\[
M_1:
\quad
Y=X.
\]

在观测 regime 下二者都满足：

\[
P(X=0,Y=0)=1.
\]

但在：

\[
do(X=1)
\]

下：

\[
P_{M_0}(Y=1)=0,
\qquad
P_{M_1}(Y=1)=1.
\]

## 定理 264.1（支持外机制不可由支持内数据识别）

如果行为／观测 regime 从不访问某个父配置，则结构机制在该配置上的值可以改变而不改变观测 law。

## 原理 264.1

positivity 不只是数值估计的技术条件，而是：

\[
\boxed{
\text{目标干预画像是否落在已观察机制 image 内}
}
\]

的可实现性条件。

---

# 265. 隐混杂使条件化与干预分离

令：

\[
U\sim\operatorname{Bernoulli}(1/2),
\]

并定义：

\[
X=U,
\qquad
Y=U.
\]

## 定理 265.1（完美观测相关）

\[
P(Y=1\mid X=1)=1,
\qquad
P(Y=1\mid X=0)=0.
\]

## 定理 265.2（零因果效应）

干预 \(X\) 不修改 \(Y=U\) 的机制，所以：

\[
P(Y=1\mid do(X=1))
=
P(Y=1\mid do(X=0))
=
\frac12.
\]

因此平均因果效应为零。

## 定义 265.1（混杂余量）

\[
\operatorname{ConfRes}(X,Y)
=
P(Y\mid X)
-
P(Y\mid do(X)),
\]

这里的减号表示两个 kernel 的差异，而不是默认其有单一标量范数。

## 原理 265.1

\[
\boxed{
\text{conditioning selects units;}
\qquad
\text{intervention replaces a mechanism.}
}
\]

两者只有在额外可交换前件下才相同。

---

# 266. 模块机制与因子替换

在 Markovian DAG 模型中，观测 law 写作：

\[
P(x_V)
=
\prod_{v\in V}
K_v(x_v\mid x_{\operatorname{pa}(v)}).
\]

## 定义 266.1（机制模块）

每个：

\[
K_v:
\mathcal X_{\operatorname{pa}(v)}
\rightsquigarrow
\mathcal X_v
\]

是一个局部生成机制。

## 定义 266.2（软干预）

软干预不把 \(X_i\) 固定为常值，而是将：

\[
K_i
\]

替换为另一个 kernel：

\[
\widetilde K_i.
\]

其他机制保持不变。

## 定理 266.1（局部替换公式）

若干预确实只替换 \(I\) 中机制，则新 joint law 为：

\[
\boxed{
P^{\widetilde K_I}(x_V)
=
\prod_{i\in I}
\widetilde K_i(x_i\mid x_{\operatorname{pa}(i)})
\prod_{v\notin I}
K_v(x_v\mid x_{\operatorname{pa}(v)}).
}
\]

## 原理 266.1（模块性是承重前件）

干预分析依赖“未被干预机制保持不变”。若一个装置改变 \(X_i\) 的同时也改变其他机制、测量装置或外生分布，则不能继续使用同一截断模型而不记录该联动。

---

# 267. 干预自然性与因果 carry

设微观模型状态为 \(M\)，粗接口为：

\[
q:\mathfrak M\to O.
\]

干预操作为：

\[
I_a:\mathfrak M\to\mathfrak M.
\]

## 定义 267.1（干预自然性）

若存在：

\[
\bar I_a:O\to O
\]

使：

\[
\boxed{
q\circ I_a
=
\bar I_a\circ q,
}
\]

则称干预 \(a\) 在粗接口 \(q\) 上下降。

## 定义 267.2（因果 carry）

\[
\boxed{
\operatorname{CausalCarry}(I_a,q)
=
\sum_{M,N}
(q(M)=q(N))
\times
(q(I_aM)\neq q(I_aN)).
}
\]

## 定理 267.1（carry 空当且仅当有效像上可下降）

在有效像上：

\[
\operatorname{CausalCarry}(I_a,q)=\varnothing
\]

当且仅当存在唯一：

\[
\bar I_a:\operatorname{Im}(q)\to\operatorname{Im}(q)
\]

使交换图成立。

## 原理 267.1

一个观测商可以对被动预测充分，却对主动干预不封闭。要获得因果状态，必须把所有允许干预后的响应一并纳入完成。

---

# 268. 素数索引的机制族

令变量或模块由素数索引：

\[
(X_p)_{p\in\mathbb P}.
\]

每个局部机制写作：

\[
K_p:
X_{\operatorname{pa}(p)}
\rightsquigarrow
X_p.
\]

## 定义 268.1（素数机制干预）

\[
do_p(\widetilde K_p)
\]

只替换第 \(p\) 个机制，前提是模型已明确给出这种模块边界。

## 定义 268.2（素数因果画像）

\[
\operatorname{PCausal}(M)
=
\left(
P_M^{do_p(\widetilde K)}
\right)_{p,\widetilde K}.
\]

## 原理 268.1（索引不制造模块性）

\[
\boxed{
p\neq q
\not\Rightarrow
K_p\text{ 与 }K_q\text{ 因果独立}.
}
\]

不同素数模块仍可能：

- 共享外生噪声；
- 存在有向边；
- 受同一环境变量影响；
- 被同一实验装置同时扰动；
- 只是在地址上不同而机制上耦合。

## 原理 268.2

prime-indexing 的价值在于提供清晰的实验目录与局部坐标；因果分解仍需由图、外生独立、模块替换和验证交换图证明。

---

# 269. 独立乘积 SCM 的干预分解

设状态分成有限个块：

\[
V
=
\bigsqcup_{i\in I}V_i.
\]

假设：

1. 不存在跨块有向边；
2. 外生变量按块独立；
3. 干预逐块替换机制；
4. 准入条件不含跨块约束。

## 定理 269.1（观测 law 乘积分解）

\[
\boxed{
P_M(X_V)
=
\bigotimes_{i\in I}
P_{M_i}(X_{V_i}).
}
\]

## 定理 269.2（干预 law 乘积分解）

对逐块干预 \(a=(a_i)_i\)：

\[
\boxed{
P_M^a
=
\bigotimes_{i\in I}
P_{M_i}^{a_i}.
}
\]

## 定理 269.3（因果等价逐块化）

若允许干预族本身为块乘积，则：

\[
M\sim_{\mathrm{int}}N
\iff
\forall i,
\quad
M_i\sim_{\mathrm{int}}N_i.
\]

因此因果商在这些前件下分解为局部因果商的有限乘积。

## 边界 269.1

任何共享外生变量、跨块边、全局守恒约束或联合干预副作用都会破坏上述自由乘积结论。

---

# 270. 跨素数混杂破坏乘积

取两个不同索引 \(p\neq q\)，令：

\[
U\sim\operatorname{Bernoulli}(1/2),
\]

\[
X_p=U,
\qquad
X_q=U.
\]

图中可以没有 \(X_p\to X_q\) 或 \(X_q\to X_p\) 的有向边，但二者共享外生源。

## 定理 270.1（观测不独立）

\[
P(X_p=X_q)=1,
\]

而：

\[
P(X_p=1)P(X_q=1)=\frac14
\neq
P(X_p=1,X_q=1)=\frac12.
\]

## 定理 270.2（局部干预暴露共享来源）

在：

\[
do(X_p=x)
\]

下：

\[
X_q=U
\]

仍为均匀 Bernoulli，并不跟随被固定的 \(X_p\)。

## 原理 270.1

\[
\boxed{
\text{没有直接边}
\neq
\text{独立};
\qquad
\text{地址互素}
\neq
\text{外生来源互素}.
}
\]

CRT 或张量地址分解不能消除共享噪声造成的因果相关。

---

# 271. 环境索引与机制不变量

令环境为：

\[
e\in\mathcal E.
\]

每个环境有 joint law：

\[
P_e(x_V)
=
\prod_{v\in V}
K_{v,e}(x_v\mid x_{\operatorname{pa}(v)}).
\]

## 定义 271.1（稳定机制集）

\[
S
=
\left\{
v:
K_{v,e}=K_{v,e'}
\quad
\forall e,e'
\right\}.
\]

## 定义 271.2（环境画像）

\[
\operatorname{EnvProf}(M)
=
\bigl(
P_{M,e}^{a}
\bigr)_{e,a}.
\]

## 定义 271.3（机制变化余量）

\[
\operatorname{ShiftRes}(e,e')
=
\left\{
v:
K_{v,e}\neq K_{v,e'}
\right\}.
\]

## 原理 271.1（不变量是机制层命题）

某个条件分布在有限样本中看似稳定，不等于其结构机制真正不变；反之，机制不变也可能因父变量分布变化而导致边缘 law 改变。

## 原理 271.2

跨环境科学推理应区分：

\[
\boxed{
\text{mechanism invariance}
\neq
\text{marginal invariance}
\neq
\text{target-effect invariance}.
}
\]

---

# 272. Transportability 是跨环境目标因子化

设源环境为 \(s\)，目标环境为 \(t\)。可用证据包括：

\[
E(M)
=
\left(
P_{M,s}^{a}
\right)_{a\in\mathcal A_s}
\times
P_{M,t}^{\mathrm{obs}}.
\]

目标为：

\[
T(M)
=
P_{M,t}(Y\mid do(X=x)).
\]

## 定义 272.1（可运输性余量）

\[
\boxed{
\operatorname{TransRes}(E,T)
=
\sum_{M,N}
(E(M)=E(N))
\times
(T(M)\neq T(N)).
}
\]

## 定理 272.1（模型类相对可运输判据）

目标效应可由全部可用源实验和目标观测唯一计算，当且仅当：

\[
\operatorname{TransRes}(E,T)=\varnothing.
\]

等价地：

\[
\ker E\subseteq\ker T.
\]

## 经典桥 272.1

selection diagrams、do-calculus 与 transportability algorithms 提供图形条件和构造公式，用于判定上述 kernel 包含何时由结构假设保证。

## 原理 272.1

\[
\boxed{
\text{源环境中已识别}
\not\Rightarrow
\text{目标环境中可运输}.
}
\]

还必须说明哪些机制保持、哪些机制变化，以及目标 law 如何由可用证据因子化。

---

# Part XXXV：因果发现、干预编码与主动实验设计

# 273. 观测 Markov 等价是方向盲区

对 DAG \(G\)，观测条件独立结构由 d-separation 约束。

## 经典定理 273.1（观测 Markov 等价刻画）

在标准 DAG 语境中，两个 DAG 具有相同的 d-separation 关系，当且仅当它们具有相同 skeleton 与相同 unshielded colliders。

## 定义 273.1（观测等价类）

\[
[G]_{\mathrm{obs}}
=
\left\{
H:
H\text{ 与 }G\text{ Markov equivalent}
\right\}.
\]

## 原理 273.1（faithfulness 边界）

从观测 law 恢复条件独立结构通常还需 faithfulness 或类似排除精确参数抵消的假设。没有该假设，law 可以具有比图结构蕴含更多的偶然独立。

## 实例 273.1

二节点图：

\[
X\to Y
\qquad\text{与}\qquad
X\leftarrow Y
\]

没有可由纯观测条件独立区分的方向差异；第 258 节给出同一 joint law 的显式 SCM 实现。

---

# 274. 干预 Markov 等价严格精化观测类

给定 intervention target family：

\[
\mathcal I
=
\{I_1,\ldots,I_m\}.
\]

## 定义 274.1（干预 Markov 等价）

两个 DAG 在观测与全部指定 intervention regimes 下诱导同一 Markov 结构时，称其 \(\mathcal I\)-Markov equivalent。

## 经典定理 274.1（精化）

在标准 perfect-intervention 前件下：

\[
\boxed{
[G]_{\mathcal I}
\subseteq
[G]_{\mathrm{obs}}.
}
\]

额外干预一般把观测 equivalence class 切分为更细的 interventional equivalence classes。

## 原理 274.1

干预之所以能够定向，不是因为它产生了“更多相关性”，而是因为它选择性删除或替换入边机制，使不同方向模型在 post-intervention law 上失去观测等价。

## 边界 274.1

若干预 target 未知、干预不完美、多个机制被联动改变、隐藏变量结构未建模，标准 interventional essential graph 结论不能直接套用。

---

# 275. 最小干预完成仍是覆盖问题

令有限候选 DAG／SCM 类为：

\[
\mathcal M
=
\{M_1,\ldots,M_N\}.
\]

对每个候选干预 \(a\)，定义：

\[
D_a
=
\left\{
\{i,j\}:
P_{M_i}^a\neq P_{M_j}^a
\right\}.
\]

## 定理 275.1（完整模型识别覆盖）

干预集合 \(J\) 使模型画像单射，当且仅当：

\[
\boxed{
\bigcup_{a\in J}D_a
=
\binom{[N]}2.
}
\]

## 推论 275.1（目标相对版本）

若只需识别目标 \(T(M)\)，则 universe 缩小为：

\[
\left\{
\{i,j\}:
T(M_i)\neq T(M_j)
\right\}.
\]

## 原理 275.1（graph orientation 与 effect identification 可分离）

一个实验可能不能完全恢复 DAG，却已经足够识别目标效应；另一个实验可能显著缩小图类，却只区分与当前目标无关的边。

---

# 276. 干预画像码与错误距离

在理想 law oracle 下，对有限干预集：

\[
J=\{a_1,\ldots,a_m\},
\]

定义模型码字：

\[
C_J(M)
=
\bigl(
P_M^{a_1},
\ldots,
P_M^{a_m}
\bigr).
\]

定义 law-coordinate Hamming 距离：

\[
d_J(M,N)
=
\left|
\left\{
r:
P_M^{a_r}\neq P_N^{a_r}
\right\}
\right|.
\]

## 定义 276.1（最小干预距离）

\[
\boxed{
d_{\min}(J)
=
\min_{M\neq N}
d_J(M,N).
}
\]

## 定理 276.1（oracle 错误检测）

若至多 \(e\) 个干预 law 坐标被任意伪造，且：

\[
2e<d_{\min}(J),
\]

则真实模型码字仍是唯一 Hamming 距离不超过 \(e\) 的候选。

## 边界 276.1

真实实验只提供有限样本，不提供精确 law 坐标。此时必须把 Hamming oracle 模型替换为 TV、Hellinger、KL、置信集或复合检验；不能把 sampling error 当作一个离散坐标翻转。

## 原理 276.1

语义秩和实验冗余再次分离：

\[
\boxed{
\text{缩小模型 kernel}
\neq
\text{提高报告错误距离}.
}
\]

---

# 277. 三模型因果自适应反模型

考虑三个抽象因果模型：

\[
M_0:\text{无 }X\leftrightarrow Y\text{ 作用},
\]

\[
M_{XY}:X\to Y,
\]

\[
M_{YX}:Y\to X.
\]

定义两个理想变化检测实验：

\[
E_X
=
\text{“干预 }X\text{ 是否改变 }Y\text{ law”},
\]

\[
E_Y
=
\text{“干预 }Y\text{ 是否改变 }X\text{ law”}.
\]

其确定签名为：

\[
\begin{array}{c|cc}
M&E_X&E_Y\\
\hline
M_0&0&0\\
M_{XY}&1&0\\
M_{YX}&0&1
\end{array}
\]

## 定理 277.1（静态精确设计）

任意单个实验都合并两个模型，因此静态零错误识别必须读取：

\[
\{E_X,E_Y\}.
\]

## 定理 277.2（自适应提前停止）

先执行 \(E_X\)：

- 若输出 \(1\)，立即判定 \(M_{XY}\)；
- 若输出 \(0\)，再执行 \(E_Y\)，区分 \(M_0,M_{YX}\)。

若先验：

\[
P(M_{XY})=1-\varepsilon,
\]

则期望实验数为：

\[
\boxed{
1+\varepsilon<2.
}
\]

## 原理 277.1

主动因果发现的平均优势来自根据干预响应提前终止；它不改变 worst-case 深度，也不凭空增加单个实验的分辨率。

---

# 278. 因果模型 belief 是主动发现的状态

令候选 SCM 集有限：

\[
\mathcal M.
\]

历史包含已执行干预与输出：

\[
h_t=(a_0,y_0,\ldots,a_{t-1},y_{t-1}).
\]

## 定义 278.1（因果 belief）

\[
\boxed{
\pi_t(M)
=
P(M\mid h_t).
}
\]

## 定理 278.1（posterior sufficiency）

若未来实验输出只通过真实模型 \(M\) 和所选干预决定，则给定 \(\pi_t\) 后，历史的其余细节对全部未来实验预测和 Bayes 决策无额外作用。

## 定义 278.2（目标 posterior）

若只关心目标 \(T(M)\)，可推前：

\[
\tau_t
=
T_*\pi_t.
\]

## 边界 278.1

\(\tau_t\) 未必足以规划未来实验，因为不同模型即使当前目标相同，也可能对未来干预产生不同 law，从而影响后续学习价值。规划状态一般需要保留完整未来实验预测所需的 causal belief quotient。

---

# 279. 因果干预 Bellman 方程

在 belief \(\pi\) 上，停止并输出行动的 Bayes 风险为：

\[
G(\pi).
\]

执行干预 \(a\) 的成本为：

\[
c_a.
\]

预测输出 law：

\[
M_a^\pi(dy)
=
\sum_{M\in\mathcal M}
\pi(M)P_M^a(dy).
\]

后验更新为：

\[
\mathsf B_a(\pi,y).
\]

## 定义 279.1（因果实验 Bellman operator）

\[
\boxed{
(\mathcal TV)(\pi)
=
\min
\left\{
G(\pi),
\inf_a
\left[
c_a
+
\gamma
\int
V(\mathsf B_a(\pi,y))
M_a^\pi(dy)
\right]
\right\}.
}
\]

## 定理 279.1（折扣收缩）

对有界 \(V,W\)：

\[
\boxed{
\|\mathcal TV-\mathcal TW\|_\infty
\le
\gamma
\|V-W\|_\infty.
}
\]

所以 \(0<\gamma<1\) 时存在唯一固定点。

## 仓库桥 279.1

这复用 v1.4 belief Bellman 的同一收缩结构；新增之处只是隐藏状态由普通状态提升为 SCM／因果类，动作由一般观察实验专门化为机制干预。

---

# 280. 模型信息不等于目标因果价值

令实验输出为 \(Y_a\)，模型为 \(M\)，目标为：

\[
\Theta=T(M).
\]

数据处理给出：

\[
\boxed{
I(\Theta;Y_a)
\le
I(M;Y_a).
}
\]

## 定义 280.1（模型信息增益）

\[
\operatorname{MIG}(a)
=
I(M;Y_a).
\]

## 定义 280.2（目标信息增益）

\[
\operatorname{TIG}(a)
=
I(T(M);Y_a).
\]

## 反模型机制 280.1

若实验只区分两个目标值相同的机制细节，则：

\[
\operatorname{MIG}(a)>0,
\qquad
\operatorname{TIG}(a)=0.
\]

## 原理 280.1

最大化模型互信息可能把预算用于无关结构发现。目标相对因果设计应优化：

\[
\operatorname{VoI}_T(a)
\]

或目标 Bayes risk reduction，而不是默认完整模型 entropy reduction。

---

# 281. Identifiability、estimability 与 computation 三分

## 定义 281.1（可识别）

目标 \(T\) 对证据接口 \(E\) 可识别，若：

\[
\ker E\subseteq\ker T.
\]

这是无限精确 law 层的语义命题。

## 定义 281.2（可估计）

存在基于有限样本的估计量：

\[
\widehat T_n
\]

在指定统计模型和损失下具有一致性、有限风险或置信保证。

## 定义 281.3（可计算）

识别公式或估计器可在可接受资源中求值。

## 原理 281.1

\[
\boxed{
\text{identifiable}
\not\Rightarrow
\text{finite-sample accurate}
\not\Rightarrow
\text{computationally tractable}.
}
\]

反向也不成立：一个算法可以对某个参数化子类工作，却不证明非参数模型类中的目标可识别。

## 原理 281.2

形式化路线应分别登记：

```text
semantic kernel theorem
identification formula
sampling theorem
algorithm
complexity bound
```

不得用其中任一层替代其他层。

---

# 282. 干预 image 与模型可证伪性

给定模型类 \(\mathfrak M_0\) 和干预族 \(\mathcal A\)，其可实现画像为：

\[
\operatorname{Im}
\left(
\Lambda_{\mathcal A}^{\mathrm{int}}
\mid_{\mathfrak M_0}
\right).
\]

## 定义 282.1（干预 image defect）

观测到的 law family \(L=(L_a)_a\) 的缺陷为：

\[
\boxed{
\operatorname{ImageDefect}(L)
=
\left[
L
\notin
\operatorname{Im}
\left(
\Lambda_{\mathcal A}^{\mathrm{int}}
\mid_{\mathfrak M_0}
\right)
\right].
}
\]

## 定理 282.1（精确 law 层的证伪）

若 `ImageDefect` 成立，则不存在 \(\mathfrak M_0\) 中任何模型同时解释全部干预 regimes。

## 边界 282.1

有限样本下无法直接观察精确 law 是否在 image 中；需要 goodness-of-fit、置信区域、容差 metric 或 Bayesian posterior predictive checking。

## 原理 282.1

因果推理不仅有 kernel 问题：

\[
\text{哪些模型无法区分},
\]

还有 image 问题：

\[
\text{哪些跨干预 law 族根本不由该模型类实现}.
\]

---

# Part XXXVI：反事实 coupling、个体效应与跨世界余量

# 283. 反事实使用同一外生状态

在 SCM \(M\) 中，给定同一外生状态：

\[
u,
\]

对不同干预分别求值：

\[
Y_x(u),
\qquad
Y_{x'}(u).
\]

## 定义 283.1（潜在结果向量）

\[
\boxed{
\mathbf Y(u)
=
(Y_x(u))_{x\in\mathcal X}.
}
\]

## 定义 283.2（反事实 law）

\[
\mathcal L_M(\mathbf Y)
\]

是由同一个 \(U\sim P_U\) 推前得到的联合 law。

## 原理 283.1（同单位 ledger）

反事实的承重结构不是各 \(Y_x\) 的边缘 law，而是它们通过同一个外生 \(u\) 的耦合。

\[
\boxed{
\left(
\mathcal L(Y_x)
\right)_x
\quad
\text{不决定}
\quad
\mathcal L((Y_x)_x).
}
\]

## 原理 283.2

对不同单位分别执行不同处理，可以估计潜在结果边缘；但同一单位不能同时显现互相冲突的处理结果。跨世界联合需要结构假设、界或额外设计，而不是更多独立单位自动给出。

---

# 284. Cross-world coupling 是新的余量层

给定干预边缘族：

\[
\mu_x
=
\mathcal L(Y_x).
\]

定义所有具有这些边缘的 coupling 集：

\[
\boxed{
\Gamma((\mu_x)_x)
=
\left\{
\gamma:
\operatorname{marg}_x\gamma=\mu_x
\quad\forall x
\right\}.
}
\]

## 定义 284.1（cross-world residual）

\[
\operatorname{CWRes}
((\mu_x)_x,Q)
=
\left\{
\gamma,\gamma'\in\Gamma:
Q(\gamma)\neq Q(\gamma')
\right\}.
\]

## 定理 284.1（反事实可识别判据）

反事实目标 \(Q\) 可由全部单世界干预边缘决定，当且仅当 \(Q\) 在 coupling fiber：

\[
\Gamma((\mu_x)_x)
\]

上为常值。

## 原理 284.1

这是因果 hierarchy 的 image-fiber 版本：

\[
\boxed{
\text{interventional marginals}
\to
\text{coupling fiber}
\to
\text{counterfactual target}.
}
\]

干预层已经完全识别时，反事实层仍可能留下非平凡 fiber。

---

# 285. 全部单世界干预仍不决定反事实联合

令：

\[
X\sim\operatorname{Bernoulli}(1/2),
\qquad
U\sim\operatorname{Bernoulli}(1/2),
\qquad
X\perp U.
\]

构造两个 SCM。

## 模型 285.S（稳定耦合）

\[
Y=U.
\]

所以：

\[
Y_0=U,
\qquad
Y_1=U.
\]

## 模型 285.F（翻转耦合）

\[
Y=U\oplus X.
\]

所以：

\[
Y_0=U,
\qquad
Y_1=1-U.
\]

## 定理 285.1（观测 law 相同）

在两个模型中，\(X,Y\) 都是相互独立的均匀 Bernoulli，因此：

\[
P(X=x,Y=y)=\frac14
\]

对全部 \(x,y\) 成立。

## 定理 285.2（全部单世界 \(X\)-干预 law 相同）

对任意 \(x\in\{0,1\}\)：

\[
Y_x
\sim
\operatorname{Bernoulli}(1/2)
\]

在两个模型中都成立。

对 \(Y\) 的完美干预也只固定 \(Y\)，而 \(X\) 保持均匀，故两模型在所有单世界完美干预下具有同一内生 joint law。

## 定理 285.3（反事实联合相反）

稳定模型：

\[
P(Y_0=Y_1)=1.
\]

翻转模型：

\[
P(Y_0\neq Y_1)=1.
\]

因此：

\[
\boxed{
M_S
\sim_{\mathrm{int}}
M_F,
\qquad
M_S
\not\sim_{\mathrm{cf}}
M_F.
}
\]

## 推论 285.1（第二层严格性）

\[
\boxed{
\ker(\operatorname{CF})
\subsetneq
\ker(\operatorname{Int})
}
\]

在二元无混杂、已知处理随机化的模型中已经严格。

---

# 286. 因果层级严格性定理

结合第 258 节与第 285 节，得到两个显式 witness pair。

## 定理 286.1（观测层严格弱于干预层）

存在 \(M,N\) 使：

\[
\operatorname{Obs}(M)=\operatorname{Obs}(N),
\]

但：

\[
\operatorname{Int}(M)\neq\operatorname{Int}(N).
\]

## 定理 286.2（干预层严格弱于反事实层）

存在 \(M,N\) 使：

\[
\operatorname{Int}(M)=\operatorname{Int}(N),
\]

但：

\[
\operatorname{CF}(M)\neq\operatorname{CF}(N).
\]

## 推论 286.1（严格层级）

在包含上述模型的有限 SCM 类中：

\[
\boxed{
Z_{\mathrm{obs}}
\prec
Z_{\mathrm{int}}
\prec
Z_{\mathrm{cf}}.
}
\]

这里 \(\prec\) 表示后者严格精化前者的有效查询商，不表示三种原始表示类型之间存在未经 transport 的集合包含。

## 最深解释 286.1

\[
\boxed{
\text{看见更多同一世界}
\text{不能替代做；}
\qquad
\text{做更多单世界实验}
\text{不能替代跨世界 coupling。}
}
\]

---

# 287. 平均效应可识别而个体效应 law 不可识别

对二元处理与二元结果，定义：

\[
p_0=P(Y_0=1),
\qquad
p_1=P(Y_1=1).
\]

随机实验可以识别 \(p_0,p_1\)。

## 定义 287.1（平均处理效应）

\[
\boxed{
\operatorname{ATE}
=
E[Y_1-Y_0]
=
p_1-p_0.
}
\]

## 定义 287.2（个体效应）

\[
\Delta
=
Y_1-Y_0
\in\{-1,0,1\}.
\]

## 定理 287.1（ATE 只依赖边缘）

\[
E[Y_1-Y_0]
=
E[Y_1]-E[Y_0]
\]

不需要知道 \((Y_0,Y_1)\) 的 coupling。

## 定理 287.2（个体效应分布依赖 coupling）

\[
P(\Delta=1)
=
P(Y_0=0,Y_1=1),
\]

\[
P(\Delta=-1)
=
P(Y_0=1,Y_1=0).
\]

二者不由 \(p_0,p_1\) 单独决定。

## 实例 287.1

第 285 节中两个模型都有：

\[
p_0=p_1=\frac12,
\qquad
ATE=0.
\]

但稳定模型中：

\[
P(\Delta=0)=1,
\]

翻转模型中：

\[
P(\Delta=1)=P(\Delta=-1)=\frac12.
\]

---

# 288. 受益与受损概率的尖锐 Fréchet 界

定义：

\[
b
=
P(Y_0=0,Y_1=1),
\]

\[
h
=
P(Y_0=1,Y_1=0).
\]

## 定理 288.1（受益概率界）

\[
\boxed{
\max\{0,p_1-p_0\}
\le
b
\le
\min\{p_1,1-p_0\}.
}
\]

## 定理 288.2（受损概率界）

\[
\boxed{
\max\{0,p_0-p_1\}
\le
h
\le
\min\{p_0,1-p_1\}.
}
\]

## 定理 288.3（净效应恒等式）

\[
\boxed{
b-h
=
p_1-p_0
=
ATE.
}
\]

### 证明

令：

\[
r=P(Y_0=1,Y_1=1).
\]

则：

\[
b=p_1-r,
\qquad
h=p_0-r.
\]

合法 joint table 要求：

\[
\max\{0,p_0+p_1-1\}
\le r\le
\min\{p_0,p_1\}.
\]

代入即得全部界；取端点 coupling 可达到界，因此尖锐。 \(\square\)

## 原理 288.1

部分识别不是证明失败，而是对 cross-world fiber 的完整几何描述：目标在该 fiber 上的最小值和最大值就是可证的全部信息。

---

# 289. Monotonicity 关闭一个 cross-world 方向

## 假设 289.1（无伤害单调性）

\[
Y_1\ge Y_0
\quad\text{a.s.}
\]

等价于：

\[
h=P(Y_0=1,Y_1=0)=0.
\]

## 定理 289.1（受益概率点识别）

在 monotonicity 下：

\[
\boxed{
b
=
p_1-p_0.
}
\]

## 定理 289.2（principal strata）

四个潜在类型缩减为三个：

\[
\begin{array}{c|c|c}
\text{类型}&Y_0&Y_1\\
\hline
\text{never}&0&0\\
\text{benefit}&0&1\\
\text{always}&1&1
\end{array}
\]

其概率分别为：

\[
1-p_1,
\qquad
p_1-p_0,
\qquad
p_0.
\]

## 原理 289.1

monotonicity 不是由随机化自动产生的统计事实；它是删除一类 coupling 的结构假设。它的作用应记录为：

\[
\boxed{
\text{缩小 counterfactual image fiber}.
}
\]

---

# 290. 归因概率属于反事实层

## 定义 290.1（必要且充分概率）

\[
\boxed{
PNS
=
P(Y_1=1,Y_0=0).
}
\]

它正是第 288 节的 \(b\)。

## 定义 290.2（必要性概率）

在一致性与适当可定义前件下：

\[
PN
=
P(Y_0=0\mid X=1,Y=1).
\]

## 定义 290.3（充分性概率）

\[
PS
=
P(Y_1=1\mid X=0,Y=0).
\]

## 原理 290.1（群体效应与个案归因分离）

\[
P(Y=1\mid do(X=1))
-
P(Y=1\mid do(X=0))
\]

是群体边缘差；\(PN,PS,PNS\) 询问同一单位在未发生处理下会怎样，属于 cross-world 查询。

## 原理 290.2

即使随机实验完全识别所有单处理 interventional marginals，归因概率通常仍只有界；额外观测数据、monotonicity、结构图或机制限制可以缩小这些界，但必须显式登记。

---

# 291. 反事实目标商

给定反事实查询族：

\[
\mathcal Q
=
\{Q_j\}_{j\in J}.
\]

定义：

\[
\Lambda_{\mathcal Q}^{\mathrm{cf}}:
\mathfrak M
\to
\prod_{j\in J}
\mathcal P(\operatorname{Val}(Q_j)).
\]

## 定义 291.1（反事实商）

\[
\boxed{
Z_{\mathcal Q}^{\mathrm{cf}}
=
\operatorname{Im}
\left(
\Lambda_{\mathcal Q}^{\mathrm{cf}}
\right).
}
\]

## 定理 291.1（目标最小充分性）

任意目标族 \(T_k\) 若均在 \(\mathcal Q\)-画像纤维上常值，则它们共同唯一因子化通过：

\[
Z_{\mathcal Q}^{\mathrm{cf}}.
\]

## 定义 291.2（反事实身份余量）

\[
\operatorname{CFRes}(\mathcal Q)
=
\sum_{M,N}
(M\neq N)
\times
\left(
\Lambda_{\mathcal Q}^{\mathrm{cf}}(M)
=
\Lambda_{\mathcal Q}^{\mathrm{cf}}(N)
\right).
\]

## 原理 291.1

即使进入反事实层，也必须指定查询族。知道 \((Y_0,Y_1)\) 的 joint law 不一定恢复全部中介嵌套反事实、外生参数化或其他变量的 cross-world joint。

---

# 292. Abduction–action–prediction 三步

对事实证据：

\[
E=e,
\]

反事实查询：

\[
Y_x,
\]

SCM 语义分三步。

## 第一步：abduction

由观测证据更新外生状态：

\[
P_U
\longmapsto
P_U(\cdot\mid E=e).
\]

## 第二步：action

把结构方程修改为：

\[
do(X=x).
\]

## 第三步：prediction

在更新后的同一外生 posterior 下求值：

\[
Y_x(U).
\]

## 公式 292.1

\[
\boxed{
P(Y_x=y\mid E=e)
=
\int
\mathbf 1\{Y_x(u)=y\}
\,P_U(du\mid E=e).
}
\]

## 原理 292.1（事实证据作用在外生 ledger）

事实证据不是在干预后世界重新采样一个独立 \(U'\)；它约束的是生成事实世界的同一个外生状态，然后该状态被带入修改后的方程。

## 原理 292.2

若模型只指定每个 intervention world 的边缘 law，却未指定共享外生 coupling，则 abduction 后的个体反事实一般无定义或不唯一。

---

# 293. Consistency、effectiveness 与 composition

SCM 反事实满足一组结构恒等式。

## 定理 293.1（effectiveness）

在干预：

\[
do(X=x)
\]

下：

\[
\boxed{
X_x=x.
}
\]

## 定理 293.2（consistency）

若事实世界中：

\[
X=x,
\]

则：

\[
\boxed{
Y=Y_x.
}
\]

## 定理 293.3（composition）

若：

\[
W_x=w,
\]

则在标准 recursive SCM 中：

\[
\boxed{
Y_{x,w}=Y_x.
}
\]

## 原理 293.1（结构恒等式不是数据检验的普通相关关系）

这些等式来自“同一机制被替换后如何求值”的定义。它们约束可实现 counterfactual image，但不由任意潜在变量 joint law 自动满足。

## 边界 293.1

不同反事实形式体系对 consistency、composition、cross-world independence 的公理化强度可能不同。形式化时必须选择明确 SCM 语义，而不能混用相互不等价的潜在结果公理包。

---

# 294. 嵌套反事实要求更高层 coupling

中介 \(M\) 下的自然直接效应涉及：

\[
Y_{x,M_{x'}}.
\]

该表达同时调用：

- \(x'\) 世界中的中介；
- \(x\) 世界中的结果机制；
- 两个世界共享的外生状态。

## 定义 294.1（嵌套查询）

\[
Q_{\mathrm{NDE}}
=
Y_{x,M_{x'}}.
\]

## 原理 294.1（单世界实验不足）

知道所有：

\[
P(Y,M\mid do(X=x))
\]

并不无条件决定：

\[
P(Y_{x,M_{x'}}).
\]

还需图形结构、跨世界独立或可由完整 counterfactual identification 算法验证的条件。

## 经典桥 294.1

完整 causal hierarchy identification 理论区分：

\[
\text{observational identification},
\quad
\text{interventional identification},
\quad
\text{counterfactual identification},
\]

并给出某些查询从较低层可计算的图形条件与算法。

## 严格边界 294.1

本文不把自然直接／间接效应的任何常用公式无条件安装为定理；每个公式必须携带其 cross-world、sequential ignorability 或 graphical identification 前件。

---

# 295. 反事实运输需要 coupling 不变量

源环境与目标环境可能具有相同 interventional marginals：

\[
P_s(Y_x)
=
P_t(Y_x)
\quad\forall x,
\]

但具有不同 cross-world coupling：

\[
P_s(Y_0,Y_1)
\neq
P_t(Y_0,Y_1).
\]

## 定义 295.1（反事实 transport residual）

\[
\operatorname{CFTransRes}
=
\sum_{M_s,M_t,N_s,N_t}
\left[
E(M_s,M_t)=E(N_s,N_t)
\right]
\times
\left[
Q(M_t)\neq Q(N_t)
\right],
\]

其中证据 \(E\) 可以包含源／目标观测和单世界实验，\(Q\) 是目标环境反事实查询。

## 定理 295.1（边缘运输不推出 coupling 运输）

第 285 节稳定／翻转模型可分别放置于两个环境，使全部单世界边缘相同而：

\[
P(Y_0=Y_1)
\]

不同。

## 原理 295.1

\[
\boxed{
\text{transporting every treatment arm marginal}
\not\Rightarrow
\text{transporting individual response type}.
}
\]

反事实运输必须说明外生 coupling、机制同一或足以识别该 coupling 的额外结构为何跨环境保持。

---

# Part XXXVII：时间化因果系统、政策干预与支持边界

# 296. 纵向结构因果模型

令时间为：

\[
t=0,\ldots,T.
\]

在每个时刻观测协变量 \(L_t\)，选择行动 \(A_t\)，得到后续状态。

结构可写作：

\[
L_{t+1}
=
f_t(L_{\le t},A_{\le t},U_{t+1}).
\]

## 定义 296.1（动态政策）

\[
\pi_t:
H_t
\rightsquigarrow
A_t,
\]

其中历史：

\[
H_t=(L_0,A_0,\ldots,L_t).
\]

## 定义 296.2（政策干预）

\[
do(A_t\sim\pi_t(\cdot\mid H_t))
\]

替换原行为分配机制，而保留状态转移机制。

## 定义 296.3（政策结果）

\[
Y^\pi
\]

表示整个行动序列由 \(\pi\) 生成时的最终结果。

## 原理 296.1

一次静态 \(do(X=x)\) 只是动态政策的长度一特例。长期因果效应需要同时记录反馈：过去行动改变未来协变量，而未来行动又依赖这些协变量。

---

# 297. Sequential g-formula

在离散有限情形，假设：

1. consistency；
2. sequential exchangeability；
3. positivity；
4. 正确记录全部影响行为与未来结果的历史。

## 经典定理 297.1（随机政策 g-formula）

政策 \(\pi\) 下的轨迹 law 为：

\[
\boxed{
P^\pi(l_{0:T},a_{0:T-1})
=
P(l_0)
\prod_{t=0}^{T-1}
\pi_t(a_t\mid h_t)
P(l_{t+1}\mid h_t,a_t).
}
\]

最终目标由该 joint law 边缘化得到：

\[
P(Y^\pi).
\]

## 原理 297.1（时间胶合）

每个转移条件 law：

\[
P(l_{t+1}\mid h_t,a_t)
\]

是局部时间接口；g-formula 在政策替换后沿历史树胶合这些接口。

## 边界 297.1

若存在未记录的 time-varying confounder、测量误差、干预副作用或 positivity 失败，则该乘积不是目标 policy law 的无条件表达式。

---

# 298. Policy positivity 是路径 image 条件

行为政策记为：

\[
\mu_t(a\mid h).
\]

目标政策为：

\[
\pi_t(a\mid h).
\]

## 定义 298.1（路径 positivity）

对所有在目标政策下可达且具有正概率的历史—行动对，要求：

\[
\boxed{
\pi_t(a\mid h)>0
\Longrightarrow
\mu_t(a\mid h)>0.
}
\]

## 定理 298.1（支持缺失盲区）

若存在目标可达 \((h,a)\) 满足：

\[
\mu_t(a\mid h)=0,
\]

则行为数据不约束该分支后的转移机制。可构造两个模型在全部行为支持上相同，却对 \(Y^\pi\) 给出不同 law。

## 原理 298.1

动态 positivity 不是每个单时刻边缘都有处理样本就足够；它要求目标政策访问的整条历史路径落在行为数据支持内。

---

# 299. Off-policy 因果余量

给定行为数据接口：

\[
E_\mu(M)
=
\mathcal L_M(H_T\text{ under }\mu),
\]

目标：

\[
T_\pi(M)
=
\mathcal L_M(Y^\pi).
\]

## 定义 299.1（off-policy residual）

\[
\boxed{
\operatorname{OPRes}(\mu,\pi)
=
\sum_{M,N}
(E_\mu(M)=E_\mu(N))
\times
(T_\pi(M)\neq T_\pi(N)).
}
\]

## 定理 299.1（可评估判据）

目标政策可由行为 law 在模型类中识别，当且仅当：

\[
\operatorname{OPRes}(\mu,\pi)=\varnothing.
\]

## 原理 299.1

importance weighting、direct modeling、doubly robust estimation等算法都建立在某个识别桥上。若 off-policy residual 非空，改变估计器不能创造行为支持之外的反事实转移。

## 原理 299.2

\[
\boxed{
\text{低方差估计器}
\neq
\text{已识别目标};
\qquad
\text{已识别目标}
\neq
\text{稳定有限样本估计}.
}
\]

---

# 300. 因果完成的 kernel–image–coupling 四联

对因果模型到查询画像的映射，应同时审计四类对象。

## 300.1 Kernel residual

\[
M\neq N,
\qquad
E(M)=E(N).
\]

不同模型被现有观测／干预语言合并。

## 300.2 Image defect

形式 law family \(L\) 是否真正来自某个 SCM：

\[
L\in\operatorname{Im}(E)?
\]

## 300.3 Coupling residual

单世界边缘已确定，但 cross-world joint 仍有多个 coupling：

\[
\Gamma((\mu_x)_x).
\]

## 300.4 Gauge residual

不同外生参数化或机制坐标产生同一全部目标查询；这种表示差异不应冒充可观察因果差异。

## 统一原理 300.1

\[
\boxed{
\begin{aligned}
\text{kernel}
&:\quad
\text{多个模型映为同一证据};\\
\text{image}
&:\quad
\text{哪些证据族可由模型实现};\\
\text{coupling}
&:\quad
\text{单世界边缘如何组成同单位多世界};\\
\text{gauge}
&:\quad
\text{同一查询对象的非规范表示}.
\end{aligned}
}
\]

## 原理 300.2（修复必须对症）

- kernel 非空：加入能横切该 kernel 的新干预；
- image 失败：扩大或修正模型类，而不是继续拟合同一模型；
- coupling 非唯一：加入 cross-world 假设、界或结构；
- gauge 非唯一：取商或选择规范，不把它误报为经验不确定性。

---

# 301. 第六阶段最终命题：因果知识是分层查询商而非单一分布

## 最终层级 301.1

\[
\boxed{
\begin{aligned}
\text{SCM}
&\xrightarrow{\operatorname{Obs}}
Z_{\mathrm{obs}}\\
&\xrightarrow{\text{new interventions}}
Z_{\mathrm{int}}\\
&\xrightarrow{\text{shared exogenous coupling}}
Z_{\mathrm{cf}}\\
&\xrightarrow{\text{task quotient}}
Z_T.
\end{aligned}
}
\]

箭头表示需要额外结构才能从较粗层获得较细层，而不是旧层自动包含新层的全部信息。

## 最终严格性 301.2

第 258 节证明：

\[
\boxed{
\text{同观测 law}
\not\Rightarrow
\text{同干预 law}.
}
\]

第 285 节证明：

\[
\boxed{
\text{同全部单世界干预 law}
\not\Rightarrow
\text{同反事实 joint law}.
}
\]

## 最终设计原则 301.3

\[
\boxed{
\text{只有能缩小目标 kernel、填补合法 image、}
\text{约束 cross-world coupling 或关闭 causal carry 的接口，}
\text{才构成真正的因果观察升级。}
}
\]

## 最深结论 301.4

\[
\boxed{
\text{观察告诉我们世界怎样共现；}
\quad
\text{干预告诉我们机制被替换后怎样响应；}
\quad
\text{反事实告诉我们同一外生历史在未发生世界中怎样展开。}
}
\]

三者共享概率语言，却不共享同一个信息层。把它们压成“更多数据”会隐藏真正的 residual；把它们写成逐层 kernel、image 与 coupling，才允许精确回答下一步究竟缺观测、缺干预、缺支持，还是缺跨世界结构。

---

# Appendix O：v1.5 版本记录与仓库锚点

## O.1 版本记录

- **v1.5 — 2026-08-22**：追加观测／干预／反事实三层查询商、有限 SCM 与完美干预语义、观测等价但干预不等价的二元反模型、干预族精化与目标余量、有限模型干预 set cover、随机化桥、back-door 调整、positivity image 条件、隐藏混杂、机制模块替换、因果 carry、prime-indexed 机制边界、独立乘积 SCM 与跨素数混杂、环境机制不变量、transportability residual、interventional Markov equivalence、干预码距离、主动因果发现、SCM belief Bellman、目标相对实验价值、identifiability／estimability／computation 三分、反事实 coupling fiber、同全部单世界干预但不同 counterfactual joint 的显式模型、ATE 与个体效应分离、Fréchet 尖锐界、monotonicity completion、概率归因、abduction–action–prediction、嵌套反事实、纵向政策、g-formula、off-policy residual 及 kernel–image–coupling–gauge 四联。

## O.2 本阶段仓库真值锚点

1. `D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization.lean`：充分接口唯一因子化到规范 future-law image，并由 law 差异推出接口差异。
2. `D5/S3/ConceptDynamics/Refinement/InductiveSufficiency.lean`：纤维常值与有效像因子化。
3. `D5/S3/ObserverMemory/Prediction/ControlledBehaviorUniversality.lean`：受控行为商的规范最小实现。
4. `D5/S3/Observer/Separation/CongruenceKernel.lean`：过程闭合的最大前向 congruence。
5. `D5/S3/Divergence/ClassicalDPI.lean` 及相关 data-processing 文件：有限随机通道下 divergence 单调桥。
6. `D5/S3/Entropy/MutualInformation.lean`：有限 mutual information 定义与非负性。
7. `D5/S3/Entropy/MutualInformationIndependence.lean`：有限 joint law 中 mutual information 为零当且仅当等于自身边缘乘积。
8. `D5/S3/Entropy/Submodularity/ConditionalMutualInformation.lean` 与 `MutualInformationChainRule.lean`：条件互信息和链式分解接口。
9. `D5/S3/Estimation/DecisionRisk/FixedSuiteBayesRiskFloor.lean`：固定实验套件的 Bayes 风险下界。
10. `D5/S3/Observer/DynamicProgramming/BellmanContraction.lean`：折扣 Bellman operator 的 contraction 与唯一固定点。
11. `D5/S3/TotalVariation/HellingerDataProcessing.lean`：随机后处理不增加有限 Hellinger 区分。
12. `D5/S3/Divergence/ProductAdditivity.lean`：有限正概率 law 的 KL 乘积可加性。

## O.3 锚点边界

上述 Lean 文件不定义完整 SCM、do-operator、DAG d-separation、back-door、do-calculus、potential outcomes、transportability 或 g-formula。本文仅把其已闭合的 kernel-factorization、随机通道、信息与 Bellman 部件作为未来因果模块的底层依赖；不得由文件名中的 `CausalState` 推断 Pearl 式 causal hierarchy 已经形式化。

---

# Appendix P：第六阶段外部经典基础

以下来源只支撑标记为经典的标准背景，不替代未来仓库 proof term：

1. I. Shpitser and J. Pearl, “Complete Identification Methods for the Causal Hierarchy,” *Journal of Machine Learning Research* **9** (2008), 1941–1979：association、intervention、counterfactual 三层及完整识别方法。
2. I. Shpitser and J. Pearl, “Identification of Joint Interventional Distributions in Recursive Semi-Markovian Causal Models,” *AAAI* (2006), 1219–1226：joint interventional identification 与 do-calculus completeness。
3. A. Hauser and P. Bühlmann, “Characterization and Greedy Learning of Interventional Markov Equivalence Classes of Directed Acyclic Graphs,” *JMLR* **13** (2012), 2409–2464：干预 Markov 等价与 interventional essential graph。
4. J. Pearl and E. Bareinboim, “Transportability of Causal and Statistical Relations: A Formal Approach,” *AAAI* (2011), 247–254, DOI `10.1609/AAAI.V25I1.7861`。
5. E. Bareinboim and J. Pearl, “Transportability of Causal Effects: Completeness Results,” *AAAI* (2012), 698–704, DOI `10.1609/AAAI.V26I1.8232`。
6. J. Tian and J. Pearl, “Probabilities of Causation: Bounds and Identification,” *Annals of Mathematics and Artificial Intelligence* **28** (2000), 287–313, DOI `10.1023/A:1018912507879`。
7. J. M. Robins 的 g-computation／纵向因果推断工作：sequential exchangeability、动态处理 regime 与 g-formula 的经典来源。
8. J. Pearl, *Causality: Models, Reasoning, and Inference*, 2nd ed.：SCM、do-operator、back-door、counterfactual semantics 与 causal hierarchy 背景。
9. J. Pearl and D. Mackenzie, *The Book of Why*：seeing／doing／imagining 的非技术层级表述；本文数学陈述以 SCM 与识别文献为准。
10. J. Tian 及后续 discrete-SCM 工作：从观测和实验 law 对 counterfactual distributions 做 sharp／partial identification 的有限多项式方法。

---

# Appendix Q：v1.5 Lean 形式化路线、证明矩阵与有限证书

## Q.1 建议模块树

```text
D5/S3/Observer/Causal/
  Foundation/
    FiniteSCM.lean
    AcyclicEvaluation.lean
    PerfectIntervention.lean
    SoftIntervention.lean
    ObservationalProfile.lean
    InterventionalProfile.lean
    CausalLawQuotient.lean
    TargetCausalResidual.lean
  Countermodels/
    DirectionReversal.lean
    HiddenConfounding.lean
    PositivityFailure.lean
    InterventionalCounterfactualGap.lean
    CrossPrimeConfounder.lean
  Design/
    InterventionCover.lean
    InterventionCodeDistance.lean
    AdaptiveOrientation.lean
    CausalBelief.lean
    CausalBellman.lean
    TargetInformationValue.lean
  Adjustment/
    RandomizationBridge.lean
    FiniteBackdoor.lean
    Positivity.lean
    TruncatedFactorization.lean
  Product/
    IndependentSCMProduct.lean
    ProductInterventionFactorization.lean
    CausalCarry.lean
  Counterfactual/
    PotentialOutcomeVector.lean
    CouplingResidual.lean
    FrechetBenefitBounds.lean
    MonotonicityCompletion.lean
    AbductionActionPrediction.lean
    CounterfactualQuotient.lean
  Longitudinal/
    DynamicPolicy.lean
    SequentialGFormula.lean
    PolicyPositivity.lean
    OffPolicyResidual.lean
  Transport/
    EnvironmentProfile.lean
    MechanismInvariance.lean
    TransportResidual.lean
```

## Q.2 第一优先：纯有限函数与反模型链

1. 定义有限 SCM 的拓扑顺序求值；
2. 定义 perfect intervention 为结构方程替换；
3. `observationalProfile` 与 `interventionalProfile`；
4. `interventional_target_factors_iff`；
5. 第 258 节 direction-reversal 反模型；
6. 第 264 节 positivity 反模型；
7. 第 265 节 hidden-confounding 反模型；
8. 第 285 节 interventional/counterfactual gap 反模型；
9. 第 288 节 \(2\times2\) coupling table 的 Fréchet 尖锐界。

这批只需有限类型、函数、PMF／有限 mass function 与直接枚举，不需要先建设完整图形 do-calculus。

## Q.3 第二优先：商与实验设计链

```lean
theorem interventionalProfile_mono
theorem causalTargetResidual_empty_iff
theorem finite_intervention_cover_iff
theorem finite_intervention_subfamily
theorem causalCarry_empty_iff_descends
theorem adaptive_orientation_expected_cost
```

`InterventionCover` 应复用既有 concept join／sensor cover 模式，但 universe 改为目标值不同的模型对，coordinate equality 改为 interventional law equality。

## Q.4 第三优先：counterfactual coupling 链

先使用显式 response-function 表示：

```lean
structure BinaryResponseType where
  y0 : Bool
  y1 : Bool
```

在其有限概率单纯形上证明：

```lean
theorem ate_eq_p1_sub_p0
theorem benefit_frechet_lower
theorem benefit_frechet_upper
theorem harm_frechet_lower
theorem harm_frechet_upper
theorem benefit_bounds_sharp
theorem monotone_benefit_eq_ate
```

这避免在第一步依赖一般 measurable SCM 的 cross-world API。

## Q.5 第四优先：图形与纵向桥

- DAG、d-separation 与 Markov equivalence 可能需要独立图论基础；
- back-door 与 do-calculus 不得以 axiom 安装；
- finite back-door 可先在显式 factorization algebra 上证明；
- longitudinal g-formula 可先对有限 horizon、有限 histories 与显式 kernel product 证明；
- transportability 与 nested counterfactual identification 应等底层 causal graph API 稳定后再接入。

## Q.6 定理状态矩阵

| 结论 | 当前状态 | 主要依赖 |
|---|---|---|
| 观测／干预／反事实 kernel 层级 | Paper definition + explicit witnesses | finite SCM |
| 观测等价但干预不等价 | Finite paper certificate | two binary models |
| 全单世界干预等价但反事实不同 | Finite paper certificate | shared-\(U\) coupling |
| 因果 law quotient 普适性质 | Paper / direct specialization | `CausalStateFactorization` |
| 干预族单调精化 | Paper direct | coordinate restriction |
| 目标因果余量空 iff 可识别 | Paper direct | range factorization |
| 有限干预 set cover 等价 | Paper direct | finite pair cover |
| 随机化桥 | Classical/Paper | independence + consistency |
| back-door 调整 | Classical, not Lean-closed here | DAG blocking + positivity |
| positivity failure | Finite paper certificate | off-support mechanism |
| hidden confounding gap | Finite paper certificate | shared Bernoulli source |
| product SCM intervention factorization | Paper | independent exogenous blocks |
| cross-prime confounding反例 | Finite paper certificate | shared source |
| interventional Markov equivalence refinement | Classical | Hauser–Bühlmann |
| transport residual criterion | Paper direct | kernel inclusion |
| transport formula completeness | Classical | selection diagrams / do-calculus |
| ATE depends only on marginals | Paper direct | linearity |
| benefit/harm Fréchet bounds | Paper finite proof | \(2\times2\) table |
| monotonicity point identification | Paper direct | remove harm cell |
| nested counterfactual identification | Classical/Open Lean bridge | causal hierarchy algorithms |
| causal belief sufficiency | Classical finite target | Bayes kernels |
| causal Bellman contraction | Paper specialization | existing Bellman anchor |
| sequential g-formula | Classical/Open Lean bridge | longitudinal exchangeability |
| off-policy residual criterion | Paper direct | target factorization |

## Q.7 必要有限测试

1. 第 258 节两个模型的 observational table 都为 \((1/2,0,0,1/2)\)；
2. `do(X=0)` 与 `do(X=1)` 下方向反转模型的 \(Y\)-law 不同；
3. 第 285 节两个模型的 observational table 都为四点均匀；
4. 两模型每个单世界 \(Y_x\) 均为 Bernoulli \(1/2\)；
5. 稳定模型满足 \(P(Y_0=Y_1)=1\)，翻转模型为零；
6. 对随机 \(p_0,p_1\in[0,1]\) 与所有合法 \(2\times2\) coupling，枚举验证 Fréchet 界；
7. monotonicity 约束下验证 \(b=p_1-p_0\)；
8. hidden-confounding 模型中 conditional effect 为一而 interventional effect 为零；
9. positivity 反模型在观测支持上 law 相同、支持外干预不同；
10. 三模型主动方向实验的静态调用数为二、期望调用数为 \(1+\varepsilon\)；
11. 独立块 SCM 的 finite joint law 等于局部 law 乘积；
12. shared-source countermodel 的 mutual information 非零；
13. causal carry 为空时 quotient intervention 良定义；
14. off-policy residual witness 的 behavior trajectory laws 相同而 target-policy laws 不同。

## Q.8 机器可审计字段

每个 causal observer theorem 应登记：

```text
model class
endogenous variables
exogenous variables
graph / parent relation
exogenous dependence
observational regime
allowed interventions
intervention semantics
target query layer
positivity / support
consistency assumptions
exchangeability assumptions
mechanism invariance
environment
law kernel
image condition
cross-world coupling
gauge quotient
sampling theorem
algorithmic status
proof status
```

该字段表防止把“同一 joint law 上的有限代数事实”静默扩大为任意隐藏变量、任意环境、任意 nested counterfactual 或任意纵向政策的全局因果定理。
