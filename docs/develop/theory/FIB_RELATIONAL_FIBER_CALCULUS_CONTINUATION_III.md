# FIB 关系纤维演算·续篇三
## ——有符号纤维的有限图表接口与可执行边界

上一续篇把 FIB 的安全压缩、有限取得和闭环控制分开；最新 `dev` 中的
《Recursive Relational Observation: Uniform Descriptor Boundary》又给出了一
个有限控制器、有限 descriptor type、无界数值参数和全 epoch `Reply/Same`
接口。本篇把这两个方向接起来，但只在一组明确的有限图表假设下工作。

本篇的目标不是宣称任意有符号纤维都已经可判定，而是给出一个可复用的
充分接口：一旦来源、动作、descriptor 和完整目标行都能落入同一个有限
Presburger 图表，FIB 边界就可以被判定并编译为有限控制器。接口缺一项时，
只能得到局部响应或有限前缀结果，不能自动得到完整取得。

---

# 三十一、有限有符号图表合同

## 定义 31.1（来源图表）

令 $I$ 为有限的来源类型集合。对每个 $i\in I$，给定维数 $k_i$、有限符号
集 $R_i$ 和一个有效集合

$$
X_i\subseteq\mathbb N^{k_i}\times R_i.
$$

来源域是带类型标签的不交并

$$
D=\bigsqcup_{i\in I}D_i,
\qquad
D_i=\{(i,x):x\in X_i\}.
$$

每个 $X_i$ 必须由一条有效 Presburger 公式定义。图表坐标只是描述；它们
不自动成为观察者可以免费读取的来源坐标。

给定一个 FIB 来源实现，是给每个 $D_i$ 一个映射

$$
\chi_i:D_i\to X_i
$$

以及以下三项证书：

1. `source-total`：每个实际来源恰有一个图表像；
2. `source-faithful`：图表上的两个点相同，当且仅当合同中声明它们的
   来源信息相同；
3. `native-action`：每个允许 FIB 动作在图表上有对应的有效后继。

第三项只要求对声明的动作菜单成立。它不把图表坐标提升为外部访问口。

## 定义 31.2（有限动作合同）

令 $A$ 为有限动作字母表，$E$ 为有限控制位置集合，$O$ 为有限回复集合。
每个位置 $e\in E$ 具有一个动作 $a_e\in A$ 或停止指令。对每个来源图表，
给定：

$$
\begin{aligned}
\operatorname{Guard}_e(i,x)&\subseteq X_i,\\
\operatorname{Reply}_e(i,x)&\in O,\\
\operatorname{Next}_e(i,x)&\in E,\\
\operatorname{Cost}_e(i,x)&\in\mathbb N^d.
\end{aligned}
$$

这些关系和函数的图都必须是 Presburger 可定义的。`Cost` 是资源向量，
不能被未经声明的单一标量替代。

一个动作合同是**同源的**，如果同一次运行中的回复、后继和资源增量都由
同一个 $(i,x)$ 产生。分别在不同来源上实现的边缘回复不能拼成一条联合
历史。

## 定义 31.3（descriptor 与完整边界）

令 $\Delta$ 为有限 descriptor type 集合，令 $n\in\mathbb N^r$ 为可能无界
的 descriptor 数值参数。一个 descriptor 是

$$
\delta=(\tau,n),\qquad \tau\in\Delta.
$$

在固定最大阶段数 $B$ 下，完整边界记录为

$$
\operatorname{bd}(e,j,H,v,Y,p),
$$

其中：

- $e$ 是控制位置；
- $j$ 是实际 update epoch；
- $H\in O^{\le B}$ 是按时间顺序保存的 raw event 记录；
- $v\in\mathbb N^d$ 是累计资源向量；
- $Y$ 是完整原目标行；
- $p$ 标记 pending 或 complete。

`Same` 比较整个 $Y$，而不是单个掩码、某一行字段或目标候选集。

若合同给出固定的 phase bound $B=qr+1$，则 $H$ 的形状集合是有限的；其
具体事件值仍由 `Reply` 逐项确定。这个 bound 是合同输入，不由有限 descriptor
type 自动推出。

---

# 三十二、有限图表到边界的精确桥梁

## 定义 32.1（精确图表接口）

一个来源图表合同满足 `ExactChart`，若：

1. 每个有效来源、位置和 epoch 的 literal reply 都由同一个
   `Reply(i,x,e,j)` 给出；
2. 每个允许后继都由同一个来源和实际动作产生，并满足
   `Next/Guard/Cost`；
3. descriptor 的实现使用同一个来源坐标，不允许逐分量换源；
4. 每个停止位置都有完整目标行 $Y(i,x)$；
5. 在同一停止位置，`Shared` 要求所有相容来源的完整 $Y$ 相等；
6. 所有上述谓词及其相容性条件都是 Presburger 可定义的。

条件 3 是 `same-source support`。它是联合实现条件，不是普通的像覆盖。

## 定理 32.2（有限图表边界可判定性）

固定有限 $I,E,A,O,\Delta$、阶段界 $B$ 和 descriptor 数值维数 $r$。在
`ExactChart` 合同下，下列问题可由一条有效 Presburger 判定：

$$
\begin{aligned}
\exists\text{ descriptor 赋值与有限控制表，使}\quad
&\operatorname{Total},\\
&\operatorname{Shared},\\
&\operatorname{Same},\\
&\operatorname{Guard/Next/Cost}
\end{aligned}
$$

在所有来源和所有允许阶段上同时成立。

若判定为真，则可以有效提取一个 descriptor 元组、每个控制位置的动作、
所有回复分支和每个停止位置的完整目标行。

### 证明

先枚举有限的 descriptor type、有限控制图和每个位置的有限事件分支形状。
数值参数 $n$ 不枚举具体上界，而作为 Presburger 存在量保留。对每个候选
形状，把 `Reply`、`Same`、`Shared`、后继闭合和资源条件写成一条 Presburger
公式；有限次合取仍是 Presburger。

来源类型与控制位置有限，阶段长度至多为 $B$，所以没有未界的控制图结构留
在量词外。对所有来源、epoch 和回复分支的要求使用 Presburger 普遍量词，
再通过否定和量词消去转成判定问题。

若公式为真，Presburger 判定过程提供一个满足赋值；有限图表枚举同时给出
动作、回复分支和停止行。因此得到实际的 finite controller witness。

该证明依赖的是图表接口已经把树来源、原生动作和完整目标行翻译成
Presburger 关系；它不声称任意 FIB 树或任意 signed fiber 都有这种翻译。∎

## 推论 32.3（边界上的有限控制器）

若定理 32.2 提取的表还带有自然数秩 $\rho$，且每个非停止响应分支满足

$$
\rho(\text{后继})<\rho(\text{当前}),
$$

则该表在每个允许来源上有限终止，并恢复完整目标行。

### 证明

`Guard/Next` 保证每一步实际可执行且边界闭合；严格下降的自然数秩排除
无限运行；停止位置的 `Same` 与完整目标行保证输出正确。∎

这一步把最新 `dev` 的 descriptor 边界与 FIB 续篇中的控制器证书连接起来：
Presburger 判定给出候选表，秩证书给出终止性。两者都不能被“存在一个循环
方程”替代。

---

# 三十三、为什么有限图表不等于完整 signed-fiber 解

## 命题 33.1（像覆盖不蕴含同源联合实现）

设两个 descriptor 分量分别有来源见证：

$$
\delta_1\text{ 由 }u_1\text{ 实现},
\qquad
\delta_2\text{ 由 }u_2\text{ 实现},
$$

但不存在一个来源同时实现 $(\delta_1,\delta_2)$。则由两个边缘覆盖得到的联合
descriptor 不是 `ExactChart` 见证。

### 证明

`Reply`、`Same` 和资源增量要求同一条实际历史。分别存在 $u_1,u_2$ 只说明
两个投影非空，不能产生联合来源。若把它们拼成一条记录，就引入了合同中
不存在的 source pair。∎

## 命题 33.2（弱化 Same 的错误接受）

若某个停止位置含有两个相容来源 $(i,x)$、$(i',x')$，满足

$$
Y(i,x)\ne Y(i',x'),
$$

而摘要式 `Same` 却把它们判为相同，则该摘要可能接受一个不正确的共享停止行。

### 证明

共享停止行只有一个输出。它最多等于其中一个完整目标行，不能同时等于两
个不同的 $Y$。摘要相同只说明被保留字段相同，不说明完整目标相同。∎

## 推论 33.3（有限前缀不是全 epoch descriptor）

若只证明每个给定有限深度 $h$ 存在一个前缀图表，则不能推出存在同一 descriptor
在所有 epoch 上满足 `Reply`、`Same` 和 successor transport。

### 证明

不同的 $h$ 可以使用不同的来源参数、descriptor 数值或控制表。有限深度
存在性是

$$
\forall h\;\exists\delta_h,
$$

而全 epoch descriptor 需要

$$
\exists\delta\;\forall h.
$$

量词不能交换。∎

这三个失败模式正是 general signed-fiber 缺口的结构，而不是 FIB 字母表大小
可以自动消除的编码问题。

---

# 三十四、动作语言决定隐藏核

## 定义 34.1（动作语言相对隐藏核）

令 $\mathcal W\subseteq\mathcal G^*$ 为合同允许的实际动作词集合。对每个
词 $w$，令 $L_w$ 是按实际时间顺序复合的后继变换；$C_\ell$ 是允许的读出。
定义

$$
K(\mathcal W)
=
\bigcap_{w\in\mathcal W}\bigcap_\ell
\ker(C_\ell L_w).
$$

如果边界还需要事件顺序、资源或停止行为，则把它们作为额外的观测分量
并一并放入核的交集中。

## 定理 34.2（动作语言单调性）

若

$$
\mathcal W_1\subseteq\mathcal W_2,
$$

则

$$
K(\mathcal W_2)\subseteq K(\mathcal W_1).
$$

### 证明

$K(\mathcal W_2)$ 是更多核的交集；删除部分动作词只能扩大或保持交集。∎

因此，所谓“当前不可见”必须带动作语言下标。固定顺序、宏动作和允许任意
交错动作，会产生不同的隐藏核。上一个 FIB 续篇中给出的交错动作反例正是
$K(\mathcal W)$ 对动作顺序敏感的具体实例。

## 推论 34.3（原生 quotient 的必要接口）

一个声称对 FIB 原生动作安全的 quotient，至少需要声明：

1. 允许的动作语言 $\mathcal W$；
2. 每个词的实际后继和合法域；
3. 同源事件分支及资源增量；
4. 停止时的完整目标行。

仅给出当前寄存器相等、静态读出核或固定干预词的核，不足以证明该 quotient
能继续参加所有允许的数学活动。

---

# 三十五、统一接口的成果与未决边界

由本篇得到的可复用结构是：

$$
\boxed{
\text{FIB 来源图表}
\longrightarrow
\text{ExactChart}
\longrightarrow
\text{Presburger descriptor/controller}
\longrightarrow
\text{rank-certified finite acquisition}
}
$$

它把上一续篇的三层边界和最新 `dev` 的 uniform descriptor boundary 连接成
一个条件编译链：

- 图表层回答来源和动作是否被完整表示；
- descriptor 层回答是否存在统一的 finite boundary；
- controller 层回答是否能在同一历史上执行并终止；
- 资源层保留 raw、update、epoch 和安装成本的向量区别。

这条链不允许以下替换：

$$
\text{finite image cover}
\not\Rightarrow
\text{same-source descriptor tuple},
$$

$$
\forall h\,\exists\delta_h
\not\Rightarrow
\exists\delta\,\forall h,
$$

$$
\text{current readout equality}
\not\Rightarrow
\text{future-action equivalence}.
$$

仍未解决的核心问题是：对一般 signed FIB fiber，如何有效构造满足
`source-total`、`source-faithful`、`native-action` 和 `ExactChart` 的图表，尤其是
非 atomic skeleton、联合 residual coordinates、全 epoch Reply 和完整 whole-row
Same。有限图表定理只给出接口内的判定与 witness extraction；它不把接口假设
伪装成已经存在。

本篇是普通数学理论，不宣称已经有 Lean/kernel 核验，也不宣称物理 actuator、
clock、reset 或全局资源最优。失败于图表识别或 descriptor 判定只保留为未决，
不能被解释为 native undecidability 或恢复不可能。

## 参考来源

- `RECURSIVE_RELATIONAL_OBSERVATION_UNIFORM_DESCRIPTOR_BOUNDARY.md`：有限
  descriptor type、全 epoch `Reply/Same`、阶段界和 Presburger 边界判定的抽象接口。
- `FIB_RELATIONAL_FIBER_CALCULUS.md`：来源、观察纤维、组合、连续实现和证明
  闭合的基础演算。
- `FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION.md`：有限取得、候选关系、控制
  记忆和秩证书。
- `FIB_RELATIONAL_FIBER_CALCULUS_CONTINUATION_II.md`：固定 native 菜单、双资源
  边界和交错动作顺序的具体反例；该引用不把其有限菜单结论推广为全地址结论。

## 追加锚（本行以下为增补区）
