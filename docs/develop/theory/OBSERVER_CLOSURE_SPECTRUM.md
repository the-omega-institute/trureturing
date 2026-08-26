# 观察者闭合谱
## 最小预测商、记忆预算、受控完成与量子可观测闭包

**版本：v1.0，2026-08-22**

---

## 摘要

既有的动力接口—余量演算把观察后的动力学是否自治归结为核保持问题：观察接口 q : X → B 把完整状态压缩为可见状态；若 q(x)=q(y)，但 q(Fx)≠q(Fy)，则更新 F 不能在观察商上良定义。被当前接口删除的区别会在未来重新出现，表现为 carry、隐藏记忆、交叉块回流、交换子泄漏或查询非识别。

本文继续推进这一结构，不再只问闭合是否成立，而是研究：闭合失败具有多深；至少需要加入多少记忆才能修复；全部修复中哪一个是规范最小的。核心对象是未来核塔：

```text
Kₙ = ⋂₀≤j≤n (Fʲ × Fʲ)⁻¹ Kq
K∞ = ⋂j≥0 (Fʲ × Fʲ)⁻¹ Kq
```

本文证明：

1. K∞ 是包含于当前观察核 Kq 的最大前向不变等价关系；
2. 商 X/K∞ 是所有既保留当前读数、又使未来自治的观察完成中的最粗者；
3. 有限系统的核塔在有限深度稳定，严格精化次数至多为 |X|−|Im(q)|；
4. 类数增长给出可加的记忆预算，其总量等于当前观察商与完整预测商之间的对数分辨率差；
5. 受控系统必须对全部行动词取共同未来核，单一自然演化下的闭合不能推出干预充分；
6. 折扣未来伪度量给出一个规范的近似闭合几何；
7. 在线性与量子系统中，最小可观测闭包由反复施加生成元或交换子生成，并在有限维中稳定；
8. 因果观察、干预与反事实查询可以统一为目标相对的核精化，但 coupling 余量不能由旧查询的后处理消除。

新增统一定理均为本文给出的 paper-level 证明，不声称已经具有仓库中的 Lean proof term。

---

## 0. 真值层级与约定

本文区分：

- **定义**：保守引入对象；
- **本文定理**：正文给出纸面证明；
- **仓库锚点**：仓库已有机器证明的局部事实；
- **形式化路线**：尚待 Lean 闭合；
- **非断言**：明确排除过度解释。

给定接口 q : X → B，定义其核关系：

```text
Kq = {(x,y) ∈ X² | q(x)=q(y)}.
```

所有下降映射都只在有效像 Bq = Im(q) 上讨论，以免把 B∖Bq 上的任意延拓误报为物理或语义结构。

---

## 1. 从一步 carry 到完整未来核

### 定义 1.1：有限未来接口

对 n ∈ ℕ，定义：

```text
q[n](x) = (q(x), q(Fx), …, q(Fⁿx)).
```

其核为：

```text
Kₙ = Kq[n]
   = ⋂₀≤j≤n (Fʲ × Fʲ)⁻¹ Kq.
```

于是：

```text
K₀ ⊇ K₁ ⊇ K₂ ⊇ …
```

### 定义 1.2：完整未来核

```text
K∞ = ⋂n≥0 Kₙ.
```

等价地：

```text
(x,y) ∈ K∞  ⇔  ∀n∈ℕ, q(Fⁿx)=q(Fⁿy).
```

### 本文定理 1.1：最大前向不变子核

K∞ 是满足以下条件的最大等价关系 R：

```text
R ⊆ Kq,
(x,y) ∈ R  ⇒  (Fx,Fy) ∈ R.
```

#### 证明

K∞ ⊆ Kq 由 n=0 得到。若 (x,y)∈K∞，则对任意 n：

```text
q(Fⁿ(Fx)) = q(Fⁿ⁺¹x) = q(Fⁿ⁺¹y) = q(Fⁿ(Fy)),
```

故 (Fx,Fy)∈K∞。

反之，设 R⊆Kq 且 R 前向不变。若 (x,y)∈R，归纳得到 (Fⁿx,Fⁿy)∈R⊆Kq，因此所有未来读数相同，即 (x,y)∈K∞。所以 R⊆K∞。∎

### 推论 1.1：一步闭合的五重等价

以下条件等价：

```text
K₀ = K₁;
Kq 对 F 前向不变；
Kq = K∞；
F 沿 q 精确下降；
Carry(q,F) = ∅.
```

因此 carry 不是独立附加对象；它恰好是核塔第一层发生严格精化的见证。

---

## 2. 最小预测完成的泛性质

### 定义 2.1：预测完成

称 r : X → S 是 (q,F) 的预测完成，若：

1. r 保留当前读数，即 q 可沿 r 因子化；
2. F 沿 r 下降，即存在 G : Sr → Sr，使 r(Fx)=G(r(x))。

第一项等价于 Kr⊆Kq；第二项等价于 Kr 对 F 前向不变。

### 定义 2.2：规范未来接口

```text
q∞(x) = (q(Fⁿx))n≥0.
```

记 Zq = Im(q∞)。在 Zq 上定义左移：

```text
σ(z₀,z₁,z₂,…) = (z₁,z₂,z₃,…).
```

于是：

```text
q∞ ∘ F = σ ∘ q∞.
```

### 本文定理 2.1：最粗预测完成

规范未来接口 q∞ 是全部预测完成中最粗的。对任意预测完成 r，都存在唯一映射 π : Sr → Zq，使：

```text
q∞ = π ∘ r.
```

等价地：

```text
Kr ⊆ K∞.
```

#### 证明

由于 r 保留 q，Kr⊆Kq；由于 F 沿 r 下降，Kr 前向不变。由定理 1.1 的最大性，Kr⊆K∞。核包含给出在有效像上的唯一因子化映射 π。∎

### 解释 2.1

这里的最粗不是信息最多，而是只加入未来会重新要求的区别，不额外恢复与未来读数无关的微观细节：

```text
最小充分记忆
= 当前观察核中，为获得前向不变性而必须切开的部分。
```

这是一种目标相对的最小完成，不是无条件重建整个微观世界。

---

## 3. 有限系统的闭合深度

设 X 有限，记：

```text
cₙ = |X/Kₙ|.
```

### 本文定理 3.1：有限稳定

存在最小 m*，使：

```text
Kₘ* = Kₘ*₊₁.
```

一旦出现一步稳定，就有：

```text
∀m≥m*, Kₘ = Kₘ* = K∞.
```

#### 证明

有限集合上的等价关系严格下降时，等价类数严格增加；而 cₙ≤|X|，所以严格增加只能发生有限次。

若 Kₘ=Kₘ₊₁，则对 (x,y)∈Kₘ，由 (x,y)∈Kₘ₊₁ 得 (Fx,Fy)∈Kₘ，所以 Kₘ 已前向不变。由定理 1.1，Kₘ=K∞。∎

### 推论 3.1：严格精化次数界

初始类数 c₀=|Bq|，最终类数不超过 |X|，故严格精化次数至多：

```text
|X| − |Bq|.
```

该界控制类分裂发生多少轮，不等于轨道周期、混合时间或系统停止时间。

---

## 4. 观察者闭合谱与记忆预算

### 定义 4.1：闭合谱

```text
C(q,F) = (c₀,c₁,c₂,…),
cₙ = |X/Kₙ|.
```

闭合谱不记录标签本身，只记录未来分辨率随观察深度增长的结构。

### 定义 4.2：第 n 层记忆增量

有限系统中定义：

```text
μₙ = log(cₙ₊₁) − log(cₙ)
   = log(cₙ₊₁/cₙ) ≥ 0.
```

### 本文定理 4.1：记忆预算望远镜恒等式

若核塔在 m* 稳定，则：

```text
Σ₀≤n<m* μₙ = log(|X/K∞| / |Bq|).
```

#### 证明

对 log(cₙ₊₁)−log(cₙ) 望远镜求和，再使用 cₘ*=|X/K∞| 与 c₀=|Bq|。∎

右侧不是 Shannon 熵，除非另行给定概率分布。它是纯组合的对数分辨率预算：完成未来自治所需的总结构记忆，等于预测商相对当前观察商增加的对数类数。

### 概率加权版本

若 X 上给定概率 p，令 [x]ₙ 表示 Kₙ 等价类，定义：

```text
Hₙ = − ΣC∈X/Kₙ p(C) log p(C).
```

则 H₀≤H₁≤…，并且：

```text
Hₙ₊₁ − Hₙ = H([x]ₙ₊₁ | [x]ₙ).
```

所以概率版本的记忆增量，是下一层未来区分在当前层条件下新增的条件熵。

---

## 5. 受控系统：自治必须对全部行动词成立

设行动集合为 A，每个行动给出更新 Fa : X → X。对行动词 w∈A*，记 Fw 为相应复合。

### 定义 5.1：受控未来核

```text
KA = ⋂w∈A* (Fw × Fw)⁻¹ Kq.
```

### 本文定理 5.1：最大公共行动 congruence

KA 是包含于 Kq、并同时对所有 Fa 前向不变的最大等价关系。

#### 证明

若 (x,y)∈KA，则对任意 a 和任意后续词 w：

```text
q(Fw(Fa x)) = q(Faw x) = q(Faw y) = q(Fw(Fa y)),
```

故 (Fa x,Fa y)∈KA。最大性由对全部行动词的归纳得到。∎

### 推论 5.1：预测闭合不推出干预闭合

某个自然更新 F 沿 q 下降，并不推出全部可选行动 Fa 都沿同一接口下降：

```text
自然轨道上的 Markov 性
≠ 政策或干预下的充分性。
```

干预不是看更多同类数据，而是扩大必须共同保持核关系的过程族。

---

## 6. 近似闭合的规范未来几何

设 (B,d) 为有界度量空间，0<λ<1。

### 定义 6.1：折扣未来伪度量

```text
Dλ(x,y) = supn≥0 λⁿ d(q(Fⁿx),q(Fⁿy)).
```

### 本文定理 6.1：规范性质

Dλ 是伪度量，并满足：

```text
d(qx,qy) ≤ Dλ(x,y);
Dλ(Fx,Fy) ≤ λ⁻¹ Dλ(x,y);
Dλ(x,y)=0 ⇔ (x,y)∈K∞.
```

#### 证明

每个 λⁿd(q(Fⁿx),q(Fⁿy)) 都是伪度量，上确界保持三角不等式。第一项取 n=0。第二项由指标换元 m=n+1 得到。第三项等价于全部非负未来距离同时为零。∎

离散核塔只回答是否可区分；Dλ 同时编码区别何时出现、区别有多大以及越远未来应如何折扣。因此它给出不依赖任意隐藏坐标选择的近似观察几何。

---

## 7. 线性与量子系统的最小闭包生成

### 7.1 线性可观测闭包

设 V 为有限维向量空间，L : V → V 为线性更新，初始读数子空间为 W₀⊆V*。定义：

```text
Wₙ₊₁ = Wₙ + L*Wₙ.
```

### 本文定理 7.1：最小 Koopman 不变读数空间

```text
W∞ = Σn≥0 (L*)ⁿW₀
```

是包含 W₀ 的最小 L* 不变线性子空间。若 dim(V)=d，塔至多经过 d−dim(W₀) 次严格维数增长后稳定。

该读数塔与未来核塔互为对偶：核塔切开状态等价类，读数塔加入区分这些类所需的函数。

### 7.2 量子可观测闭包

设有限维 Hilbert 空间上的 Hamiltonian 为 H=H*，初始可观测线性空间为 O₀。定义：

```text
Oₙ₊₁ = Oₙ + [H,Oₙ].
```

### 本文定理 7.2：最小 Heisenberg 闭包

```text
O∞ = span{adHⁿ(A) | A∈O₀, n≥0}
```

是包含 O₀ 且在 adH=[H,·] 下不变的最小线性空间。若 Hilbert 空间维数为 d，则算子空间维数为 d²，所以闭包塔在有限步内稳定。

### 推论 7.1：守恒与自治必须分开

单个 A 满足 [H,A]=0，意味着该读数守恒；更一般地，若 [H,O]⊆O，则 O 中的读数可以彼此演化而不逃出观察语言。因此：

```text
观察代数自治 ≠ 每个观察量静止。
```

### 定义 7.1：量子闭合缺陷

令 PO 为 Hilbert–Schmidt 意义下投影到 O 的正交投影，定义：

```text
εH(O) = ‖(I−PO) adH PO‖.
```

则：

```text
εH(O)=0 ⇔ [H,O]⊆O.
```

该量测量观察语言在无穷小 Heisenberg 演化下向不可表达方向的泄漏，不是一般意义上的量子神秘性。

---

## 8. 查询闭包：观察、干预与反事实

设模型类为 M，查询族为 Q。定义查询接口：

```text
EQ(M) = (Q(M))Q∈Q.
```

其核 KQ 表示全部当前查询仍无法区分的模型对。若 Q₁⊆Q₂，则：

```text
KQ₂ ⊆ KQ₁.
```

### 本文定理 8.1：目标识别的核判据

对目标 T : M → Y，以下等价：

```text
T 可由 EQ 唯一决定；
存在 h，使 T=h∘EQ；
KQ ⊆ KT.
```

证明是在有效像上的标准核因子化构造。∎

### 本文定理 8.2：后处理不能提高识别分辨率

对任意后处理 g：

```text
K(g∘EQ) ⊇ KEQ.
```

所以若 KQ⊄KT，任何只读取同一查询画像的更复杂估计器、语言模型或递归程序，都不能把 T 变成已识别对象。

### Coupling 余量

即使全部单世界干预边缘 L(Yᵃ) 都已知，也通常不能唯一决定跨世界联合分布 L((Yᵃ)a∈A)。这是 coupling 纤维的非唯一性，而非同一输入上的计算能力不足。修复它需要跨世界结构假设、共享外生变量约束、单调性、秩保持或 sharp bounds，不是对旧边缘做更多后处理。

---

## 9. 新的结构推论

### 推论 9.1：观察者时间是核精化深度

物理时间 n 描述系统运行多少步；闭合深度 m* 描述观察者必须保留多长的未来区分，才能获得自治状态：

```text
clock time ≠ observer refinement time.
```

一个系统可以运行无限久而当前接口始终闭合；另一个系统只需一步更新，就可能暴露必须长期保存的隐藏区别。

### 推论 9.2：记忆是未来复活的区别

若两个状态当前被 q 合并，却在最小时刻 n 满足 q(Fⁿx)≠q(Fⁿy)，则区分它们的记忆不是关于过去的任意存档，而是未来闭合所要求的最早 witness。

### 推论 9.3：闭合可以极粗

常值接口 q(x)=* 对任何动力学都闭合。因此零信息观察者可以没有 carry，却完全不忠实。必须分开报告：

```text
dynamic closure;
state separation;
target sufficiency.
```

### 推论 9.4：完全状态仍不等于自描述完成

恒等接口 q=idX 对普通状态目标忠实且动力闭合，但不自动给出真值谓词、全部可定义对象的枚举、系统自身一致性证明或类型扩张后的对角对象。对象层闭合与元语言闭合属于不同问题。

### 推论 9.5：统一的准确边界

集合 carry、线性交叉块、量子交换子泄漏与因果查询余量共享接口没有对相关过程闭合的骨架，但并非无条件相等的物理量。任何跨语言识别都必须明确给出状态表示、接口实现、动力学函子以及缺陷量的保真等式或误差界。

---

## 10. 与当前仓库的连接

本文延伸以下已存在的机器真值方向，但不修改它们：

- `D5/S3/ConceptDynamics/Dialectics/ExactDescentNoCarry.lean`：精确下降排除 carry；
- `D5/S3/Quantum/Dynamics/LeastInvariantObservableAlgebra.lean`：最小动力学不变观察代数；
- `D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.lean`：投影概率的交换子流；
- `D5/S3/Observer/Conditioning/UnreadStateOrthogonalProjection.lean`：未读测量的 Hilbert–Schmidt 投影结构；
- `D5/S3/Quantum/Decoherence/ReducedRecordAccessDefect.lean`：全局记录与约化访问缺陷；
- `D5/S3/ObserverMemory/FunctionalGraphs/FiniteFunctionalGraphFittingDecomposition.lean`：有限暂态—周期核分解；
- `D5/S3/Quantum/Completion/IncreasingProjectionStrongLimit.lean` 与相关完成文件：强完成、范数分离与残余塔。

建议新增的形式化目标：

1. `FutureKernelMaximality`：K∞ 的最大前向不变性；
2. `CoarsestPredictiveCompletion`：规范未来接口的泛性质；
3. `FiniteClosureDepth`：有限核塔稳定与类数界；
4. `ClosureSpectrumBudget`：组合与概率加权记忆预算；
5. `ControlledFutureCongruence`：行动词共同核；
6. `DiscountedFuturePseudoMetric`：折扣未来伪度量；
7. `IteratedObservableClosure`：线性与量子生成闭包。

最小依赖顺序为：纯集合核理论 → 有限稳定 → 受控词闭包 → 伪度量 → 线性对偶 → 量子交换子实例 → 因果查询实例。

---

## 11. 严格非断言

本文不声称：

1. 闭合谱本身是新的物理熵；
2. 类数预算在没有概率模型时等于 Shannon 信息；
3. 所有非 Markov 过程都具有有限维隐藏实现；
4. 所有量子退相干都只是接口缺陷；
5. 交换子、carry、因果混杂与熵产生是同一个量；
6. 全部干预边缘唯一决定反事实 joint；
7. 状态忠实推出自描述完备；
8. 文中的新增纸面定理已经 Lean 闭合；
9. 本文证明 RH、Weil positivity 或其他公开开放问题。

---

## 12. 最终综合

观察接口不是被动读取一个数值，而是在完整状态空间上声明一种相等关系：q(x)=q(y)。动力学自治的准确含义是，真实更新尊重这一相等：

```text
q(x)=q(y) ⇒ q(Fx)=q(Fy).
```

若更新不尊重它，未来就会重新要求一个被当前观察删除的区别。核塔记录这些区别何时复活；最小预测商只恢复未来真正需要的区别；闭合谱度量恢复过程的层数与预算；受控核要求这种相等在所有可选行动下继续成立；量子可观测闭包要求观察语言在交换子动力学下不逃逸；因果查询闭包要求目标在证据核上常值。

```text
观察 = 选择哪些状态可被视为相同；
自治 = 过程保持这种相同；
carry = 未来反驳了当前的相同声明；
记忆 = 为使该声明前向稳定而加入的最小区分；
完成 = 把观察核收缩到最大的过程 congruence。
```

最深的边界不是系统是否拥有隐藏变量，而是：

```text
当前观察所删除的区别，是否仍具有未来或干预效力？
```

---

# 13. v1.1 追加：自治修复、时间分块与自适应实验

**追加版本：v1.1，2026-08-22**

前文把预测完成定义为当前观察核中的最大前向不变子核。本次追加继续推进三个未展开的问题：闭合失败是否只有“增加记忆”这一种规范修复；改变采样时钟是否保持同一预测商；开环行动词能否完整刻画自适应观察者的实验能力。

## 13.1 预测 interior 与遗忘 closure

记 `Eq(X)` 为 X 上全部等价关系按包含排序的完备格。关系越小，分区越细。称 R 为 F-congruence，若：

```text
(x,y)∈R ⇒ (Fx,Fy)∈R.
```

定义预测 interior：

```text
I_F(R) = ⋂n≥0 (Fⁿ×Fⁿ)⁻¹R.
```

它是包含于 R 的最大 F-congruence；当 R=Kq 时，I_F(Kq)=K∞。

定义遗忘 closure：

```text
C_F(R) = ⋂{S | R⊆S 且 S 是 F-congruence}.
```

等价地，先取全部迭代像：

```text
Orb_F(R) = ⋃n≥0 (Fⁿ×Fⁿ)(R),
```

再取其反身、对称、传递闭包：

```text
C_F(R) = EqCl(Orb_F(R)).
```

### 本文定理 13.1：双规范修复

I_F 是收缩、单调、幂等的 interior operator；C_F 是扩张、单调、幂等的 closure operator。二者具有完全相同的固定点：

```text
I_F(R)=R ⇔ R 是 F-congruence ⇔ C_F(R)=R.
```

#### 证明

I_F(R)⊆R 来自 n=0；逆像保持包含，故 I_F 单调；I_F(R) 已前向不变，故再次应用 I_F 不再改变它。

C_F(R) 包含 R；若 R⊆T，则包含 T 的稳定超关系候选更少，故 C_F(R)⊆C_F(T)；C_F(R) 本身稳定，故再次闭包不变。固定点刻画直接来自最大稳定子关系与最小稳定超关系的泛性质。∎

令 j : Cong_F(X) ↪ Eq(X) 为包含映射，则：

```text
C_F ⊣ j ⊣ I_F.
```

准确地，对稳定关系 S：

```text
C_F(R)⊆S ⇔ R⊆S,
S⊆I_F(R) ⇔ S⊆R.
```

因此不闭合接口有两个方向相反的规范修复：

```text
I_F(Kq) ⊆ Kq ⊆ C_F(Kq).
```

- 左侧通过切开错误合并的状态来恢复自治，代价是增加记忆；
- 右侧通过继续合并未来会分叉的状态来恢复自治，代价是牺牲分辨率。

完整观察与完全遗忘都可能自治，所以自治不是信息量的单调函数，而是接口所声明的相等关系与过程作用是否相容。

### 有限自治代价

若 X 有限，令 N(R)=|X/R|，定义：

```text
M_F(R) = log(N(I_F(R))/N(R)),
L_F(R) = log(N(R)/N(C_F(R))),
G_F(R) = log(N(I_F(R))/N(C_F(R))).
```

则：

```text
G_F(R)=M_F(R)+L_F(R),
G_F(R)=0 ⇔ R 已经闭合.
```

第一项是保持全部现有区别时必须增加的记忆；第二项是保持全部现有等同声明时必须放弃的分辨率。

## 13.2 传感器融合与直积张量化

多个接口 qi 的联合接口核是交：

```text
K(q₁,…,qᵣ) = ⋂i Kqi.
```

### 本文定理 13.2：完成与传感器融合交换

```text
I_F(⋂i Ri) = ⋂i I_F(Ri).
```

#### 证明

逆像保持任意交：

```text
⋂n (Fⁿ×Fⁿ)⁻¹(⋂iRi)
= ⋂i⋂n (Fⁿ×Fⁿ)⁻¹Ri.
```

∎

所以先分别完成再融合，与先融合再完成，在核层面严格相同。

对独立直积系统：

```text
X=X₁×X₂,
F=(F₁,F₂),
q=(q₁,q₂),
```

有：

```text
Kₙ = Kₙ¹ × Kₙ²,
cₙ = cₙ¹ cₙ²,
μₙ = μₙ¹ + μₙ²,
m* = max(m₁*,m₂*).
```

因此独立分量的闭合谱乘法、对数记忆预算加法。偏离该公式的部分必须来自初始相关、耦合动力学或耦合读数，而不是两个独立闭合过程本身。

## 14. 时间粗粒化与采样别名

固定整数 k≥1，只在 0,k,2k,… 时刻读取 q。稀疏采样核为：

```text
K∞(k) = ⋂m≥0 (Fᵏᵐ×Fᵏᵐ)⁻¹Kq.
```

总有：

```text
K∞ ⊆ K∞(k).
```

差集中的状态对在所有采样点相同，却在某个被跳过的中间时刻不同；这是严格的采样 aliasing residual。

定义长度 k 的块接口：

```text
q<k>(x) = (q(x),q(Fx),…,q(Fᵏ⁻¹x)).
```

### 本文定理 14.1：精确时间分块

块系统以 Fᵏ 为一步更新，则：

```text
K_M(q<k>,Fᵏ) = K_{kM+k−1}(q,F),
K∞(q<k>,Fᵏ) = K∞(q,F).
```

#### 证明

块系统第 m 步读取原系统的 km,km+1,…,km+k−1 时刻。m=0,…,M 的读数时刻并集恰为 0,…,kM+k−1，所以有限核相等；取全部 M 即得完整未来核相等。∎

若原系统闭合深度为 m*，块系统闭合深度为：

```text
floor(m*/k).
```

因此只把 F 换成 Fᵏ 会丢失相位信息；同时把中间 k 个读数装入块接口，才是无损时间重参数化。

```text
改变时钟而不改变接口
≠ 对原过程做无损重参数化.
```

## 15. 折扣未来几何的 Bellman 固定点

设 (B,d) 有界，0<λ<1。定义：

```text
Dλ(x,y) = supn≥0 λⁿ d(q(Fⁿx),q(Fⁿy)).
```

对有界函数 D 定义 Bellman 算子：

```text
(TλD)(x,y)
= max{d(qx,qy), λD(Fx,Fy)}.
```

### 本文定理 15.1：唯一固定点与截断界

Tλ 在上确界范数下是 λ-压缩，并且 Dλ 是其唯一有界固定点：

```text
Dλ = TλDλ.
```

若 diam(B)≤M，有限视野近似：

```text
Dλ[N](x,y)=max0≤n≤N λⁿd(q(Fⁿx),q(Fⁿy))
```

满足：

```text
0 ≤ Dλ−Dλ[N] ≤ λᴺ⁺¹M.
```

#### 证明

u↦max{a,u} 是 1-Lipschitz，故 Tλ 是 λ-压缩。把 Dλ 的 n=0 项与 n≥1 尾项分开即可得到 Bellman 方程。截断后的全部尾项至多为 λᴺ⁺¹M。∎

对压缩接口 r，定义未来纤维直径：

```text
Δλ(r)=sup{Dλ(x,y) | r(x)=r(y)}.
```

任何只读取 r 的单值未来预测器，其最坏误差 E 都满足：

```text
E ≥ ½Δλ(r).
```

因为同一 r-纤维中的 x,y 被映射到同一个预测值，三角不等式给出 Dλ(x,y)≤2E。这个下界与模型类别、优化器和计算资源无关，是接口自身不可突破的 minimax 障碍。

## 16. 开环行动词与自适应观察者

设行动集合为 A，更新族为 Fa。观察反馈政策在时刻 t 只读取过去观察历史并选择行动：

```text
πt : Bᵗ⁺¹ → A.
```

### 本文定理 16.1：开环—反馈等价

对状态 x,y，以下等价：

```text
(x,y)∈KA;
对每个有限行动词 w，q(Fw x)=q(Fw y)；
对每个确定性观察反馈政策 π，两者产生完全相同的观察历史.
```

#### 证明

若全部开环词下输出相同，则对反馈时间归纳：相同的历史迫使政策选择相同行动；相同行动前缀下，下一读数仍相同。

反向取忽略观察、按预定时刻输出任意固定词 w 的政策，即恢复全部开环词条件。∎

随机政策在固定随机种子后退化为确定性政策，因此当随机种子与初态独立时，结论同样成立。

若政策可以直接读取隐藏完整状态，则它可能对观察等价状态选择不同动作，以上等价失效。因此：

```text
observer-feedback control
≠ oracle state-feedback control.
```

商 X/KA 带有良定义的行动更新与输出，是实现全部行动—输出轨迹的最粗确定性状态表示；任何同时保留 q 且允许全部 Fa 下降的表示都必须细于它。这给出受控观察系统的 Myhill–Nerode 型最小性。

## 17. 追加形式化路线与边界

建议按以下顺序进入 Lean：

1. `PredictiveInteriorOperator`：I_F 的收缩、单调、幂等与交保持；
2. `ForwardCongruenceClosure`：C_F 的最小稳定超关系；
3. `AutonomyAdjointTriple`：C_F ⊣ j ⊣ I_F；
4. `ObserverRepairCost`：有限类数代价分解；
5. `SensorFusionCompletion`：预测完成保持接口交；
6. `ProductClosureSpectrum`：直积核、类数、增量与深度；
7. `TimeBlockingKernel`：精确时间分块公式；
8. `DiscountedFutureBellman`：压缩映射、唯一固定点与截断界；
9. `FiberDiameterLowerBound`：通用二分之一直径下界；
10. `FeedbackPolicyIndistinguishability`：开环词与反馈政策等价。

本次追加不声称：

1. 记忆代价与遗忘代价具有普适物理单位；
2. 格论伴随本身证明意识、自由意志或量子坍缩本体论；
3. 折扣未来伪度量是唯一可能的近似观察几何；
4. 时间分块公式排除连续时间、超限时间或类型扩张中的额外困难；
5. 开环—反馈等价适用于可直接访问隐藏状态的 oracle 政策；
6. 新增纸面定理已经 Lean 闭合。

最终，观察者自治不是信息最大化，而是“所声明的相同”在过程作用下保持为相同。不闭合时，规范选择只有在约束方向明确后才唯一：

```text
记忆完成：Kq ↦ I_F(Kq)，通过增加区别恢复自治；
遗忘完成：Kq ↦ C_F(Kq)，通过删除区别恢复自治。
```

时间分辨率决定哪些时刻能够见证不相容；行动族决定哪些实验路径能够见证不相容；折扣未来几何把二值见证转化为可计算误差。三者共同把“观察者闭合”从静态接口性质提升为时间、控制与近似误差的统一结构。

---

# 18. v1.2 增订：反身代理、来源治理与可控—可观测闭包

**追加版本：v1.2，2026-08-26**

本增订只追加于前文之后，不删改第 0–17 节。前文已经把观察者闭合刻画为当前核关系在动力学或行动词作用下的稳定性；本增订进一步研究：当观察者不仅读取世界，而且能够选择行动、修改策略、承担记录并保持自身行动能力时，最小闭合对象是什么。

本增订统一四条此前分散的链：

1. **策略闭合**：哪些历史差异会改变未来选择；
2. **作者闭合**：行动差异究竟来自观察者内部、外部控制还是无主随机；
3. **控制—观察对偶**：哪些内部方向既能由观察者改变，又会在未来留下可见差异；
4. **自由保持**：观察者是否存在一种策略，使未来的自己仍然保有选择、修订与追溯能力。

全文继续使用以下真值纪律：

- **定义**：保守引入对象；
- **本文定理**：给出 paper-level 证明；
- **条件命题**：依赖额外拓扑、概率、可计算性或物理实现前件；
- **形式化路线**：尚待 Lean kernel 闭合；
- **非断言**：明确排除把操作自主性冒充为强本体自由。

核心边界是：

```text
没有典范策略 ≠ 没有确定策略；
行为随机 ≠ 行为属于主体；
内部相关 ≠ 内部因果控制；
操作自主 ≠ 完整宇宙非决定性。
```

---

# 19. 代理因果画像与最小历史商

设全部有限历史构成集合 $\mathcal H$，未来允许施加的环境或控制协议构成 $\mathcal W$，未来行动—观察—记录序列空间为 $\mathcal Z$。对历史 $h$ 与协议 $w$，定义完整未来交互律

$$
\Gamma(h)(w)
=
\operatorname{Law}
\bigl(Z_{\mathrm{future}}\mid h,\operatorname{do}(w)\bigr).
$$

## 定义 19.1（代理等价）

$$
h\sim_{\mathrm{ag}}h'
\iff
\forall w\in\mathcal W,
\quad
\Gamma(h)(w)=\Gamma(h')(w).
$$

定义代理因果状态空间

$$
\boxed{
S_{\mathrm{ag}}
=
\mathcal H/{\sim_{\mathrm{ag}}}.
}
$$

它不只决定下一动作，还决定在所有允许干预下未来行动、环境响应、记录与内部更新的联合分布。

## 本文定理 19.1（普适最小性）

若历史接口

$$
r:\mathcal H\to R
$$

足以决定完整未来交互画像，即存在

$$
F:R\to(\mathcal W\to\operatorname{Prob}(\mathcal Z))
$$

满足 $\Gamma=F\circ r$，则存在唯一映射

$$
\bar r:\operatorname{Im}(r)\to S_{\mathrm{ag}}
$$

使

$$
[h]_{\mathrm{ag}}=\bar r(r(h)).
$$

### 证明

若 $r(h)=r(h')$，则

$$
\Gamma(h)=F(r(h))=F(r(h'))=\Gamma(h'),
$$

故 $h\sim_{\mathrm{ag}}h'$。于是 $r(h)\mapsto[h]_{\mathrm{ag}}$ 与代表元无关；在有效像上唯一。∎

因此：

$$
\boxed{
\text{代理自我}
=
\text{保持全部未来可干预交互规律的最粗历史表示}.
}
$$

只保留未来动作分布得到的“策略自我”是它的进一步商；完整代理自我还保留行动与世界共同演化的差异。

---

# 20. Agency completion 是历史接口上的闭包算子

设当前自我接口为

$$
m:\mathcal H\to M,
$$

代理画像接口为

$$
q_{\mathrm{ag}}(h)=[h]_{\mathrm{ag}}.
$$

## 定义 20.1（代理完成）

$$
\boxed{
C_{\mathrm{ag}}(m)
=
m\vee q_{\mathrm{ag}},
}
$$

即

$$
C_{\mathrm{ag}}(m)(h)
=
\bigl(m(h),[h]_{\mathrm{ag}}\bigr).
$$

其核满足

$$
K_{C_{\mathrm{ag}}(m)}
=
K_m\cap K_{\mathrm{ag}}.
$$

## 本文定理 20.1（最小代理充分精化）

$C_{\mathrm{ag}}(m)$ 是同时满足以下两项的最粗接口：

1. 精化当前接口 $m$；
2. 决定完整代理画像 $\Gamma$。

### 证明

若 $r$ 同时决定 $m$ 与 $\Gamma$，则

$$
K_r\subseteq K_m,
\qquad
K_r\subseteq K_{\mathrm{ag}}.
$$

所以

$$
K_r\subseteq K_m\cap K_{\mathrm{ag}}
=K_{C_{\mathrm{ag}}(m)}.
$$

由核因子化判据得到结论。∎

## 本文定理 20.2（闭包三律）

在接口精化偏序上：

```text
m ⪯ C_ag(m)；
m ⪯ n  ⇒  C_ag(m) ⪯ C_ag(n)；
C_ag(C_ag(m)) ≃ C_ag(m).
```

因此 $C_{\mathrm{ag}}$ 是 closure operator。其固定点满足

$$
C_{\mathrm{ag}}(m)\simeq m,
$$

恰表示当前自我状态已包含全部会改变未来交互行为的历史区别。

这只是相对于已申报环境输入、行动语法与未来协议族的闭合，不是无条件“完全自知”。

---

# 21. 合法动作丛、策略截面与无典范选择

设规范观察状态空间为 $Q$，动作类型为 $A$，合法关系为

$$
\operatorname{Legal}:Q\times A\to\operatorname{Prop}.
$$

定义动作纤维

$$
\mathcal A(q)=\{a:\operatorname{Legal}(q,a)\}
$$

和总空间

$$
E_{\mathcal A}
=
\{(q,a):a\in\mathcal A(q)\}.
$$

投影

$$
p:E_{\mathcal A}\to Q,
\qquad
p(q,a)=q
$$

称为合法动作丛；这里不预设局部平凡、光滑或向量丛结构。

确定性策略是截面

$$
s:Q\to E_{\mathcal A},
\qquad
p\circ s=\operatorname{id}_Q.
$$

随机策略则是支撑位于 $\mathcal A(q)$ 内的 Markov kernel。

所以：

$$
\boxed{
\text{Law}=\text{合法动作纤维与后果核},
\qquad
\text{Policy}=\text{动作丛上的截面}.
}
$$

## 本文定理 21.1（无等变确定性选择）

设群 $G$ 同时作用于状态与动作，并保持全部已申报结构。若存在状态 $q$ 与 $g\in G$ 满足

$$
gq=q,
$$

但 $g$ 在 $\mathcal A(q)$ 上无固定点，则不存在等变确定性截面

$$
s(gq)=g\,s(q).
$$

### 证明

若存在，则

$$
s(q)=s(gq)=g\,s(q),
$$

故 $s(q)$ 是固定动作，与前件矛盾。∎

这证明的是“裸结构没有自然指定唯一动作”，不是“任何更丰富完整状态都不能确定动作”。

---

# 22. 内生对称破缺与内部信息下界

令内部历史状态为 $m\in M$，策略改为

$$
s:Q\times M\to A.
$$

若 $G$ 也作用于 $M$，并存在等变映射

$$
u:M\to A,
$$

则

$$
s(q,m)=u(m)
$$

定义联合等变策略：

$$
s(gq,gm)=g\,s(q,m).
$$

因此，公开状态仍然对称，而内部状态提供了条件化的分支坐标。

## 本文定理 22.1（有限对称选择的记忆下界）

若有限群在有限动作集 $A$ 上传递作用，$M$ 是非空有限 $G$-集合，且存在等变映射 $u:M\to A$，则

$$
\boxed{|M|\ge|A|.}
$$

### 证明

$u(M)$ 是 $A$ 的非空 $G$-不变子集。传递性迫使 $u(M)=A$，故 $u$ 满射。∎

若动作由 $(Q,M)$ 确定，则

$$
H(A\mid Q)\le H(M\mid Q).
$$

当固定公开状态下有 $r$ 个均匀对称动作时：

$$
H(M\mid Q)\ge\log_2r.
$$

所以分支信息必来自至少一处：

```text
观察者历史；
外部隐藏变量；
随机种子。
```

主体性问题不是分支信息是否存在，而是这部分信息是否由观察者自己的历史形成、读取、修改并继承。

---

# 23. 自主性残差、理由绕过与作者性不可识别

设环境接口为

$$
e:\mathcal H\to E,
$$

完整策略画像为

$$
\Pi:\mathcal H\to P.
$$

## 定义 23.1（自主性残差）

$$
\mathcal R_{\mathrm{aut}}(e;\Pi)
=
\{(h,h'):e(h)=e(h'),\ \Pi(h)\ne\Pi(h')\}.
$$

它记录外部环境相同而策略不同的历史对。

若自我接口为 $m:\mathcal H\to M$，则联合接口 $e\vee m$ 决定策略，当且仅当

$$
\boxed{
\mathcal R_{\mathrm{aut}}(e;\Pi)\cap K_m=\varnothing.
}
$$

这说明自我接口的最低功能是切开环境无法解释的策略差异。

再设观察者认可的理由接口为

$$
r:\mathcal H\to R.
$$

## 定义 23.2（理由绕过残差）

$$
\mathcal B_r(\Pi)
=
\{(h,h'):r(h)=r(h'),\ \Pi(h)\ne\Pi(h')\}.
$$

有

$$
\mathcal B_r(\Pi)=\varnothing
\iff
\exists f,\ \Pi=f\circ r.
$$

因此可以区分：

- **说服**：新证据改变理由，策略随理由改变；
- **操控**：理由接口不变，策略却被绕过而改变；
- **强迫**：外部约束把安全动作集压成单点。

## 观察作者性不可识别反例

令 $U$ 为公平比特。

模型 S：

$$
M=U,
\qquad
A=M.
$$

模型 H：

$$
M=U,
\qquad
A=U,
$$

但模型 H 中没有 $M\to A$，二者只共享隐藏原因 $U$。两模型具有相同观察联合分布，却满足

$$
P_S(A\mid do(M))\ne P_H(A\mid do(M)).
$$

所以相关性、预测精度与行为一致性都不足以证明作者性；必须增加干预、自然实验、结构方程或来源账本。

---

# 24. 因果自主容量与作者变量所有权

固定环境值 $e$，内部状态干预产生动作信道

$$
K_e(a\mid m)
=
P(A=a\mid do(M=m),E=e).
$$

## 定义 24.1（因果自主容量）

有限模型中定义

$$
\boxed{
C_{\mathrm{aut}}(e)
=
\sup_{\nu\in\operatorname{Prob}(M)}I_\nu(M;A).
}
$$

## 本文定理 24.1（零容量判据）

$$
C_{\mathrm{aut}}(e)=0
$$

当且仅当所有输入行相同：

$$
\forall m,m',
\quad
K_e(\cdot\mid m)=K_e(\cdot\mid m').
$$

若存在两行不同，取只支撑于这两个输入的非退化分布即可得到正互信息。∎

但正容量仍可能来自外部植入的内部寄存器。要把决定变量 $Z$ 认作观察者所有，至少应要求：

```text
Readable：观察者能恢复其行动相关部分；
Writable：观察者过去行动能改变其未来值；
PolicyRelevant：干预 Z 会改变未来策略；
LedgerTraceable：Z 的形成与修改可追溯到观察、选择或承诺；
BoundaryClosed：其更新在申报输入后能在观察者边界内下降。
```

记这些条件的合取为

$$
\operatorname{Owned}_O(Z).
$$

内部空间位置不是主体所有权；一个体内寄存器仍可能只是外部遥控端点。

---

# 25. 自我边界：所有权闭包与自主核心

设候选内部变量全集为 $I$，种子自我变量为 $S_0\subseteq I$。设读取、改写、策略依赖与来源追溯算子均对集合包含单调：

$$
\operatorname{Read},
\operatorname{Write},
\operatorname{Dep},
\operatorname{Trace}:
\mathcal P(I)\to\mathcal P(I).
$$

## 定义 25.1（所有权扩张）

$$
\Gamma(S)
=
S\cup S_0
\cup\operatorname{Read}(S)
\cup\operatorname{Write}(S)
\cup\operatorname{Dep}(S)
\cup\operatorname{Trace}(S).
$$

它单调且扩张，因此在幂集完备格上存在最小固定点

$$
\boxed{
\operatorname{Own}(S_0)=\mu S.\Gamma(S).
}
$$

它是包含种子自我并对行动相关依赖闭合的最小边界。

所有权扩张可能不断吞入环境，因此还需反向剪枝。令 $\operatorname{Eligible}(S)$ 表示在 $S$ 内可读、可更新、可审计并可追溯的变量，假设它单调，定义

$$
\Psi(S)=S\cap\operatorname{Eligible}(S).
$$

它单调且收缩，因此存在最大固定点

$$
\boxed{
\operatorname{Core}(I)=\nu S.\Psi(S).
}
$$

## 定义 25.2（双固定自我边界）

稳定自我边界满足

$$
\boxed{S=\Gamma(S)=\Psi(S).}
$$

它既不遗漏行动与自我更新所需的依赖，又不包含只能由边界外隐藏机制维持的伪内部变量。

若

$$
\operatorname{Own}(S_0)\not\subseteq\operatorname{Core}(I),
$$

则完整解释行动所需的某些变量无法纳入自主闭合边界；这构成外部控制、自我模型不完备或边界错误的可审计见证。

---

# 26. 透明自我预测三难与反身固定点

设动作集 $A$ 存在无不动点映射

$$
\delta:A\to A,
\qquad
\delta(a)\ne a.
$$

行动前公开预测为

$$
p:S\to A,
$$

实际行动为 $a:S\to A$。若观察者采用反预测响应

$$
a(s)=\delta(p(s)),
$$

则不存在任何状态满足 $p(s)=a(s)$。

### 证明

若相等，则

$$
p(s)=\delta(p(s)),
$$

与无不动点矛盾。∎

因此以下三项不能同时成立：

```text
预测完全正确；
预测在行动前对观察者透明可用；
观察者能够并承诺采取无固定点反制。
```

这不排除隐藏于观察者之外的预测器正确预测行为；它排除的是“可被反预测主体作为输入使用的完美公开预测”。

更一般地，若响应为

$$
a=R(p),
$$

稳定公开预测存在，当且仅当

$$
\operatorname{Fix}(R)\ne\varnothing.
$$

所以成熟意志未必表现为最大不可预测性。稳定履行承诺可构成反身固定点，并且完全可预测而不必是外部强迫。

---

# 27. 元策略、价值—策略平衡与事实—价值缺口

普通策略为

$$
\pi_t:Q\to\operatorname{Dist}(A).
$$

令策略空间为 $\mathcal P$，记忆、价值和承诺状态为 $M$，元更新器为

$$
\mathcal U:M\times\mathcal P\times Y\to M\times\mathcal P.
$$

更新：

$$
(m_{t+1},\pi_{t+1})
=
\mathcal U(m_t,\pi_t,y_t).
$$

一阶自由选择当前动作；二阶自由修改以后怎样选择。

若价值状态为 $v_t\in\mathcal V$，策略响应为 $\pi_t=B(v_t)$，经验反过来修改价值：

$$
v_{t+1}=E(v_t,\pi_t,y_t,\Lambda_t),
$$

则联合更新为

$$
(v_{t+1},\pi_{t+1})=\mathcal R(v_t,\pi_t).
$$

## 定义 27.1（反身价值—策略平衡）

$$
\mathcal R(v_*,\pi_*)=(v_*,\pi_*).
$$

它表示当前策略表达当前价值，而观察者理解该策略及后果后仍认可这一价值—策略对。

预测完备不能自动产生此平衡。即使全部后果分布已知，不同损失函数仍可产生相反唯一最优动作；事实接口只决定“会怎样”，不能从自身推出唯一“应怎样”。

承诺的更深作用是改写元更新器：

$$
\Lambda\mapsto\mathcal U_\Lambda.
$$

它可以删除某些策略固定点、创造新固定点、改变吸引盆，并把短期游移变成长程稳定人格。

---

# 28. 策略 holonomy、来源偏序与身份 DAG

设公开状态沿路径

$$
\gamma:q_0\to q_1\to\cdots\to q_n
$$

变化，记忆运输为

$$
U_{q_i\to q_{i+1}}:M_{q_i}\to M_{q_{i+1}}.
$$

当 $q_n=q_0$ 时定义

$$
\operatorname{Hol}_\gamma
=
U_{q_{n-1}\to q_n}\circ\cdots\circ U_{q_0\to q_1}.
$$

若

$$
\operatorname{Hol}_\gamma(m)\ne m,
$$

则公开情境回到原点，选择者却已改变。非平凡 holonomy 情形下，历史不是附加缓存，而是使策略成为函数所必需的坐标。

身份也不宜只写成对称等价关系。设历史前缀关系为 $h\preceq h'$，定义作者连续关系 $h\rightsquigarrow h'$：

1. $h'$ 由 $h$ 追加得到；
2. 中间每次策略或价值修改均由当时主体授权；
3. 修改进入账本；
4. 无未授权身份接管。

在授权复合闭合时，$\rightsquigarrow$ 是偏序：反身、传递，且由前缀反对称性得到反对称。

复制导致一个历史拥有多个后继；合并导致多个历史形成联合主体。因此最一般身份结构是带授权、分叉、合并和来源证明的历史 DAG，而不是单线或静态等价类。

---

# 29. 承诺深度、自由深度与代理视界

设历史 $h$ 的相容未来计划集为 $\Omega_h$。选择动作 $a$ 后，计划柱集为

$$
\Omega_{h,a}
=
\{\omega\in\Omega_h:A_h(\omega)=a\}.
$$

有限情形定义承诺深度

$$
B(h,a)
=
\log_2|\Omega_h|-
\log_2|\Omega_{h,a}|.
$$

沿历史 $h_0\to\cdots\to h_n$，若每一步恰对应所选计划柱集，则

$$
\boxed{
\sum_{t=0}^{n-1}B(h_t,a_t)
=
\log_2|\Omega_{h_0}|-
\log_2|\Omega_{h_n}|.
}
$$

选择把未来可能性体积转换成追加式历史信息。

对目标时刻 $t$，令

$$
B_t(h_\tau)
=
\{A_t(\omega):\omega\text{ 从 }h_\tau\text{ 延伸至 }t\}.
$$

若 $h_\tau\preceq h_{\tau'}$，则

$$
B_t(h_{\tau'})\subseteq B_t(h_\tau).
$$

定义最近真实分支时刻

$$
\tau^*(t)
=
\max\{\tau\le t:|B_t(h_\tau)|\ge2\}
$$

和自由深度

$$
\boxed{d_{\mathrm{free}}(t)=t-\tau^*(t).}
$$

当前只有一个动作，不表示它从未自由；它可能由更早承诺锁定。

再令当前承诺为 $C_t$，未来自我状态为 $M_{t+k}$，定义

$$
J_k=I(C_t;M_{t+k}\mid E).
$$

若记忆形成 Markov 信道，则 $J_{k+1}\le J_k$。定义 $\varepsilon$-代理视界

$$
\boxed{
h_\varepsilon(C_t)=\sup\{k:J_k\ge\varepsilon\}.
}
$$

意志强度不仅取决于此刻选择了什么，还取决于这一选择能在未来自己中存活多久。

---

# 30. 自我治理的根—环边界与审计不完备

设有限规则集合为 $R$，边 $r_i\to r_j$ 表示规则 $r_i$ 有权修改 $r_j$。

## 本文定理 30.1（有限宪法根—环二分）

有限授权图至少满足一项：

1. 存在没有任何规则有权修改的根规则；
2. 授权图含有向环。

### 证明

若无根，则每个顶点至少有一条入边。不断沿入边逆行，有限性迫使某顶点重复，从而形成有向环。∎

所以有限治理无法同时满足“全部规则可修改”与“授权完全无环”。冻结根提供稳定性但限制最高层修订；授权环提供内生修订但引入自指与固定点风险。

若自我修改语言图灵完备，则任意非平凡外延行为性质——例如永远保持某承诺、永不把控制权交给外部——不存在对所有程序都正确终止的通用判定器，否则可归约停机问题。

因此：

```text
完全开放的自我修改语言 → 通用安全审计不完备；
完全机械可判的自我修改 → 必须限制表达能力。
```

可行治理只能在 proof-carrying modification、受限能力语言、运行时监控、外部裁决与不完备审查之间组合。

---

# 31. 封闭有限主体的周期化与新颖性边界

设主体内部元状态 $z_t=(m_t,\pi_t)$ 位于有限集合，且在固定环境中确定更新：

$$
z_{t+1}=F(z_t).
$$

## 本文定理 31.1（最终周期化）

任意轨迹最终进入周期。

### 证明

有限状态序列中必有两个时刻状态相同；确定更新使以后轨迹逐项重复。∎

若行动由固定函数 $a_t=g(z_t)$ 给出，则行动轨迹也最终周期。长度 $n$ 前缀可由固定程序、初态和整数 $n$ 生成，因此其描述复杂度至多为

$$
K(a_{<n})\le K(n)+O(1)=O(\log n).
$$

所以有限、封闭、确定主体可以产生很长的表面复杂轨迹，却不能持续注入与时间成正比的不可约新信息。

长期正新颖性率至少需要：

```text
开放环境输入；
随机输入；
无界记忆增长；
无限维状态；
扩展中的动作或语言空间。
```

随机输入只提供熵，不自动提供有效逻辑；知识还要求验证、压缩、去重、整合与保存。

---

# 32. 集体作者联盟与委托瓶颈

设成员集合为 $N=\{1,\ldots,n\}$，成员内部状态为 $M_i$，集体策略画像为 $\Pi$。

## 定义 32.1（策略充分联盟）

联盟 $C\subseteq N$ 充分，当且仅当存在 $f_C$ 使

$$
\Pi=f_C(M_C,E).
$$

若 $C$ 充分且 $C\subseteq D$，则 $D$ 也充分；故充分联盟构成幂集格中的上闭集。其极小元素形成反链。

定义最小作者联盟阶数

$$
\boxed{
r_{\mathrm{coll}}
=
\min\{|C|:C\text{ 策略充分}\}.
}
$$

XOR 例中

$$
A=M_1\oplus M_2
$$

满足每个单成员与 $A$ 的互信息为零，但联合状态完全决定 $A$，所以 $r_{\mathrm{coll}}=2$。集体作者性可以严格不可约为任何个人。

委托链则有不同结构。设委托接口

$$
H_1:U_1\to Z
$$

和执行接口

$$
H_2:Z\to Y.
$$

总代理为 $H_2H_1$，并有

$$
\boxed{
\operatorname{rank}(H_2H_1)
=
\operatorname{rank}H_1
-
\dim(\operatorname{im}H_1\cap\ker H_2).
}
$$

交集是已传给执行者、却无法继续成为世界后果的委托方向。任务作者性与实施作者性必须分别记账。

---

# 33. 策略 cocycle、喉部 cocycle 与势函数障碍

设增强观察状态为 $z=(q,m)$。合法转移边 $e:z\to z'$ 携带隐藏分量增量

$$
c(e)\in\mathcal K,
\qquad
\mathcal K=K_\infty/\Delta(\mathbb Z),
$$

其中该商仍是前文登记的条件接口，不冒充现成 Lean 类型。

对路径 $\gamma=e_1\cdots e_n$ 定义

$$
C(\gamma)=\sum_i c(e_i).
$$

它满足路径拼接加法。

## 本文定理 33.1（零环和与势函数等价）

在连通路径群胚中，若反向边满足 $c(e^{-1})=-c(e)$，则以下等价：

1. 每条闭合路径 $\gamma:z\to z$ 满足 $C(\gamma)=0$；
2. 存在势函数 $\Phi:Z\to\mathcal K$，使

   $$
   c(e)=\Phi(z')-\Phi(z).
   $$

### 证明

势函数情形沿闭环望远镜求和为零。反向选基点 $z_0$，定义 $\Phi(z)$ 为任一从 $z_0$ 到 $z$ 的路径积分；零环和保证路径无关。∎

因此增强主体闭环具有非零隐藏位移，当且仅当 cocycle 不是 exact。

必须区分：公开状态回到原点但记忆 holonomy 非零，只是历史泵浦；只有公开状态和策略状态均回到原点而隐藏位移非零，才是内禀喉部泵浦。

---

# 34. 动作顺序曲率与策略—喉部半直积

设动作 $a,b$ 的增强状态更新为 $T_a,T_b$，隐藏增量为 $c(a,z),c(b,z)$。定义离散曲率

$$
\boxed{
\Omega_{a,b}(z)
=
c(a,z)+c(b,T_az)
-c(b,z)-c(a,T_bz).
}
$$

若 $T_aT_bz=T_bT_az$ 且 $c=d\Phi$，则 $\Omega_{a,b}(z)=0$。所以非零曲率表示动作顺序携带不能由单一状态势消除的隐藏信息。

若策略 holonomy 群 $H$ 作用于 $\mathcal K$：

$$
\alpha:H\to\operatorname{Aut}(\mathcal K),
$$

则组合输运位于半直积

$$
\boxed{\mathcal K\rtimes_\alpha H}
$$

中，其乘法为

$$
(k_2,h_2)(k_1,h_1)
=
(k_2+\alpha_{h_2}(k_1),h_2h_1).
$$

即使 $\mathcal K$ 阿贝尔，半直积也可能非交换：

$$
[(0,h),(k,e)]
=(\alpha_h(k)-k,e).
$$

先改变选择者再执行喉部动作，与先执行动作再改变选择者，可以产生不同隐藏结果。

---

# 35. 线性受控观察者：可达空间与不可观测空间

设有限维内积空间 $V$ 上有受控动力学

$$
x_{t+1}=Tx_t+B_Ou_t+B_Ee_t,
$$

读出为

$$
y_t=Cx_t.
$$

其中 $B_O$ 是观察者拥有的控制通道，$B_E$ 是环境通道。

定义永久不可观测子空间

$$
\boxed{
N_\infty
=
\bigcap_{n\ge0}\ker(CT^n),
}
$$

自我可达子空间

$$
\boxed{
R_O
=
\operatorname{span}_{n\ge0}\operatorname{ran}(T^nB_O),
}
$$

环境可达子空间

$$
R_E
=
\operatorname{span}_{n\ge0}\operatorname{ran}(T^nB_E).
$$

三者均对 $T$ 前向不变。

这里出现两个方向相反的闭包：

```text
N∞ = 能永久保持隐藏的最大不变方向；
R_O = 能由观察者行动生成的最小不变方向。
```

前者是可观测闭包的 kernel 面，后者是控制闭包的 image 面。

---

# 36. 可观测与可控 Gramian

取 $0<\beta<1$ 且满足收敛条件。定义

$$
W_o
=
\sum_{n\ge0}\beta^n(T^*)^nC^*CT^n,
$$

$$
W_c^O
=
\sum_{n\ge0}\beta^nT^nB_OB_O^*(T^*)^n.
$$

有能量恒等式

$$
\langle x,W_ox\rangle
=
\sum_{n\ge0}\beta^n\|CT^nx\|^2,
$$

$$
\langle x,W_c^Ox\rangle
=
\sum_{n\ge0}\beta^n\|B_O^*(T^*)^nx\|^2.
$$

因此

$$
\boxed{
\ker W_o=N_\infty,
\qquad
\ker W_c^O=R_O^\perp,
\qquad
\operatorname{ran}W_c^O=R_O.
}
$$

并满足双 Lyapunov 方程

$$
W_o=C^*C+\beta T^*W_oT,
$$

$$
W_c^O=B_OB_O^*+\beta TW_c^OT^*.
$$

观察完成与行动完成由此形成状态—效应对偶。

---

# 37. 规范代理商与两条正合列

完整行为商为 $V/N_\infty$。观察者在其中真正拥有的方向是自我可达空间的像。

## 定义 37.1（规范代理状态空间）

$$
\boxed{
\mathsf{Agt}_O
=
\frac{R_O+N_\infty}{N_\infty}
\cong
\frac{R_O}{R_O\cap N_\infty}.
}
$$

其维数为

$$
\boxed{
\dim\mathsf{Agt}_O
=
\dim R_O-
\dim(R_O\cap N_\infty).
}
$$

它恰好保存既能由观察者改变、又会在未来留下可观察差异的状态方向。

定义静默控制

$$
\mathsf{Silent}_O=R_O\cap N_\infty,
$$

得到正合列

$$
0\to\mathsf{Silent}_O
\to R_O
\to\mathsf{Agt}_O
\to0.
$$

行为商中非自我可达的部分为

$$
\mathsf{Imposed}_O
=
\frac{V/N_\infty}{\mathsf{Agt}_O}
\cong
\frac{V}{R_O+N_\infty},
$$

并有

$$
0\to\mathsf{Agt}_O
\to V/N_\infty
\to\mathsf{Imposed}_O
\to0.
$$

## 本文定理 37.1（精确代理闭合）

以下等价：

```text
R_O → V/N∞ 的自然映射是同构；
R_O∩N∞=0 且 R_O+N∞=V；
V=R_O⊕N∞.
```

此时每个行为状态具有唯一自我可达代表元。

---

# 38. 作者性 Gramian、代理 Hankel 与最小实现

定义

$$
L_O=W_o^{1/2}(W_c^O)^{1/2}
$$

和作者性 Gramian

$$
\boxed{
G_O
=
W_o^{1/2}W_c^OW_o^{1/2}.
}
$$

## 本文定理 38.1（作者性秩）

$$
\boxed{
\operatorname{rank}G_O
=
\dim\mathsf{Agt}_O.
}
$$

### 证明

$(W_c^O)^{1/2}$ 的像是 $R_O$，$W_o^{1/2}$ 的核是 $N_\infty$。故复合在 $R_O$ 上丢失的恰是 $R_O\cap N_\infty$。∎

定义折扣观察算子 $\mathcal O_\beta$ 与自我可达算子 $\mathcal C_{\beta,O}$：

$$
\mathcal O_\beta x=(\beta^{n/2}CT^nx)_{n\ge0},
$$

$$
\mathcal C_{\beta,O}(u)
=
\sum_{n\ge0}\beta^{n/2}T^nB_Ou_n.
$$

代理 Hankel 算子为

$$
\boxed{
\mathcal H_O
=
\mathcal O_\beta\mathcal C_{\beta,O}.
}
$$

其秩满足

$$
\boxed{
\operatorname{rank}\mathcal H_O
=
\dim\mathsf{Agt}_O.
}
$$

因此任何精确实现同一“自身过去控制到未来读出”映射的有限维系统，状态维数至少为该秩；可达且可观测实现恰达到它。这给“最小操作自我”一个系统论定义。

---

# 39. 最小自我修改能量与代理条件数

对 $r\in R_O$ 定义达到该状态的最低控制能量

$$
E_O(r)
=
\inf_{\mathcal C_Ou=r}\|u\|^2.
$$

## 本文定理 39.1（伪逆能量公式）

$$
\boxed{
E_O(r)
=
\langle r,(W_c^O)^\dagger r\rangle.
}
$$

同一行为商类的代表元可相差静默方向，故操作能量应进一步取

$$
E_O([r])
=
\inf_{n\in R_O\cap N_\infty}E_O(r+n).
$$

令 $\sigma_1\ge\cdots\ge\sigma_s>0$ 为 $L_O$ 或 $\mathcal H_O$ 的非零奇异值，定义

$$
\kappa_{\mathrm{ag}}=\frac{\sigma_1}{\sigma_s}.
$$

即使代理商非零，若最小奇异值极小，关键自我方向仍可能需要巨大能量、极低噪声或很长时间才能稳定使用。

所以必须区分：

```text
exact agency；
conditioned agency；
physically realizable agency.
```

---

# 40. 外部控制重叠与来源可识别性

令自我输入与外部输入到未来行为的算子分别为

$$
\mathcal H_O:\mathcal U_O\to\mathcal Y,
\qquad
\mathcal H_E:\mathcal U_E\to\mathcal Y.
$$

记

$$
S_O=\operatorname{im}\mathcal H_O,
\qquad
S_E=\operatorname{im}\mathcal H_E.
$$

## 本文定理 40.1（来源贡献唯一分解）

每个 $y\in S_O+S_E$ 的分解

$$
y=y_O+y_E
$$

唯一，当且仅当

$$
\boxed{S_O\cap S_E=0.}
$$

若交非零，则对任意 $z$ 属于交，可用 $(y_O+z,y_E-z)$ 构造另一分解。∎

定义来源求和算子

$$
J:S_O\oplus S_E\to\mathcal Y,
\qquad
J(y_O,y_E)=y_O+y_E.
$$

其核同构于 $S_O\cap S_E$。在 $J$ 单射时可定义来源条件数

$$
\kappa_{\mathrm{prov}}
=
\sigma_{\max}(J)/\sigma_{\min}(J).
$$

交为零只保证精确可识别；若两子空间几乎平行，来源分解仍对噪声脆弱。

定义抗外部复制商

$$
\boxed{
\mathsf{Unique}_O
=
S_O/(S_O\cap S_E).
}
$$

它只相对于当前申报的外部通道定义，不是绝对自由空间。

---

# 41. 资源受限代理容量与外部噪声

考虑高斯输入—输出模型

$$
Y=HU+\Xi,
\qquad
\Xi\sim\mathcal N(0,\Sigma),
\qquad
\Sigma\succ0,
$$

其中 $H=\mathcal H_O$，输入协方差 $S\succeq0$ 满足 $\operatorname{tr}S\le P$。

定义代理信道容量

$$
\boxed{
C_O(P)
=
\sup_S
\frac12\log_2\det
\bigl(I+\Sigma^{-1/2}HSH^*\Sigma^{-1/2}\bigr).
}
$$

## 本文定理 41.1（零容量判据）

对 $P>0$：

$$
C_O(P)=0
\iff H=0
\iff\mathsf{Agt}_O=0.
$$

若 $H\ne0$，选择沿非零方向的秩一协方差即可得到正容量。∎

若外部独立扰动经 $H_E$ 注入，等效噪声变为

$$
\Sigma_{\mathrm{eff}}
=
\Sigma+H_ES_EH_E^*.
$$

当 $S_E'\succeq S_E$ 时，容量单调不增。

统计噪声之外，外部还能主动取消任何属于 $S_O\cap S_E$ 的行为方向。抗取消代理商正是

$$
\boxed{
(S_O+S_E)/S_E
\cong
S_O/(S_O\cap S_E).
}
$$

---

# 42. 近似自我谱、平衡坐标与鲁棒代理秩

令代理 Hankel 奇异值为

$$
\sigma_1\ge\cdots\ge\sigma_r>0.
$$

## 定义 42.1（$\varepsilon$-自我维数）

$$
\boxed{
d_\varepsilon
=
\min\{k:\exists K,\ \operatorname{rank}K\le k,
\ \|\mathcal H_O-K\|\le\varepsilon\}.
}
$$

由最佳低秩逼近定理：

$$
\boxed{d_\varepsilon=\#\{i:\sigma_i>\varepsilon\}.}
$$

任意 $k$ 维行为模型的最坏误差至少为 $\sigma_{k+1}$；截断奇异值展开达到该界。

在最小可控—可观测实现上可选平衡坐标，使

$$
W_o=W_c^O=\operatorname{diag}(\sigma_1,\ldots,\sigma_r).
$$

高奇异值方向是容易由自身修改、又强烈影响未来的代理核心；低奇异值方向是可在容许误差下压缩的代理边缘。

若模型扰动满足 $\|\Delta\|\le\delta$，则

$$
|\sigma_i(\mathcal H_O+\Delta)-\sigma_i(\mathcal H_O)|\le\delta.
$$

定义鲁棒代理秩

$$
\boxed{r_{\mathrm{rob}}(\delta)=\#\{i:\sigma_i>\delta\}.}
$$

精确主体方向若小于模型误差，就不能被稳定宣称存在。

---

# 43. 非线性局部代理与 Lie 括号方向

对非线性系统

$$
x_{t+1}=F_t(x_t,u_t,e_t),
\qquad
y_t=h_t(x_t),
$$

沿实际轨迹线性化：

$$
\delta x_{t+1}
=A_t\delta x_t+B_t^O\delta u_t+B_t^E\delta e_t,
$$

$$
\delta y_t=C_t\delta x_t.
$$

将有限控制扰动映射到未来输出扰动得到 Jacobian $\mathcal J_{O,N}$，其块为

$$
\frac{\partial y_k}{\partial u_j}
=
C_kA_{k-1}\cdots A_{j+1}B_j^O.
$$

定义局部代理秩

$$
\boxed{r_{\mathrm{loc}}=\operatorname{rank}\mathcal J_{O,N}.}
$$

若秩在邻域恒定，则行为等价控制纤维局部形成余维 $r_{\mathrm{loc}}$ 的子流形。

连续时间控制仿射系统

$$
\dot x=f_0(x)+\sum_i u_if_i(x)
$$

中，单个方向可能满足 $dh(f_i)=dh(f_j)=0$，而动作小回路产生二阶 Lie 括号位移

$$
x\mapsto x+\varepsilon^2[f_i,f_j](x)+O(\varepsilon^3).
$$

若

$$
dh([f_i,f_j])\ne0,
$$

则任一单步一阶不可见，但特定顺序组合产生可见代理方向。动作词本身可以创造单个动作不具备的能力。

---

# 44. 有限深度代理谱

定义有限可达与可观测矩阵

$$
\mathcal C_N=[B_O,TB_O,\ldots,T^{N-1}B_O],
$$

$$
\mathcal O_N=
\begin{bmatrix}C\\CT\\\vdots\\CT^{N-1}\end{bmatrix},
$$

以及有限 Hankel 算子

$$
\mathcal H_N=\mathcal O_N\mathcal C_N.
$$

令

$$
r_N=\operatorname{rank}\mathcal H_N.
$$

则

$$
\boxed{r_N\le r_{N+1}.}
$$

有限维中它最终稳定于 $\dim\mathsf{Agt}_O$。定义代理完成深度

$$
\boxed{
d_{\mathrm{ag}}
=
\min\{N:r_N=\dim\mathsf{Agt}_O\}
}
$$

和新增代理谱

$$
\Delta r_N=r_N-r_{N-1}.
$$

这表示观察者必须考虑多长的过去控制与未来读出窗口，才能显现全部有效行动维度。有些能力立即可见，有些必须经过长时间传播才形成差异。

---

# 45. 决定—执行—世界—记录的信息结算

设内部决定 $D$ 经执行接口成为控制 $U$，产生世界结果 $Y$，再进入记录 $R$：

$$
D\to U\to Y\to R
$$

条件于公开状态 $Q$ 构成 Markov 链。

链式法则与数据处理给出：

$$
\boxed{
\begin{aligned}
H(D\mid Q)
={}&H(D\mid U,Q)\\
&+[I(D;U\mid Q)-I(D;Y\mid Q)]\\
&+[I(D;Y\mid Q)-I(D;R\mid Q)]\\
&+I(D;R\mid Q).
\end{aligned}
}
$$

四项均非负，分别解释为：

```text
未执行的决定信息；
被世界动力学抹除的决定信息；
被记录接口抹除的决定信息；
最终保留的作者签名。
```

线性情形下，若决定接口为 $K:D\to U$，世界行为接口为 $H:U\to Y$，则有效决定商为

$$
\mathsf{DecisionAgt}=D/\ker(HK).
$$

并有

$$
\ker(HK)/\ker K
\cong
\operatorname{im}K\cap\ker H.
$$

所以“有意愿”“被执行”“产生后果”“进入记录”是四个不同层次。

---

# 46. 隐蔽喉部输运与账本审计

设完整控制历史空间为 $\mathcal U$，公开行为映射为

$$
H:\mathcal U\to\mathcal Y,
$$

喉部分量输运为

$$
K:\mathcal U\to\mathcal K.
$$

定义公开静默控制 $\ker H$ 与隐蔽喉部输运群

$$
\boxed{
\mathsf{CovertThroat}=K(\ker H).
}
$$

## 本文定理 46.1（公开恢复判据）

以下等价：

1. 存在 $\bar K:\operatorname{im}H\to\mathcal K$ 使 $K=\bar K\circ H$；
2. $\ker H\subseteq\ker K$；
3. $\mathsf{CovertThroat}=0$。

这是标准核因子化判据。∎

若加入动作账本

$$
L:\mathcal U\to\Lambda,
$$

联合接口为 $(H,L)$，不可恢复输运缩为

$$
K(\ker H\cap\ker L)
\subseteq
K(\ker H).
$$

所以增加账本不能增加来源歧义，只能保持或缩小它；但账本不改变已经发生的本体输运，只改善“谁做了什么、因此隐藏分量如何变化”的可恢复性。

---

# 47. 无限维不可压缩余量与粗粒化单调性

若代理 Hankel 算子作用于无限维 Hilbert 空间，定义本质范数

$$
\boxed{
\|\mathcal H_O\|_{\mathrm{ess}}
=
\inf_{\operatorname{rank}K<\infty}
\|\mathcal H_O-K\|.
}
$$

若该值正，则任何有限维自我模型都至少具有同样大的算子误差。定义

$$
R_{\mathrm{inf}}=\|\mathcal H_O\|_{\mathrm{ess}}
$$

为不可压缩代理余量。有限记忆可任意逼近主体不是自动真理，而取决于算子的紧致性。

若限制控制接口 $S:U'\to U$，粗化输出 $P:Y\to Y'$，新代理算子为

$$
H'=PHS.
$$

则

$$
\operatorname{rank}H'\le\operatorname{rank}H.
$$

当 $\|P\|,\|S\|\le1$ 时，

$$
\sigma_i(PHS)\le\sigma_i(H).
$$

确定后处理还满足数据处理不等式。删除控制、压缩读出或遗忘记录都不能创造新的操作代理能力。

---

# 48. 自由保持核与 meta-agency

设 $S_{\mathrm{ag}}\subseteq X$ 为满足最低主体条件的安全区域，例如：

```text
代理商非零；
策略仍可修改；
关键账本仍可访问；
作者状态仍可读写；
控制权未全部不可逆交给外部。
```

定义安全前驱算子

$$
\operatorname{Pre}_S(Z)
=
\{x\in S:\exists a\in\mathcal A(x),\ T(x,a)\in Z\}.
$$

## 定义 48.1（主体生存核）

$$
\boxed{
\mathsf{FreeKernel}
=
\nu Z.\operatorname{Pre}_{S_{\mathrm{ag}}}(Z).
}
$$

它是安全区域中最大的受控前向不变集合。

有限状态下从 $Z_0=S_{\mathrm{ag}}$ 迭代

$$
Z_{n+1}=\operatorname{Pre}_{S_{\mathrm{ag}}}(Z_n)
$$

最终稳定于该核。

因此存在三类状态：

```text
当前自由且可无限保持；
当前自由但任何策略最终都会失去主体能力；
当前已不满足主体条件。
```

若 $x\in\mathsf{FreeKernel}$，而某动作把后继送出该核，则它是自我放弃动作。自由选择不等于选择保持自由。

定义 meta-agency 为保持、扩大或恢复未来代理能力的能力。它是高于即时动作数的治理自由。

---

# 49. 操作代理存在的六重等价

在线性系统

$$
x_{t+1}=Tx_t+B_Ou_t,
\qquad y_t=Cx_t
$$

中，以下条件等价：

$$
\boxed{
\begin{aligned}
\mathrm{(i)}\;&\mathsf{Agt}_O\ne0;\\
\mathrm{(ii)}\;&R_O\not\subseteq N_\infty;\\
\mathrm{(iii)}\;&\exists n\ge0,\ CT^nB_O\ne0;\\
\mathrm{(iv)}\;&\mathcal H_O\ne0;\\
\mathrm{(v)}\;&G_O\ne0;\\
\mathrm{(vi)}\;&\forall P>0,\ C_O(P)>0.
\end{aligned}
}
$$

### 证明

代理商非零等价于存在自我可达方向不在永久不可观测核中。$R_O$ 由 $T^jB_Ou$ 张成，故等价于某个 $CT^{n+j}B_Ou$ 非零；这又等价于输入—输出 Hankel 非零。前文秩等式给出 $G_O$ 非零等价；高斯容量零恰当且仅当输入—输出算子为零。∎

该定理只证明存在自身可执行控制会在未来造成可见差异；它不自动证明来源所有权、理由响应、策略可修改或强本体分岔。

---

# 50. 自由与主体的九级阶梯

可以把结构按强度排列为：

1. **动作存在**：$\mathcal A(x)\ne\varnothing$；
2. **有效分岔**：存在后果真正不同的动作；
3. **非典范性**：裸结构不提供保持全部对称性的唯一选择；
4. **操作代理**：$\mathsf{Agt}_O\ne0$；
5. **稳健代理**：在噪声和模型误差下仍有非零代理秩；
6. **来源代理**：自身行为不能被外部通道完全复制，或账本能恢复来源；
7. **策略代理**：观察者能修改以后怎样选择；
8. **历时与自由保持**：过去选择进入未来自我，且状态位于 $\mathsf{FreeKernel}$；
9. **本体自由**：给定完整宇宙过去仍有未被隐藏变量预选的真实分岔。

当前理论严格给出前八层的形式结构。第九层需要关于完整状态空间与真实转移关系的独立本体前件。

必须保持以下非蕴含：

```text
随机性 ⇏ 作者性；
不可预测 ⇏ 自由；
可预测 ⇏ 不自由；
内部影响 ⇏ 所有权；
代理商非零 ⇏ 来源可识别；
策略可修改 ⇏ 身份连续；
身份连续 ⇏ 本体分岔。
```

---

# 51. 建议 Lean 模块树

```text
D5/S3/Observer/Agency/Core/
  AgentiveProfile.lean
  AgentiveHistoryQuotient.lean
  AgencyCompletion.lean
  AgencyCompletionClosure.lean
  AutonomyResidual.lean
  ReasonBypassResidual.lean

D5/S3/Observer/Agency/Choice/
  LegalActionBundle.lean
  DeterministicPolicySection.lean
  EquivariantSelectorObstruction.lean
  EndogenousSymmetryBreaking.lean
  SymmetricChoiceMemoryLowerBound.lean

D5/S3/Observer/Agency/Ownership/
  CausalAutonomyCapacity.lean
  OwnershipClosure.lean
  AutonomousCore.lean
  StableSelfBoundary.lean
  ObservationalAuthorshipCountermodel.lean

D5/S3/Observer/Agency/Reflexive/
  TransparentPredictionDiagonal.lean
  ResponseFixedPoint.lean
  MetaPolicyDynamics.lean
  ValuePolicyEquilibrium.lean
  PolicyHolonomy.lean
  ProvenanceOrder.lean

D5/S3/Observer/Agency/Linear/
  OwnedReachableSubspace.lean
  ExternalReachableSubspace.lean
  DiscountedControllabilityGramian.lean
  AgentiveBehaviorQuotient.lean
  SilentControlExactSequence.lean
  ImposedBehaviorExactSequence.lean
  AuthorabilityGramian.lean
  AgencyHankelOperator.lean
  MinimumRevisionEnergy.lean

D5/S3/Observer/Agency/Provenance/
  ObservableControlOverlap.lean
  ProvenanceDecomposition.lean
  ProvenanceConditionNumber.lean
  UniqueOwnedBehaviorQuotient.lean
  DecisionExecutionRecordLedger.lean

D5/S3/Observer/Agency/Approximation/
  ApproximateSelfDimension.lean
  AgencyBalancedCoordinates.lean
  RobustAgencyRank.lean
  EssentialAgencyResidual.lean
  CoarseGrainingMonotonicity.lean

D5/S3/Observer/Agency/Throat/
  StrategyPathCocycle.lean
  ThroatComponentCocycle.lean
  ClosedLoopPotentialCriterion.lean
  ActionOrderCurvature.lean
  StrategyThroatSemidirect.lean
  CovertThroatTransport.lean
  LedgerThroatAudit.lean

D5/S3/Observer/Agency/Viability/
  AgencySafeSet.lean
  AgencyViabilityKernel.lean
  FreedomPreservingPolicy.lean
  SelfAbandoningAction.lean
```

建议优先闭合低依赖、高区分度结果：

```text
agentive_profile_kernel
agentive_completion_least
agency_completion_idempotent
no_equivariant_selector_of_fixed_state
symmetric_choice_memory_card_lower_bound
reason_sufficient_iff_factors
stable_self_boundary_fixed
transparent_counterprediction_impossible
finite_constitution_root_or_cycle
agentiveQuotient_equiv_reachable_mod_silent
agentiveQuotient_dim
authorabilityGramian_rank
agencyHankel_rank
source_decomposition_unique_iff_disjoint
covert_throat_zero_iff_factors
agency_viability_greatest
operational_agency_sixfold_equiv
```

---

# 52. 追加严格非断言

本增订不声称：

1. 无典范策略等价于不存在任何确定策略；
2. 策略空间大、动作熵高或行为不可预测自动等于自由意志；
3. 内部状态与行动相关自动证明内部状态具有因果控制；
4. 任意体内变量都属于观察者自我；
5. 因果自主容量正自动建立道德责任；
6. 代理因果状态商等于意识、现象自我或全部人格；
7. 完整预测分布能够从纯事实自动生成唯一价值排序；
8. 反预测障碍证明宇宙整体不可预测或非决定；
9. 反身固定点证明某项承诺合理、善或不可修改；
10. 策略 holonomy 必然存在于现实人类或量子观察者；
11. 历史来源偏序单独解决人格同一性的全部哲学问题；
12. 图灵完备自我修改完全不可治理；结论只是否定完备总判定器；
13. 有限封闭周期化排除开放系统的长期新颖性；
14. 集体联盟阶数是唯一合理的集体作者性指标；
15. $K_\infty/\Delta(\mathbb Z)$ 已经成为仓库中的完整公共 quotient API；
16. 非零喉部 cocycle 自动意味着物理允许的跨流线控制；
17. 作者性 Gramian 或代理 Hankel 的非零特征值就是自由意志；
18. 高斯容量公式适用于任意非线性、非高斯或量子控制系统；
19. 低秩自我近似自动保持因果性、稳定性、正性或 complete positivity；
20. 线性来源子空间交为零自动恢复原始细粒控制历史；
21. 账本创造作者性；账本只改善已有来源链的可审计性；
22. 自由保持核要求观察者永远选择留在其中；它只证明存在保持策略；
23. 前八级代理结构推出第九级强 libertarian freedom；
24. 本增订中的 paper-level 定理已经具有 Lean kernel proof term；
25. 本增订推进 RH、negative-base-$\varphi$、Born 规则起源或其他登记开放问题。

---

# 53. 最终统一：闭合观察者、反身主体与喉部输运

本增订把主体结构压缩为以下对象：

$$
\begin{aligned}
K_\infty
&=\text{永久不可观测方向},\\
R_O
&=\text{观察者自身可达方向},\\
\mathsf{Agt}_O
&=R_O/(R_O\cap N_\infty),\\
G_O
&=W_o^{1/2}W_c^OW_o^{1/2},\\
\mathcal H_O
&=\mathcal O_\beta\mathcal C_{\beta,O},\\
S_{\mathrm{ag}}
&=\text{完整未来交互画像的最小历史商},\\
C_{\mathrm{ag}}
&=\text{把当前自我接口反射到代理充分接口的闭包},\\
s
&=\text{历史生成的动作截面},\\
\Lambda
&=\text{行动、结果、理由与授权的追加账本},\\
\bar c
&=\text{已选动作的喉部分量 cocycle},\\
\mathsf{FreeKernel}
&=\text{可无限保持最低主体能力的最大受控不变集}.
\end{aligned}
$$

完整回路是：

$$
\boxed{
\Lambda_t
\longrightarrow
M_t
\longrightarrow
\pi_t
\longrightarrow
A_t
\longrightarrow
\Delta\kappa_t
\longrightarrow
Y_t
\longrightarrow
\Lambda_{t+1}.
}
$$

其中：

```text
Law 给出合法动作纤维与后果核；
Self 是所有权闭包与自主核心共同稳定的历史状态；
Will 是由该历史状态生成的内生对称破缺截面；
Choice 是截面在当前状态上的实际取值；
Commitment 把未来计划空间收缩为可追溯历史；
Agency 是自身控制穿过不可观测核后仍留在行为商中的部分；
Provenance 区分这一行为究竟来自自身还是外部通道；
Meta-agency 使观察者能够修改并保持未来的选择能力；
Throat transport 是已选动作经 cocycle 产生的隐藏分量后果。
```

因此最严格的统一不是：

```text
自由 = 没有原因；
自由 = 随机结果；
自由 = 喉部坐标本身。
```

而是：

$$
\boxed{
自由的操作核心，是观察者能够以自身拥有并由历史塑造的内部状态形成控制，
使该控制对未来产生可识别差异，把差异写入账本，
据此修订未来策略，并存在一种策略能够保持这种能力。
}
$$

喉部跳跃在其中的准确位置是：

$$
\boxed{
喉部跳跃不是意志本身，
而是一个来源可归属、策略可解释、历史可追溯的已选行动，
在隐藏路径分量空间中产生的本体输运。
}
$$

最后，兼容决定论但足以刻画自主性的最强结论是：

$$
\boxed{
行动不必没有原因；
关键在于行动原因是否在观察者边界内形成、可被读取和修订、
由过去自己的选择塑造，并能通过记录继续属于未来的自己。
}
$$

---

# 54. v1.3 增订：鲁棒主体、信息率、身份治理与分布式自由

**追加版本：v1.3，2026-08-26**

本增订只追加于第 53 节之后，不删改此前任何内容。它把前文的自由保持核从单主体、完全观察、非对抗模型提升到：环境对抗、部分观察、信息率限制、身份纠错、分布式治理、自我修改与可判定性边界。

继续使用同一真值纪律：以下新增结论是 paper-level 定义、定理与证明；除明确列出的形式化路线外，不声称已有同名 Lean proof term。核心边界仍是：

```text
鲁棒自主性不是强本体非决定性的证明；
随机性不是作者性；
账本不创造行动来源；
策略存在不等于策略可实现；
当前自由不等于未来自由可保持。
```

---

# 55. 对抗自由保持核

设完整状态空间为 $X$，最低主体性安全域为 $S_{\mathrm{ag}}\subseteq X$，观察者合法动作集为 $\mathcal A(x)$，观察者选择动作 $a$ 后环境可选响应集为 $\mathcal E(x,a)$，状态更新为

$$
F:X\times A\times E\to X.
$$

## 定义 55.1（观察者先行动的鲁棒前驱）

$$
\boxed{
\operatorname{Pre}_{\exists\forall}(Z)
=
\{x\in S_{\mathrm{ag}}:
\exists a\in\mathcal A(x),\
\forall e\in\mathcal E(x,a),\
F(x,a,e)\in Z\}.
}
$$

## 定义 55.2（鲁棒自由保持核）

$$
\boxed{
\mathsf{FreeKernel}_{\mathrm{rob}}
=
\nu Z.\operatorname{Pre}_{\exists\forall}(Z).
}
$$

有限状态下，从 $Z_0=S_{\mathrm{ag}}$ 递减迭代

$$
Z_{n+1}=\operatorname{Pre}_{\exists\forall}(Z_n)
$$

最终稳定于该最大固定点。

## 本文定理 55.1（无记忆鲁棒保持策略）

在有限、完全观察模型中，每个

$$
x\in\mathsf{FreeKernel}_{\mathrm{rob}}
$$

都存在动作 $a_x$，使所有允许环境响应的后继仍位于该核。因而状态反馈策略 $\pi(x)=a_x$ 能永久维持最低主体性。

### 证明

最大固定点满足

$$
\mathsf{FreeKernel}_{\mathrm{rob}}
=
\operatorname{Pre}_{\exists\forall}
(\mathsf{FreeKernel}_{\mathrm{rob}}).
$$

逐状态选择存在见证动作并重复即可。无限或可测系统还需可测选择前件。∎

定义自由保持动作集

$$
\mathcal A_{\mathrm{keep}}(x)
=
\{a:\forall e,\ F(x,a,e)\in\mathsf{FreeKernel}_{\mathrm{rob}}\}.
$$

按完整未来后果商去重复标签，可定义鲁棒操作自由容量

$$
F_{\mathrm{rob}}(x)
=
\log_2
|\mathcal A_{\mathrm{keep}}(x)/{\sim_x}|.
$$

核成员资格只保证至少有一条保持路径，不保证当前仍有多个保持自由的动作。

---

# 56. 量词次序与信息时序

若环境先显露响应，观察者随后选择动作，前驱变为

$$
\boxed{
\operatorname{Pre}_{\forall\exists}(Z)
=
\{x\in S_{\mathrm{ag}}:
\forall e\in\mathcal E(x),\
\exists a\in\mathcal A(x,e),\
F(x,a,e)\in Z\}.
}
$$

总有

$$
\operatorname{Pre}_{\exists\forall}(Z)
\subseteq
\operatorname{Pre}_{\forall\exists}(Z),
$$

故对应最大固定点满足

$$
\boxed{
\mathsf{FreeKernel}_{\mathrm{act\mbox{-}first}}
\subseteq
\mathsf{FreeKernel}_{\mathrm{observe\mbox{-}first}}.
}
$$

这说明自由不仅由动作数量决定，还由观察者何时得到环境信息决定。先承诺后观察要求一个对所有环境响应统一安全的动作；先观察后行动允许条件化响应，因此鲁棒区域通常更大。

---

# 57. 部分观察与信念自由核

观察者通常只访问读出 $q:X\to O$，不能直接使用真实状态。对观察历史 $h$，定义信念状态

$$
B(h)=\{x:x\text{ 与 }h\text{ 相容}\}\subseteq X.
$$

动作 $a$ 后得到新观察 $o'$ 时，定义信念后继

$$
\boxed{
\operatorname{Post}(B,a,o')
=
\{F(x,a,e):x\in B,\ e\in\mathcal E(x,a),\ q(F(x,a,e))=o'\}.
}
$$

对信念集合族 $\mathcal Z$，定义

$$
\boxed{
\begin{aligned}
\operatorname{Pre}_B(\mathcal Z)
=\{B:\;&B\subseteq S_{\mathrm{ag}},\
\exists a\text{ 对所有 }x\in B\text{ 均合法},\\
&\forall o',\ \operatorname{Post}(B,a,o')\ne\varnothing
\Rightarrow\operatorname{Post}(B,a,o')\in\mathcal Z\}.
\end{aligned}
}
$$

## 定义 57.1（信念自由核）

$$
\boxed{
\mathsf{BeliefFreeKernel}
=
\nu\mathcal Z.\operatorname{Pre}_B(\mathcal Z).
}
$$

## 本文定理 57.1（信念状态充分性）

任何只依赖观察历史的鲁棒安全策略，都可改写为只依赖当前信念 $B(h)$ 的策略。

### 证明

若两段历史产生同一信念，则当前可能真实状态、每个动作的后继信念族以及环境可能响应完全相同；安全延续条件只依赖该集合。∎

若接口 $r$ 精化 $q$，则相同历史下

$$
B_r(h)\subseteq B_q(h).
$$

在观察无成本且允许忽略额外信息时，精化不会降低鲁棒能力；更细信念可能解除粗纤维中互相冲突的安全约束。

---

# 58. 自由充分自我

对每段历史 $h$，令 $\mathsf{Win}(h)$ 表示所有能够从 $h$ 开始、对任意允许环境策略永久保持 $S_{\mathrm{ag}}$ 的观察者延续策略集合。

定义

$$
\boxed{
h\sim_{\mathrm{free}}h'
\iff
\mathsf{Win}(h)=\mathsf{Win}(h').
}
$$

以及自由充分自我

$$
\boxed{
M_{\mathrm{free}}
=
\mathcal H/{\sim_{\mathrm{free}}}.
}
$$

## 本文定理 58.1（普适最小性）

若历史接口 $r:\mathcal H\to R$ 足以决定 $\mathsf{Win}(h)$，则存在唯一映射从 $\operatorname{Im}(r)$ 到 $M_{\mathrm{free}}$，使历史商通过 $r$ 因子化。

这是标准 kernel 因子化：$r(h)=r(h')$ 必须推出获胜策略集合相同。∎

完整策略充分自我决定全部未来策略画像，因此自然映到 $M_{\mathrm{free}}$；反向一般不成立。自由充分自我只保存“哪些未来策略还能维持主体性”所需的历史区别。

---

# 59. 鲁棒代理价值的 Bellman 固定点

令 $r_{\mathrm{ag}}(x,a,e)$ 为有界代理奖励，可综合鲁棒动作容量、作者性谱隙、来源可识别裕量、账本完整度和策略修订能力。取 $0<\gamma<1$，定义

$$
\boxed{
(\mathcal TV)(x)
=
\sup_{a\in\mathcal A(x)}
\inf_{e\in\mathcal E(x,a)}
[r_{\mathrm{ag}}(x,a,e)+\gamma V(F(x,a,e))].
}
$$

## 本文定理 59.1（唯一价值固定点）

在有界函数空间的 sup 范数下，$\mathcal T$ 是 $\gamma$-压缩：

$$
\|\mathcal TV-\mathcal TW\|_\infty
\le\gamma\|V-W\|_\infty.
$$

故存在唯一固定点

$$
\boxed{V^*_{\mathrm{ag}}=\mathcal TV^*_{\mathrm{ag}}.}
$$

有限动作和响应集合下，最值可取，并存在平稳最优策略。∎

这纠正“最大化当前按钮数”的短视目标：当前动作可产生即时收益，却把系统送出自由保持核；另一动作可能即时收益低，却保存无限期代理价值。长期主体性由 Bellman 固定点而非单步动作数结算。

---

# 60. 承诺改变整个博弈

在固定转移和环境响应不变时，单纯扩充动作集合会扩大前驱及自由保持核：

$$
\mathcal A(x)\subseteq\mathcal A'(x)
\Rightarrow
\mathsf{FreeKernel}_{\mathcal A}
\subseteq
\mathsf{FreeKernel}_{\mathcal A'}.
$$

但承诺通常同时改变环境响应、契约、信任、资源和账本状态。因此承诺不是简单删除动作标签，而是把博弈 $\mathcal G$ 改写为 $\mathcal G_c$。

可能有

$$
|\mathcal A_c(x)|<|\mathcal A(x)|
$$

而

$$
\mathsf{FreeKernel}(\mathcal G_c)
\supsetneq
\mathsf{FreeKernel}(\mathcal G).
$$

可信承诺删除短期背叛选项，却可能消除环境的预防性破坏，扩大长期保证区域。因此选项数量与战略能力不是同一个量。

---

# 61. 自由恢复域

令 $K=\mathsf{FreeKernel}_{\mathrm{rob}}$，并允许主体暂时处于更大的可接受域 $D\supseteq K$。定义

$$
R_0=K,
$$

$$
\boxed{
R_{n+1}
=
R_n\cup
\{x\in D:\exists a,\ \forall e,\ F(x,a,e)\in R_n\}.
}
$$

## 定义 61.1（鲁棒恢复域）

$$
\boxed{
\mathsf{Recover}(K;D)=\bigcup_{n\ge0}R_n.
}
$$

定义最小恢复时间

$$
\tau_{\mathrm{rec}}(x)=\min\{n:x\in R_n\}.
$$

## 本文定理 61.1

对任意 $x\in\mathsf{Recover}(K;D)$，存在无记忆策略保证至多在 $\tau_{\mathrm{rec}}(x)$ 步内进入 $K$。

### 证明

若 $x\in R_n\setminus R_{n-1}$，定义给出一个动作使所有后继进入 $R_{n-1}$；逐层递减即可。∎

由此区分：主体性可保持、主体性受损但可恢复、以及在当前动作语法下不可恢复。

---

# 62. Barrier 与 Lyapunov 证书

若函数 $B:X\to\mathbb R$ 的次水平集

$$
S_B=\{x:B(x)\le0\}
$$

满足：对每个 $x\in S_B$，存在动作 $a$ 使所有响应后继仍满足 $B(F(x,a,e))\le0$，则

$$
\boxed{S_B\subseteq\mathsf{FreeKernel}_{\mathrm{rob}}.}
$$

这是自由保持的 barrier 证书。

若 $V:X\to\mathbb R_{\ge0}$ 满足 $V(x)=0$ 当且仅当 $x\in K$，且存在 $\delta>0$，使每个 $x\notin K$ 都有动作满足

$$
\forall e,\quad V(F(x,a,e))\le V(x)-\delta,
$$

则观察者至多经过

$$
\boxed{\left\lceil V(x)/\delta\right\rceil}
$$

步进入 $K$。这是自由恢复的有限时间 Lyapunov 证书。

---

# 63. 代理谱相变与储备

设状态 $x$ 上的局部自我控制—未来输出算子为 $H(x)$，奇异值为

$$
\sigma_1(x)\ge\sigma_2(x)\ge\cdots.
$$

定义第 $r$ 个代理维度的储备

$$
\boxed{
\operatorname{Reserve}_r(x)=\sigma_r(H(x)).
}
$$

## 本文定理 63.1（精确扰动裕量）

$$
\boxed{
\operatorname{dist}(H(x),\{K:\operatorname{rank}K\le r-1\})
=\sigma_r(H(x)).
}
$$

所以任何范数小于 $\sigma_r$ 的扰动都不能摧毁第 $r$ 个代理方向。

若 $H(x)$ 连续，则奇异值连续；代理秩只能在某个 $\sigma_r(H(x))=0$ 的边界上改变。可把

$$
S_{r,\varepsilon}=\{x:\sigma_r(H(x))\ge\varepsilon\}
$$

作为具有数值裕量的主体安全域，再计算其鲁棒自由核。

---

# 64. 来源主角度与条件数

设自我行为子空间和外部行为子空间为 $S_O,S_E$，且 $S_O\cap S_E=0$。令最小主角度为 $\theta\in(0,\pi/2]$，满足

$$
\cos\theta=\|P_OP_E\|.
$$

来源求和算子

$$
J:S_O\oplus S_E\to Y,
\qquad J(u,v)=u+v
$$

满足

$$
\boxed{
\sigma_{\min}(J)=\sqrt{1-\cos\theta},
\qquad
\sigma_{\max}(J)=\sqrt{1+\cos\theta}.
}
$$

因此

$$
\boxed{
\kappa_{\mathrm{prov}}
=
\sqrt{\frac{1+\cos\theta}{1-\cos\theta}}
=
\cot(\theta/2).
}
$$

正交来源给出条件数 $1$；角度趋零时条件数发散；真正相交时来源不再唯一。作者性不仅需要无完全重叠，还需要足够大的来源分离角。

---

# 65. 信息如何创造可执行自由

取两个真实状态 $x_0,x_1$，初始读出把二者合并。动作 $L$ 只在 $x_0$ 安全，$R$ 只在 $x_1$ 安全，另有安全观测动作 $S$，它不改变状态但揭示当前是哪一个状态。

在初始信念 $\{x_0,x_1\}$ 上，$L,R$ 都不是统一安全动作；执行 $S$ 后信念收缩为单点，随后相应的 $L$ 或 $R$ 成为安全动作。

因此信息没有凭空创造物理动作，却通过缩小认识纤维解除无知造成的统一安全约束。可定义认识论代理增益

$$
\Delta_{\mathrm{epi}}(S)
=
\mathbb E[F_{\mathrm{rob}}(B_{\mathrm{after}})]
-F_{\mathrm{rob}}(B_{\mathrm{before}}).
$$

观测动作可以没有即时外部收益或喉部位移，却因扩大未来可条件化行动能力而有正价值。

---

# 66. 有效动作语法扩张

令时刻 $t$ 的动作集合为 $\mathcal A_t$，按完整未来行为画像取商：

$$
\mathcal A_t^{\mathrm{eff}}=\mathcal A_t/{\sim_t}.
$$

新增动作若不与任何旧动作行为等价，才构成有效动作创新。单纯增加命令名、别名或相同 API 包装不增加自由。

若旧动作全部保留、旧语义不变且环境响应不恶化，则保守扩张满足

$$
\boxed{
\mathsf{FreeKernel}_t
\subseteq
\mathsf{FreeKernel}_{t+1}.
}
$$

有限情形可定义动作语法增长率

$$
\boxed{
g_{\mathrm{act}}
=
\limsup_{t\to\infty}
\frac1t\log|\mathcal A_t^{\mathrm{eff}}|.
}
$$

封闭有限、确定、固定动作语法的主体最终周期化；长期无界行动创新要求动作语言、记忆、环境输入或状态维度中的至少一项持续开放。

---

# 67. 身份保持的 kernel 判据

设旧自我状态为 $M$，自我修改为 $U:M\to M'$，需保留的身份接口为 $Z:M\to\mathcal Z$，包含承诺、价值根、来源、理由或责任记录。

## 定义 67.1（身份保持）

若存在 $\bar Z:M'\to\mathcal Z$ 使

$$
Z=\bar Z\circ U,
$$

则修改保持身份接口 $Z$。

## 本文定理 67.1

$$
\boxed{
U\text{ 保持 }Z
\iff
\ker U\subseteq\ker Z.
}
$$

证明是在 $U$ 的有效像上定义 $\bar Z(U(m))=Z(m)$；kernel 包含恰保证代表元无关。∎

定义身份抹除残差

$$
\mathcal E_{\mathrm{id}}(U;Z)
=
\{(m,m'):U(m)=U(m'),\ Z(m)\ne Z(m')\}.
$$

概率版本的身份损失为

$$
L_{\mathrm{id}}=H(Z(M)\mid U(M)).
$$

自我修改能力与身份安全的自我修改能力必须分开报告。

---

# 68. 鲁棒可撤销委托

设主体 $P$ 把部分控制权交给代理 $D$。主体自由保持核为 $K_P$，恢复域为 $\mathsf{Recover}_P(K_P)$。令 $\operatorname{Reach}_D(x)$ 表示主体成功收回控制之前，代理可强制到达的全部状态。

定义委托从 $x$ 出发鲁棒可撤销，当且仅当

$$
\boxed{
\operatorname{Reach}_D(x)
\subseteq
\mathsf{Recover}_P(K_P).
}
$$

若该包含成立且主体保留可执行撤销通道，则代理无论怎样行动，主体仍有恢复最低自主性的路径。若代理可先强制进入恢复域之外的状态，则不存在鲁棒撤销保证。

“存在关闭按钮”不等于可撤销；撤销命令还必须可执行，且撤销后的状态必须保留密钥、账本、资源和策略修改接口。

---

# 69. 集体自由联盟核

对成员集合 $N$ 和联盟 $C\subseteq N$，把 $C$ 的联合控制视为主体动作，其余成员和环境视为对抗方，定义联盟自由保持核 $\mathsf{FreeKernel}_C$。

若 $C\subseteq D$ 会扩充控制而不加强对抗，则

$$
\boxed{
\mathsf{FreeKernel}_C
\subseteq
\mathsf{FreeKernel}_D.
}
$$

定义状态 $x$ 上的最小自由保持联盟阶数

$$
\boxed{
r_{\mathrm{viab}}(x)
=
\min\{|C|:x\in\mathsf{FreeKernel}_C\}.
}
$$

它与最小作者联盟阶数不同：谁共同产生了某次行动，不等于谁共同维持了集体继续行动的能力。集体主体性可以依赖严格不可还原的协同联盟。

---

# 70. 完整动态主体语义

动态主体状态写为

$$
(x_t,B_t,m_t,\pi_t,\Lambda_t,\kappa_t),
$$

其中分别是完整世界、信念、自我、策略、账本和喉部分量。

完整一步为

$$
\mathcal A_{\mathrm{keep}}(B_t,m_t,\Lambda_t)
\longrightarrow a_t,
$$

$$
e_t\in\mathcal E(x_t,a_t),
\qquad
x_{t+1}=F(x_t,a_t,e_t),
$$

$$
\kappa_{t+1}
=
\kappa_t+\bar c(a_t,x_t,e_t),
$$

$$
y_{t+1}\sim P(\cdot\mid x_{t+1},a_t),
$$

$$
B_{t+1}=\operatorname{Post}(B_t,a_t,y_{t+1}),
$$

$$
\Lambda_{t+1}=\Lambda_t\Vert(a_t,e_t,y_{t+1}),
$$

$$
(m_{t+1},\pi_{t+1})
=\mathcal U(m_t,\pi_t,\Lambda_{t+1}).
$$

该语义把部分观察、环境对抗、自由保持、结果不确定、认识更新、喉部输运、账本追加和自我修改放入同一步骤，而不把其中任何一层冒充另一层。

---

# 71. 动态主体能力签名

可用向量而非单一标量描述主体：

$$
\boxed{
\mathbf A_O
=
(F_{\mathrm{rob}},V^*_{\mathrm{ag}},\tau_{\mathrm{rec}},
\operatorname{Reserve}_r,\theta_{\mathrm{prov}},h_\varepsilon,
 g_{\mathrm{act}},L_{\mathrm{id}},r_{\mathrm{viab}}).
}
$$

其中分别表示当前鲁棒保持动作容量、长期代理价值、恢复时间、代理谱储备、来源分离角、选择对未来自我的视界、有效动作语法增长、身份损失和最小集体保持联盟。

这些坐标之间不存在普遍单调关系：承诺可能降低即时动作容量却提高长期价值；自我修改可能扩大动作语言却损伤身份；联盟扩大可缩短恢复时间却增加来源归属复杂性。

---

# 72. 未来可作者化策略集合

对历史 $h$，定义 $\mathsf{AuthoredFuture}(h)$ 为所有同时满足以下条件的延续策略集合：

1. 对抗允许环境时维持最低主体性；
2. 保持身份与账本可恢复；
3. 不把未来控制权不可逆交给外部；
4. 保留后续策略修订能力。

动态自由不是单个动作，而是该集合是否非空、是否含多个行为不同元素、是否能在扰动后保持、受损后恢复并通过新观察或新动作语法扩张。

因此可以写成

$$
\boxed{
\text{Freedom}
=
\text{viability}
+
\text{recoverability}
+
\text{robustness}
+
\text{provenance}
+
\text{revisability}
+
\text{expandability}.
}
$$

喉部跳跃仍只是已选行动经隐藏 cocycle 产生的本体输运，不是自由的来源。

---

# 73. 安全与活性：Büchi 主体核

自由保持核允许一种退化的冻结生存：主体不死，但策略永久固定，再也不能恢复有效分岔、学习或修订。

选定主体性更新集合 $L_{\mathrm{renew}}\subseteq S_{\mathrm{ag}}$，要求其中至少恢复策略修订、代理谱裕量、账本访问或多个自由保持动作。对 $Q\subseteq Z$ 定义区域内鲁棒吸引子

$$
\operatorname{Attr}_Z(Q)
=
\mu Y[Q\cup(Z\cap\operatorname{Pre}_{\exists\forall}(Y))].
$$

定义主体性 Büchi 核

$$
\boxed{
\mathsf{LiveAgency}
=
\nu Z\;
\operatorname{Attr}_Z
(L_{\mathrm{renew}}\cap\operatorname{Pre}_{\exists\forall}(Z)).
}
$$

有限博弈中，$\mathsf{LiveAgency}\subseteq\mathsf{FreeKernel}_{\mathrm{rob}}$，并存在策略既永久保持安全，又无限多次访问更新集合。于是长期状态至少分为死亡、冻结生存和活主体三类。

---

# 74. 一步安全选择的最小观察字母表

子集 $C\subseteq X$ 称为安全兼容，若

$$
\bigcap_{x\in C}\mathcal A_X(x)\ne\varnothing.
$$

定义安全分区数

$$
\boxed{
\chi_{\mathrm{safe}}
=
\min\{k:X=C_1\dot\cup\cdots\dot\cup C_k,
\ C_i\text{ 均安全兼容}\}.
}
$$

## 本文定理 74.1

支持确定性一步安全策略的最小观察值数量恰为 $\chi_{\mathrm{safe}}$。

### 证明

任何安全观察接口的每个纤维都必须安全兼容，因此纤维数不小于最小分区数。反向，取一个最小兼容分区作为观察标签，并在每块中选一个公共安全动作。∎

故最低观察容量至少为

$$
\boxed{\log_2\chi_{\mathrm{safe}}\text{ bit}.}
$$

所需信息由安全动作兼容结构决定，而不是由微观状态总数决定。

---

# 75. 长期主体维持数据率

令 $\Omega_n$ 为长度 $n$ 的隐藏情景集合。子集 $C\subseteq\Omega_n$ 称为 $n$-步策略兼容，若存在同一个因果行动计划，使其中所有情景在前 $n$ 步都保持主体性安全。

定义最小兼容分区数

$$
N_n^{\mathrm{ag}}
=
\min\{k:\Omega_n=C_1\dot\cup\cdots\dot\cup C_k,
\ C_i\text{ 均 }n\text{-步策略兼容}\}.
$$

若观察通道每步至多输出 $M$ 个符号，则长度 $n$ 的观察词至多有 $M^n$ 个。

## 本文定理 75.1（维持数据率下界）

若该观察通道能对所有情景鲁棒维持主体性 $n$ 步，则

$$
\boxed{M^n\ge N_n^{\mathrm{ag}}.}
$$

因同一观察词纤维中的情景必须共享同一因果策略，故该纤维必须是策略兼容块。∎

定义主体维持熵

$$
\boxed{
h_{\mathrm{maint}}
=
\limsup_{n\to\infty}
\frac1n\log_2N_n^{\mathrm{ag}}.
}
$$

任何固定观察速率 $R$ 若要永久鲁棒维持主体性，必须满足

$$
\boxed{R\ge h_{\mathrm{maint}}.}
$$

自由保持因此可能要求持续从世界获得最低信息率。

---

# 76. 允许失败时的 Fano 下界

设有 $r$ 个等概率控制类别，不同类别需要不同安全策略；观察记录为 $Z$，推断为 $\widehat C(Z)$，错误概率不超过 $\varepsilon$。Fano 不等式给出

$$
H(C\mid Z)
\le h_2(\varepsilon)+\varepsilon\log_2(r-1).
$$

因为 $H(C)=\log_2r$，得到

$$
\boxed{
I(C;Z)
\ge
\log_2r-h_2(\varepsilon)-\varepsilon\log_2(r-1).
}
$$

所以允许小概率主体性失败可以减少信息需求，但不能消除率—失效率下界。完全安全极限 $\varepsilon\to0$ 恢复 $\log_2r$。

---

# 77. 作者信息瓶颈

若内部决定到公共记录形成条件 Markov 链

$$
D\to Z_1\to Z_2\to\cdots\to Z_k\to R
$$

（例如决定、运动命令、执行器、世界、传感器、账本），则条件数据处理给出

$$
\boxed{I(D;R\mid Q)\le I(D;Z_i\mid Q)}
$$

对每个中间接口成立。若各段信道容量上界为 $C_i$，则

$$
\boxed{I(D;R\mid Q)\le\min_iC_i.}
$$

线性链 $H=H_k\cdots H_1$ 同样满足

$$
\operatorname{rank}H\le\min_i\operatorname{rank}H_i.
$$

主体能力不能超过决定—执行—世界—记录链中最窄的接口。

---

# 78. 可审计作者性与内部隐私

设完整内部状态为 $M$，最小公共来源证书为 $P=f(M)$，公共记录为 $R$，且 $H(P\mid R)=0$，即记录能够恢复必要的责任来源。

## 本文定理 78.1（来源—理由泄漏分解）

$$
\boxed{
I(M;R)=H(P)+I(M;R\mid P).
}
$$

### 证明

因 $P$ 是 $M$ 的函数，$I(M;R)=I(P,M;R)$；再用链式法则与 $I(P;R)=H(P)$。∎

定义额外理由泄漏

$$
L_{\mathrm{reason}}=I(M;R\mid P).
$$

完美公共归属至少公开来源证书所含信息；理想选择性审计要求 $L_{\mathrm{reason}}=0$，即记录说明谁负责而不额外公开其内部理由和策略。

---

# 79. 信息主权

设零和博弈中主体获得信号 $q_{\mathrm{self}}$，对手获得关于主体的信号 $q_{\mathrm{adv}}$，博弈值为 $V(q_{\mathrm{self}},q_{\mathrm{adv}})$。

若主体信号被精化且主体可以忽略新增信息，则策略集扩大：

$$
\boxed{
V(q'_{\mathrm{self}},q_{\mathrm{adv}})
\ge V(q_{\mathrm{self}},q_{\mathrm{adv}}).
}
$$

若对手信号被精化，则对手条件响应集扩大：

$$
\boxed{
V(q_{\mathrm{self}},q'_{\mathrm{adv}})
\le V(q_{\mathrm{self}},q_{\mathrm{adv}}).
}
$$

所以“信息越多越好”必须注明谁得到信息。信息主权是决定哪些接口由谁读取的能力；同一账本兼具自我记忆和公共审计时会产生真实张力。

---

# 80. 私有随机化作为防御工具

随机性不产生作者性，但主体可以有理由地选择一种混合策略。设主体动作和对手预测均为比特，收益为预测错误时 $1$、预测正确时 $-1$。

公开确定策略会被对手精确反制，收益为 $-1$；主体采用行动前不向对手公开的均匀混合策略时，任意对手选择的期望收益为 $0$。

因此私有随机化严格提高鲁棒价值。应区分：

```text
meta-authorship：主体选择采用何种随机策略；
sample authorship：某个具体随机样本为何出现。
```

主体可以对随机化规则承担作者性，而不声称预选了随机样本。

---

# 81. 身份账本的纠错距离

设身份／承诺状态集合为 $\mathcal Z$，编码为

$$
c:\mathcal Z\to\Sigma^n.
$$

最小 Hamming 距离为

$$
d_{\min}=\min_{z\ne z'}d_H(c(z),c(z')).
$$

## 本文定理 81.1（唯一恢复阈值）

任意不超过 $t$ 个符号遭篡改后仍能唯一恢复原身份，当且仅当

$$
\boxed{d_{\min}\ge2t+1.}
$$

证明是半径 $t$ Hamming 球互不相交的标准充要条件。∎

定义身份篡改韧性

$$
\boxed{t_{\mathrm{id}}=\lfloor(d_{\min}-1)/2\rfloor.}
$$

账本存在与身份记录鲁棒存在必须分开；冗余签名、多位置保存和追加式记录可被解释为提高身份码距。

---

# 82. 集体意志的 quorum 交集

设集体有 $n$ 个授权成员，至多 $t$ 个 Byzantine 成员可签署冲突决定；有效集体决定需要 $q$ 个不同签名，诚实成员不双签。

## 本文定理 82.1（冲突证书排除）

若

$$
\boxed{2q>n+t,}
$$

则不可能同时存在两份相互冲突、各有 $q$ 个签名的有效证书。

### 证明

任意两个 quorum 的交集至少为 $2q-n>t$，故交集中至少有一个诚实成员；它若同时签署两份冲突证书即违背诚实性。∎

当 $2q\le n+t$ 时，两个 quorum 可只在至多 $t$ 个成员上相交，让这些成员全部 Byzantine 即可形成双证书。该条件精确刻画了抽象模型中集体意志不可分裂所需的授权交集。

---

# 83. 分布式自我的 join-semilattice

设历史偏序为 $L$。并发副本 $\lambda_1,\lambda_2$ 若要存在唯一最小无损合并，需要 join

$$
\lambda_1\vee\lambda_2.
$$

全部历史对都存在规范最小合并，当且仅当 $L$ 是 join-semilattice。此时合并幂等、交换、结合，副本按任意顺序合并均收敛。

若两个历史含互斥且不可撤销的承诺，它们可能没有一致共同上界。此时只能：显式记录冲突、拒绝合并、保留为不同后继主体，或加入更高层裁决历史。

因此共享过去不推出分叉后仍能无损重新成为同一主体；分布式身份的自然结构是带可合并区和不可合并分叉的历史 DAG。

---

# 84. 模型不确定性与鲁棒半径

设可能转移模型族为 $\mathfrak F_\delta$，并随不确定半径单调扩张：

$$
\delta_1\le\delta_2
\Rightarrow
\mathfrak F_{\delta_1}\subseteq\mathfrak F_{\delta_2}.
$$

鲁棒前驱对所有 $F\in\mathfrak F_\delta$ 取全称，因此

$$
\boxed{
\mathsf{FreeKernel}_{\delta_2}
\subseteq
\mathsf{FreeKernel}_{\delta_1}.
}
$$

定义全局主体鲁棒半径

$$
\boxed{
\delta^*(x)=\sup\{\delta:x\in\mathsf{FreeKernel}_\delta\}.
}
$$

它与局部奇异值储备不同：前者是全局动态自由保持的模型不确定裕量，后者是局部代理秩的算子扰动裕量。

---

# 85. 自由保持核的不可判定性

有限状态模型可通过固定点迭代计算自由保持核；图灵完备系统一般不可。

## 本文定理 85.1

不存在总算法，能对所有图灵完备确定系统和初态判定该初态是否属于主体自由保持核。

### 证明

给定机器 $M$ 与输入 $w$，构造唯一动作的模拟系统：机器尚未停机时状态在安全域；一旦停机即进入永久死状态。初态属于自由保持核，当且仅当 $M(w)$ 永不停止。若成员资格可判定，即可判定停机问题。∎

这是一条计算边界，不是哲学含混：一般开放自我修改系统的“能否永远保持自由”可能没有完备机械判定器。

---

# 86. Proof-carrying self-modification

设主体性安全不变量为 $I\subseteq X$，自我修改程序为 $U:X\to X$，证明携带修改为 $(U,\pi)$，其中 $\pi$ 证明

$$
U(I)\subseteq I.
$$

若 proof checker 可判定且可靠，则从 $x_0\in I$ 出发，任何由已接受修改组成的有限序列都保持 $x_t\in I$；证明是直接归纳。

但对图灵完备修改语言和非平凡语义安全性质，不存在同时总终止、接受所有安全程序并拒绝所有不安全程序的判定器，否则可归约第 85 节构造。

实际治理只能组合：可靠但不完备的证明检查、受限可判定语言、运行时监控、资源界验证以及外部制度裁决。合理目标是“所有被批准的修改都有可靠证书”，而不是“所有安全修改都必被机械识别”。

---

# 87. 三种长期固定点

动态主体至少需要三个不同不变量。

## 生存固定点

$$
\mathsf{FreeKernel}
$$

保证最低主体结构可以永久存在。

## 活性固定点

$$
\mathsf{LiveAgency}
$$

保证策略开放、学习或修订能力会无限多次恢复。

## 身份固定点

相对于身份接口 $Z$，定义 $\mathsf{IdentityKernel}_Z$ 为可永久保持 $Z$ 可恢复、承诺链可追溯和作者来源不丢失的状态域。

一般只有

$$
\mathsf{LiveAgency}\subseteq\mathsf{FreeKernel};
$$

身份核与前两者无无条件包含关系。主体可能活着且持续选择却失去旧身份，或保留旧身份却永久冻结策略。

---

# 88. 建议 Lean 模块树与严格边界

```text
D5/S3/Observer/Agency/Robust/
  AdversarialPredecessor.lean
  RobustAgencyKernel.lean
  KeepActionSet.lean
  QuantifierOrderKernel.lean

D5/S3/Observer/Agency/Belief/
  BeliefState.lean
  BeliefPost.lean
  BeliefAgencyKernel.lean
  BeliefPolicySufficiency.lean
  ObservationRefinementMonotonicity.lean

D5/S3/Observer/Agency/Recovery/
  AgencyRecoveryDomain.lean
  MinimumRecoveryTime.lean
  AgencyBarrierCertificate.lean
  AgencyLyapunovCertificate.lean
  LiveAgencyBuchi.lean

D5/S3/Observer/Agency/InformationRate/
  SafeCompatiblePartition.lean
  MinimumSafeObservationAlphabet.lean
  AgencyMaintenancePartition.lean
  AgencyDataRateLowerBound.lean
  ApproximateAgencyFanoBound.lean
  AuthorshipBottleneck.lean

D5/S3/Observer/Agency/Privacy/
  SelectiveAuditDecomposition.lean
  InformationSovereignty.lean
  PrivateRandomizationWitness.lean

D5/S3/Observer/Agency/Identity/
  IdentityPreservingModification.lean
  IdentityErasureResidual.lean
  IdentityCodeDistance.lean
  QuorumIntersection.lean
  DistributedIdentityJoin.lean

D5/S3/Observer/Agency/Governance/
  RevocableDelegation.lean
  CoalitionViabilityKernel.lean
  ModelUncertaintyMonotonicity.lean
  ViabilityUndecidable.lean
  ProofCarryingSelfModification.lean
```

优先闭合低依赖结果：

```text
adversarialPre_mono
robustKernel_greatest
actFirst_kernel_le_observeFirst_kernel
beliefPolicy_factors
freeSufficientSelf_universal
recovery_rank_decreases
safeObservation_card_eq_partitionNumber
maintenance_rate_lower_bound
identityPreserving_iff_kernel_le
quorum_conflict_impossible
modelUncertainty_kernel_antitone
proofCarryingModification_preserves
```

本增订不声称：

1. 环境必然是敌对的；对抗模型只给最坏情形保证；
2. 完全观察有限博弈的无记忆策略结论自动推广到所有连续或部分观察系统；
3. 更高观察精度在有成本、隐私泄漏或对手同步获知时必然提高净自由；
4. Bellman 奖励 $r_{\mathrm{ag}}$ 具有唯一自然标量化；
5. 承诺缩小动作集就必然提高自由保持核；它必须连同博弈语义重算；
6. 代理奇异值是人格、意识或道德价值的直接物理量；
7. Fano 下界单独给出可实现编码方案；
8. 私有随机化使随机样本本身具有作者性；
9. 码距与 quorum 条件解决全部人格或集体合法性问题；
10. join-semilattice 合并能调和逻辑上互斥的承诺；
11. 图灵不可判定性意味着具体受限系统不可验证；
12. proof-carrying 修改可以同时完整接受全部安全修改；
13. 鲁棒自主性、信息率和身份治理推出强本体自由；
14. 本增订中的新增定理已经具有 Lean kernel proof term；
15. 本增订改变此前对单次 Born 结果、喉部分量 API 或登记数学开放问题的边界。

---

# 89. 最终统一：主体自主性是可维持、可恢复、可审计的动态编码

把主体闭环写成

$$
X_t
\longrightarrow
B_t
\longrightarrow
M_t
\longrightarrow
D_t
\longrightarrow
U_t
\longrightarrow
Y_t
\longrightarrow
\Lambda_{t+1}
\longrightarrow
M_{t+1}.
$$

四种编码必须同时工作：

```text
世界到自我：观察通道以足够速率压入安全行动所需区别；
自我到行动：内部理由穿过执行瓶颈形成真实控制；
行动到历史：作者签名穿过世界与记录噪声并以足够码距进入账本；
历史到未来自我：过去选择继续影响未来策略而不被遗忘、篡改或接管。
```

隐藏路径分量仍在行动之后更新：

$$
\boxed{
\kappa_{t+1}
=
\kappa_t+\bar c(U_t,x_t,e_t).
}
$$

所以喉部 cocycle 运输行动后果，不替代观察、决策、作者性和账本编码。

最终：

$$
\boxed{
\begin{aligned}
\text{Freedom}
={}&\text{viability}+\text{liveness}+\text{recoverability}\\
&+\text{observational rate}+\text{causal control}\\
&+\text{provenance separation}+\text{identity correction}\\
&+\text{policy revision}+\text{self-modification governance}.
\end{aligned}
}
$$

主体不是一个偶尔产生选择的点，而是一个能够持续获得选择所需信息，把内部理由转化为行动，把行动可靠编码为自身历史，并在扰动后保持或恢复这一闭环的系统。

强本体自由仍是独立命题：给定完整宇宙状态后，未来是否仍存在未被隐藏变量预选的真实分岔。本增订没有偷渡该结论；它建立的是可检查、兼容决定论的鲁棒主体自主性结构。
