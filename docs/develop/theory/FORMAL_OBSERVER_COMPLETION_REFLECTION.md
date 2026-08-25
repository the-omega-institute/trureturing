# 观察者完成反射与可观测 Gram 演算
## 稳定接口的普适闭包、状态—效应反对偶与定量可观测性

**版本：v1.1，2026-08-25**

**版本史**：v1.0 初稿 → **v1.1 勘误(issue #3118)：推论 25.3 补回 Heisenberg 导数的因子 i，并将生成元记为 i·ad_H**。

---

## 摘要

`FORMAL_DYNAMICAL_INTERFACE_RESIDUALS.md` 已经把精确下降、carry、预测闭包、可观测代数不变性、线性交叉块、量子交换子流、随机 lumpability 与因果查询 kernel 统一为同一类接口因子化问题。

本文继续推进一个更强的问题：

> 当给定接口尚不闭合时，是否存在一个规范、最小、可组合并具有定量几何的完成？

本文得到四层结论。

第一，全部接口按信息精化构成偏序；对固定动力学，稳定接口构成反射子偏序。由全部未来读数组成的行为接口定义闭包算子

$$
C_F.
$$

它单调、扩张、幂等，并且是当前接口的最小稳定精化。

第二，状态 kernel 与可观测代数存在反序对应。有限维线性系统中，这一对偶具体化为

$$
N_∞ = ⋂_{n≥0} ker(C T^n) = O_∞^⊥,
$$

$$
O_∞ = span_{n≥0} ran((T*)^n C*).
$$

第三，折扣可观测 Gram 算子

$$
W_β = Σ_{n≥0} β^n (T*)^n C* C T^n
$$

满足

$$
⟨x,W_βx⟩ = Σ_{n≥0} β^n ‖C T^n x‖²,
$$

$$
ker(W_β)=N_∞,
$$

并解 Lyapunov 方程

$$
W_β = C* C + β T* W_β T.
$$

因此 observer completion 不只给出“可否区分”的布尔判据，还产生条件数、脆弱方向与目标实验设计准则。

第四，这套反射结构推广到动作词、非交换多动力学和量子 Heisenberg 闭包。若动力学不交换，一次分别闭合每个生成元通常不足；真正的联合完成必须读取全部自由词。Hamiltonian 交换子不仅决定瞬时概率流，还是 effect completion 的无穷小生成元。

本文只增加一份 Markdown 理论稿。除明确列出的仓库锚点外，新增定理均为 paper-level 证明，不声称已经 Lean 闭合。

---

# 0. 真值层级与严格边界

本文使用四种状态：

- **定义**：保守引入记号；
- **本文定理**：本文给出证明，但不声称已有同名 Lean proof term；
- **Lean 锚点**：仓库已有机器证明；
- **条件命题／路线**：仍依赖额外完备性、收敛性或实现桥。

本文不主张：

1. 可观测 Gramian 是新概念；新内容是把它嵌入仓库的 interface–remainder–observer 结构；
2. 所有非 Markov 性都由有限维线性模型完全描述；
3. Hilbert–Schmidt 几何替代 PSD、CP 或 complete positivity；
4. 非交换 closure residual 自动具有群或普通上同调结构；
5. 动力学反射解决表示满射、自描述或对角逃逸；
6. 本文证明了 negative-base-φ 主定理、RH 或其他公开难题。

---

# 1. 接口精化偏序

固定状态类型 X。一个接口是满射

$$
q : X → B_q,
$$

其中 codomain 已缩到有效像。

## 定义 1.1（信息精化）

对接口 q 与 r，定义

$$
q ⪯ r
$$

当且仅当存在唯一 factor

$$
π_{rq} : B_r → B_q
$$

使

$$
q = π_{rq} ∘ r.
$$

读作：r 至少和 q 一样精细。

## 定理 1.1（kernel 判据）

$$
q ⪯ r
⇔
K_r ⊆ K_q,
$$

其中

$$
K_q = {(x,y) : q(x)=q(y)}.
$$

### 证明

若 q 通过 r 因子化，则 r 相同必推出 q 相同，所以 K_r ⊆ K_q。

反向定义

$$
π_{rq}(r(x)) := q(x).
$$

kernel 包含保证代表元无关；r 的满射性给出唯一性。∎

## 推论 1.1

模去 kernel 相同的接口后，⪯ 是偏序。接口的纯区分能力由 kernel 完全决定；codomain 名称只是坐标。

---

# 2. 稳定接口

固定动力学

$$
F : X → X.
$$

## 定义 2.1（F-稳定）

接口 q 称为 F-稳定，若存在

$$
F̄_q : B_q → B_q
$$

满足

$$
q ∘ F = F̄_q ∘ q.
$$

等价地：

$$
(x,y)∈K_q
⇒
(Fx,Fy)∈K_q.
$$

记全部接口的偏序为 Int(X)，稳定接口子偏序为 Stab_F(X)。

## 原理 2.1

稳定性既不向任意精化单调，也不向任意粗化单调：

- 精化可能加入一个下一步不能由当前精化值决定的新坐标；
- 粗化可能重新合并具有不同未来的状态。

所以需要专门的完成算子，而不能把稳定接口理解为普通上闭集或下闭集。

---

# 3. 规范行为完成

## 定义 3.1（行为接口）

定义

$$
C_F(q)(x)
=
(q(x),q(Fx),q(F²x),…).
$$

其 codomain 取该无限词映射的有效像。

## 定理 3.1（完成 kernel）

$$
K_{C_F(q)}
=
⋂_{n≥0}(F×F)^{-n}(K_q).
$$

### 证明

两状态具有相同完成值，当且仅当对每个 n：

$$
q(F^n x)=q(F^n y).
$$

这正是属于全部逆像 kernel 的交。∎

## 定理 3.2（完成稳定）

C_F(q) 是 F-稳定接口。

### 证明

在行为词上定义左移

$$
σ(b₀,b₁,b₂,…)
=
(b₁,b₂,b₃,…).
$$

则

$$
C_F(q)(Fx)=σ(C_F(q)(x)).
$$

把 σ 限制到有效像即得下降动力学。∎

## 推论 3.1

$$
q ⪯ C_F(q),
$$

因为第零坐标恢复 q。

---

# 4. 最小稳定精化

## 定理 4.1

若 r 是 F-稳定接口且

$$
q ⪯ r,
$$

则

$$
C_F(q) ⪯ r.
$$

### 证明

q ⪯ r 给出 K_r ⊆ K_q。由于 r 稳定，若 (x,y)∈K_r，则对每个 n：

$$
(F^n x,F^n y)∈K_r⊆K_q.
$$

所以

$$
K_r
⊆
⋂_{n≥0}(F×F)^{-n}K_q
=
K_{C_F(q)}.
$$

由 kernel 判据即得。∎

## 解释

C_F(q) 不保存全部微观状态，只恢复那些在某个未来时刻会改变原读数的区别。因此它是：

$$
使当前观察世界自治所必需的最小信息精化。
$$

---

# 5. 完成是 closure operator

## 定理 5.1（扩张性）

$$
q ⪯ C_F(q).
$$

## 定理 5.2（单调性）

若

$$
q ⪯ r,
$$

则

$$
C_F(q) ⪯ C_F(r).
$$

### 证明

K_r ⊆ K_q，故对每个 n：

$$
(F×F)^{-n}K_r
⊆
(F×F)^{-n}K_q.
$$

取交并再次使用 kernel 判据。∎

## 定理 5.3（幂等性）

$$
C_F(C_F(q)) ≃ C_F(q).
$$

### 证明

第一次完成已经稳定。对稳定接口再次加入全部未来读数不会继续切分 kernel。∎

## 结论 5.1

C_F 在信息精化偏序上是 closure operator：

$$
扩张 + 单调 + 幂等。
$$

---

# 6. 反射普适性质

把偏序视为范畴，记稳定接口包含函子为

$$
ι : Stab_F(X) ↪ Int(X).
$$

## 定理 6.1（反射）

$$
C_F ⊣ ι.
$$

即对任意接口 q 和稳定接口 r：

$$
C_F(q) ⪯ r
⇔
q ⪯ r.
$$

### 证明

左向由 q ⪯ C_F(q) 和传递性。右向就是最小稳定精化定理。∎

## 推论 6.1（规范性）

任何满足下列条件的 completion 都与 C_F 等价：

1. 输出稳定接口；
2. 保留原接口；
3. 对所有稳定精化具有上述普适因子化。

因此行为 completion 不是多个可选修复之一，而由普适性质唯一刻画。

---

# 7. 最大不变 kernel

## 定义 7.1（kernel 算子）

对关系 R⊆X²，定义

$$
Φ_q(R)
=
K_q ∩ (F×F)^{-1}(R).
$$

令

$$
K₀=K_q,
$$

$$
K_{n+1}=Φ_q(K_n).
$$

则

$$
K_n
=
⋂_{k=0}^{n}(F×F)^{-k}K_q.
$$

## 定理 7.1（greatest fixed point）

$$
K_{C_F(q)}
=
νR. Φ_q(R).
$$

即它是包含于 K_q 的最大 F-前向不变关系。

### 证明

完成 kernel 显然满足

$$
K_∞=K_q∩(F×F)^{-1}K_∞.
$$

若 R⊆K_q 且 (F×F)(R)⊆R，则对所有 n：

$$
R⊆(F×F)^{-n}K_q.
$$

取交即得 R⊆K_∞。∎

## 统一解释

同一个 completion 有两种完全对偶的读法：

$$
加入全部未来可观测量
⇔
删除当前 kernel 中所有不稳定状态对。
$$

---

# 8. 动作词与受控完成

令动作字母表为 A，每个动作给出

$$
F_a : X → X.
$$

对词 w∈A*，令 F_w 为相应复合。

## 定义 8.1（受控行为接口）

$$
C_A(q)(x)
=
(q(F_wx))_{w∈A*}.
$$

## 定理 8.1

C_A(q) 是所有同时对每个 F_a 稳定、且精化 q 的接口中的最小者。

### 证明

其 kernel 为

$$
K_{C_A(q)}
=
⋂_{w∈A*}(F_w×F_w)^{-1}K_q.
$$

若 r 对每个生成元稳定且 K_r⊆K_q，则对所有动作词 w：

$$
K_r⊆(F_w×F_w)^{-1}K_q.
$$

取交即得普适性。∎

## 因果解释

把动作解释为 intervention，C_A(q) 正是所有有限干预协议产生的读数画像。观测商到干预商的升级，不是“加入更多同类样本”，而是把允许的过程幺半群从自然时间扩展为干预词。

---

# 9. 交换与非交换 completion

设 F,G:X→X。

## 定理 9.1（交换 reflector）

若

$$
FG=GF,
$$

则

$$
C_F C_G(q)
≃
C_G C_F(q)
≃
C_{⟨F,G⟩}(q).
$$

### 证明

$$
K_{C_F C_G(q)}
=
⋂_{m,n≥0}(F^mG^n×F^mG^n)^{-1}K_q.
$$

交换性使词只依赖次数对 (m,n)，故三者 kernel 相同。∎

## 定义 9.1（自由词完成）

若 F,G 不交换，定义

$$
C_{F,G}^{free}(q)(x)
=
(q(F_wx))_{w∈{F,G}*}.
$$

## 原理 9.1（词序余量）

一次执行 C_F C_G 只保证特定块状词族闭合，不一定捕获交替词 FGF、GFG 等产生的新区别。

因此：

$$
非交换观察完成
=
对全部控制词闭合，
而非对每个生成元各做一次闭合。
$$

closure order 本身可以携带信息；这是历史路径依赖的一个精确来源。

---

# 10. 状态 kernel 与 effect 代数的反对偶

设 X 为有限集合，标量域为 ℝ。

## 定义 10.1（分块代数）

对等价关系 R，定义

$$
A_R
=
{f:X→ℝ : xRy ⇒ f(x)=f(y)}.
$$

## 定义 10.2（函数族的不可分辨关系）

对 A⊆ℝ^X，定义

$$
x R_A y
⇔
∀f∈A,
 f(x)=f(y).
$$

## 定理 10.1（有限 partition algebra 反同构）

等价关系与含常数、对线性组合和点乘封闭的 partition algebra 反同构：

$$
R_{A_R}=R,
$$

$$
A_{R_A}=A.
$$

### 证明概要

若 x 与 y 不在同一 R-block，取 x 所在 block 的指示函数即可区分它们。

反向，有限维交换幂等代数由最小非零指示幂等元分解；这些幂等元对应 R_A 的 blocks，因此 A 恰好是这些 blocks 上的常值函数代数。∎

## 推论 10.1（序反转）

$$
R₁⊆R₂
⇔
A_{R₂}⊆A_{R₁}.
$$

状态 kernel 越小，effect 代数越大。

---

# 11. 完成的状态—effect 对偶

对接口 q，令

$$
A_q={h∘q : h:B_q→ℝ}.
$$

定义 Koopman 拉回

$$
U_F f=f∘F.
$$

## 定义 11.1（动力生成代数）

$$
A_∞(q,F)
=
Alg(⋃_{n≥0} U_F^n A_q),
$$

其中 Alg 表示包含常数并对线性组合和点乘封闭的最小代数。

## 定理 11.1

$$
R_{A_∞(q,F)}
=
K_{C_F(q)}.
$$

### 证明

若两状态有相同未来行为词，则所有生成元 U_F^n(h∘q) 及其代数组合都取相同值。

反向若某个未来读数不同，有限集合上存在 B_q 上的函数 h 区分这两个读数，于是 U_F^n(h∘q) 区分原状态。∎

## 最深结构

$$
最大不变 state kernel
⇔
最小不变 effect algebra.
$$

这不是两个相似结论，而是同一 completion 的反对偶描述。

---

# 12. 有限维线性 completion

设 V,Y 为有限维内积空间，

$$
T:V→V,
$$

$$
C:V→Y.
$$

## 定义 12.1（有限深度不可观测子空间）

$$
N_m
=
⋂_{k=0}^{m} ker(C T^k).
$$

## 定义 12.2（对偶 Krylov 空间）

$$
O_m
=
span{(T*)^k C* y : 0≤k≤m, y∈Y}.
$$

## 定理 12.1（正交对偶）

$$
N_m=O_m^⊥.
$$

### 证明

x∈N_m 当且仅当对每个 k≤m 和 y∈Y：

$$
0
=
⟨C T^k x,y⟩
=
⟨x,(T*)^k C* y⟩.
$$

这正是 x⊥O_m。∎

定义极限对象

$$
N_∞=⋂_{k≥0}ker(C T^k),
$$

$$
O_∞=span_{k≥0}ran((T*)^k C*).
$$

## 定理 12.2

$$
N_∞=O_∞^⊥.
$$

## 定理 12.3（最大不可观测不变子空间）

N_∞ 是包含于 ker(C) 的最大 T-不变子空间。

### 证明

若 x∈N_∞，则

$$
C T^k(Tx)=C T^{k+1}x=0
$$

对所有 k 成立，所以 Tx∈N_∞。

若 M⊆ker(C) 且 T(M)⊆M，则对 x∈M、所有 k：

$$
T^k x∈M⊆ker(C),
$$

故 x∈N_∞。∎

## 推论 12.1

$$
V/N_∞
$$

是保留全部未来 C-读数的最粗线性商，并承载唯一诱导动力学。

---

# 13. 记忆商

当前接口 C 一步删除

$$
N₀=ker(C).
$$

其中永远不会影响未来读数的部分是 N_∞。

## 定义 13.1（线性记忆余量）

$$
M(C,T)
=
N₀/N_∞.
$$

它记录“当前不可见、但未来会变得可见”的方向。

## 定理 13.1（零记忆判据）

$$
M(C,T)=0
⇔
ker(C) 对 T 不变
⇔
T 沿 C 精确下降.
$$

### 证明

M(C,T)=0 当且仅当 ker(C)=N_∞。而 N_∞ 是 ker(C) 内最大 T-不变子空间，因此等价于 ker(C) 自身不变；这正是线性下降的 kernel 条件。∎

## 推论 13.1（记忆维数）

有限维时：

$$
dim M(C,T)
=
dim O_∞ - rank(C).
$$

这给出把当前读数变为精确 Markov 状态至少需要补回的独立线性区分数。

---

# 14. 可观测 Krylov 塔的有限停止

$$
O₀⊆O₁⊆O₂⊆…
$$

在有限维中必稳定。

## 定理 14.1（一次稳定永久稳定）

若

$$
O_m=O_{m+1},
$$

则

$$
O_{m+r}=O_m
$$

对所有 r≥0 成立。

### 证明

O_m=O_{m+1} 意味 T*O_m⊆O_m，以后全部新生成元都留在 O_m。∎

## 定理 14.2（严格增长次数界）

$$
#{m:O_m⊊O_{m+1}}
≤
dim(V)-rank(C).
$$

每次严格增长至少增加一维，而初始维数为 rank(C)。

---

# 15. 折扣可观测 Gramian

设 0<β<1，并满足足够收敛条件，例如

$$
√β ‖T‖<1.
$$

## 定义 15.1

$$
W_β
=
Σ_{n=0}^{∞} β^n (T*)^n C* C T^n.
$$

## 定理 15.1（能量恒等式）

$$
⟨x,W_βx⟩
=
Σ_{n=0}^{∞} β^n ‖C T^n x‖².
$$

### 证明

逐项计算

$$
⟨x,(T*)^n C* C T^n x⟩
=
⟨C T^n x,C T^n x⟩,
$$

再利用绝对收敛求和。∎

## 推论 15.1

$$
W_β≥0.
$$

## 定理 15.2（Gram kernel）

$$
ker(W_β)=N_∞.
$$

### 证明

若 x∈N_∞，每一项都为零。

反向若 W_βx=0，则

$$
0=⟨x,W_βx⟩
=
Σ_n β^n ‖C T^n x‖².
$$

每项非负且权重为正，所以每项均为零，x∈N_∞。∎

## 定理 15.3（Lyapunov 方程）

$$
W_β=C* C+β T* W_β T.
$$

### 证明

分离 n=0 项，其余项重指标即可。∎

---

# 16. 从 exact closure 到 conditioned closure

在可观测商 V/N_∞ 上，W_β 正定。定义

$$
λ_{min}^+(W_β)
$$

为最小正特征值。

## 定义 16.1（完成条件数）

$$
κ_β
=
λ_{max}(W_β)/λ_{min}^+(W_β).
$$

## 解释

- ker(W_β)=0：exact identifiability；
- λ_min^+ 很小：理论可识别但噪声下脆弱；
- κ_β 大：不同可观测方向被极不均匀地看到。

因此 observer completion 至少分为三层：

$$
exact closure,
$$

$$
conditioned closure,
$$

$$
realizable closure.
$$

布尔 kernel 只解决第一层；Gram 几何解决第二层；PSD、CP、admission 等约束决定第三层。

---

# 17. 近似下降的 Duhamel 恒等式

设候选下降动力学 A:Y→Y，并定义一步缺陷

$$
ε=CT-AC.
$$

## 定理 17.1

对每个 n≥1：

$$
C T^n - A^n C
=
Σ_{j=0}^{n-1} A^{n-1-j} ε T^j.
$$

### 证明

对 n 归纳。n=1 即定义。若对 n 成立，则

$$
C T^{n+1}-A^{n+1}C
=
(C T^n-A^nC)T+A^n(CT-AC),
$$

代入归纳假设并重指标。∎

## 推论 17.1（范数传播）

$$
‖C T^n-A^nC‖
≤
Σ_{j=0}^{n-1}
‖A‖^{n-1-j} ‖ε‖ ‖T‖^j.
$$

若 ‖A‖,‖T‖≤L<1，则

$$
‖C T^n-A^nC‖
≤
n L^{n-1} ‖ε‖.
$$

一步近似自然性如何沿时间传播，由此可以精确审计，而不能只用“误差很小”描述。

---

# 18. 量子 effect Krylov completion

设有限维量子通道为 Φ，其 Heisenberg 对偶为 Φ*；初始可观测 operator system 为 S₀。

## 定义 18.1（effect Krylov 塔）

$$
S_m
=
OSys{(Φ*)^k E : E∈S₀, 0≤k≤m}.
$$

## 定理 18.1（未来统计对偶）

对状态 ρ,σ，以下等价：

1. 对所有 E∈S₀、k≥0，
   $$
   Tr(Φ^k(ρ)E)=Tr(Φ^k(σ)E);
   $$
2. 对所有 A∈S_∞，
   $$
   Tr((ρ-σ)A)=0.
   $$

### 证明

使用 Heisenberg–Schrödinger 对偶：

$$
Tr(Φ^k(X)E)
=
Tr(X(Φ*)^kE).
$$

对所有生成元相等，当且仅当对其线性闭包相等。∎

## 物理边界

线性不可见方向 X 是否能写成两个物理状态之差

$$
X=ρ-σ
$$

还要与 PSD 锥和迹一截面相交。线性 completion 与物理 realization 不得混同。

---

# 19. Hamiltonian 嵌套交换子塔

对 Hamiltonian H，Heisenberg 流为

$$
α_t(E)=e^{itH}Ee^{-itH}.
$$

其导数为

$$
(d/dt)α_t(E)=i[H,α_t(E)].
$$

## 定义 19.1（交换子 Krylov 空间）

$$
K_H(S₀)
=
span{ad_H^k(E):E∈S₀,k≥0},
$$

其中

$$
ad_H(E)=[H,E].
$$

## 定理 19.1（解析流生成）

有限维中：

$$
span{α_t(E):t∈ℝ,E∈S₀}
=
K_H(S₀).
$$

### 证明概要

矩阵指数给出解析展开

$$
α_t(E)
=
Σ_{k≥0}(it)^k ad_H^k(E)/k!.
$$

所以左侧包含于右侧。反向可在 t=0 取各阶导数，或用有限维 Vandermonde 插值恢复嵌套交换子。∎

## 新解释

仓库已经证明投影概率导数由 [H,P] 控制。本文进一步得到：

$$
交换子不仅测量瞬时概率流，
还生成全部未来 effect completion 的切空间。
$$

---

# 20. 静态退相干与动态回流

设未读记录通道 D 是 Hilbert–Schmidt 正交投影。静态分解为

$$
X=DX+(I-D)X.
$$

对生成元或通道 L，定义动态回流块

$$
B_{return}=D L(I-D).
$$

它把当前被记录接口删除的相干余量重新送入可见块。

## 命题 20.1

静态丢失量

$$
‖(I-D)X‖_{HS}
$$

与动态回流强度

$$
‖B_{return}‖
$$

逻辑独立：

- 可以有巨大静态相干，但 B_return=0，以后永不影响记录；
- 可以有很小静态余量，但 B_return≠0，随后影响可见读数。

所以“退相干多少”和“预测接口是否闭合”不是同一个标量。

---

# 21. 因果实验是 target-kernel transversal

设有限模型类为 M，当前证据接口为

$$
E:M→Evidence,
$$

目标为

$$
T:M→Target.
$$

## 定义 21.1（目标未分辨对）

$$
P_T(E)
=
{(M,N):E(M)=E(N), T(M)≠T(N)}.
$$

实验 a 给出额外接口 E_a，并定义横切集

$$
S_a
=
{(M,N)∈P_T(E):E_a(M)≠E_a(N)}.
$$

## 定理 21.1（有限实验 cover 判据）

实验集 A₀ 使目标可识别，当且仅当

$$
P_T(E)
⊆
⋃_{a∈A₀}S_a.
$$

### 证明

联合接口不能区分的一对模型，恰好在所有选中实验下仍同值。目标可识别等价于不存在目标不同的这种模型对。∎

## 推论 21.1

有限目标实验设计是 set-cover／hitting-set 问题。mutual information 可以作为统计代价，但不能替代 target-pair cover 的结构判据。

高信息量实验可能只区分目标相同的模型；它增加知识，却不增加该目标的可识别性。

---

# 22. 完成对系统翻译的自然性

考虑两个动力接口系统

$$
(X,F,q),
$$

$$
(Y,G,r),
$$

以及映射 h:X→Y，满足

$$
hF=Gh,
$$

$$
r h=η q
$$

对某个读出映射 η。

## 定理 22.1

存在唯一映射

$$
C(h):B_{C_F(q)}→B_{C_G(r)}
$$

使

$$
C_G(r) h
=
C(h) C_F(q).
$$

### 证明

对每个 n：

$$
r(G^n h x)
=
r(h F^n x)
=
η(q(F^n x)).
$$

所以目标行为词逐坐标由源行为词决定；有效像满射给出唯一性。∎

## 推论 22.1

C 不只是对象级 closure operator，也是保持合法 semiconjugacy 的函子。observer completion 可以在系统翻译之间自然运输。

---

# 23. 最小行为实现

定义行为映射

$$
b_q(x)_n=q(F^n x),
$$

其像为

$$
Z_q=Im(b_q).
$$

左移在 Z_q 上良定义。

## 定理 23.1（规范最小实现）

设另有精确实现

$$
R:X→S,
$$

$$
ν:S→S,
$$

$$
o:S→B_q,
$$

满足

$$
RF=νR,
$$

$$
q=oR.
$$

则从可达实现部分 Im(R) 到 Z_q 存在唯一满射 π，使

$$
πR=b_q
$$

并与更新交换。

### 证明

定义

$$
π(Rx)=b_q(x).
$$

若 Rx=Ry，则对每个 n：

$$
q(F^n x)
=o(ν^n Rx)
=o(ν^n Ry)
=q(F^n y).
$$

故定义良好；像定义给出满射，R 对可达部分满射给出唯一性。∎

## 解释

$$
Z_q
=
所有精确读出保持实现的规范最小商。
$$

---

# 24. 局部 closure、gluing 与超限共同固定点

设有 closure operator 族

$$
{C_i}_{i∈I},
$$

分别强制不同动力学、context、prime 窗口或局部图表闭合。

有限偏序中，循环应用这些 closure 最终稳定。无限完备格中可能需要超限迭代：

$$
q₀=q,
$$

$$
q_{α+1}=⋁_{i∈I}C_i(q_α),
$$

$$
q_λ=⋁_{α<λ}q_α
$$

对极限序数 λ。

## 条件命题 24.1

若各 C_i 保持相应有向 join，则到某个闭包序数时得到最小公共固定点。

## 解释

局部每一块闭合，不等于全局一次拼接就闭合。剩余障碍可能位于：

- closure 次序；
- transition compatibility；
- limit-stage image；
- realizability；
- 非平凡 holonomy。

这为 prime-window、observer atlas 与 transfinite residual tower 提供同一组织语言。

---

# 25. 新研究推论

## 推论 25.1（记忆是 reflector 的单位余量）

反射单位

$$
q⪯C_F(q)
$$

新增的不是任意隐藏状态，而是原 kernel 与最大不变子kernel之间的相对差异。在线性模型中正是

$$
ker(C)/N_∞.
$$

所以：

$$
memory
=
unit of dynamical reflection measured inside the current fiber.
$$

## 推论 25.2（Gramian 是 completion 的度量化）

行为接口只给 partition；Gramian 给其商空间加上由全部未来读出诱导的二次型：

$$
Gram geometry
=
metric shadow of the behavior quotient.
$$

## 推论 25.3（交换子是 completion 导数）

Hamiltonian 情形中，i[H,E] 是 effect orbit 在 t=0 的时间导数；嵌套交换子塔生成全部 effect reflector。因此

$$
i·ad_H
=
observer-completion generator.
$$

## 推论 25.4（实验价值应提升最弱目标方向）

实验若只提升 Gram trace，却不提升目标 residual 上的最小特征值，可能增加大量与目标无关的信息而不改善识别。

合理的谱目标是提升

$$
λ_{min}(P_T(W+W_a)P_T),
$$

离散目标则应最大覆盖当前 target-distinct model pairs。

## 推论 25.5（路径依赖有两个来源）

必须区分：

1. 动力学不交换导致的 word-order residual；
2. 局部 closure 的 transition／gluing 不兼容。

前者即使载体全局平凡也存在；后者即使局部过程交换也可能存在。

---

# 26. 与仓库 Lean 真值的锚定

本文依赖并重新组织以下已闭合结果；不修改其证明：

| 结构 | Lean 锚点 | 本文角色 |
|---|---|---|
| 精确下降排除 carry | `D5/S3/ConceptDynamics/Dialectics/ExactDescentNoCarry.exact_descent_has_no_carry` | reflector 固定点的零缺陷方向 |
| 最小不变观察代数 | `D5/S3/Quantum/Dynamics/LeastInvariantObservableAlgebra.least_invariant_observable_algebra` | state–effect 反对偶的有限实例 |
| 未读状态正交投影 | `D5/S3/Observer/Conditioning/UnreadStateOrthogonalProjection.unread_state_orthogonal_projection` | 静态 Pythagoras 分解 |
| 投影概率交换子流 | `D5/S3/Quantum/Dynamics/ProjectionProbabilityFlow.projection_probability_flow` | Hamiltonian completion 生成元 |
| 极限残余正交分解 | `D5/S3/Quantum/Completion/LimitResidualDecomposition.limit_residual_orthogonal_decomposition` | state/effect 正交对偶 |
| 强而非一致完成 | `D5/S3/Quantum/Completion/InfiniteDimensionalProjectionSeparation.infinite_dimensional_projection_separation` | 极限完成边界 |
| 超限基残余塔 | `D5/S3/Quantum/Completion/TransfiniteBasisResidualTower.transfinite_basis_residual_tower` | 超限 closure 模型 |
| 有限 Fitting 分解 | `D5/S3/ObserverMemory/FunctionalGraphs/FiniteFunctionalGraphFittingDecomposition.finite_functional_graph_fitting_decomposition` | 最小实现的暂态／周期分解 |
| quotient–fiber 熵分解 | `D5/S3/Entropy/Fusion/QuotientFiberDecomposition.quotient_fiber_entropy_decomposition` | 完成信息链式背景 |
| 关系最强后件伴随 | `D5/S3/ObserverMemory/Knowledge/RelationalPreconditionAdjunction.relational_adjunction_and_may_not_guarantee` | 受控／关系 completion 背景 |
| 未来义务不完备 | `D5/S3/ConceptDynamics/Contracts/FutureObligationIncompleteness.nonfaithful_interface_future_incomplete` | 固定状态域区分下界 |
| 相位富化边等价 | `D5/S1/Words/Expansions/BasePhiNegativePrefixTridentEdge.phase_enriched_core_trace_iff_gap_phase` | 动态 factorization 前沿实例 |

本文新增的 reflector、Gram、Krylov、交换 closure 和记忆商定理尚未以本文形态 Lean 闭合。

---

# 27. 建议 Lean 模块树

```text
D5/S3/Observer/Completion/
  InterfaceOrder.lean
  StableInterface.lean
  BehaviorCompletion.lean
  CompletionClosureOperator.lean
  CompletionReflection.lean
  GreatestInvariantKernel.lean
  ControlledBehaviorCompletion.lean
  CommutingCompletion.lean
  FreeWordCompletion.lean

D5/S3/Observer/Duality/
  PartitionAlgebraDuality.lean
  StateEffectCompletion.lean

D5/S3/Observer/Linear/
  ObservableKrylovTower.lean
  UnobservableInvariantSubspace.lean
  MemoryQuotient.lean
  DiscountedObservabilityGramian.lean
  ObservabilityLyapunov.lean
  ApproximateDescentDuhamel.lean

D5/S3/Quantum/ObserverCompletion/
  EffectKrylovTower.lean
  HamiltonianCommutatorClosure.lean
  RecordDynamicReturn.lean
  MultiContextFreeWordClosure.lean

D5/S3/Observer/CausalDesign/
  TargetPairCover.lean
  InterventionKernelTransversal.lean

D5/S3/Observer/CompletionLimits/
  CommonFixedPointIteration.lean
  TransfiniteClosure.lean
```

建议优先形式化：

```text
interfaceRefines_iff_kernel_inclusion
behaviorCompletion_kernel
behaviorCompletion_stable
behaviorCompletion_least_stable_refinement
behaviorCompletion_monotone
behaviorCompletion_idempotent
behaviorCompletion_reflection
controlledCompletion_kernel
commutingCompletions_eq
partitionAlgebra_antiEquiv
stateEffect_completion_duality
unobservable_eq_observable_orthogonal
unobservable_maximal_invariant
memoryQuotient_zero_iff_descends
observabilityGramian_inner
observabilityGramian_kernel
observabilityGramian_lyapunov
approximateDescent_iterate_identity
finite_target_experiment_cover_iff
```

---

# 28. 最终统一

给定动力接口

$$
(X,F,q),
$$

存在四个互相对偶的对象：

$$
K_q
=
当前被合并的状态对,
$$

$$
K_∞
=
其中可永久保持合并的最大不变部分,
$$

$$
A_∞
=
由全部未来拉回生成的最小不变可观测代数,
$$

$$
C_F(q)
=
实现上述二者的规范最小稳定接口.
$$

在线性模型中：

$$
N₀=ker(C),
$$

$$
N_∞=⋂_{n≥0}ker(C T^n),
$$

$$
O_∞=span_{n≥0}ran((T*)^n C*),
$$

$$
W_β=Σ_{n≥0}β^n(T*)^n C* C T^n,
$$

并满足

$$
N_∞=O_∞^⊥=ker(W_β).
$$

当前接口真正缺失的记忆不是全部 ker(C)，而是

$$
M(C,T)=ker(C)/N_∞.
$$

对受控系统，时间迭代替换为动作词；对量子系统，状态读数替换为 Heisenberg effect 词；对非交换过程，closure 次序与自由词结构本身成为余量；对因果系统，实验必须横切 target-distinct model pairs，而不是泛化地“增加信息”。

本文的最终结论是：

$$
观察者完成不是把世界全部复制进观察者，
而是把当前 fiber 中仍具有未来效力的区别，
以最小稳定、可组合、可度量的方式重新加入接口。
$$

更短地：

$$
completion
=
reflection into stable interfaces,
$$

$$
memory
=
relative kernel removed by that reflection,
$$

$$
Gramian
=
metric shadow of the reflected behavior space,
$$

$$
commutator
=
infinitesimal generator of effect completion.
$$

---

# 29. 严格非主张

1. 本文不声称所有 observer completion 都是有限维线性的。
2. 本文不声称任意接口偏序自动具备所需的全部 join。
3. 本文不声称非满射 codomain 上的下降映射唯一；唯一性均在有效像上。
4. 本文不声称稳定接口对子接口或商接口封闭。
5. 本文不声称非交换 closure residual 自动具有群、环或普通上同调结构。
6. 本文不声称分别闭合每个 context 一次足以得到自由词闭合。
7. 本文不声称 Gramian 正定自动给出物理可实现状态差。
8. 本文不声称 Hilbert–Schmidt 正交性替代 PSD、CP 或 complete positivity。
9. 本文不声称折扣 Gramian 在无收敛条件时存在为有界算子。
10. 本文不声称最小正特征值在无限维中自动与零隔离。
11. 本文不声称 mutual information 与 target-pair cover 等价。
12. 本文不声称有限 set-cover 直接解决连续 SCM 实验设计。
13. 本文不声称 nested commutator span 在无限维无界算子情形无需域分析。
14. 本文不声称静态退相干余量与动态回流强度相同。
15. 本文不声称预测 reflector 解决 representation surjectivity。
16. 本文不声称预测 reflector 消除 Cantor–Lawvere 对角逃逸。
17. 本文不声称 local closure 自动 glue 为 global closure。
18. 本文不声称超限 closure 一定在可数阶段停止。
19. 本文新增定理未经 Lean kernel 验证不得标记为 `Closed`。
20. 本文没有证明 Riemann 假设或 negative-base-φ 主分类定理。

---

# 30. 增订：喉部运动、控制选择与自由策略

**增订版本：v1.2，2026-08-25**

本增订只追加在原文之后，不改写前二十九节。它把以下此前分散的问题合并为一条严格链：

1. universal solenoid 的“喉部”中究竟允许什么连续运动；
2. 同一可见相位下的端点变化何时只是整数绕行，何时是真正跨流线跳跃；
3. cocycle、控制动作、选择策略与测量结果为何必须分层；
4. 为什么“没有结构必然的唯一策略”可以为自由留下形式席位，却尚不足以构成自由意志定理；
5. 如何把有限观察者、完整控制画像、预测充分性、信息逃逸与追加式账本组装为一个可形式化的行动语义。

本增订继续沿用原文的真值纪律：仓库已有 Lean theorem 的部分标记为 **Lean 锚点**；由这些 theorem 直接推出但尚未以同名声明封装的部分标记为 **本文推论**；涉及路径分量商、跳跃策略或自由意志归属的部分标记为 **条件定义／研究命题**。

---

# 31. 喉部、可见相位与路径分量

设 universal solenoid 具有正合列

$$
0
\longrightarrow
K_\infty
\xrightarrow{\iota}
\Sigma_\infty
\xrightarrow{\pi}
\mathbb T
\longrightarrow
0,
$$

其中

$$
K_\infty
\cong
\prod_{p\in\mathbb P}\mathbb Z_p.
$$

这里：

- $\Sigma_\infty$ 是完整状态空间；
- $\mathbb T$ 是公开可见的相位圆；
- $K_\infty=\ker\pi$ 是隐藏素数地址空间；
- $\pi^{-1}(\theta)$ 是公开相位 $\theta$ 上方的隐藏纤维，本文称为“喉部”。

## 定理 31.1（归一化流线分解；Lean 锚点）

对任意连续路径

$$
\gamma:\mathbb R\to\Sigma_\infty,
$$

固定基准时刻与可见相位的实代表后，存在唯一连续实提升 $r$ 与唯一时间无关的隐藏偏移 $k_0$，使

$$
\gamma(t)
=
\operatorname{realFlow}(r(t))
+
\iota(k_0).
$$

对应仓库锚点：

```text
D5/S1/Solenoid/StreamlineDecomposition.
  existsUnique_normalized_streamline
```

### 结论

连续完整路径可以改变可见提升 $r(t)$，但不能连续改变隐藏流线标签 $k_0$。因此严格结论不是“完整 solenoid 中没有连续运动”，而是：

$$
\boxed{
连续运动只能沿一条 real-flow 流线发生；
纯隐藏偏移沿连续时间恒定。
}
$$

## 定理 31.2（路径可达即 real-flow 同轨；Lean 锚点）

对任意 $x,y\in\Sigma_\infty$：

$$
\operatorname{Joined}(x,y)
\iff
\exists t\in\mathbb R,
\quad
y=\operatorname{realFlow}(t)+x.
$$

对应仓库锚点：

```text
D5/S1/Solenoid/PathOrbitClassification.
  path_joined_iff_real_flow_orbit
```

## 推论 31.1（同一可见纤维的整数绕行判据；本文推论）

若

$$
\pi(x)=\pi(y),
$$

则

$$
\operatorname{Joined}(x,y)
\iff
\exists n\in\mathbb Z,
\quad
y=\operatorname{realFlow}(n)+x.
$$

### 证明

由定理 31.2，路径相连等价于存在 $t\in\mathbb R$ 使

$$
y=\operatorname{realFlow}(t)+x.
$$

作用 $\pi$ 并利用 $\pi(x)=\pi(y)$，得到

$$
0
=
\pi(\operatorname{realFlow}(t))
=
t\pmod{\mathbb Z}.
$$

故 $t\in\mathbb Z$。反向由定理 31.2 立即成立。∎

这一区分修正了“同一喉部中的任何端点变化都是不可连续跳跃”的过强说法。若差值是整数 real-flow 端点，它可由完整空间中的连续绕行实现；只有不属于该整数子群的横向位移才真正跨路径分量。

---

# 32. 路径分量商与三类隐藏变化

在标准 solenoid 商表示中，可把状态写成

$$
[t,k],
\qquad
t\in\mathbb R,
\quad
k\in K_\infty,
$$

并按对角整数嵌入 $\Delta:\mathbb Z\to K_\infty$ 识别

$$
(t,k)
\sim
(t+n,k-\Delta(n)).
$$

符号正负依具体坐标约定而变，但商类不变。

## 条件定义 32.1（流线分量坐标）

定义候选分量映射

$$
\operatorname{Comp}:\Sigma_\infty
\longrightarrow
K_\infty/\Delta(\mathbb Z)
$$

为

$$
\operatorname{Comp}([t,k])=[k].
$$

标准商模型中它是良定义的，因为改变提升 $t\mapsto t+n$ 只会同时把 $k$ 改变一个对角整数。

## 条件命题 32.1（分量分类）

在上述商接口完成后，应有

$$
\operatorname{Joined}(x,y)
\iff
\operatorname{Comp}(x)=\operatorname{Comp}(y).
$$

这与定理 31.2 等价地表达“路径分量就是 real-flow 轨道”。当前仓库已经机器证明轨道分类，但尚未公开完成 $K_\infty/\mathbb Z$ 的 typed quotient/jump API；因此本命题在本文中只作标准模型的条件封装，不冒充已有 Lean 声明。

## 定义 32.2（隐藏位移的分量荷）

对 $\kappa\in K_\infty$，定义其分量荷

$$
[\kappa]
\in
K_\infty/\Delta(\mathbb Z).
$$

由此，隐藏变化分为三类。

### 第一类：纯可见连续运动

$$
x(t)=\operatorname{realFlow}(r(t))+x_0,
$$

它留在同一分量中。

### 第二类：整数绕行型隐藏端点变化

$$
y=x+\iota(\Delta(n)),
\qquad n\in\mathbb Z.
$$

从固定可见截面看，隐藏端点改变；从完整 $\Sigma_\infty$ 看，它可由绕圆 $n$ 次的连续路径实现，且

$$
[\Delta(n)]=0.
$$

### 第三类：横向跨流线跳跃

$$
y=x+\iota(\kappa),
$$

其中

$$
[\kappa]\neq0.
$$

它不能由任何连续完整路径实现。

## 命题 32.2（横向跳跃判据；条件于分量接口）

若平移

$$
T_\kappa(x)=x+\iota(\kappa),
$$

则

$$
T_\kappa
\text{ 改变路径分量}
\iff
[\kappa]\neq0.
$$

### 证明

由分量加法性：

$$
\operatorname{Comp}(T_\kappa x)
=
\operatorname{Comp}(x)+[\kappa].
$$

所以分量保持当且仅当 $[\kappa]=0$。∎

---

# 33. 连续刚性、整数动作与当前桥缺口

## 定理 33.1（纯隐藏连续实流为零；Lean 锚点）

任意连续加法同态

$$
\Phi:\mathbb R\to K_\infty
$$

都满足

$$
\Phi=0.
$$

对应仓库锚点：

```text
D5/S3/Observer/HiddenFlow/ContinuousRigidity.
  continuous_hidden_flow_eq_zero
```

这一定理只排除非平凡的连续实参数**纯隐藏流**。它没有证明所有非平凡隐藏动作都由整数参数化，也没有从拓扑中选出某一个物理动作。

## 定理 33.2（非零整数隐藏动作无连续实扩张；Lean 锚点）

若

$$
J:\mathbb Z\to K_\infty
$$

是非零加法同态，则不存在连续加法同态

$$
\Phi:\mathbb R\to K_\infty
$$

满足

$$
\Phi|_\mathbb Z=J.
$$

对应仓库锚点：

```text
D5/S3/Observer/HiddenFlow/DiscreteRigidity.
  nonzero_integer_action_has_no_continuous_real_extension
```

仓库另给出显式非零见证

$$
J_{\mathrm{can}}(n)_p=n\in\mathbb Z_p.
$$

## 严格边界 33.1

目前不能把以下两件事直接当作已机器证明的同一对象：

1. `discreteHiddenJump n` 的逐 $p$-进坐标整数 cast；
2. `realFlow n` 在 solenoid 核中的端点。

在标准模型中二者自然对应对角整数方向，但当前公开 Lean 声明中尚缺一个逐坐标桥定理。因此本增订不把

$$
J_{\mathrm{can}}(n)=\operatorname{realFlow}(n)
$$

列为已闭合等式。

## 结论 33.1

“不能在 $K_\infty$ 内连续参数化”与“不能在完整 $\Sigma_\infty$ 中由连续路径连接”是不同命题。前者由定理 33.2成立；后者必须进一步检查位移在

$$
K_\infty/\Delta(\mathbb Z)
$$

中的商类。

---

# 34. cocycle 规定组合一致性，不规定选择理由

令 $G$ 为允许控制动作的幺半群，并设其对完整状态的作用为

$$
T_g:\Sigma_\infty\to\Sigma_\infty.
$$

若隐藏位移依赖动作和当前状态，引入

$$
c:G\times\Sigma_\infty\to K_\infty.
$$

## 定义 34.1（隐藏地址 cocycle）

对左作用，要求

$$
c(gh,x)
=
c(g,T_hx)+c(h,x).
$$

这保证“先做 $h$ 再做 $g$”与“直接做 $gh$”的隐藏地址总账一致。

## 命题 34.1（cocycle 的职责）

cocycle 回答的是：

$$
\boxed{
已选动作怎样组合，
以及总隐藏位移怎样入账。
}
$$

它不回答：

$$
\boxed{
当前为什么选择 g 而不是 h。
}
$$

前者属于动力与账本一致性；后者属于 policy。把二者混同，会错误地从“动作有组合律”推出“动作选择被唯一决定”。

## 定义 34.2（分量 cocycle）

在分量商存在时，定义

$$
\bar c(g,x)
=
[c(g,x)]
\in
K_\infty/\Delta(\mathbb Z).
$$

则

$$
\bar c(g,x)=0
$$

表示该动作在路径分量层只是同流线／整数绕行型；

$$
\bar c(g,x)\neq0
$$

表示真正跨流线迁移。

---

# 35. 规律、控制语法、策略与结果的四层分离

令完整状态为 $x\in X$，动作集合为 $A$。

## 定义 35.1（合法动作关系）

$$
\operatorname{Legal}(x,a)
$$

表示动作 $a$ 在状态 $x$ 下可执行。定义

$$
\mathcal A(x)
=
\{a\in A:\operatorname{Legal}(x,a)\}.
$$

## 定义 35.2（后果核）

$$
P(x'\mid x,a)
$$

给出执行 $a$ 后完整状态的条件分布；确定性动力学是其 Dirac 特例。

## 定义 35.3（策略）

确定性策略是

$$
\pi:X\to A,
\qquad
\pi(x)\in\mathcal A(x).
$$

随机策略是

$$
\Pi:X\to\operatorname{Dist}(A),
$$

且支撑包含于 $\mathcal A(x)$。

因此：

$$
\boxed{
规律规定哪些动作合法以及各动作会造成什么；
策略规定实际选择哪个动作。
}
$$

前两项并不逻辑蕴含第三项。

## 结论 35.1

一个完整理论可以精确给出

$$
\mathcal A(x)
$$

和

$$
P(\cdot\mid x,a)
$$

而仍不提供唯一的

$$
\pi(x).
$$

这不是形式矛盾；它只说明动力学是一个受控关系，而不是已经替代理主体完成了控制选择的单值函数。

---

# 36. 有限观察者的策略可实现性

观察者不能直接访问完整状态 $x$，只访问接口

$$
q:X\to O.
$$

## 定义 36.1（$q$-可实现策略）

策略 $\Pi:X\to\operatorname{Dist}(A)$ 称为可由接口 $q$ 实现，若存在

$$
\bar\Pi:O\to\operatorname{Dist}(A)
$$

使

$$
\Pi=\bar\Pi\circ q.
$$

## 定理 36.1（策略因子化判据；本文定理）

$$
\Pi
\text{ 可由 }q\text{ 实现}
\iff
q(x)=q(y)
\Rightarrow
\Pi(x)=\Pi(y).
$$

### 证明

左向由函数合成立即得到。反向定义

$$
\bar\Pi(q(x)):=\Pi(x).
$$

纤维常值条件保证代表元无关；把 codomain 限制到 $q$ 的有效像即得唯一性。∎

这给出一个严格禁令：若策略依赖同一观察纤维内被隐藏的真实喉部地址，则该策略不能被这个有限观察者执行。把隐藏状态偷偷输入 policy，会把外部全知控制器冒充成内部观察者。

---

# 37. 完整控制画像是策略的规范信息底座

设幺半群 $G$ 作用于 $X$，公开读出为

$$
q:X\to O.
$$

定义完整控制画像

$$
\operatorname{Ctrl}_q(x)(g)
=
q(g\cdot x).
$$

定义控制等价

$$
x\sim_{\mathrm{ctl}}y
\iff
\forall g\in G,
\quad
q(g\cdot x)=q(g\cdot y).
$$

仓库已经证明，按完整控制画像取商得到的控制商：

1. 恢复当前公开读出；
2. 承载每个控制动作诱导的商上动作；
3. 决定每个动作的公开后果；
4. 是具有这些性质的最粗接口；
5. 与有限干预词的动态闭包在 kernel 层相同。

对应 Lean 锚点：

```text
D5/S3/ConceptDynamics/Control/ControlQuotientUniversalMinimality.
  control_quotient_universal_minimality
```

## 原理 37.1（后果充分而非动作唯一）

控制商告诉观察者：

$$
\boxed{
每个允许动作会公开地产生什么后果。
}
$$

它不自动告诉观察者：

$$
\boxed{
这些动作中哪一个必须被选择。
}
$$

因此“完整控制知识”与“唯一控制意志”不是同一结构。

## 定义 37.1（观察者 policy 的规范类型）

合理的策略接口应至少具有形状

$$
\bar\Pi_O:
Q_{\mathrm{ctl}}
\times
\mathrm{Goal}
\times
\Lambda
\longrightarrow
\operatorname{Dist}(G),
$$

其中：

- $Q_{\mathrm{ctl}}$ 是完整控制画像商；
- $\mathrm{Goal}$ 表示目标、价值或损失；
- $\Lambda$ 是此前追加式记录；
- 输出只在允许动作上有支撑。

目标与账本不是多余输入：相同控制画像在不同价值承诺下可以合理地产生不同选择。

---

# 38. 预测充分性只给出最优集合，不强制唯一元素

设预测接口为

$$
K:X\to\operatorname{PMF}(Y),
$$

动作损失为

$$
\ell:A\times Y\to\mathbb R.
$$

定义期望损失

$$
R(x,a)
=
\int_Y\ell(a,y)\,dK(x)(y).
$$

以及最优动作集合

$$
A^*(x)
=
\operatorname*{arg\,min}_{a\in A}R(x,a).
$$

仓库已证明：若一个概念足以决定完整预测分布 $K(x)$，它也足以决定全部期望损失和最优动作集合。

对应 Lean 锚点：

```text
D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiency.
  prediction_sufficiency_implies_decision_sufficiency
```

## 推论 38.1

即使

$$
A^*(x)
$$

被完全决定，也可能有

$$
|A^*(x)|>1.
$$

所以：

$$
\boxed{
决策充分性
\neq
唯一策略充分性。
}
$$

若人为加入固定全序并选取最小元素，确实可得到一个确定性 selector；但该 selector 的唯一性来自新增 tie-breaker，而不是来自原有物理、预测或价值结构。

---

# 39. 无典范选择定理

没有唯一最优动作仍可能只是普通平局。更强的结构障碍来自对称性。

设群 $\Gamma$ 同时作用于状态空间 $X$ 与动作空间 $A$，并保持全部已申报结构。一个“纯由结构给出”的确定性策略至少应满足等变性：

$$
\sigma(\gamma x)
=
\gamma\sigma(x).
$$

## 定理 39.1（无等变确定性 selector）

若存在 $x\in X$ 与 $\gamma\in\Gamma$ 满足

$$
\gamma x=x,
$$

但 $\gamma$ 在合法动作集 $\mathcal A(x)$ 上没有固定点：

$$
\forall a\in\mathcal A(x),
\quad
\gamma a\neq a,
$$

则不存在等变确定性 selector

$$
\sigma(x)\in\mathcal A(x).
$$

### 证明

假设存在。由 $\gamma x=x$ 和等变性：

$$
\sigma(x)
=
\sigma(\gamma x)
=
\gamma\sigma(x).
$$

所以 $\sigma(x)$ 是 $\gamma$ 的固定动作，与假设矛盾。∎

## 推论 39.1

当两个行动在此前全部结构中完全对称时，结构本身不可能在保持该对称性的同时无偏选出其中一个。

实际打破对称性的来源只能新增于下列至少一类：

1. 观察者自己的记忆、价值、承诺或身份；
2. 外部环境或隐藏控制变量；
3. 无主随机索引；
4. 显式加入的非对称 tie-breaker。

## 严格边界 39.1

$$
\neg\exists\text{ canonical selector}
$$

并不推出

$$
\neg\exists\text{ deterministic selector}.
$$

非典范性只说明结构没有自然指定哪一个；它没有排除某个更丰富完整状态上的确定性规律。

---

# 40. 没有必然策略是自由的席位，不是自由本身

必须区分三层。

## 定义 40.1（结构自由）

不存在由当前已申报结构唯一、自然地给出的 selector：

$$
\text{No canonical policy}.
$$

这是本增订从对称性与控制商最稳健支持的层次。

## 定义 40.2（自主自由）

行动对观察者自己的理由、记忆、目标和承诺真实敏感，而不只是外部环境的直接函数。

设

$$
e:X\to E
$$

为环境接口，

$$
o:X\to O
$$

为观察者内部接口，

$$
\chi:X\to A
$$

为实际行动。

若存在

$$
f:E\to A
$$

使

$$
\chi=f\circ e,
$$

则行动完全由环境接口决定，观察者在该模型中只是传动部件。

一个最低限度的内部敏感性见证是：

$$
\exists x,y,
\quad
e(x)=e(y),
\quad
o(x)\neq o(y),
\quad
\chi(x)\neq\chi(y).
$$

它说明在外部条件相同的比较中，观察者内部状态改变了行动。

## 定义 40.3（本体自由）

给定完整过去状态，仍有两个不同未来行动都是真实可达的：

$$
\exists x,a\neq b,
\quad
R(x,a,x_a)
\land
R(x,b,x_b).
$$

并且实际化哪一支既不由隐藏变量预先指定，也不只是无主噪声。

## 结论 40.1

当前仓库结构至多为第一层提供清晰形式席位，并可为第二层建立 factorization 与理由响应条件；它没有证明第三层。

因此正确命题是：

$$
\boxed{
没有必然策略是自由意志的必要开放空间之一；
但随机性、欠建模或非典范性本身都不等于自由意志。
}
$$

---

# 41. 作者性：原因的归属而非原因的消失

“自由”不应被定义为行动没有原因。无原因噪声不能自动成为主体行动。

## 定义 41.1（作者性候选）

令观察者状态由

$$
O_t=(m_t,v_t,g_t,s_t)
$$

组成，其中分别代表记忆、价值、目标与自我模型。行动规则若具有

$$
a_t
\in
\operatorname{Acceptable}(O_t,E_t,\Lambda_t),
$$

并且改变 $O_t$ 的理由结构会系统性改变可接受行动与实际行动，则行动可归属于该观察者的内部组织。

## 原理 41.1（原因归属三分）

- 外部状态绕过观察者内部结构直接决定行动：他律；
- 无主随机数替代主体打破平局：偶然；
- 观察者的记忆、价值、目标与承诺参与构成行动：主体性候选。

因此自由意志最适合被问成：

$$
\boxed{
打破未定性的原因属于谁？
}
$$

而不是简单问：

$$
\boxed{
行动有没有原因？
}
$$

---

# 42. 从单值策略改为可接受动作关系

与其在理论底层强行规定

$$
\pi(x)=a,
$$

更自然的是先定义

$$
\operatorname{Acceptable}_O(z,\Lambda,a).
$$

## 定义 42.1（观察者可接受动作集）

$$
\mathcal A_O(z,\Lambda)
=
\left\{
 a:
 \begin{array}{l}
 \operatorname{Legal}(z,a),\\
 \operatorname{Affordable}(z,a),\\
 \operatorname{GoalCoherent}_O(z,a),\\
 \operatorname{LedgerConsistent}_O(\Lambda,a),\\
 \operatorname{IdentityPreserving}_O(\Lambda,a)
 \end{array}
\right\}.
$$

规律层只要求

$$
a_t\in\mathcal A_O(z_t,\Lambda_t).
$$

它不必再给出唯一元素。

## 定义 42.2（选择事件）

$$
\operatorname{Choose}_O(z_t,\Lambda_t,a_t)
$$

表示观察者使某个可接受行动成为实际执行的行动。

该定义只为作者性保留槽位；它没有通过重命名解决自由意志。要把它提升为实质理论，仍须证明：

1. 选择不依赖观察者不可访问的隐藏坐标；
2. 选择对内部理由结构响应；
3. 选择不是外部 controller 的伪装；
4. 选择不是仅以随机种子替代主体；
5. 选择被后续记录和承诺结构所承担。

---

# 43. 自由在选择后可以生成自我施加的必然

追加式账本给自由一个重要的时间结构：选择发生前有分岔，选择发生后分岔被写入历史。

设

$$
\Lambda_{t+1}
=
\Lambda_t\mathbin{\Vert}a_t.
$$

若后续合法动作必须与账本中的承诺一致，定义

$$
\mathcal A_{t+1}(x)
=
\{a:\operatorname{Consistent}(a,\Lambda_{t+1})\}.
$$

## 命题 43.1（自我约束单调性）

若一致性谓词把新记录作为附加约束，则

$$
\mathcal A_{t+1}(x)
\subseteq
\mathcal A_t(x).
$$

### 证明

任何满足新账本全部约束的动作，必满足旧账本中已有的全部约束；新账本还可能排除违反新承诺的动作。∎

## 解释

$$
\boxed{
自由不是永远保持全部可能性开放；
自由也可以是主动关闭可能性，
把一次选择固化为未来人格的约束。
}
$$

因此确定性不总是自由的反面。若未来行动由观察者此前自由接受的承诺所约束，它可被理解为

$$
\text{Will}
\longrightarrow
\text{Commitment}
\longrightarrow
\text{Self-imposed necessity}.
$$

这一结构与“观察者是相容记录链”相容：身份不是一个无历史的瞬时 selector，而是其选择被不断追加后形成的约束系统。

---

# 44. 信息逃逸驱动的动作选择

若目标不是一般效用，而是消除特定目标的不确定性，可把原文第 21 节的 target-kernel transversal 与受控动作结合。

设当前接口为 $q$，目标为 $T$，目标残差关系为

$$
\mathcal E(q;T)
=
\{(x,y):q(x)=q(y),\ T(x)\neq T(y)\}.
$$

动作 $a$ 产生新读出 $d_a$。

## 定义 44.1（动作的结构捕获量）

$$
\Delta_T(a\mid q)
=
\mu\left(
\mathcal E(q;T)
\cap
(\ker d_a)^c
\right).
$$

## 定义 44.2（动作的有效信息增益）

令随机变量

$$
Q=q(X),
\qquad
D_a=d_a(X),
\qquad
Y=T(X).
$$

定义

$$
G_T(a\mid q)
=
I(Y;D_a\mid Q).
$$

结构捕获量与条件互信息不能混同：前者计目标残差对被切开的质量，后者计目标条件熵真正下降的 bit。

## 定义 44.3（预算信息 policy）

给定成本 $c(a)$ 与预算 $B$，可定义最优动作集合

$$
A^*_{\mathrm{info}}(q)
=
\operatorname*{arg\,max}_{c(a)\le B}
\left[
I(Y;D_a\mid Q)-\lambda c(a)
\right].
$$

或者使用单位成本增益：

$$
\operatorname*{arg\,max}_{0<c(a)\le B}
\frac{I(Y;D_a\mid Q)}{c(a)}.
$$

## 严格边界 44.1

该原则给出一个可审计的**策略族**，不是宇宙必然采用的唯一策略。不同目标、成本、风险偏好和时间折扣会产生不同最优集合；同一最优集合仍可能存在对称平局。

---

# 45. 动作选择与量子结果选择必须分开

观察者可以选择测量设置或上下文

$$
\mathcal C_a=\{E_j^{(a)}\}_j,
$$

但给定状态 $\rho$ 后，结果概率为

$$
p(j\mid a,\rho)
=
\operatorname{Tr}(\rho E_j^{(a)}).
$$

结果记录满足

$$
j\sim p(\cdot\mid a,\rho).
$$

若由 instrument $M_j^{(a)}$ 实现，则条件化状态为

$$
\rho'
=
\frac{
M_j^{(a)}\rho M_j^{(a)\dagger}
}{
p(j\mid a,\rho)
}.
$$

严格时序是：

$$
\boxed{
选择设置 a
\longrightarrow
产生并登记结果 j
\longrightarrow
观察者对 j 条件化。
}
$$

不是：

$$
\boxed{
观察者先选择 j，
世界再配合跳到 j。
}
$$

因此自由的自然候选席位在设置格、控制格、记账格和承诺格，而不是在单次 Born 结果格。把结果偏置解释为意志，还必须同时面对非信号、上下文一致性与实验统计约束。

---

# 46. 本体跳跃、控制跳跃、认识跳跃与记录跳跃

“跳跃”至少有四种不同含义。

| 层 | 对象 | 数学形式 | 是否由观察者选择 |
|---|---|---|---|
| 本体跳跃 | 完整状态的路径分量 | $\operatorname{Comp}(x')\neq\operatorname{Comp}(x)$ | 只有在控制语法允许且被实际执行时才可能相关 |
| 控制跳跃 | 离散动作 | $x' = T_a(x)$ | 设置／动作可由 policy 选择 |
| 认识跳跃 | 信念或认识纤维收缩 | $F_{t+1}=F_t\cap d_a^{-1}(y)$ | 结果后由条件化规则确定 |
| 记录跳跃 | 追加新账目 | $\Lambda_{t+1}=\Lambda_t\Vert(a,y)$ | 动作记录可选择，已发生结果不可改写为未发生 |

## 定义 46.1（认识更新）

若观察者对完整状态持有信念 $b_t$，则得到记录 $y_t$ 后：

$$
b_{t+1}(x)
=
\frac{
P(y_t\mid x,a_t)b_t(x)
}{
\int P(y_t\mid x',a_t)b_t(x')\,dx'
}.
$$

确定性读出时：

$$
b_{t+1}(x)
\propto
\mathbf 1_{\{d_{a_t}(x)=y_t\}}b_t(x).
$$

从完整系统看，可能只是一次控制、耦合与记录；从有限观察者看，大量此前仍可能的隐藏地址被瞬时排除，因此表现为认识跳跃。

---

# 47. 一步完整操作语义

定义观察者—喉部系统

$$
\mathfrak M
=
(
\Sigma_\infty,
K_\infty,
G,
q,
c,
P,
\ell,
\mathrm{cost},
\Lambda
).
$$

第 $t$ 步可严格拆为：

## 47.1 形成控制状态

$$
z_t
=
Q_{\mathrm{ctl}}(x_t)
$$

或维护后验信念 $b_t$。

## 47.2 构造可行动作集

$$
\mathcal A_t
=
\left\{
 a\in G:
 \operatorname{Legal}(a,z_t,\Lambda_t),
 \quad
 \mathrm{cost}(a)\le B_t
\right\}.
$$

## 47.3 计算动作后果

$$
P_a(y\mid z_t)
$$

以及期望损失、信息增益或其他已申报评价量。

## 47.4 形成可接受集合并作选择

$$
A_t^*
\subseteq
\mathcal A_t,
$$

$$
a_t\in A_t^*.
$$

理论可以决定 $A_t^*$；是否存在由结构唯一决定的 $a_t$ 是另一个问题。

## 47.5 执行状态更新

$$
x_t^+
=
T_{a_t}(x_t).
$$

若分量 cocycle 已定义，则

$$
\operatorname{Comp}(x_t^+)
=
\operatorname{Comp}(x_t)
+
\bar c(a_t,x_t).
$$

## 47.6 追加动作账

$$
\Lambda_t^+
=
\Lambda_t
\mathbin{\Vert}
(a_t,c(a_t,x_t),\mathrm{source},\mathrm{time},\mathrm{detector}).
$$

## 47.7 获得结果并条件化

$$
y_t
\sim
P_{a_t}(\cdot\mid x_t^+),
$$

$$
\Lambda_{t+1}
=
\Lambda_t^+\mathbin{\Vert}y_t,
$$

$$
b_{t+1}
=
P(x_{t+1}\mid\Lambda_{t+1}).
$$

其中真正作为“策略选择”的是 47.4；cocycle 负责 47.5 的地址组合一致性；结果分布负责 47.7；条件化负责观察者认识更新。

---

# 48. 新研究命题与证明状态

## 命题 48.1（同纤维路径判据）

$$
\pi(x)=\pi(y)
\Rightarrow
\left[
\operatorname{Joined}(x,y)
\iff
\exists n\in\mathbb Z,
\ y=\operatorname{realFlow}(n)+x
\right].
$$

**状态**：由现有路径轨道定理直接推出，适合独立 Lean 封装。

## 命题 48.2（分量荷判据）

$$
T_\kappa
\text{ 跨路径分量}
\iff
[\kappa]\neq0
\text{ in }K_\infty/\Delta(\mathbb Z).
$$

**状态**：依赖尚未公开完成的路径分量 quotient API。

## 命题 48.3（观察者策略因子化）

$$
\Pi
\text{ 可由 }q\text{ 实现}
\iff
K_q\subseteq K_\Pi.
$$

**状态**：普通 kernel-factorization 定理的直接实例，适合 Lean 化。

## 命题 48.4（无典范选择）

固定状态具有无固定动作的对称稳定子时，不存在等变确定性 selector。

**状态**：群作用上的短证明，可独立 Lean 化。

## 命题 48.5（承诺导致可行动作集收缩）

若账本一致性条件按追加记录单调加强，则

$$
\mathcal A_{t+1}\subseteq\mathcal A_t.
$$

**状态**：依赖具体 ledger-consistency carrier；一般关系版容易形式化。

## 命题 48.6（非典范不等于主体自由）

存在两个反例模型：

1. 对称硬币随机打破平局：无典范确定性 selector，但无内部作者性；
2. 内部理由状态确定性选择：策略确定，却可满足外部环境相同、内部理由不同导致行动不同。

所以

$$
\text{noncanonical}
\not\Rightarrow
\text{agency},
$$

且

$$
\text{deterministic}
\not\Rightarrow
\text{nonfree}.
$$

**状态**：有限 Bool 反例可机器化。

---

# 49. 与当前仓库真值的追加锚定

| 结论 | 当前锚点 | 状态 |
|---|---|---|
| 连续 solenoid 路径 = 实提升 + 恒定隐藏偏移 | `D5/S1/Solenoid/StreamlineDecomposition.existsUnique_normalized_streamline` | Lean closed |
| 路径相连 iff 同一 real-flow 轨道 | `D5/S1/Solenoid/PathOrbitClassification.path_joined_iff_real_flow_orbit` | Lean closed |
| 纯隐藏连续加法实流为零 | `D5/S3/Observer/HiddenFlow/ContinuousRigidity.continuous_hidden_flow_eq_zero` | Lean closed |
| 非零整数隐藏动作无连续实扩张 | `D5/S3/Observer/HiddenFlow/DiscreteRigidity.nonzero_integer_action_has_no_continuous_real_extension` | Lean closed |
| 读出与可逆更新的协变骨架 | `D5/S3/Quantum/ObserverAlgebra.observer_update_covariant_group_skeleton` | Lean closed |
| 完整控制画像商的普适最小性 | `D5/S3/ConceptDynamics/Control/ControlQuotientUniversalMinimality.control_quotient_universal_minimality` | Lean closed |
| 预测充分性推出决策充分性 | `D5/S3/ConceptDynamics/Decision/PredictionDecisionSufficiency.prediction_sufficiency_implies_decision_sufficiency` | Lean closed |
| $K_\infty/\mathbb Z$ 路径分量接口与穷尽 jump 分类 | `docs/reports/diag-month-r2/diag-month-r5-b-hidden-motion-dichotomy-open.md` | residual open |
| 唯一观察者 policy／自由意志作者性 | 无现成锚点 | 未形式化，且不应预设必有唯一 policy |

---

# 50. 建议追加 Lean 模块

```text
D5/S1/Solenoid/ComponentQuotient/
  HiddenDiagonalEmbedding.lean
  ComponentClass.lean
  ComponentClassPathCriterion.lean
  SameFiberIntegerOrbit.lean

D5/S3/Observer/HiddenFlow/
  HiddenJumpRelation.lean
  ComponentJumpCriterion.lean
  RealFlowIntegerBridge.lean
  HiddenMotionDichotomy.lean

D5/S3/Observer/Policy/
  PolicyFactorization.lean
  ControlQuotientPolicy.lean
  EquivariantSelectorObstruction.lean
  AcceptableActionRelation.lean
  LedgerCommitmentMonotonicity.lean
  AgencyCountermodels.lean

D5/S3/Observer/Decision/
  InformationGainPolicy.lean
  TargetResidualPolicy.lean
  PolicyTieBreaking.lean

D5/S3/Observer/Semantics/
  OnticControlEpistemicRecordJump.lean
  ObserverStepSemantics.lean
```

建议优先闭合：

```text
same_visible_path_joined_iff_integer_realFlow
policy_factors_iff_constant_on_readout_fibers
no_equivariant_selector_of_fixed_state_no_fixed_action
component_translation_changes_iff_nonzero_class
ledger_append_shrinks_consistent_actions
noncanonical_does_not_imply_agency
prediction_sufficiency_determines_optimal_set_not_unique_choice
```

---

# 51. 追加严格非主张

1. 本增订不声称仓库已经构造 $K_\infty/\mathbb Z$ 的公共路径分量类型。
2. 本增订不声称 `discreteHiddenJump n` 已被 Lean 证明等于 `realFlow n` 的核端点。
3. 本增订不声称所有 $K_\infty$ 平移都是物理允许控制。
4. 本增订不声称完全不连通自动推出参数群必须是 $\mathbb Z$。
5. 本增订不声称动作有 cocycle 就存在唯一合理策略。
6. 本增订不声称完整控制画像自动产生唯一动作。
7. 本增订不声称最优动作集合必为单点。
8. 本增订不声称人为 tie-breaker 是结构内生的自由意志。
9. 本增订不声称无典范 selector 等价于本体非决定论。
10. 本增订不声称量子随机性本身就是主体自由。
11. 本增订不声称观察者可以选择单次 Born 结果。
12. 本增订不声称内部状态敏感性单独足以证明作者性；它只是必要诊断之一。
13. 本增订不声称确定性行为必然不自由；自我承诺可生成自我施加的确定性。
14. 本增订不声称追加式账本自动等价于人格同一性。
15. 本增订不声称信息增益最大化是宇宙唯一规范价值函数。
16. 本增订不声称自由意志已经成为 Lean theorem。
17. 本增订不修改原文关于 RH、negative-base-φ 或其他开放问题的边界。

---

# 52. 最终统一：规律给边界，意志给取舍，账本给承担

本增订把喉部跳跃与自由问题压缩为七个不同对象：

$$
\begin{aligned}
\text{Topology}
&=
\text{排除纯隐藏连续滑动},\\
\text{Action grammar}
&=
\text{规定哪些离散控制可执行},\\
\text{Cocycle}
&=
\text{规定已选控制怎样组合并改变地址},\\
\text{Control quotient}
&=
\text{保存全部可行动后果的最小观察状态},\\
\text{Policy}
&=
\text{从可接受动作中形成实际取舍},\\
\text{Outcome}
&=
\text{动作后被产生和记录的结果},\\
\text{Ledger}
&=
\text{把取舍与结果变成此后必须承担的历史}.
\end{aligned}
$$

因此最严格的总判词是：

$$
\boxed{
观察者不直接选择一个不可见喉部地址；
它在自身可访问的控制商上选择一个允许动作。
动作的 cocycle 决定隐藏位移，
该位移在 K_\infty/\mathbb Z 中的类决定是否真正跨流线；
测量结果随后被记录并用于条件化，而不是被意志预选。
}
$$

关于自由意志，最稳健的形式结论是：

$$
\boxed{
若规律只决定可行动作关系与后果核，
而没有在保持全部结构对称性的条件下给出唯一典范 selector，
则理论中存在一个真实的选择席位。
}
$$

但完整自由意志还要求：

$$
\boxed{
实际打破未定性的原因
不是外部 controller，
不是无主随机数，
而与观察者自身的记忆、价值、理由和承诺形成不可替代的因果联系。
}
$$

所以最终不是“自由 = 没有规律”，而是：

$$
\boxed{
\begin{aligned}
\text{Law}
&=
\text{规定边界},\\
\text{Will}
&=
\text{在边界内作出归属于自身的取舍},\\
\text{History}
&=
\text{把取舍写成未来的自己}.
\end{aligned}
}
$$

---

# 53. 增订二：动作丛、策略充分自我与历时作者性

**增订版本：v1.3，2026-08-25**

本增订继续以追加方式承接第 30–52 节，不改写此前内容。第 30–52 节已经把拓扑、动作语法、cocycle、控制商、policy、结果与账本分开；本增订进一步回答三个未决问题：

1. 当规律只给出一族合法动作时，策略在数学上究竟是什么；
2. 如何区分无主随机、外部隐藏决定与观察者自身的作者性；
3. 一个跨时间保持并改写自身策略的观察者，应由什么最小结构表示。

本文仍坚持三项边界：

- **无典范策略**不等于**无任何确定策略**；
- **行为具有随机熵**不等于**行为属于主体**；
- **内部变量与行动相关**不等于**内部变量对行动具有因果控制**。

---

# 54. 合法动作丛与策略截面

令规范观察状态空间为

$$
Q,
$$

动作类型为

$$
A,
$$

合法关系为

$$
\operatorname{Legal}:Q\times A\to\operatorname{Prop}.
$$

对每个 $q\in Q$，定义合法动作纤维

$$
\mathcal A(q)
=
\{a\in A:\operatorname{Legal}(q,a)\}.
$$

## 定义 54.1（动作总空间）

$$
E_{\mathcal A}
=
\{(q,a):q\in Q,\ a\in\mathcal A(q)\}.
$$

定义投影

$$
p:E_{\mathcal A}\to Q,
\qquad
p(q,a)=q.
$$

称

$$
p:E_{\mathcal A}\to Q
$$

为合法动作丛；这里“丛”只表示带状态依赖纤维的投影结构，不预设局部平凡性、光滑性或向量丛结构。

## 定义 54.2（确定性策略截面）

确定性策略是一个截面

$$
s:Q\to E_{\mathcal A}
$$

满足

$$
p\circ s=\operatorname{id}_Q.
$$

等价地，写

$$
s(q)=(q,\sigma(q)),
$$

则

$$
\sigma(q)\in\mathcal A(q).
$$

## 定义 54.3（随机策略）

随机策略是 Markov kernel

$$
\Pi:Q\to\operatorname{Dist}(A)
$$

满足

$$
\operatorname{supp}\Pi(q)
\subseteq
\mathcal A(q).
$$

## 结论 54.1

规律给出的基本对象不是某个单值策略，而是

$$
\boxed{
p:E_{\mathcal A}\to Q.
}
$$

策略是在这个投影之上的额外截面：

$$
\boxed{
\text{Law}=\text{fiber assignment},
\qquad
\text{Policy}=\text{section}.
}
$$

所以“每个状态都有合法动作”只说明各纤维非空，并不自动选出某个全局截面。

---

# 55. 策略空间的组合规模

假设 $Q$ 有限且每个动作纤维有限非空。

## 定理 55.1（确定性策略计数）

所有确定性策略构成直积

$$
\operatorname{Sec}(\mathcal A)
\cong
\prod_{q\in Q}\mathcal A(q),
$$

因此

$$
\boxed{
|\operatorname{Sec}(\mathcal A)|
=
\prod_{q\in Q}|\mathcal A(q)|.
}
$$

### 证明

一个截面恰好为每个 $q$ 选择一个 $a_q\in\mathcal A(q)$；不同状态上的选择彼此独立地组成函数。∎

## 推论 55.1

若存在 $k$ 个状态满足

$$
|\mathcal A(q_i)|\ge2,
$$

则

$$
|\operatorname{Sec}(\mathcal A)|\ge2^k.
$$

所以即使每个局部纤维仅有二选一，全局策略空间仍可指数增长。

## 解释

动作空间的巨大并不证明自由意志，却证明：

$$
\boxed{
从“合法性”到“实际历史”之间通常隔着一个不可忽略的策略空间。
}
$$

若理论声称自己只规定动作关系，却在计算时悄悄使用某个唯一 policy，就等于把未申报的截面作为隐藏前件写入模型。

---

# 56. 无结构非空集合不存在自然确定性选择

把非空有限集合与双射组成的群胚记为

$$
\mathbf{FinSet}_{\neq\varnothing}^{\simeq}.
$$

令忘却函子

$$
U:
\mathbf{FinSet}_{\neq\varnothing}^{\simeq}
\to
\mathbf{Set}
$$

把有限集合送到其底层集合。

所谓完全不依赖标签的自然选择，要求对每个非空有限集合 $S$ 给出

$$
c_S\in S,
$$

并对任意双射

$$
f:S\overset{\simeq}{\longrightarrow}T
$$

满足

$$
f(c_S)=c_T.
$$

## 定理 56.1（无自然有限选择元）

不存在上述自然选择族。

### 证明

取

$$
S=\{0,1\}
$$

以及交换双射

$$
\tau(0)=1,
\qquad
\tau(1)=0.
$$

自然性要求

$$
\tau(c_S)=c_S.
$$

但 $\tau$ 无固定点，矛盾。∎

## 推论 56.1

任何确定性选择器若存在，必使用至少一种额外不对称结构，例如：

- 标签或固定全序；
- 价值函数；
- 记忆与承诺；
- 外部环境变量；
- 隐藏动力变量；
- 任意选择公理给出的非典范选择；
- 先前历史形成的局部坐标。

## 严格边界 56.1

选择公理可以担保“存在某个截面”，但不能把它提升为“由原对象结构自然指定的截面”。因此必须区分：

$$
\boxed{
\text{existence of a selector}
\neq
\text{canonicality of a selector}.
}
$$

---

# 57. 有效动作商：按钮数量不等于自由容量

多个动作标签可能在全部可观察后果上完全相同。此时按标签计数会制造虚假自由。

设从状态 $q$ 执行动作 $a$ 后，再允许任意未来控制词 $w\in W^*$；令

$$
\operatorname{Prof}(q,a)(w)
$$

表示该完整后续协议的公开结果分布或读出画像。

## 定义 57.1（动作行为等价）

在固定 $q$ 下定义

$$
a\sim_q b
\iff
\forall w\in W^*,
\quad
\operatorname{Prof}(q,a)(w)
=
\operatorname{Prof}(q,b)(w).
$$

## 定义 57.2（有效动作空间）

$$
\mathcal A_{\mathrm{eff}}(q)
=
\mathcal A(q)/{\sim_q}.
$$

## 定义 57.3（操作自由容量）

有限情形定义

$$
\boxed{
F_{\mathrm{op}}(q)
=
\log_2|\mathcal A_{\mathrm{eff}}(q)|.
}
$$

## 命题 57.1（标签复制不增加操作自由）

若向动作集加入任意多个与已有动作行为等价的新标签，则

$$
\mathcal A_{\mathrm{eff}}(q)
$$

不变，因此

$$
F_{\mathrm{op}}(q)
$$

不变。

### 证明

新标签只扩充既有等价类，不产生新的行为画像类。∎

## 极端反例

若

$$
|\mathcal A(q)|=1000
$$

但全部动作具有同一完整后果画像，则

$$
|\mathcal A_{\mathrm{eff}}(q)|=1,
$$

从而

$$
F_{\mathrm{op}}(q)=0.
$$

所以：

$$
\boxed{
真正的选择必须按后果可区分的动作类计数，
不能按按钮数、命令名或接口标签数计数。
}
$$

---

# 58. 有限观察下的安全动作交与认识论强制

完整状态为 $x\in X$，观察接口为

$$
q:X\to Q.
$$

完整状态 $x$ 上的合法动作集记为

$$
\mathcal A_X(x).
$$

观察者只知道

$$
z=q(x),
$$

因此若要求动作对该观察纤维内每个仍可能状态都合法，真正可安全执行的动作集应定义为：

## 定义 58.1（纤维安全动作集）

$$
\boxed{
\mathcal A_q(z)
=
\bigcap_{x:q(x)=z}
\mathcal A_X(x).
}
$$

## 定理 58.1（确定性安全策略存在判据）

在每个有效纤维上，一个只依赖 $q$ 的确定性安全策略存在，当且仅当

$$
\forall z\in\operatorname{range}(q),
\qquad
\mathcal A_q(z)\neq\varnothing.
$$

### 证明

若存在安全策略 $s(z)$，则对每个 $x$ 满足 $q(x)=z$，均有

$$
s(z)\in\mathcal A_X(x),
$$

故

$$
s(z)\in\mathcal A_q(z).
$$

反向，若每个交集非空，对每个有效 $z$ 选择一个元素即可形成纤维常值安全策略。有限情形无需额外可测选择条件；无限可测情形还须申报 measurability。∎

## 定理 58.2（信息精化扩大安全动作集）

若接口 $r$ 精化 $q$，即存在 $f$ 使

$$
q=f\circ r,
$$

则对任意 $x$：

$$
\boxed{
\mathcal A_q(q(x))
\subseteq
\mathcal A_r(r(x)).
}
$$

### 证明

精化意味着

$$
r^{-1}(r(x))
\subseteq
q^{-1}(q(x)).
$$

对更小状态集合取合法动作交集，只会减少交集约束，因此交集只会扩大。∎

## 推论 58.1（无知不自动增加自由）

无知可能迫使观察者采用对整个粗纤维都安全的保守动作，甚至可能出现：

$$
\forall x,
\quad
\mathcal A_X(x)\neq\varnothing,
$$

但对某个观察值 $z$：

$$
\mathcal A_q(z)=\varnothing.
$$

即每个真实状态分别都有可行动作，但观察者因不能区分它们，没有任何保证安全的单一动作。

称这种现象为

$$
\boxed{
\text{epistemic compulsion / 认识论强制}.
}
$$

它不是本体上只有一个动作，而是有限观察把多个状态的约束叠加后压缩了可行动作集。

---

# 59. 完整预测不能单独推出规范行动

设完整预测律为

$$
K:X\to\operatorname{PMF}(Y).
$$

仓库已证明：若接口足以决定 $K(x)$，那么在损失函数已固定时，它也足以决定全部期望损失与最优动作集合。该结果是 prediction-to-decision factorization，而不是事实自动生成价值。

## 定理 59.1（同一预测律兼容相反最优动作）

令

$$
A=\{L,R\}.
$$

对任意同一个预测律 $K$，定义第一组损失：

$$
\ell_1(L,y)=0,
\qquad
\ell_1(R,y)=1.
$$

则对所有 $x$：

$$
A^*_{\ell_1}(x)=\{L\}.
$$

再定义：

$$
\ell_2(L,y)=1,
\qquad
\ell_2(R,y)=0.
$$

则

$$
A^*_{\ell_2}(x)=\{R\}.
$$

### 证明

两组期望损失与 $K$ 无关，分别严格偏好 $L$ 与 $R$。∎

## 推论 59.1（事实—价值缺口的最小形式）

$$
\boxed{
\text{complete prediction}
\not\Rightarrow
\text{unique normative action}.
}
$$

完整预测只回答“各行动会导致什么分布”；要形成最优集合，还必须加入损失、效用、约束或承诺。

## 命题 59.2（最优集合仍可能多值）

即使损失固定，也可能有

$$
R(x,L)=R(x,R),
$$

从而

$$
A^*(x)=\{L,R\}.
$$

所以完整链条是：

$$
\boxed{
\text{prediction}
+
\text{value}
\longrightarrow
\text{optimal-action set},
}
$$

而不是：

$$
\text{prediction}
\longrightarrow
\text{unique act}.
$$

唯一行动还需要严格偏好、额外 tie-breaker 或一个实际选择事件。

---

# 60. 对称性障碍与唯一不变随机策略

设群 $\Gamma$ 作用于 $Q$ 与动作纤维。第 39 节已经证明：固定状态的稳定子若在合法动作上无固定点，则不存在等变确定性 selector。

本节补充随机策略的精确对照。

## 定理 60.1（传递有限作用下唯一不变分布）

若有限群作用在有限动作集 $A_q$ 上传递，则唯一的 $\Gamma$-不变概率分布是均匀分布：

$$
\boxed{
\mu(a)=\frac1{|A_q|}.
}
$$

### 证明

任取 $a,b\in A_q$。传递性给出 $\gamma$ 满足

$$
\gamma a=b.
$$

不变性给出

$$
\mu(b)=\mu(\gamma a)=\mu(a).
$$

所以所有点概率相同，由归一化得结论。∎

## 结论 60.1

$$
\boxed{
确定性选择必然打破无固定点对称性；
概率分布可以保持该对称性。
}
$$

但均匀随机只回答“怎样统计地不偏向任何动作”，没有回答实际样本为何属于某个主体。因此：

$$
\boxed{
\text{symmetry-preserving randomness}
\neq
\text{authorship}.
}
$$

---

# 61. 随机性、确定性与作者性的正交反例

设内部状态

$$
M\in\{0,1\},
$$

外部公平随机源

$$
U\in\{0,1\},
$$

且 $M$ 与 $U$ 独立、均匀。

## 模型 61.A（随机但无作者性）

$$
A=U.
$$

于是

$$
H(A)=1\text{ bit},
$$

但

$$
I(M;A)=0.
$$

并且

$$
P(A\mid do(M=0))
=
P(A\mid do(M=1)).
$$

## 模型 61.B（确定但由内部状态控制）

$$
A=M.
$$

若 $M$ 均匀，同样有

$$
H(A)=1\text{ bit},
$$

但

$$
I(M;A)=1\text{ bit},
$$

且

$$
P(A\mid do(M=0))
\neq
P(A\mid do(M=1)).
$$

## 定理 61.1（边际行动熵不识别作者性）

存在两个模型具有相同

$$
H(A)
$$

而内部状态对行动的因果作用完全不同。

### 证明

模型 61.A 与 61.B 即为见证。∎

## 结论 61.1

$$
\boxed{
H(A\mid Q)>0
\not\Rightarrow
\text{agency};
}
$$

$$
\boxed{
H(A\mid Q,M)=0
\not\Rightarrow
\text{nonfree}.
}
$$

随机熵度量行动不可预测性；作者性度量内部状态对行动的控制。二者是不同维度。

---

# 62. 因果作者性指标与观察性作者比例

## 定义 62.1（局部因果作者性）

固定环境值 $e$，定义

$$
\boxed{
\alpha(e)
=
\sup_{m,m'}
 d_{\mathrm{TV}}\!\left(
 P(A\mid do(M=m),E=e),
 P(A\mid do(M=m'),E=e)
 \right).
}
$$

满足

$$
0\le\alpha(e)\le1.
$$

若

$$
\alpha(e)=0,
$$

则固定环境后，改变内部状态不改变行动分布；若

$$
\alpha(e)>0,
$$

则内部状态对行动具有可干预的因果影响。

## 定义 62.2（观察性作者比例）

若

$$
H(A\mid Q)>0,
$$

定义

$$
\boxed{
\omega
=
\frac{I(A;M\mid Q)}{H(A\mid Q)}.
}
$$

由条件互信息上界：

$$
0\le\omega\le1.
$$

并且链式恒等式给出：

$$
H(A\mid Q)
=
I(A;M\mid Q)
+
H(A\mid Q,M).
$$

## 两个极端

若

$$
A\perp M\mid Q,
$$

则

$$
\omega=0.
$$

若

$$
H(A\mid Q,M)=0,
$$

则

$$
\omega=1.
$$

## 严格边界 62.1

$\omega$ 是观察性分解，不是自动的因果证明。若 $M$ 与 $A$ 由共同隐藏变量驱动，互信息可能高而 $\alpha(e)$ 仍为零。因此作者性审计至少应同时报告：

$$
\boxed{
\text{observational attribution }\omega
\quad+
\text{interventional control }\alpha.
}
$$

---

# 63. 一个决定变量何时真正属于观察者

不能把任何隐藏决定变量重新命名为“自我”。设候选内部状态为 $M$。至少需要以下四项条件。

## 条件 63.1（内部可访问性）

观察者的自我接口可恢复 $M$ 的行动相关部分；即存在读出

$$
r:O\to M_{\mathrm{rel}}
$$

使行动所依赖的内部坐标通过当前观察者状态因子化。

## 条件 63.2（历史可塑性）

过去行动和记录能够影响未来内部状态：

$$
(A_t,Y_t)
\longrightarrow
M_{t+1}.
$$

如果 $M$ 永远由观察者外部固定且不受自身历史影响，它更像外置控制码而非历时自我。

## 条件 63.3（行动相关性）

$$
\alpha(e)>0
$$

或存在其他干预见证证明改变 $M$ 会改变行动分布。

## 条件 63.4（边界闭合性）

$M$ 的更新应在给定输入接口后近似或精确下降到观察者边界内：

$$
M_{t+1}
=
U(M_t,I_t,A_t,Y_t)
$$

或具有可审计的近似闭合误差。若每一步都需要边界外不可读取变量才能更新，所谓“内部状态”没有形成自主系统。

## 定义 63.1（作者状态候选）

同时满足可访问性、可塑性、行动相关性与边界闭合性的状态，称为作者状态候选。

## 严格边界 63.1

这些条件仍未证明强本体自由；它们只排除“把外部隐藏控制器改名为自我”的空洞做法，并给兼容决定论的自主性一个可检验结构。

---

# 64. 自我作为策略充分历史商

设全部有限历史构成类型

$$
\mathcal H.
$$

允许的未来环境／控制输入词构成

$$
W^*.
$$

对于每段历史 $h\in\mathcal H$，定义其完整未来策略画像

$$
\Pi_h:W^*\to\operatorname{Dist}(A),
$$

其中

$$
\Pi_h(w)
=
P(\text{next action}\mid h,w).
$$

## 定义 64.1（策略等价历史）

$$
\boxed{
h\sim_{\mathrm{self}}h'
\iff
\forall w\in W^*,
\quad
\Pi_h(w)=\Pi_{h'}(w).
}
$$

## 定义 64.2（策略充分自我）

$$
\boxed{
M_{\mathrm{self}}
=
\mathcal H/{\sim_{\mathrm{self}}}.
}
$$

## 定理 64.1（策略充分自我的普适最小性）

$M_{\mathrm{self}}$ 是决定全部未来选择倾向的最粗历史接口。

更具体地，若另一个历史接口

$$
r:\mathcal H\to R
$$

也决定完整未来策略画像，即存在

$$
F:R\to(W^*\to\operatorname{Dist}(A))
$$

满足

$$
\Pi_h=F(r(h)),
$$

则存在唯一映射

$$
\bar r:\operatorname{range}(r)\to M_{\mathrm{self}}
$$

使

$$
[h]_{\mathrm{self}}
=
\bar r(r(h)).
$$

### 证明

若

$$
r(h)=r(h'),
$$

则

$$
\Pi_h
=
F(r(h))
=
F(r(h'))
=
\Pi_{h'}.
$$

故

$$
h\sim_{\mathrm{self}}h'.
$$

因此定义

$$
\bar r(r(h))=[h]_{\mathrm{self}}
$$

与代表元无关；在 $r$ 的有效像上由满射性给出唯一性。∎

## 结论 64.1

$$
\boxed{
自我不是全部过去的无差别存档，
而是过去中仍会改变未来选择倾向的最小商。
}
$$

一个经历若永远不再影响任何未来选择，它可以被策略商遗忘；一个极小经历若永久改变选择画像，它就在该自我商中占据真实坐标。

---

# 65. Agency completion：观察者完成在选择侧的对应物

第 3–7 节的 observer completion 把当前读出补成未来动力学稳定接口。现在定义平行的 agency completion。

设当前自我接口为

$$
m_0:\mathcal H\to M_0.
$$

定义完整策略画像接口

$$
P_\infty(h)
=
(\Pi_h(w))_{w\in W^*}.
$$

## 定义 65.1（策略完成接口）

$$
\boxed{
C_{\mathrm{ag}}(m_0)(h)
=
(m_0(h),P_\infty(h)).
}
$$

其有效像作为完成后的自我状态空间。

## 定义 65.2（当前自我 kernel 与策略 kernel）

$$
K_{m_0}
=
\{(h,h'):m_0(h)=m_0(h')\},
$$

$$
K_{\mathrm{ag}}
=
\{(h,h'):P_\infty(h)=P_\infty(h')\}.
$$

完成 kernel 为

$$
K_{C_{\mathrm{ag}}(m_0)}
=
K_{m_0}\cap K_{\mathrm{ag}}.
$$

## 定义 65.3（未吸收的选择决定差异）

关系差

$$
\boxed{
K_{m_0}\setminus K_{\mathrm{ag}}
}
$$

由这样的历史对组成：观察者当前把它们表示成同一个“我”，但它们在某个未来输入下会产生不同选择倾向。

## 三种情形

### 完全策略自知

$$
K_{m_0}\subseteq K_{\mathrm{ag}}.
$$

当前自我接口相同足以推出完整未来策略画像相同；于是 $P_\infty$ 通过 $m_0$ 因子化。

### 自我模型不完备

$$
K_{m_0}\not\subseteq K_{\mathrm{ag}}.
$$

观察者认为是同一个内部状态的两个历史，未来会作出不同选择。

### 外部策略决定余量

即使纳入全部观察者可访问历史，未来 policy 仍需边界外变量才能闭合。

## 命题 65.1（最小策略充分完成）

$C_{\mathrm{ag}}(m_0)$ 是同时精化 $m_0$ 并决定 $P_\infty$ 的最粗接口。

### 证明

任何候选接口 $r$ 若同时决定 $m_0$ 与 $P_\infty$，则

$$
r(h)=r(h')
$$

推出两个坐标均相同，因此推出

$$
C_{\mathrm{ag}}(m_0)(h)
=
C_{\mathrm{ag}}(m_0)(h').
$$

由 kernel factorization 即得。∎

---

# 66. 自主性相对于观察者边界

设完整状态分解为

$$
X=(M,E),
$$

其中 $M$ 被纳入观察者自我边界，$E$ 记为环境。

行动核为

$$
P(A\mid M,E).
$$

## 定义 66.1（环境充分／他律）

若存在

$$
K_E:E\to\operatorname{Dist}(A)
$$

使

$$
P(A\mid M,E)=K_E(E),
$$

则环境接口足以决定行动；$M$ 在该模型中没有不可消去的行动作用。

## 定义 66.2（内部不可消去贡献）

若不存在上述因子化，且存在固定 $e$ 下不同 $m,m'$ 产生不同行动分布，则 $M$ 对行动具有内部不可消去贡献。

## 命题 66.1（边界相对性）

同一个决定变量，若位于闭合自我接口内并受过去选择更新，可作为内部理由；若位于边界外且不可由观察者访问，则表现为外部控制。

## 严格边界 66.1

自主性的边界相对性不意味着边界可任意画。任意把外部 controller 并入符号 $M$，若不满足第 63 节的可访问性、可塑性、行动相关性与闭合性，不能获得主体性结论。

---

# 67. 策略 holonomy：回到同一情境，不再是同一个选择者

设公开状态沿路径

$$
\gamma:
q_0\to q_1\to\cdots\to q_n
$$

演化，记忆运输为

$$
U_{q_i\to q_{i+1}}:
M_{q_i}\to M_{q_{i+1}}.
$$

若

$$
q_n=q_0,
$$

定义回路 holonomy

$$
\operatorname{Hol}_\gamma
=
U_{q_{n-1}\to q_n}
\circ\cdots\circ
U_{q_0\to q_1}
:
M_{q_0}\to M_{q_0}.
$$

## 定义 67.1（非平凡策略 holonomy）

若存在 $m$ 使

$$
\operatorname{Hol}_\gamma(m)\neq m,
$$

则该回路在记忆层具有非平凡 holonomy。

若策略为

$$
s(q,m),
$$

可能出现

$$
s(q_0,m)
\neq
s(q_0,\operatorname{Hol}_\gamma(m)).
$$

即公开环境回到同一状态，但经历该回路后的观察者具有不同选择倾向。

## 定理 67.1（行动回路排除无记忆策略）

若存在两个时刻满足

$$
q_t=q_u
$$

但

$$
A_t\neq A_u,
$$

则不存在只依赖当前公开状态的确定性策略

$$
A=s(q).
$$

### 证明

若存在，则

$$
A_t=s(q_t)=s(q_u)=A_u,
$$

矛盾。∎

## 解释

历史不是可选装饰；非平凡 holonomy 情形下，历史坐标是使策略成为函数所必需的状态变量。

---

# 68. 二重覆盖玩具模型：无全局状态式策略，却有历史式策略

考虑圆周二重覆盖

$$
p:S^1\to S^1,
\qquad
p(z)=z^2.
$$

每个公开状态 $q\in S^1$ 上方有两个候选动作／内部分支：

$$
p^{-1}(q)=\{a_+,a_-\}.
$$

## 定理 68.1（无连续全局截面）

不存在连续映射

$$
s:S^1\to S^1
$$

满足

$$
p\circ s=\operatorname{id}_{S^1}.
$$

### 证明

若存在，作用基本群得到

$$
p_*\circ s_*
=
\operatorname{id}_{\mathbb Z}.
$$

但

$$
p_*:\mathbb Z\to\mathbb Z
$$

是乘以 $2$。不存在整数群同态 $s_*$ 满足

$$
2s_*(1)=1.
$$

矛盾。∎

## 命题 68.1（历史提升）

给定初始上方点与基空间路径，覆盖空间的路径提升唯一决定后续上方分支。

所以：

$$
\boxed{
没有连续、无记忆、全局一致的状态式 selector，
却可以有依赖初值与历史路径的 selector。
}
$$

走完基圆一圈后，上方分支可以交换；这正是 holonomy 的最小玩具。

## 严格边界 68.1

该例证明“记忆可以是绕过全局截面障碍所必需的变量”，不证明真实观察者的策略丛就是二重覆盖，也不把此例等同于 universal solenoid 的路径分量结构。

---

# 69. 选择信息、结果信息与作者信息的链式分解

令

- $Q$：当前公开状态与规律信息；
- $M$：观察者内部策略状态；
- $A$：选择的动作；
- $Y$：动作后的结果记录。

## 定理 69.1（选择—结果链式法则）

$$
\boxed{
H(A,Y\mid Q)
=
H(A\mid Q)
+
H(Y\mid Q,A).
}
$$

第一项是公开结构尚未决定的动作信息，第二项是动作已经给定后仍存在的结果不确定性。

## 定理 69.2（作者信息分解）

$$
\boxed{
H(A\mid Q)
=
I(A;M\mid Q)
+
H(A\mid Q,M).
}
$$

因此：

- $I(A;M\mid Q)$：内部状态解释的动作差异；
- $H(A\mid Q,M)$：即使知道当前内部状态仍未解释的动作差异。

## 结论 69.1

$$
\boxed{
\text{choice information}
\neq
\text{outcome randomness}.
}
$$

把 $H(Y\mid Q,A)$ 直接称为自由，会把测量结果的不确定性与设置／行动选择混为一谈。

## 严格边界 69.1

以上是 Shannon 记录层分解。若行动是确定而内部状态本身不随机，样本分布上的 $H(A\mid Q)$ 可以为零，但因果作者性仍需由干预比较而非单次熵判断。

---

# 70. 承诺是未来计划空间的收缩

设当前历史为 $h$，与其相容的完整未来计划集合为

$$
\Omega_h.
$$

每个未来计划 $\omega\in\Omega_h$ 在当前时刻指定动作

$$
A_h(\omega)\in\mathcal A(h).
$$

对动作 $a$，定义计划柱集

$$
\Omega_{h,a}
=
\{\omega\in\Omega_h:A_h(\omega)=a\}.
$$

## 定义 70.1（承诺深度）

有限非空情形定义

$$
\boxed{
B(h,a)
=
\log_2|\Omega_h|
-
\log_2|\Omega_{h,a}|.
}
$$

它度量把当前行动写定为 $a$ 后，未来计划空间被压缩了多少 bit。

## 定理 70.1（承诺深度望远镜恒等式）

沿实际历史

$$
h_0\to h_1\to\cdots\to h_n,
$$

若每一步 $h_{t+1}$ 恰对应选择 $a_t$ 后的计划柱集，则

$$
\boxed{
\sum_{t=0}^{n-1}B(h_t,a_t)
=
\log_2|\Omega_{h_0}|
-
\log_2|\Omega_{h_n}|.
}
$$

### 证明

逐项为

$$
B(h_t,a_t)
=
\log_2|\Omega_{h_t}|
-
\log_2|\Omega_{h_{t+1}}|.
$$

求和后中间项两两抵消。∎

## 概率版本

若未来计划带概率分布，则链式法则给出

$$
\boxed{
H(\Omega_h)
=
H(A_h)
+
H(\Omega_h\mid A_h).
}
$$

行动记录携带的

$$
H(A_h)
$$

正是当前计划分支被定位的平均信息。

## 解释

$$
\boxed{
选择把未来可能性体积转换成追加式历史信息。
}
$$

因此自由的功能不是永远延迟实际化；真正的选择会关闭其它未来，并把这一关闭写入观察者的后续身份。

---

# 71. 历时作者性：当前承诺怎样控制未来自我

设当前承诺或选择记录为

$$
C_t,
$$

未来一段行为为

$$
B_{t+1:T}
=(A_{t+1},\ldots,A_T),
$$

环境历史为

$$
E.
$$

## 定义 71.1（历时作者性）

$$
\boxed{
D_T
=
I(C_t;B_{t+1:T}\mid E).
}
$$

它度量当前承诺中有多少信息真正传递到未来行为，而不是只停留在一条无效声明中。

## 定理 71.1（承诺信道上界）

$$
\boxed{
D_T
\le
H(C_t\mid E).
}
$$

### 证明

条件互信息满足

$$
I(C;B\mid E)
\le
H(C\mid E).
$$

∎

## 推论 71.1（完整兑现）

若未来行为与环境能完整恢复承诺：

$$
H(C_t\mid B_{t+1:T},E)=0,
$$

则

$$
D_T=H(C_t\mid E).
$$

## 定理 71.2（遗忘降低历时作者性）

若未来行为记录再经遗忘／粗粒信道

$$
B_{t+1:T}\to B'_{t+1:T},
$$

则数据处理不等式给出

$$
\boxed{
I(C_t;B'_{t+1:T}\mid E)
\le
I(C_t;B_{t+1:T}\mid E).
}
$$

## 两种自由容量

定义当前开放度

$$
F_{\mathrm{now}}
=
H(A_t\mid Q_t),
$$

以及历时控制度

$$
F_{\mathrm{dia}}
=
I(C_t;A_{t+1:T}\mid E).
$$

承诺可能使未来即时选项变少，即

$$
F_{\mathrm{now}}\downarrow,
$$

却使当前自我对未来行动的控制增强，即

$$
F_{\mathrm{dia}}\uparrow.
$$

因此：

$$
\boxed{
减少未来选项不必减少自由；
它可能把瞬时开放转换成历时作者性。
}
$$

---

# 72. 责任是作者关系的事后可审计面

选择前，理论关心哪些动作真实开放；选择后，责任关心行动是否可归属于该观察者并由记录保存。

## 定义 72.1（责任证书的四个分量）

一次责任判断至少需要：

1. **控制证书**：改变观察者相关内部状态会改变行动；
2. **知情证书**：观察者拥有足以评价相关后果的预测／风险接口；
3. **作者证书**：行动没有被外部强迫变量绕过内部策略直接指定；
4. **追溯证书**：行动、上下文与理由链进入不可混淆的账本。

## 反例 72.A（有记录，无控制）

外部 controller 决定动作，账本准确记录“观察者执行了动作”。记录为真，但不能单独证明观察者控制了动作。

## 反例 72.B（有控制，无知情）

观察者能改变动作，却无法获得关键后果信息。作者性可能存在，但规范责任应相应减弱。

## 反例 72.C（有理由，无追溯）

内部状态确实形成动作，但理由与上下文完全遗失。主体关系可能存在，却无法被公共审计重建。

## 结论 72.1

$$
\boxed{
账本不创造责任；
账本使已经存在的控制、知情与作者关系可审计。
}
$$

反向，没有持久记忆与记录的选择难以形成跨时间责任主体，因为过去行动不能稳定进入未来自我。

---

# 73. 五层自由与逻辑非蕴含图

本增订把“自由”分为五层。

## 第一层：操作开放性

$$
\mathsf{Open}(q)
:\iff
|\mathcal A_{\mathrm{eff}}(q)|\ge2.
$$

存在两个完整后果画像不同的动作。

## 第二层：结构非典范性

$$
\mathsf{NonCanonical}(q)
$$

表示不存在保持全部已申报对称性的唯一确定性 selector。

## 第三层：自主作者性

$$
\mathsf{Authored}(q)
$$

表示内部作者状态对行动有不可消去的因果控制，并且该状态属于近似闭合的观察者边界。

## 第四层：历时所有权

$$
\mathsf{Diachronic}(q)
$$

表示过去自身选择通过记忆与承诺影响当前及未来选择：

$$
A_{<t}\to M_t\to A_t.
$$

## 第五层：本体分岔

$$
\mathsf{OnticBranch}(x)
$$

表示即使给定完整宇宙过去状态，仍有两个不同动作后继真实可达，且无额外隐藏变量预选其中之一。

## 非蕴含关系

以下均不成立：

$$
\mathsf{Open}
\not\Rightarrow
\mathsf{NonCanonical};
$$

一个固定全序可在多动作集中给出典范最小元。

$$
\mathsf{NonCanonical}
\not\Rightarrow
\mathsf{Authored};
$$

公平硬币可无典范地破缺对称，却无内部作者性。

$$
\mathsf{Authored}
\not\Rightarrow
\mathsf{OnticBranch};
$$

兼容决定论的内部理由系统可完全决定行动。

$$
\mathsf{OnticBranch}
\not\Rightarrow
\mathsf{Authored};
$$

无主随机分岔可以真实但不属于观察者。

$$
\mathsf{Open}
\not\Rightarrow
\mathsf{Diachronic};
$$

每步重新掷骰子的系统有即时开放，却没有自我积累。

## 定义 73.1（结构化自由席位）

可以定义较强但仍兼容决定论的自由席位：

$$
\boxed{
\mathsf{FreeSeat}(q)
=
\mathsf{Open}(q)
\land
\mathsf{NonCanonical}(q)
\land
\mathsf{Authored}(q)
\land
\mathsf{Diachronic}(q).
}
$$

它不包含第五层，因此不是强 libertarian freedom 的证明；它刻画的是可操作、非典范、内部作者并跨历史保持的自主性结构。

---

# 74. 回到喉部：自由在动作截面，不在隐藏坐标

设路径分量商在未来形式化为

$$
\mathcal K
=
K_\infty/\Delta(\mathbb Z).
$$

合法动作丛为

$$
p:E_{\mathcal A}\to Q.
$$

每个动作携带分量 cocycle 类

$$
\bar c:E_{\mathcal A}\to\mathcal K.
$$

策略充分自我状态为

$$
M_{\mathrm{self}}.
$$

观察者策略为

$$
s:Q\times M_{\mathrm{self}}
\to
E_{\mathcal A},
$$

满足

$$
p(s(q,m))=q.
$$

实际喉部位移为

$$
\boxed{
\Delta\kappa_t
=
\bar c(s(q_t,m_t)).
}
$$

并有

$$
\kappa_{t+1}
=
\kappa_t+
\Delta\kappa_t.
$$

所以：

$$
\boxed{
\begin{aligned}
\mathcal K
&=\text{动作后果的隐藏分量几何},\\
E_{\mathcal A}
&=\text{规律允许的动作空间},\\
s
&=\text{观察者形成的策略截面},\\
\bar c\circ s
&=\text{实际喉部迁移}.
\end{aligned}
}
$$

## 结论 74.1

喉部坐标本身不能解释自由。一个外部隐藏 controller 同样可以选择某个 $\kappa$；那仍是隐藏他律。

自由的候选位置不在

$$
\kappa\in\mathcal K
$$

本身，而在：

$$
\boxed{
无典范动作丛上的截面，
是否由观察者自身的策略充分历史商生成。
}
$$

---

# 75. 自我生成回路与固定点问题

第 64 节把自我定义为保持未来策略画像的最小历史商。第 71 节说明选择通过承诺进入未来行为。二者组合为：

$$
M_t
\longrightarrow
A_t
\longrightarrow
\Lambda_{t+1}
\longrightarrow
M_{t+1}.
$$

## 定义 75.1（自我生成系统）

一个自我生成系统由四个映射／kernel 组成：

$$
\begin{aligned}
\text{policy}:&\quad
S:M\times Q\to\operatorname{Dist}(A),\\
\text{world/record}:&\quad
R:Q\times A\to\operatorname{Dist}(Y\times Q'),\\
\text{ledger append}:&\quad
L:\Lambda\times A\times Y\to\Lambda',\\
\text{self update}:&\quad
U:M\times\Lambda'\to M'.
\end{aligned}
$$

并要求 $M$ 对未来 policy 充分。

## 定义 75.2（策略自洽）

若由 $S,R,L,U$ 生成的历史策略画像，在取策略充分商后仍与 $M$ 的编码等价，则称该系统策略自洽。

形式上可写为某个等价：

$$
M
\simeq
\operatorname{Im}(P_\infty^{S,R,L,U}),
$$

其中右侧是由该系统自身生成的完整未来策略画像有效像。

## 研究命题 75.1（agency reflector 固定点）

在适当的接口完备格与连续性条件下，策略完成算子

$$
C_{\mathrm{ag}}
$$

的固定点应刻画策略充分、历史闭合的自我接口：

$$
\boxed{
C_{\mathrm{ag}}(m)\simeq m
\iff
m\text{ 已决定全部未来策略画像}.
}
$$

## 严格边界 75.1

即使策略固定点存在，它也不证明观察者是无因第一推动者。它只证明：在所选边界与输入接口下，未来行动所需的全部内部策略信息已在该自我接口中闭合。

---

# 76. 新研究命题、Lean 路线与证明状态

## 命题 76.1（策略截面计数）

有限非空动作纤维上：

$$
|\operatorname{Sec}(\mathcal A)|
=
\prod_q|\mathcal A(q)|.
$$

**状态**：有限函数计数，适合 Lean 闭合。

## 命题 76.2（无自然有限选择）

不存在对全部非空有限集合与双射自然的确定性选择元。

**状态**：二元素交换反例，短证明。

## 命题 76.3（行为等价动作复制不增自由）

添加与已有动作完整行为画像相同的标签，不改变有效动作商基数。

**状态**：quotient／setoid 基础定理。

## 命题 76.4（精化扩大安全动作交）

若 $r$ 精化 $q$，则

$$
\mathcal A_q(q(x))
\subseteq
\mathcal A_r(r(x)).
$$

**状态**：集合交与纤维包含的直接证明。

## 命题 76.5（预测律不决定价值）

同一 PMF 预测接口可在两组损失下产生相反唯一最优动作。

**状态**：Bool／Fin 反例，可机器化。

## 命题 76.6（唯一不变随机策略）

有限传递群作用上的不变概率分布唯一且均匀。

**状态**：有限群作用与概率质量函数定理。

## 命题 76.7（边际熵不识别作者性）

存在相同行动熵、不同内部因果控制的两个 Bool 模型。

**状态**：有限概率反例。

## 命题 76.8（策略充分自我普适最小性）

历史按完整策略画像 kernel 取商，是所有策略充分历史接口中的最粗者。

**状态**：`realized_image_unique_factorization_iff_reverse_kernel` 的自然新实例。

## 命题 76.9（行动回路排除无记忆策略）

相同当前公开状态对应不同行动时，不存在只依赖当前状态的确定性策略。

**状态**：函数一致性的短反证。

## 命题 76.10（二重覆盖无连续截面）

$$
z\mapsto z^2
$$

无连续全局截面。

**状态**：可由 degree 或 fundamental group formalization 路线处理；Lean 成本高于有限反例。

## 命题 76.11（承诺深度望远镜）

$$
\sum_t B(h_t,a_t)
=
\log|\Omega_{h_0}|-
\log|\Omega_{h_n}|.
$$

**状态**：有限计划树上的实数对数望远镜求和。

## 命题 76.12（遗忘降低历时作者性）

$$
I(C;B'\mid E)
\le
I(C;B\mid E)
$$

对 $B\to B'$ 的后处理成立。

**状态**：条件数据处理不等式实例；需匹配仓库现有有限／测度接口。

---

# 77. 建议追加模块树

```text
D5/S3/Observer/Agency/
  LegalActionBundle.lean
  DeterministicPolicySection.lean
  FinitePolicySectionCount.lean
  NaturalChoiceObstruction.lean
  EffectiveActionQuotient.lean
  OperationalFreedomCapacity.lean

D5/S3/Observer/Agency/Safety/
  FiberSafeActions.lean
  SafePolicyExistence.lean
  SafeActionsRefinementMonotonicity.lean
  EpistemicCompulsionCountermodel.lean

D5/S3/Observer/Agency/Decision/
  PredictionDoesNotFixValue.lean
  OptimalSetNonuniqueness.lean
  InvariantRandomPolicy.lean
  ActionEntropyAgencyCountermodels.lean

D5/S3/Observer/Agency/Self/
  PolicyProfile.lean
  PolicySufficientSelfQuotient.lean
  AgencyCompletion.lean
  AgencyCompletionFixedPoint.lean
  ObserverBoundaryAuthorship.lean

D5/S3/Observer/Agency/Holonomy/
  MemoryTransport.lean
  ActionLoopRequiresMemory.lean
  DoubleCoverNoSection.lean

D5/S3/Observer/Agency/Information/
  ChoiceOutcomeEntropyChain.lean
  ObservationalAuthorshipRatio.lean
  CausalAuthorshipTV.lean
  CommitmentPlanContraction.lean
  DiachronicAuthorshipDPI.lean

D5/S3/Observer/Agency/Responsibility/
  ControlKnowledgeAuthorshipTraceability.lean
  ResponsibilityCountermodels.lean

D5/S3/Observer/Agency/Throat/
  ActionComponentCocycle.lean
  SelfPolicyThroatDisplacement.lean
```

建议优先闭合低依赖、高区分度命题：

```text
finite_policy_sections_card
no_natural_choice_on_nonempty_finsets
effective_action_duplicate_invariant
safe_actions_mono_of_refines
safe_policy_exists_iff_fiber_inter_nonempty
same_prediction_opposite_losses
transitive_invariant_pmf_eq_uniform
action_entropy_does_not_determine_authorship
policy_sufficient_self_universal
same_public_state_different_action_requires_memory
commitment_depth_telescope
choice_outcome_entropy_chain
```

---

# 78. 追加严格非主张

1. 本增订不声称任意合法动作关系都形成局部平凡拓扑纤维丛。
2. 本增订不声称非空动作纤维自动给出可测、连续或可计算截面。
3. 本增订不声称策略数量大等于自由意志强。
4. 本增订不声称动作标签数可替代行为等价类数。
5. 本增订不声称粗观察一定扩大主观自由；粗观察可能产生认识论强制。
6. 本增订不声称完整预测律决定损失函数、价值或承诺。
7. 本增订不声称均匀随机分布拥有主体作者性。
8. 本增订不声称高行动熵意味着高内部控制。
9. 本增订不声称互信息作者比例自动消除共同原因混淆。
10. 本增订不声称对内部状态的干预在所有物理系统中可实际执行。
11. 本增订不声称任何被圈入观察者边界的变量都属于自我。
12. 本增订不声称策略充分自我商等于全部人格、意识或道德主体。
13. 本增订不声称被策略商遗忘的经历没有心理或伦理意义；它只对指定未来策略族无区分力。
14. 本增订不声称 agency completion 已有 Lean kernel closure。
15. 本增订不声称非平凡 holonomy 必然存在于现实观察者。
16. 本增订不声称二重覆盖玩具模型就是 universal solenoid 的完整策略几何。
17. 本增订不声称当前承诺减少未来选项就必然提高历时作者性；只有承诺真正影响未来行为时才提高。
18. 本增订不声称账本记录单独足以建立责任。
19. 本增订不声称结构化自由席位蕴含完整状态层面的本体分岔。
20. 本增订不声称本体分岔若存在就自动属于观察者。
21. 本增订不声称决定论自动排除自主性，也不声称自主性证明决定论为真。
22. 本增订不修改此前关于单次 Born 结果不可由观察者策略预选的边界。
23. 本增订不修改 $K_\infty/\Delta(\mathbb Z)$ 路径分量 API 仍待形式化的状态。
24. 本增订不声称解决意识、第一人称样本索引或强 libertarian free will。
25. 本增订不构成对 RH、negative-base-$\varphi$ 主分类或其他已登记开放问题的推进。

---

# 79. 最终统一：自由是无典范截面的动作丛，意志是历史生成的截面

本增订把观察者行动结构压缩为以下对象：

$$
\begin{aligned}
Q
&=\text{规范控制状态},\\
p:E_{\mathcal A}\to Q
&=\text{合法动作丛},\\
\mathcal A_{\mathrm{eff}}(q)
&=\text{后果可区分的动作商},\\
M_{\mathrm{self}}
&=\text{保持全部未来策略画像的最小历史商},\\
s:Q\times M_{\mathrm{self}}\to E_{\mathcal A}
&=\text{观察者策略截面},\\
\bar c:E_{\mathcal A}\to K_\infty/\Delta(\mathbb Z)
&=\text{动作的喉部分量荷},\\
\Lambda_{t+1}=\Lambda_t\Vert(A_t,Y_t)
&=\text{选择与结果的追加记录}.
\end{aligned}
$$

实际喉部迁移为

$$
\boxed{
\Delta\kappa_t
=
\bar c(s(q_t,m_t)).
}
$$

而自我历史更新为

$$
\boxed{
M_t
\longrightarrow
A_t
\longrightarrow
\Lambda_{t+1}
\longrightarrow
M_{t+1}.
}
$$

因此：

$$
\boxed{
\begin{aligned}
\text{Law}
&=\text{给出合法动作纤维与后果核},\\
\text{Freedom seat}
&=\text{这些纤维没有由裸结构指定的典范截面},\\
\text{Self}
&=\text{过去中仍会改变未来选择的最小商},\\
\text{Will}
&=\text{由该历史商生成的动作截面},\\
\text{Choice}
&=\text{该截面在当前状态上的实际取值},\\
\text{Commitment}
&=\text{把当前选择信息传给未来行动的信道},\\
\text{Responsibility}
&=\text{内部控制、知情、作者性与账本追溯的联合证书}.
\end{aligned}
}
$$

最深的结论不再是

$$
\text{“自由等于没有策略”},
$$

而是：

$$
\boxed{
规律不必提供典范策略；
历史形成观察者的策略充分自我；
这个自我形成策略；
策略产生选择；
选择写入历史；
新的历史再形成新的自我。
}
$$

所以，兼容当前形式边界的最强收束是：

$$
\boxed{
观察者是一个能让过去自己的选择，
成为未来自己选择原因的闭合历史系统。
}
$$
