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

---

# 80. 增订三：有限维量子观察者的操作商、仪器语义与经典记录

**增订版本：v1.4，2026-08-26**

本增订继续以纯追加方式承接第 0–79 节，不改写、删减或重排此前内容。前文已经建立一般接口反射、状态—效应反对偶、可观测 Gram 几何、动作丛、策略充分自我与历时作者性；本增订把这些结构严格落到有限维量子力学中，回答以下问题：

1. 量子观察者究竟是什么数学对象；
2. 观察者真正获得的是状态本身、一次结果，还是一族概率签名；
3. 静态 POVM、测量 instrument、环境记录与顺序实验为什么必须分层；
4. 信息完备、有限时间完备、稳健完备与物理可实现完备之间是什么关系；
5. 退相干如何产生稳定经典记录，而不额外引入“意识导致坍缩”公理；
6. 局部观察、自我观察、经典答案表与对角逃逸分别有哪些严格边界；
7. 如何把量子层析、prime-time observation、最小预算与 observer completion 统一为同一个可见空间／不可见残差理论。

本增订沿用四级真值纪律：

- **定义**：引入保守记号；
- **本文定理**：给出完整 paper-level 证明，但尚无同名 Lean theorem；
- **Lean 锚点**：仓库中已有机器核验结果；
- **研究命题／形式化路线**：依赖尚未建立的统一 carrier、CP instrument、partial trace 或无限维分析接口。

本增订的基础不是“观察行为自动推出量子力学”，而是标准有限维复量子结构。严格地说：

$$
\boxed{
\text{observer existence}
\not\Rightarrow
\text{complex Hilbert-space quantum mechanics}.
}
$$

要从一般操作理论重建复量子力学，还需要关于凸性、系统复合、连续可逆变换、局域层析或等价结构的额外公理。本文只在这些底层结构既定后研究观察者可见性、记录、条件化与完成。

---

# 81. 状态—效应配对是量子观察的基础接口

固定有限维复 Hilbert 空间

$$
\mathcal H\cong\mathbb C^d,
\qquad
d\ge 1.
$$

记 Hermitian 实向量空间为

$$
\operatorname{Herm}_d
=
\{A\in M_d(\mathbb C):A^\dagger=A\},
$$

迹零子空间为

$$
\operatorname{Herm}_d^0
=
\{A\in\operatorname{Herm}_d:\operatorname{Tr}A=0\}.
$$

它们满足

$$
\dim_{\mathbb R}\operatorname{Herm}_d=d^2,
$$

$$
\dim_{\mathbb R}\operatorname{Herm}_d^0=d^2-1.
$$

在 Hermitian 空间上使用 Hilbert–Schmidt 配对

$$
\langle A,B\rangle_{\mathrm{HS}}
=
\operatorname{Tr}(AB).
$$

## 定义 81.1（量子态）

$$
\mathsf S_d
=
\{\rho\in\operatorname{Herm}_d:
\rho\ge0,\ \operatorname{Tr}\rho=1\}.
$$

纯态是

$$
\rho_\psi
=
|\psi\rangle\langle\psi|,
\qquad
\langle\psi|\psi\rangle=1.
$$

## 定义 81.2（效果）

$$
\mathsf{Eff}_d
=
\{E\in\operatorname{Herm}_d:0\le E\le I\}.
$$

效果 $E$ 表示一个二值问题的“是”分支。

## 定义 81.3（有限测量上下文）

对设置 $x$，一个有限结果 POVM 是效果族

$$
\mathcal E^x
=
\{E_{a|x}\}_{a\in A_x}
$$

满足

$$
E_{a|x}\ge0,
\qquad
\sum_{a\in A_x}E_{a|x}=I.
$$

## 原理 81.1（Born 配对）

$$
\boxed{
p(a\mid x,\rho)
=
\operatorname{Tr}(\rho E_{a|x}).
}
$$

这一定义同时保证：

$$
p(a\mid x,\rho)\ge0,
$$

$$
\sum_a p(a\mid x,\rho)=1,
$$

以及对状态和效果的仿射性。

仓库 `D5/S3/Quantum/FiniteDimensional.lean` 已经机器核验正半定、迹一矩阵对投影给出归一、可加、非负的 Born 权重；`D5/S3/Observer/BornReduction.lean` 进一步证明，当

$$
\rho=|\psi\rangle\langle\psi|,
\qquad
E=|\phi\rangle\langle\phi|
$$

时，

$$
\boxed{
\operatorname{Tr}(\rho E)
=
|\langle\phi|\psi\rangle|^2.
}
$$

因此“模平方”不是另一套独立规则，而是迹配对在纯态—秩一效果上的化简。

---

# 82. 静态量子观察者与概率签名

## 定义 82.1（静态量子观察者）

一个静态量子观察者定义为

$$
\mathfrak O_{\mathrm{stat}}
=
\left(
X,\{A_x\}_{x\in X},
\{E_{a|x}\}_{x,a}
\right),
$$

其中每个 $x$ 给出一个 POVM。

## 定义 82.2（观察签名）

$$
\boxed{
\Sigma_{\mathfrak O}(\rho)
=
\left(
\operatorname{Tr}(\rho E_{a|x})
\right)_{x,a}.
}
$$

观察者一次实验得到的是某个随机结果；只有对同一制备进行足够多次重复，才能估计上述概率签名。因此必须区分：

$$
\text{single outcome},
$$

$$
\text{empirical frequency},
$$

$$
\text{ideal probability signature}.
$$

层析理论讨论的是第三者与其有限样本估计，而不是“一次测量直接读出完整波函数”。

## 定义 82.3（观察等价）

$$
\boxed{
\rho\sim_{\mathfrak O}\sigma
\iff
\Sigma_{\mathfrak O}(\rho)
=
\Sigma_{\mathfrak O}(\sigma).
}
$$

等价地：

$$
\rho\sim_{\mathfrak O}\sigma
\iff
\forall x,a,\quad
\operatorname{Tr}\bigl((\rho-\sigma)E_{a|x}\bigr)=0.
$$

## 定义 82.4（操作现实）

$$
\boxed{
\mathsf R_{\mathfrak O}
=
\mathsf S_d/\!\sim_{\mathfrak O}.
}
$$

这里的商不是说完整状态“不存在”，而是说观察者的全部申报实验不能区分同一纤维中的状态。观察者现实是状态空间对其可执行实验协议的操作商。

---

# 83. 可见空间与不可见残差

## 定义 83.1（可见实算子空间）

$$
\boxed{
V_{\mathfrak O}
=
\operatorname{span}_{\mathbb R}
\left(
\{I\}\cup
\{E_{a|x}\}_{x,a}
\right)
\subseteq
\operatorname{Herm}_d.
}
$$

其复化

$$
\mathcal V_{\mathfrak O}
=
V_{\mathfrak O}+iV_{\mathfrak O}
$$

是一个含单位、对伴随封闭的 operator system。

必须严格区分：

$$
V_{\mathfrak O}
$$

与这些效果生成的乘法代数

$$
C^*(E_{a|x}).
$$

前者决定静态线性统计；后者包含效果乘积及其非交换组合。代数生成完整并不自动表示当前 POVM 概率信息完备。

例如量子比特只读 $X$ 与 $Z$ 时，

$$
V_{\mathfrak O}
=
\operatorname{span}_{\mathbb R}\{I,X,Z\}
$$

仍看不见 $Y$ 方向；但 $X,Z$ 作为代数生成元已经生成

$$
M_2(\mathbb C).
$$

## 定义 83.2（不可见残差）

$$
\boxed{
N_{\mathfrak O}
=
V_{\mathfrak O}^{\perp}
=
\{D\in\operatorname{Herm}_d:
\operatorname{Tr}(DA)=0,\ \forall A\in V_{\mathfrak O}\}.
}
$$

由于

$$
I\in V_{\mathfrak O},
$$

任意

$$
D\in N_{\mathfrak O}
$$

自动满足

$$
\operatorname{Tr}D=0.
$$

因此

$$
N_{\mathfrak O}
\subseteq
\operatorname{Herm}_d^0.
$$

## 定理 83.1（观察等价的残差刻画）

$$
\boxed{
\rho\sim_{\mathfrak O}\sigma
\iff
\rho-\sigma\in N_{\mathfrak O}.
}
$$

### 证明

若签名相同，则 $\rho-\sigma$ 与每个效果正交；两态同为迹一，所以它也与 $I$ 正交，因此与 $V_{\mathfrak O}$ 的全部线性组合正交。

反向若差属于 $N_{\mathfrak O}$，它与全部效果正交，故所有 Born 概率相同。∎

## 结论 83.1

量子观察者的静态结构完全由一对反对偶对象刻画：

$$
\boxed{
V_{\mathfrak O}
=
\text{可见 effect 方向},
}
$$

$$
\boxed{
N_{\mathfrak O}
=
\text{不可见 state-difference 方向}.
}
$$

并有

$$
N_{\mathfrak O}
=
V_{\mathfrak O}^{\perp}.
$$

---

# 84. 观察商的仿射表示

定义限制映射

$$
r_{\mathfrak O}:
\mathsf S_d\to V_{\mathfrak O}^*
$$

为

$$
r_{\mathfrak O}(\rho)(A)
=
\operatorname{Tr}(\rho A).
$$

## 定理 84.1（操作商表示）

$$
\boxed{
\mathsf S_d/\!\sim_{\mathfrak O}
\cong_{\mathrm{aff}}
r_{\mathfrak O}(\mathsf S_d).
}
$$

### 证明

由定理 83.1，

$$
r_{\mathfrak O}(\rho)=r_{\mathfrak O}(\sigma)
$$

当且仅当

$$
\rho\sim_{\mathfrak O}\sigma.
$$

故 $r_{\mathfrak O}$ 恰以观察等价类为纤维，在商上诱导双射。迹配对对 $\rho$ 仿射，因此诱导双射保持凸组合。∎

## 推论 84.1

观察者所见状态空间仍是紧凸集，但一般维数下降：

$$
\dim_{\mathrm{aff}}
\mathsf R_{\mathfrak O}
\le
\dim V_{\mathfrak O}-1.
$$

只有当观察者完备时，该商保留全部

$$
d^2-1
$$

个迹一 Hermitian 自由度。

---

# 85. 信息完备性的等价定理与显式反例证书

## 定义 85.1（信息完备观察者）

$$
\mathfrak O
\text{ 信息完备}
$$

当且仅当

$$
\rho\sim_{\mathfrak O}\sigma
\Longrightarrow
\rho=\sigma.
$$

## 定理 85.1（完备性四重等价）

以下条件等价：

$$
\text{(i)}
\quad
\mathfrak O\text{ 信息完备};
$$

$$
\text{(ii)}
\quad
N_{\mathfrak O}=\{0\};
$$

$$
\text{(iii)}
\quad
V_{\mathfrak O}=\operatorname{Herm}_d;
$$

$$
\text{(iv)}
\quad
\operatorname{span}_{\mathbb R}
\left\{
E_{a|x}
-
\frac{\operatorname{Tr}E_{a|x}}{d}I
\right\}
=
\operatorname{Herm}_d^0.
$$

### 证明

有限维非退化内积给出

$$
V^\perp=\{0\}
\iff
V=\operatorname{Herm}_d.
$$

而

$$
\operatorname{Herm}_d
=
\mathbb RI
\oplus
\operatorname{Herm}_d^0,
$$

故 (iii) 与 (iv) 等价。

由定理 83.1，(ii) 立即推出 (i)。

反之，若存在非零

$$
D\in N_{\mathfrak O},
$$

则

$$
\operatorname{Tr}D=0.
$$

取

$$
0<\varepsilon<
\frac{1}{d\|D\|_\infty}
$$

并定义

$$
\rho_\pm
=
\frac{I}{d}
\pm
\varepsilon D.
$$

其最小本征值满足

$$
\lambda_{\min}(\rho_\pm)
\ge
\frac1d-\varepsilon\|D\|_\infty
>0,
$$

所以

$$
\rho_\pm\in\mathsf S_d.
$$

但

$$
\rho_+-\rho_-
=
2\varepsilon D\in N_{\mathfrak O},
$$

故

$$
\rho_+\sim_{\mathfrak O}\rho_-,
$$

而

$$
\rho_+\neq\rho_-.
$$

这与信息完备矛盾。∎

## 推论 85.1（不完备预算的物理证书）

证明某观察预算不完备，不应只报告 rank deficiency；可以给出一个明确的

$$
0\neq D\in N_{\mathfrak O}
$$

以及两个物理状态

$$
\boxed{
\rho_\pm=\frac Id\pm\varepsilon D
}
$$

作为不可区分证书。

该证书同时满足：

1. 两态均正半定；
2. 两态均迹一；
3. 两态不同；
4. 当前全部读出概率完全相同。

这把线性 residual 转化成可审计的物理反例。

---

# 86. 有限效果压缩与结果预算下界

## 定理 86.1（有限完备效果证书）

设可能的效果族

$$
\mathcal E\subseteq\mathsf{Eff}_d
$$

可以是无限集。若它们联合起来信息完备，则存在有限子集

$$
E_1,\ldots,E_m\in\mathcal E
$$

满足

$$
m\le d^2-1,
$$

且这些效果已经能分离所有迹一量子态。

### 证明

对每个 $E\in\mathcal E$ 定义中心化效果

$$
\widetilde E
=
E-
\frac{\operatorname{Tr}E}{d}I.
$$

信息完备等价于这些中心化效果张成

$$
\operatorname{Herm}_d^0.
$$

该空间维数为

$$
d^2-1.
$$

从任意生成集中选出一个基，至多需要 $d^2-1$ 个元素。∎

## 重要解释

状态集合

$$
\mathsf S_d
$$

是连续无穷的，但它嵌入有限维仿射空间。因此：

$$
\boxed{
\text{连续无穷状态集}
+
\text{有限算子维数}
\Longrightarrow
\text{有限完备观察证书}.
}
$$

这比“有限状态空间存在有限分离窗口”更强。

## 推论 86.1（单 POVM 结果数下界）

若一个 POVM 有 $m$ 个结果，则

$$
\sum_{a=1}^m E_a=I.
$$

中心化后：

$$
\sum_{a=1}^m\widetilde E_a=0,
$$

所以其中心化效果最多张成 $m-1$ 维空间。若该 POVM 信息完备，则

$$
m-1\ge d^2-1,
$$

即

$$
\boxed{
m\ge d^2.
}
$$

## 推论 86.2（多上下文预算下界）

若第 $x$ 个上下文有 $m_x$ 个结果，则信息完备必须满足

$$
\boxed{
\sum_x(m_x-1)\ge d^2-1.
}
$$

仓库 `CompleteContextTomography` 使用 $d+1$ 个互补秩一上下文，每个有 $d$ 个结果，其独立参数数恰为

$$
(d+1)(d-1)=d^2-1.
$$

该形式化证明了互补重叠律推出投影差与单位矩阵张成完整矩阵空间，并由全部上下文概率唯一恢复 Hermitian 迹一矩阵。

---

# 87. 模型相对完备性

实际实验常有先验模型：

$$
\mathcal M\subseteq\mathsf S_d,
$$

例如纯态、低秩态、某对称态族或参数化热态族。

## 定义 87.1（模型相对完备）

观察者在 $\mathcal M$ 上完备，当且仅当

$$
\rho,\sigma\in\mathcal M,
\quad
\rho\sim_{\mathfrak O}\sigma
\Longrightarrow
\rho=\sigma.
$$

## 定理 87.1（差集判据）

$$
\boxed{
\mathfrak O
\text{ 在 }\mathcal M\text{ 上完备}
\iff
N_{\mathfrak O}
\cap
(\mathcal M-\mathcal M)
=
\{0\}.
}
$$

其中

$$
\mathcal M-\mathcal M
=
\{\rho-\sigma:\rho,\sigma\in\mathcal M\}.
$$

### 证明

模型上不完备恰好意味着存在不同

$$
\rho,\sigma\in\mathcal M
$$

且

$$
\rho-\sigma\in N_{\mathfrak O}.
$$

这等价于上述交集中存在非零元素。∎

## 结论 87.1

“观察者不完备”必须说明相对哪个状态模型。某个测量族可能无法恢复任意密度矩阵，却能唯一恢复一个低维先验族。

---

# 88. 观察者精化、联合与容量守恒

## 定义 88.1（观察者精化）

定义

$$
\mathfrak O_1\preceq\mathfrak O_2
$$

当且仅当 $\mathfrak O_2$ 至少与 $\mathfrak O_1$ 一样能区分状态：

$$
\rho\sim_{\mathfrak O_2}\sigma
\Longrightarrow
\rho\sim_{\mathfrak O_1}\sigma.
$$

## 定理 88.1（精化的三重等价）

$$
\boxed{
\mathfrak O_1\preceq\mathfrak O_2
\iff
N_{\mathfrak O_2}\subseteq N_{\mathfrak O_1}
\iff
V_{\mathfrak O_1}\subseteq V_{\mathfrak O_2}.
}
$$

### 证明

第一项与第二项由定理 83.1 得到；第二项与第三项由正交补反序性得到。∎

## 定理 88.2（联合观察者）

令

$$
\mathfrak O_1\vee\mathfrak O_2
$$

包含两者全部效果。则

$$
V_{\mathfrak O_1\vee\mathfrak O_2}
=
V_{\mathfrak O_1}+V_{\mathfrak O_2},
$$

$$
\boxed{
N_{\mathfrak O_1\vee\mathfrak O_2}
=
N_{\mathfrak O_1}\cap N_{\mathfrak O_2}.
}
$$

因此观察者合作的本体不是“平均各自观点”，而是合并可见 effect 空间；不可见残差则取交。

## 定义 88.2（观察容量与残差）

$$
C(\mathfrak O)
=
\dim V_{\mathfrak O}-1,
$$

$$
R(\mathfrak O)
=
\dim N_{\mathfrak O}.
$$

## 定理 88.3（有限维容量守恒）

$$
\boxed{
C(\mathfrak O)+R(\mathfrak O)=d^2-1.
}
$$

信息精化使

$$
C(\mathfrak O)\uparrow,
$$

同时使

$$
R(\mathfrak O)\downarrow.
$$

这给出量子观察者 completion 的离散进度量。

---

# 89. 通道、Heisenberg 拉回与时间观察

设系统在测量之间通过量子通道

$$
\Phi:M_d(\mathbb C)\to M_d(\mathbb C)
$$

演化。这里 $\Phi$ 为完全正、迹保持线性映射。

定义 Heisenberg 对偶

$$
\Phi^*
$$

满足

$$
\operatorname{Tr}(\Phi(\rho)A)
=
\operatorname{Tr}(\rho\Phi^*(A)).
$$

迹保持等价于

$$
\Phi^*(I)=I.
$$

## 定理 89.1（观察者拉回）

在通道之后测量效果 $E$，等价于在初态上测量

$$
\Phi^*(E).
$$

具体地：

$$
\boxed{
\operatorname{Tr}(\Phi^t(\rho)E)
=
\operatorname{Tr}\bigl(\rho(\Phi^*)^t(E)\bigr).
}
$$

## 定义 89.1（有限时间可见空间）

给定基础效果族 $\{E_r\}_{r=1}^m$，定义

$$
V_n
=
\operatorname{span}_{\mathbb R}
\left\{
I,
(\Phi^*)^t(E_r):
0\le t<n,\ 1\le r\le m
\right\}.
$$

定义

$$
N_n=V_n^\perp.
$$

## 定理 89.2（时间单调性）

$$
V_n\subseteq V_{n+1},
$$

因此

$$
\boxed{
N_{n+1}\subseteq N_n.
}
$$

观察更久只能消除不可区分方向，不能制造新的不可区分方向。

这一结论是仓库 `BiaxialMonotoneRefinement` 在量子状态—效果配对上的线性实例。

## 严格实验边界 89.1

必须区分：

1. 每个时间点重新制备相同初态，再演化 $t$ 步并测量；
2. 对同一个样本连续测量。

第一种由 $(\Phi^*)^t(E)$ 描述；第二种必须使用 instrument 词，因为早期测量会改变后续状态。

---

# 90. 量子可观测矩阵、Gramian 与有限时间压缩

取

$$
D=d^2-1
$$

并选择 $\operatorname{Herm}_d^0$ 的 Hilbert–Schmidt 正交基

$$
F_1,\ldots,F_D.
$$

任意状态差写成

$$
X=\sum_{\mu=1}^D x_\mu F_\mu.
$$

由于 $\Phi$ 保迹，迹零空间对 $\Phi$ 不变。令其在该基上的实矩阵表示为

$$
A\in M_D(\mathbb R).
$$

定义测量矩阵

$$
C_{r\mu}
=
\operatorname{Tr}(E_rF_\mu).
$$

则时间 $t$ 的概率差向量为

$$
CA^t x.
$$

## 定义 90.1（有限时间可观测矩阵）

$$
\mathscr O_n
=
\begin{bmatrix}
C\\
CA\\
CA^2\\
\vdots\\
CA^{n-1}
\end{bmatrix}.
$$

## 定义 90.2（有限时间 Gramian）

$$
W_n
=
\sum_{t=0}^{n-1}
(A^t)^\top C^\top C A^t.
$$

## 定理 90.1（秩—Gram—残差等价）

以下等价：

$$
N_n=\{0\},
$$

$$
\operatorname{rank}\mathscr O_n=D,
$$

$$
W_n>0.
$$

### 证明

对任意坐标向量 $x$，

$$
x^\top W_nx
=
\sum_{t=0}^{n-1}
\|CA^t x\|_2^2.
$$

故 $x$ 属于 Gramian kernel，当且仅当全部时间读出差都为零；这正是 $N_n$。有限维中 Gramian 正定等价于 kernel 为零，也等价于堆叠矩阵满列秩。∎

## 定理 90.2（有限时间层析）

若无限时间观察信息完备，则前

$$
D=d^2-1
$$

个时间层已经信息完备：

$$
\boxed{
N_\infty=\{0\}
\Longrightarrow
N_D=\{0\}.
}
$$

更强地：

$$
N_\infty=N_D.
$$

### 证明

由 Cayley–Hamilton 定理，

$$
A^D
$$

是

$$
I,A,\ldots,A^{D-1}
$$

的线性组合。所有更高次幂递归落入相同 span，因此无限可观测矩阵的行空间已经由前 $D$ 个时间层生成。∎

## 结论 90.1

$$
\boxed{
\text{finite-dimensional quantum complete observation}
\Longrightarrow
\text{finite-horizon complete certificate}.
}
$$

有限性来自 Hermitian 差空间维数，而不是来自状态集合有限。

---

# 91. 量子 instrument：概率与状态改变的统一

POVM 只决定一步结果概率；完整测量还要描述结果后状态。

## 定义 91.1（量子 instrument）

对设置 $x$，量子 instrument 是一族线性映射

$$
\{\mathcal I_{a|x}\}_{a\in A_x}
$$

满足：

1. 每个 $\mathcal I_{a|x}$ 完全正；
2. 每个分支迹不增加；
3. 分支和

$$
\Lambda_x
=
\sum_a\mathcal I_{a|x}
$$

迹保持。

定义效果

$$
E_{a|x}
=
\mathcal I_{a|x}^*(I).
$$

则

$$
E_{a|x}\ge0,
\qquad
\sum_aE_{a|x}=I.
$$

## 定理 91.1（instrument 的 Born 边缘）

$$
\boxed{
p(a\mid x,\rho)
=
\operatorname{Tr}\mathcal I_{a|x}(\rho)
=
\operatorname{Tr}(\rho E_{a|x}).
}
$$

## 定义 91.2（条件状态）

若

$$
p(a\mid x,\rho)>0,
$$

则

$$
\boxed{
\rho_{a|x}
=
\frac{\mathcal I_{a|x}(\rho)}
{p(a\mid x,\rho)}.
}
$$

## 定义 91.3（未读状态）

$$
\boxed{
\overline\rho_x
=
\sum_a\mathcal I_{a|x}(\rho).
}
$$

并有量子全概率分解

$$
\boxed{
\overline\rho_x
=
\sum_a
p(a\mid x,\rho)\rho_{a|x},
}
$$

其中零概率分支按任意约定填充而不影响加权和。

仓库 `Conditioning.lean` 已在有限正交投影测量上机器核验：

- 记录权重之和等于原迹；
- 未读测量保迹；
- 未读映射幂等；
- 固定点恰好是记录间交叉块为零的矩阵；
- 非零结果条件态正半定且迹一；
- 未读状态等于条件分支的加权集合。

---

# 92. 同一 POVM 不等于同一观察者

取量子比特 $Z$ 投影

$$
P_0=|0\rangle\langle0|,
\qquad
P_1=|1\rangle\langle1|.
$$

定义 Lüders instrument：

$$
\mathcal L_a(\rho)
=
P_a\rho P_a.
$$

再定义测量—重制备 instrument：

$$
\mathcal J_a(\rho)
=
\operatorname{Tr}(P_a\rho)
|+\rangle\langle+|.
$$

两者具有相同效果：

$$
\mathcal L_a^*(I)
=
\mathcal J_a^*(I)
=
P_a.
$$

所以它们对任意初态的一步结果分布完全相同。

但得到结果 $0$ 后：

$$
\mathcal L
\text{ 产生 }|0\rangle,
$$

$$
\mathcal J
\text{ 产生 }|+\rangle.
$$

若随后测量 $X$，前者得到 $+$ 的概率为 $1/2$，后者为 $1$。

## 定理 92.1（静态等价不推出顺序等价）

存在两个 instrument：

$$
\mathcal I,\mathcal J
$$

使其效果 POVM 完全相同，但某个二步实验的联合结果分布不同。

## 结论 92.1

$$
\boxed{
\text{POVM}
=
\text{一步统计接口},
}
$$

$$
\boxed{
\text{instrument}
=
\text{统计 + 干预接口}.
}
$$

所以完整量子观察者不能只定义为一组效果；顺序观察必须保留 instrument 分支。

---

# 93. 顺序观察者与 word effects

把一次设置—结果分支写成字母

$$
g=(x,a).
$$

对词

$$
w=g_1g_2\cdots g_n,
$$

定义 Schrödinger 分支复合

$$
\mathcal I_w
=
\mathcal I_{g_n}
\circ\cdots\circ
\mathcal I_{g_1}.
$$

定义 Heisenberg word effect

$$
\boxed{
F_w
=
\mathcal I_{g_1}^*
\circ\cdots\circ
\mathcal I_{g_n}^*(I).
}
$$

## 定理 93.1（词概率迹表示）

$$
\boxed{
p(w\mid\rho)
=
\operatorname{Tr}\mathcal I_w(\rho)
=
\operatorname{Tr}(\rho F_w).
}
$$

### 证明

反复应用对偶关系：

$$
\operatorname{Tr}(\mathcal I_g(X)A)
=
\operatorname{Tr}(X\mathcal I_g^*(A)).
$$

从末分支向前拉回单位效果，即得。∎

## 定义 93.1（顺序可见空间）

$$
V_n^{\mathrm{seq}}
=
\operatorname{span}_{\mathbb R}
\{F_w:|w|\le n\}.
$$

空词满足

$$
F_\varepsilon=I.
$$

等价地可递归定义：

$$
V_0^{\mathrm{seq}}=\mathbb RI,
$$

$$
V_{n+1}^{\mathrm{seq}}
=
V_n^{\mathrm{seq}}
+
\sum_g
\mathcal I_g^*
\bigl(V_n^{\mathrm{seq}}\bigr).
$$

定义顺序残差

$$
N_n^{\mathrm{seq}}
=
\left(V_n^{\mathrm{seq}}\right)^\perp.
$$

## 定理 93.2（顺序观察等价）

两个状态对全部长度不超过 $n$ 的实验词不可区分，当且仅当

$$
\rho-\sigma\in N_n^{\mathrm{seq}}.
$$

这把非交换 instrument 词纳入原文第 8–9 节的自由词 completion。

---

# 94. 顺序层析的有限深度终止

## 定理 94.1（一次稳定永久稳定）

若

$$
V_{n+1}^{\mathrm{seq}}
=
V_n^{\mathrm{seq}},
$$

则对所有 $m\ge n$：

$$
V_m^{\mathrm{seq}}
=
V_n^{\mathrm{seq}}.
$$

### 证明

等式意味着对每个分支 $g$：

$$
\mathcal I_g^*
\left(V_n^{\mathrm{seq}}\right)
\subseteq
V_n^{\mathrm{seq}}.
$$

因此任何更长的对偶分支复合仍把 $I$ 送入同一空间，不再产生新方向。∎

## 定理 94.2（有限顺序完备证书）

若全部有限实验词联合起来信息完备，则存在

$$
n\le d^2-1
$$

使长度不超过 $n$ 的词已经信息完备。

### 证明

递增链

$$
\mathbb RI
=
V_0^{\mathrm{seq}}
\subseteq
V_1^{\mathrm{seq}}
\subseteq
\cdots
\subseteq
\operatorname{Herm}_d
$$

从维数 $1$ 开始，最多达到 $d^2$。若在完备前某一步不再严格增长，由定理 94.1 永久稳定，永远不可能完备。因此若最终完备，至多发生 $d^2-1$ 次严格增长。∎

## 解释

静态效果不完备的观察者可能通过受控顺序干预变得完备；但所需词深在有限维中仍有有限上界。

---

# 95. 理想记录、条件化与两种“坍缩”

设投影测量满足

$$
P_aP_b=\delta_{ab}P_a,
\qquad
\sum_aP_a=I.
$$

Lüders instrument 为

$$
\mathcal I_a(\rho)=P_a\rho P_a.
$$

引入记录空间

$$
\mathcal H_M
=
\operatorname{span}\{|a\rangle_M\}.
$$

定义等距映射

$$
V|\psi\rangle
=
\sum_a
P_a|\psi\rangle\otimes|a\rangle_M.
$$

## 定理 95.1（记录等距性）

$$
V^\dagger V=I.
$$

### 证明

$$
V^\dagger V
=
\sum_{a,b}
P_aP_b\langle a|b\rangle
=
\sum_aP_a
=
I.
$$

∎

对一般状态：

$$
V\rho V^\dagger
=
\sum_{a,b}
P_a\rho P_b
\otimes
|a\rangle\langle b|_M.
$$

## 定理 95.2（选择性条件化）

读取记录 $a$ 后，系统条件态为

$$
\boxed{
\rho_a
=
\frac{P_a\rho P_a}
{\operatorname{Tr}(\rho P_a)}.
}
$$

## 定理 95.3（非选择性边缘化）

忽略记录自由度后：

$$
\boxed{
\operatorname{Tr}_M(V\rho V^\dagger)
=
\sum_aP_a\rho P_a.
}
$$

## 严格区分 95.1

因此“坍缩”至少有两种不同数学含义：

$$
\boxed{
\text{selective update}
=
\text{对已知记录条件化},
}
$$

$$
\boxed{
\text{unread update}
=
\text{忽略记录后的约化通道}.
}
$$

两者均不需要把人类意识加入动力学公式。

但它们也没有单独证明：

$$
\boxed{
\text{全局本体只保留一个分支}.
}
$$

这是量子解释层的附加问题，不能由偏迹恒等式偷渡得到。

---

# 96. 环境记录 Gram 通道

设系统指针基为

$$
\{|i\rangle\}_{i=1}^d,
$$

环境为每个系统地址写入归一化记录

$$
|e_i\rangle.
$$

受控记录等距映射为

$$
V|i\rangle
=
|i\rangle\otimes|e_i\rangle.
$$

定义记录 Gram 矩阵

$$
G_{ij}
=
\langle e_j|e_i\rangle.
$$

## 定理 96.1（环境边缘通道）

对任意系统矩阵 $\rho$：

$$
\boxed{
\mathcal D_G(\rho)
=
\operatorname{Tr}_E(V\rho V^\dagger)
=
G\odot\rho,
}
$$

即

$$
(\mathcal D_G(\rho))_{ij}
=
G_{ij}\rho_{ij}.
$$

### 证明

展开

$$
V\rho V^\dagger
=
\sum_{i,j}
\rho_{ij}
|i\rangle\langle j|
\otimes
|e_i\rangle\langle e_j|.
$$

对环境取偏迹，得到系数

$$
\operatorname{Tr}
(|e_i\rangle\langle e_j|)
=
\langle e_j|e_i\rangle.
$$

∎

仓库 `EnvironmentRecords.lean` 已在二点系统上形式化同一结构：记录重叠决定逐项 record channel，并在常数非对角重叠时精确等于 phase damping。`MeasurementMarginal.lean` 进一步证明，复制地址到正交环境记录并取偏迹时，结果恰为

$$
\sum_kP_k\rho P_k
$$

且所有非对角项为零。

---

# 97. 固定块代数、经典中心与指数退相干

## 定理 97.1（记录通道固定点）

$$
\boxed{
\mathcal D_G(\rho)=\rho
\iff
(G_{ij}-1)\rho_{ij}=0
\quad
\forall i,j.
}
$$

### 证明

逐矩阵元比较即可。∎

## 定义 97.1（记录等价）

对归一化记录，定义

$$
i\approx_E j
\iff
G_{ij}=1.
$$

由 Cauchy–Schwarz 等号条件，

$$
G_{ij}=1
$$

当且仅当

$$
|e_i\rangle=|e_j\rangle.
$$

故 $\approx_E$ 是等价关系。令等价类为

$$
C_1,\ldots,C_r
$$

并令

$$
P_k
=
\sum_{i\in C_k}|i\rangle\langle i|.
$$

## 定理 97.2（固定块代数）

$$
\boxed{
\operatorname{Fix}(\mathcal D_G)
=
\bigoplus_{k=1}^r
P_kM_d(\mathbb C)P_k
\cong
\bigoplus_{k=1}^r
M_{|C_k|}(\mathbb C).
}
$$

### 证明

定理 97.1 表明，只有记录完全相同的地址之间可以保留矩阵元；这些地址恰组成上述等价类。∎

## 解释

环境并不总是把系统变成完全经典概率分布。更一般结果是：

$$
\boxed{
\text{classical record label}
+
\text{quantum state inside each indistinguishable block}.
}
$$

固定代数的中心为

$$
Z(\operatorname{Fix}\mathcal D_G)
=
\bigoplus_k\mathbb CP_k,
$$

它给出稳定、可复制的经典标签；类内矩阵代数给出 decoherence-free quantum degrees of freedom。

## 定理 97.3（重复记录的指数衰减）

若每次交互写入独立的同型环境记录，则

$$
(\mathcal D_G^n(\rho))_{ij}
=
G_{ij}^n\rho_{ij}.
$$

若不同记录类之间存在统一常数

$$
|G_{ij}|\le q<1,
$$

定义极限 pinching

$$
\mathcal P(\rho)
=
\sum_kP_k\rho P_k.
$$

则

$$
\boxed{
\|\mathcal D_G^n(\rho)-\mathcal P(\rho)\|_{\mathrm{HS}}
\le
q^n
\|\rho-\mathcal P(\rho)\|_{\mathrm{HS}}.
}
$$

### 证明

类外矩阵元逐项乘以 $G_{ij}^n$；平方求和后提取 $q^{2n}$，再开平方。∎

仓库 `QubitWitnesses` 与 `Decoherence` 已机器核验量子比特非对角项按 $c^N$ 精确衰减、阻尼复合时系数相乘，并证明非平凡相位阻尼固定点恰好是对角矩阵。

## 推论 97.1（纯经典性判据）

若每个记录等价类均为单点，则固定代数交换：

$$
\operatorname{Fix}(\mathcal D_G)\cong\mathbb C^d.
$$

观察者状态只剩概率向量

$$
(p_1,\ldots,p_d).
$$

因此：

$$
\boxed{
\text{classical observable reality}
=
\text{stable accessible commutative algebra}.
}
$$

---

# 98. 非交换性、兼容性与不确定性

仓库 `ObserverAlgebra` 定义寄存器读取

$$
(M_f\psi)(i)=f(i)\psi(i)
$$

和可逆更新

$$
(U_\tau\psi)(i)=\psi(\tau^{-1}i).
$$

`ObserverCommutator` 机器核验：

$$
\boxed{
[U_\tau,M_f]\psi(i)
=
\left(
f(\tau^{-1}i)-f(i)
\right)
\psi(\tau^{-1}i).
}
$$

`ObserverMetric` 定义更新缺陷

$$
\delta_\tau f(i)
=
f(\tau^{-1}i)-f(i)
$$

及其有限窗口 sup 半范数，并证明其为零当且仅当读出在更新下不变。

## 定义 98.1（通道不扰动可观测量）

量子通道 $\Lambda$ 不扰动 Hermitian 量 $A$，若

$$
\Lambda^*(A)=A.
$$

这等价于：

$$
\operatorname{Tr}(\Lambda(\rho)A)
=
\operatorname{Tr}(\rho A)
$$

对所有状态成立。

## 定义 98.2（操作中心）

$$
\boxed{
\mathcal Z_{\mathrm{op}}
=
\mathcal A_{\mathfrak O}
\cap
\operatorname{Fix}(\Lambda^*).
}
$$

它表示观察前后均可访问且期望不变的事实代数。

## 定理 98.1（锐测量兼容性）

两组 PVM

$$
\{P_a\},
\qquad
\{Q_b\}
$$

存在联合 PVM，当且仅当

$$
P_aQ_b=Q_bP_a
$$

对全部 $a,b$ 成立。

### 证明

若逐项交换，定义

$$
R_{ab}=P_aQ_b.
$$

它们构成联合 PVM并恢复两个边缘。

反向若存在联合 PVM $R_{ab}$，则

$$
P_aQ_b
=
R_{ab}
=
Q_bP_a.
$$

∎

此结论只针对锐 PVM；一般非锐 POVM 可在效果不两两交换时仍联合可测。

## 定理 98.2（Robertson 不确定性）

对 Hermitian $A,B$：

$$
\boxed{
\Delta_\rho A\,
\Delta_\rho B
\ge
\frac12
\left|
\operatorname{Tr}(\rho[A,B])
\right|.
}
$$

### 证明概要

在算子空间定义半内积

$$
\langle X,Y\rangle_\rho
=
\operatorname{Tr}(\rho X^\dagger Y).
$$

对中心化算子应用 Cauchy–Schwarz，再取内积虚部，其值为交换子期望的一半。∎

非交换性不是“观察者意识扰乱现实”，而是允许问题的算子组合结构依赖顺序。

---

# 99. 局部观察者与约化态边界

设全局系统为

$$
\mathcal H_A\otimes\mathcal H_B.
$$

观察者 $B$ 只能访问局部效果

$$
I_A\otimes E_B.
$$

定义约化态

$$
\rho_B
=
\operatorname{Tr}_A\rho_{AB}.
$$

## 定理 99.1（局部观察等价）

若观察者 $B$ 可以使用全部局部效果，则

$$
\boxed{
\rho_{AB}\sim_B\sigma_{AB}
\iff
\operatorname{Tr}_A\rho_{AB}
=
\operatorname{Tr}_A\sigma_{AB}.
}
$$

### 证明

正向：所有局部期望相等意味着两个约化态对全部 Hermitian 局部算子配对相等，非退化性推出约化态相等。

反向：由偏迹定义，

$$
\operatorname{Tr}\bigl(\rho_{AB}(I\otimes E)\bigr)
=
\operatorname{Tr}(\rho_BE).
$$

约化态相等即全部局部读出相等。∎

## 推论 99.1（局部不可见维数）

若

$$
\dim\mathcal H_A=d_A,
\qquad
\dim\mathcal H_B=d_B,
$$

则全局迹零 Hermitian 维数为

$$
d_A^2d_B^2-1,
$$

而全部 $B$ 局部读出最多保留

$$
d_B^2-1
$$

个自由度。因此局部不可见残差维数为

$$
\boxed{
d_B^2(d_A^2-1).
}
$$

## 例 99.1

两个 Bell 态

$$
|\Phi^\pm\rangle
=
\frac{|00\rangle\pm|11\rangle}{\sqrt2}
$$

全局正交，但单边约化态均为

$$
I/2.
$$

所以任何单边观察者都看不到其全局相位差。

---

# 100. 单样本、自我观察与不可克隆边界

## 定理 100.1（非正交态不能单次完美区分）

若两个纯态可由一次测量无误区分，则它们正交。

### 证明

若某效果 $E$ 完美识别 $|\psi\rangle$ 而排除 $|\phi\rangle$，则

$$
\langle\psi|E|\psi\rangle=1,
$$

$$
\langle\phi|E|\phi\rangle=0.
$$

由 $0\le E\le I$ 得

$$
E|\psi\rangle=|\psi\rangle,
$$

$$
E|\phi\rangle=0.
$$

所以

$$
\langle\phi|\psi\rangle
=
\langle\phi|E|\psi\rangle
=
0.
$$

∎

因此完整层析要求重复制备、先验限制或额外副本，不能从单个任意未知态中一次读出全部参数。

## 定理 100.2（不可克隆）

若酉变换 $U$ 同时满足

$$
U|\psi\rangle|0\rangle
=
|\psi\rangle|\psi\rangle,
$$

$$
U|\phi\rangle|0\rangle
=
|\phi\rangle|\phi\rangle,
$$

则

$$
\langle\phi|\psi\rangle
=
\langle\phi|\psi\rangle^2.
$$

所以两态要么相同，要么正交。

### 证明

酉变换保持内积；输入内积为

$$
\langle\phi|\psi\rangle,
$$

输出内积为

$$
\langle\phi|\psi\rangle^2.
$$

故结论成立。∎

## 自我观察边界

内部观察者作为宇宙子系统，只能直接访问其局部记录代数。即使它能层析自己的约化态，也不能由局部记录唯一恢复与外部系统的全部纠缠纯化。

所以：

$$
\boxed{
\text{self-observation completeness}
}
$$

必须相对于可重复制备、可访问代数和系统边界定义，不能被理解成“一个有限子系统瞬时拥有宇宙完整波函数”。

---

# 101. 经典答案表的双重障碍

一种强经典模型要求每个隐藏纤维 $\lambda$ 为全部问题预先赋值，并保持矩阵代数的加法、乘法和单位：

$$
v_\lambda:
M_d(\mathbb C)\to\mathbb C.
$$

这要求一个含单位复代数 character。

## 定理 101.1（非平凡矩阵代数无 character）

当 $d\ge2$ 时：

$$
\boxed{
\operatorname{AlgHom}_{\mathbb C}
(M_d(\mathbb C),\mathbb C)
=
\varnothing.
}
$$

### 证明

对矩阵单位 $e_{ij}$，若 $i\ne j$：

$$
e_{ij}^2=0,
$$

所以

$$
v(e_{ij})^2=0,
$$

从而

$$
v(e_{ij})=0.
$$

又有

$$
e_{ii}=e_{ij}e_{ji},
$$

故

$$
v(e_{ii})=0.
$$

于是

$$
1=v(I)=\sum_i v(e_{ii})=0,
$$

矛盾。∎

仓库 `WindowCharacter.lean` 已用 Weyl clock–shift 关系对每个非平凡有限窗口矩阵代数形式化相同障碍。

但严格边界是：

$$
\boxed{
\text{no algebra character}
}
$$

要求保持整个代数结构，比通常 Kochen–Specker 型投影赋值条件更强；不能不加说明地把两者视为同一 theorem。

## 定理 101.2（局域确定性 CHSH 上界）

对任意隐藏纤维上的

$$
A_0,A_1,B_0,B_1\in\{-1,+1\},
$$

有

$$
|A_0B_0+A_0B_1+A_1B_0-A_1B_1|
\le2.
$$

概率混合后仍满足

$$
|\mathbb ES|\le2.
$$

而仓库 `CHSHWitness.lean` 已机器核验具体 Bell 态与四个观测量达到

$$
\boxed{
2\sqrt2.
}
$$

`ClassicalAnswerTableExclusion.lean` 将无 character 与 CHSH 超经典值作用于同一个 preparation-independent deterministic answer table，得到非上下文分支与局域分支的双重排除。

## 结论 101.1

量子观察者的结果统计不能一般地还原为一张同时满足：

1. 对全部上下文预存确定答案；
2. 保持完整矩阵代数关系；
3. 满足局域因子化；
4. 与 Bell 统计一致

的单一经典答案表。

---

# 102. 稳健观察度量与噪声放大

布尔完备性只回答“理论上可否区分”，实验还要回答“区分是否稳定”。

取有限效果

$$
E_1,\ldots,E_m
$$

与正权重

$$
w_r>0.
$$

## 定义 102.1（状态侧观察半范数）

对

$$
D\in\operatorname{Herm}_d^0
$$

定义

$$
\boxed{
\|D\|_{\mathfrak O}^2
=
\sum_{r=1}^m
w_r
\left|
\operatorname{Tr}(DE_r)
\right|^2.
}
$$

## 定理 102.1（kernel）

$$
\boxed{
\ker\|\cdot\|_{\mathfrak O}
=
N_{\mathfrak O}.
}
$$

因此

$$
d_{\mathfrak O}(\rho,\sigma)
=
\|\rho-\sigma\|_{\mathfrak O}
$$

在状态空间上是伪距离，在操作商上是真距离；它在完整状态空间上是真距离，当且仅当观察者信息完备。

取 $\operatorname{Herm}_d^0$ 正交基，并定义矩阵

$$
M_{r\mu}
=
\sqrt{w_r}\operatorname{Tr}(E_rF_\mu).
$$

令

$$
\alpha
=
\lambda_{\min}(M^\top M),
$$

$$
\beta
=
\lambda_{\max}(M^\top M).
$$

## 定理 102.2（frame bounds）

$$
\boxed{
\alpha\|D\|_{\mathrm{HS}}^2
\le
\|D\|_{\mathfrak O}^2
\le
\beta\|D\|_{\mathrm{HS}}^2.
}
$$

观察者完备当且仅当

$$
\alpha>0.
$$

定义条件数

$$
\boxed{
\kappa(\mathfrak O)
=
\sqrt{\beta/\alpha}.
}
$$

## 定理 102.3（线性重建噪声界）

若观测模型为

$$
y=Mx+\eta
$$

并使用 Moore–Penrose 最小二乘重建，则

$$
\boxed{
\|\widehat x-x\|_2
\le
\frac{\|\eta\|_2}{\sqrt\alpha}.
}
$$

### 证明

$$
\widehat x-x=M^\dagger\eta,
$$

而

$$
\|M^\dagger\|_{2\to2}
=
1/\sigma_{\min}(M)
=
1/\sqrt\alpha.
$$

∎

仓库 `ObserverMetric` 当前度量的是读出对更新的敏感度；本节度量的是状态差对观察者的可见度。二者分别属于 update-side 与 state-side geometry。

---

# 103. 最小观察预算是秩次模覆盖

设候选测量设置集合为

$$
\mathcal X.
$$

每个设置 $x$ 贡献中心化效果子空间

$$
U_x
=
\operatorname{span}_{\mathbb R}
\left\{
E_{a|x}
-
\frac{\operatorname{Tr}E_{a|x}}dI
\right\}_a.
$$

对设置集合 $S\subseteq\mathcal X$，定义

$$
r(S)
=
\dim
\left(
\sum_{x\in S}U_x
\right).
$$

## 定理 103.1（观察秩单调）

若

$$
A\subseteq B,
$$

则

$$
r(A)\le r(B).
$$

## 定理 103.2（观察秩次模）

$$
\boxed{
r(A)+r(B)
\ge
r(A\cup B)+r(A\cap B).
}
$$

### 证明

令

$$
U_A=\sum_{x\in A}U_x.
$$

则

$$
\dim(U_A+U_B)
+
\dim(U_A\cap U_B)
=
\dim U_A+\dim U_B.
$$

又有

$$
U_{A\cap B}\subseteq U_A\cap U_B.
$$

代入即得。∎

等价的边际收益递减形式为：

$$
r(A\cup\{x\})-r(A)
\ge
r(B\cup\{x\})-r(B)
$$

当 $A\subseteq B$。

## 定义 103.1（最小完备预算）

给定成本 $c_x>0$，求

$$
\min_{S\subseteq\mathcal X}
\sum_{x\in S}c_x
$$

满足

$$
r(S)=d^2-1.
$$

这是线性秩次模覆盖问题，而不仅是按效果标签做普通 set cover。

若预算不完备，从正交补中选择

$$
0\neq D\in
\left(\sum_{x\in S}U_x\right)^\perp
$$

即可由第 85 节构造密度矩阵对反例证书。

---

# 104. 量子 prime-time observer

仓库一般 prime-time 观察框架使用读出

$$
O_p(T^t x).
$$

量子化时令状态为 $\rho$，动力为量子通道 $\Phi$，第 $p$ 个观察通道为效果 $E_p$：

$$
O_p(\rho)
=
\operatorname{Tr}(\rho E_p).
$$

对有限索引集合 $J$ 与时间窗 $m$，定义：

$$
\rho\sim_{J,m}\sigma
$$

当且仅当

$$
\operatorname{Tr}
\left(
E_p\Phi^t(\rho-\sigma)
\right)
=0
$$

对所有

$$
p\in J,
\qquad
0\le t<m
$$

成立。

Heisenberg 化后：

$$
\operatorname{Tr}
\left(
(\rho-\sigma)(\Phi^*)^t(E_p)
\right)
=0.
$$

## 定义 104.1（prime-time 可见空间）

$$
V_{J,m}
=
\operatorname{span}_{\mathbb R}
\left\{
I,
(\Phi^*)^t(E_p):
p\in J,\ 0\le t<m
\right\}.
$$

## 定理 104.1（prime-time 残差）

$$
\boxed{
N_{J,m}
=
V_{J,m}^{\perp}.
}
$$

## 定理 104.2（双轴精化）

若

$$
J\subseteq K,
\qquad
m\le n,
$$

则

$$
V_{J,m}\subseteq V_{K,n},
$$

所以

$$
N_{K,n}\subseteq N_{J,m}.
$$

这与仓库 `BiaxialMonotoneRefinement` 的集合关系定理完全一致。

## 定理 104.3（量子有限压缩）

若全部索引—全部时间联合起来信息完备，则存在至多

$$
d^2-1
$$

个具体索引—时间效果

$$
(p_1,t_1),\ldots,(p_k,t_k)
$$

已经张成 $\operatorname{Herm}_d^0$，从而分离全部状态。

所以：

$$
\boxed{
\text{all-prime/all-time quantum completeness}
\Longrightarrow
\text{finite prime-time certificate}.
}
$$

这里的“prime”在一般 Lean carrier 中只是自然数索引；要获得真实算术素数观察者，还需添加

$$
p\in\mathbb P
$$

约束及相应数论读出。

---

# 105. 对角化与量子观察者的严格边界

仓库当前 `ObserverDiagonalSeparation.lean` 将两个独立事实包装在同一存在命题中：

1. 一维量子上下文的读出是单射；
2. 独立 `Unit/Bool` carrier 上存在固定点自由的对角逃逸。

其逻辑形状是

$$
\exists Q,\exists D,
\quad
\operatorname{Tomography}(Q)
\land
\operatorname{DiagonalEscape}(D).
$$

它不是：

$$
\operatorname{Tomography}(Q)
\Longrightarrow
\operatorname{DiagonalEscape}(Q),
$$

也不是：

$$
\operatorname{DiagonalEscape}
\Longrightarrow
\operatorname{BornRandomness}.
$$

## 原理 105.1（真实桥的最低要求）

要建立非平凡“对角—量子观察者”桥，至少需要：

1. 同一个量子状态 carrier，且 $d\ge2$；
2. 对角评估来自物理合法 instrument 或 effect；
3. 逃逸对象对应可实验区分的状态、效果、过程或记录；
4. 明确使用 positivity、normalization 与 complete positivity；
5. 得到不同于已知 contextuality、Bell、no-cloning 或普通层析的结论；
6. 给出可证伪的物理或信息论后果。

## 严格结论 105.1

对角化可以攻击“完整确定性答案表”的表示能力，但 Born 概率不能仅由 Cantor–Lawvere 逃逸推出。概率结构仍需：

$$
\text{positive state}
+
\text{normalized effects}
+
\text{state–effect pairing}.
$$

---

# 106. 无限维边界：维数不是完成进度

有限维理论中：

$$
R(\mathfrak O)=\dim N_{\mathfrak O}
$$

是良好离散进度量。

无限维中不成立。仓库 `ResidualProgressMeasure.lean` 与 `TerminalResidualDimension.lean` 已机器核验：在

$$
\ell^2(\mathbb N)
$$

中存在严格递减闭子空间链

$$
R_0\supsetneq R_1\supsetneq R_2\supsetneq\cdots
$$

使每个 $R_n$ 都线性等距同构于整个环境空间，但

$$
\bigcap_nR_n=\{0\}.
$$

所以：

$$
\boxed{
\text{same Hilbert dimension at every finite stage}
}
$$

与

$$
\boxed{
\text{genuine strict completion progress}
}
$$

可以同时发生。

## 定义 106.1（测试残差）

对闭子空间 $R$ 与测试族 $T$：

$$
\mathcal R_T(R)
=
\sup_{x\in T}\|P_Rx\|.
$$

仓库已经证明，对递减且具有正交投影的残差链，该量单调不增。

## 结论 106.1

无限维 observer completion 应使用：

- 投影范数；
- 指定测试族；
- 谱隙；
- trace-class / Hilbert–Schmidt 能量；
- 强、弱或一致收敛模式

而不能只用裸基数维数。

---

# 107. 完整量子观察者定义

## 定义 107.1（量子观察者）

一个有限维量子观察者定义为

$$
\boxed{
\mathfrak O
=
\left(
\mathcal H_S,
\mathcal H_M,
X,
\{A_x\},
\{\mathcal I_{a|x}\},
\Phi,
\mathcal A_M
\right).
}
$$

其中：

- $\mathcal H_S$：被观察系统空间；
- $\mathcal H_M$：记录／记忆空间；
- $X$：可选择测量设置；
- $A_x$：设置 $x$ 的结果集；
- $\mathcal I_{a|x}$：CP instrument 分支；
- $\Phi$：观察间隔中的系统动力学；
- $\mathcal A_M$：观察者可以读取的记录代数。

## 定义 107.2（经典—量子记录通道）

$$
\boxed{
\mathcal M_x(\rho)
=
\sum_a
\mathcal I_{a|x}(\rho)
\otimes
|a\rangle\langle a|_M.
}
$$

若只保留结果、丢弃测后系统：

$$
\boxed{
\mathcal C_x(\rho)
=
\sum_a
\operatorname{Tr}(\rho E_{a|x})
|a\rangle\langle a|.
}
$$

## 定义 107.3（顺序签名）

对全部允许实验词 $w$：

$$
\boxed{
\Sigma_{\mathfrak O}^{\mathrm{seq}}(\rho)(w)
=
\operatorname{Tr}(\rho F_w).
}
$$

## 定义 107.4（完整观察等价）

$$
\rho\sim_{\mathfrak O}^{\mathrm{seq}}\sigma
$$

当且仅当全部允许实验词产生相同概率。

## 定义 107.5（顺序可见 operator system）

$$
\boxed{
V_{\mathfrak O}^{\mathrm{seq}}
=
\operatorname{span}_{\mathbb R}
\{F_w:w\text{ allowed}\}.
}
$$

其不可见残差为

$$
\boxed{
N_{\mathfrak O}^{\mathrm{seq}}
=
\left(
V_{\mathfrak O}^{\mathrm{seq}}
\right)^\perp.
}
$$

---

# 108. 量子观察者统一定理

## 定理 108.1（统一 kernel 定理）

对任意有限维量子观察者：

$$
\boxed{
\rho\sim_{\mathfrak O}^{\mathrm{seq}}\sigma
\iff
\rho-\sigma\in
N_{\mathfrak O}^{\mathrm{seq}}.
}
$$

## 定理 108.2（统一完备性）

以下等价：

$$
\mathfrak O
\text{ 对允许顺序协议信息完备},
$$

$$
N_{\mathfrak O}^{\mathrm{seq}}=\{0\},
$$

$$
V_{\mathfrak O}^{\mathrm{seq}}
=
\operatorname{Herm}_d.
$$

## 定理 108.3（有限协议证书）

若允许的全部有限词联合起来信息完备，则存在有限词集

$$
w_1,\ldots,w_m
$$

满足

$$
m\le d^2-1
$$

且中心化 word effects 已经张成

$$
\operatorname{Herm}_d^0.
$$

若按最大词长计，则存在

$$
n\le d^2-1
$$

使长度不超过 $n$ 的词已经完备。

## 定理 108.4（不完备物理反例）

若观察者不完备，则存在

$$
0\neq D\in
N_{\mathfrak O}^{\mathrm{seq}}
$$

以及

$$
\rho_\pm
=
\frac Id\pm\varepsilon D
$$

使：

$$
\rho_+\neq\rho_-,
$$

但：

$$
\Sigma_{\mathfrak O}^{\mathrm{seq}}(\rho_+)
=
\Sigma_{\mathfrak O}^{\mathrm{seq}}(\rho_-).
$$

## 总解释

统一理论由四层组成：

$$
\boxed{
\text{effect}
\longrightarrow
\text{probability},
}
$$

$$
\boxed{
\text{instrument}
\longrightarrow
\text{state intervention},
}
$$

$$
\boxed{
\text{record}
\longrightarrow
\text{conditioning / marginalization},
}
$$

$$
\boxed{
\text{visible operator system}
\longleftrightarrow
\text{invisible state residual}.
}
$$

观察者不是一个额外于物理的意识变量，而是具有有限问题集、干预能力、记忆载体与可访问记录代数的操作系统。

---

# 109. 与当前 Lean 真值的追加锚定

| 结构 | Lean 锚点 | 本增订中的角色 |
|---|---|---|
| Pauli 非交换、Born 权重、无矩阵 character | `D5/S3/Quantum/FiniteDimensional` | 最小有限维量子骨架 |
| X/Z 无公共本征向量、Bell 非乘积、$c^N$ 阻尼 | `D5/S3/Quantum/QubitWitnesses` | 不兼容、纠缠与相干衰减见证 |
| 阻尼复合与固定对角代数 | `D5/S3/Quantum/Decoherence` | 退相干半群与固定点 |
| 环境记录 Gram 通道 | `D5/S3/Quantum/EnvironmentRecords` | 记录重叠到局部退相干 |
| 坐标运输与 Hadamard 指针基 | `D5/S3/Quantum/PointerBasis` | 环境选择的稳定坐标 |
| 投影记录、未读态与条件态 | `D5/S3/Observer/Conditioning` | Lüders instrument 的矩阵实例 |
| 纯态秩一 Born 模平方化简 | `D5/S3/Observer/BornReduction` | state–effect pairing 的纯态证书 |
| 复制地址记录的环境边缘 | `D5/S3/Observer/MeasurementMarginal` | 非选择性测量的具体 dilation |
| 完备互补上下文层析 | `D5/S3/Quantum/Tomography/CompleteContextTomography` | $V_{\mathfrak O}=\operatorname{Herm}$ 的实例 |
| 一维层析与独立布尔逃逸并存 | `D5/S3/Quantum/Tomography/ObserverDiagonalSeparation` | 对角—量子桥的当前严格边界 |
| 读出—更新协变与交换子 | `D5/S3/Quantum/ObserverAlgebra`, `ObserverCommutator` | 非交换动态读出骨架 |
| 更新缺陷半范数 | `D5/S3/Observer/ObserverMetric` | update-side geometry |
| 循环窗口操作中心 | `D5/S3/Observer/CenterOperational` | 更新不变读出的具体中心 |
| 非平凡窗口无 character | `D5/S3/Observer/WindowCharacter` | 强经典答案表障碍 |
| Bell 态 CHSH 值 $2\sqrt2$ | `D5/S3/QuantumBounds/CHSHWitness` | 局域经典界之外的量子见证 |
| 同一答案表的双重排除 | `D5/S3/Observer/ClassicalAnswerTableExclusion` | 非上下文／局域联合边界 |
| 正迹保持映射存在平稳态 | `D5/S3/Quantum/ChannelFixedState` | 通道长期固定状态存在性 |
| 双轴不可区分精化 | `D5/S3/Observer/Refinement/BiaxialMonotoneRefinement` | prime-time 单调性 |
| 有限状态的有限 prime-time 层析 | `D5/S3/Observer/Refinement/FinitePrimeTimeTomography` | 量子有限维压缩的离散前身 |
| 无限维残差测试量 | `D5/S3/Observer/Completion/ResidualProgressMeasure` | 无限维完成进度 |
| 常维严格尾链与零终端 | `D5/S3/Observer/Completion/TerminalResidualDimension` | 裸维数失效反例 |
| 对角通道不能造相干、Hadamard 可以 | `D5/S3/Observer/StateNotPath` | “状态不是经典路径”证书 |
| GNS 矩阵范数平方恒等式 | `D5/S3/Quantum/GNSMatrix` | 正性配对的 Hilbert 几何 |
| 通用克隆机约化谱与熵 | `D5/S3/Quantum/CloningMachine` | 近似克隆模型的现有分析 |

本增订中的统一可见空间、物理反例证书、有限效果压缩、顺序 word-effect completion、一般 Gram 记录块、稳健 frame bounds、秩次模预算与局部约化等价尚未以本文同名 theorem 全部 Lean 闭合。

---

# 110. 建议追加 Lean 模块树

```text
D5/S3/QuantumObserver/Core/
  StateEffectPairing.lean
  StaticObserver.lean
  QuantumInstrument.lean
  RecordChannel.lean

D5/S3/QuantumObserver/Visibility/
  VisibleRealSpace.lean
  InvisibleResidual.lean
  ObservationalEquivalence.lean
  OperationalQuotient.lean
  RefinementOrder.lean
  JointObserver.lean

D5/S3/QuantumObserver/Tomography/
  CompletenessEquivalences.lean
  PhysicalIndistinguishablePair.lean
  FiniteEffectCertificate.lean
  OutcomeBudgetLowerBound.lean
  ModelRelativeCompleteness.lean

D5/S3/QuantumObserver/Dynamics/
  HeisenbergPullback.lean
  FiniteTimeVisibleSpace.lean
  ObservabilityMatrix.lean
  ObservabilityGramian.lean
  FiniteHorizonTomography.lean

D5/S3/QuantumObserver/Sequential/
  WordEffect.lean
  SequentialVisibleSpace.lean
  SequentialStabilization.lean
  FiniteSequentialHorizon.lean
  SamePovmDifferentInstrument.lean

D5/S3/QuantumObserver/Records/
  IdealProjectiveDilation.lean
  SelectiveVsUnreadUpdate.lean
  GeneralRecordGramChannel.lean
  RecordClassFixedAlgebra.lean
  RepeatedRecordConvergence.lean
  ClassicalCenter.lean

D5/S3/QuantumObserver/Local/
  PartialTraceObservationalEquivalence.lean
  LocalResidualDimension.lean
  SingleCopyDiscrimination.lean
  NoCloningBoundary.lean
  RecordConsistency.lean

D5/S3/QuantumObserver/Robust/
  StateObservationSeminorm.lean
  ObserverFrameBounds.lean
  ObserverConditionNumber.lean
  LinearReconstructionNoiseBound.lean

D5/S3/QuantumObserver/Budget/
  CenteredEffectRank.lean
  ObservationRankSubmodular.lean
  MinimumCompleteBudget.lean
  IncompleteBudgetPhysicalCertificate.lean

D5/S3/QuantumObserver/PrimeTime/
  QuantumPrimeTimeObserver.lean
  PrimeTimeResidual.lean
  FinitePrimeTimeEffectCertificate.lean

D5/S3/QuantumObserver/Boundary/
  CharacterVsContextuality.lean
  DiagonalQuantumBridgeRequirements.lean
  InfiniteDimensionalProgressBoundary.lean
```

建议优先闭合：

```text
observationalEquivalent_iff_sub_mem_invisibleResidual
informationallyComplete_iff_visibleSpace_eq_top
incomplete_observer_has_density_pair_certificate
complete_observer_has_finite_effect_certificate
informationallyComplete_povm_card_lower_bound
observerRefines_iff_visibleSpace_le
jointObserver_invisibleResidual_eq_inf
finite_time_observability_iff_gramian_posDef
complete_time_observer_finite_horizon
sequence_probability_eq_trace_wordEffect
sequential_complete_has_finite_horizon
same_povm_different_sequential_statistics
recordChannel_apply_eq_gram_mul
recordChannel_fixed_iff_supported_on_record_classes
repeated_record_converges_to_pinching
local_observationalEquivalent_iff_partialTrace_eq
stateObservationSeminorm_kernel
observationRank_submodular
quantum_prime_time_residual_eq_orthogonal
```

---

# 111. 追加严格非主张

1. 本增订不声称“存在观察者”本身推出复 Hilbert 空间、公理化 Born 规则或张量积系统复合。
2. 本增订不声称人的意识是量子 instrument、偏迹或条件状态更新的必要输入。
3. 本增订不声称 POVM 效果唯一决定测后状态；相同 POVM 可由不同 instrument 实现。
4. 本增订不声称一次未知量子态测量可以完成状态层析。
5. 本增订不声称层析恢复的是某个单次实验中“预先存在的经典答案表”。
6. 本增订不声称代数生成完整等价于静态效果线性 span 完整。
7. 本增订不声称所有非交换效果均不可联合测量；PVM 交换判据不直接推广为任意 POVM 的逐项交换必要性。
8. 本增订不声称退相干单独证明全局本体只剩一个结果。
9. 本增订不声称环境记录总把固定代数变成完全交换代数；一般仍可保留类内量子块。
10. 本增订不声称 pointer basis 由意识选择；它由系统—环境耦合与稳定记录结构决定。
11. 本增订不声称局部约化态包含全局纠缠的全部信息。
12. 本增订不声称观察者可以从自身单一局部记录重建宇宙完整纯态。
13. 本增订不声称无矩阵代数 character 与完整 Kochen–Specker 定理无条件等价。
14. 本增订不声称 CHSH 超经典值单独排除所有非局域或上下文隐藏变量模型。
15. 本增订不声称信息完备自动意味着数值稳定；最小 frame eigenvalue 可能极小。
16. 本增订不声称 Hilbert–Schmidt 噪声界自动覆盖有限样本统计、系统漂移或模型错设。
17. 本增订不声称秩次模预算等价于任意噪声目标下的最优实验设计。
18. 本增订不声称 `FinitePrimeTimeTomography` 当前索引已强制为算术素数。
19. 本增订不声称当前 `ObserverDiagonalSeparation` 已建立量子随机性与对角逃逸的因果桥。
20. 本增订不声称 Cantor–Lawvere 对角化单独推出 Born 概率。
21. 本增订不声称有限时间上界 $d^2-1$ 在无限维中仍成立。
22. 本增订不声称无限维残差可由裸 Hilbert 维数测量。
23. 本增订不声称正、迹保持但非完全正的任意抽象映射都是物理量子通道。
24. 本增订不声称每个 paper-level 定理已经具有 Lean kernel proof term。
25. 本增订不修改此前关于自由意志、喉部分量、RH、negative-base-$\varphi$ 或其他开放问题的边界。

---

# 112. 最终统一：量子观察者是全局状态到稳定记录现实的受限通道

本增订把量子观察者压缩为以下对象：

$$
\begin{aligned}
\rho
&=
\text{完整量子状态},\\
E_{a|x}
&=
\text{可提出的问题与结果效果},\\
\mathcal I_{a|x}
&=
\text{结果分支及其状态干预},\\
F_w
&=
\text{顺序协议在初态上的 word effect},\\
V_{\mathfrak O}^{\mathrm{seq}}
&=
\text{全部允许协议生成的可见 operator system},\\
N_{\mathfrak O}^{\mathrm{seq}}
&=
\left(V_{\mathfrak O}^{\mathrm{seq}}\right)^\perp,\\
\mathsf R_{\mathfrak O}
&=
\mathsf S_d/\!\sim_{\mathfrak O},\\
\mathcal A_M
&=
\text{观察者能够稳定读取的记录代数}.
\end{aligned}
$$

其基础关系为：

$$
\boxed{
p(w\mid\rho)
=
\operatorname{Tr}(\rho F_w),
}
$$

$$
\boxed{
\rho\sim_{\mathfrak O}\sigma
\iff
\rho-\sigma\in
N_{\mathfrak O}^{\mathrm{seq}},
}
$$

$$
\boxed{
\mathfrak O\text{ 完备}
\iff
V_{\mathfrak O}^{\mathrm{seq}}
=
\operatorname{Herm}_d,
}
$$

$$
\boxed{
\text{有限维完备}
\Longrightarrow
\text{有限效果／有限词深证书},
}
$$

$$
\boxed{
\text{环境记录}
\Longrightarrow
\text{块代数稳定化},
}
$$

$$
\boxed{
\text{经典记录}
=
\text{稳定可访问代数的交换中心}.
}
$$

因此最严格的本体—操作收束不是：

$$
\text{“观察者看见，于是创造世界”},
$$

而是：

$$
\boxed{
完整量子状态通过观察者有限的效果、instrument、动力学与记录代数，
被压缩成一个操作可区分、可条件化、可共享的现实商。
}
$$

量子性的核心也不是“物体同时偷偷走了多条经典路径”，而是：

$$
\boxed{
状态包含可在不同观察上下文中转化为概率差异的复相位结构；
这些上下文与顺序干预不能一般地压缩为一张保持全部代数关系和局域统计的经典确定答案表。
}
$$

退相干所完成的是：

$$
\boxed{
把环境反复记录的区分放大为稳定块标签，
并抑制这些标签之间的相干；
它解释经典记录结构如何涌现，
但不凭自身选定唯一量子解释。
}
$$

把本增订与前文 observer completion、agency completion 合并，最终得到三重反射：

$$
\boxed{
\begin{aligned}
\text{dynamical completion}
&=
\text{补入未来会影响读出的状态区别},\\
\text{quantum observer completion}
&=
\text{补入允许协议可生成的 effect 方向},\\
\text{agency completion}
&=
\text{补入未来会改变策略的历史区别}.
\end{aligned}
}
$$

三者共同说明：

$$
\boxed{
观察者不是完整宇宙的副本，
而是一个把未来有效区别、可执行问题、实际记录与历史选择
闭合进自身有限接口的系统。
}
$$

---

# 113. 增订四：素数观察者与量子观察者的局部—全局统一

**增订版本：v1.5，2026-08-26**

本增订继续纯追加承接第 0–112 节，不改写、删除或重排此前内容。它把 `FORMAL_PRIME_OBSERVER_DYNAMICS.md` 中的素数／素数幂局部接口、CRT 联合、prime-time 行为商、Galois–Frobenius 观察，以及本文件第 80–112 节的有限维量子观察者统一到同一个状态—效应—残差框架。

核心禁令是：

$$
\boxed{
\text{prime observer}\neq\text{quantum observer}.
}
$$

素数观察者首先规定局部算术坐标、精度塔和实验索引；量子观察者规定状态—效应配对、非交换 instrument、记录和动态协议。二者的严格交汇对象是：

$$
\boxed{
\text{prime-indexed quantum observer}.
}
$$

其基本索引可以写成

$$
i=(p,k,b,a,t),
$$

其中 $p$ 是素数，$k$ 是 $p$-进／素数幂精度，$b$ 是量子测量上下文，$a$ 是结果分支，$t$ 是演化时间。

本增订严格区分：

- **Lean 锚点**：仓库已有机器核验；
- **本文定理**：本增订给出纸面证明；
- **条件桥**：需要额外 carrier、partial trace、CP map 或无限和 API；
- **非主张**：不得由形式相似偷渡为物理本体结论。

---

# 114. 确定性素数观察者嵌入交换量子理论

设 $X$ 为有限状态集，局部接口为

$$
q_i:X\to O_i.
$$

令

$$
\mathcal H_X=\mathbb C^X
$$

并以

$$
\{|x\rangle:x\in X\}
$$

为标准正交基。

对每个结果 $o\in O_i$ 定义投影

$$
\boxed{
P_{o|i}
=
\sum_{x:q_i(x)=o}
|x\rangle\langle x|.
}
$$

## 定理 114.1（确定性读出的 PVM 实现）

对固定 $i$：

$$
P_{o|i}P_{o'|i}
=
\delta_{oo'}P_{o|i},
$$

且

$$
\sum_oP_{o|i}=I.
$$

### 证明

不同读出纤维互不相交，因此相应基投影正交；所有纤维并为 $X$，故投影和为单位。∎

## 定理 114.2（kernel 保持）

对计算基态

$$
\rho_x=|x\rangle\langle x|,
$$

有

$$
\operatorname{Tr}(\rho_xP_{o|i})
=
\mathbf1_{\{q_i(x)=o\}}.
$$

因此

$$
\boxed{
q_i(x)=q_i(y)
\iff
\rho_x,\rho_y
\text{ 对该 PVM 不可区分}.
}
$$

## 定理 114.3（交换性）

所有由这些确定性接口得到的投影均在同一标准基对角，因此

$$
[P_{o|i},P_{o'|j}]=0.
$$

所以任何有限确定性素数观察系统都可以忠实嵌入一个交换量子观察子理论：

$$
\boxed{
\text{deterministic prime observation}
\hookrightarrow
\text{commutative quantum observation}.
}
$$

反向不成立：一般量子观察者可包含相位、非交换上下文与纠缠，这些结构不能由一族共同对角的确定性读出穷尽。

---

# 115. CRT 给出真正的 prime-power 量子张量分解

令

$$
M=\prod_{p\mid M}p^{v_p(M)}.
$$

定义有限寄存器 Hilbert 空间

$$
\mathcal H_M
=
\ell^2(\mathbb Z/M\mathbb Z).
$$

CRT 给出集合等价

$$
\mathbb Z/M\mathbb Z
\cong
\prod_{p\mid M}
\mathbb Z/p^{v_p(M)}\mathbb Z.
$$

因此标准基诱导一个酉同构

$$
\boxed{
U_{\mathrm{CRT}}:
\mathcal H_M
\overset\sim\longrightarrow
\bigotimes_{p\mid M}
\mathcal H_{p^{v_p(M)}}.
}
$$

在计算基上：

$$
|n\bmod M\rangle
\longmapsto
\bigotimes_{p\mid M}
|n\bmod p^{v_p(M)}\rangle.
$$

## Lean 锚点 115.1

`D5/S3/ObserverMemory/PrimePowerTensorTower.lean` 已经在更强的完整矩阵代数层机器核验：

$$
\boxed{
M_{\mathbb Z/M\mathbb Z}(\mathbb C)
\cong
\bigotimes_{p\mid M}
M_{\mathbb Z/p^{v_p(M)}\mathbb Z}(\mathbb C).
}
$$

其 `prime_power_tensor_factor_decomposition` 给出对应代数等价的双射性。

## 结论 115.1

这里“不同素数是横向张量因子”不再只是比喻。对有限 CRT 窗口，prime-power 分解确实给出量子寄存器的自然局部子系统分解。

---

# 116. 代数张量分解不推出状态独立

即使

$$
\mathcal B(\mathcal H_M)
\cong
\bigotimes_p
\mathcal B(\mathcal H_{p^{k_p}}),
$$

一般量子态并不满足

$$
\rho=\bigotimes_p\rho_p.
$$

它可以包含经典相关、相位相关和纠缠。

## 原理 116.1

$$
\boxed{
\text{factorization of observable algebra}
\not\Rightarrow
\text{factorization of state}.
}
$$

只有当状态本身为乘积态且测量局部张量分解时，联合概率才分解：

$$
P((a_p)_p)
=
\prod_pP_p(a_p).
$$

因此 `PrimePowerTensorTower` 建立了 carrier/algebra 分解，但不能被解释成“不同素数在任意量子状态中统计独立”。

---

# 117. CRT 层析的三个模型层级

## 117.1 单一计算基标签

若先验模型限制为

$$
\rho_n=|n\bmod M\rangle\langle n\bmod M|,
$$

则全部 prime-power residue 坐标

$$
(n\bmod p^{v_p(M)})_{p\mid M}
$$

由 CRT 唯一恢复 $n\bmod M$。

所以 CRT 对该离散基模型信息完备。

## 117.2 计算基上的经典概率混合

若

$$
\rho
=
\sum_{n\bmod M}
\mu(n)|n\rangle\langle n|,
$$

完整联合 residue tuple 的分布可恢复 $\mu$。但只知道各 prime-power 边缘分布

$$
(\mu_p)_p
$$

一般不能恢复跨素数相关。

## 117.3 任意量子状态

纯 residue PVM 只读取对角元

$$
\rho_{nn}.
$$

例如

$$
|\psi_\pm\rangle
=
\frac{|x\rangle\pm|y\rangle}{\sqrt2}
$$

在所有计算基 residue 统计上相同，却具有不同相对相位。

若 $\dim\mathcal H_M=M$，对角 Hermitian 可见空间维数为 $M$，而全部 Hermitian 空间维数为 $M^2$。所以纯 residue 观察留下

$$
\boxed{
M^2-M
}
$$

维线性不可见残差。

## 结论 117.1

$$
\boxed{
\text{CRT tomography}
=
\text{classical basis-label tomography},
}
$$

不是任意量子态的完整层析。

---

# 118. 量子素数局部—全局余量

设

$$
\mathcal H
=
\bigotimes_{j=1}^{r}\mathcal H_j,
\qquad
\dim\mathcal H_j=d_j,
$$

其中每个 $j$ 对应一个 prime-power 因子。

定义所有单素数约化态读出：

$$
\mathcal R_{\mathrm{loc}}(\rho)
=
(\rho_j)_{j=1}^{r},
$$

其中

$$
\rho_j
=
\operatorname{Tr}_{\widehat j}\rho.
$$

## 定义 118.1（量子局部—全局余量）

$$
\boxed{
\operatorname{QLGRes}
=
\{(\rho,\sigma):
\rho\neq\sigma,
\ \rho_j=\sigma_j\ \forall j\}.
}
$$

## 定理 118.1（局部完整仍可全局不唯一）

若至少两个因子维数不小于 $2$，则

$$
\operatorname{QLGRes}\neq\varnothing.
$$

### 证明

在两个因子的二维子空间中取

$$
|\Phi^\pm\rangle
=
\frac{|00\rangle\pm|11\rangle}{\sqrt2}.
$$

二者是不同正交全局态，但每个单边约化态均为 $I/2$；其余因子固定为同一纯态即可。∎

## 结论 118.1

$$
\boxed{
\text{知道每个 prime factor 的完整局部量子态}
\not\Rightarrow
\text{知道完整全局量子态}.
}
$$

这给出了 `FORMAL_PRIME_OBSERVER_DYNAMICS.md` 的“局部—全局余量”在量子理论中的直接非交换实例。

---

# 119. 跨素数相关扇区的精确正交分解

对每个局部 Hermitian 空间写

$$
\operatorname{Herm}(\mathcal H_j)
=
\mathbb RI_j
\oplus
\operatorname{Herm}_0(\mathcal H_j).
$$

张量积展开得到全局正交直和：

$$
\boxed{
\operatorname{Herm}(\mathcal H)
=
\bigoplus_{S\subseteq[r]}
V_S,
}
$$

其中

$$
V_S
=
\left(
\bigotimes_{j\in S}
\operatorname{Herm}_0(\mathcal H_j)
\right)
\otimes
\left(
\bigotimes_{j\notin S}\mathbb RI_j
\right).
$$

其维数为

$$
\boxed{
\dim V_S
=
\prod_{j\in S}(d_j^2-1).
}
$$

空集项 $V_\varnothing=\mathbb RI$。

## 定理 119.1（单素数可见空间）

若观察者能使用每个单素数因子的全部局部 Hermitian 效果，但不能直接测联合相关，则可见线性空间为

$$
V_{\le1}
=
V_\varnothing
\oplus
\bigoplus_{|S|=1}V_S.
$$

其维数：

$$
\boxed{
1+\sum_{j=1}^r(d_j^2-1).
}
$$

总 Hilbert 维数记为

$$
D=\prod_jd_j.
$$

因此不可见迹零残差维数为

$$
\boxed{
D^2-1-
\sum_{j=1}^r(d_j^2-1).
}
$$

它恰由所有 $|S|\ge2$ 的跨素数相关扇区组成。

## 最深解释 119.1

$$
\boxed{
\text{quantum local-global residual}
=
\text{cross-prime correlation sectors}.
}
$$

量子层揭示的不是“素数神秘纠缠”，而是张量分解后局部边缘天然遗漏联合算子方向。

---

# 120. $m$-素数观察层级

定义

$$
V_{\le m}
=
\bigoplus_{|S|\le m}V_S.
$$

则

$$
\boxed{
\dim V_{\le m}
=
\sum_{|S|\le m}
\prod_{j\in S}(d_j^2-1).
}
$$

定义残差

$$
N_{>m}
=
V_{\le m}^{\perp}
=
\bigoplus_{|S|>m}V_S.
$$

于是形成严格层级：

$$
V_{\le1}
\subseteq
V_{\le2}
\subseteq\cdots\subseteq
V_{\le r}
=
\operatorname{Herm}(\mathcal H).
$$

## 原理 120.1（prime correlation order）

素数观察者的索引轴不能只写成

$$
(p,k,t).
$$

量子化后还必须允许“参与联合可观测量的素数子集”这一相关阶数轴：

$$
\boxed{
(S,k,b,a,t),
\qquad
S\subseteq\mathbb P_{\mathrm{finite}}.
}
$$

这把“增加素数数量”和“增加联合相关阶数”严格区分。

---

# 121. 局部动力学不能自动消除跨素数余量

设

$$
\Phi
=
\bigotimes_{j=1}^{r}\Phi_j
$$

是完全局部的乘积通道。

若效果 $E_j$ 只作用在第 $j$ 个因子，则

$$
\Phi^*(E_j\otimes I_{\widehat j})
=
\Phi_j^*(E_j)\otimes I_{\widehat j}.
$$

## 定理 121.1（局部支持保持）

乘积动力学的 Heisenberg 拉回保持每个相关扇区的支持集合：若

$$
A\in V_S,
$$

则

$$
\Phi^*(A)
\in
\bigoplus_{T\subseteq S}V_T
$$

；若各 $\Phi_j^*$ 还保持迹零局部空间，则甚至

$$
\Phi^*(V_S)\subseteq V_S.
$$

### 证明

对简单张量逐因子作用，再由线性扩张得到。若某局部迹零方向在非双随机通道下可产生单位分量，支持可以下降但不能引入新的外部因子；若局部对偶保持迹零，则支持集合保持。∎

## 推论 121.1（纯局部 prime-time no-go）

若初始可见空间只有 $V_{\le1}$，且动力学始终是局部乘积通道，则全部时间 Heisenberg 闭包不能生成 $|S|\ge2$ 的新联合相关方向。

因此：

$$
\boxed{
\text{local measurement}
+
\text{local dynamics}
\not\Rightarrow
\text{global quantum tomography}.
}
$$

跨素数相关余量若要通过时间变得可见，必须存在跨因子耦合或直接联合测量。

---

# 122. 跨素数耦合把高阶相关运输进局部读出

设 Hamiltonian 分解为

$$
H=\sum_SH_S,
$$

其中 $H_S$ 只作用于素数集合 $S$。

若 $A_R$ 只作用在 $R$ 上，则

$$
\operatorname{supp}[H_S,A_R]
\subseteq
S\cup R.
$$

Heisenberg 方程为

$$
\frac{dA}{dt}
=i[H,A].
$$

因此 effect support 沿由非零 $H_S$ 定义的相互作用超图传播。

## 原理 122.1（交互图必要性）

如果相互作用超图分成两个互不连通的 prime blocks，起初只位于一个 block 的效果在全部嵌套交换子下都不能获得另一个 block 的支持。

所以全局 prime-time 完备至少需要：

$$
\boxed{
\text{measurement support}
+
\text{interaction propagation}
}
$$

覆盖全部相关扇区。

图连通本身不是充分条件；交换子 Lie 闭包仍可能因对称性、守恒量或退化而落在真子代数中。

---

# 123. 量子有限 prime-time 压缩定理

仓库 `D5/S3/Observer/Refinement/FinitePrimeTimeTomography.lean` 已证明：若状态类型 $X$ 有限且全部自然数索引—全部时间读出共同分离状态，则存在一个有限索引集与有限时间深度已经分离；其源码明确指出该 `Nat` 索引并未强制为真实素数。

有限维量子情形可以去掉“状态集合有限”条件。

设全部 prime/precision/context/time 效果记为

$$
\mathcal E_\infty
=
\{(\Phi^*)^t(E_{p,k,b,a})\}.
$$

对每个效果中心化：

$$
\widetilde E
=
E-
\frac{\operatorname{Tr}E}{d}I.
$$

## 定理 123.1（量子 finite prime-time certificate）

若

$$
\operatorname{span}_{\mathbb R}
\{\widetilde E:E\in\mathcal E_\infty\}
=
\operatorname{Herm}_d^0,
$$

则存在

$$
m\le d^2-1
$$

个具体索引—时间效果

$$
E_{i_1,t_1},\ldots,E_{i_m,t_m}
$$

已经信息完备。

### 证明

$\operatorname{Herm}_d^0$ 是 $d^2-1$ 维实向量空间；从任意生成族抽取一个基即可。∎

令

$$
J=\{i_1,\ldots,i_m\},
\qquad
T=1+\max_jt_j.
$$

则有限矩形窗口 $J\times\{0,\ldots,T-1\}$ 已经完备。

## 结论 123.1

$$
\boxed{
\text{all-prime/all-precision/all-time completeness}
\Longrightarrow
\text{finite prime-time quantum certificate}.
}
$$

这里的有限性来自算子空间维数，不来自量子状态集合的基数。

---

# 124. prime precision entropy 与量子观察预算

仓库 `D5/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction.lean` 已机器核验：对 $s>1$、素数 $p$，canonical prime-exponent geometric channel 的未解析尾熵在每增加一层精度时精确按

$$
\boxed{
p^{-s}}
$$

缩放。

若记第 $k$ 层未解析熵为 $R_{p,k}$，则：

$$
\boxed{
R_{p,k+1}
=p^{-s}R_{p,k}.
}
$$

这一定理属于算术概率通道，不是量子退相干定理；但它提供了自然的纵向 prime-precision 成本权重。

## 定义 124.1（prime-precision 概率权重）

令

$$
Z_s=\sum_{p\in\mathbb P}p^{-s},
\qquad s>1.
$$

定义

$$
\boxed{
\nu_s(p,k)
=
\frac{(1-p^{-s})p^{-s(k+1)}}{Z_s},
\qquad k\ge0.
}
$$

因为

$$
\sum_{k\ge0}(1-p^{-s})p^{-s(k+1)}=p^{-s},
$$

故

$$
\sum_{p,k}\nu_s(p,k)=1.
$$

这给出一个横向 prime、纵向 precision 的规范可和预算分布。

---

# 125. zeta-weighted prime-time Gramian

再令

$$
\mu_\beta(t)
=(1-\beta)\beta^t,
\qquad 0<\beta<1.
$$

对中心化 Heisenberg 效果

$$
e_{p,k,b,a,t}
=
(\Phi^*)^t(E_{p,k,b,a})
-
\frac{\operatorname{Tr}((\Phi^*)^tE_{p,k,b,a})}{d}I,
$$

给定上下文／结果正权重 $w_{b,a}$，定义形式上的 prime-time Gram 算子：

$$
\boxed{
W_{s,\beta}
=
\sum_{p,k,b,a,t}
\nu_s(p,k)\mu_\beta(t)w_{b,a}
|e_{p,k,b,a,t}\rangle
\langle e_{p,k,b,a,t}|.
}
$$

有限维且权重总和有限时，该正算子和在算子范数下收敛。

## 定理 125.1（能量恒等式）

对任何迹零 Hermitian 状态差 $D$：

$$
\boxed{
\langle D,W_{s,\beta}D\rangle_{\mathrm{HS}}
=
\sum_{p,k,b,a,t}
\nu_s(p,k)\mu_\beta(t)w_{b,a}
|\operatorname{Tr}(De_{p,k,b,a,t})|^2.
}
$$

## 定理 125.2（kernel）

若所有申报权重严格为正，则

$$
\boxed{
\ker W_{s,\beta}
=
\bigcap_{p,k,b,a,t}
\ker\bigl[D\mapsto
\operatorname{Tr}(De_{p,k,b,a,t})\bigr].
}
$$

### 证明

右侧显然包含于 kernel。反向若二次型为零，则正权重下每个非负平方项都必须为零。∎

所以：

$$
\boxed{
W_{s,\beta}>0
\iff
\text{全部加权 prime-time effects 信息完备}.
}
$$

参数具有清楚的实验设计含义：

$$
\begin{aligned}
s&=\text{横向素数预算衰减},\\
k&=\text{纵向同素数精度},\\
\beta&=\text{时间深度折扣}.
\end{aligned}
$$

不得把某个特殊 $s$ 值无条件解释成物理相变或 RH 临界线。

---

# 126. Frobenius 观察的量子后处理不可恢复定理

仓库 `D5/S3/Factorization/Galois/GaloisPrimeObserver.lean` 定义带分歧标签的 Frobenius 素数观察器：未分歧素数输出 Frobenius 共轭类，分歧素数输出 `none`。

它已经机器核验：若共轭类输出有限且分歧素数集合有限，则存在某个共轭类被无限多个未分歧素数共同输出；并分别给出删除两个假设后的边界反例。

现在设任意量子编码

$$
\eta:
\operatorname{Option}(\operatorname{ConjClasses}G)
\to
\mathsf S(\mathcal H),
$$

后接任意量子通道／instrument 观察签名

$$
\Sigma_{\mathfrak O}.
$$

定义复合：

$$
p
\mapsto
O_{\mathrm{Frob}}(p)
\mapsto
\eta(O_{\mathrm{Frob}}(p))
\mapsto
\Sigma_{\mathfrak O}.
$$

## 定理 126.1（后处理不可恢复）

$$
\boxed{
\ker O_{\mathrm{Frob}}
\subseteq
\ker(
\Sigma_{\mathfrak O}\circ\eta\circ O_{\mathrm{Frob}}
).
}
$$

### 证明

若两个素数已有完全相同的 Frobenius 标签，则其量子编码态相同，任何确定的下游量子通道与统计读出必给相同结果。∎

## 结论 126.1

$$
\boxed{
\text{quantum postprocessing cannot recover information
already erased by the Frobenius-class quotient}.
}
$$

若要区分同一 Frobenius fiber 内的素数，必须增加不经该粗标签因子化的新接口，而不是只对旧标签做更复杂的量子处理。

---

# 127. Frobenius 素数身份的相对信息率趋零

固定 $N$，令 $P_N$ 在所有 $p\le N$ 的素数中均匀分布。则素数身份熵：

$$
H(P_N)=\log\pi(N).
$$

若某固定 Galois/Frobenius 观察器只有 $r<\infty$ 个可能输出，则

$$
H(O(P_N))\le\log r.
$$

因此：

$$
\boxed{
\frac{H(O(P_N))}{H(P_N)}
\le
\frac{\log r}{\log\pi(N)}
\longrightarrow0.
}
$$

## 原理 127.1

有限输出的素数观察器即使对某些算术性质极有意义，也不可能以正比例保存不断增长的“素数身份信息”。

这比“存在无限 fiber”更定量，但仍不等于 Chebotarev 密度定理；它只使用有限输出容量与素数数量发散。

---

# 128. 二次角色观察是一个交换量子子代数

仓库 `D5/S3/PrimeForms/Splitting/QuadraticCharacterProfileRedundancy.lean` 已机器核验：在

$$
(\mathbb Z/60\mathbb Z)^\times
$$

上，Gaussian、Eisenstein、Golden 三个 splitting characters 生成全部二次 character；所有二次 character 都在三环画像 fiber 上常值，而每个 fiber 恰有两个元素。

把单位类 $u$ 编码为计算基态 $|u\rangle$。每个二次角色成为对角可观测量：

$$
A_\chi
=
\sum_u\chi(u)|u\rangle\langle u|.
$$

这些算子两两交换。

## 定理 128.1（二次角色量子后处理 no-go）

若

$$
\operatorname{triRingImage}(u)
=
\operatorname{triRingImage}(v),
$$

则对任何由三 splitting characters 通过加法、乘法、函数演算以及仅依赖其联合经典输出的量子制备得到的观察协议，$u,v$ 仍不可区分。

### 证明

仓库定理说明每个二次 character 都在该 fiber 上常值；这些 character 生成的交换代数中任意函数亦常值。任何只依赖其输出的下游通道仍通过同一 quotient 因子化。∎

## 结论 128.1

$$
\boxed{
\text{adding more quadratic characters}
\text{ cannot recover the missing two-element fiber bit}.
}
$$

必须加入不属于该二次角色代数的新观察量，例如定向信息或更精细非因子化接口。

---

# 129. Galois fiber product 与量子 marginal fiber 的差异

仓库 `D5/S3/Factorization/Galois/GaloisFusion.lean` 已机器核验：两个子扩张的联合 Galois restriction 必须满足共同交域上的兼容性，即落在相应 group fiber product；在适当的生成、有限 Galois 与线性无交条件下，联合 restriction 可以达到更强的乘积分解。

量子系统有一个形式相似但本质不同的 map：

$$
R:
\mathsf S(\mathcal H_A\otimes\mathcal H_B)
\to
\mathsf S(\mathcal H_A)
\times
\mathsf S(\mathcal H_B),
$$

$$
R(\rho)=(\rho_A,\rho_B).
$$

它对任意局部状态对 $(\alpha,\beta)$ 有乘积态扩张 $\alpha\otimes\beta$，故满射；但它不单射，因为纠缠态可共享同一 marginals。

## 原理 129.1

必须分开：

$$
\boxed{
\begin{aligned}
\text{local compatibility}
&=\text{局部对象在重叠处一致},\\
\text{global existence}
&=\text{存在全局对象实现局部数据},\\
\text{global uniqueness}
&=\text{该全局对象由局部数据唯一决定}.
\end{aligned}
}
$$

量子纠缠给出“existence 成立但 uniqueness 失败”的典型局部—全局 fiber。

---

# 130. 平行精化与串行后处理的 kernel 演算

设两个观察接口

$$
q_1:X\to O_1,
\qquad
q_2:X\to O_2.
$$

平行联合

$$
q(x)=(q_1(x),q_2(x))
$$

满足：

$$
\boxed{
\ker q
=
\ker q_1\cap\ker q_2.
}
$$

所以平行增加独立接口只会减少余量。

反之，串行后处理

$$
X\xrightarrow qO\xrightarrow fY
$$

满足：

$$
\boxed{
\ker q
\subseteq
\ker(f\circ q).
}
$$

所以后处理只能保持或扩大不可区分关系。

## 量子对应

平行加入观察者：

$$
V_{1\vee2}=V_1+V_2,
$$

$$
N_{1\vee2}=N_1\cap N_2.
$$

串行 CPTP／经典后处理服从数据处理原则，不可能把已完全相同的上游状态／law 标签再次区分。

## 结论 130.1

“量子技术增强素数观察”只有在它加入新的平行效果、联合上下文或动力生成方向时才可能真正缩小 kernel；如果量子层仅位于一个已经压缩的 arithmetic label 后面，它不能恢复上游丢失信息。

---

# 131. 横向素数与纵向精度在量子化后仍不对称

`FORMAL_PRIME_OBSERVER_DYNAMICS.md` 的核心结构轴是：

$$
\boxed{
\text{different primes = horizontal combination},
}
$$

$$
\boxed{
\text{same prime precision = vertical refinement}.
}
$$

这一结构在量子化后必须保留。

## 横向

不同 prime powers 形成真实张量因子：

$$
\mathcal H_{p^k}\otimes\mathcal H_{q^\ell},
\qquad p\neq q.
$$

它们允许独立局部效果、联合效果、经典相关和纠缠。

## 纵向

同一素数的 residue tower 是粗化链：

$$
\mathbb Z/p^{k+1}\mathbb Z
\to
\mathbb Z/p^k\mathbb Z.
$$

在 outcome 侧是逆系统；在 effect 侧通过拉回形成正向嵌入：

$$
\mathcal A_{p,k}
\hookrightarrow
\mathcal A_{p,k+1}.
$$

因此不同 $k$ 层不是独立张量因子。把它们当成独立子系统会重复计算同一 $p$-进信息。

---

# 132. prime Weyl observer：从 residue 读出升级到相位读出

对

$$
\mathcal H_{p^k}
=
\ell^2(\mathbb Z/p^k\mathbb Z)
$$

定义 clock 与 shift：

$$
Z|x\rangle
=\omega^x|x\rangle,
$$

$$
X|x\rangle
=|x+1\rangle,
$$

其中

$$
\omega=e^{2\pi i/p^k}.
$$

它们满足 Weyl 关系：

$$
\boxed{
ZX=\omega XZ.
}
$$

$Z$ 的谱投影读取 residue／address；Fourier 变换后的 $X$ 上下文读取相位／频率。二者共同生成完整局部矩阵代数。

## 原理 132.1

纯 arithmetic prime observer 对应 clock/residue sector；真正局部完备的 quantum prime observer 至少需要加入与 residue algebra 不共同对角化的相位上下文。

因此可写：

$$
\boxed{
\begin{aligned}
\text{arithmetic prime observer}
&=\text{residue / clock sector},\\
\text{local quantum prime observer}
&=\text{clock + shift + instruments},\\
\text{global quantum prime observer}
&=\text{local sectors + cross-prime correlations}.
\end{aligned}
}
$$

---

# 133. 自适应 prime-quantum 实验

仓库 `D5/S3/ConceptDynamics/ExperimentDesign/ThreeStateAdaptiveEarlyStopping.lean` 已机器核验一个三状态例子：固定两实验 transcript 与自适应 transcript 都保持精确识别，自适应策略最坏深度仍为 $2$，但期望实验数降为

$$
1+2\varepsilon<2
$$

对 $0<\varepsilon<1/2$ 成立。

在 prime-quantum setting 中，将实验动作定义为：

$$
\boxed{
a_t=(p_t,k_t,b_t,\mathcal I_t,\Phi_t).
}
$$

它分别选择 prime、precision、measurement basis/instrument 与动力学准备。

设候选量子状态／通道模型为 $\theta\in\Theta$，历史为 $h_t$，posterior：

$$
\pi_t(\theta)=P(\theta\mid h_t).
$$

一个自适应 policy：

$$
a_t=\pi_{\mathrm{policy}}(\pi_t)
$$

可根据当前剩余 fiber 选择下一个 prime-time experiment，并在满足风险阈值时提前停止。

## 严格边界 133.1

必须区分：

1. 每轮重新制备同一未知态后执行不同 prime-time 测量；
2. 对同一个单量子样本连续执行 instrument。

第二种情况下早期测量改变后续状态，不能用相互独立的静态 Born law 替代 instrument word probability。

---

# 134. 四层 prime-quantum residual tower

合并两套理论后，不应把所有“剩余”压成一个未类型化集合。至少区分：

## 定义 134.1（算术 residual）

$$
N_{\mathrm{arith}}
=
\{(x,y):q_{p,k}(x)=q_{p,k}(y)\ \forall p,k\}.
$$

## 定义 134.2（量子 visibility residual）

$$
N_{\mathrm{quant}}
=
V_{\mathfrak O}^{\perp}.
$$

## 定义 134.3（cross-prime correlation residual）

对只看至多 $m$-prime observables 的观察者：

$$
N_{>m}
=
\bigoplus_{|S|>m}V_S.
$$

## 定义 134.4（sequential protocol residual）

$$
N_{\mathrm{seq}}
=
\left(\operatorname{span}\{F_w:w\text{ allowed}\}\right)^\perp.
$$

如果这些是**平行独立接口**，联合残差由 kernel 交给出；若它们处于**串行压缩管道**中，则必须计算复合接口的 kernel，不能机械写成集合交。

这条 typed-residual discipline 是后续 Lean 统一时必须保持的约束。

---

# 135. prime completion 与 dynamical completion 一般不交换

令

$$
C_{\mathrm{prime}}
$$

表示只闭合所允许的 prime-local effect family，令

$$
C_\Phi
$$

表示在 Heisenberg 动力下闭合全部时间轨道。

若

$$
\Phi^*(\mathcal A_p)
\subseteq
\mathcal A_p
$$

对每个 prime-local algebra 成立，则两种完成在该局部族内相容。

但若 $\Phi$ 含跨素数耦合，则可能出现：

$$
\Phi^*(\mathcal A_p)
\not\subseteq
\mathcal A_p.
$$

时间闭包会生成 cross-prime effects；若每一步又投影回 prime-local 空间，这些新信息会被删除。

## 定义 135.1（cross-prime completion defect）

令

$$
\Pi_{\mathrm{loc}}
$$

为到 $V_{\le1}$ 的 Hilbert–Schmidt 正交投影。定义

$$
\boxed{
\Delta_\Phi(E)
=
\|(I-\Pi_{\mathrm{loc}})\Phi^*(E)\|_{\mathrm{HS}}.
}
$$

若

$$
\Delta_\Phi(E)=0,
$$

该局部效果一步后仍无跨素数部分；若正，则动力学已把局部问题运输出新的相关信息。

## 原理 135.1

一般不能无条件写：

$$
C_\Phi C_{\mathrm{prime}}
=
C_{\mathrm{prime}}C_\Phi.
$$

完成次序本身可以携带信息，这正是原文非交换 reflector 的 prime-quantum 具体实例。

---

# 136. 任务相对 prime-quantum 完成

完整量子态层析通常不是实际任务所需的最小预算。

设目标 observable 子空间为

$$
T\subseteq\operatorname{Herm}_d.
$$

设当前 prime-time 可见空间为

$$
V_{J,m}.
$$

## 定义 136.1（任务完成）

观察者对目标 $T$ 完成，当且仅当

$$
T\subseteq V_{J,m}.
$$

## 定理 136.1（目标预测充分性）

若 $T\subseteq V_{J,m}$，则对任意 $A\in T$，其期望

$$
\operatorname{Tr}(\rho A)
$$

由 prime-time 观察签名唯一决定。

反之，若存在

$$
A\in T\setminus V_{J,m},
$$

则存在迹零残差方向 $D\in V_{J,m}^\perp$ 与 $\operatorname{Tr}(DA)\neq0$，从而可构造两个当前观察不可区分、但目标期望不同的物理状态。

因此 prime-quantum 实验设计应首先问：

$$
\boxed{
\text{which target subspace must be captured?}
}
$$

而不是默认追求所有 $d^2-1$ 个状态自由度。

---

# 137. 当前 Lean 锚点与新桥状态

| 统一结构 | 当前仓库锚点 | 本增订状态 |
|---|---|---|
| finite prime-time separation | `D5/S3/Observer/Refinement/FinitePrimeTimeTomography` | Lean closed；索引是一般 `Nat` |
| prime-power full matrix tensor factorization | `D5/S3/ObserverMemory/PrimePowerTensorTower` | Lean closed |
| Frobenius observer infinite fiber | `D5/S3/Factorization/Galois/GaloisPrimeObserver` | Lean closed |
| Galois restriction fiber-product compatibility | `D5/S3/Factorization/Galois/GaloisFusion` | Lean closed |
| three-ring quadratic-character redundancy | `D5/S3/PrimeForms/Splitting/QuadraticCharacterProfileRedundancy` | Lean closed |
| prime precision entropy contraction | `D5/S3/Analytic/PrimeProducts/PrimePrecisionEntropyContraction` | Lean closed |
| static quantum visible-space theory | 本文件 81–88 | paper-level unified layer |
| Heisenberg finite-horizon theory | 本文件 89–94 | paper-level unified layer |
| local reduced-state boundary | 本文件 99 | paper-level theorem |
| deterministic prime observer → commuting PVM | 本增订 114 | paper-level direct proof |
| quantum prime local-global residual | 本增订 118–120 | paper-level direct proof |
| finite-dimensional quantum prime-time certificate | 本增订 123 | paper-level direct proof |
| zeta-weighted prime-time Gramian | 本增订 124–125 | paper-level / Lean target |
| Frobenius quantum postprocessing no-recovery | 本增订 126 | paper-level factorization theorem |
| completion noncommutation defect | 本增订 135 | definition / research bridge |

已有 Lean 文件只锚定各自实际声明；本表不得解释为新增 prime-quantum 总理论已经全部通过 kernel。

---

# 138. 建议追加 Lean 模块树

```text
D5/S3/Quantum/PrimeObserver/
  DeterministicPrimeObserverEmbedding.lean
  PrimeIndexedEffectFamily.lean
  QuantumPrimeTimeVisibleSpace.lean
  FiniteQuantumPrimeTimeTomography.lean
  ZetaWeightedPrimeTimeGramian.lean

D5/S3/Quantum/PrimeTensor/
  CRTBasisTensorEquiv.lean
  PrimeLocalMarginalMap.lean
  PrimeLocalGlobalResidual.lean
  CorrelationSectorDecomposition.lean
  PrimeCorrelationOrder.lean

D5/S3/Quantum/PrimeDynamics/
  ProductChannelPrimeSupport.lean
  HamiltonianPrimeSupportPropagation.lean
  PrimeCompletionCommutation.lean
  PrimeCompletionDefect.lean

D5/S3/Quantum/GaloisObserver/
  FrobeniusClassQuantumEncoding.lean
  FrobeniusPostprocessingNoRecovery.lean
  QuadraticProfileCommutativeNoGo.lean
  GaloisQuantumLocalGlobalComparison.lean

D5/S3/Quantum/PrimeActive/
  PrimeInstrumentAction.lean
  PrimeBeliefState.lean
  AdaptivePrimeExperiment.lean
  PrimeTaskRelativeCompletion.lean
```

建议优先闭合低依赖定理：

```text
deterministic_readout_pvm
basis_state_prime_kernel_iff
prime_local_marginals_not_injective
correlation_sector_dimension
local_product_channel_preserves_support
quantum_prime_time_has_finite_certificate
frobenius_quantum_postprocessing_kernel_mono
quadratic_profile_postprocessing_no_refinement
task_complete_iff_target_subspace_le_visible
```

随后再闭合：

```text
zeta_prime_precision_weight_sum_one
zeta_weighted_gramian_inner
zeta_weighted_gramian_kernel
prime_completion_defect_zero_iff_local_preserved
```

---

# 139. 追加严格非主张

1. 本增订不声称素数本身是有意识的观察者。
2. 本增订不声称素数产生量子力学或量子随机性。
3. 本增订不声称所有量子系统天然具有 arithmetic prime-power tensor decomposition；这里的分解针对选定 CRT finite-register carrier。
4. 本增订不声称 `PrimePowerTensorTower` 推出任意量子态按素数统计独立。
5. 本增订不声称 CRT residue 数据可以恢复任意量子相位或纠缠。
6. 本增订不声称各单素数 reduced states 决定全局状态。
7. 本增订不声称跨素数相关 residual 必然是物理基本粒子之间的纠缠；它首先是所选张量分解上的算子扇区。
8. 本增订不声称相互作用图连通足以保证完整层析。
9. 本增订不声称局部动力学能通过延长时间自动看到跨素数 correlation sectors。
10. 本增订不声称 `FinitePrimeTimeTomography` 当前 Lean theorem 已把索引限制为真实素数。
11. 本增订不声称 finite quantum prime-time certificate 已有同名 Lean proof term。
12. 本增订不声称 prime precision entropy contraction 是量子退相干定律。
13. 本增订不声称 zeta-weighted Gramian 的 $s$ 参数具有已证明的物理温度、能量或 RH 临界意义。
14. 本增订不声称 $s=1/2$、$s=1$ 或其他特殊值自动对应量子相变。
15. 本增订不声称 Frobenius infinite fiber theorem 等价于 Chebotarev 密度定理。
16. 本增订不声称量子后处理可以恢复已经由 Frobenius quotient 删除的 prime identity。
17. 本增订不声称 three-ring quadratic profile 是完整 mod-$60$ 身份接口；现有 Lean theorem 反而证明其 fiber 大小为二。
18. 本增订不声称增加任意数量的二次 character 可以打破现有三环 fiber。
19. 本增订不声称 Galois fiber product 与量子 marginal fiber 是同一个数学对象；它们只共享局部—全局 compatibility/existence/uniqueness 的组织问题。
20. 本增订不声称不同 prime precision 层是独立量子子系统。
21. 本增订不声称 Weyl clock/shift 结构本身是新物理定律。
22. 本增订不声称 adaptive prime experiment 必然优于所有静态方案；优势依赖 prior、cost、loss 与实验模型。
23. 本增订不声称后验 belief 可在单样本未知态问题中绕过不可克隆或状态扰动。
24. 本增订不声称所有 residual 可以不分类型地取交；串行接口必须计算复合 kernel。
25. 本增订不修改此前关于对角逃逸、意识、自由意志、RH、negative-base-$\varphi$ 或其他开放问题的严格边界。

---

# 140. 最终统一：素数给局部坐标，量子给非交换可见性，时间给相关运输

把本增订压缩为一个统一 prime-quantum observer：

$$
\boxed{
\mathfrak O_{\mathbb P,Q}
=
\left(
\mathcal H,
\{\mathcal H_{p^k}\},
\{E_{p,k,b,a}\},
\{\mathcal I_{p,k,b,a}\},
\Phi,
\mathcal A_M
\right).
}
$$

其静态／动态可见空间为：

$$
V_{J,T}
=
\operatorname{span}_{\mathbb R}
\left\{
I,
(\Phi^*)^t(E_i):
i\in J,\ 0\le t<T
\right\},
$$

不可见 residual 为：

$$
N_{J,T}=V_{J,T}^\perp.
$$

在 CRT finite-register 模型中：

$$
\boxed{
\text{prime powers}
\longrightarrow
\text{tensor factors},
}
$$

但：

$$
\boxed{
\text{local marginals}
\not\Rightarrow
\text{global state},
}
$$

因为遗漏的是：

$$
\boxed{
\text{cross-prime correlation sectors}.
}
$$

纯 residue 观察读取交换对角代数；Weyl 相位上下文补入局部非交换方向；跨 prime coupling 或联合 effects 才能访问高阶相关扇区。时间的作用因此不是简单“多等一会儿”，而可以是：

$$
\boxed{
\text{transport hidden correlation directions into measurable effect directions}.
}
$$

Frobenius 与二次角色结果提供另一条严格边界：

$$
\boxed{
\text{once a prime identity difference is quotiented out by a coarse arithmetic label,}
\text{downstream quantum processing cannot recreate it}.
}
$$

所以最深的统一不是“素数 = 量子”，而是：

$$
\boxed{
\begin{aligned}
\text{prime structure}
&=\text{where local questions are indexed and factored},\\
\text{quantum structure}
&=\text{which state differences those questions can reveal},\\
\text{correlation structure}
&=\text{what remains invisible to all local prime marginals},\\
\text{dynamics}
&=\text{which invisible directions can later enter the visible span},\\
\text{completion}
&=\text{the minimal finite protocol whose effects capture the required target space}.
\end{aligned}
}
$$

因此：

$$
\boxed{
经典 CRT 说明局部素数坐标可以恢复离散基标签；
量子局部—全局余量说明，同样的局部坐标并不足以恢复振幅之间的相位、相关与纠缠。
}
$$

这正是素数观察者理论进入量子层后新增的核心结构：

$$
\boxed{
\text{local arithmetic coordinates}
+
\text{noncommutative measurement contexts}
+
\text{cross-prime correlations}
+
\text{prime-time dynamical completion}.
}
$$
# 继续：统一观察者演算的闭合形式

前面的推导已经把各种观察者压缩到了同一个核心：

$$
\boxed{
K_{\mathfrak O}
=
\bigcap_{\pi\in\mathsf{Prot}_{\mathfrak O}}
\ker \mathcal L_\pi
}
$$

其中：

* \(X\) 是隐藏世界、模型、状态或历史；
* \(\pi\) 是允许执行的协议；
* \(\mathcal L_\pi(x)\) 是协议在状态 \(x\) 上产生的结果 law；
* \(K_{\mathfrak O}\) 是所有允许协议都无法区分的状态关系。

现在继续把它闭合成一套完整的**统一观察者理论**。

---

# 168. 统一观察者表示定理

定义一个类型化协议观察者：

$$
\mathfrak O
=
\left(
X,\mathsf{Prot},\mathsf{Out},\mathcal L
\right),
$$

其中：

$$
\mathcal L_\pi:
X\to
\mathsf{Law}(\mathsf{Out}(\pi)).
$$

定义完整行为签名：

$$
\Sigma_{\mathfrak O}(x)
=
\left(
\mathcal L_\pi(x)
\right)_{\pi\in\mathsf{Prot}}.
$$

定义：

$$
K_{\mathfrak O}
=
\ker\Sigma_{\mathfrak O}.
$$

## 定理 168.1（统一观察者表示）

存在规范等价：

$$
\boxed{
X/K_{\mathfrak O}
\cong
\operatorname{range}\Sigma_{\mathfrak O}.
}
$$

而且，对任意其他接口：

$$
r:X\to R,
$$

以下三个条件等价。

### 条件一：协议充分性

所有协议 law 都通过 \(r\) 因子化：

$$
\forall\pi,\quad
\exists \overline{\mathcal L}_\pi,
\qquad
\mathcal L_\pi
=
\overline{\mathcal L}_\pi\circ r.
$$

### 条件二：kernel 包含

$$
\boxed{
K_r\subseteq K_{\mathfrak O}.
}
$$

### 条件三：规范因子化

存在唯一映射：

$$
\bar r:
\operatorname{range}r
\to
\operatorname{range}\Sigma_{\mathfrak O}
$$

使：

$$
\Sigma_{\mathfrak O}
=
\bar r\circ r
$$

在 \(r\) 的有效像上成立。

## 证明

若所有协议都通过 \(r\) 因子化，则：

$$
r(x)=r(y)
$$

必然推出：

$$
\mathcal L_\pi(x)=\mathcal L_\pi(y)
\qquad
\forall\pi.
$$

故：

$$
K_r\subseteq K_{\mathfrak O}.
$$

反过来，若 kernel 包含成立，定义：

$$
\bar r(r(x))
=
\Sigma_{\mathfrak O}(x).
$$

若：

$$
r(x)=r(y),
$$

则：

$$
(x,y)\in K_r\subseteq K_{\mathfrak O},
$$

所以：

$$
\Sigma_{\mathfrak O}(x)
=
\Sigma_{\mathfrak O}(y).
$$

故定义与代表元无关。

唯一性来自 \(r\) 对其有效像的满射性。证毕。

仓库的 `CompletionCriterion` 已经机器核验了其中最底层的 kernel quotient—realized range 等价，以及“商等于完整形式余域”等价于观察映射满射。

---

# 169. 最小行为实现：观察者的 Nerode 型商

定理 168.1 表明：

$$
Q_{\mathfrak O}
=
X/K_{\mathfrak O}
$$

并不是任意压缩，而是所有能够预测完整协议行为的接口中**最粗的一个**。

设一个实现状态空间：

$$
S
$$

带有编码：

$$
e:X\to S,
$$

并且从 \(e(x)\) 可以恢复全部协议 law。

那么必存在唯一满射：

$$
\boxed{
S_{\mathrm{reachable}}
\longrightarrow
Q_{\mathfrak O}.
}
$$

因此：

$$
\boxed{
Q_{\mathfrak O}
=
\text{保持全部允许未来行为的最小状态实现}.
}
$$

这同时统一了：

* 动态系统的未来 itinerary 商；
* 自动机的行为等价状态；
* 概率系统的预测状态；
* 量子系统的操作等价态；
* 素数系统的完整局部画像；
* 历史系统的 belief state；
* 行动系统的策略充分自我。

仓库已经对有限 itinerary 给出极强实例：kernel 商、完整 itinerary 的实际像及兼容有限前缀逆极限彼此等价，并且在有限状态空间中存在有限 completion depth。

---

# 170. 观察者格：所有观察者构成同一个精化偏序

固定隐藏空间 \(X\)。

把 kernel 相同的观察接口视为同一个观察者。定义精化：

$$
\mathfrak O_1
\preceq
\mathfrak O_2
$$

当且仅当 \(\mathfrak O_2\) 至少能区分 \(\mathfrak O_1\) 能区分的一切：

$$
\boxed{
K_{\mathfrak O_2}
\subseteq
K_{\mathfrak O_1}.
}
$$

若允许任意 quotient 接口，则观察者等价类与 \(X\) 上的等价关系反序对应。

## 170.1 联合观察者是 join

联合观察签名：

$$
\Sigma_{\mathfrak O_1\vee\mathfrak O_2}(x)
=
\left(
\Sigma_{\mathfrak O_1}(x),
\Sigma_{\mathfrak O_2}(x)
\right).
$$

于是：

$$
\boxed{
K_{\mathfrak O_1\vee\mathfrak O_2}
=
K_{\mathfrak O_1}
\cap
K_{\mathfrak O_2}.
}
$$

## 170.2 共同粗化是 meet

两个观察者的最细共同粗化，对应包含：

$$
K_{\mathfrak O_1}\cup K_{\mathfrak O_2}
$$

的最小等价关系：

$$
\boxed{
K_{\mathfrak O_1\wedge\mathfrak O_2}
=
\operatorname{EqClosure}
\left(
K_{\mathfrak O_1}\cup
K_{\mathfrak O_2}
\right).
}
$$

所以：

$$
\boxed{
\text{观察者格}
\cong
\text{状态分割格的反序}.
}
$$

仓库的 pullback algebra 结果已经机器核验了相应的三重对偶：

$$
\boxed{
\text{观察精化}
\iff
\text{反向 kernel 包含}
\iff
\text{可观察函数代数包含}.
}
$$

---

# 171. 观察函数—状态关系的统一 Galois connection

对状态关系：

$$
R\subseteq X^2,
$$

定义所有在 \(R\) 上常值的目标：

$$
\operatorname{Obs}(R)
=
\left\{
f:
xRy\Rightarrow f(x)=f(y)
\right\}.
$$

对函数族：

$$
\mathcal F,
$$

定义共同 kernel：

$$
\operatorname{Ker}(\mathcal F)
=
\bigcap_{f\in\mathcal F}\ker f.
$$

则有：

$$
\boxed{
\mathcal F\subseteq\operatorname{Obs}(R)
\iff
R\subseteq\operatorname{Ker}(\mathcal F).
}
$$

这产生一个反序 Galois connection。

于是完整观察函数闭包为：

$$
\boxed{
\overline{\mathcal F}
=
\operatorname{Obs}
\left(
\operatorname{Ker}(\mathcal F)
\right).
}
$$

含义是：

> 从当前观察函数族中逻辑上能够恢复的全部函数。

对于接口 \(q\)，这就是：

$$
\overline{\{q\}}
=
\{f:f\text{ factors through }q\}.
$$

仓库进一步证明，这个 pullback algebra 的最小非空事件，恰好是实际观察纤维。

因此：

$$
\boxed{
\text{状态纤维}
=
\text{观察事件代数的原子}.
}
$$

这说明状态侧的 partition 和命题侧的 observable algebra 不是两套理论，而是完全反对偶的两种坐标。

---

# 172. 协议闭包是观察者反射

设初始观察函数族为：

$$
\mathcal F_0.
$$

设允许动作、动力或仪器生成一个协议幺半群／自由范畴：

$$
\mathcal P.
$$

对每个协议 \(w\)，状态演化为：

$$
T_w.
$$

确定性情况下定义：

$$
T_w^*f
=
f\circ T_w.
$$

定义协议闭包：

$$
\boxed{
\mathcal F_\infty
=
\operatorname{Closure}
\left\{
T_w^*f:
w\in\mathcal P,\ f\in\mathcal F_0
\right\}.
}
$$

其共同 kernel 为：

$$
K_\infty
=
\bigcap_{w,f}
\ker(T_w^*f).
$$

## 定理 172.1（最大不变 residual）

\(K_\infty\) 是包含于初始 kernel：

$$
K_0
=
\operatorname{Ker}(\mathcal F_0)
$$

中的最大协议不变等价关系。

即：

$$
K_\infty\subseteq K_0,
$$

且：

$$
xK_\infty y
\Rightarrow
T_wxK_\infty T_wy
\quad
\forall w.
$$

若另一个关系 \(R\subseteq K_0\) 对所有协议稳定，则：

$$
R\subseteq K_\infty.
$$

## 证明

若 \(xK_\infty y\)，则对任意 \(u,w,f\)：

$$
f(T_uT_wx)
=
f(T_uT_wy),
$$

故：

$$
T_wxK_\infty T_wy.
$$

若 \(R\subseteq K_0\) 且 \(R\) 不变，则：

$$
xRy
\Rightarrow
T_wxRT_wy
\Rightarrow
f(T_wx)=f(T_wy).
$$

因此 \(R\subseteq K_\infty\)。证毕。

所以：

$$
\boxed{
\text{observer completion}
=
\text{dual probes 的最小不变闭包}
=
\text{state residual 的最大不变子关系}.
}
$$

---

# 173. 确定性、概率与量子观察是同一反变原理的三个富化层

## 173.1 集合层

$$
T:X\to X,
\qquad
T^*f=f\circ T.
$$

## 173.2 概率层

若 \(K\) 是 Markov kernel，则：

$$
K^*f(x)
=
\int f(y)\,K(x,dy).
$$

它把未来可观测量拉回当前状态。

## 173.3 量子层

若 \(\Phi\) 是量子通道：

$$
\operatorname{Tr}(\Phi(\rho)E)
=
\operatorname{Tr}(\rho\Phi^*(E)).
$$

若 \(\mathcal I_a\) 是 instrument 分支，协议词 \(w\) 的 word effect 为：

$$
F_w
=
\mathcal I_{w_1}^*
\cdots
\mathcal I_{w_n}^*(I).
$$

于是：

$$
P(w\mid\rho)
=
\operatorname{Tr}(\rho F_w).
$$

完整可见空间：

$$
V_\infty
=
\operatorname{span}_{\mathbb R}
\{F_w:w\in\mathcal P\}.
$$

不可见 residual：

$$
\boxed{
N_\infty
=
V_\infty^\perp.
}
$$

因此三种理论共享同一结构：

$$
\boxed{
\begin{aligned}
\text{state evolution}
&:\text{covariant};\\
\text{observable propagation}
&:\text{contravariant};\\
\text{observer completion}
&:\text{least invariant dual closure};\\
\text{hidden residual}
&:\text{annihilator of that closure}.
\end{aligned}
}
$$

量子理论的特殊性不是 kernel 逻辑改变了，而是 dual probe 空间变成了非交换 operator system。

---

# 174. 目标完成是所有知识、预测、因果与策略完成的共同母式

设目标族：

$$
\mathcal T
=
\{T_\alpha:X\to Y_\alpha\}.
$$

定义：

$$
K_{\mathcal T}
=
\bigcap_\alpha\ker T_\alpha.
$$

给定当前接口：

$$
q:X\to Q,
$$

定义：

$$
C_{\mathcal T}(q)(x)
=
\left(
q(x),
(T_\alpha(x))_\alpha
\right).
$$

则：

$$
\boxed{
K_{C_{\mathcal T}(q)}
=
K_q\cap K_{\mathcal T}.
}
$$

## 定理 174.1（最小目标充分完成）

\(C_{\mathcal T}(q)\) 是所有同时：

* 精化 \(q\)；
* 决定全部目标 \(T_\alpha\)；

的接口中的最粗者。

由此：

$$
\boxed{
\begin{aligned}
\text{knowledge completion}
&=\text{加入事实值目标};\\
\text{prediction completion}
&=\text{加入未来 law};\\
\text{causal completion}
&=\text{加入全部干预响应};\\
\text{quantum completion}
&=\text{加入全部 word effects};\\
\text{prime completion}
&=\text{加入全部 }(p,k,t)\text{ 读出};\\
\text{agency completion}
&=\text{加入未来策略画像};\\
\text{self completion}
&=\text{加入仍会改变未来选择的历史差异}.
\end{aligned}
}
$$

所以项目中的大量 completion 并不是不同运算，而是同一个：

$$
C_{\mathcal T}
$$

在不同目标族上的实例。

---

# 175. Posterior、未来行为状态与 self 的严格层级

设历史空间为：

$$
\mathcal H.
$$

posterior：

$$
\pi:
\mathcal H\to\mathsf{Prob}(\Theta).
$$

完整未来实验行为：

$$
\Sigma_{\mathrm{fut}}:
\mathcal H\to B_{\mathrm{fut}}.
$$

策略画像：

$$
\Sigma_{\mathrm{act}}:
\mathcal H\to B_{\mathrm{act}}.
$$

仓库已证明：在 Bayes update 与 kernel 一致时，相同 posterior 保证所有 belief-adaptive 有限未来输出 law 以及递归 Bayes continuation value 相同。

更一般的可测版本证明，相同 belief 对任意未来 policy 和任意 Bayes 决策问题产生相同最优值。

因此存在因子：

$$
F:
\operatorname{range}\pi
\to
B_{\mathrm{fut}}
$$

满足：

$$
\Sigma_{\mathrm{fut}}
=
F\circ\pi.
$$

所以：

$$
\boxed{
K_\pi
\subseteq
K_{\mathrm{fut}}.
}
$$

若策略进一步只依赖 posterior：

$$
\Sigma_{\mathrm{act}}
=
G\circ\pi,
$$

则：

$$
\boxed{
K_\pi
\subseteq
K_{\mathrm{act}}.
}
$$

于是形成：

$$
\boxed{
\mathcal H
\xrightarrow{\pi}
\operatorname{range}\pi
\twoheadrightarrow
Q_{\mathrm{fut}}
\twoheadrightarrow
M_{\mathrm{self}}.
}
$$

其中：

$$
Q_{\mathrm{fut}}
=
\mathcal H/K_{\mathrm{fut}},
$$

$$
M_{\mathrm{self}}
=
\mathcal H/K_{\mathrm{act}}.
$$

这带来两个重要结论。

## 175.1 Posterior 充分不等于最小

posterior 最小，当且仅当：

$$
F
$$

在 posterior 有效像上单射。

不同 posterior 若对全部允许未来实验都产生相同 law，则它们应在最小行为状态中继续被合并。

## 175.2 Self 不是完整 belief

self 只保留 belief／history 中会改变未来策略的部分：

$$
\boxed{
\text{self}
=
\text{policy-relevant quotient of belief and history}.
}
$$

因此：

$$
\boxed{
\text{world}
\neq
\text{belief}
\neq
\text{predictive state}
\neq
\text{self}.
}
$$

---

# 176. 记忆不是一个对象，而是四种不同关系

统一理论要求严格区分：

## 存储

事件是否仍存在于 ledger、环境或物理介质。

## 访问

当前 readout 是否可以恢复该记录。

## 知识

目标值是否在当前观察纤维上常值：

$$
K_{q_t}
\subseteq
K_f.
$$

## 未来效力

当前被合并的差异是否会在未来改变：

* 读出；
* 预测；
* 决策；
* 策略。

线性系统中，若当前读出为 \(C\)，完整未来不可见空间为 \(N_\infty\)，则：

$$
\boxed{
M_{\mathrm{pred}}
=
\ker C/N_\infty
}
$$

表示“当前不可见、但未来会产生观察差异”的记忆坐标。

于是：

$$
\boxed{
\text{stored}
\neq
\text{accessible}
\neq
\text{known}
\neq
\text{future-relevant}.
}
$$

仓库的 `TwoTimeKnowledge` 已明确证明：事件可以在完整 ledger 中持续存在，但后期 readout 变粗后，事件值不再在读出纤维上常值，于是发生真正的语义遗忘。

---

# 177. 自我报告不能放大内部观察能力

设世界状态为：

$$
X.
$$

内部自我接口：

$$
q:X\to M.
$$

自我报告：

$$
r:M\to R.
$$

报告接口是：

$$
r\circ q:X\to R.
$$

由串行 kernel 法则：

$$
\boxed{
K_q
\subseteq
K_{r\circ q}.
}
$$

因此：

$$
\boxed{
\text{仅靠对内部状态继续描述、压缩或递归命名，}
\text{不能恢复内部接口已丢失的世界差异}.
}
$$

这可以称为：

$$
\boxed{
\text{self-report no-amplification theorem}.
}
$$

它不声称内部观察者永远无法增长知识。增长可以来自：

* 新的外部传感器；
* 新的干预；
* 时间动力把隐藏信息带入可见面；
* 新的记录访问；
* 多观察者联合；
* 新的量子上下文。

但单纯：

$$
M\to R
$$

的后处理不能增加区分力。

---

# 178. 并行—串行二元律

观察理论的所有信息变化都可以先用两条法则审计。

## 并行加入

$$
\Sigma(x)
=
(\Sigma_1(x),\Sigma_2(x))
$$

给出：

$$
\boxed{
K_\Sigma
=
K_{\Sigma_1}\cap K_{\Sigma_2}.
}
$$

## 串行后处理

$$
X\xrightarrow{\Sigma}B\xrightarrow{f}C
$$

给出：

$$
\boxed{
K_\Sigma
\subseteq
K_{f\circ\Sigma}.
}
$$

## 精确无损判据

串行后处理保持 kernel：

$$
K_{f\circ\Sigma}
=
K_\Sigma
$$

当且仅当 \(f\) 在实际像：

$$
\operatorname{range}\Sigma
$$

上单射。

所以：

$$
\boxed{
\text{后处理无损}
\iff
\text{后处理在实际行为像上可逆}.
}
$$

但这只是集合层无损。若要求恢复映射还必须是：

* 连续；
* 可测；
* 仿射；
* 随机通道；
* 完全正量子通道；

则还需要相应的结构化左逆。

这严格区分：

$$
\boxed{
\text{semantic injectivity}
\neq
\text{physical recoverability}.
}
$$

---

# 179. 观察 atlas 的局部—全局统一定理

设局部观察空间为：

$$
B_i,
\qquad i\in I,
$$

并有兼容限制映射。

令兼容族空间：

$$
L_{\mathrm{loc}}
=
\varprojlim_iB_i.
$$

全局对象产生：

$$
\Sigma_{\mathrm{loc}}:
X\to L_{\mathrm{loc}}.
$$

## 定理 179.1（观察 atlas 分解）

最强局部—全局完整性：

$$
\Sigma_{\mathrm{loc}}
\text{ 是双射}
$$

等价于以下两个条件同时成立。

### 分离性

$$
\boxed{
K_{\Sigma_{\mathrm{loc}}}
=
\Delta_X.
}
$$

局部数据唯一决定全局对象。

### 胶合性

$$
\boxed{
\operatorname{range}\Sigma_{\mathrm{loc}}
=
L_{\mathrm{loc}}.
}
$$

每个兼容局部族都由某个全局对象实现。

因此：

$$
\boxed{
\text{local–global exactness}
=
\text{uniqueness}
+
\text{existence}.
}
$$

这两者逻辑独立。

* 量子局部边缘可以不唯一决定全局纠缠态；
* 某些形式局部 law 族可能根本不存在联合全局状态；
* 素数局部画像可能留下全局类余量；
* 兼容有限前缀在某些系统中可能没有全局无限实现。

仓库当前已经把局部—全局谓词完整性表达为正、负缺陷集合同时为空。

---

# 180. Prime observer 是一个多轴观察 atlas

素数观察者的自然索引不是单一素数，而是：

$$
\boxed{
(S,(k_p)_{p\in S},t,c)
}
$$

其中：

* \(S\subset_{\mathrm{fin}}\mathbb P\)：联合观察的素数集合；
* \(k_p\)：第 \(p\) 个方向的精度；
* \(t\)：时间；
* \(c\)：测量上下文、干预或 instrument。

这四个方向分别对应：

$$
\begin{aligned}
S
&:\text{横向 locality / correlation order};\\
k_p
&:\text{纵向 }p\text{-进精化};\\
t
&:\text{动力学 completion};\\
c
&:\text{观察／干预／量子上下文}.
\end{aligned}
$$

因此完整素数观察签名应写成：

$$
\Sigma_{\mathrm{prime}}(x)
=
\left(
\mathcal L_{S,k,t,c}(x)
\right)_{S,k,t,c}.
$$

普通单素数读出只是：

$$
|S|=1
$$

的截面。

跨素数量子相关位于：

$$
|S|\ge2
$$

的扇区。

所以项目中的素数观察、CRT、prime-power tensor、Frobenius、分裂画像和时间层析，实际上都是同一个 local atlas 在不同子索引范畴上的限制。

---

# 181. 观察深度的目标相对信息下界

设目标：

$$
T:X\to Z.
$$

真正需要区分的对象数为：

$$
N_T
=
|\operatorname{range}T|.
$$

设每次实验最多返回 \(B\) 个答案，协议最坏深度为 \(h\)。

深度 \(h\) 的确定性 \(B\)-叉决策树最多产生：

$$
B^h
$$

个叶 transcript。

若协议可以零错误恢复 \(T(x)\)，则不同目标值必须对应可区分的 transcript，故：

$$
\boxed{
N_T\le B^h.
}
$$

因此：

$$
\boxed{
h
\ge
\operatorname{clog}_B N_T.
}
$$

仓库目前已对完整状态识别形式化：

$$
\operatorname{clog}_B|X|
\le
h,
$$

并证明该下界在完整 transcript 状态族上可达到。

仓库还证明，允许自适应提前停止并不能突破最坏深度下界；它只可能改变平均代价，一个单实验仍最多具有 \(B\) 个实际输出。

---

# 182. 新推论：平均观察深度的熵下界

上一节是最坏情形界。统一协议理论还能推出平均情形界。

设目标随机变量为：

$$
Z=T(X)
$$

并具有先验分布。

设一个零错误自适应 \(B\)-叉协议在随机停止时间 \(\tau\) 终止，其叶 transcript 为 \(W\)。

因为协议能从 \(W\) 唯一恢复 \(Z\)：

$$
H(Z\mid W)=0.
$$

所以：

$$
H(Z)\le H(W).
$$

而 \(B\)-叉前缀树的叶编码满足：

$$
H(W)
\le
\mathbb E[\tau]\log B.
$$

因此：

$$
\boxed{
\mathbb E[\tau]
\ge
\frac{H(Z)}{\log B}.
}
$$

这说明：

$$
\boxed{
\text{自适应策略可以靠先验不均匀降低平均深度，}
\text{但不能低于目标熵所要求的平均信息预算}.
}
$$

若允许错误概率 \(\varepsilon\)，结合 Fano 型界可得到：

$$
\boxed{
\mathbb E[\tau]\log B
\ge
H(Z)
-
h_2(\varepsilon)
-
\varepsilon\log(|Z|-1).
}
$$

这会自然连接仓库已有的：

* worst-case depth；
* adaptive early stopping；
* posterior；
* mutual information；
* Bayes risk；

形成一个统一的**观察编码定理**。

该平均深度结论目前是 paper-level 推论，不应在建立相应 prefix-code 与随机停止形式化前标记为 Lean-closed。

---

# 183. 统一加权 Gram 定理

对有限维状态差空间 \(V\)，设每个协议 \(\pi\) 给出线性读出：

$$
C_\pi:V\to Y_\pi.
$$

取严格正权重：

$$
w_\pi>0.
$$

定义观察 Gram 算子：

$$
\boxed{
W_{\mathfrak O}
=
\sum_{\pi}
w_\pi C_\pi^*C_\pi.
}
$$

若求和收敛，则对任意状态差 \(v\)：

$$
\boxed{
\langle v,W_{\mathfrak O}v\rangle
=
\sum_\pi
w_\pi\|C_\pi v\|^2.
}
$$

因此：

$$
\boxed{
\ker W_{\mathfrak O}
=
\bigcap_\pi\ker C_\pi.
}
$$

## 解释

同一个定理产生：

* 线性系统 observability Gramian；
* 量子效果 frame operator；
* prime-time 加权 Gramian；
* zeta-weighted prime-precision Gramian；
* 参数模型 Fisher 信息矩阵；
* 局部层析的条件数；
* 实验设计中的最弱可见方向。

所以：

$$
\boxed{
\text{Gramian}
=
\text{观察 kernel 的二次型量化}.
}
$$

最小正特征值：

$$
\lambda_{\min}^+(W_{\mathfrak O})
$$

不是额外装饰，而是最难观察方向的统计稳定度。

这解释了为什么：

$$
K_{\mathfrak O}=\Delta
$$

仍远远不够。kernel 可以已经消失，但：

$$
\lambda_{\min}
\approx0
$$

时，有限噪声下仍几乎不可识别。

---

# 184. 完整性不应再使用单一布尔值

一个观察者至少需要六个独立状态字段。

$$
\boxed{
\operatorname{Status}(\mathfrak O)
=
\left(
S_{\mathrm{sep}},
S_{\mathrm{img}},
S_{\mathrm{dyn}},
S_{\mathrm{task}},
S_{\mathrm{stat}},
S_{\mathrm{rec}}
\right).
}
$$

其中：

## 分离完备

$$
S_{\mathrm{sep}}
:
K_{\mathfrak O}=\Delta_X.
$$

## 实现完备

$$
S_{\mathrm{img}}
:
\operatorname{Im}\Sigma=L_{\mathrm{formal}}.
$$

## 动力完备

$$
S_{\mathrm{dyn}}
:
K_{\mathfrak O}
\text{ 对全部允许更新为 congruence}.
$$

## 任务完备

$$
S_{\mathrm{task}}
:
K_{\mathfrak O}\subseteq K_{\mathcal T}.
$$

## 统计完备

具有有限样本、一致性、误差率或正 Gram 下界。

## 记录完备

结果可以稳定写入、检索、共享并进入未来更新。

因此不能再无类型地写：

$$
\text{ObserverComplete}.
$$

应写成：

$$
\operatorname{Separated},
\quad
\operatorname{RealizationComplete},
\quad
\operatorname{DynamicallyClosed},
\quad
\operatorname{SufficientFor}(T),
\quad
\operatorname{StatisticallyStable},
\quad
\operatorname{RecordClosed}.
$$

---

# 185. 统一 residual 类型系统

观察者余量也不应只使用一个 `Residual`。

## 185.1 Identity residual

$$
\operatorname{IdRes}
=
K_{\mathfrak O}\setminus\Delta_X.
$$

## 185.2 Target residual

$$
\operatorname{TargetRes}
=
K_{\mathfrak O}\setminus K_{\mathcal T}.
$$

## 185.3 Dynamic residual

$$
\operatorname{DynRes}
=
\left\{
(x,y)\in K_{\mathfrak O}:
(F_ax,F_ay)\notin K_{\mathfrak O}
\right\}.
$$

## 185.4 Image residual

$$
\operatorname{ImageRes}
=
L_{\mathrm{formal}}
\setminus
\operatorname{Im}\Sigma.
$$

## 185.5 Gluing residual

兼容局部记录无法产生全局实现，或同一局部族具有多个全局实现。

## 185.6 Metric residual

kernel 已经为零，但最小分离值、谱隙或证据率趋近零。

## 185.7 Budget residual

在给定深度、精度、成本或样本数内仍无法消除的区分。

## 185.8 Memory residual

当前未编码但会影响未来观察的历史差异。

## 185.9 Agency residual

当前 self interface 合并了未来策略不同的历史。

完整审计向量应写为：

$$
\boxed{
\mathcal R(\mathfrak O)
=
\left(
R_{\mathrm{id}},
R_T,
R_{\mathrm{dyn}},
R_{\mathrm{img}},
R_{\mathrm{glue}},
R_{\mathrm{metric}},
R_{\mathrm{budget}},
R_{\mathrm{memory}},
R_{\mathrm{agency}}
\right).
}
$$

这比用一个未经定义的“信息逃逸率”覆盖所有缺陷严格得多。

---

# 186. Completion 算子的公共固定点

设：

$$
C_1,\ldots,C_m
$$

分别表示：

* 时间 completion；
* 干预 completion；
* 素数 completion；
* 量子上下文 completion；
* 记录 completion；
* belief completion；
* agency completion。

每个 \(C_i\) 都可以是观察者精化格上的 closure operator：

$$
q\preceq C_i(q),
$$

$$
q\preceq r
\Rightarrow
C_i(q)\preceq C_i(r),
$$

$$
C_i(C_i(q))
\simeq
C_i(q).
$$

但一般：

$$
C_iC_j
\neq
C_jC_i.
$$

因此不能任意各执行一次就宣称获得“总完成”。

## 定义 186.1（统一完成）

统一观察者完成应是满足：

$$
C_i(q^*)\simeq q^*
\qquad
\forall i
$$

的最小共同固定点：

$$
\boxed{
q^*
=
\operatorname{lfp}
\left(
q\mapsto
\bigvee_iC_i(q)
\right).
}
$$

若观察者精化格具有有限高度，则迭代：

$$
q_{n+1}
=
\bigvee_iC_i(q_n)
$$

必在有限步稳定。

若无限维或无限状态，则可能需要：

* 极限阶段 join；
* 超限迭代；
* 拓扑闭包；
* 强／弱算子极限；
* 可测 completion。

这把仓库中的 cascade completion、inverse-limit descent、transfinite residual 和非交换协议 completion 放到同一固定点框架中。

---

# 187. Noetherian observer principle

前面所有有限化结果有一个共同根源。

## 原理

若观察者精化链所在的偏序具有有限高度或 ascending-chain condition，则任何由逐步加入协议产生的 completion 都会有限停止。

## 有限集合实例

观察 partition 的类数至多为：

$$
|X|.
$$

每次严格精化至少增加一个类，因此严格增长次数有限。

仓库已经证明有限观察历史逐步细化并在有限深度达到无限未来关系，同时给出稳定深度与类数增长的界。

## 有限维线性实例

可见子空间维数至多：

$$
d.
$$

每次严格增长至少增加一维。

## 量子实例

迹零 Hermitian 空间维数：

$$
d^2-1.
$$

因此全部 word effects 若最终完备，存在至多：

$$
d^2-1
$$

个独立中心化效果证书。

## 任意观察族在有限状态上的实例

若无限观察族联合忠实，则有限状态对集合使其可以抽取有限忠实子族。仓库已经机器核验这个结果。

所以：

$$
\boxed{
\text{finite witness}
\text{ 的真正来源是 observer lattice 的有限高度，}
\text{而不只是“对象数量有限”}.
}
$$

---

# 188. 观察者不是现实创造者，而是现实商的生成器

完整世界状态可能是：

$$
x\in X.
$$

观察者拥有协议族：

$$
\mathsf{Prot}_{\mathfrak O}.
$$

它实际建立的是：

$$
[x]_{\mathfrak O}
\in
X/K_{\mathfrak O}.
$$

因此观察者并不通过观察“创造 \(x\)”；它通过协议决定：

$$
\boxed{
\text{哪些世界差异在自己的操作语言中仍然存在}.
}
$$

换言之：

$$
\boxed{
\text{观察者不创造世界状态，}
\quad
\text{观察者生成一个世界状态的操作商}.
}
$$

不同观察者可能拥有不同 quotient：

$$
X/K_{\mathfrak O_1},
\qquad
X/K_{\mathfrak O_2}.
$$

这并不意味着存在两个互相矛盾的世界，而是意味着它们保留不同的区分结构。

当二者交换记录时，联合观察者对应：

$$
K_{\mathfrak O_1}
\cap
K_{\mathfrak O_2}.
$$

---

# 189. 观察者、知识、记忆与自我的最终字典

$$
\boxed{
\begin{aligned}
\text{World}
&=X;\\[1mm]
\text{Protocol}
&=\pi;\\[1mm]
\text{Observation law}
&=\mathcal L_\pi(x);\\[1mm]
\text{Behavior signature}
&=\Sigma_{\mathfrak O}(x);\\[1mm]
\text{Observer equivalence}
&=\ker\Sigma_{\mathfrak O};\\[1mm]
\text{Observer reality}
&=X/\ker\Sigma_{\mathfrak O};\\[1mm]
\text{Realized records}
&=\operatorname{Im}\Sigma_{\mathfrak O};\\[1mm]
\text{Knowledge}
&=\text{目标在观察纤维上常值};\\[1mm]
\text{Memory}
&=\text{会改变未来行为的历史区分};\\[1mm]
\text{Belief}
&=\text{隐藏状态的条件分布};\\[1mm]
\text{Predictive state}
&=\text{保持全部未来 law 的最小历史商};\\[1mm]
\text{Self}
&=\text{保持全部未来策略画像的最小历史商};\\[1mm]
\text{Agency}
&=\text{从 self quotient 到合法动作丛的策略截面};\\[1mm]
\text{Classical fact}
&=\text{稳定、可访问、可广播的记录中心};\\[1mm]
\text{Quantum observer}
&=\text{非交换 instrument 协议的实现};\\[1mm]
\text{Prime observer}
&=\text{以素数、精度、时间和局部集合索引的观察 atlas}.
\end{aligned}
}
$$

---

# 190. 统一理论的最深新结论

## 结论一：观察者是 quotient–limit 桥

$$
\boxed{
\frac{\text{world states}}
{\text{protocol indistinguishability}}
\cong
\text{realized compatible record families}
\subseteq
\text{formal record limit}.
}
$$

## 结论二：所有 completion 都是 target completion

$$
\boxed{
C_{\mathcal T}(q)
=
q\vee\mathcal T.
}
$$

不同理论只是在选择不同目标族。

## 结论三：所有动力观察都是 Heisenberg closure

$$
\boxed{
\text{least invariant probe closure}
\longleftrightarrow
\text{greatest invariant state residual}.
}
$$

## 结论四：posterior 通常不是最小 observer state

posterior 是充分坐标；最小状态还要继续模去对所有可用未来协议都无差别的 posterior。

## 结论五：self 是策略相对的观察商

$$
\boxed{
\text{self}
=
\frac{\text{histories}}
{\text{same future action profile}}.
}
$$

## 结论六：局部—全局必须同时审计 kernel 与 image

只证明局部观察分离全局对象，不证明所有兼容局部族都能实现；只证明局部族可胶合，也不证明全局对象唯一。

## 结论七：adaptivity 改变平均成本，不取消信息预算

最坏深度由目标商类数控制；平均深度由目标熵控制。

## 结论八：递归描述不会自动增加观察力

$$
X\to M\to R
$$

的串行自我描述不能恢复 \(X\to M\) 已经删除的信息。

---

# 191. 建议的统一 Lean 模块

```text
D5/S3/Observer/Unified/
  ProtocolObserver.lean
  DependentOutcomeLaw.lean
  BehaviorSignature.lean
  ObservationalKernel.lean
  KernelRangeRepresentation.lean
  MinimalBehaviorRealization.lean
  ObserverRefinementOrder.lean
  ObserverLattice.lean
  ParallelSerialLaws.lean

D5/S3/Observer/Unified/Target/
  TargetKernel.lean
  TargetSufficiency.lean
  TargetCompletion.lean
  KnowledgeAsFactorization.lean
  PredictionAsTargetCompletion.lean
  PolicyProfileCompletion.lean

D5/S3/Observer/Unified/Dynamics/
  ProtocolGeneratedClosure.lean
  GreatestInvariantResidual.lean
  HeisenbergProbeClosure.lean
  CommonCompletionFixedPoint.lean
  CompletionOrderDefect.lean
  NoetherianObserverPrinciple.lean

D5/S3/Observer/Unified/Atlas/
  CompatibleRecordFamily.lean
  ObserverQuotientLimit.lean
  SeparationVsRealization.lean
  LocalGlobalExactness.lean
  ObserverImageDefect.lean
  FiberProductFusion.lean

D5/S3/Observer/Unified/Belief/
  BeliefFutureBehaviorFactor.lean
  BeliefMinimalityCriterion.lean
  PosteriorBehaviorQuotient.lean
  PolicySelfQuotient.lean

D5/S3/Observer/Unified/Memory/
  StoredAccessibleKnownRelevant.lean
  PredictiveMemoryResidual.lean
  SelfReportNoAmplification.lean

D5/S3/Observer/Unified/Budget/
  TargetWorstCaseDepthLowerBound.lean
  ExpectedDepthEntropyLowerBound.lean
  ApproximateIdentificationFanoBound.lean

D5/S3/Observer/Unified/Quantitative/
  ObserverLawPseudometric.lean
  WeightedObserverGramian.lean
  GramKernelIntersection.lean
  StatisticalConditioning.lean

D5/S3/Observer/Unified/Instances/
  DeterministicObserver.lean
  MarkovObserver.lean
  QuantumInstrumentObserver.lean
  PrimeIndexedObserver.lean
  CausalInterventionObserver.lean
  AgencyObserver.lean
```

优先形式化顺序应为：

```text
behaviorSignature
observationalKernel
quotient_equiv_behaviorRange
interface_sufficient_iff_kernel_le
targetSufficient_iff_kernel_le
targetCompletion_least
jointObserver_kernel_eq_inf
postprocessing_kernel_mono
postprocessing_kernel_eq_iff_injective_on_range
observerAtlas_exact_iff_injective_surjective
belief_factors_to_futureBehavior
belief_minimal_iff_futureBehavior_factor_injective
selfReport_kernel_mono
target_depth_clog_lower_bound
weightedGramian_kernel
```

---

# 192. 严格非主张

这套统一不意味着：

1. 所有观察者共享同一个物理实现；
2. 所有随机系统都可化为量子系统；
3. 所有量子系统都来自素数结构；
4. 素数具有意识；
5. 操作等价等于绝对本体相等；
6. posterior 永远是最小状态；
7. self quotient 等于全部人格或意识；
8. 记录存在等于当前知道；
9. 局部兼容自动意味着全局可实现；
10. 局部完备自动意味着全局唯一；
11. 自适应实验可以突破最坏信息下界；
12. kernel 为零自动意味着统计稳定；
13. 任意 completion 算子都彼此交换；
14. 自我递归自动产生额外世界信息；
15. 量子观察者可以选择单次 Born outcome；
16. 对角化单独推出量子概率；
17. 观察者商证明意识创造现实；
18. 当前全部 paper-level 统一定理已经获得 Lean proof term。

---

# 193. 最终统一公式

整个项目的观察者相关理论可以最终压缩成：

$$
\boxed{
\begin{aligned}
\mathfrak O
&=
(X,\mathsf{Prot},\mathsf{Out},\mathcal L),\\
\Sigma_{\mathfrak O}(x)
&=
(\mathcal L_\pi(x))_{\pi},\\
K_{\mathfrak O}
&=
\ker\Sigma_{\mathfrak O},\\
Q_{\mathfrak O}
&=
X/K_{\mathfrak O},\\
Q_{\mathfrak O}
&\cong
\operatorname{Im}\Sigma_{\mathfrak O},\\
\mathcal A_{\mathfrak O}
&=
\operatorname{Obs}(K_{\mathfrak O}),\\
\mathfrak O\text{ sufficient for }\mathcal T
&\iff
K_{\mathfrak O}\subseteq K_{\mathcal T},\\
\mathfrak O_1\preceq\mathfrak O_2
&\iff
K_{\mathfrak O_2}\subseteq K_{\mathfrak O_1},\\
K_{\mathfrak O_1\vee\mathfrak O_2}
&=
K_{\mathfrak O_1}\cap K_{\mathfrak O_2},\\
K_{f\circ\Sigma}
&\supseteq
K_\Sigma,\\
\text{local–global exactness}
&=
\text{injectivity}+\text{surjectivity},\\
\text{dynamic completion}
&=
\text{least invariant probe closure},\\
\text{hidden residual}
&=
\text{annihilator of visible closure}.
\end{aligned}
}
$$

最深的本体—结构收束是：

$$
\boxed{
观察者不是一个站在宇宙之外观看宇宙的点；
观察者是宇宙内部一套允许协议、记录边界、记忆更新与行动策略，
它把完整世界历史压缩为一个能够预测未来协议结果的最小行为商。
}
$$

进一步：

$$
\boxed{
知识是这个商上可定义的函数，
记忆是仍会改变未来行为的历史差异，
自我是仍会改变未来策略的历史差异，
经典事实是稳定可广播的记录中心，
量子性是协议代数的非交换结构，
素数性是局部协议索引的算术几何。
}
$$

所以，项目中所有观察者工作的真正统一核心可以命名为：

$$
\boxed{
\textbf{Protocol–Quotient–Limit Observer Theory}
}
$$

中文可称：

$$
\boxed{
\textbf{协议—商—极限统一观察者理论}.
}
$$
# 统一观察者理论的第二次闭合

## 从协议商到双侧完成、局部—全局、自指与科学发现

当前 `dev` 已包含此前的量子—素数观察者统一文档；随后仓库又合并了一次治理勘误。该勘误撤回的是一条形式化收据，而非相应 Lean 源文件本身，因此以下必须持续区分：

$$
\mathbf L:\text{仓库中已有 Lean 定理};
$$

$$
\mathbf P:\text{由这些结构继续推出的 paper-level 定理};
$$

$$
\mathbf R:\text{尚需新数学或新物理桥梁的研究命题}.
$$

上一阶段得到：

$$
\mathfrak O
=
(X,\mathsf{Prot},\mathsf{Out},\mathcal L),
$$

$$
\Sigma_{\mathfrak O}(x)
=
\bigl(\mathcal L_\pi(x)\bigr)_{\pi\in\mathsf{Prot}},
$$

$$
K_{\mathfrak O}
=
\ker \Sigma_{\mathfrak O},
$$

$$
Q_{\mathfrak O}
=
X/K_{\mathfrak O}
\cong
\operatorname{Im}\Sigma_{\mathfrak O}.
$$

这已经统一了“观察者怎样压缩世界”。

但它还没有回答五个更深的问题：

1. 协议本身是否有冗余？
2. 形式上可能的记录是否都有真实世界实现？
3. 多个观察者的联合知识与共同知识是否相同？
4. 自指和对角化究竟改变的是观察 kernel，还是行为像？
5. 观察者理论怎样成为一套可反复发现新实验、新定义和新模型的科学方法？

下面继续闭合。

---

# 194. 观察者不是单边商，而是一个双侧评价结构

设所有协议输出都被编码进某个共同语义空间 \(\Lambda\)。定义评价：

$$
e_{\mathfrak O}:
X\times P\to\Lambda,
$$

$$
e_{\mathfrak O}(x,\pi)
=
\mathcal L_\pi(x),
$$

其中：

* \(X\) 是世界状态；
* \(P\) 是协议；
* \(\Lambda\) 是结果、概率 law、矩阵期望、记录或行为值。

于是每个状态产生一行：

$$
r_x:P\to\Lambda,
\qquad
r_x(\pi)=e(x,\pi),
$$

每个协议产生一列：

$$
c_\pi:X\to\Lambda,
\qquad
c_\pi(x)=e(x,\pi).
$$

这暴露出两种不同的冗余。

## 状态冗余

$$
x\sim_X y
\iff
r_x=r_y.
$$

也就是：

$$
\forall\pi,\quad
\mathcal L_\pi(x)=\mathcal L_\pi(y).
$$

这正是原来的观察 kernel：

$$
\sim_X=K_{\mathfrak O}.
$$

## 协议冗余

$$
\pi\sim_P\rho
\iff
c_\pi=c_\rho.
$$

也就是：

$$
\forall x,\quad
\mathcal L_\pi(x)=\mathcal L_\rho(x).
$$

两个协议即使语法、设备或名称不同，只要对所有允许状态产生同一 law，在当前模型中就是操作等价协议。

---

# 195. 双外延观察者核

定义：

$$
\overline X=X/{\sim_X},
\qquad
\overline P=P/{\sim_P}.
$$

评价下降为：

$$
\overline e:
\overline X\times\overline P\to\Lambda,
$$

$$
\overline e([x],[\pi])=e(x,\pi).
$$

## 定理 195.1：双外延下降

该定义与代表元无关，而且：

$$
[x]\neq[y]
\Longrightarrow
\exists[\pi],\quad
\overline e([x],[\pi])
\neq
\overline e([y],[\pi]),
$$

$$
[\pi]\neq[\rho]
\Longrightarrow
\exists[x],\quad
\overline e([x],[\pi])
\neq
\overline e([x],[\rho]).
$$

### 证明

第一式来自状态等价关系的定义。若所有协议列值都相同，则 \(x\sim_Xy\)。

第二式同理。证毕。

所以：

$$
\boxed{
\overline{\mathfrak O}
=
(\overline X,\overline P,\overline e)
}
$$

同时删除了重复状态行和重复协议列。

这可以称为：

$$
\boxed{
\text{观察者的双外延核}
}
$$

或：

$$
\boxed{
\text{biextensional observer core}.
}
$$

此前的理论主要完成了 \(X\) 侧；统一理论还应同时完成 \(P\) 侧。

---

# 196. 观察者具有三种根本缺陷，而不是一种

现在可以正式区分三个逻辑独立的缺陷。

## 196.1 状态 kernel 缺陷

存在：

$$
x\neq y
$$

却有：

$$
r_x=r_y.
$$

即多个世界状态具有同一完整行为。

这是：

$$
\boxed{
\text{非唯一性缺陷}.
}
$$

## 196.2 协议 column 缺陷

存在：

$$
\pi\neq\rho
$$

却有：

$$
c_\pi=c_\rho.
$$

即多个协议名称实际做的是同一件事。

这是：

$$
\boxed{
\text{实验冗余缺陷}.
}
$$

## 196.3 行为像缺陷

形式行为空间记为：

$$
B_{\mathrm{formal}}
\subseteq
\prod_{\pi\in P}\Lambda_\pi.
$$

但实际世界只能产生：

$$
B_{\mathrm{real}}
=
\operatorname{Im}\Sigma_{\mathfrak O}.
$$

若：

$$
B_{\mathrm{real}}
\subsetneq
B_{\mathrm{formal}},
$$

则存在形式上可写、甚至局部兼容，但没有任何世界状态实现的行为族。

这是：

$$
\boxed{
\text{非存在性／实现缺陷}.
}
$$

仓库已机器核验：

$$
X/\ker\Sigma
\cong
\operatorname{Im}\Sigma,
$$

而该商等于整个形式余域，当且仅当 \(\Sigma\) 满射，即每个形式行为都可实现。

因此必须永远区分：

$$
\boxed{
\text{separation}
\neq
\text{realization}.
}
$$

---

# 197. 对角化本质上制造的是行为像缺陷

这是统一观察者理论中一个极重要的重新定位。

设：

$$
e:X\times X\to Y.
$$

把每个 \(a\in X\) 看作一行预测器：

$$
R(a):X\to Y,
\qquad
R(a)(x)=e(a,x).
$$

设：

$$
\delta:Y\to Y
$$

无不动点：

$$
\forall y,\quad
\delta(y)\neq y.
$$

定义对角行为：

$$
d(x)=\delta(e(x,x)).
$$

## 定理 197.1：对角行为不可实现

$$
\boxed{
d\notin\operatorname{Im}R.
}
$$

### 证明

假设存在 \(a\)：

$$
R(a)=d.
$$

在 \(x=a\) 处：

$$
e(a,a)
=
R(a)(a)
=
d(a)
=
\delta(e(a,a)),
$$

与 \(\delta\) 无不动点矛盾。证毕。

所以对角化首先证明：

$$
\boxed{
\text{某个形式行为不在当前行为像中}.
}
$$

它不必证明：

$$
\ker R\neq\Delta_X.
$$

完全可能出现：

$$
R\text{ 是单射}
$$

但仍然：

$$
R\text{ 不是满射}.
$$

因此：

$$
\boxed{
\text{对角不完备}
=
\text{image defect},
\quad
\text{而非必然的 state-kernel defect}.
}
$$

这是连接项目中“对角化”和“观察者 completion”的最严格方式。

---

# 198. 递归自我描述为何不增加观察力，但对角化仍有力量

设内部状态接口：

$$
q:X\to M.
$$

自我描述程序：

$$
r:M\to R.
$$

则：

$$
X\xrightarrow{q}M\xrightarrow{r}R.
$$

必有：

$$
\boxed{
\ker q
\subseteq
\ker(r\circ q).
}
$$

所以对已有内部状态继续：

* 命名；
* 压缩；
* 解释；
* 递归描述；
* 自我报告；

不能恢复 \(q\) 已经删除的世界差异。

但是对角化做的不是普通后处理。它利用：

$$
\text{自地址}
+
\text{评价}
+
\text{固定点自由变换}
$$

构造一个新的形式行为，并证明它不在现有行为像中。

因此：

$$
\boxed{
\text{自我报告不能增加 state separation，}
}
$$

但：

$$
\boxed{
\text{对角化可以证明当前行为模型不具备 realization completeness。}
}
$$

递归的力量不是“凭空看见更多世界数据”，而是：

$$
\boxed{
\text{暴露模型对自身形式语言的非满射性}.
}
$$

---

# 199. 协议不是集合，而应组织成范畴

不同协议之间通常存在：

* 前缀；
* 截断；
* 后处理；
* 串行组合；
* 并行组合；
* 精度粗化；
* 时间限制；
* 忘记某些输出；
* 限制到某个观察上下文。

因此协议索引最好组织成范畴：

$$
\mathcal C_{\mathfrak O}.
$$

对象 \(c\) 表示一个有限观察上下文。

态射：

$$
u:c\to d
$$

表示从较丰富的 \(d\)-记录限制或后处理得到 \(c\)-记录。

令：

$$
\mathcal B:
\mathcal C_{\mathfrak O}^{op}\to\mathbf{Set}
$$

为记录预层：

$$
c\longmapsto\mathcal B(c).
$$

其中 \(\mathcal B(c)\) 是上下文 \(c\) 的形式记录空间。

若：

$$
u:c\to d,
$$

则：

$$
\mathcal B(u):
\mathcal B(d)\to\mathcal B(c)
$$

是限制映射。

---

# 200. 每个世界状态产生一个兼容记录族

给定状态 \(x\in X\)，每个上下文都产生记录：

$$
\beta_c(x)\in\mathcal B(c).
$$

自然性要求：

$$
\mathcal B(u)(\beta_d(x))
=
\beta_c(x).
$$

因此 \(x\) 产生一个兼容族：

$$
\beta(x)
=
\bigl(\beta_c(x)\bigr)_c
\in
\varprojlim_{c\in\mathcal C}\mathcal B(c).
$$

定义：

$$
\Gamma(\mathcal B)
=
\varprojlim_c\mathcal B(c),
$$

即所有形式兼容记录族。

于是得到：

$$
\boxed{
\beta:
X\to\Gamma(\mathcal B).
}
$$

统一观察者商为：

$$
X/\ker\beta
\cong
\operatorname{Im}\beta.
$$

而局部—全局 image defect 为：

$$
\boxed{
\Gamma(\mathcal B)
\setminus
\operatorname{Im}\beta.
}
$$

这同时容纳：

* 有限时间前缀；
* 有限素数集合；
* 有限 \(p\)-进精度；
* 有限干预家族；
* 量子测量上下文；
* 多观察者局部记录；
* 有限历史；
* 有限计算窗口。

---

# 201. 各种观察者只是不同协议 site

## 时间观察者

上下文为：

$$
\{0,\ldots,n\}.
$$

限制是截断未来记录。

## 素数观察者

上下文为有限素数集及精度：

$$
(S,(k_p)_{p\in S}).
$$

限制是删除素数或降低精度。

## 量子顺序观察者

上下文是有限 instrument word 或协议树。

限制是取前缀或遗忘部分结果。

## 因果观察者

上下文是有限干预族。

限制是删除某些干预 regime。

## 多主体观察者

上下文是有限主体集合及其公开记录。

限制是忘记部分主体消息。

所以：

$$
\boxed{
\text{time completion},
\text{prime completion},
\text{quantum protocol completion},
\text{causal completion}
}
$$

都可以解释为：

$$
\boxed{
\text{在各自协议 site 上研究兼容局部记录的全局截面}.
}
$$

---

# 202. 观察紧致性定理

设：

* \(X\) 是紧致空间；
* 每个有限上下文记录空间 \(\mathcal B(c)\) 是 Hausdorff；
* 每个：

$$
\beta_c:X\to\mathcal B(c)
$$

连续；

* 上下文族对有限 join 封闭。

设给定一个兼容记录族：

$$
b=(b_c)_c.
$$

并假设每个有限上下文记录都可实现：

$$
b_c\in\operatorname{Im}\beta_c
\qquad
\forall c.
$$

## 定理 202.1：有限局部可实现推出全局可实现

存在：

$$
x\in X
$$

使：

$$
\beta_c(x)=b_c
\qquad
\forall c.
$$

### 证明

定义闭集：

$$
F_c
=
\{x\in X:\beta_c(x)=b_c\}.
$$

每个 \(F_c\) 非空且闭。

对有限上下文：

$$
c_1,\ldots,c_n,
$$

取联合上下文：

$$
d=c_1\vee\cdots\vee c_n.
$$

因为 \(b_d\) 可实现，存在 \(x_d\)：

$$
\beta_d(x_d)=b_d.
$$

由兼容性：

$$
x_d\in
F_{c_1}\cap\cdots\cap F_{c_n}.
$$

所以 \(\{F_c\}\) 具有有限交性质。

由 \(X\) 紧致：

$$
\bigcap_cF_c\neq\varnothing.
$$

证毕。

---

# 203. 紧致性解决 existence，但不解决 uniqueness

若再有：

$$
\ker\beta=\Delta_X,
$$

则上述实现唯一。

因此：

$$
\boxed{
\text{紧致性}
+
\text{有限局部可实现}
\Longrightarrow
\text{全局存在};
}
$$

$$
\boxed{
\text{观察分离性}
\Longrightarrow
\text{全局唯一}.
}
$$

最终：

$$
\boxed{
\text{局部—全局精确性}
=
\text{compact realization}
+
\text{observational separation}.
}
$$

有限状态空间是紧致定理的最简单实例。

仓库的有限 itinerary 工作甚至证明了更强结果：在有限状态系统中，不仅兼容完整前缀族可以实现，而且存在一个有限 completion depth，达到该深度后就已经决定全部未来。

---

# 204. 观察事件代数是世界商的对偶

对确定性接口：

$$
q:X\to Q,
$$

定义可观察事件代数：

$$
\mathcal A_q
=
\{A\subseteq X:
A=q^{-1}(B)
\text{ for some }B\subseteq Q\}.
$$

等价地：

$$
A\in\mathcal A_q
\iff
A\text{ 在每个 }q\text{-fiber 上常值}.
$$

对函数也类似：

$$
\operatorname{Obs}(K_q)
=
\{f:X\to V:
xK_qy\Rightarrow f(x)=f(y)\}.
$$

仓库已经证明：

$$
\boxed{
q\text{ 精化关系}
\iff
\text{反向 kernel 包含}
\iff
\text{pullback observable algebra 包含}.
}
$$

所以世界商和观察代数是同一结构的两面：

$$
\boxed{
\text{状态侧：合并不可区分世界};
}
$$

$$
\boxed{
\text{命题侧：保留在这些 fiber 上常值的函数}.
}
$$

---

# 205. 动态观察的三重对偶

给定：

$$
T:X\to X
$$

和初始接口：

$$
q:X\to Q.
$$

初始 kernel：

$$
K_0=\ker q.
$$

定义完整未来 kernel：

$$
K_\infty
=
\bigcap_{n\ge0}
(T^n\times T^n)^{-1}(K_0).
$$

即：

$$
xK_\infty y
\iff
q(T^nx)=q(T^ny)
\quad
\forall n.
$$

仓库已机器核验：该 all-iterate pullback 是 \(K_0\) 内最大的前向 congruence，并且具有单调性、收缩性和幂等性。

定义 observable algebra：

$$
\mathcal A_0
=
\operatorname{Obs}(K_0).
$$

定义动力闭包：

$$
\mathcal A_\infty
=
\operatorname{Alg}
\left\{
f\circ T^n:
f\in\mathcal A_0,\ n\ge0
\right\}.
$$

则：

$$
\boxed{
K_\infty
=
\operatorname{Ker}(\mathcal A_\infty).
}
$$

因此得到：

$$
\boxed{
\begin{aligned}
\text{state side}
&:\text{最大的稳定 residual};\\
\text{interface side}
&:\text{最小的稳定 refinement};\\
\text{observable side}
&:\text{最小的 }T^*\text{-不变代数闭包}.
\end{aligned}
}
$$

这三个并不是类比，而是同一个 completion 的三种坐标。

---

# 206. 受控观察的最小行为实现

若动作集合为 \(U\)，每个动作给出：

$$
T_u:X\to X.
$$

对有限动作词：

$$
w=(u_1,\ldots,u_n),
$$

定义：

$$
T_w.
$$

完整受控行为：

$$
B(x)(w)=q(T_wx).
$$

行为 kernel：

$$
x\sim_By
\iff
B(x)=B(y).
$$

商：

$$
Q_B=X/{\sim_B}.
$$

仓库已经证明：任何保持全部更新和读出的有限受控实现，都唯一并满射地映到该完整行为商；其状态数不小于完整行为商。

因此：

$$
\boxed{
Q_B
=
\text{全部受控未来行为的最小状态实现}.
}
$$

这实际上统一了：

* 自动机最小化；
* 预测状态；
* POMDP belief compression；
* 量子 instrument-word quotient；
* 素数—时间协议状态；
* 策略充分自我。

---

# 207. Completion 是反射，而 kernel completion 是内算子

定义观察者精化序：

$$
q\preceq r
\iff
r\text{ 比 }q\text{ 更细}.
$$

等价于：

$$
K_r\subseteq K_q.
$$

给定目标族 \(\mathcal T\)，定义：

$$
C_{\mathcal T}(q)
=
q\vee\mathcal T.
$$

即联合记录：

$$
x\longmapsto
\bigl(q(x),(T_\alpha(x))_\alpha\bigr).
$$

对任何已经足以决定 \(\mathcal T\) 的观察者 \(r\)：

$$
\boxed{
C_{\mathcal T}(q)\preceq r
\iff
q\preceq r.
}
$$

所以：

$$
C_{\mathcal T}
$$

是从所有观察者到“\(\mathcal T\)-充分观察者”子类的反射。

而状态关系侧：

$$
R\longmapsto
\operatorname{CongKernel}_T(R)
$$

是：

* 单调；
* 收缩；
* 幂等；

的 interior operator。

因此：

$$
\boxed{
\text{interface completion 是 closure/reflection，}
}
$$

$$
\boxed{
\text{kernel completion 是 interior/coreflection}.
}
$$

它们由反序关系互相转换。

---

# 208. 新协议真正增加信息的充要条件

设当前协议族为 \(P\)，kernel 为：

$$
K_P.
$$

加入新协议 \(\pi\)，得到：

$$
K_{P\cup\{\pi\}}
=
K_P\cap\ker\mathcal L_\pi.
$$

## 定理 208.1：协议创新判据

新协议严格增加观察能力，当且仅当存在：

$$
x,y\in X
$$

满足：

$$
xK_Py
$$

但：

$$
\mathcal L_\pi(x)
\neq
\mathcal L_\pi(y).
$$

即：

$$
\boxed{
\pi\text{ 有创新}
\iff
\exists(x,y)\in
K_P\setminus\ker\mathcal L_\pi.
}
$$

因此一个实验是否“新”，不取决于：

* 名称不同；
* 设备不同；
* 公式不同；
* 计算过程更复杂；

而取决于它是否切开了当前某个 residual fiber。

---

# 209. 旧协议重复不能穿透精确 kernel

若一切新 transcript 都只是完整旧协议 law 画像的函数，则：

$$
K_{\mathrm{old}}
\subseteq
K_{\mathrm{transcript}}.
$$

所以以下操作不会穿透旧 kernel：

* 无限重复同一实验；
* 调整采样次数；
* 自适应重排同一协议族；
* 对 transcript 做随机后处理；
* 使用更复杂分类器；
* 使用量子计算处理已经压缩后的经典标签。

仓库已经对固定干预族形式化了这一点：若两个模型具有相同的整个干预 law 画像，则任意重复次数、样本量、自适应 transcript law 和随机后处理都不能同时恢复它们不同的目标。

但加入真正的新干预可以严格缩小 kernel；仓库也已有一个有限 Boolean SCM 的严格例子：

$$
K_{\mathrm{intervention}}
\subsetneq
K_{\mathrm{observation}}.
$$

因此：

$$
\boxed{
\text{更多计算}
\neq
\text{更多观察};
}
$$

$$
\boxed{
\text{只有新的物理／操作耦合，才能产生新的区分方向}.
}
$$

---

# 210. 多观察者的“联合知识”与“共同知识”方向相反

设主体 \(i\) 的观察 kernel 为：

$$
K_i.
$$

可观察函数代数为：

$$
\mathcal A_i=\operatorname{Obs}(K_i).
$$

## 210.1 联合／分布式知识

所有主体把记录汇集起来：

$$
K_{\mathrm{pool}}
=
\bigcap_iK_i.
$$

其可观察代数：

$$
\mathcal A_{\mathrm{pool}}
=
\operatorname{Obs}
\left(
\bigcap_iK_i
\right).
$$

这是联合后能够知道的一切。

## 210.2 共同知识

定义主体可达关系的等价闭包：

$$
K_{\mathrm{common}}
=
\operatorname{EqClosure}
\left(
\bigcup_iK_i
\right).
$$

共同知识函数必须沿每个主体的不可区分边，以及所有这些边的有限链保持不变：

$$
\mathcal A_{\mathrm{common}}
=
\operatorname{Obs}(K_{\mathrm{common}}).
$$

有：

$$
\boxed{
\mathcal A_{\mathrm{common}}
=
\bigcap_i\mathcal A_i.
}
$$

### 证明

函数若在每个 \(K_i\) 上常值，就在其并及等价闭包上常值。

反向显然。证毕。

因此：

$$
\boxed{
\mathcal A_{\mathrm{common}}
\subseteq
\mathcal A_i
\subseteq
\mathcal A_{\mathrm{pool}}.
}
$$

共同知识是**交**，联合知识是**join**。

---

# 211. 一个极端的共同知识—联合知识分离例子

令：

$$
X=\{0,1\}^2.
$$

观察者一只看第一位：

$$
q_1(x_1,x_2)=x_1.
$$

观察者二只看第二位：

$$
q_2(x_1,x_2)=x_2.
$$

则：

$$
K_1\cap K_2=\Delta_X.
$$

所以联合观察完全恢复状态：

$$
\mathcal A_{\mathrm{pool}}
=
\operatorname{Fun}(X).
$$

但：

* \(K_1\) 允许改变第二位；
* \(K_2\) 允许改变第一位；
* 交替沿这些边，可以连接四个状态中的任意两个。

所以：

$$
K_{\mathrm{common}}
=
X\times X.
$$

因此：

$$
\mathcal A_{\mathrm{common}}
=
\{\text{常值函数}\}.
$$

即：

$$
\boxed{
\text{两个人联合起来什么都能知道，}
\quad
\text{但在交流之前，几乎没有非平凡共同知识}.
}
$$

仓库目前已有公共公告的一个 Lean 实例：真实命题被公开宣布并据此限制模型后，该命题在所有有限主体可达路径上保持成立，从而成为公告后共同知识。

---

# 212. 通信是否实现完整观察者融合

每个观察者拥有行为：

$$
\Sigma_i:X\to B_i.
$$

但实际广播的消息可能是压缩：

$$
m_i=f_i\circ\Sigma_i.
$$

联合消息：

$$
M(x)
=
\bigl(m_i(x)\bigr)_i.
$$

完整联合行为：

$$
\Sigma(x)
=
\bigl(\Sigma_i(x)\bigr)_i.
$$

显然：

$$
\ker\Sigma
\subseteq
\ker M.
$$

## 定理 212.1：无损通信判据

$$
\boxed{
\ker M=\ker\Sigma
}
$$

当且仅当：

$$
f:
\operatorname{Im}\Sigma
\to
\prod_i\operatorname{Im}m_i
$$

在实际联合行为像上单射。

也就是说，通信不必传输每个原始数据字节，但必须在**实际可发生的联合记录集合**上无损。

若每个：

$$
f_i
$$

在 \(\operatorname{Im}\Sigma_i\) 上单射，则这是一个充分条件，但不是必要条件；不同主体的压缩可能互相补偿。

仓库的 least-common-refinement 定理已经给出了两个 quotient completion 的规范融合：任何兼容且满射覆盖两个 quotient 的实现，都唯一满射地下沉到二者 kernel 交所定义的最小共同 refinement。

---

# 213. 一致记录不等于真实记录

多个主体输出相同消息可能有三种完全不同的原因：

$$
\boxed{
\begin{aligned}
&\text{它们独立观察到同一真实事实};\\
&\text{它们共享同一个粗 kernel};\\
&\text{它们复制了同一个上游错误或伪造源}.
\end{aligned}
}
$$

因此记录模型必须加入 provenance：

$$
r
=
(\text{payload},
\text{source},
\text{protocol},
\text{time},
\text{integrity proof}).
$$

相对于信任模型 \(\mathcal T\)，一个事实 \(f\) 才能称为受信知识，如果 \(f\) 在所有同时满足：

* 当前记录；
* provenance；
* 完整性规则；
* 信任假设；

的世界状态上常值。

所以：

$$
\boxed{
\text{共识是观察现象，}
\quad
\text{真实性是模型与 provenance 条件下的目标充分性}.
}
$$

---

# 214. 观察、干预和反事实构成严格协议层级

设：

$$
P_{\mathrm{obs}}
\subseteq
P_{\mathrm{int}}
\subseteq
P_{\mathrm{cf}}.
$$

分别为：

* 被动观察协议；
* 干预协议；
* 反事实耦合查询。

则：

$$
\boxed{
K_{\mathrm{cf}}
\subseteq
K_{\mathrm{int}}
\subseteq
K_{\mathrm{obs}}.
}
$$

第一处严格性可能来自：

不同模型产生同样的每个单独干预分布，但对跨世界反事实变量采用不同 coupling。

第二处严格性已经被仓库的 Boolean SCM 例子证实。

不过必须严格说明：

反事实查询通常不是一个直接可执行的物理实验，而是对结构模型的更强目标语言。因此：

$$
K_{\mathrm{cf}}
$$

首先是**模型语义 kernel**，不自动等于物理可操作 kernel。

---

# 215. Posterior 是充分状态，但不必是最小状态

设历史空间：

$$
H.
$$

posterior：

$$
\Pi:H\to\mathsf{Prob}(\Theta).
$$

有限未来自适应行为：

$$
B:H\to\mathsf{FutureLaw}.
$$

仓库已证明，在标准 Bayes update 条件下：

$$
\Pi(h)=\Pi(h')
$$

推出所有 belief-adaptive 有限未来输出 law 和递归 Bayes continuation value相同。

因此存在：

$$
F:
\operatorname{Im}\Pi
\to
\operatorname{Im}B
$$

使：

$$
B=F\circ\Pi.
$$

所以：

$$
\boxed{
K_\Pi\subseteq K_B.
}
$$

但 posterior 是最小未来行为状态，当且仅当：

$$
\boxed{
F\text{ 在 }\operatorname{Im}\Pi\text{ 上单射}.
}
$$

若两个不同 posterior 对所有允许实验都产生相同未来 law，则最小行为商还应继续合并它们。

---

# 216. Belief、predictive state 与 self 没有无条件固定顺序

定义策略画像：

$$
S:H\to\mathsf{PolicyProfile}.
$$

若策略只依赖 posterior：

$$
S=G\circ\Pi,
$$

则：

$$
K_\Pi\subseteq K_S.
$$

若策略只依赖最小未来行为：

$$
S=J\circ B,
$$

则：

$$
K_B\subseteq K_S.
$$

但如果策略使用：

* 身份标签；
* 历史来源；
* 道德承诺；
* 记忆 provenance；
* 与未来输出 law 无关的偏好；

则 \(S\) 未必通过 \(B\) 因子化。

因此不能无条件写：

$$
\Pi\to B\to S.
$$

严格结论是：

$$
\boxed{
\text{kernel 包含关系由实际因子化决定，}
\quad
\text{不能由概念名称决定}.
}
$$

最小 self 定义为：

$$
\boxed{
M_{\mathrm{self}}
=
H/\ker S.
}
$$

即：

> 恰好保留仍会改变未来策略的历史差异。

---

# 217. Reflexive observer：观察者成为世界状态的一部分

设完整世界状态：

$$
x=(e,m),
$$

其中：

* \(e\) 是环境；
* \(m\) 是观察者记忆、自我模型和策略状态。

读出：

$$
q:X\to M.
$$

策略：

$$
\pi:M\to A.
$$

环境更新：

$$
F:X\times A\to X.
$$

闭环动力学：

$$
T(x)=F(x,\pi(q(x))).
$$

此时观察者不是外部读取器，而是：

$$
\boxed{
\text{世界动力学中的闭环子结构}.
}
$$

它的观察会影响记忆，记忆决定行动，行动又改变未来可观察状态。

因此 reflexive observer 的完整行为必须对**策略闭环协议**取 kernel，而不能只对开放环读出取 kernel。

---

# 218. 精确透明自我预测的不可能三角

设动作集合 \(A\) 上存在固定点自由响应：

$$
\delta:A\to A,
\qquad
\delta(a)\neq a.
$$

预测器：

$$
P:M\to A.
$$

观察者读取预测后选择：

$$
\pi(m)=\delta(P(m)).
$$

若预测器要求精确：

$$
P(m)=\pi(m),
$$

则：

$$
P(m)=\delta(P(m)),
$$

矛盾。

所以以下三者不能同时成立：

$$
\boxed{
\begin{aligned}
&\text{预测对主体完全可访问};\\
&\text{预测要求逐结果精确};\\
&\text{主体能够执行固定点自由的反预测响应}.
\end{aligned}
}
$$

这可以称为：

$$
\boxed{
\text{透明自我预测三难}.
}
$$

它不是量子不确定性，也不是证明自由意志，而是一个闭环 fixed-point obstruction。

---

# 219. 三种解除自我预测矛盾的方法

## 限制透明性

主体在行动前看不到完整预测。

## 降低精确性

只预测概率分布而非单次结果。

例如二值翻转对概率：

$$
p\mapsto1-p
$$

存在固定分布：

$$
p=\frac12.
$$

所以分布级自洽可以存在，但结果级精确预测仍失败。

## 限制响应自由

主体预先承诺不根据预测反向改变行动。

因此：

$$
\boxed{
\text{commitment}
}
$$

可以把原本没有固定点的闭环改造成有固定点闭环。

这说明 commitment 不是单纯减少自由，它也可以创造：

* 可预测性；
* 跨时间协调；
* 可信承诺；
* 稳定 self-model。

---

# 220. 对角化与自我预测无解都属于 image/dynamic defect

现在可以进一步分类。

## 对角逃逸

产生：

$$
d\notin\operatorname{Im}\Sigma.
$$

它是：

$$
\boxed{
\text{image defect}.
}
$$

## 透明反预测

预测与响应无法共同满足闭环方程：

$$
p=\delta(p).
$$

它是：

$$
\boxed{
\text{dynamic realization defect}.
}
$$

## 状态不可区分

存在：

$$
x\neq y,
\qquad
\Sigma(x)=\Sigma(y).
$$

它是：

$$
\boxed{
\text{kernel defect}.
}
$$

三者必须分开：

$$
\boxed{
\text{non-uniqueness}
\neq
\text{non-existence}
\neq
\text{dynamic inconsistency}.
}
$$

---

# 221. 抽象观察者与物理观察者之间还缺一层实现态射

一个抽象观察者可以定义任意 law：

$$
\mathcal L_\pi:X\to\mathsf{Law}(O_\pi).
$$

但物理实现必须给出：

* 物理状态空间 \(W\)；
* 状态编码 \(h:W\to X\)；
* 协议编译器 \(C:P\to P_{\mathrm{phys}}\)；
* 实际物理 law \(\mathcal L^{\mathrm{phys}}\)。

并满足：

$$
\boxed{
\mathcal L^{\mathrm{phys}}_{C(\pi)}(w)
=
\mathcal L_\pi(h(w)).
}
$$

量子情况下还要满足：

* 完全正性；
* 迹保持或迹不增；
* 局域性；
* no-signalling；
* 有限能量／有限维近似；
* 合法记录实现。

因此：

$$
\boxed{
\text{abstract semantic completeness}
\not\Rightarrow
\text{physical realizability}.
}
$$

同理：

$$
\boxed{
\text{存在一个区分函数}
\not\Rightarrow
\text{存在一个可实施实验}.
}
$$

---

# 222. 近似观察者：kernel 应升级为伪度量

精确 kernel 只区分：

$$
D=0
\quad\text{与}\quad
D>0.
$$

设 \(D\) 是 law 空间上的区分度，例如：

* total variation；
* Hellinger；
* trace distance；
* 某种有界风险差；
* 可操作判别优势。

定义：

$$
d_{\mathfrak O}(x,y)
=
\sup_{\pi\in P}
w_\pi
D\bigl(
\mathcal L_\pi(x),
\mathcal L_\pi(y)
\bigr).
$$

若：

$$
D(\mu,\nu)=0\iff\mu=\nu
$$

且所有 \(w_\pi>0\)，则：

$$
\boxed{
d_{\mathfrak O}(x,y)=0
\iff
xK_{\mathfrak O}y.
}
$$

协议精化使：

$$
d_{\mathfrak O}
$$

单调不减。

串行后处理若满足 data processing，则区分度不增。

因此精确 kernel 理论是近似观察几何的零距离骨架。

---

# 223. 目标相对近似充分性

对目标：

$$
T:X\to Z
$$

给定目标度量：

$$
d_Z.
$$

若存在：

$$
L<\infty
$$

使：

$$
d_Z(Tx,Ty)
\le
L\,d_{\mathfrak O}(x,y),
$$

则观察者对目标具有 Lipschitz 稳健充分性。

这比：

$$
K_{\mathfrak O}\subseteq K_T
$$

更强。

后者只说：

$$
d_{\mathfrak O}=0
\Longrightarrow
d_Z=0.
$$

前者进一步控制：

$$
\text{小观察误差}
\Longrightarrow
\text{小目标误差}.
$$

因此完整性应分成：

$$
\boxed{
\begin{aligned}
\text{exact sufficiency}
&:\ker包含;\\
\text{stable sufficiency}
&:\text{正分离常数};\\
\text{statistical sufficiency}
&:\text{有限样本误差界};\\
\text{physical sufficiency}
&:\text{协议可实现}.
\end{aligned}
}
$$

---

# 224. 统一 Gram 定理

设状态差位于有限维内积空间 \(V\)。

每个协议产生线性读出：

$$
C_\pi:V\to Y_\pi.
$$

取严格正权重：

$$
w_\pi>0.
$$

定义：

$$
W_{\mathfrak O}
=
\sum_\pi
w_\pi C_\pi^*C_\pi.
$$

则：

$$
\langle v,W_{\mathfrak O}v\rangle
=
\sum_\pi
w_\pi\|C_\pi v\|^2.
$$

因此：

$$
\boxed{
\ker W_{\mathfrak O}
=
\bigcap_\pi\ker C_\pi.
}
$$

所以以下对象都是同一结构的实例：

$$
\begin{aligned}
&\text{线性系统 observability Gramian};\\
&\text{量子 tomography frame operator};\\
&\text{prime-time weighted Gramian};\\
&\text{Fisher information};\\
&\text{局部参数 Jacobian Gram};\\
&\text{zeta-weighted prime-precision Gramian}.
\end{aligned}
$$

最小特征值：

$$
\lambda_{\min}(W_{\mathfrak O})
$$

衡量最脆弱可见方向，而条件数衡量噪声放大。

---

# 225. Observer completion 不等于 metric completion

精确行为像：

$$
B_{\mathrm{real}}
=
\operatorname{Im}\Sigma
$$

可能不是完备空间。

对其度量完成：

$$
\widehat B
$$

可能加入一些 ideal behaviors：

$$
\widehat B\setminus B_{\mathrm{real}}.
$$

这些 ideal behavior 可以是：

* Cauchy 极限；
* 无限精度局部记录；
* profinite 点；
* 无限时间统计极限；
* 弱算子极限；
* 不由任何原始有限状态实现的理想态。

所以必须区分：

$$
\boxed{
\text{观测商完成}
}
$$

与：

$$
\boxed{
\text{拓扑／度量完成}.
}
$$

前者删除不可区分状态；后者添加极限点。

两者方向完全不同。

---

# 226. Noetherian 观察者原理

为什么仓库中如此多的有限状态观察过程最终会有限停止？

真正原因不是某个具体公式，而是观察者精化格具有有限高度。

设：

$$
q_0\preceq q_1\preceq q_2\preceq\cdots
$$

每一步严格精化都会严格增加：

* partition 类数；
* 可见子空间维数；
* 独立效果数；
* 可区分行为数。

若上界有限，则严格增长次数有限。

因此：

$$
\boxed{
\text{有限高度}
\Longrightarrow
\text{completion 有限稳定}.
}
$$

实例包括：

$$
|X|<\infty,
$$

或：

$$
\dim V<\infty,
$$

或量子系统：

$$
\dim\operatorname{Herm}_0(\mathcal H)=d^2-1.
$$

---

# 227. 开放协议语法会破坏有限稳定

若观察者不仅增加固定语法中的协议，还能扩展协议语言本身：

$$
P_0
\subsetneq
P_1
\subsetneq
P_2
\subsetneq\cdots,
$$

例如新加入：

* 新定义；
* 新传感器；
* 新干预变量；
* 新量子上下文；
* 新素数局部数据；
* 对旧观察器的元观察；
* 对证明系统的编码；

则没有理由要求 completion 在有限步停止。

定义协议语法生成器：

$$
G(P)
=
P\cup
\{\text{由 }P\text{ 可构造的新协议}\}.
$$

统一完成：

$$
P^*
=
\operatorname{lfp}G.
$$

有限阶段：

$$
P_{n+1}=G(P_n).
$$

极限阶段：

$$
P_\lambda
=
\bigcup_{\alpha<\lambda}P_\alpha.
$$

所以超限 completion 不是神秘递归，而是：

$$
\boxed{
\text{在开放协议语法下寻找最小固定点}.
}
$$

---

# 228. 所有 completion 算子不一定交换

设：

$$
C_T
$$

为时间 completion，

$$
C_I
$$

为干预 completion，

$$
C_P
$$

为素数 completion，

$$
C_Q
$$

为量子上下文 completion，

$$
C_M
$$

为记忆 completion。

一般：

$$
C_iC_j(q)
\neq
C_jC_i(q).
$$

例如：

* 先让动力传播局部信息，再加入跨素数读出；
* 先把每一步投影到局部代数，再做动力闭包；

可能得到不同可见空间。

统一完成必须取所有 completion 的最小共同固定点：

$$
\boxed{
q^*
=
\operatorname{lfp}
\left(
q\mapsto
\bigvee_iC_i(q)
\right).
}
$$

若各 completion 两两交换，则一次组合后即可稳定。

若不交换，则必须迭代。

---

# 229. 科学发现有两种完全不同的修复方向

设当前模型为 \(X_n\)，观察者为 \(\mathfrak O_n\)。

## 229.1 Separation repair

找到：

$$
x\neq y,
\qquad
xK_{\mathfrak O_n}y,
$$

但目标不同：

$$
T(x)\neq T(y).
$$

这是 target residual witness。

修复方式是加入新协议 \(\pi\)，使：

$$
\mathcal L_\pi(x)
\neq
\mathcal L_\pi(y).
$$

这缩小 kernel。

## 229.2 Realization repair

找到一个形式兼容行为：

$$
b\in B_{\mathrm{formal}}
$$

但：

$$
b\notin\operatorname{Im}\Sigma_{\mathfrak O_n}.
$$

修复方式有两种：

1. 扩大世界／模型类，使 \(b\) 可实现；
2. 加强 admissibility 条件，证明 \(b\) 根本不是合法形式行为。

这修复 image defect。

因此科学进步不是单轴的“知道更多”。

它同时沿两个方向运动：

$$
\boxed{
\text{缩小 observational kernel}
}
$$

与：

$$
\boxed{
\text{校正 realized image}.
}
$$

---

# 230. 对角化是一种 realization audit

在上述科学循环中，对角化不是直接发明一个新世界状态。

它构造一个形式行为：

$$
d
$$

并证明：

$$
d\notin\operatorname{Im}\Sigma.
$$

因此对角化给出：

$$
\boxed{
\text{当前模型行为像不是形式行为域的全部}.
}
$$

随后必须作出选择：

* 扩大状态空间；
* 扩大语法；
* 限制形式行为域；
* 放弃固定点自由 twist；
* 放弃全局自地址；
* 接受不完备性。

所以对角化在统一观察者理论中的角色是：

$$
\boxed{
\text{行为像的内部审计器}.
}
$$

---

# 231. 统一观察者的规范化流程

给定任意原始观察者，依次执行：

## 第一步：协议生成闭包

加入所有允许的：

* 组合；
* 时间演化；
* 干预；
* 后处理；
* 顺序 instrument；
* 联合观察。

得到：

$$
P_\infty.
$$

## 第二步：状态外延化

模去行为相同的状态：

$$
X\to X/{\sim_X}.
$$

## 第三步：协议分离化

模去所有状态上行为相同的协议：

$$
P_\infty\to P_\infty/{\sim_P}.
$$

## 第四步：行为像化

只保留真实可实现行为：

$$
B_{\mathrm{real}}
=
\operatorname{Im}\Sigma.
$$

## 第五步：理想极限完成

按需要取：

* 逆极限；
* 拓扑闭包；
* 度量完成；
* 弱／强算子闭包。

得到：

$$
\widehat B.
$$

最终结构：

$$
\boxed{
\operatorname{Core}(\mathfrak O)
=
\left(
X/{\sim_X},
P_\infty/{\sim_P},
B_{\mathrm{real}},
\widehat B
\right).
}
$$

这四个部分分别回答：

$$
\begin{aligned}
&\text{哪些世界状态真正不同？}\\
&\text{哪些协议真正不同？}\\
&\text{哪些行为真实发生？}\\
&\text{哪些理想行为作为极限存在？}
\end{aligned}
$$

---

# 232. 观察者的完整分类坐标

任何观察者都可以按以下轴定位。

## 语义轴

$$
\text{deterministic}
\to
\text{probabilistic}
\to
\text{quantum}.
$$

## 协议能力轴

$$
\text{passive}
\to
\text{dynamic}
\to
\text{interventional}
\to
\text{counterfactual}
\to
\text{reflexive}.
$$

## 局部性轴

$$
\text{single-site}
\to
\text{multi-site}
\to
\text{local-global atlas}.
$$

## 记忆轴

$$
\text{memoryless}
\to
\text{finite memory}
\to
\text{predictive state}
\to
\text{inverse-limit memory}.
$$

## 精确度轴

$$
\text{exact kernel}
\to
\text{metric separation}
\to
\text{finite-sample inference}.
$$

## 实现轴

$$
\text{formal}
\to
\text{mathematical realization}
\to
\text{physical implementation}
\to
\text{auditable record}.
$$

“素数观察者”“量子观察者”“因果观察者”不是互斥类别，而是在这些轴上的不同坐标组合。

---

# 233. 新的统一观察者总定理

可以把上述结构压缩成如下 paper-level 总定理。

## 统一观察者双完成定理

给定协议评价系统：

$$
e:X\times P\to\Lambda,
$$

并给定协议生成闭包 \(\operatorname{Cl}(P)\)，则存在规范结构：

$$
\mathfrak O^*
=
(X^*,P^*,e^*,B_{\mathrm{real}},B_{\mathrm{formal}})
$$

满足：

$$
X^*
=
X/\!\sim_X,
$$

$$
P^*
=
\operatorname{Cl}(P)/\!\sim_P,
$$

$$
B_{\mathrm{real}}
=
\operatorname{Im}
\left(
X\to
\Lambda^{\operatorname{Cl}(P)}
\right),
$$

并且：

1. \(e^*\) 没有重复状态行；
2. \(e^*\) 没有重复协议列；
3. \(X^*\cong B_{\mathrm{real}}\)；
4. 任意保持全部协议行为的状态实现都满射到 \(X^*\)；
5. 任意纯后处理不能缩小 \(X^*\) 的 kernel；
6. 新协议严格增加能力，当且仅当它切开某个旧 residual fiber；
7. \(B_{\mathrm{formal}}\setminus B_{\mathrm{real}}\) 精确描述 realization defect；
8. 对角化在满足自地址和固定点自由条件时构造 realization defect；
9. 若状态空间紧致且所有有限局部记录连续可实现，则兼容局部记录全局可实现；
10. 若再有状态分离，则局部记录唯一决定全局状态。

这可以视为此前“协议—商—极限”理论的真正双侧闭合。

---

# 234. 最深的进一步结论

## 第一：观察者理论的基本对象不是“眼睛”，而是评价矩阵

$$
\boxed{
\text{state}\times\text{protocol}
\longrightarrow
\text{law}.
}
$$

## 第二：kernel 和 image 是两种完全不同的不完备

$$
\boxed{
\text{kernel defect}=\text{多个状态同一行为};
}
$$

$$
\boxed{
\text{image defect}=\text{某些形式行为没有状态}.
}
$$

## 第三：对角化作用在 image，不必作用在 kernel

这是对角理论与观察者理论最重要的精确桥梁。

## 第四：动态 completion 是三重对偶

$$
\boxed{
\text{最大稳定 residual}
\leftrightarrow
\text{最小稳定 observer refinement}
\leftrightarrow
\text{最小不变 observable closure}.
}
$$

## 第五：共同知识和联合知识相反

$$
\boxed{
\text{共同知识}
=
\text{observable algebra 的交};
}
$$

$$
\boxed{
\text{联合知识}
=
\text{kernel 的交所产生的更大代数}.
}
$$

## 第六：posterior 是 sufficient statistic，不自动是 minimal ontology

最小状态由允许协议决定，而不是由“posterior”这个名字决定。

## 第七：自我递归不能恢复被内部接口删除的数据

但它可以通过对角化证明自我模型的形式行为域过大。

## 第八：科学发展需要同时修复 kernel 与 image

实验解决非唯一性，模型修订解决非存在性。

---

# 235. 下一阶段最值得 Lean 化的定理链

```text
Observer/Unified/Evaluation/
  StateRowKernel.lean
  ProtocolColumnKernel.lean
  BiextensionalCollapse.lean

Observer/Unified/Presheaf/
  FiniteContextRecords.lean
  CompatibleRecordFamily.lean
  ObservationalCompactness.lean
  SeparationRealizationExactness.lean

Observer/Unified/Diagonal/
  DiagonalEscapeIsImageDefect.lean
  SelfReportKernelMonotonicity.lean
  TransparentPredictionNoFixedPoint.lean

Observer/Unified/MultiAgent/
  PooledObserverKernel.lean
  CommonKnowledgeKernel.lean
  CommonVsDistributedObservableAlgebra.lean
  LosslessCommunicationOnRealizedRange.lean

Observer/Unified/Dynamics/
  StateKernelObservableClosureDuality.lean
  ProtocolNoveltyCriterion.lean
  CommonCompletionFixedPoint.lean

Observer/Unified/Approximate/
  ProtocolLawPseudometric.lean
  TargetLipschitzSufficiency.lean
  WeightedGramKernel.lean
```

首要 theorem names 可以是：

```lean
stateQuotient_equiv_behaviorRange

biextensionalEvaluation_descends

diagonalEscape_mem_imageResidual

selfReport_kernel_mono

compatibleFiniteRecords_realized_of_compact

localGlobalExact_iff_separating_and_surjective

dynamicKernel_eq_kernel_observableClosure

protocol_strictly_innovative_iff_separates_oldFiber

commonObservableAlgebra_eq_iInter

pooledObserver_kernel_eq_iInter

losslessCommunication_iff_injective_on_realizedRange

equalPosterior_factors_futureBehavior
```

---

# 最终收束

统一观察者理论现在可以写成：

$$
\boxed{
\begin{aligned}
\text{World states}
&=X,\\
\text{Protocols}
&=P,\\
\text{Evaluation}
&=e:X\times P\to\Lambda,\\
\text{State reality}
&=X/\text{equal rows},\\
\text{Protocol reality}
&=P/\text{equal columns},\\
\text{Real behavior}
&=\operatorname{Im}\Sigma,\\
\text{Formal behavior}
&=\Gamma(\mathcal B),\\
\text{Hidden residual}
&=\text{row kernel},\\
\text{Protocol redundancy}
&=\text{column kernel},\\
\text{Realization defect}
&=\Gamma(\mathcal B)\setminus\operatorname{Im}\Sigma,\\
\text{Dynamic completion}
&=\text{least invariant protocol closure},\\
\text{Knowledge}
&=\text{functions constant on state fibers},\\
\text{Self}
&=\text{histories modulo future policy equality}.
\end{aligned}
}
$$

最深的一句话是：

$$
\boxed{
观察者不是一个“看见世界”的点，
而是一张世界状态与可执行协议之间的评价网。
}
$$

这张网同时决定：

$$
\boxed{
\begin{aligned}
&\text{哪些状态差异真实可操作；}\\
&\text{哪些实验只是重复命名；}\\
&\text{哪些记录可以由真实世界实现；}\\
&\text{哪些局部记录能够胶合为全局事实；}\\
&\text{哪些历史差异必须保留为记忆与自我；}\\
&\text{哪些自我描述因为对角化而无法闭合。}
\end{aligned}
}
$$

因此，项目全部观察者工作的更完整名称可以进一步升级为：

$$
\boxed{
\textbf{Protocol–Evaluation–Quotient–Image–Limit Theory}
}
$$

中文为：

$$
\boxed{
\textbf{协议—评价—商—像—极限统一观察者理论}.
}
$$
以下内容可直接承接现有第 203 节。前文已经把统一观察者理论压缩为评价网

$$
\text{state}\times\text{protocol}
\longrightarrow
\text{law},
$$

并将商、像、局部胶合、自指逃逸、实验精化与极限实现纳入同一结构。

---

# 204. 增订七：二重外延化、协议概念格与观察谱

## 204.1 本增订的核心问题

前文主要从**状态侧**研究观察者：

$$
x\sim_{\mathfrak O}y
\iff
\forall p\in P,\quad
e(x,p)=e(y,p).
$$

但评价网还有完全对偶的一侧：

$$
p\sim_{\mathfrak O}^{\vee}q
\iff
\forall x\in X,\quad
e(x,p)=e(x,q).
$$

因此，一个完整观察者理论不能只问：

> 哪些状态被现有协议合并？

还必须同时问：

> 哪些协议只是不同名称下的同一问题？

本增订建立以下新层次：

$$
\boxed{
\text{状态去重}
+
\text{协议去重}
+
\text{二者之间的 Galois 闭包}
+
\text{线性观察谱}
+
\text{可实现像证书}.
}
$$

为使状态与协议可以严格交换，以下若讨论双侧对偶，暂设所有协议共享同一 law carrier：

$$
e:X\times P\longrightarrow\Lambda.
$$

若实际输出依赖协议类型

$$
e_p:X\to\Lambda_p,
$$

则状态侧理论仍直接成立；协议侧比较则需要先给出公共比较载体或明确的异构 law 等价。

---

# 205. 状态行、协议列与对偶观察者

## 定义 205.1（状态行为行）

对每个状态 $x\in X$，定义其行为行：

$$
r_x:P\to\Lambda,
\qquad
r_x(p)=e(x,p).
$$

## 定义 205.2（协议响应列）

对每个协议 $p\in P$，定义其响应列：

$$
c_p:X\to\Lambda,
\qquad
c_p(x)=e(x,p).
$$

于是评价网可以同时写成：

$$
\Sigma_X:X\to\Lambda^P,
\qquad
\Sigma_X(x)=r_x,
$$

以及

$$
\Sigma_P:P\to\Lambda^X,
\qquad
\Sigma_P(p)=c_p.
$$

## 定义 205.3（双侧 kernel）

状态 kernel 为

$$
K_X
=
\ker\Sigma_X
=
\{(x,y):r_x=r_y\},
$$

协议 kernel 为

$$
K_P
=
\ker\Sigma_P
=
\{(p,q):c_p=c_q\}.
$$

## 定义 205.4（行外延与列外延）

观察者称为：

* **状态外延的**，若 $\Sigma_X$ 单射；
* **协议外延的**，若 $\Sigma_P$ 单射；
* **双外延的**，若二者均单射。

状态外延表示不存在两个完全不可区分的状态标签；协议外延表示不存在两个在全部状态上完全相同的问题标签。

## 定义 205.5（对偶观察者）

定义

$$
\mathfrak O^\vee
=
(P,X,\Lambda,e^\vee),
$$

其中

$$
e^\vee(p,x)=e(x,p).
$$

于是：

$$
(\mathfrak O^\vee)^\vee=\mathfrak O,
$$

并且状态 kernel 与协议 kernel 互换。

## 结论 205.1

观察者不是单向映射

$$
X\to\text{records},
$$

而是一张双侧评价矩阵：

$$
\boxed{
\begin{array}{c|cccc}
 & p_1&p_2&\cdots&p_m\\
\hline
x_1&e(x_1,p_1)&e(x_1,p_2)&\cdots&e(x_1,p_m)\\
x_2&e(x_2,p_1)&e(x_2,p_2)&\cdots&e(x_2,p_m)\\
\vdots&\vdots&\vdots&&\vdots
\end{array}
}
$$

状态完备性研究矩阵行是否不同；协议非冗余性研究矩阵列是否不同。

---

# 206. 双外延坍缩定理

## 定义 206.1（双商）

定义

$$
\overline X=X/K_X,
\qquad
\overline P=P/K_P.
$$

并令

$$
\overline e:
\overline X\times\overline P
\longrightarrow\Lambda
$$

由

$$
\overline e([x],[p])=e(x,p)
$$

给出。

## 定理 206.1（良定义性）

$\overline e$ 良定义。

### 证明

若

$$
x\sim_X y,
\qquad
p\sim_P q,
$$

则先由 $x\sim_Xy$ 得

$$
e(x,p)=e(y,p),
$$

再由 $p\sim_Pq$ 得

$$
e(y,p)=e(y,q).
$$

故

$$
e(x,p)=e(y,q).
$$

所以结果与代表元无关。∎

## 定理 206.2（双外延性）

$$
(\overline X,\overline P,\Lambda,\overline e)
$$

是双外延观察者。

### 证明

若两个状态类在全部协议类上同值，则其任意代表在全部原协议上同值，故原状态属于同一 $K_X$ 类。协议侧同理。∎

## 定理 206.3（商次序交换）

先商去状态重复，再商去协议重复，与先商协议再商状态，得到规范同构的评价对象：

$$
(X/K_X)/K_P
\cong
(P/K_P)/K_X
$$

更准确地说，两条路径的最终状态载体、协议载体和评价映射分别规范同构。

### 原因

协议是否重复只取决于其在所有状态行上的值；把相同行合并不会改变两列是否相等。对偶地，把相同列合并也不会改变两行是否相等。

## 定理 206.4（双外延坍缩的普适最小性）

设存在满射

$$
a:X\twoheadrightarrow X',
\qquad
b:P\twoheadrightarrow P',
$$

以及双外延评价

$$
e':X'\times P'\to\Lambda
$$

满足

$$
e(x,p)=e'(a(x),b(p)).
$$

则存在唯一双射

$$
\alpha:\overline X\overset{\sim}{\longrightarrow}X',
$$

以及唯一双射

$$
\beta:\overline P\overset{\sim}{\longrightarrow}P'
$$

使整个评价方块交换。

### 证明

若 $xK_Xy$，则对全部 $p$：

$$
e'(a(x),b(p))
=
e'(a(y),b(p)).
$$

由于 $b$ 满射，上式对全部 $p'\in P'$ 成立。由 $e'$ 的状态外延性：

$$
a(x)=a(y).
$$

反向若 $a(x)=a(y)$，显然 $xK_Xy$。所以

$$
\ker a=K_X.
$$

因此 $a$ 在 $\overline X$ 上诱导双射。协议侧同理。∎

## 结论 206.1

双外延坍缩不是任意数据清洗，而是评价网的规范最小表示：

$$
\boxed{
\text{删除所有不可操作区分的状态标签}
+
\text{删除所有不可操作区分的协议标签}.
}
$$

---

# 207. 协议—区分关系的 Galois 连接

双外延商只能删除完全重复对象。更深的问题是：一组协议究竟生成了哪些区分？哪些协议已经被这一组协议语义蕴含？

## 定义 207.1（协议族诱导的状态关系）

对任意协议子集

$$
Q\subseteq P,
$$

定义

$$
K(Q)
=
\bigcap_{p\in Q}\ker c_p.
$$

即

$$
xK(Q)y
\iff
\forall p\in Q,\quad e(x,p)=e(y,p).
$$

## 定义 207.2（关系所允许的协议）

对任意关系

$$
R\subseteq X\times X,
$$

定义

$$
\Pi(R)
=
\{p\in P:R\subseteq\ker c_p\}.
$$

也就是说，$\Pi(R)$ 是全部不能切开 $R$ 中状态对的协议。

## 定理 207.1（反序 Galois 连接）

对任意 $Q\subseteq P$ 与 $R\subseteq X^2$：

$$
\boxed{
Q\subseteq\Pi(R)
\iff
R\subseteq K(Q).
}
$$

### 证明

左侧表示每个 $p\in Q$ 都在每个 $(x,y)\in R$ 上取相同值。这恰好表示每个 $(x,y)\in R$ 属于所有 $\ker c_p$ 的交。∎

## 定义 207.3（协议闭包）

$$
\operatorname{Cl}_P(Q)
=
\Pi(K(Q)).
$$

## 定义 207.4（关系闭包）

$$
\operatorname{Cl}_X(R)
=
K(\Pi(R)).
$$

## 定理 207.2（闭包算子）

两个算子均满足：

$$
Q\subseteq\operatorname{Cl}_P(Q),
$$

$$
Q_1\subseteq Q_2
\Longrightarrow
\operatorname{Cl}_P(Q_1)
\subseteq
\operatorname{Cl}_P(Q_2),
$$

$$
\operatorname{Cl}_P^2(Q)
=
\operatorname{Cl}_P(Q),
$$

关系侧同理。

## 解释

$\operatorname{Cl}_P(Q)$ 不只是由 $Q$ 通过语法组合生成的协议，而是：

$$
\boxed{
所有在状态区分能力上不超过 $Q$ 的现有协议。
}
$$

两个协议可以表达式完全不同、计算复杂度完全不同，却属于同一个观察闭包。

---

# 208. 精确协议新颖性判据

## 定理 208.1（零增益判据）

对任意现有协议族 $Q$ 与候选协议 $p$：

$$
\boxed{
p\in\operatorname{Cl}_P(Q)
\iff
K(Q\cup\{p\})=K(Q).
}
$$

### 证明

若 $p\in\Pi(K(Q))$，则 $p$ 在每个 $K(Q)$ 类上常值，因此加入 $p$ 不会继续切分这些类。

反向，若加入 $p$ 后 kernel 不变，则任意 $(x,y)\in K(Q)$ 仍满足

$$
e(x,p)=e(y,p),
$$

所以

$$
K(Q)\subseteq\ker c_p,
$$

即

$$
p\in\Pi(K(Q)).
$$

∎

## 推论 208.1（严格新颖性）

$$
\boxed{
K(Q\cup\{p\})
\subsetneq
K(Q)
\iff
p\notin\operatorname{Cl}_P(Q).
}
$$

因此一个协议是否真正增加认识能力，不由下列因素决定：

* 名称是否新；
* 公式是否更长；
* 计算是否更复杂；
* 输出 bit 数是否更多；
* 是否使用量子、素数或神经网络术语。

唯一严格标准是：

$$
\boxed{
它是否切开了旧协议族尚未切开的状态对。
}
$$

## 定义 208.1（闭合观察概念）

称一对

$$
(R,Q)
$$

为闭合观察概念，若

$$
R=K(Q),
\qquad
Q=\Pi(R).
$$

这些闭合对构成一个完整概念格：

* 协议越多，状态关系越细；
* 状态关系越细，允许常值的协议越少；
* 两侧以反序方式互相决定。

---

# 209. 有限协议压缩定理

## 定理 209.1（有限商的 $r-1$ 协议证书）

设 $X$ 有限，$Q\subseteq P$，并令

$$
r
=
|X/K(Q)|.
$$

则存在有限子集

$$
Q_0\subseteq Q
$$

满足

$$
K(Q_0)=K(Q),
$$

且

$$
\boxed{
|Q_0|\le r-1.
}
$$

### 证明

从

$$
Q_0=\varnothing
$$

开始，此时只有一个观察类。

若当前 $K(Q_0)\neq K(Q)$，则存在 $x,y$：

$$
xK(Q_0)y,
\qquad
\neg xK(Q)y.
$$

后式保证存在某个 $p\in Q$ 使

$$
e(x,p)\neq e(y,p).
$$

加入该协议后，当前分块数至少增加一。由于当前分块始终比目标分块粗，分块数不超过 $r$。从一个块开始，最多经过 $r-1$ 次严格增加即达到目标分块。∎

## 推论 209.1

即使协议全集无限，只要最终操作商只有有限个状态类，就存在有限区分证书。

这里有限性来自目标商的块数，而不是来自原状态类型或协议语法是否有限。

## 定理 209.2（输出容量下界）

设一个协议子集 $S$ 已经分离上述 $r$ 个状态类。令

$$
m_p
=
|\operatorname{Im}(c_p)|
$$

为协议 $p$ 在目标状态类上的有效输出数，则

$$
\boxed{
r\le\prod_{p\in S}m_p.
}
$$

因此

$$
\boxed{
\log_2r
\le
\sum_{p\in S}\log_2m_p.
}
$$

若所有协议至多有 $m$ 个结果：

$$
\boxed{
|S|
\ge
\left\lceil\log_mr\right\rceil.
}
$$

## 解释

于是有限观察预算存在两类完全不同的界：

$$
\left\lceil\log_mr\right\rceil
\le
\text{最小协议数}
\le
r-1.
$$

左侧来自单协议输出容量；右侧来自逐步切开观察类。

---

# 210. 自适应区分树

固定目标商

$$
C=X/K(Q),
\qquad
|C|=r.
$$

由于每个 $p\in Q$ 在每个目标类上常值，可把协议视为函数

$$
p:C\to\Lambda.
$$

## 定理 210.1（自适应深度上界）

若 $Q$ 分离 $C$ 中所有不同类，则存在一棵自适应协议树，其最坏深度满足

$$
\boxed{
D_{\max}\le r-1.
}
$$

### 证明

若当前候选集合 $S\subseteq C$ 有至少两个元素，选取不同的 $a,b\in S$。由分离性，存在协议 $p$ 使

$$
p(a)\neq p(b).
$$

执行 $p$ 后，$S$ 被分为至少两个非空子集，因此每个分支的候选数至多为 $|S|-1$。递归即可。∎

## 定理 210.2（有限结果深度下界）

若每个协议至多产生 $m$ 个结果，则任何能够识别全部 $r$ 个类的决策树均满足

$$
\boxed{
D_{\max}
\ge
\left\lceil\log_mr\right\rceil.
}
$$

因为深度 $D$ 的 $m$ 叉树最多有 $m^D$ 个叶。

## 严格边界 210.1

以上是无噪声、协议结果精确可读的组合界。存在：

* 统计误差；
* 量子测量扰动；
* 协议成本不同；
* 结果概率极不均匀；
* 可执行协议依赖历史

时，最小样本数、最小期望成本与最小最坏深度必须分别定义，不能由同一 $r-1$ 界替代。

---

# 211. 线性观察算子与双 Gram 几何

设状态差异空间为有限维 Hilbert 空间 $V$，协议读出是线性泛函

$$
\ell_i:V\to\mathbb F,
\qquad
1\le i\le m,
$$

其中 $\mathbb F=\mathbb R$ 或 $\mathbb C$。

定义观察算子

$$
M:V\to\mathbb F^m,
$$

$$
Mv
=
\begin{bmatrix}
\ell_1(v)\\
\vdots\\
\ell_m(v)
\end{bmatrix}.
$$

## 定义 211.1（状态 Gram 算子）

$$
\boxed{
W_X=M^*M.
}
$$

## 定义 211.2（协议 Gram 算子）

$$
\boxed{
W_P=MM^*.
}
$$

## 定理 211.1（双 kernel）

$$
\boxed{
\ker W_X=\ker M,
}
$$

$$
\boxed{
\ker W_P=\ker M^*.
}
$$

### 解释

* $\ker M$：全部协议都看不见的状态方向；
* $\ker M^*$：协议线性组合中的完全冗余方向。

若

$$
a=(a_1,\ldots,a_m)\in\ker M^*,
$$

则

$$
\sum_i a_i\ell_i=0.
$$

所以协议侧 residual 不是“没有状态”，而是多个协议之间存在不可消去的线性依赖。

## 定理 211.2（双可见空间）

$$
\operatorname{ran}W_X
=
\operatorname{ran}M^*,
$$

$$
\operatorname{ran}W_P
=
\operatorname{ran}M.
$$

前者是状态空间中真正被协议张成的方向；后者是协议结果空间中真正可以由状态变化实现的方向。

---

# 212. 观察谱对偶定理

## 定理 212.1（非零谱一致）

$W_X=M^*M$ 与 $W_P=MM^*$ 具有相同的非零特征值，并具有相同代数重数：

$$
\boxed{
\operatorname{Spec}_{>0}(M^*M)
=
\operatorname{Spec}_{>0}(MM^*).
}
$$

### 证明

若

$$
M^*Mv=\lambda v,
\qquad
\lambda>0,
$$

则 $Mv\neq0$，并且

$$
MM^*(Mv)
=
M(M^*Mv)
=
\lambda Mv.
$$

所以 $Mv$ 是 $MM^*$ 的 $\lambda$-特征向量。反向使用 $M^*$。这两个映射在正特征空间之间互逆至比例，故重数相同。∎

## 推论 212.1（秩一致）

$$
\boxed{
\operatorname{rank}W_X
=
\operatorname{rank}M
=
\operatorname{rank}W_P.
}
$$

## 推论 212.2（条件数对偶）

状态重建的非零谱条件数与协议独立化的非零谱条件数完全相同。

因此同一个小奇异值有两种对偶解释：

$$
\boxed{
\text{存在一个极难看见的状态方向}
}
$$

等价于

$$
\boxed{
\text{存在一个近乎线性依赖的协议组合}.
}
$$

## 最深解释 212.1

观察困难并不只属于被观察对象，也不只属于仪器；它是状态空间与协议空间耦合后的共同谱性质：

$$
\boxed{
\text{weak state mode}
\Longleftrightarrow
\text{nearly redundant protocol mode}.
}
$$

---

# 213. 平行增加协议与串行后处理

## 213.1 平行观察

设两个观察算子为

$$
M_1:V\to Y_1,
\qquad
M_2:V\to Y_2.
$$

联合观察为

$$
M_{\parallel}v
=
(M_1v,M_2v).
$$

则

$$
\boxed{
\ker M_{\parallel}
=
\ker M_1\cap\ker M_2,
}
$$

以及

$$
\boxed{
W_{\parallel}
=
M_{\parallel}^*M_{\parallel}
=
W_1+W_2.
}
$$

所以真正增加新实验是把正半定信息算子相加。

## 213.2 串行后处理

设现有观察之后执行线性后处理

$$
B:Y\to Z.
$$

新观察为

$$
M'=BM.
$$

则

$$
\boxed{
\ker M
\subseteq
\ker(BM).
}
$$

后处理只能保持或扩大不可见 kernel。

其 Gramian 为

$$
W'
=
M^*B^*BM.
$$

若 $B$ 是 contraction：

$$
B^*B\le I,
$$

则

$$
\boxed{
W'\le W.
}
$$

## 定理 213.1（无损后处理判据）

$$
\ker(BM)=\ker M
$$

当且仅当 $B$ 在 $\operatorname{ran}M$ 上单射。

## 统一结论

$$
\boxed{
\begin{aligned}
\text{parallel new evidence}
&\Rightarrow
W\text{ 相加，kernel 可缩小};\\
\text{serial postprocessing}
&\Rightarrow
W\text{ 收缩，kernel 不能缩小}.
\end{aligned}
}
$$

这给出了“新实验”和“对旧数据做更复杂计算”的严格分界。

---

# 214. 目标可估计性与最小范数协议合成

设目标是线性泛函

$$
t:V\to\mathbb F.
$$

由 Riesz 表示，存在向量 $v_t\in V$ 使

$$
t(x)=\langle v_t,x\rangle.
$$

## 定理 214.1（目标可观测性四重等价）

以下条件等价：

$$
\text{(i)}
\quad
t(x)\text{ 由 }Mx\text{ 唯一决定};
$$

$$
\text{(ii)}
\quad
\ker M\subseteq\ker t;
$$

$$
\text{(iii)}
\quad
v_t\in\operatorname{ran}M^*;
$$

$$
\text{(iv)}
\quad
\exists a\in Y,\quad M^*a=v_t.
$$

此时

$$
\boxed{
t(x)=\langle a,Mx\rangle.
}
$$

### 证明

目标由观察结果决定，当且仅当它在每个观察 fiber 上常值，即在 $\ker M$ 上为零。有限维正交对偶给出

$$
(\ker M)^\perp
=
\operatorname{ran}M^*.
$$

其余等价显然。∎

## 定义 214.1（最小范数合成）

在所有满足

$$
M^*a=v_t
$$

的系数中，令 $a_*$ 为最小范数解。

则

$$
a_*
=
(M^*)^\dagger v_t
=
M(M^*M)^\dagger v_t.
$$

## 定理 214.2（目标估计成本）

$$
\boxed{
\|a_*\|^2
=
\left\langle
v_t,
W_X^\dagger v_t
\right\rangle.
}
$$

若观察噪声为各向同性：

$$
y=Mx+\eta,
\qquad
\operatorname{Cov}(\eta)=\sigma^2I,
$$

则所有无偏线性估计器中，最小方差为

$$
\boxed{
\sigma^2
\left\langle
v_t,W_X^\dagger v_t
\right\rangle.
}
$$

## 推论 214.1

“目标属于可见 span”只回答能否估计；伪逆二次型回答估计有多脆弱：

$$
\boxed{
\text{exact target visibility}
+
\text{target-specific condition cost}.
}
$$

---

# 215. 实验选择的体积目标与最弱方向目标

设每个候选协议 $p$ 贡献正半定算子

$$
G_p\ge0.
$$

对协议集 $S$ 定义带正则的信息算子：

$$
W_S
=
\lambda I+\sum_{p\in S}G_p,
\qquad
\lambda>0.
$$

## 定义 215.1（对数体积信息）

$$
F(S)
=
\log\det W_S-\log\det(\lambda I).
$$

## 定理 215.1（单调次模性）

$F$ 是单调次模函数：

$$
A\subseteq B
\Longrightarrow
F(A\cup\{p\})-F(A)
\ge
F(B\cup\{p\})-F(B).
$$

### 证明概要

边际收益可写为

$$
\log\det
\left(
I+
G_p^{1/2}W_A^{-1}G_p^{1/2}
\right).
$$

由

$$
W_A\le W_B
$$

得到

$$
W_A^{-1}\ge W_B^{-1}.
$$

而 $\log\det(I+X)$ 对正半定序单调，因此边际收益递减。∎

## 解释

$\log\det$ 衡量的是整体可见椭球体积。已有协议越多，一个新协议通常提供的独立体积越少。

## 严格边界 215.1（最小特征值不是一般次模的）

令

$$
G_1=
\begin{bmatrix}
1&0\\
0&0
\end{bmatrix},
\qquad
G_2=
\begin{bmatrix}
0&0\\
0&1
\end{bmatrix}.
$$

定义

$$
g(S)=
\lambda_{\min}
\left(
\sum_{p\in S}G_p
\right).
$$

则

$$
g(\varnothing)=g(\{1\})=g(\{2\})=0,
$$

但

$$
g(\{1,2\})=1.
$$

因此对

$$
A=\varnothing,
\qquad
B=\{1\},
\qquad
p=2,
$$

边际增益分别为 $0$ 与 $1$，违反次模的边际递减条件。

所以：

$$
\boxed{
\text{整体体积优化}
\neq
\text{最弱方向优化}.
}
$$

针对特定目标 residual，应直接提升投影 Gramian 的最小特征值，而不能只最大化总信息体积。

---

# 216. 度量富化观察者

设 law carrier $\Lambda$ 带有有界度量

$$
d_\Lambda\le1.
$$

## 定义 216.1（状态观察伪度量）

$$
\boxed{
d_X(x,y)
=
\sup_{p\in P}
d_\Lambda(e(x,p),e(y,p)).
}
$$

## 定义 216.2（协议响应伪度量）

$$
\boxed{
d_P(p,q)
=
\sup_{x\in X}
d_\Lambda(e(x,p),e(x,q)).
}
$$

## 定理 216.1

$d_X$ 与 $d_P$ 均为伪度量。

并且：

$$
d_X(x,y)=0
\iff
xK_Xy,
$$

$$
d_P(p,q)=0
\iff
pK_Pq.
$$

所以精确双外延商正是这两个伪度量的零距离商。

## 定理 216.2（最小支配性）

$d_X$ 是使全部协议读出成为 $1$-Lipschitz 映射的最小伪度量。

即若另一个伪度量 $\delta_X$ 满足

$$
d_\Lambda(e(x,p),e(y,p))
\le
\delta_X(x,y)
$$

对所有 $p$ 成立，则

$$
\boxed{
d_X(x,y)\le\delta_X(x,y).
}
$$

协议侧同理。

## 结论 216.1

精确 kernel 只保留零与非零。度量富化则保留完整可区分强度：

$$
\boxed{
\text{kernel}
=
\text{observer metric 的零层}.
}
$$

---

# 217. 近似 kernel 与超度量闭包

给定协议族 $Q\subseteq P$，定义

$$
d_Q(x,y)
=
\sup_{p\in Q}
d_\Lambda(e(x,p),e(y,p)).
$$

## 定义 217.1（$\varepsilon$-不可区分关系）

$$
K_Q^\varepsilon
=
\{(x,y):d_Q(x,y)\le\varepsilon\}.
$$

一般度量情形下，$K_Q^\varepsilon$ 未必传递，但满足精确的加法组合律：

## 定理 217.1

$$
\boxed{
K_Q^\varepsilon
\circ
K_Q^\delta
\subseteq
K_Q^{\varepsilon+\delta}.
}
$$

### 证明

若

$$
d_Q(x,y)\le\varepsilon,
\qquad
d_Q(y,z)\le\delta,
$$

则由三角不等式

$$
d_Q(x,z)
\le
d_Q(x,y)+d_Q(y,z)
\le
\varepsilon+\delta.
$$

∎

## 定理 217.2（超度量阈值闭合）

若 $d_\Lambda$ 是超度量：

$$
d(a,c)
\le
\max\{d(a,b),d(b,c)\},
$$

则 $d_Q$ 也是超度量，并且对每个 $\varepsilon$：

$$
\boxed{
K_Q^\varepsilon
\text{ 是等价关系}.
}
$$

### 解释

普通噪声几何产生“容差逐步累积”；超度量几何产生真正的嵌套观察分块：

$$
\varepsilon_1\le\varepsilon_2
\Longrightarrow
K_Q^{\varepsilon_1}
\subseteq
K_Q^{\varepsilon_2}.
$$

这正适合 $p$-进精度观察：同一精度阈值内的不可区分关系天然传递。

---

# 218. 素数观察者的规范加权度量

考虑隐藏素数地址空间

$$
K_\infty
=
\prod_{p\in\mathbb P}\mathbb Z_p.
$$

在每个坐标上使用标准 $p$-进度量：

$$
d_p(u_p,v_p)
=
p^{-v_p(u_p-v_p)},
$$

约定

$$
p^{-\infty}=0.
$$

令

$$
Z_{\mathbb P}(s)
=
\sum_{p\in\mathbb P}p^{-s},
\qquad
s>1.
$$

## 定义 218.1（zeta 加权素数观察度量）

$$
\boxed{
D_s(u,v)
=
\frac1{Z_{\mathbb P}(s)}
\sum_{p\in\mathbb P}
p^{-s}d_p(u_p,v_p).
}
$$

## 定理 218.1

$D_s$ 是 $K_\infty$ 上的度量，并诱导乘积拓扑。

### 证明概要

正定性来自每个权重严格为正。若 $D_s(u_n,u)\to0$，则对任意固定 $p$：

$$
p^{-s}d_p((u_n)_p,u_p)
\le
Z_{\mathbb P}(s)D_s(u_n,u),
$$

故每个坐标收敛。

反向，给定 $\varepsilon>0$，先选有限素数集 $F$ 使尾权重和小于 $\varepsilon/2$；再令有限多个坐标足够接近，使有限部分小于 $\varepsilon/2$。∎

## 定义 218.2（有限精度局部度量）

只读取模 $p^K$ 时，定义

$$
d_p^{(K)}(u,v)
=
\begin{cases}
d_p(u,v),&u\not\equiv v\pmod{p^K},\\
0,&u\equiv v\pmod{p^K}.
\end{cases}
$$

则

$$
0\le
d_p(u,v)-d_p^{(K)}(u,v)
\le
p^{-K}.
$$

## 定理 218.2（有限 prime–precision 窗口误差）

给定有限素数集 $F$ 和每个 $p\in F$ 的精度 $K_p$，定义

$$
D_{s,F,K}(u,v)
=
\frac1{Z_{\mathbb P}(s)}
\sum_{p\in F}
p^{-s}d_p^{(K_p)}(u_p,v_p).
$$

则一致误差满足：

$$
\boxed{
0
\le
D_s-D_{s,F,K}
\le
\frac{
\displaystyle
\sum_{p\notin F}p^{-s}
+
\sum_{p\in F}p^{-(s+K_p)}
}{
Z_{\mathbb P}(s)
}.
}
$$

## 最深解释 218.1

这给出一个严格的有限观察预算：

* 新增素数，减少横向 tail；
* 增加 $K_p$，减少纵向精度误差；
* $s$ 决定远素数方向的预算折扣。

这里的 $s$ 是观察度量权重参数；本定理不赋予任何特殊 $s$ 值以 RH 或物理临界意义。

---

# 219. 紧致状态空间的局部—全局实现定理

令

$$
\Sigma:X\to\prod_{p\in P}\Lambda_p
$$

为完整行为映射：

$$
\Sigma(x)_p=e_p(x).
$$

假设：

1. $X$ 紧致；
2. 每个 $\Lambda_p$ 是 Hausdorff 空间；
3. 每个 $e_p$ 连续。

## 定理 219.1（行为像闭性）

$$
\boxed{
\Sigma(X)
\text{ 在 }
\prod_{p\in P}\Lambda_p
\text{ 中紧致且闭}.
}
$$

### 证明

$\Sigma$ 作为逐坐标连续映射是连续的。紧致空间的连续像紧致；Hausdorff 空间中的紧致子集闭。∎

## 定理 219.2（有限一致性推出全局实现）

给定形式行为签名

$$
\lambda=(\lambda_p)_{p\in P}.
$$

若对每个有限协议集

$$
F\subseteq P
$$

都存在某个 $x_F\in X$ 满足

$$
e_p(x_F)=\lambda_p
\qquad
\forall p\in F,
$$

则存在单一全局状态 $x\in X$ 满足

$$
\boxed{
e_p(x)=\lambda_p
\qquad
\forall p\in P.
}
$$

### 证明

对每个 $p$ 定义闭集

$$
C_p
=
\{x\in X:e_p(x)=\lambda_p\}.
$$

有限一致性正是这些闭集具有有限交性质。由 $X$ 紧致：

$$
\bigcap_{p\in P}C_p\neq\varnothing.
$$

∎

## 结论 219.1

在紧致连续模型中：

$$
\boxed{
\text{每个有限窗口都可实现}
\Longrightarrow
\text{完整无限行为可实现}.
}
$$

这为以下对象提供共同实现原则：

* 有限维量子态上的无限效果期望表；
* profinite／$p$-进逆极限状态；
* 紧致动力系统的无限时间读出；
* 紧致参数模型的全部实验协议。

---

# 220. 非紧致条件下的幽灵行为

紧致性不是装饰条件。

令

$$
X=\mathbb N,
$$

并定义协议

$$
p_n(x)
=
\mathbf1_{\{x\ge n\}}.
$$

考虑形式签名

$$
\lambda_n=1
\qquad
\forall n.
$$

对任意有限协议集

$$
\{p_{n_1},\ldots,p_{n_k}\},
$$

取

$$
x\ge\max_i n_i
$$

即可实现全部有限约束。

但不存在自然数 $x$ 满足

$$
x\ge n
\qquad
\forall n\in\mathbb N.
$$

所以完整签名不可实现。

## 结论 220.1

存在：

$$
\boxed{
\text{每个有限观察窗口都像真实状态，}
\quad
\text{但无限联合后没有任何真实状态实现。}
}
$$

称此类对象为**幽灵行为**或**理想边界行为**。

它可能位于：

$$
\overline{\Sigma(X)}
\setminus
\Sigma(X).
$$

因此必须严格区分：

$$
\boxed{
\text{有限可满足}
\neq
\text{全局可实现},
}
$$

除非存在紧致性、饱和性或其他有限交原理。

---

# 221. 非可实现行为的有限线性见证

现在假设：

* $X$ 是紧致凸集；
* 每个协议输出为实数；
* 每个 $e_p:X\to\mathbb R$ 连续且仿射。

则

$$
\Sigma(X)
\subseteq
\mathbb R^P
$$

是紧致凸集，其中 $\mathbb R^P$ 使用乘积拓扑。

## 定理 221.1（有限 no-go 证书）

若形式签名

$$
y\in\mathbb R^P
$$

不属于可实现像：

$$
y\notin\Sigma(X),
$$

则存在有限协议

$$
p_1,\ldots,p_m
$$

和实系数

$$
c_1,\ldots,c_m
$$

使

$$
\boxed{
\sum_{i=1}^m c_i y_{p_i}
>
\sup_{x\in X}
\sum_{i=1}^m c_i e_{p_i}(x).
}
$$

### 证明

$\Sigma(X)$ 是闭凸集，故可由连续线性泛函与外部点严格分离。乘积拓扑上任意连续线性泛函只依赖有限多个坐标，因此分离泛函必具有上述有限形式。∎

## 解释

无限协议表不真实时，总存在一个有限实验不等式揭示其不真实。

这种证书类型统一了：

* Bell 型线性不等式；
* 上下文兼容性不等式；
* 边缘问题的线性 witness；
* 矩与概率表的不可实现证书；
* 有限协议组合的 no-go inequality。

这里统一的是**证书结构**，不是说这些理论的物理内容相同。

## 推论 221.1

在有限维量子理论中，若一张完整效果期望表不来自任何密度矩阵，则存在有限个效果和一个线性不等式证明其不可实现。

---

# 222. 可实现像的定量距离

在有限维行为坐标空间中，令

$$
I=\Sigma(X)
$$

为非空闭凸可实现像。固定范数 $|\cdot|$，其对偶范数记为 $|\cdot|_*$。

定义支持函数：

$$
h_I(c)
=
\sup_{z\in I}\langle c,z\rangle.
$$

## 定理 222.1（距离—见证对偶）

对任意形式签名 $y$：

$$
\boxed{
\operatorname{dist}(y,I)
=
\sup_{\|c\|_*\le1}
\left[
\langle c,y\rangle-h_I(c)
\right].
}
$$

## 解释

右侧的最优 $c$ 是归一化 no-go witness；其违反量正好等于 $y$ 到真实行为像的距离。

因此可以定义：

$$
\boxed{
\operatorname{RealizationDefect}(y)
=
\operatorname{dist}(y,\Sigma(X)).
}
$$

它不只回答“是否可实现”，还回答“离最近真实模型有多远”。

## 定理 222.2（后处理收缩）

设线性后处理

$$
B:Y\to Z.
$$

则

$$
\boxed{
\operatorname{dist}(By,B(I))
\le
\|B\|\,
\operatorname{dist}(y,I).
}
$$

特别地，若 $|B|\le1$：

$$
\operatorname{RealizationDefect}(By)
\le
\operatorname{RealizationDefect}(y).
$$

所以规范化的串行后处理不能增强对上游不一致性的区分能力。

---

# 223. 动力系统的双侧最小实现

设动作字母表为 $A$，每个动作给出

$$
F_a:X\to X,
$$

基础读出为

$$
q:X\to O.
$$

对词

$$
w=a_1\cdots a_n
$$

定义

$$
F_w
=
F_{a_n}\circ\cdots\circ F_{a_1}.
$$

## 定义 223.1（完整控制行为）

$$
\beta(x)(w)
=
q(F_wx).
$$

定义最小行为状态空间：

$$
Q_\infty
=
\operatorname{Im}\beta.
$$

## 定理 223.1（行为更新良定义）

对每个动作 $a$，定义

$$
\beta(x)\cdot a
=
\beta(F_ax).
$$

该更新只依赖 $\beta(x)$，与代表状态无关。

### 证明

若

$$
\beta(x)=\beta(y),
$$

则对任意未来词 $w$：

$$
q(F_wF_ax)
=
\beta(x)(aw)
=
\beta(y)(aw)
=
q(F_wF_ay).
$$

故

$$
\beta(F_ax)=\beta(F_ay).
$$

∎

因此自由幺半群 $A^*$ 在 $Q_\infty$ 上作用。

## 定义 223.2（协议词同余）

$$
u\equiv_{\mathrm{act}}v
\iff
\forall z\in Q_\infty,
\quad
z\cdot u=z\cdot v.
$$

## 定理 223.2

$\equiv_{\mathrm{act}}$ 是 $A^*$ 上的双边幺半群同余。

因此可定义有效协议作用幺半群：

$$
\boxed{
M_{\mathrm{eff}}
=
A^*/{\equiv_{\mathrm{act}}}.
}
$$

它在 $Q_\infty$ 上忠实作用。

## 最深结构 223.1

动力观察者存在两个规范最小对象：

$$
\boxed{
Q_\infty
=
\text{最小未来行为状态空间},
}
$$

$$
\boxed{
M_{\mathrm{eff}}
=
\text{最小忠实协议作用幺半群}.
}
$$

前者删除重复状态历史；后者删除重复控制词。

---

# 224. 随机 instrument 的预测状态完成

静态协议只给一步 law。若协议会改变状态，则必须研究全部未来 transcript。

设 $\mathcal H$ 为可达历史集合，$W$ 为未来协议词集合。对历史 $h$ 与未来词 $w$，记未来记录 law 为

$$
\mathsf L(h,w).
$$

## 定义 224.1（预测等价）

$$
h\sim_{\mathrm{pred}}h'
\iff
\forall w,
\quad
\mathsf L(h,w)=\mathsf L(h',w).
$$

## 定义 224.2（预测状态）

$$
\Psi(h)
=
\bigl(\mathsf L(h,w)\bigr)_{w\in W}.
$$

定义预测状态空间：

$$
\boxed{
S_{\mathrm{pred}}
=
\operatorname{Im}\Psi.
}
$$

## 定理 224.1（条件更新良定义）

在有限或离散 law 情形，若历史 $h,h'$ 预测等价，并且动作 $a$ 后结果 $y$ 的概率为正，则条件化后的历史

$$
hay,
\qquad
h'ay
$$

仍具有相同未来预测状态。

### 证明

对任意后续事件 $z$：

$$
P(z\mid h,a,y,w)
=
\frac{
P(y,z\mid h,a,w)
}{
P(y\mid h,a)
}.
$$

预测等价保证分子与分母分别相同，所以条件 law 相同。∎

## 定理 224.2（预测状态的普适最小性）

若另一个历史接口

$$
r:\mathcal H\to R
$$

能够决定全部未来 transcript law，则存在唯一映射

$$
\overline r:\operatorname{Im}r\to S_{\mathrm{pred}}
$$

使

$$
\Psi=\overline r\circ r.
$$

所以 $S_{\mathrm{pred}}$ 是全部未来实验预测所需的最粗历史状态。

## 严格结论 224.1

$$
\boxed{
\text{相同一步输出 law}
\not\Rightarrow
\text{相同顺序协议行为}.
}
$$

只有完整 transcript law 相同，才可以安全地把两个 instrument 或历史合并。

---

# 225. 预测商、风险商与决策商

预测状态通常仍比具体任务需要的信息更细。

设 $\mathcal L$ 是损失函数族。对历史 $h$、动作 $a$ 与损失 $\ell$，定义风险

$$
R_{\ell,a}(h)
=
\mathbb E_{\Psi(h)}
[\ell(a,Y)].
$$

## 定义 225.1（风险等价）

$$
h\sim_{\mathrm{risk}}h'
\iff
\forall \ell\in\mathcal L,\ \forall a,
\quad
R_{\ell,a}(h)=R_{\ell,a}(h').
$$

## 定义 225.2（最优集合等价）

$$
h\sim_{\mathrm{opt}}h'
$$

当且仅当所有任务下的最优动作集合相同。

## 定理 225.1（商层级）

$$
\boxed{
K_{\mathrm{pred}}
\subseteq
K_{\mathrm{risk}}
\subseteq
K_{\mathrm{opt}}.
}
$$

### 原因

相同完整预测 law 必然产生相同全部期望损失；相同风险向量必然产生相同最优集合。

反向一般不成立：

* 不同 law 可能对给定损失族具有相同期望；
* 不同风险数值可能仍具有相同 argmin。

## 定理 225.2（任务族分离判据）

若 $\mathcal L$ 对允许 law 是 measure-determining 的，即任意不同 law 总能被某个损失函数区分，则

$$
\boxed{
K_{\mathrm{pred}}
=
K_{\mathrm{risk}}.
}
$$

有限结果空间中，包含全部事件指示函数的损失族可以分离全部概率 law。

## 结论 225.1

观察者状态不存在脱离任务的唯一“最小充分状态”。存在一条任务相关压缩链：

$$
\boxed{
\text{完整历史}
\longrightarrow
\text{预测状态}
\longrightarrow
\text{风险状态}
\longrightarrow
\text{最优行动状态}.
}
$$

---

# 226. 双外延不等于自描述完备

双外延只保证：

* 不同状态具有不同响应行；
* 不同协议具有不同响应列。

它不保证协议空间能够表示任意状态函数。

## 定义 226.1（响应函数完备）

称评价

$$
e:X\times P\to\Lambda
$$

在协议侧响应完备，若对每个函数

$$
f:X\to\Lambda
$$

都存在协议 $p_f\in P$ 使

$$
e(x,p_f)=f(x)
\qquad
\forall x.
$$

## 定理 226.1（有限计数障碍）

若

$$
|X|=n\ge1,
\qquad
|\Lambda|=k\ge2,
$$

则响应完备要求

$$
\boxed{
|P/K_P|
\ge
k^n.
}
$$

### 证明

不同函数 $f:X\to\Lambda$ 必须由扩展上不同的协议列表示，而此类函数共有 $k^n$ 个。∎

## 推论 226.1（有限自容纳不可能）

若协议必须由状态内部索引，并满足

$$
|P|\le|X|=n,
$$

则响应完备不可能，因为

$$
k^n>n
\qquad
(k\ge2,n\ge1).
$$

## 定理 226.2（固定点自由对角障碍）

设

$$
P=X,
$$

且存在无不动点函数

$$
\delta:\Lambda\to\Lambda.
$$

若评价弱点满射，即每个

$$
f:X\to\Lambda
$$

都可写成某一列

$$
f(x)=e(x,p),
$$

则产生矛盾。

### 证明

定义

$$
g(x)
=
\delta(e(x,x)).
$$

由弱点满射，存在 $p$ 使

$$
e(x,p)=g(x)
$$

对所有 $x$ 成立。取 $x=p$：

$$
e(p,p)
=
g(p)
=
\delta(e(p,p)),
$$

这与 $\delta$ 无不动点矛盾。∎

## 结论 226.1

必须区分：

$$
\boxed{
\text{外延完备}
=
\text{现有对象互不重复},
}
$$

与

$$
\boxed{
\text{表达完备}
=
\text{所有可能响应函数均可表示}.
}
$$

前者可以成立；后者在自评价和固定点自由反转存在时必然失败。

---

# 227. 四种完成及其非交换性

统一观察者至少包含四种不同操作。

## 227.1 外延完成

$$
E(\mathfrak O)
=
(\overline X,\overline P,\overline e).
$$

删除重复状态和重复协议。

## 227.2 动力完成

$$
C_A(P_0)
=
\{p\circ F_w:p\in P_0,\ w\in A^*\}.
$$

加入全部未来或干预上下文。

## 227.3 行为像限制

$$
I(\mathfrak O)
=
\Sigma(X).
$$

删除不能由任何真实状态实现的形式记录。

## 227.4 极限完成

$$
L(\mathfrak O)
=
\overline{\Sigma(X)}.
$$

加入可由真实行为逼近、但未必由真实状态实现的理想行为。

## 定理 227.1（连续动力保持行为闭包）

设行为空间 $B$ 上的动作

$$
S_a:B\to B
$$

连续，并且

$$
S_a(\Sigma(X))
\subseteq
\Sigma(X).
$$

则

$$
\boxed{
S_a(\overline{\Sigma(X)})
\subseteq
\overline{\Sigma(X)}.
}
$$

### 证明

连续映射满足

$$
S_a(\overline I)
\subseteq
\overline{S_a(I)}
\subseteq
\overline I.
$$

∎

所以在连续条件下，理想极限行为自动继承动力学。

## 严格边界 227.1

若动作不连续，真实行为像可以动力不变，而其闭包不再不变。

例如令

$$
I=\{1/n:n\ge1\}\subset\mathbb R,
$$

定义

$$
F(1/n)=1,
\qquad
F(0)=\sqrt2.
$$

则

$$
F(I)\subseteq I,
$$

但

$$
0\in\overline I,
\qquad
F(0)\notin\overline I.
$$

## 原理 227.1（静态协议商与顺序完成）

若协议只是固定状态空间上的普通读出函数，则静态相等协议在预复合动力学后仍相等。

但若协议是 instrument，静态结果边缘相同不保证状态干预相同。因此：

$$
\boxed{
\text{先按一步 POVM quotient}
\quad\text{再做顺序 closure}
}
$$

可能错误地合并两个顺序行为不同的 instrument。

正确顺序应是：

$$
\boxed{
\text{先生成完整 transcript semantics}
\longrightarrow
\text{再按完整行为 quotient}.
}
$$

---

# 228. 本增订得到的新结构结论

## 结论 228.1（协议新颖性的精确标准）

$$
\boxed{
p\text{ 真正新增认识}
\iff
p\notin\Pi(K(Q)).
}
$$

## 结论 228.2（观察困难的双侧谱来源）

$$
\boxed{
\text{难以看见的状态方向}
\iff
\text{近乎冗余的协议组合}.
}
$$

二者由 $M^*M$ 与 $MM^*$ 的共同非零谱刻画。

## 结论 228.3（目标知识等于协议线性可合成性）

$$
\boxed{
t\text{ 在观察商上良定义}
\iff
t\in\operatorname{ran}M^*.
}
$$

## 结论 228.4（无限不一致具有有限 witness）

在紧致凸仿射模型中：

$$
\boxed{
y\notin\Sigma(X)
\Longrightarrow
\exists\text{ 有限协议线性不等式证书}.
}
$$

## 结论 228.5（素数观察具有统一有限逼近率）

$$
\boxed{
\text{全 prime–precision 观察误差}
\le
\text{prime tail}
+
\text{precision tail}.
}
$$

## 结论 228.6（动力观察者有两个最小对象）

$$
\boxed{
\text{minimal behavior state}
+
\text{minimal faithful protocol monoid}.
}
$$

## 结论 228.7（自描述障碍发生在表达像而非外延 kernel）

一个观察者可以没有重复状态、没有重复协议，却仍不能表示自己的全部可能响应函数。

因此：

$$
\boxed{
\text{kernel closure}
\not\Rightarrow
\text{image surjectivity}
\not\Rightarrow
\text{self-description completeness}.
}
$$

---

# 229. 建议 Lean 模块树

```text
D5/S3/Observer/ProtocolEvaluation/
  HomogeneousEvaluation.lean
  StateRowProtocolColumn.lean
  DualObserver.lean
  BiextensionalCollapse.lean
  BiextensionalUniversalProperty.lean

D5/S3/Observer/ProtocolEvaluation/Galois/
  DistinctionKernel.lean
  RelationProtocolGalois.lean
  ProtocolSemanticClosure.lean
  ProtocolNoveltyCriterion.lean
  ClosedObserverConcept.lean

D5/S3/Observer/ProtocolEvaluation/Finite/
  FiniteProtocolCompression.lean
  OutputCapacityLowerBound.lean
  AdaptiveSeparationTree.lean

D5/S3/Observer/ProtocolEvaluation/Linear/
  LinearObservationOperator.lean
  StateGramOperator.lean
  ProtocolGramOperator.lean
  DualNonzeroSpectrum.lean
  ParallelObservation.lean
  SerialPostprocessing.lean
  TargetObservableSynthesis.lean
  MinimumNormEstimator.lean
  LogDetSubmodular.lean
  MinEigenvalueNotSubmodular.lean

D5/S3/Observer/ProtocolEvaluation/Metric/
  CanonicalStatePseudometric.lean
  CanonicalProtocolPseudometric.lean
  ApproximateKernelComposition.lean
  UltrametricThresholdEquivalence.lean

D5/S3/Observer/PrimeMetric/
  WeightedPadicObserverMetric.lean
  ProductTopologyEquivalence.lean
  FinitePrimeTailBound.lean
  FinitePrecisionTailBound.lean

D5/S3/Observer/Realization/
  CompactBehaviorImage.lean
  FiniteConsistencyRealization.lean
  NoncompactGhostBehavior.lean
  FiniteLinearNoGoWitness.lean
  RealizationDistanceDuality.lean
  PostprocessingDefectContraction.lean

D5/S3/Observer/DynamicMinimality/
  ControlledBehaviorImage.lean
  EffectiveProtocolCongruence.lean
  FaithfulProtocolMonoid.lean
  PredictiveStateImage.lean
  ConditionalPredictiveUpdate.lean
  TaskRelativeDecisionQuotient.lean

D5/S3/Observer/SelfReference/
  ResponseCompletenessCardinality.lean
  FiniteInternalProtocolNoGo.lean
  FixedPointFreeSelfEvaluation.lean
  BiextensionalNotSelfComplete.lean
```

建议优先闭合的低依赖定理：

```text
protocol_mem_semanticClosure_iff_kernel_unchanged
finite_protocol_subfamily_card_le_quotientCard_sub_one
protocol_output_capacity_lower_bound
dualGram_nonzeroSpectrum_eq
parallelGram_eq_add
serialPostprocessing_gram_le
targetObservable_iff_mem_range_adjoint
canonicalObserverPseudometric_kernel
ultrametric_threshold_is_equivalence
weightedPadicMetric_finiteWindow_error
compact_finiteConsistency_realizable
noncompact_finitelyRealizable_not_realizable
effectiveProtocolWord_setoid
responseComplete_card_lower_bound
fixedPointFree_forbids_weakPointSurjective_selfEvaluation
```

---

# 230. 追加严格非主张

1. 本增订不声称双外延坍缩、Galois 连接、奇异值分解或紧致性原理本身是新数学概念。
2. 本增订的新内容是把它们组织为同一个 typed observer calculus，并推导其跨算术、动力、量子和策略层后果。
3. 本增订不声称协议 Galois 闭包可以自动计算；无限协议族的闭包成员问题可能不可判定。
4. 本增订不声称 $r-1$ 协议上界在噪声、重复采样或物理扰动条件下仍是样本复杂度界。
5. 本增订不声称输出容量下界自动可达。
6. 本增订不声称 Gramian 大迹或大行列式保证每个目标方向稳定。
7. 本增订不声称最小特征值目标一般具有次模性。
8. 本增订不声称线性协议组合总能作为物理可执行协议实现。
9. 本增订不声称 Moore–Penrose 合成系数自动满足正性、概率归一化或量子 CP 条件。
10. 本增订不声称普通度量的 $\varepsilon$-kernel 是等价关系。
11. 本增订不声称 zeta 加权素数度量选出的 $s$ 具有 RH 临界意义。
12. 本增订不声称紧致性是有限一致性推出全局实现的唯一可能条件；它是一个清晰充分条件。
13. 本增订不声称任意非凸行为像外部点都具有分离原像本身的单一线性 witness；有限 witness 定理使用凸性。
14. 本增订不声称理想闭包中的每个行为都对应物理状态。
15. 本增订不声称预测状态等于意识、体验或第一人称自我。
16. 本增订不声称决策商保留所有规范理由；它只保留指定损失族所需的信息。
17. 本增订不声称有效协议幺半群唯一决定实际 policy。
18. 本增订不声称静态 POVM 等价足以推出 instrument 等价。
19. 本增订不声称双外延性等于表达满射性。
20. 本增订不声称固定点自由自评价障碍证明量子随机性、自由意志或本体非决定论。
21. 本增订不声称有限自描述计数障碍直接推广到任意无限基数而无需额外集合论分析。
22. 本增订不修改此前关于 RH、negative-base-$\varphi$、意识坍缩和强本体自由的严格边界。

---

# 231. 最终统一：观察者是状态与协议共同压缩出的评价核心

给定同质评价网

$$
e:X\times P\to\Lambda,
$$

存在两个外延 kernel：

$$
K_X
=
\{(x,y):\forall p,\ e(x,p)=e(y,p)\},
$$

$$
K_P
=
\{(p,q):\forall x,\ e(x,p)=e(x,q)\}.
$$

其规范双外延核心为

$$
\boxed{
\overline e:
(X/K_X)\times(P/K_P)
\longrightarrow\Lambda.
}
$$

协议子集与状态关系之间存在反序 Galois 连接：

$$
\boxed{
Q\subseteq\Pi(R)
\iff
R\subseteq K(Q).
}
$$

因此：

$$
\boxed{
\text{协议新颖性}
=
\text{是否严格缩小状态 kernel}.
}
$$

在线性情形中，评价网压缩为观察算子

$$
M:V\to Y,
$$

其双 Gram 几何满足

$$
\boxed{
W_X=M^*M,
\qquad
W_P=MM^*,
}
$$

以及

$$
\boxed{
\operatorname{Spec}_{>0}(W_X)
=
\operatorname{Spec}_{>0}(W_P).
}
$$

在度量情形中：

$$
\boxed{
d_X(x,y)
=
\sup_p d_\Lambda(e(x,p),e(y,p))
}
$$

把精确不可区分 kernel 提升为连续可见几何。

在实现层：

$$
\boxed{
\mathcal I_{\mathfrak O}
=
\Sigma(X)
\subseteq
\prod_p\Lambda_p
}
$$

记录哪些形式行为真正来自状态；紧致性保证有限一致行为可以胶合，凸性保证非实现行为具有有限线性 witness。

在动力层：

$$
\boxed{
Q_\infty
=
\operatorname{Im}
\left[
x\mapsto(q(F_wx))_{w\in A^*}
\right]
}
$$

是最小未来行为状态，而

$$
\boxed{
M_{\mathrm{eff}}
=
A^*/{\equiv_{\mathrm{act}}}
}
$$

是最小忠实协议作用幺半群。

在决策层：

$$
\boxed{
K_{\mathrm{pred}}
\subseteq
K_{\mathrm{risk}}
\subseteq
K_{\mathrm{opt}}.
}
$$

在自指层，双外延只能消除重复行列；它不能使评价网表示所有自身响应函数。若 law carrier 存在无不动点反转，则普遍自评价必遭遇对角逃逸。

因此，统一观察者理论进一步收束为：

$$
\boxed{
\begin{aligned}
\text{State quotient}
&=
\text{删除协议无法区分的状态差异},\\
\text{Protocol quotient}
&=
\text{删除状态无法区分的协议差异},\\
\text{Galois closure}
&=
\text{识别已经被当前区分结构语义蕴含的协议},\\
\text{Observer spectrum}
&=
\text{量化状态脆弱方向与协议冗余方向的共同强度},\\
\text{Behavior image}
&=
\text{区分形式记录与真实可实现记录},\\
\text{Dynamic realization}
&=
\text{把未来协议结果闭合为最小预测状态},\\
\text{Self boundary}
&=
\text{标记外延完成仍无法跨越的表达与对角极限}.
\end{aligned}
}
$$

最终的核心公式不再只是

$$
\text{state}\times\text{protocol}\to\text{law},
$$

而是：

$$
\boxed{
\frac{\text{states}}{\text{identical rows}}
\;\times\;
\frac{\text{protocols}}{\text{identical columns}}
\longrightarrow
\text{realizable laws},
}
$$

并由动力闭包、度量闭包与预测闭包继续作用。

最短的理论判词是：

$$
\boxed{
观察者不是单方面压缩世界的接口；
观察者是世界状态与可执行问题相互区分、相互去重、
并在真实行为像中共同闭合后形成的评价核心。
}
$$
先纠正一个执行状态：上一轮所称“已提交 PR”并未实际成功。状态文件记录的是 `success: False`，失败原因为 GitHub CLI 未安装。以下内容只作为继续发展的 paper-level 理论，不把它声称为已经进入仓库的提交。

现有稿已经把观察者定义为类型化的协议评价结构，并明确区分 Lean 锚点、纸面定理和仍需额外桥梁的研究命题。 下面从第 232 节继续。

---

# 232. 增订八：决策序、上下文像缺陷与观察—控制最小实现

此前理论的基本对象是评价网：

$$
e:X\times P\longrightarrow \Lambda .
$$

其中：

* `X` 是隐藏状态；
* `P` 是允许协议；
* `e(x,p)` 是状态 `x` 在协议 `p` 下产生的 law。

状态 kernel 为：

$$
K_P
=
\left\{
(x,y):
e(x,p)=e(y,p)
\ \text{for every }p\in P
\right\}.
$$

这个 kernel 只回答一个零误差问题：

> 两个状态是否产生完全相同的全部协议 law？

但它还没有回答：

1. 一个观察者是否能模拟另一个观察者；
2. 即使 kernel 都是对角，谁的统计决策能力更强；
3. 局部兼容记录为何可能没有全局实现；
4. 一个系统哪些状态既能被行动触达，又能被观察识别；
5. 预测状态中有多少记忆真正暴露在未来记录中。

本增订建立四条新桥：

$$
\text{kernel order}
\longrightarrow
\text{decision order}
\longrightarrow
\text{approximate deficiency},
$$

$$
\text{local records}
\longrightarrow
\text{contextual image defect},
$$

$$
\text{controllability}
+
\text{observability}
\longrightarrow
\text{minimal bidirectional state},
$$

$$
\text{past}
\longrightarrow
\text{predictive causal state}
\longrightarrow
\text{memory decomposition}.
$$

---

# 233. 双侧观察者态射

考虑两个同一 law carrier 上的观察者：

$$
\mathfrak O
=
(X,P,e),
$$

$$
\mathfrak O'
=
(X',P',e').
$$

## 定义 233.1（观察者态射）

一个态射由一对映射组成：

$$
f:X\longrightarrow X',
$$

$$
g:P'\longrightarrow P,
$$

并满足评价保持条件：

$$
e'(f(x),p')
=
e(x,g(p'))
$$

对所有 `x` 和 `p'` 成立。

这里方向具有关键不对称性：

* 状态沿 `f` 正向翻译；
* 协议沿 `g` 反向编译。

它表达：

> 目标观察者中的每一个协议，都能被源观察者中的一个协议实现，并且翻译后的状态产生完全相同的 law。

## 定理 233.1（复合）

若：

$$
(f_1,g_1):
\mathfrak O_1\longrightarrow\mathfrak O_2,
$$

$$
(f_2,g_2):
\mathfrak O_2\longrightarrow\mathfrak O_3,
$$

则复合为：

$$
(f_2\circ f_1,\ g_1\circ g_2).
$$

评价保持由两次代入立即得到。

## 定义 233.2（对偶观察者）

交换状态和协议：

$$
\mathfrak O^\vee
=
(P,X,e^\vee),
$$

其中：

$$
e^\vee(p,x)=e(x,p).
$$

于是：

$$
(\mathfrak O^\vee)^\vee
=
\mathfrak O.
$$

状态压缩和协议压缩因此不是两套理论，而是同一个双侧评价结构的对偶面。

---

# 234. 四种不同的观察者强弱关系

考虑共同隐藏参数空间 `Θ` 上的概率实验。

一个实验 `E` 给每个参数 `θ` 一个输出分布：

$$
E_\theta\in\Delta(Y).
$$

另一个实验 `F` 给出：

$$
F_\theta\in\Delta(Z).
$$

必须区分四种强弱关系。

## 234.1 Kernel 精化

定义：

$$
E\succeq_K F
$$

当且仅当：

$$
E_\theta=E_{\theta'}
\Longrightarrow
F_\theta=F_{\theta'}.
$$

等价地：

$$
K_E\subseteq K_F.
$$

它只比较哪些参数被完全合并。

## 234.2 确定性后处理

若存在函数：

$$
h:Y\longrightarrow Z
$$

使：

$$
F_\theta=h_*E_\theta,
$$

则 `F` 是 `E` 的确定性粗化。

## 234.3 随机后处理

若存在 Markov kernel：

$$
K(z\mid y)
$$

使：

$$
F_\theta(z)
=
\sum_y K(z\mid y)E_\theta(y),
$$

则记：

$$
E\succeq_B F.
$$

这称为统计模拟序或决策序。

## 234.4 近似模拟

若不存在精确 kernel `K`，仍可问 `E` 能否近似模拟 `F`。这将由 deficiency 度量。

> **Kernel 精化只记录零误差区分；随机后处理序记录全部统计决策能力。**

---

# 235. 有限 Blackwell 判据

设：

* 参数集 `Θ` 有限；
* 输出集 `Y,Z` 有限；
* 动作集 `A` 有限；
* 先验为 `π`；
* 损失函数为：

$$
\ell:\Theta\times A\longrightarrow\mathbb R.
$$

实验 `E` 下的最优 Bayes 风险定义为：

$$
R^*(E;\pi,\ell)
=
\inf_d
\sum_{\theta,y,a}
\pi(\theta)
E_\theta(y)
d(a\mid y)
\ell(\theta,a),
$$

其中 `d` 遍历所有输出到动作的随机决策规则。

## 定理 235.1（决策支配）

有限情形下，以下条件等价：

第一，`F` 是 `E` 的随机后处理：

$$
F=K\circ E.
$$

第二，对所有先验、动作集和损失函数：

$$
R^*(E;\pi,\ell)
\le
R^*(F;\pi,\ell).
$$

### 正向证明

若：

$$
F=K\circ E,
$$

那么任何基于 `F` 的决策规则，都可以由 `E` 按以下方式模拟：

1. 先用 `K` 把 `E` 的输出随机化为一个伪 `F` 输出；
2. 再执行原来的 `F` 决策规则。

所以 `E` 能做出 `F` 能做出的全部决策，最优风险不会更高。

### 反向证明概要

所有 `E` 的随机后处理构成有限维空间中的紧凸多面体。

若 `F` 不属于该多面体，则存在一个线性泛函将 `F` 与全部后处理严格分离。把该线性泛函归一化为一个先验加损失函数，就得到某个决策问题，其中 `F` 的最优风险严格低于 `E`，与假设矛盾。

## 结论 235.1

观察者的真正统计能力可以定义为：

> **它对全部决策问题能够达到的风险集合。**

这比单纯比较 kernel 严格得多。

---

# 236. Kernel 完备远弱于统计完备

取二元参数：

$$
\Theta=\{0,1\}.
$$

定义噪声实验 `E`：

$$
E_0=(0.6,0.4),
$$

$$
E_1=(0.4,0.6).
$$

定义完美实验 `F`：

$$
F_0=(1,0),
$$

$$
F_1=(0,1).
$$

两个实验都是参数单射的，因此：

$$
K_E=K_F=\Delta_\Theta.
$$

从 kernel 看，它们同样完备。

但总变差距离分别为：

$$
d_{\mathrm{TV}}(E_0,E_1)=0.2,
$$

$$
d_{\mathrm{TV}}(F_0,F_1)=1.
$$

Markov 后处理不能增加总变差距离，所以不存在随机 kernel 使：

$$
F=K\circ E.
$$

因此：

$$
E\succeq_K F,
$$

但：

$$
E\not\succeq_B F.
$$

> **Kernel 为零只表示无限精度、无限样本下原则上可区分；它不表示有限样本下同样容易区分。**

---

# 237. 观察者 deficiency

## 定义 237.1（单向 deficiency）

定义 `E` 模拟 `F` 的误差：

$$
\delta(F\mid E)
=
\inf_K
\sup_{\theta}
d_{\mathrm{TV}}
\left(
F_\theta,
K E_\theta
\right).
$$

其中 `K` 遍历所有从 `Y` 到 `Z` 的 Markov kernel。

若：

$$
\delta(F\mid E)=0,
$$

在有限情形下即表示：

$$
E\succeq_B F.
$$

## 定理 237.1（风险传输界）

若：

$$
0\le\ell\le1,
$$

则：

$$
R^*(E;\pi,\ell)
\le
R^*(F;\pi,\ell)
+
\delta(F\mid E).
$$

### 证明

选择一个使模拟误差接近 deficiency 的 `K`。

用 `E` 先模拟 `F`，再执行 `F` 的近最优决策规则。总变差误差对 `[0,1]` 有界损失的期望影响不超过相应总变差距离。取上确界及极限即得。

## 定义 237.2（双向实验距离）

$$
\Delta(E,F)
=
\max
\left\{
\delta(F\mid E),
\delta(E\mid F)
\right\}.
$$

## 定理 237.2（三角不等式）

$$
\delta(G\mid E)
\le
\delta(G\mid F)
+
\delta(F\mid E).
$$

原因是：

* 用 `E` 近似模拟 `F`；
* 再用 `F` 近似模拟 `G`；
* Markov kernel 对总变差是 contraction。

因此 deficiency 把精确观察者序升级为近似观察者几何。

---

# 238. 量子后处理序

设参数 `θ` 被编码为量子态：

$$
\rho_\theta.
$$

另一个量子实验给出：

$$
\sigma_\theta.
$$

## 定义 238.1（量子后处理）

若存在 CPTP 通道 `Λ` 使：

$$
\sigma_\theta
=
\Lambda(\rho_\theta)
$$

对所有 `θ` 成立，则称第一族量子统计上支配第二族。

这意味着任何对 `σ_θ` 的后续测量，都可以在 `ρ_θ` 上先执行 `Λ` 后模拟。

## 定义 238.2（状态族 deficiency）

$$
\delta_Q(\sigma\mid\rho)
=
\inf_\Lambda
\sup_\theta
\frac12
\left\|
\sigma_\theta-\Lambda(\rho_\theta)
\right\|_1.
$$

## 通道版本

若比较的是完整量子通道：

$$
\Phi,\Psi,
$$

则使用：

$$
\delta_\diamond(\Psi\mid\Phi)
=
\frac12
\inf_\Lambda
\left\|
\Psi-\Lambda\circ\Phi
\right\|_\diamond.
$$

diamond norm 允许输入系统与任意辅助系统纠缠，因此它比较的是最强的下游操作能力。

## 严格层级

$$
\text{same quantum kernel}
$$

不推出：

$$
\text{CPTP postprocessing equivalence}.
$$

更不推出：

$$
\text{small diamond deficiency}.
$$

量子观察者强弱不能只用“是否信息完备”一个布尔量表达。

---

# 239. 上下文性是局部—全局 image defect

设：

* `M` 是全部测量标签；
* `\mathcal C` 是一族可共同执行的测量上下文；
* 每个测量 `m` 有结果集 `O_m`。

对上下文：

$$
C\in\mathcal C,
$$

定义联合结果空间：

$$
\Omega_C
=
\prod_{m\in C}O_m.
$$

一个经验模型给每个上下文一个概率分布：

$$
e_C\in\Delta(\Omega_C).
$$

## 定义 239.1（重叠兼容性）

对任意上下文 `C,D`，要求：

$$
e_C|_{C\cap D}
=
e_D|_{C\cap D}.
$$

这只表示不同上下文在公共测量上的边缘一致。

## 定义 239.2（全局模型）

完整赋值空间为：

$$
\Omega_M
=
\prod_{m\in M}O_m.
$$

若存在全局分布：

$$
\mu\in\Delta(\Omega_M)
$$

使其在每个上下文上的边缘恰好为 `e_C`，则经验模型存在全局实现。

定义边缘映射：

$$
\operatorname{Marg}:
\Delta(\Omega_M)
\longrightarrow
\prod_{C\in\mathcal C}
\Delta(\Omega_C).
$$

于是非上下文模型集合为：

$$
\operatorname{Im}(\operatorname{Marg}).
$$

## 核心结论

上下文性恰好是：

$$
e
\notin
\operatorname{Im}(\operatorname{Marg}),
$$

尽管 `e` 已经满足全部重叠兼容条件。

> **量子上下文性首先是局部记录无法胶合为全局概率模型的 image defect，而不是状态 kernel defect。**

---

# 240. 强上下文性与概率上下文性

## 定义 240.1（支持相容的全局赋值）

一个确定性全局赋值：

$$
s\in\Omega_M
$$

称为与经验模型支持相容，若：

$$
s|_C\in\operatorname{supp}(e_C)
$$

对每个上下文成立。

## 定义 240.2（强上下文性）

若不存在任何支持相容的全局赋值，则称模型强上下文。

## 定义 240.3（概率上下文性）

即使存在某些支持相容赋值，也可能不存在任何全局概率分布的凸组合重现全部上下文概率。

因此：

$$
\text{strong contextuality}
\Longrightarrow
\text{probabilistic contextuality},
$$

反向不必成立。

这对应两种 image defect：

* 支持层的全局截面为空；
* 概率层的全局凸实现为空。

Bell 非局域性可以视为增加空间分离和局域因子约束后的特殊上下文 image defect，但一般上下文性并不要求空间分离。

---

# 241. 上下文 witness 与实现距离

有限测量情形中，全部非上下文模型形成一个凸多面体：

$$
\mathcal N
=
\operatorname{conv}
\left\{
\text{deterministic global assignments}
\right\}.
$$

若：

$$
e\notin\mathcal N,
$$

凸分离定理给出线性 witness：

$$
\langle w,e\rangle
>
\sup_{n\in\mathcal N}
\langle w,n\rangle.
$$

这就是一般形式的上下文不等式。

## 定义 241.1（上下文距离）

给定范数：

$$
\operatorname{CtxDist}(e)
=
\inf_{n\in\mathcal N}
\|e-n\|.
$$

它把“是否上下文”升级为“离非上下文集合多远”。

## 与统一理论的关系

前文的实现缺陷为：

$$
B_{\mathrm{formal}}
\setminus
B_{\mathrm{real}}.
$$

这里：

$$
B_{\mathrm{real}}=\mathcal N.
$$

所以 Bell witness、上下文 witness 和一般观察 realization witness 都属于同一个凸像分离结构。

---

# 242. 观察者必须与控制者同时建模

只研究观察者会遗漏一个对称问题：

> 哪些状态差异虽然可见，却永远不能由主体的动作产生？

考虑离散时间线性系统：

$$
x_{t+1}
=
Ax_t+Bu_t,
$$

$$
y_t
=
Cx_t.
$$

其中：

* `x_t` 是内部状态；
* `u_t` 是控制输入；
* `y_t` 是观察输出。

## 定义 242.1（可达子空间）

$$
\mathcal R
=
\operatorname{span}
\left\{
A^kBu:
k\ge0
\right\}.
$$

## 定义 242.2（不可观察子空间）

$$
\mathcal N
=
\bigcap_{k\ge0}
\ker(CA^k).
$$

解释：

* `\mathcal R` 中的方向能由某段控制历史从零状态产生；
* `\mathcal N` 中的方向永远不影响任何未来输出。

## 有限维停止

若状态维数为 `n`，Cayley–Hamilton 给出：

$$
\mathcal R
=
\operatorname{span}
\left\{
B,AB,\ldots,A^{n-1}B
\right\},
$$

$$
\mathcal N
=
\bigcap_{k=0}^{n-1}
\ker(CA^k).
$$

---

# 243. 最小观察—控制状态

只应保留两类状态方向：

1. 可以被动作触达；
2. 在未来能够影响输出。

因此定义：

$$
\mathcal X_{\min}
=
\mathcal R
/
(\mathcal R\cap\mathcal N).
$$

## 定理 243.1（诱导动力学）

因为：

$$
A\mathcal R\subseteq\mathcal R,
$$

$$
A\mathcal N\subseteq\mathcal N,
$$

所以 `A` 在商空间上诱导良定义映射。

又因为：

$$
\operatorname{Im}B\subseteq\mathcal R,
$$

控制输入下降到商空间。

并且：

$$
C|_{\mathcal R\cap\mathcal N}=0,
$$

输出映射也下降到商空间。

## 定理 243.2（商系统可达）

商空间由输入方向及其 `A` 迭代生成，因此完全可达。

## 定理 243.3（商系统可观察）

若某个商类的全部未来输出为零，则其代表属于 `\mathcal N`；又因为代表属于 `\mathcal R`，它属于：

$$
\mathcal R\cap\mathcal N,
$$

所以该商类为零。

因此：

$$
\boxed{
\mathcal X_{\min}
=
\frac{
\text{reachable states}
}{
\text{reachable but forever invisible states}
}.
}
$$

这才是同时相对于观察和行动的最小状态。

---

# 244. Hankel 算子与最小状态维数

定义系统的 Markov 参数：

$$
H_k
=
CA^kB.
$$

构造块 Hankel 矩阵：

$$
\mathcal H_{r,s}
=
\begin{bmatrix}
CB&CAB&\cdots&CA^{s-1}B\\
CAB&CA^2B&\cdots&CA^sB\\
\vdots&\vdots&&\vdots\\
CA^{r-1}B&CA^rB&\cdots&CA^{r+s-2}B
\end{bmatrix}.
$$

定义有限可观测映射：

$$
\mathcal O_r x
=
\begin{bmatrix}
Cx\\
CAx\\
\vdots\\
CA^{r-1}x
\end{bmatrix},
$$

定义有限可控映射：

$$
\mathcal C_s
\begin{bmatrix}
u_0\\
\vdots\\
u_{s-1}
\end{bmatrix}
=
\sum_{j=0}^{s-1}A^jBu_j.
$$

于是：

$$
\mathcal H_{r,s}
=
\mathcal O_r\mathcal C_s.
$$

## 定理 244.1（Hankel rank）

当 `r,s` 足够大时：

$$
\boxed{
\operatorname{rank}\mathcal H_{r,s}
=
\dim\mathcal R
-
\dim(\mathcal R\cap\mathcal N).
}
$$

### 证明

`\mathcal C_s` 的像最终稳定为 `\mathcal R`。

`\mathcal O_r` 在 `\mathcal R` 上的 kernel 最终稳定为：

$$
\mathcal R\cap\mathcal N.
$$

所以：

$$
\operatorname{rank}
(\mathcal O_r|_{\mathcal R})
=
\dim\mathcal R
-
\dim(\mathcal R\cap\mathcal N).
$$

Hankel 矩阵的像正是该可见可达像。∎

## 推论 244.1（最小维数）

任何产生同一完整输入—输出行为的有限维线性实现，其状态维数至少为 Hankel rank。

而商系统：

$$
\mathcal X_{\min}
$$

恰好达到该维数。

> **最小状态维数不是原微观状态数，而是完整过去输入与完整未来输出之间 Hankel 关系的秩。**

---

# 245. 可控 Gramian 与可观测 Gramian

假设离散系统稳定，例如：

$$
\rho(A)<1.
$$

定义可控 Gramian：

$$
W_c
=
\sum_{k=0}^{\infty}
A^kBB^*(A^*)^k.
$$

定义可观测 Gramian：

$$
W_o
=
\sum_{k=0}^{\infty}
(A^*)^kC^*CA^k.
$$

## 定理 245.1（可达范围）

$$
\operatorname{ran}W_c
=
\mathcal R.
$$

## 定理 245.2（不可观察 kernel）

$$
\ker W_o
=
\mathcal N.
$$

第二式来自能量恒等式：

$$
\langle x,W_ox\rangle
=
\sum_{k=0}^{\infty}
\|CA^kx\|^2.
$$

所以二次型为零，当且仅当所有未来输出均为零。

## 解释

* `W_c` 衡量将系统推向某个状态方向需要多少控制能量；
* `W_o` 衡量某个状态方向在未来输出中释放多少观测能量。

两者分别是 agency 和 observation 的度量化。

---

# 246. Hankel 奇异值：同时可控且可见的模式

在最小稳定实现中，`W_c` 和 `W_o` 均正定。

定义正算子：

$$
K
=
W_c^{1/2}W_oW_c^{1/2}.
$$

令其特征值为：

$$
\sigma_1^2
\ge
\sigma_2^2
\ge
\cdots
>
0.
$$

称 `σ_i` 为 Hankel 奇异值。

## 定理 246.1

这些 `σ_i` 正是过去输入到未来输出 Hankel 算子的非零奇异值。

## 解释

若某方向：

* 很容易被控制产生；
* 但几乎不影响输出；

则其 `σ_i` 很小。

若某方向：

* 很容易被观察；
* 但几乎不能由行动触达；

其 `σ_i` 也很小。

只有同时可控且可见的方向，才具有大的 Hankel 奇异值。

> **Hankel 谱是 agency 与 observation 的共同有效谱。**

---

# 247. 平衡观察—控制坐标

对于最小稳定线性系统，存在坐标变换，使：

$$
W_c
=
W_o
=
\operatorname{diag}
(\sigma_1,\ldots,\sigma_n).
$$

这称为平衡坐标。

在这种坐标中，每个状态方向的：

* 可控强度；
* 可观察强度；

被同一个数 `σ_i` 同时衡量。

## 定义 247.1（双向有效核心）

给定阈值 `τ`，保留：

$$
\sigma_i\ge\tau
$$

的模式，舍弃：

$$
\sigma_i<\tau
$$

的模式。

这不再是单纯 observer quotient，也不是单纯 control restriction，而是：

$$
\boxed{
\text{observable}
\cap
\text{reachable}
\cap
\text{robustly coupled}.
}
$$

## 严格边界 247.1

低 Hankel 奇异值不表示该状态方向“不存在”。

它只表示该方向在给定：

* 控制接口；
* 观察接口；
* 动力学；
* 时间尺度；
* 能量范数

下，对输入—输出行为贡献较小。

---

# 248. 预测因果状态

考虑有限字母表上的随机过程。

记完整过去为：

$$
\overleftarrow X_t,
$$

完整未来为：

$$
\overrightarrow X_t.
$$

## 定义 248.1（预测等价过去）

两个过去 `h,h'` 等价，当且仅当：

$$
P(\overrightarrow X_t\mid h)
=
P(\overrightarrow X_t\mid h').
$$

定义预测状态映射：

$$
\epsilon(h)
=
[h].
$$

预测状态随机变量为：

$$
S_t
=
\epsilon(\overleftarrow X_t).
$$

## 定理 248.1（预测充分性）

$$
\overrightarrow X_t
\perp
\overleftarrow X_t
\mid
S_t.
$$

因为 `S_t` 已经保留了过去对未来条件分布的全部影响。

## 定理 248.2（普适最小性）

若另一个过去统计量：

$$
R_t=r(\overleftarrow X_t)
$$

也满足：

$$
P(\overrightarrow X_t\mid\overleftarrow X_t)
=
P(\overrightarrow X_t\mid R_t),
$$

则存在唯一映射 `f` 使：

$$
S_t=f(R_t)
$$

在实际像上成立。

所以：

$$
\boxed{
S_t
=
\text{保持完整未来 law 的最粗过去商}.
}
$$

这正是一般协议行为商在随机过程上的实例。

---

# 249. 预测状态的单值更新

设当前预测状态为 `s`，下一观察符号为 `a`，且：

$$
P(X_t=a\mid S_t=s)>0.
$$

## 定理 249.1（unifilar update）

存在函数：

$$
T_{\epsilon}
$$

使：

$$
S_{t+1}
=
T_{\epsilon}(S_t,X_t)
$$

几乎处处成立。

### 证明

取两个属于同一预测状态的过去 `h,h'`。

它们具有相同完整未来 law，因此：

* 下一符号 `a` 的概率相同；
* 在条件 `a` 下的剩余未来分布也相同。

所以扩展后的过去 `ha` 和 `h'a` 仍属于同一预测状态。新状态只依赖旧状态和新符号，而不依赖旧过去的代表元。∎

## 结论 249.1

预测 completion 不只是一个静态 sufficient statistic；它自动产生闭合状态更新：

$$
\boxed{
\text{predictive quotient}
+
\text{new observation}
\longrightarrow
\text{next predictive quotient}.
}
$$

---

# 250. 预测记忆的熵分解

假设过程平稳，并定义预测状态熵：

$$
C_\mu
=
H(S_t).
$$

定义过去—未来互信息：

$$
E
=
I(
\overleftarrow X_t;
\overrightarrow X_t
).
$$

由于：

$$
S_t=f(\overleftarrow X_t),
$$

且：

$$
\overrightarrow X_t
\perp
\overleftarrow X_t
\mid S_t,
$$

可得：

$$
E
=
I(
S_t;
\overrightarrow X_t
).
$$

于是：

$$
H(S_t)
=
I(
S_t;
\overrightarrow X_t
)
+
H(
S_t\mid\overrightarrow X_t
).
$$

定义：

$$
\chi
=
H(
S_t\mid\overrightarrow X_t
).
$$

因此：

$$
\boxed{
C_\mu
=
E+\chi.
}
$$

## 解释

* `E` 是预测状态中实际暴露在未来记录里的部分；
* `χ` 是系统为了正确预测未来而必须内部保存，但从单条完整未来轨迹仍不能反向完全恢复的部分。

> **记忆可以对未来预测必不可少，却不一定直接出现在未来记录中。**

这比“存储”和“可见”二分更细。

---

# 251. 策略因果状态与 self

把“未来输出”替换为“未来行动—记录 law”。

设历史为 `h`，未来外部输入协议为 `w`，由历史产生的未来行动 law 为：

$$
\Pi_h(w).
$$

定义：

$$
h\sim_{\mathrm{self}}h'
$$

当且仅当：

$$
\Pi_h(w)=\Pi_{h'}(w)
$$

对所有未来输入协议成立。

定义策略状态：

$$
S_{\mathrm{self}}
=
[h]_{\mathrm{self}}.
$$

这与此前 self quotient 一致，但现在可以定义熵量：

$$
C_{\mathrm{self}}
=
H(S_{\mathrm{self}}).
$$

对实际未来行为记录 `B^+`：

$$
C_{\mathrm{self}}
=
I(S_{\mathrm{self}};B^+)
+
H(S_{\mathrm{self}}\mid B^+).
$$

第一项是未来行为中可被外部推断的 self 信息。

第二项是：

> 即使知道完整实际未来轨迹，仍不能恢复的内部策略差异。

它可称为私有策略记忆。

## 严格边界 251.1

该“私有”只相对于一条实际未来轨迹。

若允许对同一 self 状态执行全部反事实输入协议，则完整策略画像按定义能够区分所有 self 类。

因此必须区分：

* 单条实现历史的可识别性；
* 全协议反事实画像的可识别性。

---

# 252. 统一观察者能力的六层偏序

一个观察者不能再用单一“完备／不完备”评价。至少需要六层。

## 第一层：零误差分离

由 kernel 决定：

$$
K_E.
$$

## 第二层：统计决策能力

由 Blackwell 后处理序决定：

$$
E\succeq_B F.
$$

## 第三层：近似模拟能力

由 deficiency 决定：

$$
\delta(F\mid E).
$$

## 第四层：局部—全局实现能力

由行为像决定：

$$
\operatorname{Im}\Sigma.
$$

## 第五层：行动可达能力

由 reachable set 或 controllability Gramian 决定：

$$
\mathcal R,
\qquad
W_c.
$$

## 第六层：闭环预测能力

由全部未来协议 law 的最小行为商决定：

$$
Q_{\mathrm{beh}}.
$$

因此建议定义：

$$
\operatorname{Power}(\mathfrak O)
=
\left(
K,
\mathsf B,
\delta,
\mathsf I,
\mathsf R,
\mathsf P
\right).
$$

其中各字段分别表示：

* separation；
* decision；
* deficiency；
* realization image；
* reachability；
* predictive closure。

不同观察者可以在这些轴上不可比较。

---

# 253. 可达行为核心定理

现在给出一个统一有限／一般系统定理。

设：

* `X` 是完整状态空间；
* `X_{\mathrm{rch}}` 是从允许初态和干预可达的状态；
* `P` 是全部允许未来协议；
* `\mathcal L_p(x)` 是协议 law。

定义可达行为等价：

$$
x\sim_{\mathrm{beh}}y
$$

当且仅当：

$$
\mathcal L_p(x)
=
\mathcal L_p(y)
$$

对所有 `p` 成立。

定义：

$$
Q_{\mathrm{core}}
=
X_{\mathrm{rch}}
/
{\sim_{\mathrm{beh}}}.
$$

## 定理 253.1（可达行为核心）

`Q_{\mathrm{core}}` 满足：

1. 每个状态类都可由允许过程到达；
2. 不同状态类被某个未来协议区分；
3. 全部协议更新在该商上良定义；
4. 任意精确再现相同可达协议行为的实现，都唯一满射到 `Q_{\mathrm{core}}`。

### 证明

前三项分别来自：

* 对可达集的限制；
* 行为 kernel 的定义；
* 行为等价对协议前缀闭合。

第四项是 kernel 因子化普适性。

## 各领域实例

确定性自动机：

$$
Q_{\mathrm{core}}
=
\text{Myhill–Nerode states}.
$$

线性系统：

$$
Q_{\mathrm{core}}
=
\mathcal R/
(\mathcal R\cap\mathcal N).
$$

随机过程：

$$
Q_{\mathrm{core}}
=
\text{predictive causal states}.
$$

量子顺序实验：

$$
Q_{\mathrm{core}}
=
\frac{
\text{reachable quantum states}
}{
\text{equal instrument-word laws}
}.
$$

策略系统：

$$
Q_{\mathrm{core}}
=
\text{policy-sufficient self states}.
$$

## 关键边界

上下文性不由这个商自动解决。

行为商处理：

$$
\text{不同状态是否产生同一行为}.
$$

上下文性处理：

$$
\text{兼容局部行为是否存在一个全局实现}.
$$

所以 kernel completion 与 image completion仍然是两条独立轴。

---

# 254. 建议 Lean 模块树

```text
D5/S3/Observer/UnifiedMorphisms/
  EvaluationObserver.lean
  ObserverMorphism.lean
  ObserverDual.lean
  ReachableBehaviorCore.lean

D5/S3/Observer/DecisionOrder/
  FiniteExperiment.lean
  StochasticPostprocessing.lean
  BlackwellForward.lean
  BlackwellFiniteConverse.lean
  KernelOrderStrictlyWeaker.lean
  ExperimentDeficiency.lean
  DeficiencyRiskBound.lean
  DeficiencyTriangle.lean

D5/S3/QuantumObserver/DecisionOrder/
  QuantumExperimentPostprocessing.lean
  StateFamilyDeficiency.lean
  ChannelDiamondDeficiency.lean

D5/S3/Observer/Contextuality/
  MeasurementScenario.lean
  CompatibleEmpiricalModel.lean
  GlobalMarginalMap.lean
  NoncontextualImage.lean
  StrongContextuality.lean
  ContextualWitness.lean
  ContextualDistance.lean

D5/S3/Observer/ControlDuality/
  ReachableSubspace.lean
  UnobservableSubspace.lean
  ReachableObservableQuotient.lean
  HankelFactorization.lean
  HankelRankMinimality.lean
  ControllabilityGramian.lean
  ObservabilityGramian.lean
  HankelSingularValues.lean
  BalancedObserverAgentCore.lean

D5/S3/Observer/PredictiveStates/
  PredictiveEquivalence.lean
  PredictiveStateUniversal.lean
  PredictiveStateUnifilar.lean
  StatisticalComplexity.lean
  PredictiveMemoryDecomposition.lean
  PolicyCausalState.lean
```

优先形式化的低依赖定理：

```text
stochasticPostprocessing_kernel_mono

noisyInjectiveExperiment_not_blackwellAbove_perfect

deficiency_risk_bound

compatibleModel_noncontextual_iff_mem_marginalRange

strongContextual_implies_contextual

reachableObservableQuotient_reachable

reachableObservableQuotient_observable

hankel_rank_eq_reachable_dim_sub_inter_unobservable_dim

observabilityGramian_kernel

controllabilityGramian_range

predictiveState_universal

predictiveState_update_wellDefined

predictiveComplexity_eq_excess_add_hiddenMemory

reachableBehaviorCore_universal
```

---

# 255. 严格非主张

1. Kernel 相同不表示两个概率实验 Blackwell 等价。
2. 信息完备不表示有限样本统计效率相同。
3. Blackwell 支配不表示两个实验具有相同物理实现成本。
4. 小 deficiency 不自动表示计算后处理容易实现。
5. 量子 trace-distance deficiency 不等于完整 channel diamond deficiency。
6. 上下文性是局部—全局 image defect，但不是所有 image defect 都是量子上下文性。
7. 重叠兼容性不表示存在全局联合分布。
8. 存在支持相容赋值不表示存在全局概率模型。
9. 线性系统的可控／可观测商不自动推广到任意非线性系统而无需额外结构。
10. 低 Hankel 奇异值不表示对应自由度本体上不存在。
11. 平衡截断是行为近似，不是微观世界删除。
12. 预测状态是未来 law 的最小充分统计，不等于意识状态。
13. 预测状态熵不等于主观体验复杂度。
14. 私有策略记忆不等于不可验证的神秘自由意志。
15. 行为核心最小性只相对于申报的协议集合。
16. 扩大协议语法会进一步精化行为核心。
17. Contextuality image defect 与 diagonal image defect 具有共同形式，但具体约束与物理含义不同。
18. 本增订中的 Blackwell、Hankel、预测状态和上下文统一尚未形成同一个 Lean record。
19. 本增订没有推出 Born 规则来自对角化。
20. 本增订没有推出量子力学来自素数结构。
21. 本增订没有证明 RH、强本体自由或意识坍缩。

---

# 256. 最终统一：观察者、控制者与预测者是同一个行为核的三个方向

此前的评价网是：

$$
e:X\times P\longrightarrow\Lambda.
$$

现在加入动作输入和未来协议后，真正的核心对象成为：

$$
\mathcal B:
X_{\mathrm{rch}}
\longrightarrow
\prod_{p\in P}
\mathsf{Law}_p.
$$

其 kernel 给出：

$$
K_{\mathrm{beh}}
=
\ker\mathcal B.
$$

规范状态是：

$$
Q_{\mathrm{core}}
=
X_{\mathrm{rch}}/K_{\mathrm{beh}}.
$$

但完整理论还需要三个互补结构。

统计决策序：

$$
E\succeq_B F
$$

回答一个观察者能否模拟另一个观察者的全部决策。

局部—全局像：

$$
\operatorname{Im}(\operatorname{Marg})
$$

回答兼容局部 law 是否来自某个全局对象。

观察—控制 Hankel 核：

$$
\mathcal X_{\min}
=
\mathcal R/
(\mathcal R\cap\mathcal N)
$$

回答哪些状态方向既能被行动产生，又能在未来被观察。

预测因果状态：

$$
S
=
\frac{
\text{pasts}
}{
\text{equal future laws}
}
$$

回答哪些历史差异仍会改变未来概率。

于是统一结构可以写为：

$$
\begin{aligned}
\text{Observer}
&=
\text{questions that distinguish states},
\\
\text{Controller}
&=
\text{actions that reach states},
\\
\text{Predictor}
&=
\text{history quotient that determines future laws},
\\
\text{Contextuality}
&=
\text{compatible local laws outside the global image},
\\
\text{Decision power}
&=
\text{downstream tasks simulable by postprocessing},
\\
\text{Minimal reality}
&=
\text{reachable states modulo complete behavioral equivalence}.
\end{aligned}
$$

最深的收束是：

> **世界状态只有在能够被某种允许行动触达、能够通过某种允许协议影响未来记录，并且其局部行为能够进入一个真实全局实现时，才属于观察者—行动者的有效现实核心。**

更短地：

$$
\boxed{
Q_{\mathrm{effective}}
=
\frac{
\text{reachable states}
}{
\text{indistinguishable under every future protocol}
}.
}
$$

而这个商的强弱，不再只由 kernel 衡量，还必须同时报告：

$$
\boxed{
\text{decision order},
\quad
\text{deficiency},
\quad
\text{realization image},
\quad
\text{Hankel spectrum},
\quad
\text{predictive memory}.
}
$$
