# 观察者完成反射与可观测 Gram 演算
## 稳定接口的普适闭包、状态—效应反对偶与定量可观测性

**版本：v1.0，2026-08-22**

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

Hamiltonian 情形中，[H,E] 是 effect orbit 的时间导数；嵌套交换子塔生成全部 effect reflector。因此

$$
ad_H
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
