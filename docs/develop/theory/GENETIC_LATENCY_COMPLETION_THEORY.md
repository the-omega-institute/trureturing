# 基因潜显完成论
## 从 ACGT、环境相对补与杂合重叠，到观察残余、因果完成、未来许可与群体选择

**Genetic Latency–Completion Theory，GLCT**

**版本：v1.0，2026-08-26**

---

## 摘要

传统遗传学用“显性等位基因掩盖隐性等位基因”描述杂合体表型。该说法适合作为入门语言，却把下列不同层次压成了一个二元标签：

$$
\text{序列符号}
\neq
\text{等位基因}
\neq
\text{基因型}
\neq
\text{分子状态}
\neq
\text{表型读出}
\neq
\text{未来干预结果}.
$$

本文建立一门统一理论：

$$
\boxed{
\text{显性}
=
\text{异质底层状态在指定观察商中的相等};
}
$$

$$
\boxed{
\text{隐性}
=
\text{仍位于当前观察残余中的非零差异};
}
$$

$$
\boxed{
\text{显现}
=
\text{时间、环境、干预、反事实查询或繁殖目标使差异逃逸出残余};
}
$$

$$
\boxed{
\text{完成}
=
\text{把全部相关未来、动作与目标加入观察语言后得到的规范最小商}.
}
$$

该理论以仓库已经机器验证的环境相对补、kernel–refinement 对偶、可观察事件代数、未来同余、隐藏流、非干扰、控制商、因果查询层级、目标族最小商、概率分离、后验充分性、残余覆盖与局部—整体粘合为基础，把静态显隐遗传学推进为：

$$
\text{观察遗传学}
\to
\text{动力学遗传学}
\to
\text{干预遗传学}
\to
\text{反事实遗传学}
\to
\text{决策与进化遗传学}.
$$

本文不声称形式结构自动给出具体生化参数，也不把 A、C、G、T 四种碱基字面地分类成“两个离散、两个连续”。连续性属于时间、浓度、构象、概率和状态纤维；碱基符号本身仍是离散字母。

---

# 0. 真值层级与严格边界

本文使用四种状态。

1. **定义**：保守引入类型、映射、关系或数值。
2. **本文定理**：本文给出证明，但不声称仓库已有同名基因专用 Lean proof term。
3. **Lean 锚点**：仓库中已有机器证明，可作为形式化依赖。
4. **模型定理／研究命题**：依赖有限性、确定性、连续性、随机交配或其他明确前件。

本文不主张：

1. A、G 在生物化学上是“离散碱基”，而 C、T 是“连续碱基”；四种碱基作为字母和分子种类均是离散类别。
2. 等位基因 b 是等位基因 a 的集合补；二倍体杂合体恰好说明两者存在域可以重叠。
3. “没有被 DNA 拒绝”自动推出“从当前状态可达”。许可、可达、可存活和资源可行必须分别定义。
4. 观察上等价自动推出机制同一；任何有限观察族都只定义一个 residual。
5. 显性、诊断阳性、治疗阈值和群体适合度是同一个关系。
6. 本文的基因专用定理已经全部 Lean 闭合。
7. 本文可替代实验遗传学、分子生物学或临床判断。

---

# Part I：ACGT、类型与环境相对补

## 1.1 DNA 字母与等位基因不是同一类型

设 DNA 字母表为：

$$
Σ = \{A,C,G,T\}.
$$

长度为 n 的序列属于：

$$
Σ^n.
$$

某个位点的等位基因类型可以是序列子集：

$$
\mathcal A_ℓ \subseteq Σ^{n_ℓ},
$$

也可以是某种功能等价关系下的商：

$$
\mathcal A_ℓ = Σ^{n_ℓ}/\sim_{allele}.
$$

因此，碱基字母、序列、等位基因、基因型和表型必须保持类型区分。

若希望保留最初“离散—连续—离散—连续”的节奏，可把 ACGT 重新解释为一个过程语义，而不是化学断言：

$$
A = \text{Address},
\quad
C = \text{Context},
\quad
G = \text{Gate},
\quad
T = \text{Trajectory}.
$$

其中 Address 与 Gate 是离散结构，Context 与 Trajectory 可带连续或随机状态。该记号只是一种模型命名，不改变真实碱基的生物化学分类。

---

## 1.2 四种不同的“反”

必须区分：

$$
\neg P
$$

作为命题否定；

$$
Ω \setminus A
$$

作为环境 Ω 中的集合补；

$$
c_u(x)=u-x
$$

作为相对于总量 u 的代数补；

以及 DNA 配对规则：

$$
A\leftrightarrow T,
\qquad
C\leftrightarrow G.
$$

这些运算的输入、输出类型和语义均不同。

仓库 `D5/S0/Conventions/AmbientComplementDependence` 已机器验证：减法补必须携带显式 ambient total；同一对象在不同总量下的补一般不同。

---

## 定理 1.1（单点反域判据）

设 t 属于集合 Ω。则存在 s 使：

$$
Ω\setminus\{t\}=\{s\}
$$

当且仅当：

$$
Ω=\{t,s\}.
$$

### 证明

若补集为单点，则 Ω 由 t 与该单点组成。反向显然。证毕。

因此：

$$
\boxed{
\text{只有当背景宇宙本来就只有两个状态时，“除它以外的一切”才等于另一个点。}
}
$$

把高基数状态空间中的补域压成一个 `false`，是一个商映射，而不是对象层的同一。

---

# Part II：倍性、杂合重叠与非 Boolean 等位存在

## 2.1 基因型空间

设等位基因类型为：

$$
\mathcal A.
$$

p 倍体基因型定义为无序多重集：

$$
\mathcal G_p = Sym^p(\mathcal A).
$$

对二等位二倍体：

$$
\mathcal A=\{a,b\},
\qquad
\mathcal G_2=\{aa,ab,bb\}.
$$

---

## 2.2 等位基因存在事件

定义：

$$
E_a=\{g\in\mathcal G_p:n_a(g)>0\},
$$

$$
E_b=\{g\in\mathcal G_p:n_b(g)>0\}.
$$

在二倍体二等位情形：

$$
E_a=\{aa,ab\},
\qquad
E_b=\{ab,bb\}.
$$

于是：

$$
E_a\cap E_b=\{ab\}.
$$

而：

$$
E_a^c=\{bb\},
\qquad
E_b^c=\{aa\}.
$$

所以：

$$
\boxed{E_b\neq E_a^c.}
$$

---

## 定理 2.1（杂合重叠定理）

对二等位 p 倍体系统，若 p 大于等于 2，则：

$$
E_a\cap E_b\neq\varnothing.
$$

### 证明

基因型：

$$
a^{p-1}b
$$

同时含有 a 与 b，因此属于交集。证毕。

只有在二等位单倍体：

$$
\mathcal G_1=\{a,b\}
$$

中，才有：

$$
E_b=E_a^c.
$$

因此杂合体是等位基因 Boolean 互补性的精确障碍。

---

## 2.3 显性表型与隐性等位基因可以重叠

若 a 对 b 完全显性，当前表型读出满足：

$$
q_0(aa)=q_0(ab)=D,
$$

$$
q_0(bb)=R.
$$

显性表型事件为：

$$
D_a=q_0^{-1}(D)=\{aa,ab\}.
$$

隐性等位基因存在事件为：

$$
E_b=\{ab,bb\}.
$$

所以：

$$
D_a\cap E_b=\{ab\}.
$$

即：

$$
\boxed{
\text{隐性等位基因可以真实存在于显性表型区域中。}
}
$$

成为补集的是显性表型事件与隐性表型事件，而不是两个等位基因的存在事件。

---

# Part III：上下文、状态、观察语言与显性 residual

## 3.1 上下文与内部实现

定义上下文空间：

$$
\mathcal C.
$$

一个上下文可包含其他位点、表观状态、细胞类型、组织、年龄、性别、环境和历史。

定义完整内部状态空间：

$$
\mathcal X.
$$

确定性实现映射为：

$$
ρ:\mathcal G_p\times\mathcal C\to\mathcal X.
$$

记：

$$
x_{aa,c}=ρ(aa,c),
\quad
x_{ab,c}=ρ(ab,c),
\quad
x_{bb,c}=ρ(bb,c).
$$

随机实现将在后文改为概率核。

---

## 3.2 观察语言

单个读出为：

$$
q:\mathcal X\to Y.
$$

一般观察语言定义为：

$$
\mathcal L=\{q_i:\mathcal X\to Y_i\}_{i\in I}.
$$

联合 profile：

$$
Π_{\mathcal L}(x)=(q_i(x))_{i\in I}.
$$

定义观察 residual：

$$
R_{\mathcal L}=ker(Π_{\mathcal L}).
$$

即：

$$
xR_{\mathcal L}y
\iff
∀i\in I,\ q_i(x)=q_i(y).
$$

规范商为：

$$
Z_{\mathcal L}=\mathcal X/R_{\mathcal L},
$$

规范投影为：

$$
π_{\mathcal L}:\mathcal X\to Z_{\mathcal L}.
$$

观察者看到的是商类：

$$
[x]_{\mathcal L},
$$

而不是完整状态 x。

---

## 定义 3.1（完全显性）

在观察语言 L 与上下文 c 下，定义：

$$
a\triangleright_{\mathcal L,c}b
$$

当且仅当：

$$
π_{\mathcal L}(x_{aa,c})
=
π_{\mathcal L}(x_{ab,c})
\neq
π_{\mathcal L}(x_{bb,c}).
$$

等价地：

$$
x_{aa,c}R_{\mathcal L}x_{ab,c},
$$

且：

$$
\neg(x_{ab,c}R_{\mathcal L}x_{bb,c}).
$$

---

## 定义 3.2（隐性差异）

若：

$$
x_{aa,c}\neq x_{ab,c},
$$

但：

$$
x_{aa,c}R_{\mathcal L}x_{ab,c},
$$

则称 b 对当前语言是潜伏差异。

所以：

$$
\boxed{
\text{隐性不是零，而是商投影之前仍存在、商投影之后暂时消失的差异。}
}
$$

---

## 定理 3.1（显性必然要求观察不忠实）

若 a 对 b 完全显性，且 x_aa,c 与 x_ab,c 不同，则联合 profile 在相关状态集上不是单射。

### 证明

两个不同状态具有相同 profile，故映射非单射。证毕。

若观察语言包含一个可精确恢复基因型的注入读出，则不同基因型不可能保持完全显性等价。因此不存在脱离观察语言的绝对显性。

---

## 定理 3.2（固定观察下的非对称性）

$$
a\triangleright_{\mathcal L,c}b
\Rightarrow
\neg(b\triangleright_{\mathcal L,c}a).
$$

### 证明

前者给出 ab 与 bb 不等价；后者却要求二者等价，矛盾。证毕。

---

## 定理 3.3（显性一般不传递）

存在三个等位基因 a、b、d，使：

$$
a\triangleright b,
\qquad
b\triangleright d,
$$

但：

$$
\neg(a\triangleright d).
$$

### 见证

取标量表型：

$$
P(aa)=P(ab)=0,
$$

$$
P(bb)=P(bd)=1,
$$

$$
P(dd)=P(ad)=2.
$$

前两条显性成立，而 a 对 d 显性要求 P(aa)=P(ad)，不成立。证毕。

多等位基因显性关系因此适合表示为有向图，而不是天然全序；甚至可以构造有向环。

---

# Part IV：观察族—残余关系 Galois 结构

## 4.1 联合 kernel 与关系不变量

设候选观察器全集为：

$$
\mathfrak Q.
$$

对观察族 Γ，定义：

$$
K(Γ)=\bigcap_{q\in Γ}ker(q).
$$

对关系 R，定义所有尊重 R 的观察器：

$$
I(R)=\{q\in\mathfrak Q:R\subseteq ker(q)\}.
$$

仓库 `DefinitionKernelGalois` 已机器验证：

$$
Γ\subseteq I(R)
\iff
R\subseteq K(Γ).
$$

---

## 定理 4.1（观察闭包）

定义：

$$
Cl_Q(Γ)=I(K(Γ)).
$$

则 Cl_Q 是扩张、单调且幂等的闭包算子。

### 证明

由 Galois 对应得到扩张性；K 与 I 均反单调，复合后单调；标准 Galois 闭包恒等式给出幂等性。证毕。

若：

$$
q\in Cl_Q(Γ),
$$

则 q 不能切开任何 Γ 尚未切开的状态对。它在区分语义上是冗余观察器。

---

## 定理 4.2（原始揭示判据）

$$
q\notin Cl_Q(Γ)
$$

当且仅当存在 x、y，使：

$$
(x,y)\in K(Γ),
$$

但：

$$
q(x)\neq q(y).
$$

### 证明

q 不属于 I(K(Γ))，恰表示 K(Γ) 不包含于 ker(q)。证毕。

因此新实验真正有意义，当且仅当它切开当前 residual 中至少一个尚未分离的状态对。

仓库 `InvolutiveBlindResidual` 已机器验证一个结构化特例：隐藏 involution 若被旧定义族全部忽略，而新 Boolean 读出沿该 involution 反转，就会产生非空盲 residual 和 primitive semantic escape。

---

# Part V：可观察事件代数与 Boolean 取反的边界

## 5.1 可观察事件

定义：

$$
\mathcal E(\mathcal L)
=
\{A\subseteq\mathcal X:
 xR_{\mathcal L}y
\Rightarrow
(x\in A\iff y\in A)\}.
$$

仓库 `ObservableEventAlgebraDuality` 已机器验证：

$$
\text{观察精化}
\iff
\text{kernel 反向包含}
\iff
\text{可观察事件代数正向包含}.
$$

---

## 定理 5.1（事件分离刻画）

$$
xR_{\mathcal L}y
\iff
∀A\in\mathcal E(\mathcal L),\ (x\in A\iff y\in A).
$$

### 证明

正向由事件在纤维上常值。反向若 profiles 不同，取 x 所在 profile 纤维的逆像事件即可分离二者。证毕。

---

## 推论 5.2（显性的事件代数刻画）

完全显性等价于：

$$
∀A\in\mathcal E(\mathcal L),
\quad
1_A(x_{aa,c})=1_A(x_{ab,c}),
$$

同时存在 B 属于该事件代数，使：

$$
1_B(x_{ab,c})\neq1_B(x_{bb,c}).
$$

即当前语言中没有任何可表达事件能区分 aa 与 ab，但至少有一个事件能区分 ab 与 bb。

---

## 定理 5.3（Boolean 取反不能恢复已商掉的信息）

若 A 是可观察事件，则 A 的补仍是可观察事件。若 aa 与 ab 在当前 residual 中等价，则：

$$
aa\in A\iff ab\in A,
$$

同时：

$$
aa\in A^c\iff ab\in A^c.
$$

因此只对现有粗读出取反，不能切开其内部纤维。要揭示隐性差异，必须扩张观察语言，而不是反复否定同一个 Boolean 输出。

---

# Part VI：离散语法、连续纤维与显性阈值

## 6.1 混合状态模型

离散调控或基因状态记为：

$$
s_n\in S.
$$

连续有效状态记为：

$$
z(t)\in M.
$$

两次跳跃之间：

$$
\dot z(t)=f_{s_n,e(t),u(t)}(z(t)).
$$

触发 guard 后：

$$
(s,z)\mapsto(s',R_{s\to s'}(z)).
$$

所以离散 DNA 语言与连续生命轨迹的正确结合是：

$$
\boxed{
\text{离散底空间}
+
\text{连续／随机状态纤维}
+
\text{离散 gate}
+
\text{连续时间轨迹}.
}
$$

---

## 6.2 连通到离散的硬分类障碍

若内部表示像连通，输出空间离散，且 decoder 连续，则 decoder 必为常函数。

仓库 `ContinuousHardClassificationObstruction` 已机器验证更一般的因子化形式：非恒定硬分类必迫使表示像不连通、decoder 不连续、输出非离散或源空间不连通中的至少一项发生。

因此非平凡显性边界至少需要：

1. 阈值处的不连续；
2. 多个不连通吸引域；
3. 随机跳跃；
4. 连续概率输出后再做硬判定。

---

## 6.3 剂量—阈值显性

设功能等位基因每份提供 u，失活等位基因提供 0：

$$
d_{aa}=2u,
\quad
d_{ab}=u,
\quad
d_{bb}=0.
$$

定义：

$$
q_θ(d)=1\quad\text{当且仅当}\quad d\ge θ.
$$

若：

$$
0<θ\le u,
$$

则：

$$
q_θ(2u)=q_θ(u)\neq q_θ(0),
$$

失活等位基因在该性状下隐性。

若：

$$
u<θ\le2u,
$$

则：

$$
q_θ(2u)\neq q_θ(u)=q_θ(0),
$$

一份正常拷贝不足以跨越阈值。

所以显性方向取决于剂量、网络响应与观察阈值的相对位置。

---

## 6.4 非锐显性

若输出不是硬阈值，而是平滑函数：

$$
q_{β,θ}(d)=\frac{1}{1+e^{-β(d-θ)}},
$$

则通常：

$$
q(2u)\neq q(u)\neq q(0).
$$

完全显性可以是实验容差或生理饱和下的近似等价，而非底层状态严格相同。

---

## 6.5 数量性显性系数

若标量性状满足 y_aa 不等于 y_bb，定义：

$$
h=
\frac{y_{ab}-y_{bb}}{y_{aa}-y_{bb}}.
$$

则：

$$
h=1
$$

表示 a 完全显性；

$$
h=0
$$

表示 b 完全显性；

$$
0<h<1
$$

表示中间型；

$$
h>1
$$

表示超显性；

$$
h<0
$$

表示低于两个纯合体。

该系数在非退化仿射尺度变换下不变，但一般不在任意非线性尺度变换下不变。

共显性更适合向量值输出，例如：

$$
P(aa)=(1,0),
\quad
P(ab)=(1,1),
\quad
P(bb)=(0,1).
$$

---

# Part VII：精度塔、显性带与揭示前沿

## 7.1 相容精度塔

设：

$$
q_k:X\to O_k,
$$

且存在降精度映射：

$$
ρ_k:O_{k+1}\to O_k
$$

满足：

$$
q_k=ρ_k\circ q_{k+1}.
$$

仓库 `CompatiblePrecisionTowerMonotonicity` 已机器验证：

$$
ker(q_{k+1})\subseteq ker(q_k).
$$

---

## 定义 7.1（成对揭示阈值）

$$
r(x,y)=\inf\{k:q_k(x)\neq q_k(y)\},
$$

若永不分离则取无穷。

---

## 定理 7.1（精度持久性）

若在第 k 层已分离，则所有更高精度层仍分离。

### 证明

若更高层重新相等，沿降精度映射投影回第 k 层就会推出第 k 层相等，矛盾。证毕。

---

## 定理 7.2（显性精度区间）

定义：

$$
r_1=r(x_{aa},x_{ab}),
$$

$$
r_2=r(x_{ab},x_{bb}).
$$

则第 k 层完全显性当且仅当：

$$
\boxed{r_2\le k<r_1.}
$$

所以显性成立的层集合是区间：

$$
D_{a\triangleright b}=[r_2,r_1).
$$

该区间非空当且仅当：

$$
r_2<r_1.
$$

显性不是一个脱离精度的点标签，而是观察精化过程中的一个区间。

定义显性宽度：

$$
W_{dom}=r_1-r_2
$$

在两个阈值有限时成立。

---

## 7.2 时间—精度联合前沿

设自然动力学为 τ，定义：

$$
W_{k,n}(x)=
(q_k(x),q_k(τx),\ldots,q_k(τ^n x)).
$$

定义 residual：

$$
R_{k,n}=ker(W_{k,n}).
$$

则：

$$
R_{k+1,n}\subseteq R_{k,n},
$$

$$
R_{k,n+1}\subseteq R_{k,n}.
$$

对状态对 x、y，揭示区域：

$$
U_{x,y}=\{(k,n):W_{k,n}(x)\neq W_{k,n}(y)\}
$$

在乘积偏序中是上集。其最小元构成揭示前沿。

显性相区为：

$$
\mathcal D_{a\triangleright b}
=
U_{x_{ab},x_{bb}}
\setminus
U_{x_{aa},x_{ab}}.
$$

它表示 ab 与 bb 已分离，而 aa 与 ab 尚未分离的全部资源配置。

沿任何单调增加精度、时间或干预数量的实验路径，每个状态对只会由“未揭示”跨越一次进入“已揭示”，所以显性沿该路径仍形成区间。

---

# Part VIII：未来完成、揭示深度与最大不变 residual

## 8.1 未来观察词

固定动力学：

$$
τ:X\to X.
$$

长度 n 的未来观察词为：

$$
W_n(x)=
(q(x),q(τx),\ldots,q(τ^n x)).
$$

定义：

$$
E_n=ker(W_n).
$$

有：

$$
E_{n+1}\subseteq E_n.
$$

无限未来 residual：

$$
E_∞=\bigcap_{n\ge0}E_n.
$$

---

## 定义 8.1（揭示深度）

若 aa 与 ab 当前等价，定义：

$$
d_{rev}
=
\inf\{n:(x_{aa},x_{ab})\notin E_n\}.
$$

取值：

- 0：当前已显现；
- 有限正数：延迟显现；
- 无穷：在该动力学与观察下永久不可区分。

---

## 定理 8.1（有限未来完成）

仓库 `FiniteFutureCongruence` 已机器验证：有限状态系统中，E_n 在某个有限深度 m_star 稳定：

$$
E_∞=E_{m_*},
$$

且 E_∞ 是包含于当前观察 kernel 中的最大前向不变关系。

所以：

$$
\boxed{
E_∞
=
E_0
-
\text{全部未来会破裂的伪等价状态对}.
}
$$

稳定显性就是当前显性 residual 中经未来闭包检验后仍存活的等价。

---

## 定理 8.2（有限分裂预算）

若 X 有 N 个状态，未来 refinement 严格删除不同状态对的次数不超过：

$$
\binom{N}{2}.
$$

若按等价类数计算，初始有 k_0 个类，则严格分裂次数不超过：

$$
N-k_0.
$$

---

# Part IX：非干扰、可见—隐藏交叉块与定量潜伏

## 9.1 非干扰

设当前公开读出：

$$
l:X\to L,
$$

隐藏状态：

$$
h:X\to H,
$$

演化：

$$
F:X\to Y,
$$

未来公开读出：

$$
O:Y\to B.
$$

若存在：

$$
\bar F:L\to B
$$

使：

$$
O\circ F=\bar F\circ l,
$$

则当前公开状态相同必推出未来公开状态相同。

仓库 `NoninterferenceSecretFlowExclusion` 已机器验证该结构。

---

## 定理 9.1（显现即 noninterference 失败）

若：

$$
l(x_{aa})=l(x_{ab}),
$$

但：

$$
O(Fx_{aa})\neq O(Fx_{ab}),
$$

则不存在上述下降映射。

所以隐性显现是隐藏基因信息突破当前表型接口的非干扰。

---

## 9.2 线性可见—隐藏分解

设：

$$
\mathcal H=V\oplus H.
$$

令 P 为可见投影，Q=I-P 为隐藏投影，T 为线性演化。

当前隐藏差异：

$$
δ=x_{ab}-x_{aa}
$$

满足：

$$
Pδ=0,
\qquad
Qδ=δ.
$$

下一步可见差异为：

$$
PTδ=PTQδ.
$$

因此：

$$
\boxed{PTQδ\neq0}
$$

正是一步显现条件。

仓库 `ProjectionCommutatorIdentity` 已机器验证：

$$
PT-TP=PTQ-QTP,
$$

以及完整 reducing 条件等价于两个交叉块同时为零。

---

## 定理 9.2（可见自治判据）

若 P 的平方等于 P，则以下三者等价：

1. 存在 bar_T 使 PT=bar_T P；
2. ker(P) 包含于 ker(PT)；
3. PTQ=0。

### 证明

因子化立即给出 kernel 包含；kernel 包含应用于 Qx 给出 PTQ=0；若 PTQ=0，则 PT=PTP，可在 range(P) 上定义诱导动力学。证毕。

所以隐藏状态不影响下一步可见状态只要求 PTQ=0，不必要求双向完全解耦。

---

## 9.3 永久不可观察子空间

定义：

$$
\mathcal N_∞=\bigcap_{n\ge0}ker(PT^n).
$$

若 δ 属于该空间，则所有有限时间均不可见。

若维数为 d，由 Cayley–Hamilton：

$$
\mathcal N_∞
=
\bigcap_{n=0}^{d-1}ker(PT^n).
$$

因此有限维线性模型只需有限层即可判定永久不可观察性。

---

## 9.4 折扣可观测能量

在级数收敛条件下，定义：

$$
W_β=
\sum_{n\ge0}β^n(T^*)^nP^*PT^n,
\qquad
0<β<1.
$$

定义潜伏—显现能量：

$$
\mathcal V_β(δ)
=
\langle δ,W_βδ\rangle
=
\sum_{n\ge0}β^n\|PT^nδ\|^2.
$$

于是：

$$
\mathcal V_β(δ)=0
\iff
δ\in\mathcal N_∞.
$$

该 Gramian 方向与 `FORMAL_OBSERVER_COMPLETION_REFLECTION.md` 的 paper-level observer-completion 分析一致；本文不把它误标为已有基因专用 Lean 定理。

---

# Part X：动作完成、控制商与反事实显性

## 10.1 过程 monoid 完成

设 monoid S 作用于 X。定义完成 profile：

$$
C_S(q)(x)=(q(s\cdot x))_{s\in S}.
$$

完成 residual：

$$
R_{q,S}=ker(C_S(q))
=
\bigcap_{s\in S}(s\times s)^{-1}(ker q).
$$

仓库 `ControlQuotientUniversalMinimality` 已机器验证：按所有 monoid-indexed public outcomes 取商，是所有能恢复当前读出、对动作封闭并决定全部动作后果的表示中规范最粗的表示。

定义控制潜能：

$$
Potential_{q,S}(x)=[x]_{R_{q,S}}.
$$

---

## 定义 10.1（干预完全显性）

$$
a\triangleright^{ctl}_{q,c}b
$$

当且仅当：

$$
x_{aa,c}R_{q,S}x_{ab,c},
$$

且：

$$
\neg(x_{ab,c}R_{q,S}x_{bb,c}).
$$

干预完全显性推出当前显性，反向不成立。

---

## 10.2 观察—干预—反事实层级

仓库 `ObservationInterventionCounterfactualChain` 已机器验证，在有限确定性 Boolean SCM 中：

$$
R_{CF}\subseteq R_{Int}\subseteq R_{Obs},
$$

并且两次包含均可严格。

因此定义因果显性深度：

- -1：aa 与 ab 在观察层已不同；
- 0：观察层相同，但干预层可分；
- 1：全部干预边缘相同，但联合反事实 profile 可分；
- 2：完整反事实 profile 仍相同。

于是：

$$
\boxed{
\text{“显性有多强”可以定义为它能穿过多深的因果查询层。}
}
$$

---

## 10.3 结构因果实现

仓库 `ParentOrderedStructuralEvaluationSemantics` 已机器验证：有限父节点有序结构模型在给定外部状态与干预后具有唯一结果；`InterventionEffectiveness` 进一步验证被干预坐标最终等于指定值。

因此基因因果图：

$$
G\to RNA\to Protein\to Complex\to Cell\to Trait
$$

可在结构模型中区分：

1. 自然观察显性；
2. 对全部环境的结构显性；
3. 对全部允许干预的稳定显性；
4. 仅在中介干预后显现的因果潜伏。

---

# Part XI：随机显性、统计分离与后验内部性

## 11.1 随机实现

将实现映射推广为概率核：

$$
ρ:\mathcal G_p\times\mathcal C\to Prob(\mathcal X).
$$

观察与过程诱导完整 transcript 概率律：

$$
μ_{g,c}^{\mathcal L,S}\in Prob(Ω_{\mathcal L,S}).
$$

---

## 定义 11.1（精确分布显性）

$$
μ_{aa}=μ_{ab},
$$

且：

$$
μ_{ab}\neq μ_{bb}.
$$

这是随机系统中真正的完全显性。

---

## 定义 11.2（近似显性）

给定距离 D 与 0 不大于 epsilon 小于 delta，定义：

$$
D(μ_{aa},μ_{ab})\le ε,
$$

$$
D(μ_{ab},μ_{bb})\ge δ.
$$

D 可取总变差、Wasserstein 或任务相关风险距离。

---

## 11.2 四类统计潜伏

### 同律

$$
μ_{aa}=μ_{ab}.
$$

任何可测统计量均同分布。

### 等价但不同律

$$
μ_{aa}\ll μ_{ab},
\qquad
μ_{ab}\ll μ_{aa},
$$

但二者不相等。

仓库 `EquivalentLawPosteriorInterior` 已机器验证：对严格内部先验，规范后验几乎处处严格位于 0 与 1 之间，且不存在质量 1 对 0 的完美分离事件。

### 互相奇异

$$
μ_{aa}\perp μ_{ab}.
$$

仓库 `SingularProbabilityPerfectSeparator` 已机器验证：存在可测事件 A，使：

$$
μ_{aa}(A)=1,
\qquad
μ_{ab}(A)=0.
$$

反向亦直接成立，所以互相奇异等价于存在零误差可测分离。

### 混合情形

两律既非互相绝对连续，也非完全奇异；部分 transcript 区域可完美揭示，其他区域保留不可消除的不确定性。

---

## 11.3 决策近似而非机制同一

仓库 `BoundedRiskSimulatorTransport` 已机器验证：若粗实验能以统一总变差误差 epsilon 模拟精细实验，则对任意 0 到 1 有界损失，任意精细实验决策规则都可移植到粗实验，风险增加至多 epsilon。

因此必须区分：

$$
\text{机制不同},
\quad
\text{统计可分},
\quad
\text{决策有价值}.
$$

一个差异可以真实且可检测，却对指定行动几乎没有额外价值。

---

# Part XII：信息分解与未来条件信息

## 12.1 静态隐藏信息

令 G 为随机基因型，联合观察为 Π_L(G)。定义：

$$
I_{eff}(\mathcal L)=H(Π_{\mathcal L}(G)),
$$

$$
I_{hidden}(\mathcal L)=H(G\mid Π_{\mathcal L}(G)).
$$

因为观察是 G 的函数：

$$
H(G)=I_{eff}(\mathcal L)+I_{hidden}(\mathcal L).
$$

若观察语言扩张，隐藏信息不能增加。

---

## 12.2 完全显性的最小例子

对 Aa 与 Aa 交配：

$$
P(AA)=\frac14,
\quad
P(Aa)=\frac12,
\quad
P(aa)=\frac14.
$$

所以：

$$
H(G)=1.5\ \text{bits}.
$$

若 A 完全显性：

$$
P(D)=\frac34,
\quad
P(R)=\frac14.
$$

则：

$$
H(Y)\approx0.811278\ \text{bits},
$$

$$
H(G\mid Y)\approx0.688722\ \text{bits}.
$$

这部分信息没有消失，只是当前表型通道未携带它。

---

## 12.3 动态完成信息

仓库 `CompletionInformationChainDecomposition` 已机器验证：

$$
H(W_m)
=
H(O_0)
+
\sum_{k=1}^{m}H(O_k\mid W_{k-1}),
$$

并在稳定完成深度：

$$
H(CompletedState\mid O_0)
=
\sum_{k=1}^{m_*}H(O_k\mid W_{k-1}).
$$

因此动态隐性信息就是当前观察之后、由后续观察逐层释放的条件信息总和。

---

# Part XIII：目标族、carrier 与繁殖完成

## 13.1 目标族最小商

设目标族：

$$
K_i:X\to Y_i,
\qquad i\in I.
$$

联合目标：

$$
K_*(x)=(K_i(x))_{i\in I}.
$$

规范最小商：

$$
Z_*=X/ker(K_*).
$$

仓库 `TargetFamilyMinimalQuotient` 已机器验证：该商是同时决定整个目标族的最粗充分状态；任何能决定全部目标的其他表示都必须至少同样精细。

---

## 13.2 Carrier 定理

当前健康目标可满足：

$$
Health(aa)=Health(ab)=healthy,
$$

$$
Health(bb)=affected.
$$

但理想孟德尔配子核满足：

$$
Γ(aa)=δ_a,
$$

$$
Γ(ab)=\frac12δ_a+\frac12δ_b,
$$

$$
Γ(bb)=δ_b.
$$

所以：

$$
Γ(aa)\neq Γ(ab).
$$

只观察健康时，aa 与 ab 在同一个商类；加入繁殖目标后，规范最小商必须把 carrier 单独分出。

因此：

$$
\boxed{
\text{carrier 不是人为附加标签，而是繁殖目标加入后由最小充分性强制产生的状态。}
}
$$

---

# Part XIV：未来许可、可达、存活与资源

## 14.1 轨迹背景空间

设从当前状态出发的候选轨迹背景为：

$$
Ω_{x_0}.
$$

DNA 直接排除的轨迹：

$$
R_{DNA}(g)\subseteq Ω_{x_0}.
$$

DNA 许可域：

$$
Permit_Ω(g)=Ω_{x_0}\setminus R_{DNA}(g).
$$

该补集必须相对于明确 Ω 定义。

---

## 14.2 实际未来

定义：

$$
Future(g,x_0,c)
=
Permit_Ω(g)
\cap
Reach(g,x_0,c)
\cap
Viable(g,c)
\cap
ResourceFeasible(c).
$$

所以：

$$
Future\subseteq Permit.
$$

但一般：

$$
Permit\not\subseteq Reach.
$$

最小反例是恒等动力学：全部状态均被许可，但从初态只能到达自身。

---

## 14.3 五层未来分解

有限深度 n 下定义：

$$
F_n\subseteq V_n\subseteq R_n\subseteq P_n\subseteq Ω_n.
$$

分别表示实际可实现、可存活、可达、DNA 许可和全部候选前缀。

有不交并分解：

$$
Ω_n
=
(Ω_n\setminus P_n)
\sqcup
(P_n\setminus R_n)
\sqcup
(R_n\setminus V_n)
\sqcup
(V_n\setminus F_n)
\sqcup
F_n.
$$

分别对应 DNA 拒绝、许可但不可达、可达但不可存活、可存活但资源不可行、真实可实现。

---

## 14.4 约束信息 telescope

若相关集合非空，定义：

$$
I_{DNA}^{(n)}=\log_2\frac{|Ω_n|}{|P_n|},
$$

$$
I_{dyn}^{(n)}=\log_2\frac{|P_n|}{|R_n|},
$$

$$
I_{via}^{(n)}=\log_2\frac{|R_n|}{|V_n|},
$$

$$
I_{res}^{(n)}=\log_2\frac{|V_n|}{|F_n|}.
$$

则：

$$
\log_2\frac{|Ω_n|}{|F_n|}
=
I_{DNA}^{(n)}+I_{dyn}^{(n)}+I_{via}^{(n)}+I_{res}^{(n)}.
$$

所以总未来压缩量可以分解为基因、动力学、存活和资源限制，而不是用无类型的“无穷减 DNA”表示。

---

## 14.5 当前表型隐性、未来结构显性

定义：

$$
Δ_F(a,b;c)
=
Future(aa,c)\triangle Future(ab,c).
$$

若当前 profiles 相等，但：

$$
Δ_F(a,b;c)\neq\varnothing,
$$

则 b 是当前表型隐性、未来结构显性：当前结果相同，但可达未来、风险或干预响应不同。

---

# Part XV：实验设计、残余覆盖与最小揭示成本

## 15.1 目标相关状态对

设有限候选状态集 X，目标：

$$
T:X\to Y.
$$

定义目标不同的无序状态对：

$$
U_T=\{\{x,y\}:T(x)\neq T(y)\}.
$$

候选实验 i 的分离集合：

$$
D_i=\{\{x,y\}\in U_T:q_i(x)\neq q_i(y)\}.
$$

---

## 定理 15.1（目标充分性等价于状态对覆盖）

有限实验族 J 足以决定 T，当且仅当：

$$
U_T=\bigcup_{i\in J}D_i.
$$

### 证明

若 T 经联合读出因子化，则目标不同状态对不可能联合读出相同，故至少被一个实验分开。反向若所有目标不同对均被覆盖，则联合读出相同必推出目标相同，所以 T 在读出纤维上常值并下降到有效像。证毕。

---

## 15.2 最小成本面板

给每个实验成本 c_i，最小目标充分面板是：

$$
\min_J\sum_{i\in J}c_i
$$

满足：

$$
U_T=\bigcup_{i\in J}D_i.
$$

仓库 `MinimumCompleteObserverSetCover` 已机器验证完整状态识别版本等价于加权 set cover。本文的目标相关版本只把覆盖全集缩小为 U_T。

---

## 15.3 Residual exact cover

仓库 `ResidualSeparationAdapter` 已机器验证：有限 residual snapshot 被精确覆盖，当且仅当选定 package 中不存在仍被联合 kernel 盲掉的 residual pair；正权重下未覆盖权重为零与无盲对等价。

定义最小揭示复杂度：

$$
m^*=\min\{|J|:J\text{ 覆盖全部目标 residual}\}.
$$

定义最小揭示成本：

$$
C^*=\min\{\sum_{i\in J}c_i:J\text{ 覆盖全部目标 residual}\}.
$$

---

## 15.4 次模收益与贪心推进

仓库 `WeightedResidualCoverage` 已机器验证加权 residual capture 的边际收益递减；`GreedyResidualAllocation` 已机器验证贪心选择每一步最大化单步收益，且只要仍有正权重 residual 可被候选实验分开，就取得严格正进展。

这为基因检测面板、干预组合和跨组织采样提供了统一的有限覆盖语义。

---

## 15.5 多目标 Pareto 前沿

实验方案 A 的价值可写为：

$$
V(A)=(Information,ResidualCapture,Transfer,Cost,Risk).
$$

前三项越大越好，后二项越小越好。

仓库 `ParetoWeakPreorder` 已机器验证，在各坐标均为 preorder 时，弱 Pareto 关系自反且传递。

所以没有额外效用函数时，规范对象是 Pareto 非支配前沿，而不是唯一“最佳实验”。

该 Pareto dominance 与遗传显性 dominance 是不同类型上的不同关系，必须避免术语混淆。

---

# Part XVI：多位点、上位作用与局部—整体显性

## 16.1 多位点上下文

全基因型空间为：

$$
\mathcal G=\prod_{ℓ\in L}Sym^{p_ℓ}(\mathcal A_ℓ).
$$

研究位点 ℓ 时，其余位点 g_{-ℓ} 属于上下文。

所以正确显性谓词是：

$$
a\triangleright_{\mathcal L,c,g_{-ℓ}}b.
$$

同一等位基因对可在不同背景下保持、失去或反转显性。

---

## 16.2 表型非加性不自动等于分子直接相互作用

即使内部剂量加性：

$$
z=z_1+z_2,
$$

若观察为非线性：

$$
y=f(z),
$$

表型层有限差分仍可非零。

所以必须区分：

1. 底层机制相互作用；
2. 饱和或阈值；
3. 观察尺度造成的伪 epistasis。

---

## 16.3 局部—整体粘合

将组织、时间窗或环境区域表示为覆盖：

$$
U=\bigcup_iU_i.
$$

各局部上有响应截面：

$$
s_i^{aa},
\quad
s_i^{ab},
\quad
s_i^{bb}.
$$

仓库 `SheafPairwiseEqualizer` 已机器验证：在 sheaf 条件下，兼容局部截面族唯一粘合为全局截面。

因此若所有局部：

$$
s_i^{aa}=s_i^{ab},
$$

且重叠上相容，则全局响应相等。

若任何一个局部目标分开二者，则包含该局部目标的全局联合 profile 不可能保持完全显性。

所以：

$$
\boxed{
\text{全局显性是一条局部响应能否一致粘合的命题。}
}
$$

---

## 16.4 摘要相同不等于机制同一

仓库 `PowerTraceSimilarityCountermodel` 已机器验证：零矩阵与非零平方零矩阵可以拥有相同全部正幂迹与相同特征多项式，却具有不同秩且不相似。

所以即使两个基因调控线性模型匹配许多谱摘要，也只证明它们位于该摘要观察族的同一 residual，不证明完整机制同一。

---

# Part XVII：群体选择中的潜伏阶

本部分是模型定理。假设二倍体随机交配、选择发生在合子形成后、无突变迁移漂变。令 b 频率为 x，a 频率为 p=1-x。

基因型频率：

$$
aa:p^2,
\quad
ab:2px,
\quad
bb:x^2.
$$

适合度：

$$
w_{aa}=1,
$$

$$
w_{ab}=1-hs,
$$

$$
w_{bb}=1-s.
$$

平均适合度：

$$
\bar w=p^2+2px(1-hs)+x^2(1-s).
$$

选择后的 b 频率：

$$
x'
=
\frac{x^2(1-s)+px(1-hs)}{\bar w}.
$$

化简：

$$
x'-x
=
-
\frac{s p x(hp+(1-h)x)}{\bar w}.
$$

---

## 定理 17.1（完全隐性选择是二阶的）

若 h=0，则：

$$
x'-x
=
-
\frac{s(1-x)x^2}{1-sx^2}.
$$

当 x 趋近 0：

$$
x'-x=-sx^2+O(x^3).
$$

所以稀有完全隐性有害等位基因的选择信号从二阶开始。

若 h 大于 0：

$$
x'-x=-hsx+O(x^2),
$$

选择信号从一阶开始。

定义选择揭示阶：

$$
r_{sel}=ord_{x=0}|x'-x|.
$$

完全隐性时 r_sel=2，杂合体已有作用时通常 r_sel=1。

---

## 定理 17.2（p 倍体完全隐性庇护）

假设只有全 b 基因型 b^p 适合度为 1-s，其余均为 1。全隐性基因型频率为 x^p。

则：

$$
\bar w=1-sx^p,
$$

$$
x'
=
\frac{x-sx^p}{1-sx^p},
$$

所以：

$$
x'-x
=
-
\frac{s x^p(1-x)}{1-sx^p}.
$$

当 x 趋近 0：

$$
x'-x=-sx^p+O(x^{p+1}).
$$

因此：

$$
\boxed{r_{sel}=p.}
$$

倍性越高，完全隐性效应进入群体选择读出的最低阶越高。

---

## 17.3 表型显性不推出适合度显性

完全可能：

$$
q_{phen}(aa)=q_{phen}(ab),
$$

但：

$$
q_{fit}(aa)\neq q_{fit}(ab).
$$

反之亦可。

预测群体演化必须使用包含适合度目标的联合目标商，而不能只使用形态表型商。

---

# Part XVIII：后验、政策充分性与行动阈值

## 18.1 后验是未来决策的充分状态

设隐藏状态 Θ 表示真实基因型、机制类别或环境亚型。观察历史 h 产生后验：

$$
P(Θ\mid h).
$$

仓库 `PosteriorFuturePolicySufficiency` 已机器验证：若两个历史具有相同后验，则对任意未来政策、未来 transcript、终端动作类型和非负损失，它们的条件 Bayes 最优值相同。

所以对未来决策：

$$
\boxed{
\text{原始历史可以被压缩为当前后验。}
}
$$

表型等价、控制响应等价、后验等价和决策价值等价是不同 residual。

---

## 18.2 行动阈值

二元决策中，设目标状态后验为 p，误阳性与误阴性代价为正数 c_FP 与 c_FN。

仓库 `OptimalAcceptanceThreshold` 已机器验证：接受／干预最优当且仅当：

$$
p\ge\frac{c_{FP}}{c_{FP}+c_{FN}}.
$$

因此：

$$
\boxed{
\text{分子显性}
\neq
\text{诊断阳性}
\neq
\text{应当治疗}.
}
$$

行动取决于后验和损失函数，而不只取决于显隐标签。

---

# Part XIX：统一潜伏签名

## 定义 19.1（遗传潜伏签名）

对等位基因对 a、b 和上下文 c，定义：

$$
Λ(a,b;c)
=
(r_2,r_1,\partial U,C^*,σ_{law},λ_{causal},r_{sel},\mathcal V_β,I_{hidden}).
$$

其中：

- r_2：ab 与 bb 的精度分离阈值；
- r_1：aa 与 ab 的精度分离阈值；
- partial U：时间—精度—干预揭示前沿；
- C_star：最小目标充分揭示成本；
- sigma_law：equal、equivalent、mixed 或 singular；
- lambda_causal：观察、干预、反事实显性深度；
- r_sel：群体选择揭示阶；
- V_beta：动力学可观测能量；
- I_hidden：指定语言下的剩余基因信息。

经典 Boolean 显性只是该签名在固定精度 k 上的投影：

$$
Dom_k(a,b)=1
\iff
r_2\le k<r_1.
$$

所以：

$$
\boxed{
\text{显性／隐性不是理论终点，而是高维潜伏签名的一维切片。}
}
$$

---

# Part XX：统一主定理

## 定理 20.1（基因潜显完成表示定理）

给定：

1. 等位基因类型 A；
2. 基因型空间 G_p；
3. 上下文 c；
4. 状态实现 rho；
5. 当前观察语言 L_0；
6. 过程 monoid S；
7. 完整目标族 T。

定义：

$$
R_0=ker(Π_{\mathcal L_0}),
$$

$$
R_S=ker(C_S(Π_{\mathcal L_0})),
$$

$$
R_T=ker(Π_{\mathcal T}).
$$

则：

### 当前显性

$$
x_{aa,c}R_0x_{ab,c},
$$

且：

$$
\neg(x_{ab,c}R_0x_{bb,c}).
$$

### 动态可揭示隐性

$$
x_{aa,c}R_0x_{ab,c},
$$

但：

$$
\neg(x_{aa,c}R_Sx_{ab,c}).
$$

### 目标可揭示隐性

$$
x_{aa,c}R_Sx_{ab,c},
$$

但：

$$
\neg(x_{aa,c}R_Tx_{ab,c}).
$$

### 完成显性

$$
x_{aa,c}R_Tx_{ab,c},
$$

且：

$$
\neg(x_{ab,c}R_Tx_{bb,c}).
$$

所有能够由完整目标 profile 决定的目标，都唯一地经由完成商 X/R_T 因子化。

### 证明纲要

前三种分类直接由嵌套 residual 定义。完成商的充分性与最小性来自联合 profile kernel 的规范 quotient universal property。对有限候选模型，若完整实验族能分离全部目标不同模型对，则存在有限子族保留全部区分。

---

# Part XXI：可证伪性

本理论的每个实例都必须给出明确的语言、上下文、过程、目标和容差。

## 21.1 当前显性的反驳

若当前语言中存在 q，使：

$$
q(x_{aa,c})\neq q(x_{ab,c}),
$$

则完全显性为假。

## 21.2 动力学完全显性的反驳

若存在 n：

$$
Π_{\mathcal L}(τ^n x_{aa,c})
\neq
Π_{\mathcal L}(τ^n x_{ab,c}),
$$

则动力学完全显性为假。

## 21.3 干预显性的反驳

若存在允许动作 s：

$$
Π_{\mathcal L}(s\cdot x_{aa,c})
\neq
Π_{\mathcal L}(s\cdot x_{ab,c}),
$$

则干预显性为假。

## 21.4 近似显性的反驳

若：

$$
D(μ_{aa},μ_{ab})>ε,
$$

则指定容差下的近似显性为假。

## 21.5 全局显性的反驳

若某个被纳入目标族的组织、时间窗或环境局部 profile 分离 aa 与 ab，则全局完全显性为假。

---

# Part XXII：与仓库现有形式化的连接

以下是本理论的主要 Lean 锚点。它们提供抽象基础，但不等于基因专用结论已经自动闭合。

1. `D5/S0/Conventions/AmbientComplementDependence`
   - 环境相对补。
2. `D5/S3/ConceptDynamics/DefinitionEscape/DefinitionKernelGalois`
   - 观察族与关系的 Galois 对应。
3. `D5/S3/ConceptDynamics/RefinementAlgebra/ObservableEventAlgebraDuality`
   - refinement、kernel 与事件代数对偶。
4. `D5/S3/ConceptDynamics/RefinementFactorization/CompatiblePrecisionTowerMonotonicity`
   - 精度塔 kernel 反单调。
5. `D5/S3/Observer/Separation/FiniteFutureCongruence`
   - 有限未来完成与最大不变同余。
6. `D5/S3/ConceptDynamics/Disclosure/NoninterferenceSecretFlowExclusion`
   - 非干扰排除隐藏信息流。
7. `D5/S3/Observer/HiddenFlow/ProjectionCommutatorIdentity`
   - 可见—隐藏交叉块与交换子。
8. `D5/S3/ConceptDynamics/Control/ControlQuotientUniversalMinimality`
   - 动作完成商的普适最小性。
9. `D5/S3/ConceptDynamics/Causal/ParentOrderedStructuralEvaluationSemantics`
   - 父节点有序 SCM 的唯一求值。
10. `D5/S3/ConceptDynamics/Causal/InterventionEffectiveness`
    - 干预坐标固定为指定值。
11. `D5/S3/ConceptDynamics/Causal/ObservationInterventionCounterfactualChain`
    - 观察、干预、反事实 kernel 链。
12. `D5/S3/ConceptDynamics/CanonicalImage/GlobalProfileCounterfactualTargetMinimality`
    - 反事实目标族经规范 profile image 因子化。
13. `D5/S3/ConceptDynamics/SufficiencyQuotient/TargetFamilyMinimalQuotient`
    - 联合目标最小充分商。
14. `D5/S3/ConceptDynamics/Experiment/FiniteInterventionExtraction`
    - 有限候选模型的有限分离干预族。
15. `D5/S3/ConceptDynamics/ExperimentDesign/MinimumCompleteObserverSetCover`
    - 最小完整观察器等价于加权 set cover。
16. `D5/S3/ConceptDynamics/ResidualCoverage/ResidualSeparationAdapter`
    - exact cover 与无盲 residual pair 等价。
17. `D5/S3/ConceptDynamics/ResidualCoverage/WeightedResidualCoverage`
    - 加权 residual capture 次模性。
18. `D5/S3/ConceptDynamics/ResidualCoverage/GreedyResidualAllocation`
    - 贪心单步最优与正进展。
19. `D5/S3/Observer/MeasureSeparation/EquivalentLawPosteriorInterior`
    - 等价律后验内部性与无完美分离。
20. `D5/S3/Observer/MeasureSeparation/SingularProbabilityPerfectSeparator`
    - 奇异律完美分离。
21. `D5/S3/Estimation/DecisionRisk/BoundedRiskSimulatorTransport`
    - 总变差模拟误差控制决策风险。
22. `D5/S3/Estimation/DecisionRisk/PosteriorFuturePolicySufficiency`
    - 后验对全部未来政策 Bayes 值充分。
23. `D5/S3/ConceptDynamics/DecisionValueScale/OptimalAcceptanceThreshold`
    - 成本敏感行动阈值。
24. `D5/S3/ConceptDynamics/Gluing/SheafPairwiseEqualizer`
    - 兼容局部截面的唯一全局粘合。
25. `D5/S0/Observation/PowerTraceSimilarityCountermodel`
    - 丰富摘要仍可能遗漏完整机制类。

---

# Part XXIII：建议的 Lean 4 形式化结构

建议新建：

```text
D5/S3/Biology/GeneticLatency/
  AlleleAndGenotype.lean
  AllelePresenceOverlap.lean
  ContextualRealization.lean
  ObservationLanguage.lean
  GeneticResidual.lean
  CompleteDominance.lean
  DominanceEventAlgebra.lean
  DominanceBand.lean
  PrecisionRevealInterval.lean
  TimePrecisionRevealFrontier.lean
  DynamicCompletion.lean
  RevealDepth.lean
  ProcessCompletion.lean
  NoninterferenceReveal.lean
  LinearHiddenLeakage.lean
  CausalDominanceHierarchy.lean
  DistributionalDominance.lean
  FuturePermission.lean
  TargetFamilyGeneticQuotient.lean
  CarrierCompletion.lean
  FiniteRevealExperiments.lean
  ContextualDominanceSheaf.lean
  GeneticHiddenInformation.lean
  PopulationSelectionLatency.lean
  PosteriorDecisionDominance.lean
```

最小接口草案：

```lean
structure GeneticLatencyModel where
  Allele : Type u
  Genotype : Type v
  Context : Type w
  State : Type x
  ObsIdx : Type i
  Outcome : ObsIdx → Type o
  realize : Genotype → Context → State
  readout : (j : ObsIdx) → State → Outcome j

def profile
    (M : GeneticLatencyModel)
    (x : M.State) :
    (j : M.ObsIdx) → M.Outcome j :=
  fun j => M.readout j x

def ObsEquivalent
    (M : GeneticLatencyModel)
    (x y : M.State) : Prop :=
  M.profile x = M.profile y

def CompleteDominates
    (M : GeneticLatencyModel)
    (aa ab bb : M.Genotype)
    (c : M.Context) : Prop :=
  M.ObsEquivalent (M.realize aa c) (M.realize ab c) ∧
  ¬ M.ObsEquivalent (M.realize ab c) (M.realize bb c)
```

首批应闭合的基因专用承重定理：

```text
allele_presence_overlap_of_mixed_genotype
allele_presence_not_complement_in_diploid
complete_dominance_iff_kernel_pattern
complete_dominance_iff_event_indistinguishable
observer_closure_operator
primitive_assay_iff_separates_current_residual
dominance_band_order_convex
dominance_precision_interval
time_precision_reveal_upper_set
process_completion_kernel_formula
process_completion_universal_minimality
current_dominance_does_not_imply_dynamic_dominance
noninterference_excludes_recessive_reveal
visible_autonomy_iff_hidden_visible_block_zero
finite_state_reveal_depth_bound
observation_intervention_counterfactual_dominance_chain
gamete_target_separates_carrier
target_family_genetic_quotient_minimal
finite_genetic_model_finite_reveal_family
target_sufficient_panel_iff_target_pair_cover
local_dominance_glues_to_global
hidden_genetic_information_antitone
diploid_recessive_selection_is_second_order
polyploid_recessive_selection_order_eq_ploidy
equal_posterior_equal_future_policy_value
```

---

# Part XXIV：研究纲领

## 24.1 显性带几何

研究所有保持：

$$
aa\sim ab,
\qquad
ab\not\sim bb
$$

的观察接口在 partition lattice 中形成的序凸区域。

## 24.2 遗传潜伏谱

对嵌套语言：

$$
\mathcal L_0\subseteq\mathcal L_1\subseteq\cdots,
$$

定义差异首次逃逸层级。所有状态对的首次逃逸层级构成潜伏谱。

## 24.3 最小揭示实验

寻找最小成本实验族，覆盖全部目标相关 residual pair，而不是盲目增加数据量。

## 24.4 动态可观测性

研究 W_beta 的谱、弱可见方向、揭示时间和噪声敏感性。

## 24.5 因果潜显层级

系统分类观察隐性、干预隐性、反事实隐性与决策隐性。

## 24.6 局部—全局障碍

研究不同组织、年龄与环境中的局部显性是否能兼容粘合成全局关系。

## 24.7 群体选择潜伏阶

把基因型效应逃逸出 fitness residual 的最低频率阶作为群体层显现深度。

---

# 最终总结构

本理论的最短公式是：

$$
\boxed{
a\triangleright_{\mathcal L,c}b
\iff
[x_{aa,c}]_{\mathcal L}
=
[x_{ab,c}]_{\mathcal L}
\neq
[x_{bb,c}]_{\mathcal L}.}
$$

可揭示隐性为：

$$
\boxed{
[x_{aa,c}]_{\mathcal L_0}
=
[x_{ab,c}]_{\mathcal L_0},
\qquad
[x_{aa,c}]_{\mathcal L_*}
\neq
[x_{ab,c}]_{\mathcal L_*}.}
$$

完整链条为：

$$
\boxed{
\begin{aligned}
\text{显性}
&=\text{当前观察商中的相等},\\
\text{隐性}
&=\text{当前 residual 中的非零差异},\\
\text{显现}
&=\text{差异逃逸出 residual},\\
\text{完成}
&=\text{加入全部相关未来、动作、反事实与目标},\\
\text{潜能}
&=\text{完成商中的状态},\\
\text{实验价值}
&=\text{切开的目标 residual，而不是数据字节数},\\
\text{决策意义}
&=\text{后验与政策价值商中的区别},\\
\text{进化显现}
&=\text{差异进入适合度读出的最低频率阶}.
\end{aligned}}
$$

最终一句：

$$
\boxed{
\text{显性不是一个等位基因压掉另一个等位基因；
它是观察接口把不同底层状态投影到同一个结果。
隐性也不是不存在；
它是尚未逃逸出当前观察核的未来差异。}
$$

---

# Part XXV：追加版本、真值勘误与承重替换

**追加版本：v1.2，2026-08-26。**

本追加严格位于 v1.0 原文之后，不删除、不改写此前任何段落。若前文的仓库真值标签与本追加发生冲突，以本节的后验勘误为准。

## 25.1 两项 receipt 撤回

仓库在后续 wave-57 errata 中撤回了以下两个 digestion receipt：

1. `ObservableEventAlgebraDuality` 的 receipt：审查认为它形成了对既有 pullback-algebra 结构的定义性分叉；
2. `PosteriorFuturePolicySufficiency` 的 receipt：审查指出其未来 transcript 核在类型上不依赖历史，结论实质上只是用后验相等进行重写。

对应冻结 Lean 文件、Blueprint 和 Golden shard 仍在仓库中，但本追加不再把这两个 receipt 作为新的承重成果。

事件侧改由以下结构承重：

- `ConceptKernelOrderDuality`；
- `LeastCommonReadoutRefinement`；
- `FiberModalOperatorLaws`；
- 本文直接给出的纤维事件证明。

后验决策侧改由本文的 belief-Markov 前件承重：只有当未来生成律对历史的依赖确实经当前 belief 因子化时，相同后验才推出相同未来政策价值。

---

# Part XXVI：观察纤维上的知识、可能性与遗传认识论边界

## 26.1 纤维模态算子

给定观察：

$$
q:X\to B,
$$

定义状态 x 的观察纤维：

$$
[x]_q=\{y:q(y)=q(x)\}.
$$

对事件 P 定义知识与可能性：

$$
K_q(P)=\{x:[x]_q\subseteq P\},
$$

$$
\Diamond_q(P)=\{x:[x]_q\cap P\neq\varnothing\}.
$$

仓库 `FiberModalOperatorLaws` 已机器验证：K_q 是收缩、单调、幂等且保持有限交的内算子；Diamond_q 是扩张、单调、幂等的对偶闭包，并满足：

$$
K_q(P)=\bigl(\Diamond_q(P^c)\bigr)^c.
$$

## 26.2 完全显性纤维中的精确计算

令：

$$
X=\{AA,Aa,aa\},
$$

且：

$$
q(AA)=q(Aa)=D,
\qquad
q(aa)=R.
$$

定义：

$$
E_A=\{AA,Aa\},
\quad
E_a=\{Aa,aa\},
\quad
C_a=\{Aa\}.
$$

则：

$$
K_q(E_A)=E_A,
\qquad
\Diamond_q(E_A)=E_A;
$$

$$
K_q(E_a)=\{aa\},
\qquad
\Diamond_q(E_a)=X;
$$

$$
K_q(C_a)=\varnothing,
\qquad
\Diamond_q(C_a)=\{AA,Aa\}.
$$

因此，显性表型能确定“至少含一个 A”，却不能确定是否携带 a；整个显性纤维都与 carrier 身份相容。

## 26.3 认识论边界

定义：

$$
\partial_qP=\Diamond_q(P)\setminus K_q(P).
$$

它包含所有既不能由当前观察确定、又不能被当前观察排除的状态。

在完全显性模型中：

$$
\partial_qC_a=\{AA,Aa\}.
$$

所以经典 carrier 状态不是“不可存在”，而是位于当前表型的认识论边界。

## 定理 26.1（观察精化压缩认识论边界）

若 r 精化 q，即存在 f 使：

$$
q=f\circ r,
$$

则对任意事件 P：

$$
K_q(P)\subseteq K_r(P),
$$

$$
\Diamond_r(P)\subseteq\Diamond_q(P),
$$

$$
\partial_rP\subseteq\partial_qP.
$$

### 证明

r-纤维包含于 q-纤维。粗纤维全部落入 P 时，细纤维也全部落入 P；细纤维与 P 相交时，粗纤维亦相交。第三式由前两式直接推出。证毕。

---

# Part XXVII：目标识别、规范最小披露与遗传隐私

## 27.1 查询族识别

设候选模型空间 M，查询族：

$$
Q_i:M\to A_i,
$$

联合查询：

$$
Q_*(m)=(Q_i(m))_i,
$$

目标：

$$
T:M\to Z.
$$

仓库 `QueryFamilyIdentification` 已机器验证：

$$
Q\text{ 识别 }T
\iff
\ker Q_*\subseteq\ker T,
$$

并等价于 T 唯一地经查询商因子化。

因此实验族不需要恢复完整基因型；它只需要切开所有目标不同的模型对。

## 27.2 规范目标商

定义：

$$
Z_T=M/\ker T.
$$

该商只保留决定 T 所必需的区别。若 Q 识别 T，则存在唯一映射：

$$
h:M/\ker Q_*\to Z_T
$$

使目标投影经查询商下降。

所以 Z_T 是精确决定目标的最粗接口，也是目的限制披露的规范状态。

## 27.3 超额披露

在 Q 已识别 T 的前提下，定义：

$$
Excess(Q;T)
=
\{\{x,y\}:T(x)=T(y),\ Q_*(x)\neq Q_*(y)\}.
$$

则：

$$
Excess(Q;T)=\varnothing
\iff
\ker Q_*=\ker T.
$$

### 证明

目标识别给出 ker(Q_*) 包含于 ker(T)。超额披露为空给出反向包含；反向由 kernel 相等直接成立。证毕。

完全显性表型可以识别当前显性／隐性性状，却不识别 carrier；这不是逻辑缺陷，而是一种目标限制隐私。

---

# Part XXVIII：实验面板作为目标相关纠错码

## 28.1 观察码距

令有限实验坐标集为 I。每个状态 x 的码字为：

$$
c_Q(x)=(q_i(x))_{i\in I}.
$$

定义 Hamming 分离数：

$$
d_Q(x,y)=|\{i:q_i(x)\neq q_i(y)\}|.
$$

对目标 T 定义：

$$
d_T(Q)=\min_{T(x)\neq T(y)}d_Q(x,y).
$$

## 定理 28.1（坐标删除鲁棒性）

删除任意至多 f 个实验后，剩余面板仍识别 T，当且仅当：

$$
d_T(Q)\ge f+1.
$$

### 证明

若每个目标不同状态对至少有 f+1 个分离坐标，删除 f 个不可能抹去全部分离。反向若某目标不同状态对仅被至多 f 个坐标分开，删除这些坐标即产生目标碰撞。证毕。

仓库 `CoordinateDeletionRobustness` 已机器验证完整状态单射版本。

## 定理 28.2（对抗错误纠正）

若：

$$
d_T(Q)\ge2e+1,
$$

则至多 e 个坐标错误时，目标类仍可唯一恢复。

### 证明

若一个接收码字同时位于两个不同目标码字的 e-球内，则三角不等式使两真实码字距离至多 2e，与最小距离矛盾。证毕。

所以遗传检测面板不仅是统计量集合，也可以按目标相关纠错码设计。

---

# Part XXIX：隐性等位基因作为预测状态中的必要记忆

## 29.1 最大稳定 residual

给定当前表型 q 与动力学 tau，定义：

$$
\mathsf C_\tau(\ker q)
=
\bigcap_{n\ge0}(\tau^n\times\tau^n)^{-1}(\ker q).
$$

仓库 `CongruenceKernel` 已机器验证：该关系是包含于 ker(q) 的最大前向同余，并且单调、收缩、幂等。

## 定理 29.1（未来显现排除表型自治）

若：

$$
q(AA)=q(Aa),
$$

但存在 n 使：

$$
q(\tau^nAA)\neq q(\tau^nAa),
$$

则不存在闭合表型动力学 bar_tau 满足：

$$
q\tau=\bar\tau q.
$$

### 证明

若下降存在，则 q(tau^n x)=bar_tau^n(q(x))，当前相等会推出所有未来相等，矛盾。证毕。

## 定理 29.2（预测记忆必要性）

设 r:X→Z 精化 q，且存在 tau_Z 使：

$$
r\tau=\tau_Zr.
$$

若 AA 与 Aa 在某个未来 q-读出上不同，则：

$$
r(AA)\neq r(Aa).
$$

所以会影响未来的隐性等位基因不能从任何精确预测状态中删除。

在有限概率模型中，可定义额外预测记忆：

$$
M_q=H(X/\mathsf C_\tau(\ker q)\mid q(X)).
$$

它衡量在知道当前表型后，为精确预测未来仍须保存多少状态信息。

---

# Part XXX：坐标干预、目标效应与修复 residual

## 30.1 四种不同的干预成功

仓库 `InterventionEffectiveness` 已机器验证：结构干预中的被选坐标最终精确等于赋值。但必须区分：

$$
\begin{aligned}
\text{坐标有效}&:x'_v=a_v,\\
\text{状态有效}&:x'\neq x,\\
\text{目标有效}&:T(x')\neq T(x),\\
\text{安全修复}&:x'\in A.
\end{aligned}
$$

完全显性模型中，Aa→AA 的编辑可以在坐标上完全成功，却保持当前表型不变。

## 30.2 修复成本

设安全集 A，允许干预 U，成本 c。定义：

$$
C_A(x)=\inf\{c(u):u\cdot x\in A\}.
$$

定义修复潜伏对：

$$
Gap_{repair}(q,A)
=
\{(x,y):q(x)=q(y),\ C_A(x)\neq C_A(y)\}.
$$

若该集合非空，则 C_A 不能经当前表型 q 因子化。

所以当前表型相同并不推出相同最小治疗、相同剂量、相同副作用或相同复发路径。

## 30.3 干预目标商

定义：

$$
u\sim_Tv
\iff
\forall x,\ T(u\cdot x)=T(v\cdot x).
$$

不同编辑操作可以在当前目标下属于同一类，而在更精细的未来或分子目标下重新分离。

---

# Part XXXI：拷贝显现阶、群体可见阶与选择阶

## 31.1 拷贝显现阶

在 p 倍体中，令 y_k 表示含 k 个 b 拷贝时的目标值。定义：

$$
r_{copy}=\min\{k\ge1:y_k\neq y_0\}.
$$

二倍体完全隐性正是：

$$
y_0=y_1\neq y_2,
\qquad
r_{copy}=2.
$$

## 定理 31.1（群体可见性阶）

若每个拷贝独立以概率 x 为 b，则含至少 r 个 b 拷贝的群体质量：

$$
M_r^{(p)}(x)=\sum_{k=r}^{p}\binom pkx^k(1-x)^{p-k}
$$

满足：

$$
M_r^{(p)}(x)=\binom prx^r+O(x^{r+1}).
$$

所以最低拷贝显现阶就是稀有等位基因进入群体表型的最低频率阶。

## 定理 31.2（选择潜伏阶）

假设 k<r 时适合度为 1，而 k=r 时适合度为 1-s，更高拷贝项有界。则：

$$
x'-x
=
-\kappa_rx^r+O(x^{r+1}),
$$

其中：

$$
\kappa_r=\frac rp\binom prs.
$$

所以：

$$
r_{copy}=r_{population}=r_{selection}
$$

在该模型中由同一最低非零作用阶控制。

## 31.3 突变—选择平衡

加入每个非 b 拷贝以概率 μ 正向突变为 b，忽略反向突变，则：

$$
x'-x
=
\mu-\kappa_rx^r+o(\mu+x^r).
$$

平衡频率满足：

$$
\boxed{
x_*=
\left(\frac{\mu}{\kappa_r}\right)^{1/r}(1+o(1)).}
$$

对应平均适合度损失：

$$
L_*=1-\bar w
\sim
\frac pr\mu.
$$

高阶隐性提高平衡等位基因频率与携带者储库，但群体负荷仍保持一阶 μ 量级。

---

# Part XXXII：跨代 test-cross 的有限与无限完成

## 32.1 理想 test-cross

未知显性表型亲本为 AA 或 Aa，与 aa 交配。

若为 AA，全部后代显性；若为 Aa，每个后代显性／隐性各半。

观察 n 个后代而未见隐性个体时，carrier 漏检概率为：

$$
2^{-n}.
$$

要使该概率不超过 α，足够取：

$$
n\ge\left\lceil\log_2\frac1α\right\rceil.
$$

## 32.2 后验更新

若先验：

$$
P(Aa)=π,
\qquad
P(AA)=1-π,
$$

连续观察 n 个显性后代后：

$$
P(Aa\mid D^n)
=
\frac{π2^{-n}}{(1-π)+π2^{-n}}.
$$

任意有限 n 都不能逻辑上排除 carrier；但出现一个隐性后代，在理想模型中立即排除 AA。

## 32.3 无限行为完成

在无限后代序列空间，事件“全部后代显性”在 AA 下概率 1，在 Aa 下概率 0。因此两个无限 transcript 律互相奇异。仓库 `SingularProbabilityPerfectSeparator` 给出一般完美分离事件。

所以有限样本逐渐压缩后验，而无限行为完成可以将两个生成机制零误差分开。

---

# Part XXXIII：环境显性相变与鲁棒边际

## 33.1 连续显性系数

沿连续上下文路径 t↦c(t)，设：

$$
y_{AA}(t),\ y_{Aa}(t),\ y_{aa}(t)
$$

连续，且两纯合体始终不同。定义：

$$
h(t)=\frac{y_{Aa}(t)-y_{aa}(t)}{y_{AA}(t)-y_{aa}(t)}.
$$

若 h(0)=1 而 h(1)=0，则介值定理保证 h 必经过所有中间值。因此连续上下文中的显性反转必须经过不完全显性或某个纯合体退化边界；真正跳变需要阈值、不连通吸引域或离散跃迁。

## 33.2 度量边际

在一般度量表型空间定义：

$$
d_A=d(y_{Aa},y_{AA}),
\qquad
d_a=d(y_{Aa},y_{aa}),
$$

$$
m_A=d_a-d_A.
$$

若每个表型点受到至多 η 的扰动，则每个距离改变至多 2η，从而：

$$
m'_A\ge m_A-4η.
$$

因此：

$$
m_A>4η
\Rightarrow
\text{显性方向在该扰动下保持。}
$$

该边际比要求精确相等更适合真实实验。

---

# Part XXXIV：锚点识别与 belief-Markov 修正版

## 34.1 锚点完整识别

设初始锚点 a，可达集 R(a)，完整行为读出 beta。仓库 `AnchorFullIdentification` 已机器验证：

$$
\text{完整锚定识别}
\iff
R(a)=X
\quad\land\quad
β\text{ 单射}.
$$

因此实验失败有两类：目标状态不可达，或可达状态在完整行为下仍碰撞。

## 34.2 相同后验为何一般不够

设未来核：

$$
Q(p,h,θ).
$$

即使两个历史 h、h' 对 θ 的后验相同，只要 Q 仍显式依赖历史，未来价值仍可不同。最小反例取单点隐藏状态，此时所有历史后验相同，却可指定不同未来 transcript 律。

## 定义 34.1（belief-Markov 条件）

存在 bar_Q 使：

$$
Q(p,h,θ)=\bar Q(p,π_h,θ),
$$

其中 π_h 为当前 belief。

## 定理 34.1（修正的后验政策充分性）

在 belief-Markov 条件下：

$$
π_h=π_{h'}
$$

推出同一策略下全部状态条件未来核相等，因此任意共同损失函数下的规则风险与 Bayes 最优值相同。

这是真正把历史压缩到后验所需的结构前件。对遗传系统，充分 belief 通常不能只包含基因型后验，还可能必须包含表观状态、损伤、年龄和代谢记忆的联合后验。

---

# Part XXXV：亲本来源、有序基因型与一般对称商

## 35.1 有序二倍体

定义：

$$
\widetilde{\mathcal G}
=\mathcal A_m\times\mathcal A_p.
$$

来源交换 involution：

$$
σ(a_m,b_p)=(b_m,a_p).
$$

无序二倍体是其轨道商。

## 定理 35.1（来源下降判据）

目标：

$$
T:\widetilde{\mathcal G}\to Y
$$

经无序商唯一下降，当且仅当：

$$
T(a_m,b_p)=T(b_m,a_p)
$$

对全部 a、b 成立。

若该等式失败，普通记号 ab 已过早合并了两个目标不同的来源状态。

## 35.2 群作用推广

若群 Γ 作用于遗传微状态 X，则目标经轨道商 X/Γ 下降，当且仅当：

$$
T(γx)=T(x)
$$

对全部 γ、x 成立。每一次使用商基因型都隐含“被商掉的对称方向对全部目标无影响”的假设。

仓库 `InvolutiveBlindResidual` 提供来源交换被旧语言隐藏、被新读出反转时的 blind-residual 形式锚点。

---

# Part XXXVI：单倍型相位与连续重组可见度

## 36.1 两位点相位

单倍型空间：

$$
\mathcal H=\{AB,Ab,aB,ab\}.
$$

coupling 与 repulsion 状态：

$$
C=\{AB,ab\},
\qquad
R=\{Ab,aB\}.
$$

二者逐位点基因型同为 (Aa,Bb)，所以逐位点接口不能恢复相位。

## 36.2 配子律

重组比例 r∈[0,1/2]。coupling 下：

$$
P_C^r(AB)=P_C^r(ab)=\frac{1-r}{2},
$$

$$
P_C^r(Ab)=P_C^r(aB)=\frac r2.
$$

repulsion 下交换上述两组概率。

## 定理 36.1（相位总变差可见度）

$$
\boxed{
d_{TV}(P_C^r,P_R^r)=|1-2r|.}
$$

当 r=0 时两律支撑不交；当 0<r<1/2 时统计可分但单次不完美；当 r=1/2 时两律同为均匀分布，相位被繁殖输出完全抹除。

因此离散相位差异通过连续重组参数被调制为连续可见强度。

## 36.3 重复后代

对 r<1/2，经验配子频率在两个相位下收敛到不同极限，因此无限独立繁殖 transcript 可渐近完美识别相位。

---

# Part XXXVII：互补粗观察、联合完成与重复的边界

## 37.1 对立显性联合恢复

取：

$$
q_1(AA)=q_1(Aa)=0,
\quad
q_1(aa)=1,
$$

$$
q_2(AA)=0,
\quad
q_2(Aa)=q_2(aa)=1.
$$

单独每个读出都合并一对基因型，但联合值分别为：

$$
AA\mapsto(0,0),
\quad
Aa\mapsto(0,1),
\quad
aa\mapsto(1,1),
$$

因此联合读出单射。

仓库 `LeastCommonReadoutRefinement` 已机器验证联合读出是最小共同精化，kernel 等于两个 kernel 的交。

## 定理 37.1（确定性重复无增益）

对：

$$
q^{[n]}(x)=(q(x),\ldots,q(x)),
$$

有：

$$
\ker q^{[n]}=\ker q.
$$

所以重复同一个无噪声粗表型不能恢复 carrier。

## 37.2 随机重复

若状态诱导的单次随机律不同，则重复样本可以估计该分布坐标；有限输出空间上，不同 i.i.d. 律的无限乘积可由经验频率极限分开。若单次律本来相同，任意重复仍相同。

必须区分 observer depth 与 sample depth：前者增加新语义坐标，后者提高对既有随机通道的估计精度。

---

# Part XXXVIII：mosaic 群体、bulk 平均与非线性 carry

## 38.1 分布值状态

细胞群体状态应表示为：

$$
μ\in Prob(V).
$$

bulk 均值接口：

$$
m(μ)=\int z\,dμ(z).
$$

取：

$$
μ=δ_0,
\qquad
ν=\frac12δ_{-1}+\frac12δ_1.
$$

二者均值均为 0，但二阶矩分别为 0 与 1。

## 定理 38.1（均值闭合判据）

对单细胞映射 f，存在 F 使：

$$
\int f(z)dμ(z)=F\left(\int zdμ(z)\right)
$$

对所有有限支撑概率分布成立，当且仅当 f 保持所有有限凸组合：

$$
f\left(\sum_iλ_iz_i\right)=\sum_iλ_if(z_i).
$$

### 证明

取 Dirac 分布得 F=f；再取任意有限混合得凸组合保持。反向直接代入。证毕。

所以 bulk 均值只有在底层响应对群体混合仿射时才是精确闭合状态。真正非线性一般会产生均值相同、未来均值不同的 mosaic carry。

---

# Part XXXIX：中性网络、突变鲁棒性与 cryptic variation

## 39.1 突变图

令基因型空间带突变图：

$$
\mathcal M=(G,E).
$$

表型纤维 q^{-1}(y) 的内部连通分量称为 neutral network。

在：

$$
AA\leftrightarrow Aa\leftrightarrow aa
$$

中，完全显性使 AA↔Aa 成为中性边，而 Aa↔aa 穿过表型边界。

## 39.2 鲁棒半径

定义：

$$
ρ_q(x)=\inf\{d_\mathcal M(x,z):q(z)\neq q(x)\}-1.
$$

距离不超过 ρ_q(x) 的突变均保持表型。

定义中性分量直径：

$$
D_{cryptic}(x;q)
=
\sup_{u,v\in\mathcal N_q(x)}d_\mathcal M(u,v).
$$

大直径表示系统可在表型不变时积累大量基因型差异。换环境目标 r 后，原来 q-中性的状态对可能被 r 分离；联合读出 kernel 等于两个环境 kernel 的交。

---

# Part XL：修复完成与治疗潜伏

## 40.1 修复 profile

定义完整响应：

$$
\mathcal R_A(x)
=
\bigl(\mathbf1_A(u\cdot x),c(u)\bigr)_{u\in\mathcal U}.
$$

两个状态治疗等价，当且仅当该 profile 相同。

可能出现：

$$
q(AA)=q(Aa),
$$

但：

$$
\mathcal R_A(AA)\neq\mathcal R_A(Aa).
$$

此时隐性等位基因不改变未治疗表型，却改变可修复性、成本、剂量或副作用。

## 40.2 修复目标非下降定理

若存在 q(x)=q(y) 但 C_A(x)≠C_A(y)，则不存在 bar_C_A 使：

$$
C_A=\bar C_A\circ q.
$$

任何精确决定修复方案的接口必须切开所有治疗潜伏对。

---

# Part XLI：统一协议完成

定义遗传协议：

$$
\mathfrak P=(Γ,\mathcal L,S,N,\mathcal T),
$$

其中：

- Γ：允许商掉的遗传对称；
- L：观察语言；
- S：时间与干预过程；
- N：重复采样规则；
- T：目标族。

协议 profile Π_P 同时记录观察、过程、随机 transcript、繁殖相位、修复响应和群体选择输出。

定义规范协议状态：

$$
Z_\mathfrak P=X/\ker Π_\mathfrak P.
$$

于是：

$$
a\triangleright_{\mathfrak P,c}b
\iff
[x_{aa,c}]_\mathfrak P
=
[x_{ab,c}]_\mathfrak P
\neq
[x_{bb,c}]_\mathfrak P.
$$

隐性就是某个差异尚未被协议 profile 分离。

---

# Part XLII：扩展遗传潜伏签名

定义：

$$
Λ^{++}(a,b;c)
=
(\partial_qC_b,d_T,f_{max},M_q,D_{origin},V_{phase},V_{mosaic},D_{cryptic},r_{copy},x_*,L_*,C_A,λ_{causal},σ_{law}).
$$

其中：

- partial_q C_b：carrier 的认识论边界；
- d_T：目标类最小实验码距；
- f_max=d_T-1：坐标删除容忍度；
- M_q：精确未来预测所需的额外记忆；
- D_origin：亲本来源交换缺陷；
- V_phase=|1-2r|：相位可见度；
- V_mosaic：bulk 平均未表达的细胞异质性；
- D_cryptic：中性网络隐藏尺度；
- r_copy：最低拷贝显现阶；
- x_*：突变—选择平衡频率；
- L_*：对应群体负荷；
- C_A：最小修复成本；
- lambda_causal：因果查询潜伏深度；
- sigma_law：统计分离类别。

传统 dominant／recessive 只是该签名在一个固定当前表型上的 Boolean 投影。

---

# Part XLIII：追加形式化路线

建议在既有规划中继续增加：

```text
D5/S3/Biology/GeneticLatency/
  FiberGeneticKnowledge.lean
  GeneticEpistemicBoundary.lean
  TargetMinimalDisclosure.lean
  TargetObservationCode.lean
  PredictiveGeneticMemory.lean
  RepairCompletion.lean
  CopyRevealOrder.lean
  TestCrossCompletion.lean
  BeliefMarkovGenetics.lean
  OrderedGenotypeOrigin.lean
  HaplotypePhaseVisibility.lean
  OpposedDominanceCompletion.lean
  RepeatedObservation.lean
  MosaicMeanClosure.lean
  NeutralMutationNetwork.lean
  MutationSelectionLatency.lean
  GeneticProtocolCompletion.lean
```

优先承重定理：

```text
carrier_possible_but_not_known_under_complete_dominance
refinement_shrinks_genetic_epistemic_boundary
target_quotient_is_minimal_disclosure
target_distance_characterizes_erasure_robustness
target_distance_corrects_adversarial_errors
future_reveal_forces_predictive_state_separation
effective_edit_does_not_imply_target_effect
copy_reveal_order_controls_population_visibility
copy_reveal_order_controls_selection_order
finite_testcross_false_negative_probability
infinite_testcross_laws_are_singular
equal_posterior_requires_belief_markov_future_kernel
ordered_genotype_target_descends_iff_swap_invariant
coupling_repulsion_gamete_tv_distance
deterministic_repetition_preserves_kernel
bulk_mean_closes_iff_map_preserves_convex_combinations
mutation_selection_latency_equilibrium
repair_gap_obstructs_phenotype_factorization
```

---

# 追加总结

本追加得到的统一链条是：

$$
\boxed{
\text{看不见}
\neq
\text{不知道}
\neq
\text{不可识别}
\neq
\text{不能影响未来}.
}
$$

$$
\boxed{
\text{无序基因型}
\to
\text{来源 residual},
\qquad
\text{逐位点基因型}
\to
\text{相位 residual},
}
$$

$$
\boxed{
\text{bulk 平均}
\to
\text{mosaic residual},
\qquad
\text{当前表型}
\to
\text{预测与修复 residual}.
}
$$

最终，遗传潜伏不是某个等位基因“没有作用”，而是一个真实差异被当前采用的对称商、聚合器、观察语言、采样深度、动力学接口或目标族压在 residual 中。显现则是该差异在新的来源坐标、单倍型查询、非线性流、随机重复、环境目标、繁殖过程、选择动力或修复任务中重新成为可分辨量。
