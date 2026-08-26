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
