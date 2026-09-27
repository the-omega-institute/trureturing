# 因果查询分辨率谱：从可执行查询到非交换方块

**Reference input.** This volume is a new, user-directed mathematical reference input. Its author kind is **AI**; author/model is **OpenAI GPT-6 via Codex**, with one read-only SSHX thinking seat used as a research prompt; source/session identifier is **the continuing user goal, 2026-09-27**. The volume is a candidate theory construction, not a Lean declaration and not a claim of literature priority. Lean declarations and their kernel-checked axiom closures remain the repository's mathematical truth source.

本卷只做纯理论生成：不做消化、atom、CAS、Lean 形式化或实验结算。它承接《因果、位置与局域事件的关系几何》中的操作性因果、事件效果与区域束缚，但提出一个更窄而更强的组织方式：把“因果”看作查询资源改变时，不可区分关系如何被切细。

本卷的 AHH 候选是：

$$
\boxed{
\text{因果箭头不是图上的一条线，}
\quad
\text{而是某个可执行查询族下非交换方块的最小分辨率证书。}
}
$$

“最小”不是预设一个标量强度，而是指查询资源偏序中的极小元。不同的时间深度、干预权限和读出精度可能互不可比，因此一个因果结论通常是一组证书，而不是一个数字。

---

# 一、模型、查询与目标

## definition 1.1: 有限实现

一个有限实现是六元组

$$
M=(S,U,A,T,O,\mu),
$$

其中 $S$ 是有限内部状态集，$U$ 是有限来源或环境状态集，$A$ 是允许的局部动作集，$T:S\times A\times U\to S$ 是一步状态转移，$O:S\to Y$ 是读出到有限结果集 $Y$ 的映射，$\mu$ 是来源 $U$ 的概率律。

一段动作词 $\alpha=(a_0,\ldots,a_{t-1})\in A^t$ 诱导递归状态

$$
\begin{aligned}
s_0&=s,\\
s_{j+1}&=T(s_j,a_j,u),\\
\operatorname{run}_M(s,u,\alpha)&=s_t.
\end{aligned}
$$

如果初态或动作标签本身是随机的，可以把它们并入扩大的来源变量；随机性不等于没有机制。

## definition 1.2: 可执行查询

一个查询实例是四元组

$$
q=(\iota,\alpha,e,\tau),
$$

其中 $\iota$ 是允许的准备规则，$\alpha$ 是动作词，$e:Y\to[0,1]$ 是结果效果，$\tau$ 是查询所允许读取的输出时间或记录位置。

查询在实现 $M$ 上产生响应数

$$
R_M(q)=\mathbb E_{u\sim\mu}\left[e\left(O\left(\operatorname{run}_M(\iota(u),u,\alpha)\right)\right)\right].
$$

离散结果的完整概率分布可以由所有指示效果恢复。若实验只能访问部分效果，则只保留该部分响应；这正是分辨率的一部分。

## definition 1.3: 查询族与查询资源

一个查询族 $\mathcal Q$ 是查询实例的集合。一个查询资源偏序是三元组

$$
(\mathsf R,\le,\mathcal Q_{(-)}),
$$

满足

$$
r\le r'\Longrightarrow \mathcal Q_r\subseteq\mathcal Q_{r'}.
$$

资源可以同时记录动作权限、最大时间、允许准备、读出效果和记录精度。例如可以令 $r=(I,H,E)$，其中 $I$ 是动作集合、$H$ 是时间深度集合、$E$ 是效果集合，按逐项包含排序。两个资源可以各自在不同坐标上更强而互不可比。

## definition 1.4: 目标与实现的可识别性

一个目标是映射

$$
C:\mathcal M\to Z,
$$

其中 $\mathcal M$ 是选定实现类，$Z$ 是目标值集。例子包括“动作端 $A$ 是否能影响输出端 $B$”、“区域 $R$ 是否在时间窗内无泄漏”、“两个实现是否具有相同的单位来源反事实”，以及“某个仪器分支是否在所有允许输入上被排除”。

目标 $C$ 在查询族 $\mathcal Q$ 下可识别，若

$$
R_M(q)=R_N(q)\quad\forall q\in\mathcal Q
\Longrightarrow
C(M)=C(N).
$$

这是关于实现类和允许查询的联合命题。只在一个初态或一个查询上观察到相同读数，不足以得到可识别性。

---

# 二、查询核与分辨率偏序

## definition 2.1: 查询不可区分关系

由查询族 $\mathcal Q$ 定义实现上的关系

$$
M\equiv_{\mathcal Q}N
\iff
R_M(q)=R_N(q)\quad\forall q\in\mathcal Q.
$$

它是一个等价关系。记其等价类划分为 $\Pi(\mathcal Q)$，记目标核为

$$
\ker C=\{(M,N):C(M)=C(N)\}.
$$

这里的“核”表示被查询或目标合并的实现对，不特指线性算子的零空间。

## theorem 2.2: 查询资源单调细化定理

若 $\mathcal Q\subseteq\mathcal Q'$，则

$$
M\equiv_{\mathcal Q'}N
\Longrightarrow
M\equiv_{\mathcal Q}N.
$$

等价地，$\Pi(\mathcal Q')$ 细于或等于 $\Pi(\mathcal Q)$；增加查询只会切细不可区分纤维，不会把原本可区分的两个实现重新合并。

### 证明

若 $M\equiv_{\mathcal Q'}N$，则对每个 $q\in\mathcal Q$，由于 $q$ 也属于 $\mathcal Q'$，有 $R_M(q)=R_N(q)$。这正是 $M\equiv_{\mathcal Q}N$。证毕。

## theorem 2.3: 目标可识别的核包含判据

目标 $C$ 在查询族 $\mathcal Q$ 下可识别，当且仅当

$$
\boxed{
\equiv_{\mathcal Q}\ \subseteq\ \ker C.
}
$$

### 证明

若可识别，查询等价的任意一对实现都具有相同目标值，所以核包含成立。

反过来，若核包含成立，$M\equiv_{\mathcal Q}N$ 立即推出 $(M,N)\in\ker C$，即 $C(M)=C(N)$。证毕。

## corollary 2.4: 目标响应因子化

目标 $C$ 在 $\mathcal Q$ 下可识别，当且仅当存在唯一映射

$$
\overline C:\operatorname{im}(\mathcal R_{\mathcal Q})\to Z
$$

使

$$
C=\overline C\circ\mathcal R_{\mathcal Q},
\qquad
\mathcal R_{\mathcal Q}(M)=(R_M(q))_{q\in\mathcal Q}.
$$

### 证明

若因子化存在，响应相同必给出目标相同。反过来，在响应像上定义 $\overline C(\mathcal R_{\mathcal Q}(M))=C(M)$。定理 2.3 保证定义与代表元无关；像上的满射性给出唯一性。证毕。

这个判据是充分边界的资源化版本：它只问查询是否切开目标所需的纤维，不要求查询恢复实现的全部细节。

---

# 三、因果箭头是一个非交换方块

## definition 3.1: 动作—演化—读出方块

固定确定性内部状态空间 $X$、动作映射族 $I_a:X\to X$、演化映射 $F:X\to X$ 和目标端读出 $O_B:X\to Y_B$。在时间 $t$ 和动作 $a$ 下的响应是

$$
\Gamma_{t,a}=O_B\circ F^t\circ I_a.
$$

比较动作 $a$ 与 $a'$ 的因果效应，就是比较两个从同一个输入空间到同一个读出空间的复合映射。

## theorem 3.2: 非交换方块的无信号判据

对允许动作集 $A_0\subseteq A$ 和时间集 $H_0\subseteq\mathbb N$，以下条件等价：

第一，查询意义下无 $A$ 到 $B$ 的影响：

$$
\Gamma_{t,a}(x)=\Gamma_{t,a'}(x)
\quad
\forall x\in X,\ \forall t\in H_0,\ \forall a,a'\in A_0.
$$

第二，每个时间层都存在与动作无关的因子 $G_t:X\to Y_B$，使

$$
\boxed{
O_B\circ F^t\circ I_a=G_t
\quad\forall a\in A_0.
}
$$

第三，所有允许动作的响应方块在目标读出后相等。

### 证明

第一推出第二：固定任意 $a_0\in A_0$，令 $G_t=O_B\circ F^t\circ I_{a_0}$。第一条件立即给出对每个 $a$ 的相等式。

第二推出第一：将两边分别取 $a$ 与 $a'$ 即得响应相等。第三只是第一条件的逐点写法。证毕。

这里的无信号是因子化而不是图形稀疏性。若中间节点承接了输入，但 $F$ 把该差异重置、丢弃或在读出前抵消，方块仍可交换。

## corollary 3.3: 影响证书

若存在

$$
x\in X,\quad t\in H_0,\quad a,a'\in A_0
$$

使

$$
O_B(F^t(I_a(x)))\ne O_B(F^t(I_{a'}(x))),
$$

则四元组 $(x,t,a,a')$ 是 $A\to B$ 的一个查询影响证书。它只证明在声明的准备、时间和读出接口下存在影响，不证明所有接口下都有影响。

### 证明

该四元组直接违反定理 3.2 的无信号条件，因此对应动作比较在该查询上可区分。证毕。

## theorem 3.4: 路径存在不是因果证书

存在有限实现，其结构图中有从动作端到读出端的有向路径，但对全部允许动作、初态和时间，目标方块仍然交换。

### 证明

取状态 $X=\{0,1\}^2$，写成 $(a,b)$，定义动作 $I_u(a,b)=(u,b)$，演化

$$
F(a,b)=(0,b),
$$

读出 $O_B(a,b)=b$。可以画出动作坐标先进入演化节点、再连接到输出节点的路径；但

$$
O_B(F(I_u(a,b)))=b
$$

与 $u$ 无关，任意更长时间仍为 $b$。所以所有方块交换而路径并未消失。证毕。

这说明图上的路径至多提供一个待检验的候选通道；实际因果内容是方块是否在允许接口上失去因子化。

---

# 四、资源谱与最小证书

## definition 4.1: 分辨率证书集

给定资源偏序 $(\mathsf R,\le)$ 和目标 $C$，定义其证书集

$$
\mathsf{Cert}(C)=\{r\in\mathsf R:\equiv_{\mathcal Q_r}\subseteq\ker C\}.
$$

其中一个 $r$ 表示一整套资源上限，而不是一次实验结果。

## theorem 4.2: 证书集是上闭集

若 $r\in\mathsf{Cert}(C)$ 且 $r\le r'$，则

$$
r'\in\mathsf{Cert}(C).
$$

### 证明

由资源单调性，$\mathcal Q_r\subseteq\mathcal Q_{r'}$，故

$$
\equiv_{\mathcal Q_{r'}}\subseteq\equiv_{\mathcal Q_r}.
$$

再由 $r\in\mathsf{Cert}(C)$ 得

$$
\equiv_{\mathcal Q_{r'}}\subseteq\ker C.
$$

证毕。

## definition 4.3: 最小分辨率证书

证书集中的极小元素组成

$$
\mathsf{MinCert}(C)=\operatorname{Min}_{\le}\mathsf{Cert}(C).
$$

若 $\mathsf R$ 不是全序，$\mathsf{MinCert}(C)$ 可以含有多个互不可比资源。它们表达不同的可行路线，例如“更长时间但较粗读出”和“较短时间但更细读出”。

## theorem 4.4: 最小证书反链定理

$\mathsf{MinCert}(C)$ 是反链：若 $r,r'\in\mathsf{MinCert}(C)$ 且 $r\le r'$，则 $r=r'$。

若资源偏序有限，则每个 $r\in\mathsf{Cert}(C)$ 上方都包含某个最小证书。

### 证明

若 $r\le r'$ 且二者不同，$r'$ 不是极小元，矛盾。因此极小证书两两不可比较。

有限偏序中的非空上闭集，从任意元素沿严格下降链必在有限步到达极小元素；上闭性保证该极小元素仍在证书集。证毕。

## proposition 4.5: 不存在普遍正确的单标量因果强度

若资源偏序含有两个互不可比的最小证书，则不存在一个只依赖资源的全序标量 $s:\mathsf R\to\mathbb R$，能够同时保持所有目标的证书极小性与资源可比关系。

### 证明

设 $r$ 与 $r'$ 互不可比，且对某个目标 $C$ 都是极小证书。任意全序标量必满足 $s(r)\le s(r')$ 或 $s(r')\le s(r)$。若把前者解释为 $r$ 资源更弱，则会错误地把 $r'$ 的独立证书压成可由 $r$ 替代；后者同理。要保持两个方向的“极小但不可替代”，必须保留偏序或其反链结构。证毕。

这里不是说不能定义某个实验项目的成本标量，而是说成本标量不能自动成为因果本体。

## definition 4.6: 实现对的分辨率谱

对实现对 $(M,N)$，定义其最小分辨率集合

$$
\mathsf{Res}(M,N)=
\operatorname{Min}_{\le}
\{r\in\mathsf R:\exists q\in\mathcal Q_r,\ R_M(q)\ne R_N(q)\}.
$$

若集合为空，记 $\mathsf{Res}(M,N)=\varnothing$。这表示在声明的资源宇宙内，两实现仍不可区分，而不是它们在所有可能理论中绝对相同。

## theorem 4.7: 目标证书与分辨率谱的对应

对目标 $C$，有

$$
r\in\mathsf{Cert}(C)
\iff
\forall M,N,\ C(M)\ne C(N)\Longrightarrow
\exists r'\le r\text{ 使 }r'\in\mathsf{Res}(M,N)\text{ 或 }r\in\mathsf{Res}^{\uparrow}(M,N),
$$

其中 $\mathsf{Res}^{\uparrow}(M,N)$ 表示包含某个最小分辨率证书的上闭集。

### 证明

若 $r$ 是目标证书，任何目标不同的实现对不能在 $\mathcal Q_r$ 下等价，因此 $r$ 上方必有一个区分它们的最小资源。

反过来，若每一目标不同的实现对都在 $r$ 的查询响应中被切开，则 $M\equiv_{\mathcal Q_r}N$ 必推出 $C(M)=C(N)$，由定理 2.3 得 $r\in\mathsf{Cert}(C)$。证毕。

---

# 五、一个延迟因果的精确例子

## definition 5.1: 延迟链模型

取状态空间 $X=\{0,1\}^3$，写成 $(x,h,b)$。动作 $I_u$ 把 $x$ 设置为 $u\in\{0,1\}$，而不改动 $h,b$。读出为 $O(x,h,b)=b$。

定义两个实现：

$$
F_{\mathrm{delay}}(x,h,b)=(x,x,h),
$$

以及

$$
F_{\mathrm{reset}}(x,h,b)=(0,0,b).
$$

初态固定为 $(0,0,0)$。两模型都允许同样的动作接口和同样的被动初始读数。

## theorem 5.2: 一步查询不能看到两步因果

在动作后只读取一步的资源 $r_1$ 下，

$$
R_{F_{\mathrm{delay}}}(I_u)=R_{F_{\mathrm{reset}}}(I_u)=0
\quad\forall u.
$$

在读取两步的资源 $r_2$ 下，

$$
R_{F_{\mathrm{delay}}}(I_u)=u,
\qquad
R_{F_{\mathrm{reset}}}(I_u)=0.
$$

因此 $r_1$ 不能识别“是否存在延迟因果链”，而 $r_2$ 可以；且 $r_1<r_2$。

### 证明

动作后，$F_{\mathrm{delay}}(u,0,0)=(u,u,0)$，而 $F_{\mathrm{reset}}(u,0,0)=(0,0,0)$，两者的 $b$ 坐标都为零。

再次演化时，延迟模型给出

$$
F_{\mathrm{delay}}(u,u,0)=(u,u,u),
$$

所以读出为 $u$；重置模型仍给出读出零。证毕。

## corollary 5.3: 当前没有变化不等于没有因果

若观察资源只包含一步读出，则两模型在该资源下完全等价；这不能推出在扩大的时间资源下仍然无影响。

### 证明

由定理 5.2，一步查询的响应完全相同，而两步查询已分离该实现对。证毕。

## proposition 5.4: 两类资源可以互补而不可互换

扩展输出为 $Y=\{0,1\}^2$，设粗效果只读取第一坐标，细效果读取第二坐标。可以构造实现对 $(M_1,N_1)$ 与 $(M_2,N_2)$，使得：

- $(M_1,N_1)$ 只能由较长时间配合粗效果分离；
- $(M_2,N_2)$ 只能由较短时间配合细效果分离；
- 同一资源坐标的“更长”或“更细”都不能单独支配另一条路线。

### 证明思路

令第一对在第二坐标始终相同、第一坐标的差异延迟到时间二；令第二对在时间一就改变第二坐标、第一坐标始终相同。将两对并入一个不相交的有限实现类即可。于是时间资源和读出资源分别切开不同纤维，二者互不可比。证毕。

---

# 六、接口瓶颈与查询闭包

## definition 6.1: 查询接口因子

设 $\kappa:\mathcal M\to K$ 是实现摘要。如果对某个查询族 $\mathcal Q$ 存在响应函数

$$
\overline{\mathcal R}:K\to\operatorname{im}(\mathcal R_{\mathcal Q})
$$

使

$$
\mathcal R_{\mathcal Q}=\overline{\mathcal R}\circ\kappa,
$$

则称 $\kappa$ 是该查询族的接口因子。

## theorem 6.2: 接口瓶颈定理

若 $\kappa$ 是 $\mathcal Q$ 的接口因子，且目标 $C$ 在某个 $\kappa$ 纤维内取不同值，则 $C$ 在 $\mathcal Q$ 下不可识别。

### 证明

若 $\kappa(M)=\kappa(N)$，接口因子化给出

$$
\mathcal R_{\mathcal Q}(M)=\mathcal R_{\mathcal Q}(N).
$$

但假设 $C(M)\ne C(N)$，违反定理 2.3 的核包含条件。证毕。

## corollary 6.3: 只能增加后处理不能恢复被合并的因果区别

若所有现有查询响应都先经过同一个摘要 $\kappa$，任何只对摘要做后处理的规则都不能识别在 $\kappa$ 纤维内变化的目标。

### 证明

后处理是摘要上的函数，仍然对同一 $\kappa$ 值给出同一结果；它不会切开原有纤维。证毕。

发现两个实现拥有相同旧读数、但目标答案不同后，应增加能切开该纤维的关系（更长续接、更强干预或更细读出），而不是继续在旧摘要上换算法。

## theorem 6.4: 查询闭包的最小性

设 $\mathcal T$ 是一个目标族。若 $\mathcal Q^*$ 满足：

1. 每个 $C\in\mathcal T$ 都在 $\mathcal Q^*$ 下可识别；
2. 删除 $\mathcal Q^*$ 中任一不可约查询都会使某个 $C\in\mathcal T$ 失去可识别性；

则 $\mathcal Q^*$ 是目标族的一个极小查询闭包。若两个极小闭包互不包含，它们对应不同的因果实验路线，不能仅凭查询数量判定优劣。

### 证明

第一条是充分性，第二条是极小性定义。两个闭包互不包含说明各自至少含有一条对方没有的必要查询；因此集合包含关系不能比较它们。证毕。

---

# 七、量子通道是同一方块的线性版本

## definition 7.1: 量子查询资源

令

$$
\mathcal N:\mathcal L(\mathcal H_A\otimes\mathcal H_B)\to\mathcal L(\mathcal H_C)
$$

是通道。一个量子查询资源 $r$ 指定允许输入集合 $\mathcal I_r$ 和输出效果集合 $\mathcal E_r$。两通道或两输入实现的查询响应由

$$
(\rho,E)\longmapsto\operatorname{Tr}[\mathcal N(\rho)E]
$$

给出。

若 $r\le r'$，要求 $\mathcal I_r\subseteq\mathcal I_{r'}$ 且 $\mathcal E_r\subseteq\mathcal E_{r'}$。

## theorem 7.2: 量子无信号是查询方块的因子化

若对所有联合输入 $\rho,\sigma$，

$$
\operatorname{Tr}_A\rho=\operatorname{Tr}_A\sigma
\Longrightarrow
\mathcal N(\rho)=\mathcal N(\sigma),
$$

则存在唯一通道 $\mathcal F:B\to C$ 使

$$
\mathcal N=\mathcal F\circ\operatorname{Tr}_A.
$$

反过来，若该因子化成立，则对所有查询资源都没有 $A$ 到 $C$ 的无条件信号。

### 证明

固定一个 $A$ 态 $\omega_A$，定义

$$
\mathcal F(X)=\mathcal N(\omega_A\otimes X).
$$

无信号假设给出对任意 $\rho$：

$$
\mathcal N(\rho)=\mathcal F(\operatorname{Tr}_A\rho).
$$

偏迹满射保证唯一性。反向代入立即成立。证毕。

## corollary 7.3: 限制效果只得到相对分辨率

若只允许效果集合 $\mathcal E_r$，则不能从响应相同推出完整输出态相同；最多得到输出在 $\mathcal E_r$ 所生成的商空间中相同。

### 证明

响应相同只给

$$
\operatorname{Tr}[(\mathcal N(\rho)-\mathcal N(\sigma))E]=0
\quad\forall E\in\mathcal E_r.
$$

若 $\mathcal E_r$ 不能分离所有 Hermitian 算子，仍存在非零差异与全部允许效果正交。证毕。

因此“没有观测到远端信号”必须带资源下标；在全效果、全输入资源下的因子化，才是模型内的无信号结构结论。

---

# 八、位置与束缚的分辨率解释

## definition 8.1: 区域泄漏查询

在有限维酉动力学 $U_t=e^{-itH/\hbar}$ 下，区域 $R$ 的投影为 $P_R$，定义时间 $t$ 的泄漏效果

$$
L_{R,t}=I-U_t^\dagger P_RU_t.
$$

对状态 $\rho$，泄漏响应为

$$
\ell_{R,t}(\rho)=\operatorname{Tr}(\rho L_{R,t})
=1-\operatorname{Tr}(U_t\rho U_t^\dagger P_R).
$$

它是一个特殊的查询：动作固定为“自由演化到 $t$”，读出只问“是否已经离开 $R$”。

## theorem 8.2: 单时刻排除与永久束缚是不同资源证书

以下三种陈述严格形成资源增强链：

1. 对给定 $\rho,t$，$\ell_{R,t}(\rho)=0$；
2. 对给定 $\rho$ 和全部 $t\in[0,T]$，$\ell_{R,t}(\rho)=0$；
3. 对所有支持于 $R$ 的 $\rho$ 和全部 $t\in\mathbb R$，$\ell_{R,t}(\rho)=0$。

第三项当且仅当

$$
[H,P_R]=0.
$$

### 证明

第一项只涉及一个状态和一个查询，不能推出第二项；延迟链或周期演化即可给出反例。

第二项比第一项包含更多查询，因此由资源单调性它更强。

第三项等价于 $U_tP_R=P_RU_t$ 对所有 $t$ 成立。对 $t=0$ 微分得到 $[H,P_R]=0$；反向由函数演算得到 $U_tP_R=P_RU_t$，再代入泄漏式即得。证毕。

## corollary 8.3: 位置约束是零泄漏纤维而不是额外力量

在给定动力学和查询资源下，位置持续留在 $R$ 的含义是状态落在泄漏查询的零纤维；当资源升级为“所有时间、所有区域内初态”时，该零纤维结构等价于 Hamiltonian 的区域分块对角性。

### 证明

第一句是 $\ell_{R,t}(\rho)=0$ 的定义。第二句由定理 8.2 的第三项给出。证毕。

---

# 九、反事实层与单位来源保持

## definition 9.1: 单位来源查询

令实现写成 $f_M(u,a)$，其中 $u$ 是同一来源单位、$a$ 是局部动作。单位来源反事实查询固定 $u$，比较

$$
\bigl(f_M(u,a)\bigr)_{a\in A_0}.
$$

分布查询只比较

$$
\operatorname{Law}_{u\sim\mu}(f_M(u,a))
$$

而不保留同一个 $u$ 的配对。

## theorem 9.2: 分布资源与单位来源资源的严格分辨率差

存在两个实现 $M,N$，使所有动作下的输出分布相同，但单位来源反事实查询不同。

### 证明

取 $u\in\{0,1\}$ 均匀。令

$$
f_M(u,a)=u,
\qquad
f_N(u,a)=u\oplus a.
$$

对每个固定 $a$，两者输出都为均匀位，因此分布查询完全相同。固定 $u$ 后，$M$ 对动作不变，而 $N$ 在 $a=1$ 时翻转，故单位来源 profile 不同。证毕。

## corollary 9.3: 反事实层不是统计层的自动极限

增加更多动作的边缘分布，不必然获得单位来源反事实；要进入更高分辨率层，查询接口必须保留同一来源单位或一个已证的耦合关系。

### 证明

定理 9.2 给出同一统计响应纤维中的两个不同反事实目标，因此只在该纤维上继续收集同类边缘分布不能识别目标。证毕。

这也是为什么“完整联合分布”与“完整反事实图”不能混写：后者包含跨动作的同源配对结构。

---

# 十、统一定理：因果是查询核上的非闭合目标

## theorem 10.1: 因果证书统一定理

设 $C$ 是任何由有限实现定义的目标，且 $\mathcal Q_r$ 是单调查询资源族。则以下四种说法等价地描述同一个结构：

1. $r$ 足以识别 $C$；
2. $\equiv_{\mathcal Q_r}\subseteq\ker C$；
3. $C$ 因子化通过响应摘要 $\mathcal R_{\mathcal Q_r}$；
4. 每一对目标不同的实现，都有一个资源不超过 $r$ 的查询响应将其分开。

对因果目标，若 $C(M)$ 记录“某动作能否改变某输出”，则其最小证书就是最小的非交换方块查询；对位置目标，最小证书是最小的非零泄漏或全时零泄漏查询；对反事实目标，最小证书还必须包含同源配对资源。

### 证明

1 与 2 是定理 2.3，2 与 3 是推论 2.4，2 与 4 是实现对的逐纤维展开。最后三种实例分别由定理 3.2、定理 8.2 与定理 9.2 的资源定义得到。证毕。

## proposition 10.2: AHH 结构的最短表述

在本卷模型内，“$A$ 因果影响 $B$”不是一个脱离接口的二元事实，而是以下带下标命题：

$$
\operatorname{Causal}_{\mathcal Q}(A\to B;M)
\iff
\exists q\in\mathcal Q,\quad
R_{M,\operatorname{do}(A=a)}(q)\ne R_{M,\operatorname{do}(A=a')}(q).
$$

若改用更丰富的查询族，命题可能从不可识别变成可识别；若把目标从边缘分布升级为单位来源反事实，原有查询族可能再次不足。因果关系的几何形状因此是一个随查询资源变换的等价类谱。

### 证明思路

这是非交换方块、查询核和资源单调性的共同展开：存在差异是一个证书，查询族不足时差异落在同一纤维，查询族扩张时纤维只能细化。证毕。

---

# 十一、边界、反例与开放问题

## proposition 11.1: 图同构不保持查询谱

两个实现可以有相同的静态有向图、相同的被动观察分布，甚至相同的节点标签，但具有不同的干预查询谱。

### 证明思路

把定理 3.4 的重置模型与延迟模型放在相同的三节点图上，再只改变局部转移方程。被动初态可取相同，主动响应却分别恒定和延迟显现。因此图同构与查询谱相同之间没有逻辑蕴含。证毕。

## proposition 11.2: 单个静态暗点不产生永久无因果

若某个 $t_0$ 和 $\rho$ 满足 $\ell_{R,t_0}(\rho)=0$，不能推出 $[H,P_R]=0$，也不能推出之后全部查询都为零。

### 证明

取两能级 Hamiltonian $H=\hbar gX$、初态 $|0\rangle\langle0|$ 和单模式区域投影 $P_0$。有

$$
\operatorname{Tr}(\rho_tP_0)=\cos^2(gt),
$$

在 $t_0=0$ 时泄漏为零，但对一般 $t$ 不为零，且 $[H,P_0]\ne0$。证毕。

## open problem 11.3: 连续时空中的查询资源极限

当时间、位置和效果族不再有限时，需要给出资源偏序的拓扑或测度结构，使“极小证书”“资源极限”和“查询闭包”不依赖任意枚举。尚未解决的具体问题包括：

1. 何种紧致性条件保证目标证书集存在极小元；
2. 何种连续性把有限时间查询的上闭集极限送到光锥或半群结构；
3. 测量资源的实验成本如何与偏序保持可组合；
4. 在开放量子系统中，环境记忆应被视为来源坐标、续接资源还是新的目标层。

## open problem 11.4: 资源谱的联合实现

分别对两个目标找到的最小证书不一定能在同一个实验实现中同时达到。需要一个联合实现定理，刻画

$$
\mathsf{MinCert}(C_1)\times\mathsf{MinCert}(C_2)
$$

何时存在共同的准备、来源、仪器和历史。边缘资源可达不等于联合资源同时可达。

---

# 十二、来源、核验边界与原创性状态

| 来源 | 精确范围与使用边界 |
| --- | --- |
| CAUSAL_LOCATION_LOCAL_EVENT_RELATION_GEOMETRY.md | repo-derived：无信号因子化、事件效果支撑、Hamiltonian 区域不变与记录接口；本卷把这些读作查询资源的实例，不声称重复证明即取得新 Lean 真值。 |
| GENETIC_LATENCY_COMPLETION_THEORY.md | repo-derived：观察—干预—反事实层级和因果潜伏的已有表述；本卷只借用其问题分层，不把其章节号当作本卷地址。 |
| CIRPT_FORMAL_CONCEPT_DYNAMICS_RECONSTRUCTION.md | repo-derived：未来响应、商关系和边界语言；本卷把它们重组为资源偏序与证书反链。 |
| 外部文献 | 本轮未做逐条文献核对；不标记任何外部命题为 literature-attested。 |
| 查询分辨率谱、非交换方块的证书反链 | suspected-novel：这是本卷的候选综合，不是原创性结论；需要后续文献搜索和反例审查。 |

**核验边界。** 本卷证明均为有限集合、有限时间或有限维线性代数中的纸面推导。它没有给出 Lean 编译证据，没有证明连续时空、无限资源或真实实验中的实现定理，也没有把候选综合升级为已验证的项目数学真值。

---

# 十三、AHH 时刻的工作定义

本卷暂把 AHH 时刻记录为下面这条可检验的研究命题，而不是心理状态：

> **当一个因果问题的答案随查询资源改变时，真正稳定的对象不是某一条箭头，而是从资源偏序到不可区分划分的单调映射；因果结论是这个映射上某个目标核的上闭证书集。**

它带来四个直接后果：

1. “有路径”只能提出证书搜索任务；
2. “没有观察到变化”只能在声明的查询纤维内成立；
3. “位置被束缚”是泄漏查询的全时间零纤维，不是额外的钉住力量；
4. “反事实更深”意味着保留同一来源的联合结构，而不是把更多边缘分布堆起来。

若后续反例显示这些后果不能在同一资源框架中共存，本卷应把 AHH 命题降为局部类比，并保留失败边界。

# 十四、带成本的类型化查询晶格

前面的资源偏序只记录“能问哪些问题”。为了把分辨率谱变成可比较的研究对象，还要把查询的语义类型和取得代价写入同一接口。下面这一批是本卷相对于单纯核包含表述的新增层；它仍是有限模型中的候选理论，不是已经编译的项目定理。

## definition 14.1: 四类类型化查询

固定有限实现类 $\Theta$。查询类型分为：

1. $\operatorname{Obs}_h$：不施加动作，只读取长度为 $h$ 的轨迹律；
2. $\operatorname{Int}_w$：施加动作词 $w$，读取单一世界的终点或轨迹律；
3. $\operatorname{Cont}_{h,v}$：先取得历史 $h$，再施加续接词 $v$，读取条件未来律；
4. $\operatorname{CF}_{(w_i)_{i\le k}}$：固定同一个来源单位，同时读取多个动作词的联合响应。

若条件历史概率为零，$\operatorname{Cont}$ 的响应定义为特殊符号 $\bot$，因此类型在全部输入上总定义。$\operatorname{CF}$ 必须显式携带共同来源耦合；相同的各个边缘律不自动给出同一个反事实联合律。

## definition 14.2: 类型化响应画像与伪距离

令 $q$ 是任一类型化查询，$P_\theta(q)$ 是其有限结果空间上的精确概率律。对有限查询族 $\Gamma$，定义画像

$$
\Phi_\Gamma(\theta)=\bigl(P_\theta(q)\bigr)_{q\in\Gamma},
$$

以及

$$
\Pi_\Gamma
=\{(\theta,\theta'):\Phi_\Gamma(\theta)=\Phi_\Gamma(\theta')\}.
$$

令 $\operatorname{TV}$ 是总变差距离，定义

$$
d_\Gamma(\theta,\theta')
=\max_{q\in\Gamma}
\operatorname{TV}\bigl(P_\theta(q),P_{\theta'}(q)\bigr),
$$

空查询族的距离规定为零。于是

$$
d_\Gamma(\theta,\theta')=0
\iff
(\theta,\theta')\in\Pi_\Gamma.
$$

给每个查询一个非负整数成本 $c(q)$，查询族成本为

$$
\operatorname{cost}(\Gamma)=\sum_{q\in\Gamma}c(q).
$$

## theorem 14.3: 查询晶格的交与严格切分

对任意有限查询族 $\Gamma,\Delta$，有

$$
\boxed{
\Pi_{\Gamma\cup\Delta}
=\Pi_\Gamma\cap\Pi_\Delta.
}
$$

并且

$$
\Pi_{\Gamma\cup\{q\}}\subsetneq\Pi_\Gamma
$$

当且仅当存在 $\theta,\theta'\in\Theta$，使

$$
(\theta,\theta')\in\Pi_\Gamma,
\qquad
P_\theta(q)\ne P_{\theta'}(q).
$$

### 证明

联合画像相等，当且仅当它在 $\Gamma$ 坐标上相等且在 $\Delta$ 坐标上相等，这给出第一式。

加入 $q$ 后仍然属于 $\Pi_\Gamma$，所以只可能细化。严格性等价于存在旧纤维内的一对实现被新坐标分开，这正是第二式中的见证。证毕。

## theorem 14.4: 有限目标的首次充分预算

令目标 $T:\Theta\to Z$，且 $\Theta$ 与允许查询集合均有限。定义

$$
B_T=
\min\left\{
\operatorname{cost}(\Gamma):
\Pi_\Gamma\subseteq\ker T
\right\},
$$

若不存在充分查询族则令 $B_T=\infty$。则：

1. $\operatorname{cost}(\Gamma)\ge B_T$ 当且仅当 $\Gamma$ 至少达到某个充分查询族的成本；
2. $B_T<\infty$ 时，最小值由某个查询族取得；
3. $B_T$ 是目标首次完全分离所需的查询预算，而不是实现细节完全恢复所需的预算。

### 证明

有限性保证查询族只有有限多个，故非空可行成本集合是有限自然数集合并取得最小值。核包含判据给出充分性；目标核通常大于实现恒等核，所以目标预算不要求恢复全部实现。证毕。

## theorem 14.5: 预算谱只能细化且只在新见证处跳变

设 $\Gamma_b$ 是成本不超过 $b$ 的查询族，且 $b\le b'$ 时 $\Gamma_b\subseteq\Gamma_{b'}$。则

$$
\Pi_{\Gamma_{b'}}\subseteq\Pi_{\Gamma_b},
\qquad
d_{\Gamma_b}\le d_{\Gamma_{b'}}.
$$

预算 $b'$ 处发生严格切分，当且仅当新增查询中存在一对此前属于同一 $\Pi_{\Gamma_b}$ 纤维、而在新增响应上不同的实现。若当前实现类有 $m$ 个初始等价类，则严格切分次数至多为 $m-1$。

### 证明

第一部分由定理 2.2 与总变差最大值的集合包含性直接得到。严格跳变由定理 14.3 的见证刻画。

每次严格切分至少把一个等价类分成两个，类数至少增加一；从 $m$ 个初始类开始，严格增加次数至多达到单点划分所需的 $m-1$ 次。证毕。

## theorem 14.6: 共同来源反事实严格增加分辨率

存在有限实现对 $\theta_S,\theta_F$，使得所有 $\operatorname{Obs}$ 与 $\operatorname{Int}$ 查询的概率律相同，但某个共同来源反事实查询 $\operatorname{CF}$ 的联合律不同。因此

$$
\Pi_{\Gamma\cup\{\operatorname{CF}\}}
\subsetneq
\Pi_\Gamma
$$

其中 $\Gamma$ 只含 $\operatorname{Obs}$ 与 $\operatorname{Int}$ 查询。

### 证明

取共同来源 $u=(x,z)\in\{0,1\}^2$ 均匀，动作 $a\in\{0,1\}$ 记为 setX。两实现都读出 $X=x$；在无动作时都读出 $Y=z$。在动作 $a$ 后，令

$$
\theta_S:\ Y=z,
\qquad
\theta_F:\ Y=z\oplus a.
$$

对每个固定 $a$，$Y$ 都是均匀位，因而全部单世界边缘查询相同。固定同一个 $u$ 比较 $a=0,1$ 时，$\theta_S$ 给出

$$
(Y_0,Y_1)=(z,z),
$$

而 $\theta_F$ 给出

$$
(Y_0,Y_1)=(z,z\oplus1).
$$

前者联合结果总相等，后者总不相等，所以共同来源反事实查询切开旧纤维。证毕。

## corollary 14.7: 反事实深度不能由边缘查询数量替代

在定理 14.6 的实现对中，无论增加多少同类的单世界边缘动作，只要不引入共同来源耦合或等价的联合约束，目标“两个动作是否作用于同一来源单位上的同一响应”仍不可识别。

### 证明

两实现对每个动作的边缘律相同，因此所有只读取这些边缘的查询仍落在同一纤维；定理 6.2 和定理 14.6 给出不可识别性。证毕。

## proposition 14.8: AHH 的带价版本

若目标是“实现具有某种因果结构”，则最小证书不只是最少查询数，而是一个带价的极小查询族：

$$
\mathsf{MinCert}_c(T)
=
\operatorname{Min}_{\subseteq}
\left\{
\Gamma:
\Pi_\Gamma\subseteq\ker T
\right\},
\qquad
\operatorname{value}(\Gamma)=\operatorname{cost}(\Gamma).
$$

两个极小查询族可以具有同样的目标充分性而不同的成本；成本更低者只是给定实验合同下更经济，不因此成为因果本体上更“真实”的箭头。

### 证明思路

查询晶格的严格切分由定理 14.3 给出，目标充分性由定理 2.3 给出，成本只是在可行集合上施加的附加序。把成本序误写成目标真值会把实验设计偏好冒充结构事实。证毕。

---

# 十五、本批导航与新增边界

本批把前文的抽象资源偏序具体化为四类带类型查询，并增加了成本、总变差距离、有限预算谱和共同来源联合律。它扩充了前文，而不改判前文的有限无信号、区域泄漏或反事实分布分离陈述。

SSHX 思考席将本方向判为 **recombination**：查询核格、观察—干预—反事实层和未来同余在仓内已有相邻材料。本卷新增的候选范围是把它们放进同一个**带成本的类型化查询接口**，并给出预算跳变与共同来源耦合的明确见证；这仍需逐条文献搜索和后续反例审查。

## 追加锚（本行以下为增补区）
