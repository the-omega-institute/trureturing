# 因果、位置与局域事件的关系几何

**Reference input.** This volume is user-supplied mathematical reference input. Its author kind is **AI**; author/model is **OpenAI GPT-6 via Codex**; source/session identifier is **the user-provided conversation, 2026-09-27**. The prose records definitions, conditional arguments, and claimed proofs; Lean declarations and their kernel-checked axiom closures remain the repository's mathematical truth source. The volume is not itself Lean-verified.

本轮固定在 `dev` 的 `2ba91a5665`。核对的实际接口包括《动态充分边界与内部观察者》、布尔干预—反事实分离、`WordProbabilityTraceRepresentation`，以及 `ProjectionProbabilityFlow`。以下采用独立编号，给出这些接口上的自包含推导；不将本回答宣称为新增且已编译的 Lean 证明。

---

# 一、静态相关形状，还不足以决定因果

## definition 1.1: 允许局部替换的关系模型

一个有限确定性结构模型由变量、共同来源变量 $u$ 和局部方程组成：

$$
x_v=f_v(x_{\operatorname{pa}(v)},u).
$$

依赖图无有向环，因此给定 $u$ 后，全部变量可以依次确定。

干预：

$$
\operatorname{do}(x_a=\alpha)
$$

表示将节点 $a$ 的局部方程替换为常值 $\alpha$，其他机制与来源律保持不变。

这里的“替换权限”属于模型。如果实际观察者不能执行这种操作，它只是模型中的反事实比较，不能冒充已经取得的实验结果。

## definition 1.2: 指定接口下的可检测因果影响

在同一个其余实验条件 $c$ 下，若存在两种允许的局部操作 $a_0,a_1$，使目标端 $B$ 的结果分布不同：

$$
p_c(y_B\mid\operatorname{do}(a_0))
\ne
p_c(y_B\mid\operatorname{do}(a_1)),
$$

则称该接口检测到了 $A$ 对 $B$ 的因果影响。

这是一个**操作性影响定义**，不是把所有因果内容压成一次统计比较。下面的两个定理说明其边界。

## theorem 1.3: 同一个观察分布，可以对应不同的因果方向

存在两个有限模型，它们的完整可见联合分布相同，但执行同一个局部干预后，目标分布不同。

### 证明

取均匀随机位：

$$
U\in\{0,1\}.
$$

定义模型：

$$
M:\quad X=U,\qquad Y=X,
$$

以及：

$$
N:\quad Y=U,\qquad X=Y.
$$

不干预时，两模型都满足：

$$
p(X=0,Y=0)=p(X=1,Y=1)=\frac12.
$$

所以完整可见联合分布相同。

执行 $\operatorname{do}(X=0)$。

在 $M$ 中：

$$
Y=X=0,
$$

因此 $p(Y=0)=1$。

在 $N$ 中，$Y=U$ 的机制不变，所以：

$$
p(Y=0)=\frac12.
$$

两者不同。证毕。

### 结论

$$
\boxed{
\text{哪些读数能够一起出现}
\quad\text{不唯一决定}\quad
\text{改变一个局部后会怎样}.
}
$$

因此，纯关系几何若要具有因果内容，必须保存**允许的局部替换与替换后的续接关系**，而不只是保存一张静态联合值表。

## theorem 1.4: 相同的全部干预边缘，也不一定恢复单位层面的依赖

令来源位 $u$ 均匀分布，控制位为 $a$。定义：

$$
f_0(u,a)=u,
$$

$$
f_1(u,a)=u\oplus a.
$$

则两模型对每个固定控制 $a$，输出分布都为均匀分布；但对固定来源单位 $u$，控制的作用不同。

### 证明

在 $f_0$ 中，无论 $a$ 是什么，输出都是均匀位 $u$。

在 $f_1$ 中，$a=0$ 时输出 $u$，$a=1$ 时输出 $1-u$，两者也都均匀。

因此所有控制下的边缘分布相同。

但对每个固定 $u$：

$$
f_0(u,0)=f_0(u,1),
$$

而：

$$
f_1(u,0)\ne f_1(u,1).
$$

证毕。

项目的 `InterventionCounterfactualSeparation` 与 `CounterfactualKernelStrictlyFiner` 已经形式化了这一具体分离及其核包含关系。

**所以，因果分析必须保留三层区别：观察相关、干预后的分布、同一来源单位的反事实依赖。**

这条经典结果不授权我们给所有不相容的量子测量预填一个共同结果表。

# 二、量子因果：哪些输出真正依赖某个输入端？

下面给出有限维通道中一个精确的“无因果信号”判据。此类因果与半因果通道是标准量子信息研究对象。

## definition 2.1: 输入端与输出端

固定有限维空间：

$$
\mathcal H_A,\qquad\mathcal H_B,\qquad\mathcal H_C,
$$

以及量子通道：

$$
\mathcal N:
\mathcal L(\mathcal H_A\otimes\mathcal H_B)
\to
\mathcal L(\mathcal H_C).
$$

其中 $C$ 是所关心的输出端。

称 **$A$ 对 $C$ 无信号作用**，若对任意联合输入 $\rho,\sigma$：

$$
\operatorname{Tr}_A\rho=\operatorname{Tr}_A\sigma
\Longrightarrow
\mathcal N(\rho)=\mathcal N(\sigma).
$$

也就是说：保持 $B$ 输入相同，改变 $A$ 及其与 $B$ 的关联，仍不改变 $C$ 的输出。

这是对全部输入的结构性质，比“某个初态上没观察到变化”更强。

## theorem 2.2: 无信号、边缘因子化与对偶局域性的等价

以下条件等价。

**第一，无信号：**

$$
\operatorname{Tr}_A\rho=\operatorname{Tr}_A\sigma
\Longrightarrow
\mathcal N(\rho)=\mathcal N(\sigma).
$$

**第二，存在唯一量子通道 $\mathcal F:B\to C$，使：**

$$
\boxed{
\mathcal N=\mathcal F\circ\operatorname{Tr}_A.
}
$$

**第三，对每个输出效果 $0\preceq E\preceq I_C$，存在 $B$ 上的效果 $G_E$，使：**

$$
\boxed{
\mathcal N^*(E)=I_A\otimes G_E.
}
$$

### 证明

**第一推出第二。**

固定任意 $A$ 态 $\omega_A$，定义：

$$
\mathcal F(X)=\mathcal N(\omega_A\otimes X).
$$

准备 $\omega_A$、张量输入与 $\mathcal N$ 的复合都是完全正保迹的，因此 $\mathcal F$ 是通道。

对任意密度矩阵 $\rho_{AB}$，它与：

$$
\omega_A\otimes\operatorname{Tr}_A\rho_{AB}
$$

具有相同的 $B$ 边缘。故：

$$
\mathcal N(\rho_{AB})
=
\mathcal F(\operatorname{Tr}_A\rho_{AB}).
$$

密度矩阵线性张成整个矩阵空间，所以等式对全部算子成立。

偏迹是满射的，因此 $\mathcal F$ 唯一。

**第二推出第三。**

对任意输入 $\rho$：

$$
\begin{aligned}
\operatorname{Tr}[\rho\mathcal N^*(E)]
&=\operatorname{Tr}[\mathcal N(\rho)E]\\
&=\operatorname{Tr}[\operatorname{Tr}_A\rho\,\mathcal F^*(E)]\\
&=\operatorname{Tr}[\rho(I_A\otimes\mathcal F^*(E))].
\end{aligned}
$$

迹配对非退化，因此：

$$
\mathcal N^*(E)=I_A\otimes\mathcal F^*(E).
$$

**第三推出第一。**

若 $\rho,\sigma$ 具有相同的 $B$ 边缘，则对每个效果 $E$：

$$
\begin{aligned}
\operatorname{Tr}[(\mathcal N(\rho)-\mathcal N(\sigma))E]
&=
\operatorname{Tr}[(\rho-\sigma)(I_A\otimes G_E)]\\
&=0.
\end{aligned}
$$

全部效果能够分离密度矩阵，所以输出相同。证毕。

### 几何读法

把输出检验沿关系反向拉回：

- 若拉回后完全不需要 $A$ 的坐标，$A$ 不能影响该输出；
- 若它确实依赖 $A$，则需要进一步检验允许准备与操作能否显现这种依赖。

$$
\boxed{
\text{因果不只是图上有线，}
\quad
\text{而是输出关系是否真正依赖该输入端}.
}
$$

## corollary 2.3: 纠缠本身不允许远端任意控制本地读数

对任意联合态 $\rho_{AB}$ 和任意 $A$ 上的通道 $\mathcal E_A$：

$$
\boxed{
\operatorname{Tr}_A
[(\mathcal E_A\otimes\operatorname{id}_B)(\rho_{AB})]
=
\operatorname{Tr}_A\rho_{AB}.
}
$$

### 证明

写：

$$
\mathcal E_A(X)=\sum_jK_jXK_j^\dagger,
\qquad
\sum_jK_j^\dagger K_j=I_A.
$$

对任意 $B$ 效果 $F$，操作后的概率为：

$$
\sum_j
\operatorname{Tr}[\rho_{AB}(K_j^\dagger K_j\otimes F)]
=
\operatorname{Tr}[\rho_{AB}(I_A\otimes F)].
$$

全部 $B$ 效果的概率相同，故边缘相同。证毕。

条件于 $A$ 的特定结果，$B$ 的条件态可以改变；但这不是无条件的远端信号。结果标签仍须通过允许的关系传递。

# 三、局域机制怎样形成因果锥？

## definition 3.1: 有限局域过程网络

设一份有限无环量子网络由带输入、输出端口的局部通道组成。

每条量子输出线只连接到其指定后继输入；经典控制、测量结果、共同参考和环境记忆若会影响后续，也必须作为相应端口保留。

对输出端 $B$，定义其图论祖先区域：

$$
\operatorname{Past}(B),
$$

即沿有向连线能够接到 $B$ 的全部局部节点。

## theorem 3.2: 无有向路径，意味着无该方向的可控影响

若节点 $A\notin\operatorname{Past}(B)$，那么在相同输入和其他局部机制下，将 $A$ 的通道替换为任意另一合法通道，不改变 $B$ 的边缘输出。

### 证明

取 $B$ 的任意效果 $F_B$，把其他终端放置为恒等效果。

沿网络反向拉回检验。

若一个节点的所有输出上只有恒等效果，由其通道保迹：

$$
\mathcal E^*(I)=I,
$$

该节点被消去，且不依赖它具体是哪一个通道。

递归消去所有不属于 $B$ 祖先的节点。因为 $A$ 不在祖先区域，它对最终拉回效果没有贡献。

所以任意输入与这个效果的迹配对不变，全部 $B$ 输出概率不变。证毕。

这是量子电路因果结构的一种直接证明；局部机制、噪声来源与因果图之间的更一般对应已有量子因果模型框架。

### 两个边界

**有路径不保证有非零影响。** 中间通道可能丢弃输入、输出固定态；不同贡献也可能抵消。

**任意稀疏 Hamiltonian 图也不自动给出相对论光锥。** 连续传播：

$$
e^{-itH/\hbar}
=
\sum_{k=0}^{\infty}
\frac{(-it/\hbar)^k}{k!}H^k
$$

会汇总所有阶数。某个矩阵元的低阶项为零，不等于它对所有小的非零时间严格为零。

因此，从关系网络恢复物理光锥，还需要明确的局域动力学及连续极限条件，不能只看邻接矩阵。

# 四、位置事件何时被禁止，何时被确定？

## definition 4.1: 位置是相对于接口的读数

固定有限位置或模式标签集：

$$
X=\{1,\ldots,d\}.
$$

单激发空间为：

$$
\mathcal H_1=\operatorname{span}\{|x\rangle:x\in X\}.
$$

对区域 $R\subseteq X$，定义位置投影：

$$
P_R=\sum_{x\in R}|x\rangle\langle x|.
$$

若当前态为 $\rho$，理想区域检验概率为：

$$
p(R)=\operatorname{Tr}(\rho P_R).
$$

这里 $x$ 是已声明的模式或有限探测单元，不是已经取得一个无限精确的连续坐标。

更一般地，一个带钟、探测方式和结果标签的事件 $e$，对应仪器分支：

$$
\Phi_e(\rho)=\sum_\alpha K_{e,\alpha}\rho K_{e,\alpha}^\dagger,
$$

以及效果：

$$
E_e=\sum_\alpha K_{e,\alpha}^\dagger K_{e,\alpha},
\qquad
0\preceq E_e\preceq I.
$$

它的概率为：

$$
p_\rho(e)=\operatorname{Tr}(\rho E_e).
$$

这些是标准量子状态与测量的操作定义。

## theorem 4.2: 事件排除与事件确定的精确判据

设 $\rho$ 为密度矩阵，$0\preceq E\preceq I$。则：

$$
\boxed{
\operatorname{Tr}(\rho E)=0
\iff
\operatorname{supp}\rho\subseteq\ker E,
}
$$

以及：

$$
\boxed{
\operatorname{Tr}(\rho E)=1
\iff
\operatorname{supp}\rho\subseteq\ker(I-E).
}
$$

### 证明

因为：

$$
\operatorname{Tr}(\rho E)
=
\operatorname{Tr}(\sqrt\rho E\sqrt\rho)
=
\|\sqrt E\sqrt\rho\|_{\mathrm{HS}}^2,
$$

其为零，当且仅当：

$$
\sqrt E\sqrt\rho=0.
$$

$\sqrt\rho$ 的像空间是 $\operatorname{supp}\rho$，而 $\sqrt E$ 与 $E$ 核相同，因此得到第一式。

又因为：

$$
1-\operatorname{Tr}(\rho E)
=
\operatorname{Tr}[\rho(I-E)],
$$

对 $I-E$ 应用第一式即可得到第二式。证毕。

### 这正面回答了“是什么约束它在那里”

在该模型中：

- **不可能出现**：当前态的支撑完全落在该事件效果的零空间；
- **确定出现**：当前态的支撑完全落在该效果的本征值一空间；
- **介于两者之间**：模型给出非平凡概率，而非唯一结果。

这些是状态与探测关系的相容性，不是一种额外的“因果推力”。

## corollary 4.3: 对所有来源禁止，与对某个来源禁止不同

有：

$$
\boxed{
 p_\rho(e)=0\quad\forall\rho
\iff
E_e=0.
}
$$

但对某个 $\rho$ 有 $p_\rho(e)=0$，不必意味着 $E_e=0$。

### 证明

若 $E_e=0$，结论显然。

反过来，若 $E_e\ne0$，其正半定性保证存在单位向量 $\psi$ 使：

$$
\langle\psi|E_e|\psi\rangle>0.
$$

取 $\rho=|\psi\rangle\langle\psi|$ 即产生正概率，矛盾。证毕。

**因此，一次准备中的暗点，不能直接当成整个过程的因果禁区。**

## corollary 4.4: 首次定位事件的相容性

沿用前文的未点击分支 $Q$ 与局域点击分支 $L_x$，则：

$$
\boxed{
 p_\rho(n,x)
=
\|L_xQ^{n-1}\sqrt\rho\|_{\mathrm{HS}}^2.
}
$$

所以：

$$
\boxed{
 p_\rho(n,x)=0
\iff
L_xQ^{n-1}\sqrt\rho=0.
}
$$

### 证明

第 $n$ 轮首次点击的分支算子为：

$$
K_{n,x}=L_xQ^{n-1}.
$$

其概率是：

$$
\operatorname{Tr}(K_{n,x}\rho K_{n,x}^\dagger),
$$

等于所给范数平方。证毕。

这把准备、此前未点击的更新、相干传播与局域探测，全都放入同一个约束式。

# 五、什么能让粒子持续留在一个区域？

“这一刻的探测概率集中在 $R$”与“以后一直不会离开 $R$”是不同命题。

## definition 5.1: 固定动力学下的区域不变性

设：

$$
H=H^\dagger,
\qquad
U_t=e^{-itH/\hbar},
\qquad \hbar>0.
$$

取区域投影 $P=P_R$，记：

$$
Q_R=I-P.
$$

称 $R$ 对该动力学**普适不变**，若对每个满足：

$$
\rho=P\rho P
$$

的初态，以及全部 $t\in\mathbb R$，都有：

$$
U_t\rho U_t^\dagger
=
P\,U_t\rho U_t^\dagger P.
$$

## theorem 5.2: 永久区域束缚等价于跨边界耦合为零

下列条件等价：

$$
R\text{ 对该动力学普适不变};
$$

$$
\boxed{
Q_RHP=0;
}
$$

$$
\boxed{
[H,P]=0.
}
$$

### 证明

**区域不变推出跨界耦合为零。**

取任意 $\psi\in\operatorname{ran}P$。区域不变性给：

$$
Q_RU_t\psi=0
\qquad\forall t.
$$

在 $t=0$ 微分：

$$
Q_R\left(-\frac{i}{\hbar}H\right)\psi=0.
$$

因此 $Q_RHP=0$。

**跨界耦合为零推出对易。**

由于 $H$ 自伴，取伴随得到：

$$
PHQ_R=0.
$$

所以 $H$ 在：

$$
\mathcal H=\operatorname{ran}P\oplus\operatorname{ran}Q_R
$$

上分块对角，故 $[H,P]=0$。

**对易推出区域不变。**

若 $[H,P]=0$，则 $U_tP=PU_t$。于是：

$$
U_t\rho U_t^\dagger
=
U_tP\rho PU_t^\dagger
=
P\,U_t\rho U_t^\dagger P.
$$

证毕。

### 精确含义

$$
\boxed{
\text{在给定闭系统动力学下，区域永久封闭}
\iff
\text{不存在穿过该区域边界的耦合块}.
}
$$

量词是“对该区域内所有初态”。某个特殊暗态可能留在区域中，并不要求整个区域都封闭。

如果持续插入测量，动力学已经改变，必须分析新的仪器过程；不能直接套用这个固定酉演化定理。

## corollary 5.3: 精确固定在一个模式的条件

对：

$$
P_x=|x\rangle\langle x|,
$$

状态 $|x\rangle\langle x|$ 在全部时间保持不变，当且仅当：

$$
\boxed{
H|x\rangle=E_x|x\rangle
}
$$

对某个实数 $E_x$ 成立。

在模式矩阵中，这等价于：

$$
H_{yx}=0\qquad(y\ne x).
$$

### 证明

这是定理5.2在一维子空间上的情形。自伴算子在一维不变空间上只能乘以一个实数。证毕。

因此，在离散模型中，**让一个位置模式精确不散开，需要它是动力学的不变方向；“初始时刻位于这里”本身不足够。**

## theorem 5.4: 小跨界耦合给出有限时间泄漏上界

令：

$$
\varepsilon_R=\|Q_RHP\|.
$$

若初态支持于 $R$，则：

$$
\boxed{
\operatorname{Tr}[Q_RU_t\rho U_t^\dagger]
\le
\min\left\{
1,\frac{t^2\varepsilon_R^2}{\hbar^2}
\right\}.
}
$$

### 证明

定义分块动力学：

$$
H_0=PHP+Q_RHQ_R,
\qquad
U_t^0=e^{-itH_0/\hbar}.
$$

Duhamel 恒等式给：

$$
U_t-U_t^0
=
-\frac{i}{\hbar}
\int_0^tU_{t-s}(H-H_0)U_s^0\,ds.
$$

由于 $U_s^0P$ 的像仍在 $P$ 子空间，且：

$$
(H-H_0)U_s^0P=Q_RHP\,U_s^0P,
$$

所以：

$$
\|Q_RU_tP\|
=
\|Q_R(U_t-U_t^0)P\|
\le
\frac{|t|}{\hbar}\varepsilon_R.
$$

对支持于 $R$ 的纯态取范数平方，再对混合态作凸组合，得到所需界。概率本身不超过一，故可取两界的最小值。证毕。

这提供了一个比“锁在某处”更细的分级：

$$
\boxed{
\text{严格封闭}
\quad\text{或}\quad
\text{在指定时间与误差内近似封闭}.
}
$$

# 六、体—边界关系在这里对应的是概率通量

项目实际 Lean 模块 `ProjectionProbabilityFlow` 已证明：Hamiltonian 演化下，投影概率的导数由对易子迹给出；投影与 Hamiltonian 对易时，该概率恒定。下面保留 $\hbar$，并将其展开成区域边界通量。

## theorem 6.1: 区域占据概率的边界通量公式

设：

$$
\rho_t=U_t\rho_0U_t^\dagger,
\qquad
p_R(t)=\operatorname{Tr}(\rho_tP_R).
$$

则：

$$
\boxed{
\frac{dp_R}{dt}
=
\frac{i}{\hbar}
\operatorname{Tr}[\rho_t[H,P_R]].
}
$$

在模式坐标中定义：

$$
J_{y\to x}(t)
=
\frac{2}{\hbar}
\operatorname{Im}\bigl(H_{xy}(\rho_t)_{yx}\bigr).
$$

有：

$$
J_{x\to y}=-J_{y\to x},
$$

以及：

$$
\boxed{
\frac{dp_R}{dt}
=
\sum_{\substack{x\in R\\y\notin R}}J_{y\to x}(t).
}
$$

### 证明

由：

$$
\dot\rho_t=-\frac{i}{\hbar}[H,\rho_t],
$$

及迹的循环性质：

$$
\begin{aligned}
\frac{dp_R}{dt}
&=
-\frac{i}{\hbar}\operatorname{Tr}([H,\rho_t]P_R)\\
&=
\frac{i}{\hbar}\operatorname{Tr}(\rho_t[H,P_R]).
\end{aligned}
$$

逐对角元展开：

$$
\frac{d(\rho_t)_{xx}}{dt}
=
\frac{2}{\hbar}
\sum_y\operatorname{Im}(H_{xy}(\rho_t)_{yx}).
$$

因为 $H,\rho_t$ 都 Hermitian，交换 $x,y$ 后乘积变为共轭，虚部反号。

对 $x\in R$ 求和，区域内部的成对通量相互抵消，只剩跨边界项。证毕。

### 关系几何中的解释

$$
\boxed{
\text{区域内部概率怎样变化}
=
\text{边界耦合与当前相干关系共同形成的净通量}.
}
$$

这里不是“边界大小决定粒子往哪里去”。边界上的耦合强度与态的相位结构，都参与决定通量。

也不能从某一时刻导数为零推出永久静止。例如：

$$
H=\hbar gX,\qquad \rho_0=|0\rangle\langle0|
$$

给出：

$$
p_0(t)=\cos^2(gt).
$$

在 $t=0$ 导数为零，但随后概率仍会离开模式0。

# 七、一次局域记录为什么是一个结果，而不是波态的全部内容？

## definition 7.1: 理想位置记录耦合

令：

$$
P_x=|x\rangle\langle x|,
\qquad
\sum_xP_x=I.
$$

取正交记录标签 $|r_x\rangle$，定义：

$$
J\psi=\sum_xP_x\psi\otimes|r_x\rangle.
$$

## theorem 7.2: 记录耦合保留相干整体，同时给出互斥结果接口

有：

$$
J^\dagger J=I.
$$

记录 $x$ 的概率为：

$$
p(x)=\operatorname{Tr}(\rho P_x),
$$

且：

$$
\sum_xp(x)=1.
$$

但对：

$$
|\psi\rangle=\alpha|L\rangle+\beta|R\rangle,
\qquad
\alpha\beta\ne0,
$$

联合态为：

$$
\boxed{
J|\psi\rangle
=
\alpha|L\rangle|r_L\rangle
+
\beta|R\rangle|r_R\rangle,
}
$$

并不等于其中任意一个分支。

### 证明

记录标签正交，故：

$$
J^\dagger J
=
\sum_xP_x^\dagger P_x
=I.
$$

对记录投影取迹得到相应概率；完整性给概率和为一。

最后一式由线性性直接得到。由于两个非零分支正交，整个向量不等于单独一个分支。证毕。

**所以，局域记录接口、分支概率与实际取得某个结果，是需要分别陈述的内容。** 不能把“联合耦合已经写出来”冒称为“唯一实际结果已经由酉方程选出”。

## proposition 7.3: 非平凡结果律不能仅由一个固定操作态充当确定选择器

固定相同的准备、装置与当前档案，记这些操作资料为 $\omega$。

若它们给出的结果律同时满足：

$$
p_\omega(x)>0,\qquad p_\omega(y)>0,
\qquad x\ne y,
$$

则不存在一个只依赖 $\omega$ 的确定函数：

$$
f(\omega)
$$

能在完全相同的 $\omega$ 下重现该非平凡结果分布。

### 证明

确定函数在固定输入 $\omega$ 下只能产生一个固定值，诱导的分布是：

$$
\delta_{f(\omega)}.
$$

它不可能同时给两个不同结果正概率。证毕。

这个命题不排除某种扩展理论引入额外来源变量 $\lambda$，使用 $f(\omega,\lambda)$。但那需要新增关于 $\lambda$、其分布及其与实验设置关系的明确假设。

**把已经发生的结果写入“完整图”，再从图中读回，不等于从测量前的操作资料预测了那个结果。**

# 八、把因果与位置一起放进“全息充分边界”

## definition 8.1: 包含干预的未来响应边界

固定实际来源集合 $S$，以及共同允许的未来实验族 $\mathcal T$。

$\mathcal T$ 应包括任务要求比较的局部干预、位置检验、记录和失败标签。

定义：

$$
\mathcal B_{\mathcal T}(s)
=
\bigl(\operatorname{Law}(E[s])\bigr)_{E\in\mathcal T}.
$$

这不是说观察者已执行全部实验，而是完整描述这些实验会如何响应。

对候选摘要：

$$
\eta:S\to B,
$$

称它是该任务的因果—定位充分边界，若全部响应可通过 $\eta$ 恢复。

## theorem 8.2: 因果—定位全息边界的充要条件

$\eta$ 充分，当且仅当：

$$
\boxed{
\ker\eta\subseteq\ker\mathcal B_{\mathcal T}.
}
$$

等价地，存在唯一映射：

$$
R:\eta(S)\to\operatorname{im}\mathcal B_{\mathcal T}
$$

使：

$$
\boxed{
\mathcal B_{\mathcal T}=R\circ\eta.
}
$$

### 证明

若恢复映射存在，相同摘要必给出相同全部响应。

反过来，若核包含成立，在实际像上定义：

$$
R(\eta(s))=\mathcal B_{\mathcal T}(s).
$$

同一纤维中的来源响应相同，因此定义良定。实际像上的满射性给唯一性。证毕。

如果 $\mathcal T$ 只包括被动位置照片，该边界可能无法恢复干预响应；把干预加入实验族，可以严格缩小不可区分纤维。

这正对应项目已有动态充分边界判据的任务化版本。

## theorem 8.3: 完整未来边界在实际结果后递归闭合

在给定量子仪器模型中，设未来实验族对合法前缀与续接封闭。

若两初态 $\rho,\sigma$ 的全部未来响应相同，则它们对当前结果 $y$ 给出相同概率；该概率非零时，结果后的条件态也具有相同的全部未来响应。

### 证明

当前 $y$ 的概率属于声明的未来响应，因此两者相同，记为 $p_y$。

任意合法后续词 $w$ 的条件概率为：

$$
p_\rho(w\mid y)
=
\frac{p_\rho(yw)}{p_\rho(y)}.
$$

全部未来响应相同给出：

$$
p_\rho(yw)=p_\sigma(yw),
\qquad
p_\rho(y)=p_\sigma(y)=p_y>0.
$$

因此条件后续概率相同。证毕。

在内部观察者模型中，还要同时保留使下一选择成立的档案、控制、参考与权限。若这些不同，不能强迫观察者采取同一动作。

项目的顺序仪器词迹公式，为上述联合概率与条件续接提供了实际形式支点。

# 九、这一组结果真正回答了什么？

现在可以把你的问题准确翻译成四个判据。

## 1. “这里能否因果影响那里？”

在完整有限维通道模型中，无影响对应：

$$
\boxed{
\mathcal N^*(E_C)=I_A\otimes G_E.
}
$$

目标检验拉回后不需要 $A$ 的关系。

## 2. “这个位置为什么不能出现粒子式事件？”

在给定准备与仪器下，对应：

$$
\boxed{
K_e\sqrt\rho=0
}
$$

或多 Kraus 情形下每个 $K_{e,\alpha}\sqrt\rho=0$。

是准备、传播与探测接口不相容，可能包括相干抵消。

## 3. “什么让它一直留在这个区域？”

在固定、未插入额外测量的有限维酉动力学下，普适区域封闭对应：

$$
\boxed{
[H,P_R]=0.
}
$$

即该区域与补区域之间没有动力学耦合。

## 4. “为什么这一次一定在这里？”

只有当当前条件态满足：

$$
\boxed{
\operatorname{supp}\rho\subseteq\ker(I-E_e)
}
$$

时，该事件才由操作模型给出概率一。

若概率严格介于零与一，前面的几何和动力学已经规定了结果律，但尚未提供额外的确定结果选择器。

---

## 最终的关系语言

> **因果，是完整关系结构在允许局部改变下表现出来的依赖与传播规则。位置，是量子态与已校准局域接口之间的关系。束缚，是特定动力学不让状态越过某个子空间边界。探测事件，是这些关系通过仪器形成的一份实际记录。**

因此，不需要在关系几何之外再放一个叫“因果”的力量，把粒子钉在一点。

但完整几何必须明确保存：

$$
\boxed{
\text{允许改变什么}
\;\longrightarrow\;
\text{改变怎样传播}
\;\longrightarrow\;
\text{哪些事件具有何种概率}
\;\longrightarrow\;
\text{取得记录后怎样继续}.
}
$$

**“形状就是约束”在这里获得了具体内容：约束不是一个笼统的名字，而是通道的因子化、效果的支撑条件、Hamiltonian 的跨界耦合，以及记录后的递归闭合。**
